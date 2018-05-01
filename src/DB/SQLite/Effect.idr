module DB.SQLite.Effect
import Effects
import DB.SQLite.SQLiteCodes

%default total

%link C "sqlite3api.o"
%include C "sqlite3api.h"
%lib C "sqlite3"

%dynamic "libsqlite3"
%dynamic "sqlite3api.so"
%access public export

data ConnectionPtr = ConnPtr Ptr
data StmtPtr = PSPtr Ptr

data DBVal = DBInt Int
           | DBText String
           | DBFloat Double
           | DBNull

implementation Show DBVal where
  show (DBInt i) = "DBInt " ++ show i
  show (DBText t) = "DBText " ++ show t
  show (DBFloat f) = "DBFloat " ++ show f
  show DBNull = "DBNull"

-- Type synonym for a table
ResultSet : Type
ResultSet = List (List DBVal)

DBName : Type
DBName = String

QueryString : Type
QueryString = String

Column : Type
Column = Int

ArgPos : Type
ArgPos = Int
data BindError = BE ArgPos SQLiteCode

{- Connection-stage resources -}
data SQLiteConnected : Type where
  SQLConnection : ConnectionPtr -> SQLiteConnected

{- PreparedStatement resources -}
data BindStep = Binding | Bound

data SQLitePSSuccess : BindStep -> Type where
  -- We record potential bind failures within the resource,
  -- and branch on the finishBind step. This prevents us from
  -- having to branch on every bind, which would be impractical.
  SQLitePS : ConnectionPtr -> StmtPtr -> SQLitePSSuccess a
  SQLiteBindFail : ConnectionPtr -> StmtPtr -> BindError -> SQLitePSSuccess a


data SQLitePSFail : Type where
  PSFail : ConnectionPtr -> SQLitePSFail

data SQLiteFinishBindFail : Type where
  SQLiteFBFail : ConnectionPtr -> StmtPtr -> SQLiteFinishBindFail

{- Executing Resources -}
-- Tag used to indicate whether another row may be fetched
data ExecutionResult = ValidRow
                     | InvalidRow

data SQLiteExecuting : ExecutionResult -> Type where
  SQLiteE : ConnectionPtr -> StmtPtr -> SQLiteExecuting a

data QueryError = ConnectionError SQLiteCode
                | BindingError BindError
                | StatementError SQLiteCode
                | ExecError String
                | InternalError

implementation Show QueryError where
  show (ConnectionError code) = "Error connecting to database, code: " ++ (show code)
  show (BindingError (BE ap code)) = "Error binding variable, pos: " ++ (show ap) ++ ", code: " ++ (show code)
  show (StatementError code) = "Error creating prepared statement, code: " ++ (show code)
  show (ExecError err) = err
  show (InternalError) = "Internal Error."

data Sqlite : Effect where
  -- Opens a connection to the database
  OpenDB : DBName -> sig Sqlite (Either QueryError ()) () (\result => (either (const ()) (const SQLiteConnected) result))
  -- Closes the database handle
  CloseDB : sig Sqlite () SQLiteConnected ()
  -- Prepares a statement, given a basic query string
  PrepareStatement : QueryString -> sig Sqlite (Either QueryError ())
                      (SQLiteConnected)
                       (\result => either (const SQLitePSFail)
                              (const $ SQLitePSSuccess Binding) result)
  -- Binds arguments to the given argument position
  BindInt : ArgPos -> Int -> sig  Sqlite () (SQLitePSSuccess Binding)
  BindFloat : ArgPos -> Double -> sig Sqlite () (SQLitePSSuccess Binding)
  BindText : ArgPos -> String -> Int -> sig Sqlite () (SQLitePSSuccess Binding)
  BindNull : ArgPos -> sig Sqlite () (SQLitePSSuccess Binding)

  -- Checks to see whether all the binds were successful, if not then fails with the bind error
  FinishBind : sig Sqlite (Maybe QueryError) (SQLitePSSuccess Binding) (\result => maybe (SQLitePSSuccess Bound) (const SQLiteFinishBindFail) result)

  -- Executes the statement, and fetches the first row
  ExecuteStatement : sig Sqlite (StepResult) (SQLitePSSuccess Bound)
                       (\result => if hasMoreRows result
                         then SQLiteExecuting ValidRow
                         else SQLiteExecuting InvalidRow)

  RowStep : sig Sqlite (StepResult) (SQLiteExecuting ValidRow)
              (\result => if hasMoreRows result
                then SQLiteExecuting ValidRow
                else SQLiteExecuting InvalidRow)

  -- We need two separate effects, but this is entirely non-user-facing due to
  -- if_valid in the wrapper function
  Reset : sig Sqlite (StepResult) (SQLiteExecuting state)
            (\result => if hasMoreRows result
              then SQLiteExecuting ValidRow
              else SQLiteExecuting InvalidRow)

  -- Column access functions
  GetColumnName : Column -> sig  Sqlite String (SQLiteExecuting ValidRow)
  GetColumnDataSize : Column -> sig  Sqlite Int (SQLiteExecuting ValidRow)
  GetColumnText : Column -> sig  Sqlite String (SQLiteExecuting ValidRow)
  GetColumnInt : Column -> sig Sqlite Int (SQLiteExecuting ValidRow)
  GetColumnFloat : Column -> sig Sqlite Double (SQLiteExecuting ValidRow)
  IsColumnNull : Column -> sig Sqlite Bool (SQLiteExecuting ValidRow)

  -- Finalisation Functions
  Finalise : sig Sqlite () (SQLiteExecuting s) SQLiteConnected


  -- Cleanup functions to handle error states
  CleanupPSFail : sig Sqlite () SQLitePSFail  ()  
  CleanupBindFail : sig  Sqlite () SQLiteFinishBindFail ()


private
foreignGetError : ConnectionPtr -> IO Int
foreignGetError (ConnPtr ptr) = foreign FFI_C "idr_errcode" (Ptr -> IO Int) ptr

private
foreignNextRow : ConnectionPtr -> IO StepResult
foreignNextRow (ConnPtr ptr) =
  map stepResult (foreign FFI_C "sqlite3_step_idr" (Ptr -> IO Int) ptr)

private
foreignFinalise : ConnectionPtr -> IO ()
foreignFinalise (ConnPtr c) = do foreign FFI_C "sqlite3_finalize_idr" (Ptr -> IO Int) c
                                 pure ()

private
foreignClose : ConnectionPtr -> IO ()
foreignClose (ConnPtr c) = do foreign FFI_C "sqlite3_close_idr" (Ptr -> IO Int) c
                              pure ()

-- That's the painful bit done, since exception branching will allow us to not have to do
-- the ugliness of pass-through handlers
implementation Handler Sqlite IO where
  handle () (OpenDB file) k = do
    ff <- foreign FFI_C "sqlite3_open_idr" (String -> IO Ptr) file
    is_null <- nullPtr ff
    if (not is_null) then k (Right ()) (SQLConnection (ConnPtr ff))
                     else k (Left (ConnectionError sqlite_ERROR)) ()

  handle (SQLConnection (ConnPtr conn)) CloseDB k = do
    foreign FFI_C "sqlite3_close_idr" (Ptr -> IO Int) conn
    k () ()

  handle (SQLConnection (ConnPtr conn)) (PrepareStatement str) k = do
    res <- foreign FFI_C "sqlite3_prepare_idr" (Ptr -> String -> IO Ptr) conn str
    is_null <- nullPtr res
    if (not is_null) then k (Right ()) (SQLitePS (ConnPtr conn) (PSPtr res))
                     else do err <- foreignGetError (ConnPtr conn)
                             k (Left (StatementError err)) (PSFail (ConnPtr conn))

  handle (SQLitePS (ConnPtr conn) (PSPtr res)) (BindInt pos i) k = do
    res <- foreign FFI_C "sqlite3_bind_int_idr" (Ptr -> Int -> Int -> IO Ptr) conn pos i
    is_null <- nullPtr res
    if (not is_null) then k () (SQLitePS (ConnPtr conn) (PSPtr res))
                     else do err <- foreignGetError (ConnPtr conn)
             -- putStrLn $ "BindInt error: " ++ (show err)
                             k () (SQLiteBindFail (ConnPtr conn) (PSPtr res) (BE pos err))

  handle (SQLitePS (ConnPtr conn) (PSPtr res)) (BindFloat pos f) k = do
    res <- foreign FFI_C "sqlite3_bind_double_idr" (Ptr -> Int -> Double -> IO Ptr) conn pos f
    is_null <- nullPtr res
    if (not is_null) then k () (SQLitePS (ConnPtr conn) (PSPtr res))
                     else do err <- foreignGetError (ConnPtr conn)
                             k () (SQLiteBindFail (ConnPtr conn) (PSPtr res) (BE pos err))

  handle (SQLitePS (ConnPtr conn) (PSPtr res)) (BindText pos str str_len) k = do
    res <- foreign FFI_C "sqlite3_bind_text_idr"
                   (Ptr -> String -> Int -> Int -> IO Ptr)
                   conn str pos str_len
    is_null <- nullPtr res
    if (not is_null) then k () (SQLitePS (ConnPtr conn) (PSPtr res))
                     else do err <- foreignGetError (ConnPtr conn)
               -- putStrLn $ "BindStr error: " ++ (show err)
                             k () (SQLiteBindFail (ConnPtr conn) (PSPtr res) (BE pos err))

  handle (SQLitePS (ConnPtr conn) (PSPtr res)) (BindNull pos) k = do
    res <- foreign FFI_C "sqlite3_bind_null_idr" (Ptr -> Int -> IO Ptr) conn pos
    is_null <- nullPtr res
    if (not is_null) then k () (SQLitePS (ConnPtr conn) (PSPtr res))
                     else do err <- foreignGetError (ConnPtr conn)
                             k () (SQLiteBindFail (ConnPtr conn) (PSPtr res) (BE pos err))

  -- Ok, I lied, we have to do *some* pass-throughs. But they're not terrible.
  handle (SQLiteBindFail conn ps be) (BindInt _ _) k = k () (SQLiteBindFail conn ps be)
  handle (SQLiteBindFail conn ps be) (BindText _ _ _) k = k () (SQLiteBindFail conn ps be)
  handle (SQLiteBindFail conn ps be) (BindFloat _ _) k = k () (SQLiteBindFail conn ps be)
  handle (SQLiteBindFail conn ps be) (BindNull _) k = k () (SQLiteBindFail conn ps be)


  -- Finishing binding, reporting any bind errors if they occurred
  handle (SQLitePS c p) (FinishBind) k =
    k Nothing (SQLitePS c p)

  handle (SQLiteBindFail c ps be) (FinishBind) k =
    k (Just (BindingError be)) (SQLiteFBFail c ps)

  handle (SQLitePS (ConnPtr c) (PSPtr p)) (ExecuteStatement) k = do
    step <- foreignNextRow (ConnPtr c)
    case step of
      Unstarted    => k Unstarted    (SQLiteE (ConnPtr c) (PSPtr p))
      StepComplete => k StepComplete (SQLiteE (ConnPtr c) (PSPtr p))
      StepFail     => k StepFail     (SQLiteE (ConnPtr c) (PSPtr p))
      NoMoreRows   => k NoMoreRows   (SQLiteE (ConnPtr c) (PSPtr p))

  handle (SQLiteE (ConnPtr c) (PSPtr p)) (RowStep) k = do
    step <- foreignNextRow (ConnPtr c)
    case step of
      Unstarted    => k Unstarted    (SQLiteE (ConnPtr c) (PSPtr p))
      StepComplete => k StepComplete (SQLiteE (ConnPtr c) (PSPtr p))
      StepFail     => k StepFail     (SQLiteE (ConnPtr c) (PSPtr p))
      NoMoreRows   => k NoMoreRows   (SQLiteE (ConnPtr c) (PSPtr p))

  -- Getting values from the current row
  handle (SQLiteE (ConnPtr c) (PSPtr p)) (GetColumnName i) k = do
    res <- foreign FFI_C "sqlite3_column_name_idr" (Ptr -> Int -> IO String) c i
    k res (SQLiteE (ConnPtr c) (PSPtr p))

  handle (SQLiteE (ConnPtr c) (PSPtr p)) (GetColumnDataSize i) k = do
    res <- foreign FFI_C "sqlite3_column_bytes_idr" (Ptr -> Int -> IO Int) c i
    k res (SQLiteE (ConnPtr c) (PSPtr p))

  handle (SQLiteE (ConnPtr c) (PSPtr p)) (GetColumnInt i) k = do
    res <- foreign FFI_C "sqlite3_column_int_idr" (Ptr -> Int -> IO Int) c i
    k res (SQLiteE (ConnPtr c) (PSPtr p))

  handle (SQLiteE (ConnPtr c) (PSPtr p)) (GetColumnFloat i) k = do
    res <- foreign FFI_C "sqlite3_column_double_idr" (Ptr -> Int -> IO Double) c i
    k res (SQLiteE (ConnPtr c) (PSPtr p))

  handle (SQLiteE (ConnPtr c) (PSPtr p)) (GetColumnText i) k = do
    res <- foreign FFI_C "sqlite3_column_text_idr" (Ptr -> Int -> IO String) c i
    k res (SQLiteE (ConnPtr c) (PSPtr p))

  handle (SQLiteE (ConnPtr c) (PSPtr p)) (IsColumnNull i) k = do
    res <- foreign FFI_C "sqlite3_column_null_idr" (Ptr -> Int -> IO Int) c i
    k (res /= 0) (SQLiteE (ConnPtr c) (PSPtr p))

  -- Resetting our position
  handle (SQLiteE (ConnPtr c) (PSPtr p)) (Reset) k = do
    foreign FFI_C "sqlite3_reset_idr" (Ptr -> IO Int) c
    step <- foreignNextRow (ConnPtr c)
    case step of
      Unstarted    => k Unstarted    (SQLiteE (ConnPtr c) (PSPtr p))
      StepComplete => k StepComplete (SQLiteE (ConnPtr c) (PSPtr p))
      StepFail     => k StepFail     (SQLiteE (ConnPtr c) (PSPtr p))
      NoMoreRows   => k NoMoreRows   (SQLiteE (ConnPtr c) (PSPtr p))

{-  handle (SQLiteE (ConnPtr c) (PSPtr p)) (ResetFromEnd) k = do
    foreign FFI_C (FFun "sqlite3_reset_idr" [FPtr] FInt) c
    step <- foreignNextRow (ConnPtr c)
    case step of
      StepComplete => k StepComplete (SQLiteE (ConnPtr c) (PSPtr p))
      StepFail     => k StepFail     (SQLiteE (ConnPtr c) (PSPtr p))
      NoMoreRows   => k NoMoreRows   (SQLiteE (ConnPtr c) (PSPtr p))
-}
      -- Finalising the SQL Statement
  handle (SQLiteE c p) (Finalise) k = do
    foreignFinalise c
    k () (SQLConnection c)

  handle (PSFail c) CleanupPSFail k = do
    foreignClose c
    k () ()

  handle (SQLiteFBFail c p) CleanupBindFail k = do
    foreignFinalise c
    foreignClose c
    k () ()
  --hack
  handle _ _ k = believe_me ()



SQLITE : Type -> EFFECT
SQLITE t = MkEff t Sqlite
{- User-facing functions -}
openDB : DBName ->  Eff (Either QueryError ()) [SQLITE ()]
                     (\result => [SQLITE (either (const ()) (const SQLiteConnected) result)])
openDB name = call $ OpenDB name

closeDB : Eff () [SQLITE (SQLiteConnected)] [SQLITE ()]
closeDB = call CloseDB

prepareStatement : QueryString -> Eff (Either QueryError ())
                    [SQLITE SQLiteConnected]
                    (\result => [SQLITE ( either (const SQLitePSFail)
                                      (const $ SQLitePSSuccess Binding) result)])
prepareStatement stmt = call $ PrepareStatement stmt

bindInt : ArgPos -> Int -> Eff () [SQLITE (SQLitePSSuccess Binding)]
bindInt pos i = call $ BindInt pos i

bindFloat : ArgPos -> Double -> Eff () [SQLITE (SQLitePSSuccess Binding)]
bindFloat pos f = call $ BindFloat pos f

bindText : ArgPos -> String -> Eff () [SQLITE (SQLitePSSuccess Binding)]
bindText pos str = call $ BindText pos str str_len
  where natToInt : Nat -> Int
        natToInt Z = 0
        natToInt (S k) = 1 + (natToInt k)

        str_len : Int
        str_len = natToInt (length str)

bindNull : ArgPos -> Eff () [SQLITE (SQLitePSSuccess Binding)]
bindNull pos = call $ BindNull pos

finishBind : Eff (Maybe QueryError) [SQLITE (SQLitePSSuccess Binding)]
               (\result => [SQLITE (maybe (SQLitePSSuccess Bound) (const SQLiteFinishBindFail) result)])
finishBind = call FinishBind

nextRow : Eff StepResult [SQLITE (SQLiteExecuting ValidRow)]
            (\result => [SQLITE (if hasMoreRows result
                       then SQLiteExecuting ValidRow
                       else SQLiteExecuting InvalidRow)])
nextRow = call RowStep

reset : Eff StepResult [SQLITE (SQLiteExecuting state)]
          (\result => [SQLITE (if hasMoreRows result
                     then SQLiteExecuting ValidRow
                     else SQLiteExecuting InvalidRow)])
reset = call Reset


getColumnName : Column -> Eff String [SQLITE (SQLiteExecuting ValidRow)]
getColumnName col = call $ GetColumnName col

getColumnText : Column -> Eff String [SQLITE (SQLiteExecuting ValidRow)]
getColumnText col = call $ GetColumnText col

getColumnInt : Column -> Eff Int [SQLITE (SQLiteExecuting ValidRow)]
getColumnInt col = call $ GetColumnInt col

getColumnFloat : Column -> Eff Double [SQLITE (SQLiteExecuting ValidRow)]
getColumnFloat col = call $ GetColumnFloat col

isColumnNull : Column -> Eff Bool [SQLITE (SQLiteExecuting ValidRow)]
isColumnNull col = call $ IsColumnNull col

getColumnDataSize : Column -> Eff Int [SQLITE (SQLiteExecuting ValidRow)]
getColumnDataSize col = call $ GetColumnDataSize col

finalise : Eff () [SQLITE (SQLiteExecuting s)] [SQLITE SQLiteConnected]
finalise = call Finalise

cleanupPSFail : Eff () [SQLITE (SQLitePSFail)] [SQLITE ()]
cleanupPSFail = call CleanupPSFail

cleanupBindFail :  Eff () [SQLITE (SQLiteFinishBindFail)] [SQLITE ()]
cleanupBindFail = call CleanupBindFail

-- Just makes it a tad nicer to write
executeStatement : Eff StepResult [SQLITE (SQLitePSSuccess Bound)]
                     (\result => [SQLITE (if hasMoreRows result
                                then SQLiteExecuting ValidRow
                                else SQLiteExecuting InvalidRow)])
executeStatement = call ExecuteStatement


getQueryError : Either QueryError b -> QueryError
getQueryError (Left qe) = qe
getQueryError _ = InternalError

total
multiBind' : List (Int, DBVal) -> Eff () [SQLITE (SQLitePSSuccess Binding)]
multiBind' [] = Effects.pure ()
multiBind' ((pos, (DBInt i)) :: xs) = do bindInt pos i
                                         multiBind' xs
multiBind' ((pos, (DBFloat f)) :: xs) = do bindFloat pos f
                                           multiBind' xs
multiBind' ((pos, (DBText t)) :: xs) = do bindText pos t
                                          multiBind' xs
multiBind' ((pos, DBNull) :: xs) = do bindNull pos
                                      multiBind' xs
-- Binds multiple values within a query

multiBind : List (Int, DBVal) -> Eff (Maybe QueryError)
                 [SQLITE (SQLitePSSuccess Binding)]
                 (\result => [SQLITE (maybe (SQLitePSSuccess Bound) (const SQLiteFinishBindFail) result)])
            
multiBind vals = do
  multiBind' vals
  finishBind



getRowCount' : StepResult -> Eff (Either QueryError Int) [SQLITE (SQLiteExecuting s)] [SQLITE ()]
               
getRowCount' NoMoreRows   = do finalise
                               closeDB
                               pure $ Left (ExecError "Unable to get row count")
getRowCount' StepFail     = do finalise
                               closeDB
                               pure $ Left (ExecError "Error whilst getting row count")
getRowCount' {s=ValidRow} StepComplete = do last_insert_id <- getColumnInt 0
                                            finalise
                                            closeDB
                                            pure $ Right last_insert_id
getRowCount' {s=InvalidRow} StepComplete = do finalise
                                              closeDB
                                              pure $ Left (ExecError "Invalid row")
getRowCount' Unstarted    = do finalise
                               closeDB
                               pure $ Left (ExecError "Not started")

getBindError : Maybe QueryError -> QueryError
getBindError (Just (BindingError be)) = (BindingError be)
getBindError _ = InternalError


getRowCount : Eff (Either QueryError Int) [SQLITE SQLiteConnected] [SQLITE ()] 
getRowCount = do
  let insert_id_sql = "SELECT last_insert_rowid()"
  sql_prep_res <- prepareStatement insert_id_sql
  case sql_prep_res of
    Left err => do cleanupPSFail
                   pure (Left err)
    Right () =>
      do bind_res_2 <- finishBind
         case bind_res_2 of
           Just err => do let be = getBindError bind_res_2
                          cleanupBindFail
                          pure $ Left be
           Nothing =>
             do exec_res <- executeStatement
                case exec_res of
                  NoMoreRows => getRowCount' NoMoreRows
                  StepComplete => getRowCount' StepComplete
                  StepFail => getRowCount' StepFail
                  Unstarted => getRowCount' Unstarted

executeInsert : String ->
                String ->
                List (Int, DBVal) ->
                Eff (Either QueryError Int) [SQLITE ()]
executeInsert db_name query bind_vals =
  do db_res <- openDB db_name
     case db_res of
       Left err => pure (Left err)
       Right () =>
         do ps_res <- prepareStatement query
            case ps_res of
              Left err => do cleanupPSFail
                             pure (Left err)
              Right () =>
                do bind_res <- multiBind bind_vals
                   case bind_res of
                     Just err => do cleanupBindFail
                                    pure (Left err)
                     Nothing  => executeIt
  -- split out to make typechecking faster
  where executeIt : Eff (Either QueryError Int) [SQLITE (SQLitePSSuccess Bound)] [SQLITE ()]
                    
        executeIt =
          do er_1 <- executeStatement
             case er_1 of
               StepFail => do finalise {s=ValidRow}
                              closeDB
                              pure $ Left (ExecError "Error inserting")
               Unstarted => do finalise {s=ValidRow}
                               closeDB
                               pure $ Left (ExecError "Internal error: 'unstarted' after execution")
               NoMoreRows => do finalise {s=InvalidRow}
                                getRowCount
               StepComplete => do finalise {s=ValidRow}
                                  getRowCount


-- Helper functions for selection from a DB
partial
collectResults : (Eff (List DBVal) [SQLITE (SQLiteExecuting ValidRow)]) ->
                 Eff ResultSet [SQLITE (SQLiteExecuting ValidRow)] [SQLITE (SQLiteExecuting InvalidRow)]
collectResults fn =
  do results <- fn
     case !nextRow of
       Unstarted => pure $ results :: !(collectResults fn)
       StepFail => pure $ results :: !(collectResults fn)
       StepComplete => pure $ results :: !(collectResults fn)
       NoMoreRows => pure [results]


-- Convenience function to abstract around some of the boilerplate code.
-- Takes in the DB name, query, a list of (position, variable value) tuples,
-- a function to process the returned data,
partial
executeSelect : (db_name : String) -> (q : String) -> List (Int, DBVal) ->
                (Eff (List DBVal) [SQLITE (SQLiteExecuting ValidRow)]) ->
                Eff (Either QueryError ResultSet) [SQLITE ()]
executeSelect db_name q bind_vals fn =
  do Right () <- openDB db_name | Left err => pure (Left err)
     Right () <- prepareStatement q | Left err => do cleanupPSFail
                                                     pure $ Left err
     Nothing <- multiBind bind_vals | Just err => do cleanupBindFail
                                                     pure $ Left err
     case !executeStatement of
       Unstarted => do res <- collectResults fn
                       finalise
                       closeDB
                       pure $ Right res
       StepFail => do res <- collectResults fn
                      finalise
                      closeDB
                      pure $ Right res
       StepComplete => do res <- collectResults fn
                          finalise
                          closeDB
                          pure $ Right res
       NoMoreRows => do finalise
                        closeDB
                        pure $ Right []

