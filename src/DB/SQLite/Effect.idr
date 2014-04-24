module DB.SQLite.Effect
import Effects
import DB.SQLite.SQLiteCodes

%default total

%link C "sqlite3api.o"
%include C "sqlite3api.h"
%lib C "sqlite3"

%dynamic "libsqlite3"
%dynamic "sqlite3api.so"
%access public

data ConnectionPtr = ConnPtr Ptr
data StmtPtr = PSPtr Ptr

data DBVal = DBInt Int
           | DBText String
           | DBFloat Float
           | DBNull

instance Show DBVal where
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

instance Show QueryError where
  show (ConnectionError code) = "Error connecting to database, code: " ++ (show code)
  show (BindingError (BE ap code)) = "Error binding variable, pos: " ++ (show ap) ++ ", code: " ++ (show code)
  show (StatementError code) = "Error creating prepared statement, code: " ++ (show code)
  show (ExecError err) = err
  show (InternalError) = "Internal Error."

data Sqlite : Effect where
  -- Opens a connection to the database
  OpenDB : DBName ->
           { () ==> either (const ()) (const SQLiteConnected) result } Sqlite (Either QueryError ())
  -- Closes the database handle
  CloseDB : { SQLiteConnected ==> () } Sqlite ()
  -- Prepares a statement, given a basic query string
  PrepareStatement : QueryString ->
                     { SQLiteConnected ==>
                       either (const SQLitePSFail)
                              (const $ SQLitePSSuccess Binding) result } Sqlite (Either QueryError ())
  -- Binds arguments to the given argument position
  BindInt : ArgPos -> Int -> { SQLitePSSuccess Binding } Sqlite ()
  BindFloat : ArgPos -> Float ->
              { SQLitePSSuccess Binding } Sqlite ()
  BindText : ArgPos -> String -> Int ->
             { SQLitePSSuccess Binding } Sqlite ()
  BindNull : ArgPos -> { SQLitePSSuccess Binding } Sqlite ()

  -- Checks to see whether all the binds were successful, if not then fails with the bind error
  FinishBind : {SQLitePSSuccess Binding ==>
                maybe (SQLitePSSuccess Bound) (const SQLiteFinishBindFail) result } Sqlite (Maybe QueryError)

  -- Executes the statement, and fetches the first row
  ExecuteStatement : { SQLitePSSuccess Bound ==>
                       if hasMoreRows result
                         then SQLiteExecuting ValidRow
                         else SQLiteExecuting InvalidRow } Sqlite StepResult

  RowStep : { SQLiteExecuting ValidRow ==>
              if hasMoreRows result
                then SQLiteExecuting ValidRow
                else SQLiteExecuting InvalidRow } Sqlite StepResult

  -- We need two separate effects, but this is entirely non-user-facing due to
  -- if_valid in the wrapper function
  Reset : { SQLiteExecuting state ==>
            if hasMoreRows result
              then SQLiteExecuting ValidRow
              else SQLiteExecuting InvalidRow} Sqlite StepResult

  -- Column access functions
  GetColumnName : Column -> { SQLiteExecuting ValidRow } Sqlite String
  GetColumnDataSize : Column -> { SQLiteExecuting ValidRow } Sqlite Int
  GetColumnText : Column -> { SQLiteExecuting ValidRow } Sqlite String
  GetColumnInt : Column -> { SQLiteExecuting ValidRow } Sqlite Int
  GetColumnFloat : Column -> { SQLiteExecuting ValidRow } Sqlite Float
  IsColumnNull : Column -> { SQLiteExecuting ValidRow } Sqlite Bool

  -- Finalisation Functions
  Finalise : { SQLiteExecuting s ==> SQLiteConnected } Sqlite ()


  -- Cleanup functions to handle error states
  CleanupPSFail : { SQLitePSFail ==> () } Sqlite ()
  CleanupBindFail : { SQLiteFinishBindFail ==> () } Sqlite ()



private
foreignGetError : ConnectionPtr -> IO Int
foreignGetError (ConnPtr ptr) = mkForeign (FFun "idr_errcode" [FPtr] FInt) ptr

private
foreignNextRow : ConnectionPtr -> IO StepResult
foreignNextRow (ConnPtr ptr) =
  map stepResult (mkForeign (FFun "sqlite3_step_idr" [FPtr] FInt) ptr)

private
foreignFinalise : ConnectionPtr -> IO ()
foreignFinalise (ConnPtr c) = do mkForeign (FFun "sqlite3_finalize_idr" [FPtr] FInt) c
                                 return ()

private
foreignClose : ConnectionPtr -> IO ()
foreignClose (ConnPtr c) = do mkForeign (FFun "sqlite3_close_idr" [FPtr] FInt) c
                              return ()


-- That's the painful bit done, since exception branching will allow us to not have to do
-- the ugliness of pass-through handlers
instance Handler Sqlite IO where
  handle () (OpenDB file) k = do
    ff <- mkForeign (FFun "sqlite3_open_idr" [FString] FPtr) file
    is_null <- nullPtr ff
    if (not is_null) then k (Right ()) (SQLConnection (ConnPtr ff))
                     else k (Left (ConnectionError sqlite_ERROR)) ()

  handle (SQLConnection (ConnPtr conn)) CloseDB k = do
    mkForeign (FFun "sqlite3_close_idr" [FPtr] FInt) conn
    k () ()

  handle (SQLConnection (ConnPtr conn)) (PrepareStatement str) k = do
    res <- mkForeign (FFun "sqlite3_prepare_idr" [FPtr, FString] FPtr) conn str
    is_null <- nullPtr res
    if (not is_null) then k (Right ()) (SQLitePS (ConnPtr conn) (PSPtr res))
                     else do err <- foreignGetError (ConnPtr conn)
                             k (Left (StatementError err)) (PSFail (ConnPtr conn))

  handle (SQLitePS (ConnPtr conn) (PSPtr res)) (BindInt pos i) k = do
    res <- mkForeign (FFun "sqlite3_bind_int_idr" [FPtr, FInt, FInt] FPtr) conn pos i
    is_null <- nullPtr res
    if (not is_null) then k () (SQLitePS (ConnPtr conn) (PSPtr res))
                     else do err <- foreignGetError (ConnPtr conn)
             -- putStrLn $ "BindInt error: " ++ (show err)
                             k () (SQLiteBindFail (ConnPtr conn) (PSPtr res) (BE pos err))

  handle (SQLitePS (ConnPtr conn) (PSPtr res)) (BindFloat pos f) k = do
    res <- mkForeign (FFun "sqlite3_bind_double_idr" [FPtr, FInt, FFloat] FPtr) conn pos f
    is_null <- nullPtr res
    if (not is_null) then k () (SQLitePS (ConnPtr conn) (PSPtr res))
                     else do err <- foreignGetError (ConnPtr conn)
                             k () (SQLiteBindFail (ConnPtr conn) (PSPtr res) (BE pos err))

  handle (SQLitePS (ConnPtr conn) (PSPtr res)) (BindText pos str str_len) k = do
    res <- mkForeign (FFun "sqlite3_bind_text_idr" [FPtr, FString, FInt, FInt] FPtr) conn str pos str_len
    is_null <- nullPtr res
    if (not is_null) then k () (SQLitePS (ConnPtr conn) (PSPtr res))
                     else do err <- foreignGetError (ConnPtr conn)
               -- putStrLn $ "BindStr error: " ++ (show err)
                             k () (SQLiteBindFail (ConnPtr conn) (PSPtr res) (BE pos err))

  handle (SQLitePS (ConnPtr conn) (PSPtr res)) (BindNull pos) k = do
    res <- mkForeign (FFun "sqlite3_bind_null_idr" [FPtr, FInt] FPtr) conn pos
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
      StepComplete => k StepComplete (SQLiteE (ConnPtr c) (PSPtr p))
      StepFail     => k StepFail     (SQLiteE (ConnPtr c) (PSPtr p))
      NoMoreRows   => k NoMoreRows   (SQLiteE (ConnPtr c) (PSPtr p))

  handle (SQLiteE (ConnPtr c) (PSPtr p)) (RowStep) k = do
    step <- foreignNextRow (ConnPtr c)
    case step of
      StepComplete => k StepComplete (SQLiteE (ConnPtr c) (PSPtr p))
      StepFail     => k StepFail     (SQLiteE (ConnPtr c) (PSPtr p))
      NoMoreRows   => k NoMoreRows   (SQLiteE (ConnPtr c) (PSPtr p))

  -- Getting values from the current row
  handle (SQLiteE (ConnPtr c) (PSPtr p)) (GetColumnName i) k = do
    res <- mkForeign (FFun "sqlite3_column_name_idr" [FPtr, FInt] FString) c i
    k res (SQLiteE (ConnPtr c) (PSPtr p))

  handle (SQLiteE (ConnPtr c) (PSPtr p)) (GetColumnDataSize i) k = do
    res <- mkForeign (FFun "sqlite3_column_bytes_idr" [FPtr, FInt] FInt) c i
    k res (SQLiteE (ConnPtr c) (PSPtr p))

  handle (SQLiteE (ConnPtr c) (PSPtr p)) (GetColumnInt i) k = do
    res <- mkForeign (FFun "sqlite3_column_int_idr" [FPtr, FInt] FInt) c i
    k res (SQLiteE (ConnPtr c) (PSPtr p))

  handle (SQLiteE (ConnPtr c) (PSPtr p)) (GetColumnFloat i) k = do
    res <- mkForeign (FFun "sqlite3_column_double_idr" [FPtr, FInt] FFloat) c i
    k res (SQLiteE (ConnPtr c) (PSPtr p))

  handle (SQLiteE (ConnPtr c) (PSPtr p)) (GetColumnText i) k = do
    res <- mkForeign (FFun "sqlite3_column_text_idr" [FPtr, FInt] FString) c i
    k res (SQLiteE (ConnPtr c) (PSPtr p))

  handle (SQLiteE (ConnPtr c) (PSPtr p)) (IsColumnNull i) k = do
    res <- mkForeign (FFun "sqlite3_column_null_idr" [FPtr, FInt] FInt) c i
    k (res /= 0) (SQLiteE (ConnPtr c) (PSPtr p))

  -- Resetting our position
  handle (SQLiteE (ConnPtr c) (PSPtr p)) (Reset) k = do
    mkForeign (FFun "sqlite3_reset_idr" [FPtr] FInt) c
    step <- foreignNextRow (ConnPtr c)
    case step of
      StepComplete => k StepComplete (SQLiteE (ConnPtr c) (PSPtr p))
      StepFail     => k StepFail     (SQLiteE (ConnPtr c) (PSPtr p))
      NoMoreRows   => k NoMoreRows   (SQLiteE (ConnPtr c) (PSPtr p))

{-  handle (SQLiteE (ConnPtr c) (PSPtr p)) (ResetFromEnd) k = do
    mkForeign (FFun "sqlite3_reset_idr" [FPtr] FInt) c
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


SQLITE : Type -> EFFECT
SQLITE t = MkEff t Sqlite
{- User-facing functions -}
openDB : DBName -> { [SQLITE ()] ==>
                     [SQLITE (either (const ()) (const SQLiteConnected) result)] } Eff IO (Either QueryError ())
openDB name = OpenDB name

closeDB : { [SQLITE (SQLiteConnected)] ==> [SQLITE ()] } Eff IO ()
closeDB = CloseDB

prepareStatement : QueryString ->
                   { [SQLITE SQLiteConnected] ==>
                     [SQLITE ( either (const SQLitePSFail)
                                      (const $ SQLitePSSuccess Binding) result)] } Eff IO (Either QueryError ())
prepareStatement stmt = (PrepareStatement stmt)

bindInt : ArgPos -> Int ->
          { [SQLITE (SQLitePSSuccess Binding)] } Eff IO ()
bindInt pos i = (BindInt pos i)

bindFloat : ArgPos -> Float -> { [SQLITE (SQLitePSSuccess Binding)] } Eff IO ()
bindFloat pos f = (BindFloat pos f)

bindText : ArgPos -> String -> { [SQLITE (SQLitePSSuccess Binding)] } Eff IO ()
bindText pos str = (BindText pos str str_len)
  where natToInt : Nat -> Int
        natToInt Z = 0
        natToInt (S k) = 1 + (natToInt k)

        str_len : Int
        str_len = natToInt (length str)

bindNull : ArgPos -> { [SQLITE (SQLitePSSuccess Binding)] } Eff IO ()
bindNull pos = BindNull pos

finishBind : { [SQLITE (SQLitePSSuccess Binding)] ==>
               [SQLITE (maybe (SQLitePSSuccess Bound) (const SQLiteFinishBindFail) result)] } Eff IO (Maybe QueryError)
finishBind = FinishBind

nextRow : { [SQLITE (SQLiteExecuting ValidRow)] ==>
            [SQLITE (if hasMoreRows result
                       then SQLiteExecuting ValidRow
                       else SQLiteExecuting InvalidRow)] } Eff IO StepResult
nextRow = RowStep

reset : { [SQLITE (SQLiteExecuting state)] ==>
          [SQLITE (if hasMoreRows result
                     then SQLiteExecuting ValidRow
                     else SQLiteExecuting InvalidRow)] } Eff IO StepResult
reset = Reset


getColumnName : Column -> { [SQLITE (SQLiteExecuting ValidRow)] } Eff IO String
getColumnName col = GetColumnName col

getColumnText : Column -> { [SQLITE (SQLiteExecuting ValidRow)] } Eff IO String
getColumnText col = GetColumnText col

getColumnInt : Column -> { [SQLITE (SQLiteExecuting ValidRow)] } Eff IO Int
getColumnInt col = GetColumnInt col

getColumnFloat : Column -> { [SQLITE (SQLiteExecuting ValidRow)] } Eff IO Float
getColumnFloat col = GetColumnFloat col

isColumnNull : Column -> { [SQLITE (SQLiteExecuting ValidRow)] } Eff IO Bool
isColumnNull col = IsColumnNull col

getColumnDataSize : Column -> { [SQLITE (SQLiteExecuting ValidRow)] } Eff IO Int
getColumnDataSize col = GetColumnDataSize col

finalise : { [SQLITE (SQLiteExecuting s)] ==>
             [SQLITE SQLiteConnected] } Eff IO ()
finalise = Finalise

cleanupPSFail : { [SQLITE (SQLitePSFail)] ==> [SQLITE ()] } Eff IO ()
cleanupPSFail = CleanupPSFail

cleanupBindFail : { [SQLITE (SQLiteFinishBindFail)] ==> [SQLITE ()] } Eff IO ()
cleanupBindFail = CleanupBindFail

-- Just makes it a tad nicer to write
executeStatement : { [SQLITE (SQLitePSSuccess Bound)] ==>
                     [SQLITE (if hasMoreRows result
                                then SQLiteExecuting ValidRow
                                else SQLiteExecuting InvalidRow)] } Eff IO StepResult
executeStatement = ExecuteStatement


getQueryError : Either QueryError b -> QueryError
getQueryError (Left qe) = qe
getQueryError _ = InternalError

total
multiBind' : List (Int, DBVal) -> { [SQLITE (SQLitePSSuccess Binding)] } Eff IO ()
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

multiBind : List (Int, DBVal) ->
            { [SQLITE (SQLitePSSuccess Binding)] ==>
              [SQLITE (maybe (SQLitePSSuccess Bound) (const SQLiteFinishBindFail) result)] }
            Eff IO (Maybe QueryError)
multiBind vals = do
  multiBind' vals
  finishBind



getRowCount' : StepResult ->
               { [SQLITE (SQLiteExecuting s)] ==> [SQLITE ()] }
               Eff IO (Either QueryError Int)
getRowCount' NoMoreRows   = do finalise
                               closeDB
                               return $ Left (ExecError "Unable to get row count")
getRowCount' StepFail     = do finalise
                               closeDB
                               return $ Left (ExecError "Error whilst getting row count")
getRowCount' {s=ValidRow} StepComplete = do last_insert_id <- getColumnInt 0
                                            finalise
                                            closeDB
                                            return $ Right last_insert_id
getRowCount' {s=InvalidRow} StepComplete = do finalise
                                              closeDB
                                              return $ Left (ExecError "Invalid row")
getRowCount' Unstarted    = do finalise
                               closeDB
                               return $ Left (ExecError "Not started")

getBindError : Maybe QueryError -> QueryError
getBindError (Just (BindingError be)) = (BindingError be)
getBindError _ = InternalError


getRowCount : { [SQLITE SQLiteConnected] ==> [SQLITE ()] } Eff IO (Either QueryError Int)
getRowCount = do
  let insert_id_sql = "SELECT last_insert_rowid()"
  sql_prep_res <- prepareStatement insert_id_sql
  case sql_prep_res of
    Left err => do cleanupPSFail
                   return (Left err)
    Right () =>
      do bind_res_2 <- finishBind
         case bind_res_2 of
           Just err => do let be = getBindError bind_res_2
                          cleanupBindFail
                          return $ Left be
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
                { [SQLITE ()] } Eff IO (Either QueryError Int)
executeInsert db_name query bind_vals =
  do db_res <- openDB db_name
     case db_res of
       Left err => return (Left err)
       Right () =>
         do ps_res <- prepareStatement query
            case ps_res of
              Left err => do cleanupPSFail
                             return (Left err)
              Right () =>
                do bind_res <- multiBind bind_vals
                   case bind_res of
                     Just err => do cleanupBindFail
                                    return (Left err)
                     Nothing  => executeIt
  -- split out to make typechecking faster
  where executeIt : { [SQLITE (SQLitePSSuccess Bound)] ==>
                      [SQLITE ()] }
                    Eff IO (Either QueryError Int)
        executeIt =
          do er_1 <- executeStatement
             case er_1 of
               StepFail => do finalise {s=ValidRow}
                              closeDB
                              return $ Left (ExecError "Error inserting")
               Unstarted => do finalise {s=ValidRow}
                               closeDB
                               return $ Left (ExecError "Internal error: 'unstarted' after execution")
               NoMoreRows => do finalise {s=InvalidRow}
                                getRowCount
               StepComplete => do finalise {s=ValidRow}
                                  getRowCount


-- Helper functions for selection from a DB
partial
collectResults : ({ [SQLITE (SQLiteExecuting ValidRow)] } Eff IO (List DBVal)) ->
                 { [SQLITE (SQLiteExecuting ValidRow)] ==>
                   [SQLITE (SQLiteExecuting InvalidRow)] } Eff IO ResultSet
collectResults fn =
  do results <- fn
     step_res <- nextRow
     case step_res of
       Unstarted => return $ results :: !(collectResults fn)
       StepFail => return $ results :: !(collectResults fn)
       StepComplete => return $ results :: !(collectResults fn)
       NoMoreRows => return [results]


-- Convenience function to abstract around some of the boilerplate code.
-- Takes in the DB name, query, a list of (position, variable value) tuples,
-- a function to process the returned data,
partial
executeSelect : (db_name : String) -> (q : String) -> List (Int, DBVal) ->
                ({ [SQLITE (SQLiteExecuting ValidRow)] } Eff IO (List DBVal)) ->
                { [SQLITE ()] } Eff IO (Either QueryError ResultSet)
executeSelect db_name q bind_vals fn =
  do Right () <- openDB db_name | Left err => return (Left err)
     Right () <- prepareStatement q | Left err => do cleanupPSFail
                                                     return $ Left err
     Nothing <- multiBind bind_vals | Just err => do cleanupBindFail
                                                     return $ Left err
     case !executeStatement of
       Unstarted => do res <- collectResults fn
                       finalise
                       closeDB
                       return $ Right res
       StepFail => do res <- collectResults fn
                      finalise
                      closeDB
                      return $ Right res
       StepComplete => do res <- collectResults fn
                          finalise
                          closeDB
                          return $ Right res
       NoMoreRows => do finalise
                        closeDB
                        return $ Right []

-- -}
-- -}
-- -}

-- Local Variables:
-- idris-packages: ("effects" "sqlite")
-- End:
