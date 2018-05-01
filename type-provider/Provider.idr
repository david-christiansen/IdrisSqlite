module Provider

import DB.SQLite.Effect
import DB.SQLite.SQLiteCodes
import Effects

import Database
import ParserHack
import Queries
import Schema
import SQLiteTypes

%access export

%language TypeProviders

mkDB : ResultSet -> Either String (List (String, Schema))
mkDB [] = Right []
mkDB ([DBText v]::rest) =
  case getSchema (toLower v) of
    Nothing => Left ( "Couldn't parse schema '" ++ v ++ "'\n")
    Just (t, tbl) =>
      with Applicative
        Right List.(::) <*> Right (t, tbl) <*> mkDB rest
mkDB _ = Left "Couldn't understand SQLite output - wrong type"

getSchemas : (filename : String) -> Eff (Provider (DB filename)) [SQLITE ()] 
getSchemas file =
  do let ddlQuery = "SELECT `sql` FROM `sqlite_master` " ++
                    "WHERE NOT (sqlite_master.name LIKE \"sqlite%\");"
     resSet <- executeSelect file ddlQuery [] $
               do sql <- getColumnText 0
                  pure [DBText sql]
     case resSet of
       Left err => pure (Error $ "Error reading '" ++ file ++ "': " ++ (show err))
       Right res => case mkDB res of
                      Left err => pure (Error err)
                      Right db => pure (Provide (MkDB file db))

getRow : (s : Schema) -> SimpleEff.Eff (Row s) [SQLITE (SQLiteExecuting ValidRow)]
getRow s = go 0 s
  where go : Int -> (s : Schema) -> Eff (Row s) [SQLITE (SQLiteExecuting ValidRow)]
        go i []          = pure []
        go i ((_ ::: ty) :: s) = [| getCol ty :: go (i+1) s |]
          where getCol : (t : SQLiteType) -> Eff (interpSql t) [SQLITE (SQLiteExecuting ValidRow)]
                getCol TEXT = getColumnText i
                getCol INTEGER = do int <- getColumnInt i
                                    pure (cast int)
                getCol REAL = getColumnFloat i
                getCol (NULLABLE x) = do nullp <- isColumnNull i
                                         case nullp of
                                           True => pure Nothing
                                           False => do val <- getCol x
                                                       pure (Just val)

collectRows : (s : Schema) -> Eff (Table s) [SQLITE (SQLiteExecuting ValidRow)] [SQLITE (SQLiteExecuting InvalidRow)]
collectRows s = do row <- getRow s
                   case !nextRow of
                     Unstarted => pure $ row :: !(collectRows s)
                     StepFail => pure $ row :: !(collectRows s)
                     StepComplete => pure $ row :: !(collectRows s)
                     NoMoreRows => pure [row]

query : {file : String} -> {db : DB file} -> Query db s -> Eff (Either QueryError (Table s)) [SQLITE ()]
query {file=fn} q =
  case !(openDB fn) of
    Left err => pure $ Left err
    Right () =>  -- FIXME should really use binding
      case !(prepareStatement (compileQuery q)) of
        Left err => do cleanupPSFail
                       pure $ Left err
        Right () =>
          case !finishBind of
            Just err => do cleanupBindFail ; pure $ Left err
            Nothing =>
              case !executeStatement of
                Unstarted => do rs <- collectRows _
                                finalise
                                closeDB
                                pure (Right rs)
                StepFail => do rs <- collectRows _
                               finalise
                               closeDB
                               pure (Right rs)
                StepComplete => do rs <- collectRows _
                                   finalise
                                   closeDB
                                   pure (Right rs)
                NoMoreRows => do finalise
                                 closeDB
                                 pure (Right [])


 
