module DB.SQLite.SQLiteTest

import Effects
import DB.SQLite.SQLiteNew
import DB.SQLite.SQLiteCodes


testInsert : String -> Int -> { [SQLITE ()] } Eff IO (Either QueryError ())
testInsert name age =
  do open_db <- openDB "test.db"
     case open_db of
       Left err => return $ Left err
       Right () =>
         do let sql = "INSERT INTO `test` (`name`, `age`) VALUES (?, ?);"
            prep_res <- prepareStatement sql
            case prep_res of
              Left err => do cleanupPSFail ; return $ Left err
              Right () =>
                do bindText 1 name
                   bindInt 2 age
                   bind_res <- finishBind
                   case bind_res of
                     Just err => do cleanupBindFail ; return $ Left err
                     Nothing =>
                       case !executeStatement of
                         Unstarted => do finalise
                                         closeDB
                                         pure (Right ())
                         StepFail => do finalise
                                        closeDB
                                        pure (Right ())
                         StepComplete => do finalise
                                            closeDB
                                            pure (Right ())
                         NoMoreRows => do finalise
                                          closeDB
                                          pure (Right ())

{-


testSelect : Eff IO [SQLITE ()] (Either Int (List (String, String)))
testSelect = do
  open_db <- openDB "test.db"
  if_valid then do
    let sql = "SELECT `name`, `sql` FROM `sqlite_master`;"
    sql_prep_res <- prepareStatement sql
    if_valid then do 
      finishBind
      if_valid then do
        executeStatement
        results <- collectResults
        finaliseInvalid
        closeDB
        Effects.pure $ Right results
      else do cleanupBindFail
              Effects.pure $ Left (-1)
    else do cleanupPSFail
            Effects.pure $ Left (-2)
  else Effects.pure $ Left (-3)
  -}

namespace Main
  main : IO ()
  main = do select_res <- run [()] testSelect
            case select_res of
                 Left err => putStrLn $ "Error: " ++ (show err)
                 Right results => do traverse (putStrLn . show) results
                                     pure ()


{-
main : IO ()
main = do insert_res <- run [()] (testInsert "Simon" 21)
          case insert_res of 
            Left err => putStrLn $ "Error inserting" ++ (show err)
            Right _ => putStrLn $ "Operation completed successfully."
-}

-- -}
-- -}
-- -}
