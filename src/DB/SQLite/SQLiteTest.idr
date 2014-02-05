module DB.SQLite.SQLiteTest

import Effects
import DB.SQLite.Effect
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




testSelect : { [SQLITE ()] } Eff IO (Either QueryError ResultSet)
testSelect =
  executeSelect "test.db" "SELECT `name`, `sql` FROM `sqlite_master`;" [] $
  do name <- getColumnText 0
     sql <- getColumnText 1
     return [DBText name, DBText sql]


namespace Main
  main : IO ()
  main = do select_res <- run $ testInsert "foo" 29
            case select_res of
                 Left err => putStrLn $ "Error: " ++ (show err)
                 Right () => putStrLn $ "Done"
            select_res <- run $ testSelect
            case select_res of
              Left err => putStrLn $ "Error reading: " ++ show err
              Right res => putStrLn (show res)

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
