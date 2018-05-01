module DB.SQLite.SQLiteTest

import Effects
import DB.SQLite.Effect
import DB.SQLite.SQLiteCodes


testInsert : String -> Int -> Eff (Either QueryError ()) [SQLITE ()]
testInsert name age =
  do open_db <- openDB "test.db"
     case open_db of
       Left err => pure $ Left err
       Right () =>
         do let sql = "INSERT INTO `test` (`name`, `age`) VALUES (?, ?);"
            prep_res <- prepareStatement sql
            case prep_res of
              Left err => do cleanupPSFail ; pure $ Left err
              Right () =>
                do bindText 1 name
                   bindInt 2 age
                   bind_res <- finishBind
                   case bind_res of
                     Just err => do cleanupBindFail ; pure $ Left err
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




testSelect : Eff (Either QueryError ResultSet) [SQLITE ()]
testSelect =
  executeSelect "test.db" "SELECT `name`, `sql` FROM `sqlite_master`;" [] $
  do name <- getColumnText 0
     sql <- getColumnText 1
     pure [DBText name, DBText sql]


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


-- -}
-- -}
-- -}
