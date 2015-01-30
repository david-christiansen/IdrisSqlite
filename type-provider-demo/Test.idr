module Test

import Effects
import DB.SQLite.Effect

import Provider
import Database
import Queries
import ErrorHandlers
import Schema
import SQLiteTypes


%language TypeProviders

%link C "sqlite3api.o"
%include C "sqlite3api.h"
%lib C "sqlite3"




%provide (db : DB "test.sqlite") with run (getSchemas "test.sqlite")




foos : Query db ["foo":::INTEGER]
foos = SELECT (["foo":::INTEGER]) FROM "test" WHERE (Col "food" == Col "food")






people : Query db ["name":::TEXT]
people = SELECT ["name":::TEXT] FROM "people" WHERE 1





transit : Query db ["name":::TEXT, "age":::NULLABLE INTEGER, "wheels":::INTEGER, "description" ::: TEXT]
transit = SELECT ["name":::TEXT, "age":::NULLABLE INTEGER, "wheels":::INTEGER, "description":::TEXT]
          FROM "people" * "transport"
          WHERE Col "name" == Col "owner"



printRes : Query db s -> IO ()
printRes q = do res <- runInit [()] (query q)
                case res of
                  Left err => putStrLn (show err)
                  Right table => putStrLn (showTable _ table)
namespace Main
  main : IO ()
  main = do --printRes foos
            printRes people
            printRes transit
            putStrLn "ok"


-- -}
-- -}
-- -}
-- -}

-- Local Variables:
-- idris-packages: ("lightyear" "sqlite" "effects")
-- End:
