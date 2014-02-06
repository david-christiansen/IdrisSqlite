module Test

import Provider

import Database
import Queries

%language TypeProviders

%link C "sqlite3api.o"
%include C "sqlite3api.h"
%lib C "sqlite3"

%provide (db : DB "test.sqlite") with run (getSchemas "test.sqlite")

foos : Query db ["foo":::INTEGER]
foos = SELECT (["foo":::INTEGER]) FROM "test" WHERE (Col "foo" == Col "foo")

people : Query db ["name":::TEXT]
people = SELECT ["name":::TEXT] FROM "people" WHERE 1

transit : Query db ["name":::TEXT, "wheels":::INTEGER]
transit = SELECT ["name":::TEXT, "wheels":::INTEGER]
          FROM "people" * "transport"
          WHERE Col "name" == Col "owner"

printRes : Query db s -> IO ()
printRes q = do res <- runInit [()] (query q)
                case res of
                  Left err => putStrLn (show err)
                  Right table => putStrLn (showTable _ table)
namespace Main
  main : IO ()
  main = do printRes foos
            printRes people
            printRes transit
            putStrLn "ok"


