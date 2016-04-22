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
%language ErrorReflection

-- Use the SQLite dependencies in generated code
%link C "sqlite3api.o"
%include C "sqlite3api.h"
%lib C "sqlite3"

%auto_implicits off

%provide (db : DB "test.sqlite") with run {m=IO} (getSchemas "test.sqlite")

%error_handlers Col    ok hasColErr
%error_handlers Select ok notSubSchemaErr

speakers : Query db ["name":::TEXT, "bio":::TEXT]
speakers = SELECT ["name":::TEXT, "bio":::TEXT] FROM "speaker" WHERE 1

talks : Query db ["title":::TEXT, "abstract":::TEXT]
talks = SELECT ["title":::TEXT, "abstract":::TEXT] FROM "talk" WHERE 1


program : Query db ["name":::TEXT, "title":::TEXT, "abstract":::TEXT]
program = SELECT ["name":::TEXT, "title":::TEXT, "abstract":::TEXT]
          FROM "speaker" * "talk"
          WHERE Col "id" == Col "speaker_id"

printRes : {s : Schema} -> Query db s -> IO ()
printRes q = do res <- runInit [()] (query q)
                case res of
                  Left err => putStrLn (show err)
                  Right table => putStrLn (showTable _ table)
namespace Main
  main : IO ()
  main = do putStrLn "The speakers are:"
            printRes speakers
            putStrLn "The talks are:"
            printRes talks
            putStrLn "Conference program"
            printRes program
            putStrLn "ok"
