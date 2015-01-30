module Database

import Schema

import Decidable.Equality

data DB : String -> Type where
  MkDB : (dbFile : String) ->
         (dbTables : List (String, Schema)) -> DB dbFile

%name DB db

data HasTable : List (String, Schema) -> String -> Schema -> Type where
  Here : HasTable ((name, s)::ts) name s
  There : HasTable ts name s ->
          HasTable ((name',s')::ts) name s

