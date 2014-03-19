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

emptyDBNoTables : HasTable [] t s -> _|_
emptyDBNoTables Here impossible

instance Uninhabited (HasTable [] t s) where
  uninhabited = emptyDBNoTables

decHasTable_lemma1 : ((HasTable db t s) -> _|_) ->
                     (t' = t -> _|_) ->
                     HasTable ((t',s')::db) t s -> _|_
decHasTable_lemma1 notThere notName Here = notName refl
decHasTable_lemma1 notThere notName (There there) = notThere there

decHasTable_lemma2 : (notThere : (HasTable db t s) -> _|_) ->
                     ((s' = s) -> _|_) ->
                     (HasTable ((t', s') :: db) t s) -> _|_
decHasTable_lemma2 notThere notSchema Here = notSchema refl
decHasTable_lemma2 notThere notSchema (There there) = notThere there

decHasTable : (db : List (String, Schema)) -> (t : String) -> (s : Schema) -> Dec (HasTable db t s)
decHasTable [] t s = No uninhabited
decHasTable ((t',s')::db) t s with (decHasTable db t s)
  decHasTable ((t',s')::db) t s | (Yes x) = Yes (There x)
  decHasTable ((t',s')::db) t s | (No notThere) with (decEq t' t, decEq s' s)
    decHasTable ((t,s)::db) t s | (No notThere) | (Yes refl, Yes refl) = Yes Here
    decHasTable ((t',s')::db) t s | (No notThere) | (No nope, _) =
      No $ decHasTable_lemma1 notThere nope
    decHasTable ((t',s')::db) t s | (No notThere) | (_, No nope) =
      No $ decHasTable_lemma2 notThere nope
