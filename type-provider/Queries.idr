module Queries

import SQLiteTypes
import Schema
import Database

import Decidable.Equality
import Language.Reflection
import Language.Reflection.Errors
import Language.Reflection.Utils

%access public export
%default total
%language ErrorReflection

namespace Row0
  data Row : Schema -> Type where
    Nil : Row []
    (::) : (x : interpSql t) -> (xs : Row s) -> Row ((c:::t) :: s)
  %name Row r1,r2,r3

  getSchema : Row s -> Schema
  getSchema {s} _ = s

  getCol : HasCol s attr -> Row s -> interpSql (getTy attr)
  getCol Here (x :: xs) = x
  getCol (There at) (y :: xs) = getCol at xs

  projectRow : (SubSchema s1 s2) -> Row s2 -> Row s1
  projectRow Empty r1 = []
  projectRow {s1=(attr::small)} (Head tailSub alsoThere) r ?= {projectRow_lemma}
     let head = getCol alsoThere r in
     let tail = projectRow tailSub r in
     the (Row ((getName attr ::: getTy attr)::small)) (head::tail)

  showRow : (s : Schema) -> Row s -> String
  showRow []               []  = "\n"
  showRow ((_ ::: t) :: s) (x :: xs) = showSql t x ++ "|" ++ showRow s xs

namespace Table
  data Table : Schema -> Type where
    Nil : Table s
    (::) : (r : Row s) -> (rs : Table s) -> Table s


  showTable' : (s : Schema) -> Table s -> String
  showTable' s [] = ""
  showTable' s (r :: rs) = showRow s r ++ showTable' s rs

  showHeader : Schema -> String
  showHeader [] = "\n"
  showHeader ((col ::: _) :: s) = col ++ "|" ++ showHeader s

  showTable : (s : Schema) -> Table s -> String
  showTable s t = showHeader s ++ showTable' s t


namespace Expr

  data Expr : Schema -> SQLiteType -> Type where
    Col : (c : String) -> {t : SQLiteType} ->
          {auto ok : HasCol s (c:::t)} ->
          Expr s t
    (==) : Expr s t -> Expr s t -> Expr s INTEGER
    (>) : Expr s INTEGER -> Expr s INTEGER -> Expr s INTEGER
    (<) : Expr s INTEGER -> Expr s INTEGER -> Expr s INTEGER
    (>=) : Expr s INTEGER -> Expr s INTEGER -> Expr s INTEGER
    (<=) : Expr s INTEGER -> Expr s INTEGER -> Expr s INTEGER
    Length : Expr s TEXT -> Expr s INTEGER
    Not : Expr s INTEGER -> Expr s INTEGER
    CstI : Integer -> Expr s INTEGER

  compileOp : String -> String -> String -> String
  compileOp op x y = "(" ++ x ++ ") " ++ op ++ " (" ++ y ++ ")"

  compileExpr : Expr s t -> String
  compileExpr (Col c) = "`" ++ c ++ "`"
  compileExpr (x == y) = compileOp "==" (compileExpr x) (compileExpr y)
  compileExpr (x > y) = compileOp ">" (compileExpr x) (compileExpr y)
  compileExpr (x < y) = compileOp "<" (compileExpr x) (compileExpr y)
  compileExpr (x >= y) = compileOp ">=" (compileExpr x) (compileExpr y)
  compileExpr (x <= y) = compileOp "<=" (compileExpr x) (compileExpr y)
  compileExpr (Length x) = "LENGTH(" ++ compileExpr x ++ ")"
  compileExpr (Not x) = "NOT(" ++ compileExpr x ++ ")"
  compileExpr (CstI i) = show i

  fromInteger : Integer -> Expr s INTEGER
  fromInteger = CstI


namespace Query
  %reflection
  reflectListPrf : List a -> Tactic
  reflectListPrf [] = Refine (UN "Here") `Seq` Solve
  reflectListPrf (x :: xs)
       = Try (Refine (UN "Here") `Seq` Solve)
             (Refine (UN "There") `Seq` (Solve `Seq` reflectListPrf xs))
  -- TMP HACK! FIXME!
  -- The evaluator needs a 'function case' to know its a reflection function
  -- until we propagate that information! Without this, the _ case won't get
  -- matched.
  --reflectListPrf (x ++ y) = Refine "Here" `Seq` Solve
  reflectListPrf _ = Refine (UN "Here") `Seq` Solve

  %reflection
  solveHasTable : Type -> Tactic
  solveHasTable (HasTable ts n s) = reflectListPrf ts `Seq` Solve
  solveHasTable (HasTable (x ++ y) n s) = Solve

  data Tables : DB file -> Schema -> Type where
    T : (name : String) ->
        {default tactics { byReflection solveHasTable; }
         ok : HasTable db name s} ->
        Tables (MkDB file db) s
    (*) : (t1 : String) ->
          {auto
           ok : HasTable db t1 s1} ->
          Tables (MkDB file db) s2 ->
          {auto disj : isDisjoint s1 s2 = Disjoint} ->
          Tables (MkDB file db) (append s1 s2)

  implicit
  toTables : (tbl : String) ->
             {auto
              ok : HasTable db tbl s} ->
             Tables (MkDB name db) s
  toTables tbl {ok = ok} = T tbl {ok = ok}

  compileTables : {db : DB f} -> Tables db s -> String
  compileTables (T n) = n
  compileTables (x * y) = x ++ ", " ++ compileTables y

  data Cmd : DB f -> Type where
    Insert : (into : String) -> (s : Schema) ->
             {default tactics { byReflection solveHasTable; }
              ok : HasTable db into s} ->
             (values : Table s) ->
             Cmd (MkDB f db)
    Delete : (from : String) -> (s : Schema) ->
             {default tactics { byReflection solveHasTable; }
              ok : HasTable db from s} ->
             (when : Expr s INTEGER) ->
             Cmd (MkDB f db)

  syntax INSERT INTO [table] AS [schema] VALUES [values] = Insert table schema values
  syntax DELETE FROM [table] AS [schema] WHEN [when] = Delete table schema when


  data Query : DB f -> Schema -> Type where
    Select : {db : DB f} -> Tables db s -> Expr s INTEGER -> (s' : Schema) ->
             {auto ok : SubSchema s' s} ->
             Query db s'

  syntax SELECT [schema] FROM [tables] WHERE [expr] = Select tables expr schema

  compileQuery : {db : DB f} -> Query db proj -> String
  compileQuery (Select ts expr proj) = "SELECT " ++
                                       cols ++
                                       " FROM " ++
                                       compileTables ts ++
                                       " WHERE " ++
                                       compileExpr expr ++
                                       ";"
    where cols : String
          cols = Foldable.concat . List.intersperse ", " . colNames $ proj

---------- Proofs ----------

Queries.Row0.projectRow_lemma = proof
  intros
  rewrite (attrEta attr)
  exact value


