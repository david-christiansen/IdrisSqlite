module ErrorHandlers

import Queries
import Schema
import SQLiteTypes
import Language.Reflection
import Language.Reflection.Errors

%language ErrorReflection

||| Convert a reflected schema to a nice formatted error view
getAttrs : TT -> List ErrorReportPart
getAttrs `(~a ::: ~b) = [SubReport
                          [ TermPart a
                          , TextPart ":::"
                          , TermPart b] ]
getAttrs `(Schema.(::) ~hd ~tl) = getAttrs hd ++ getAttrs tl
getAttrs `(Schema.append ~a ~b) = getAttrs a ++ getAttrs b
getAttrs x = []


||| Rewrite column missing errors
hasColErr : Err -> Maybe (List ErrorReportPart)
hasColErr (CantSolveGoal `(HasCol ~s ~want) _) =
  [| getWant want ++
     pure ([TextPart "in the schema"] ++ getAttrs s) |]
  where getWant : TT -> Maybe (List ErrorReportPart)
        getWant `(~c ::: ~typ : Attribute)=
          pure [ TextPart "The column"
               , TermPart c
               , TextPart "was not found with type"
               , TermPart typ
               ]
        getWant _ = Nothing
hasColErr _ = Nothing


||| Rewrite subschema errors
notSubSchemaErr : Err -> Maybe (List ErrorReportPart)
notSubSchemaErr (CantSolveGoal `(SubSchema ~s1 ~s2) ctxt) =
  Just $ [TextPart "Bad schema:"] ++
         getAttrs s1 ++
         [SubReport $
           [TextPart "Expected subschema of"] ++
            getAttrs s2]
notSubSchemaErr (CantSolveGoal (App (App (App (App equals _) _) l) _) xs) = getSchemas l
  where getSchemas (App (App _ s1) s2) =
          Just $ [TextPart "Bad schema:"] ++
                 getAttrs s1 ++
                 [SubReport $
                   [TextPart "Expected subschema of"] ++
                    getAttrs s2]
        getSchemas _ = Nothing
notSubSchemaErr _ = Nothing
