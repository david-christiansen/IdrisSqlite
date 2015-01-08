module ErrorHandlers

import Queries
import Schema
import SQLiteTypes
import Language.Reflection
import Language.Reflection.Errors

%language ErrorReflection

getAttrs : TT -> List ErrorReportPart
getAttrs `(~a ::: ~b) = [SubReport
                          [ TermPart a
                          , TextPart ":::"
                          , TermPart b] ]
getAttrs `(Schema.(::) ~hd ~tl) = getAttrs hd ++ getAttrs tl
getAttrs `(Schema.append ~a ~b) = getAttrs a ++ getAttrs b
getAttrs x = []


getHasColErr : TT -> Maybe (List ErrorReportPart)
getHasColErr `(HasCol ~s ~want) = [| getWant want ++
                                     pure ([TextPart "in the schema"] ++ getAttrs s) |]
  where getWant : TT -> Maybe (List ErrorReportPart)
        getWant (App (App _ (TConst (Str c))) typ) = pure [ TextPart "The column"
                                                    , TermPart (TConst (Str c))
                                                    , TextPart "was not found with type"
                                                    , TermPart typ]
        getWant _ = Nothing
getHasColErr _ = Nothing


%error_handler
notFound : Err -> Maybe (List ErrorReportPart)
notFound (CantUnify x tm tm' err xs y) = Nothing
notFound (CantConvert tm tm' xs) = Nothing
notFound (CantSolveGoal (App (App (App (App equals _) _) l) _) xs) = Just (getSchemas l)
  where getSchemas (App (App _ a) b) = [TextPart "The schema"] ++ getAttrs a ++ [TextPart "\nisn't a subschema of"] ++ getAttrs b
        getSchemas _ = []
notFound (CantSolveGoal tm xs) = getHasColErr tm
notFound _ = Nothing
