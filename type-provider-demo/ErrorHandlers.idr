module ErrorHandlers

import Queries
import Language.Reflection
import Language.Reflection.Errors

%language ErrorReflection

getAttrs : TT -> List ErrorReportPart
getAttrs (App (App (P _ (NS (UN ":::") _) _) a) b) = [SubReport
                                                      [TermPart a,
                                                       TextPart ":::",
                                                       TermPart b]]
getAttrs (App (App (P _ (NS (UN "::") _) _) hd) tl) = getAttrs hd ++ getAttrs tl
getAttrs (App (App (P _ (NS (UN "append") _) _) a) b) = getAttrs a ++ getAttrs b
getAttrs x = []


getHasColErr : TT -> Maybe (List ErrorReportPart)
getHasColErr (App (App hasCol s) want) = [| getWant want ++
                                            pure ([TextPart "in"] ++ getAttrs s) |]
  where getWant : TT -> Maybe (List ErrorReportPart)
        getWant (App (App _ (TConst (Str c))) typ) = pure [ TextPart "The column"
                                                          , TermPart (TConst (Str c))
                                                          , TextPart "was not found with type"
                                                          , TermPart typ]
        getWant _ = Nothing
getHasColErr _ = Nothing


%error_handler
notFound : Err -> Maybe (List ErrorReportPart)
notFound (Msg "") = Just []
notFound (CantUnify x tm tm' err xs y) = Nothing
notFound (CantConvert tm tm' xs) = Nothing
notFound (CantSolveGoal (App (App (App (App equals _) _) l) _) xs) = Just (getSchemas l)
  where getSchemas (App (App _ a) b) = [TextPart "The schema"] ++ getAttrs a ++ [TextPart "\nisn't a subschema of"] ++ getAttrs b
        getSchemas _ = []
notFound (CantSolveGoal tm xs) = getHasColErr tm
notFound _ = Nothing
