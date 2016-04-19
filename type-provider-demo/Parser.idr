module Parser

import Lightyear.Core
import Lightyear.Strings
import Lightyear.Combinators
import Queries

sqltype : Parser SQLiteType
sqltype = the (Parser _) $
          (do token "int"  <|> token "integer"
              pure INTEGER)
      <|> (do token "text" <|> token "string"
              pure TEXT)
      <|> (do token "real" <|> token "float"
              pure REAL)

name : Parser String
name = do n <- many (satisfy (\c => c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z'))
          return (pack n)

nullable : Parser Bool
nullable = (do token "not"
               token "null"
               return False)
       <|> return True


sqlCol : Parser Attribute
sqlCol = do n <- name
            space
            ty <- sqltype
            null <- nullable
            pure (n:::(if null then NULLABLE ty else ty))

comma : Parser ()
comma = char ','


cols : Parser Schema
cols = do cols <- sepBy sqlCol (space $> comma $> space)
          pure (toSchema cols)
  where toSchema : List Attribute -> Schema
        toSchema [] = []
        toSchema (x::xs) = x :: toSchema xs



table : Parser (String, Schema)
table = do token "create"
           token "table"
           n <- name
           space
           token "("
           cs <- cols
           space
           token ")"
           pure (n,cs)

