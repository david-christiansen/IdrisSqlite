module ParserHack
import Schema
import SQLiteTypes

%access export

people : String
people = "CREATE TABLE \"people\" (\"id\" INTEGER PRIMARY KEY  AUTOINCREMENT  NOT NULL  UNIQUE , \"name\" VARCHAR NOT NULL , \"age\" INTEGER)"

--quote : Char
--quote = '\"'

--createTable : Parser Char List ()
--createTable = str (unpack "CREATE") ~ many1 space ~ str (unpack "TABLE") ^^^ ()

-- schema : Parser String
-- schema = do createTable
--             many1 space
--             is quote
--             res <- many1 (isNot quote)
--             is quote
--             many1 space
--             return (pack res)
-- --            sequence_ [ is quote, many1 space, is '(']
-- --            return (pack res)

dropPrefixBy : (a -> a -> Bool) -> List a -> List a -> Maybe (List a)
dropPrefixBy p [] ys = Just ys
dropPrefixBy p (x::xs) [] = Nothing
dropPrefixBy p (x::xs) (y::ys) = if p x y then dropPrefixBy p xs ys else Nothing

getWhile : (a -> Bool) -> List a -> (List a, List a)
getWhile p [] = ([], [])
getWhile p (x::xs) with (p x)
  | True = let (ok, rest) = getWhile p xs
           in (x :: ok, rest)
  | False = ([], x::xs)



isPrefix : (Eq a) => List a -> List a -> Bool
isPrefix [] _ = True
isPrefix (x::xs) [] = False
isPrefix (x::xs) (y::ys) = x == y && isPrefix xs ys

subList : (Eq a) => List a -> List a -> Bool
subList [] _ = False
subList (x::xs) [] = False
subList (x::xs) (y::ys) = (x == y && isPrefix xs ys) || subList (x::xs) ys

isNullable : String -> Bool
isNullable = not . subList ["NOT", "NULL"] . split (==' ')

getType : String -> Maybe String
getType opts = List.find (isType . toUpper) (split (==' ') opts)
    where isType : String -> Bool
          isType x = List.elem x ["INTEGER", "VARCHAR", "TEXT", "INT" ]


colNameTypeNullable : String -> Maybe (String, String, Bool)
colNameTypeNullable col = case dropPrefixBy (==) [] (unpack (trim col)) of
                            Nothing   => Nothing
                            Just rest => let (name, rest') = (getWhile (/= ' ') rest)
                                         in case dropPrefixBy (==) [' '] rest' of
                                            Just rest'' => case getType (pack rest'') of
                                                             Just tp => Just (pack name, tp, isNullable (toUpper (pack rest'')))
                                                             Nothing => Nothing
                                            Nothing     => Nothing

nameCols : String -> Maybe (String, List String)
nameCols schema = case dropPrefixBy (\x,y => toLower x == toLower y) (unpack "create table ") (unpack schema) of
                    Nothing => Nothing
                    Just rest => let (name, rest') = (getWhile (/= ' ') rest)
                                 in case dropPrefixBy (==) [' ', '('] rest' of
                                      Just rest'' => case dropPrefixBy (==) [')'] (reverse rest'') of
                                                       Just rest''' =>
                                                         Just (pack name, split (==',') (pack (reverse rest''')))
                                                       Nothing => Nothing
                                      Nothing => Nothing

parse : String -> Maybe (String, List (String, String, Bool))
parse schema = case nameCols schema of
                 Just (n, cols) => case sequence {f=Maybe} (map colNameTypeNullable (filter isColumn cols)) of
                                     Just cols' => Just (n, cols')
                                     Nothing => Nothing
                 Nothing => Nothing
  where isColumn : String -> Bool
        isColumn col = not $ isPrefixOf "foreign" (toLower (trim col))
toSchema : List (String, String, Bool) -> Maybe Schema
toSchema [] = Just []
toSchema ((colName, colT, nullable)::cols) = do tp <- getType (toUpper colT) nullable
                                                rest <- toSchema cols
                                                return ((colName:::tp) :: rest)
    where getType : String -> Bool -> Maybe SQLiteType
          getType t         True  = map NULLABLE (getType t False)
          getType "VARCHAR" False = Just TEXT
          getType "TEXT"    False = Just TEXT
          getType "INTEGER" False = Just INTEGER
          getType "INT"     False = Just INTEGER
          getType "REAL"    False = Just REAL
          getType _         False = Nothing

getSchema : String -> Maybe (String, Schema)
getSchema str = do nameCols <- parse str
                   tableSchema <- toSchema (snd nameCols)
                   Just (fst nameCols, tableSchema)
