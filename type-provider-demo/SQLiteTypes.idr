module SQLiteTypes

import Decidable.Equality

%default total


public export data SQLiteType = TEXT | INTEGER | REAL
                | NULLABLE SQLiteType

export interpSql : SQLiteType -> Type
interpSql TEXT = String
interpSql INTEGER = Integer
interpSql REAL = Double
interpSql (NULLABLE x) = Maybe (interpSql x)

equalSql : (t : SQLiteType) -> (x, y : interpSql t) -> Bool
equalSql TEXT x y = x == y
equalSql INTEGER x y = x == y
equalSql REAL x y = x == y
equalSql (NULLABLE ty) (Just x) (Just y) = equalSql ty x y
equalSql (NULLABLE ty) Nothing Nothing = True
equalSql (NULLABLE ty) _ _ = False

export showSql : (t : SQLiteType) -> (x : interpSql t) -> String
showSql TEXT x = show x
showSql INTEGER x = show x
showSql REAL x = show x
showSql (NULLABLE ty) (Just x) = showSql ty x
showSql (NULLABLE ty) Nothing = "null"


integerNotText : INTEGER = TEXT -> Void
integerNotText Refl impossible

realNotText : REAL = TEXT -> Void
realNotText Refl impossible

nullableNotText : NULLABLE t = TEXT -> Void
nullableNotText Refl impossible

realNotInteger : REAL = INTEGER -> Void
realNotInteger Refl impossible

nullableNotInteger : NULLABLE t = INTEGER -> Void
nullableNotInteger Refl impossible

nullableNotReal : NULLABLE t = REAL -> Void
nullableNotReal Refl impossible

export implementation DecEq SQLiteType where
  decEq TEXT TEXT            = Yes Refl
  decEq INTEGER TEXT         = No integerNotText
  decEq REAL TEXT            = No realNotText
  decEq (NULLABLE x) TEXT    = No nullableNotText
  decEq TEXT INTEGER         = No $ integerNotText . sym
  decEq INTEGER INTEGER      = Yes Refl
  decEq REAL INTEGER         = No realNotInteger
  decEq (NULLABLE x) INTEGER = No nullableNotInteger
  decEq TEXT REAL            = No $ realNotText . sym
  decEq INTEGER REAL         = No $ realNotInteger . sym
  decEq REAL REAL            = Yes Refl
  decEq (NULLABLE x) REAL    = No nullableNotReal
  decEq TEXT (NULLABLE x)    = No $ nullableNotText . sym
  decEq INTEGER (NULLABLE x) = No $ nullableNotInteger . sym
  decEq REAL (NULLABLE x)    = No $ nullableNotReal . sym
  decEq (NULLABLE y) (NULLABLE x) with (decEq y x)
    decEq (NULLABLE x) (NULLABLE x) | (Yes Refl) = Yes Refl
    decEq (NULLABLE y) (NULLABLE x) | (No prf) = No $ prf . inside
      where inside : NULLABLE a = NULLABLE b -> a = b
            inside Refl = Refl
