module Schema

import SQLiteTypes

import Decidable.Equality
import Language.Reflection

%access public export
%default total

%auto_implicits on

infix 5 :::
data Attribute = (:::) String SQLiteType
%name Attribute attr,attr'

getName : Attribute -> String
getName (c:::_) = c

getTy : Attribute -> SQLiteType
getTy (_:::t) = t

attrEta : (attr : Attribute) -> (getName attr ::: getTy attr) = attr
attrEta (x ::: y) = Refl

attrInj : (c ::: t = c' ::: t') -> (c=c', t=t')
attrInj Refl = (Refl, Refl)

-- the first case forces it to get stuck if the constants are not in canonical form
foo : (x : String) -> (y : String) -> Dec (x = y)
foo "" "" = Yes Refl
foo x y with (decEq x y)
  foo x y | Yes _ = Yes (really_believe_me (Refl {x}))
  foo x y | No urgh = No urgh


implementation DecEq Attribute where
  decEq (x ::: y) (z ::: w) with (foo x z, decEq y w)
    decEq (x ::: y) (x ::: y) | (Yes Refl, Yes Refl) = Yes Refl
    decEq (x ::: y) (x ::: w) | (Yes Refl, No prf) = No $ prf . snd . attrInj
    decEq (x ::: y) (z ::: w) | (No prf, _) = No $ prf . fst . attrInj

data Schema = Nil | (::) Attribute Schema
%name Schema s,s'

append : (s1, s2 : Schema) -> Schema
append [] s2 = s2
append (attr :: s) s2 = attr :: (append s s2)

names : Schema -> List String
names [] = []
names ((n ::: _) :: s) = n :: names s


data HasCol : Schema -> Attribute -> Type where
  Here : HasCol (attr::s) attr
  There : HasCol s attr -> HasCol (attr'::s) attr

HasColNotEmpty : HasCol [] a -> Void
HasColNotEmpty Here impossible
HasColNotEmpty (There _) impossible

implementation Uninhabited (HasCol [] a) where
  uninhabited x = HasColNotEmpty x

decHasColLemma :  (HasCol s attr -> Void) ->
                  (attr' = attr -> Void) ->
                  HasCol (attr' :: s) attr -> Void
decHasColLemma h1 h2 Here = h2 Refl
decHasColLemma h1 h2 (There x) = h1 x

decHasCol : (s : Schema) -> (attr : Attribute) -> Dec (HasCol s attr)
decHasCol [] attr = No HasColNotEmpty
decHasCol (attr' :: s) attr with (decEq attr' attr)
  decHasCol (attr' :: s) attr' | (Yes Refl) = Yes Here
  decHasCol (attr' :: s) attr | (No f) with (decHasCol s attr)
    decHasCol (attr' :: s) attr | (No f) | (Yes x) = Yes (There x)
    decHasCol (attr' :: s) attr | (No f) | (No g) = No $ \h => decHasColLemma g f h


data SubSchema : Schema -> Schema -> Type where
  Empty : SubSchema [] s
  Head : (tailSub : SubSchema small large) ->
         (alsoThere : HasCol large attr) ->
         SubSchema (attr :: small) large

HasColNamed : Schema -> String -> Type
HasColNamed s col = (t : SQLiteType ** HasCol s (col ::: t))

decHasColNamed_lemma : ((HasColNamed s col) -> Void) -> ((col' = col) -> Void) ->
                       (t ** HasCol ((col' ::: ty) :: s) (col ::: t)) -> Void
decHasColNamed_lemma notThere notHere (ty ** Here)         = notHere Refl
decHasColNamed_lemma notThere notHere (ty ** (There more)) = notThere (ty ** more)


decHasColNamed : (s : Schema) -> (col : String) -> Dec (HasColNamed s col)
decHasColNamed [] col = No $ \h => HasColNotEmpty (snd h)
decHasColNamed ((col' ::: ty) :: s) col with (decEq col' col)
  decHasColNamed ((col ::: ty) :: s)  col | (Yes Refl) = Yes (ty ** Here)
  decHasColNamed ((col' ::: ty) :: s) col | (No f) with (decHasColNamed s col)
    decHasColNamed ((col' ::: ty) :: s) col | (No f) | (Yes x) =
      Yes (fst x ** There (snd x))
    decHasColNamed ((col' ::: ty) :: s) col | (No f) | (No g) = No (decHasColNamed_lemma g f)

colNames : Schema -> List String
colNames [] = []
colNames ((col ::: _) :: s) = col :: colNames s

data Disjointness : Type where
  Disjoint : Disjointness
  Overlap : (attr : Attribute) -> Disjointness

isDisjoint : (s1, s2 : Schema) -> Disjointness
isDisjoint [] s2 = Disjoint
isDisjoint (attr :: s) s2 with (decHasColNamed s2 (getName attr))
  isDisjoint (attr :: s) s2 | (Yes x) = Overlap attr
  isDisjoint (attr :: s) s2 | (No f) = isDisjoint s s2


