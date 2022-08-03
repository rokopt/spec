module Library.IdrisUtils

import public Data.Maybe
import public Data.List
import public Data.List.Reverse
import public Data.Nat
import public Data.Vect
import public Data.Fin
import public Data.DPair
import public Data.Bool
import public Decidable.Decidable
import public Decidable.Equality
import public Control.Function
import public Control.Relation
import public Control.Order
import public Control.Monad.Identity
import public Data.Binary
import public Data.Nat.Properties
import public Data.Nat.Exponentiation
import public Data.Binary.Digit
import public Syntax.PreorderReasoning

%default total

infixr 1 |>
public export
(|>) : {0 a, b, c : Type} -> (a -> b) -> (b -> c) -> (a -> c)
(|>) = flip (.)

-- Like Idris's standard `Subset`, but with even the `pred` type
-- parameter erased.
public export
record Subset0 (type : Type) (0 pred : type -> Type) where
  constructor Element0
  fst : type
  0 snd : pred fst

public export
curry : {0 p : a -> Type} -> (Subset0 a p -> c) -> (x : a) -> (0 _ : p x) -> c
curry f x y = f $ Element0 x y

public export
uncurry : {0 p : a -> Type} -> ((x : a) -> (0 _ : p x) -> c) -> Subset0 a p -> c
uncurry f s = f s.fst s.snd

export
elementInjectiveFst : Element0 x p = Element0 y q -> x = y
elementInjectiveFst Refl = Refl

export
elementInjectiveSnd : Element0 x p = Element0 x q -> p = q
elementInjectiveSnd Refl = Refl

public export
bimap : (f : a -> b) -> (0 _ : forall x. p x -> q (f x)) ->
  Subset0 a p -> Subset0 b q
bimap f g (Element0 x y) = Element0 (f x) (g y)

public export
Eq type => Eq (Subset0 type pred) where
  (==) = (==) `on` fst

public export
Ord type => Ord (Subset0 type pred) where
  compare = compare `on` fst

public export
Show type => Show (Subset0 type pred) where
  show = show . fst

public export
boolToDigit : Bool -> Digit
boolToDigit True = I
boolToDigit False = O

public export
lteTolt : {m, n : Nat} -> LTE m n -> Not (m = n) -> LT m n
lteTolt {m=0} {n=Z} LTEZero neq = void $ neq Refl
lteTolt {m=0} {n=(S n)} LTEZero neq = LTESucc LTEZero
lteTolt {m=(S m)} {n=(S n)} (LTESucc x) neq =
  LTESucc $ lteTolt {m} {n} x (\eq => case eq of Refl => neq Refl)

public export
lteAddLeft : (m, n : Nat) -> LTE n (m + n)
lteAddLeft m n = rewrite plusCommutative m n in lteAddRight {m} n

public export
compareNatSucc : (n : Nat) -> compareNat n (S n) = LT
compareNatSucc Z = Refl
compareNatSucc (S n) = compareNatSucc n

public export
lteZeroIsZero : {n : Nat} -> LTE n 0 -> 0 = n
lteZeroIsZero {n=Z} _ = Refl
lteZeroIsZero {n=(S _)} lt = void $ succNotLTEzero lt

public export
lteSuccEitherEqLte : {m, n : Nat} -> LTE m (S n) -> Either (m = S n) (LTE m n)
lteSuccEitherEqLte {m} {n} lte with (decEq m (S n))
  lteSuccEitherEqLte {m} {n} lte | Yes eq =
    Left eq
  lteSuccEitherEqLte {m} {n} lte | No neq =
    Right $ fromLteSucc $ lteTolt lte neq

public export
voidF : (a : Type) -> Void -> a
voidF _ x = void x

public export
IsTrue : Bool -> Type
IsTrue b = b = True

public export
IsJustTrue : {a : Type} -> Maybe a -> Type
IsJustTrue x = isJust x = True

public export
repeat : {0 x : Type} -> (x -> x) -> Nat -> x -> x
repeat f Z e = e
repeat f (S n) e = f (repeat f n e)

public export
fromIsJust : {a : Type} -> {x : Maybe a} -> IsJustTrue x -> a
fromIsJust {x=(Just x)} Refl = x
fromIsJust {x=Nothing} Refl impossible

public export
IsYesTrue : {a : Type} -> Dec a -> Type
IsYesTrue x = isYes x = True

public export
fromIsYes : {a : Type} -> {x : Dec a} -> IsYesTrue x -> a
fromIsYes {x=(Yes x)} Refl = x
fromIsYes {x=(No n)} Refl impossible

public export
equalNatCorrect : {m : Nat} -> equalNat m m = True
equalNatCorrect {m=Z} = Refl
equalNatCorrect {m=(S m')} = equalNatCorrect {m=m'}

public export
predLen : {0 a : Type} -> List a -> Nat
predLen = pred . length

public export
magmaFromNonEmptyList : {a : Type} -> (a -> a -> a) -> a -> List a -> a
magmaFromNonEmptyList f x [] = x
magmaFromNonEmptyList f x (x' :: l) = f x $ magmaFromNonEmptyList f x' l

public export
monoidFromList : {a : Type} -> a -> (a -> a -> a) -> List a -> a
monoidFromList id compose [] = id
monoidFromList id compose (x :: l) = magmaFromNonEmptyList compose x l

public export
pairInj1 : {a, b : Type} -> {p, p' : (a, b)} -> p = p' -> fst p = fst p'
pairInj1 Refl = Refl

public export
pairInj2 : {a, b : Type} -> {p, p' : (a, b)} -> p = p' -> snd p = snd p'
pairInj2 Refl = Refl

public export
DecEqPred : (a: Type) -> Type
DecEqPred a = (x, x': a) -> Dec (x = x')

export
encodingDecEq : {a, b : Type} ->
  (encode : a -> b) -> (decode : b -> Maybe a) ->
  (encodingIsCorrect : (x : a) -> decode (encode x) = Just x) ->
  (bDecEq : DecEqPred b) ->
  DecEqPred a
encodingDecEq encode decode encodingIsCorrect bDecEq x x' with
  (bDecEq (encode x) (encode x'))
    encodingDecEq encode decode encodingIsCorrect bDecEq x x' | Yes eq = Yes $
      injective $
        trans
          (sym (encodingIsCorrect x))
          (trans
            (cong decode eq)
            (encodingIsCorrect x'))
    encodingDecEq encode decode encodingIsCorrect bDecEq x x' | No neq =
      No $ \xeq => neq $ cong encode xeq

-- A list with a length stored together with it at run time.
public export
record LList (a : Type) (len : Nat) where
  constructor MkLList
  llList : List a
  llValid : length llList = len

public export
Show a => (len : Nat) => Show (LList a len) where
  show (MkLList l _) = show l ++ "(len=" ++ show len ++ ")"

public export
record LLAlg (a, b : Type) where
  constructor MkLLAlg
  llZ : b
  llS : Nat -> a -> b -> b

public export
llCata : {len : Nat} -> LLAlg a b -> LList a len -> b
llCata {len} (MkLLAlg z s) (MkLList l valid) = llCataInternal z s len l valid
  where
  llCataInternal :
    b ->
    (Nat -> a -> b -> b) ->
    (len : Nat) ->
    (l : List a) ->
    length l = len ->
    b
  llCataInternal z s Z [] Refl = z
  llCataInternal z s (S n) (x :: xs) valid =
    s n x $ llCataInternal z s n xs $ injective valid

public export
InitLList : {a : Type} -> (l : List a) -> LList a (length l)
InitLList l = MkLList l Refl
