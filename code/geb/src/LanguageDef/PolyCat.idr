module LanguageDef.PolyCat

import Library.IdrisUtils
import Library.IdrisCategories

%default total

-------------------------
-------------------------
---- Dependent types ----
-------------------------
-------------------------

public export
SliceObj : Type -> Type
SliceObj a = a -> Type

public export
Pi : {a : Type} -> SliceObj a -> Type
Pi {a} p = (x : a) -> p x

public export
Sigma : {a : Type} -> SliceObj a -> Type
Sigma {a} p = (x : a ** p x)

public export
SigmaToPair : {0 a, b : Type} -> (Sigma {a} (const b)) -> (a, b)
SigmaToPair (x ** y) = (x, y)

public export
PairToSigma : {0 a, b : Type} -> (a, b) -> (Sigma {a} (const b))
PairToSigma (x, y) = (x ** y)

public export
DecPred : Type -> Type
DecPred a = a -> Bool

public export
Satisfies : {0 a : Type} -> DecPred a -> a -> Type
Satisfies p x = p x = True

public export
Refinement : {a : Type} -> DecPred a -> Type
Refinement {a} p = Subset a (Satisfies p)

public export
MkRefined : {0 a : Type} -> {0 p : DecPred a} ->
  (x : a) -> {auto 0 satisfies : Satisfies p x} ->
  Refinement {a} p
MkRefined x {satisfies} = Element x satisfies

--------------------------------------------------
--------------------------------------------------
---- Natural number induction and coinduction ----
--------------------------------------------------
--------------------------------------------------

------------------------------------------------------
---- Dependent (slice category of natural numbers ----
------------------------------------------------------

public export
NatSliceObj : Type
NatSliceObj = SliceObj Nat

public export
NatPi : NatSliceObj -> Type
NatPi = Pi {a=Nat}

public export
NatSigma : NatSliceObj -> Type
NatSigma = Sigma {a=Nat}

-- If we view a slice object as a functor from the discrete category of
-- natural numbers to the category `Type`, then this type can be viewed as
-- a natural transformation.
public export
NatSliceNatTrans : NatSliceObj -> NatSliceObj -> Type
NatSliceNatTrans p q = (n : Nat) -> p n -> q n

public export
NatSliceMorphism : NatSliceObj -> (Nat -> Nat) -> Type
NatSliceMorphism p f = NatSliceNatTrans p (p . f)

public export
NatDepAlgebra : NatSliceObj -> Type
NatDepAlgebra p = (p Z, NatSliceMorphism p S)

public export
natDepCata : {0 p : NatSliceObj} ->
  NatDepAlgebra p -> NatPi p
natDepCata (z, s) Z = z
natDepCata dalg@(z, s) (S n) = s n (natDepCata dalg n)

public export
NatDepCoalgebra : NatSliceObj -> Type
NatDepCoalgebra p = NatSliceNatTrans p (Maybe . p . S)

public export
natDepAna : {0 p : NatSliceObj} ->
  NatDepCoalgebra p -> NatSigma p -> Inf (Maybe (NatSigma p))
natDepAna coalg (n ** x) with (coalg n x)
  natDepAna coalg (n ** x) | Nothing = Nothing
  natDepAna coalg (n ** x) | Just x' = Delay (natDepAna coalg (S n ** x'))

-----------------------
---- Non-dependent ----
-----------------------

public export
NatAlgebra : Type -> Type
NatAlgebra a = (a, Nat -> a -> a)

public export
natCata : {0 a : Type} -> NatAlgebra a -> Nat -> a
natCata = natDepCata {p=(const a)}

public export
NatCoalgebra : Type -> Type
NatCoalgebra a = Nat -> a -> Maybe a

public export
natAna : {0 a : Type} -> NatCoalgebra a -> (Nat, a) -> Inf (Maybe (Nat, a))
natAna coalg nx =
  map {f=Maybe} SigmaToPair $ natDepAna {p=(const a)} coalg $ PairToSigma nx

-------------------------------------
-------------------------------------
---- Bounded (finite) data types ----
-------------------------------------
-------------------------------------

---------------------------------
---- Bounded natural numbers ----
---------------------------------

public export
ltTrue : Nat -> Nat -> Type
ltTrue m n = (m < n) = True

public export
lteTrue : Nat -> Nat -> Type
lteTrue m n = (m <= n) = True

public export
gtTrue : Nat -> Nat -> Type
gtTrue m n = (m > n) = True

public export
gteTrue : Nat -> Nat -> Type
gteTrue m n = (m >= n) = True

-- All natural numbers less than or equal to `n`.
public export
BoundedNat : Nat -> Type
BoundedNat = Refinement {a=Nat} . (>=)

public export
MkBoundedNat : {0 n : Nat} ->
  (m : Nat) -> {auto 0 gte : gteTrue n m} -> BoundedNat n
MkBoundedNat m {gte} = MkRefined m {satisfies=gte}

----------------------------------------
---- Tuples (fixed-length products) ----
----------------------------------------

public export
NTuple : Type -> Nat -> Type
NTuple a n = Refinement {a=(List a)} ((==) n . length)

public export
MkNTuple : {0 a : Type} -> (l : List a) -> NTuple a (length l)
MkNTuple l = MkRefined l {satisfies=(equalNatCorrect {m=(length l)})}

-----------------------
---- Bounded lists ----
-----------------------

public export
BoundedList : Type -> Nat -> Type
BoundedList a n = Refinement {a=(List a)} ((>=) n . length)

public export
MkBoundedList : {0 a : Type} -> {0 n : Nat} ->
  (l : List a) -> {auto 0 gte : gteTrue n (length l)} -> BoundedList a n
MkBoundedList l {gte} = MkRefined l {satisfies=gte}

{-
public export
BoundedNatMorphism : NatObj -> NatObj -> Type
BoundedNatMorphism = PrefixMap

public export
BoundedNatId : (n : NatObj) -> BoundedNatMorphism n n
BoundedNatId n = id

public export
BoundedNatCompose :
  {a, b, c : NatObj} ->
  BoundedNatMorphism b c ->
  BoundedNatMorphism a b ->
  BoundedNatMorphism a c
BoundedNatCompose = (.)

public export
BoundedNatInitial : Type
BoundedNatInitial = NatOPrefix NatOZ

public export
BoundedNatFromInitial : (n : NatObj) -> BoundedNatMorphism NatOZ n
BoundedNatFromInitial n (_ ** ltz) = void $ FromLTZeroContra _ ltz

public export
BoundedNatTerminal : Type
BoundedNatTerminal = NatOPrefix NatO1

public export
BoundedNatToTerminal : (n : NatObj) -> BoundedNatMorphism n NatO1
BoundedNatToTerminal n = PrefixArrayConst $ NatOPrefixZ NatOZ

public export
BoundedNatCoproduct : NatObj -> NatObj -> Type
BoundedNatCoproduct m n = NatOPrefix (natObjSum m n)

public export
BoundedNatInjLeft :
  (l, r : NatObj) -> BoundedNatMorphism l (natObjSum l r)
BoundedNatInjLeft dom cod = ?BoundedNatInjLeft_hole

public export
BoundedNatInjRight :
  (l, r : NatObj) -> BoundedNatMorphism r (natObjSum l r)
BoundedNatInjRight dom cod = ?BoundedNatInjRight_hole

public export
BoundedNatCase :
  {domL, domR, cod : NatObj} ->
  BoundedNatMorphism domL cod ->
  BoundedNatMorphism domR cod ->
  BoundedNatMorphism (natObjSum domL domR) cod
BoundedNatCase {domL} {domR} {cod} caseL caseR = ?BoundedNatCase_hole

public export
BoundedNatProduct : NatObj -> NatObj -> Type
BoundedNatProduct m n = NatOPrefix (natObjMul m n)

public export
BoundedNatProjLeft :
  (l, r : NatObj) -> BoundedNatMorphism (natObjMul l r) l
BoundedNatProjLeft dom cod = ?BoundedNatProjLeft_hole

public export
BoundedNatProjRight :
  (l, r : NatObj) -> BoundedNatMorphism (natObjMul l r) r
BoundedNatProjRight dom cod = ?BoundedNatProjRight_hole

public export
BoundedNatPair :
  {dom, codL, codR : NatObj} ->
  BoundedNatMorphism dom codL ->
  BoundedNatMorphism dom codR ->
  BoundedNatMorphism dom (natObjMul codL codR)
BoundedNatPair {dom} {codL} {codR} pairL pairR = ?BoundedNatPair_hole

public export
BoundedNatHomSet : NatObj -> NatObj -> Type
BoundedNatHomSet m n = NatOPrefix (natObjRaiseTo m n)

public export
BoundedNatExponential : NatObj -> NatObj -> Type
BoundedNatExponential = flip BoundedNatHomSet

public export
BoundedNatExponentialCardinality :
  (m, n : NatObj) -> BoundedNatExponential m n = NatOPrefix (natObjPow m n)
BoundedNatExponentialCardinality m n = Refl

public export
BoundedNatEval : (m, n : NatObj) ->
  BoundedNatMorphism (natObjMul (natObjRaiseTo m n) m) n
BoundedNatEval m n = ?BoundedNatEval_hole

public export
BoundedNatCurry : {m, n, p : NatObj} ->
  BoundedNatMorphism (natObjMul m n) p ->
  BoundedNatMorphism m (natObjRaiseTo n p)
BoundedNatCurry {m} {n} {p} f = ?BoundedNatCurry_hole

-}

--------------------------
--------------------------
---- Polynomial types ----
--------------------------
--------------------------

---------------------------------------------------------
---------------------------------------------------------
---- Compilation target category (simplified VampIR) ----
---------------------------------------------------------
---------------------------------------------------------
