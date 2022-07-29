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

public export
shape : {0 a : Type} -> {0 p : DecPred a} -> Refinement {a} p -> a
shape = fst

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

public export
natGenIndStrengthened : {0 p : NatSliceObj} ->
  (p 0) ->
  ((n : Nat) -> ((m : Nat) -> LTE m n -> p m) -> p (S n)) ->
  (x : Nat) -> (y : Nat) -> LTE y x -> p y
natGenIndStrengthened {p} p0 pS =
  natDepCata
    {p=(\x => (y : Nat) -> LTE y x -> p y)}
    (\n, lte => replace {p} (lteZeroIsZero lte) p0,
     \n, hyp, y, lteySn => case lteSuccEitherEqLte lteySn of
      Left eq => replace {p} (sym eq) $ pS n hyp
      Right lteyn => hyp y lteyn)

public export
natGenInd : {0 p : NatSliceObj} ->
  (p 0) ->
  ((n : Nat) -> ((m : Nat) -> LTE m n -> p m) -> p (S n)) ->
  (k : Nat) -> p k
natGenInd p0 pS k = natGenIndStrengthened p0 pS k k reflexive

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

--------------------------------------------
---- Fixed-width binary natural numbers ----
--------------------------------------------

public export
FixedNat : Nat -> Type
FixedNat = NTuple Digit

public export
toNat : {0 bits : Nat} -> FixedNat bits -> Nat
toNat = toNat . shape

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

---------------------
---- Polynomials ----
---------------------

public export
PolyTerm : Type
PolyTerm = (Nat, Nat)

public export
ptPow : PolyTerm -> Nat
ptPow = fst

public export
ptCoeff : PolyTerm -> Nat
ptCoeff = snd

-- A list of (power, coefficient) pairs.
public export
PolyShape : Type
PolyShape = List PolyTerm

public export
validPT : DecPred (Nat, Nat)
validPT t = ptCoeff t /= 0

-- We define a valid (normalized) polynomial shape as follows:
--   - The shape of the polynomial is a list of pairs of natural numbers,
--     where each list element represents a term (monomial), and the
--     pair represents (power, coefficient)
--   - Entries are sorted by strictly descending power
--   - There are no entries for powers with zero coefficients
-- Consequences of these rules include:
--  - Equality of valid polynomials is equality of underlying shapes
--  - The tail of a valid polynomial is always valid
--  - The meaning of an entry (a term) is independent of which list
--    it appears in, and thus can be determined by looking at the term
--    in isolation
--  - The degree of the polynomial is the left element of the head of the
--    list (or zero if the list is empty)
public export
validPoly : DecPred PolyShape
validPoly (t :: ts@(t' :: _)) =
  if (validPT t && ptPow t > ptPow t') then validPoly ts else False
validPoly [t] = validPT t
validPoly [] = True

public export
Polynomial : Type
Polynomial = Refinement {a=PolyShape} validPoly

public export
ValidPoly : PolyShape -> Type
ValidPoly = Satisfies validPoly

public export
MkPolynomial :
  (shape : PolyShape) -> {auto 0 valid : validPoly shape = True} -> Polynomial
MkPolynomial shape {valid} = MkRefined {a=PolyShape} shape {satisfies=valid}

public export
headPow : PolyShape -> Nat
headPow (t :: ts) = ptPow t
headPow [] = 0

public export
degree : Polynomial -> Nat
degree = headPow . shape

public export
accumPTCoeff : Nat -> PolyShape -> Nat
accumPTCoeff = foldl ((|>) ptCoeff . (+))

public export
sumPTCoeff : PolyShape -> Nat
sumPTCoeff = accumPTCoeff 0

public export
sumCoeff : Polynomial -> Nat
sumCoeff = sumPTCoeff . shape

public export
numTerms : Polynomial -> Nat
numTerms = length . shape

-- Parameters: (accumulator, power, input).
-- Performs exponentiation by breaking it down into individual multiplications.
public export
ptInterpNatAccum : Nat -> Nat -> Nat -> Nat
ptInterpNatAccum acc (S p) n = ptInterpNatAccum (n * acc) p n
ptInterpNatAccum acc Z n = acc

public export
ptInterpNatByMults : PolyTerm -> Nat -> Nat
ptInterpNatByMults t = ptInterpNatAccum (ptCoeff t) (ptPow t) -- acc == coeff

-- Performs exponentiation using built-in power function.
public export
ptInterpNat : PolyTerm -> Nat -> Nat
ptInterpNat t n = (ptCoeff t) * power n (ptPow t)

public export
psInterpNatAccum : Nat -> PolyShape -> Nat -> Nat
psInterpNatAccum acc (t :: ts) n = psInterpNatAccum (ptInterpNat t n + acc) ts n
psInterpNatAccum acc [] n = acc

public export
psInterpNat : PolyShape -> Nat -> Nat
psInterpNat = psInterpNatAccum 0

public export
polyInterpNat : Polynomial -> Nat -> Nat
polyInterpNat = psInterpNat . shape

-----------------------------------
---- Arithmetic on polynomials ----
-----------------------------------

public export
scalePolyRevAcc : Nat -> PolyShape -> PolyShape -> PolyShape
scalePolyRevAcc Z acc _ = []
scalePolyRevAcc n@(S _) acc [] = acc
scalePolyRevAcc n@(S _) acc ((p, c) :: ts) =
  scalePolyRevAcc n ((p, n * c) :: acc) ts

public export
scalePolyRev : Nat -> PolyShape -> PolyShape
scalePolyRev n = scalePolyRevAcc n []

public export
scalePolyShape : Nat -> PolyShape -> PolyShape
scalePolyShape n = reverse . scalePolyRev n

public export
scalePreservesValid : {0 n : Nat} -> {0 poly : PolyShape} ->
  ValidPoly poly -> ValidPoly (scalePolyShape n poly)
scalePreservesValid {n} {poly} valid = ?scalePolyShapeCorrect_hole

public export
scalePoly : Nat -> Polynomial -> Polynomial
scalePoly n (Element poly valid) =
  Element (scalePolyShape n poly) (scalePreservesValid valid)

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
