module LanguageDef.PolyCat

import Library.IdrisUtils
import Library.IdrisCategories

%default total

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
NatSliceObj = Nat -> Type

public export
NatPi : NatSliceObj -> Type
NatPi p = (n : Nat) -> p n

public export
NatSigma : NatSliceObj -> Type
NatSigma p = (n : Nat ** p n)

-- If we view a slice object as a functor from the discrete category of
-- natural numbers to the category `Type`, then this type can be viewed as
-- a natural transformation between slice objects.
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
NatDepCoalgebra p = NatSliceNatTrans p (const $ Maybe $ NatSigma p)

public export
natDepAna : {0 p : NatSliceObj} ->
  NatDepCoalgebra p -> NatSliceNatTrans p (const $ Inf (Maybe $ NatSigma p))
natDepAna coalg n x with (coalg n x)
  natDepAna coalg n x | Nothing = Nothing
  natDepAna coalg n x | Just (n' ** x') = Delay (natDepAna coalg n' x')

-----------------------
---- Non-dependent ----
-----------------------

public export
NatSigmaToPair : {0 a : Type} -> NatSigma (const a) -> (Nat, a)
NatSigmaToPair (n ** x) = (n, x)

public export
NatPairToSigma : {0 a : Type} -> (Nat, a) -> NatSigma (const a)
NatPairToSigma (n, x) = (n ** x)

public export
NatAlgebra : Type -> Type
NatAlgebra a = (a, Nat -> a -> a)

public export
natCata : {0 a : Type} -> NatAlgebra a -> Nat -> a
natCata = natDepCata {p=(const a)}

public export
NatCoalgebra : Type -> Type
NatCoalgebra a = Nat -> a -> Maybe (Nat, a)

public export
NatCoalgToDep : {0 a : Type} -> NatCoalgebra a -> NatDepCoalgebra (const a)
NatCoalgToDep coalg n x = map {f=Maybe} NatPairToSigma $ coalg n x

public export
natAna : {0 a : Type} -> NatCoalgebra a -> Nat -> a -> Inf (Maybe (Nat, a))
natAna {a} coalg n x =
  map {f=Maybe} NatSigmaToPair $ natDepAna (NatCoalgToDep coalg) n x

--------------------------
--------------------------
---- Polynomial types ----
--------------------------
--------------------------

public export
PolyTypeNF : (Nat -> Type) -> Nat -> Type
PolyTypeNF f 0 = Void
PolyTypeNF f (S n) = ?PolyTypeNF_hole

---------------------------------------------------------
---------------------------------------------------------
---- Compilation target category (simplified VampIR) ----
---------------------------------------------------------
---------------------------------------------------------
