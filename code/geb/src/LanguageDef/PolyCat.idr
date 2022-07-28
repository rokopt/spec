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
natDepCata : {0 p : NatSliceObj} -> NatDepAlgebra p -> NatPi p
natDepCata (z, s) Z = z
natDepCata dalg@(z, s) (S n) = s n (natDepCata dalg n)

public export
NatDepCoalgebra : NatSliceObj -> Type
NatDepCoalgebra p = NatSliceNatTrans p (const $ NatSigma p)

public export
natDepAna : {0 p : NatSliceObj} -> NatDepCoalgebra p ->
  (n : Nat) -> (x : p n) -> Inf (n' : Nat ** p n')
natDepAna coalg n x =
  case coalg n x of (n' ** x') => Delay (natDepAna coalg n' x')

-----------------------
---- Non-dependent ----
-----------------------

public export
NatAlgebra : Type -> Type
NatAlgebra a = (a, Nat -> a -> a)

public export
natCata : {0 a : Type} -> NatAlgebra a -> Nat -> a
natCata (z, s) Z = z
natCata alg@(z, s) (S n) = s n (natCata alg n)

public export
NatCoalgebra : Type -> Type
NatCoalgebra a = Nat -> a -> (Nat, Either () a)

public export
natAna : {0 a : Type} -> NatCoalgebra a -> Nat -> a -> Inf (Nat, Either () a)
natAna coalg n x = case coalg n x of
  (n', Left ()) => (n', Left ())
  (n', Right x') => Delay (natAna coalg n' x')

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
