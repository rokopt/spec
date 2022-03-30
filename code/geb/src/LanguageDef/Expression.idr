module LanguageDef.Expression

import Library.IdrisUtils
import LanguageDef.Atom

%default total

-----------------------------------
-----------------------------------
---- Free equivalence in Idris ----
-----------------------------------
-----------------------------------

-- A type which represents witnesses to an equivalence relation.
public export
data FreeEquivF : Type -> Type -> Type where
  -- `EqRefl` represents the equivalence between some term `x` of type `a`
  -- and itself.
  EqRefl : a -> FreeEquivF a carrier
  -- Given a term of `carrier`, which represents an equivalence bewteen
  -- terms `x` and `y` of `a`, `EqSym` represents an equivalence between
  -- `y` and `x`.
  EqSym : a -> a -> carrier -> FreeEquivF a carrier
  -- Given terms `eq` and `eq'` of type `carrier`, which respectively
  -- represent the equivalences of `x` and `y` and of `y` and `z` of type `a`,
  -- `EqTrans` represents the equivalence of `x` and `z`.
  EqTrans : a -> a -> a -> carrier -> carrier -> FreeEquivF a carrier

public export
Functor (FreeEquivF a) where
  map _ (EqRefl x) = EqRefl x
  map f (EqSym x y eq) = EqSym x y $ f eq
  map f (EqTrans x y z eq eq') = EqTrans x y z (f eq) (f eq')

-- Tests for the validity of a witness to an equivalence relation,
-- and if it is valid, returns which terms are being witnessed to be equivalent.
public export
checkFreeEquiv : Eq a => FreeEquivF a (Maybe (a, a)) -> Maybe (a, a)
checkFreeEquiv (EqRefl x) = Just (x, x)
checkFreeEquiv (EqSym x y eq) = case eq of
  Just (x', y') => if x == x' && y == y' then Just (x, y) else Nothing
  Nothing => Nothing
checkFreeEquiv (EqTrans x y z eq eq') = case (eq, eq') of
  (Just (x', y'), Just (y'', z')) =>
    if x == x' && y == y' && y == y'' && z == z' then Just (x, z) else Nothing
  _ => Nothing

-------------------------
-------------------------
---- Free categories ----
-------------------------
-------------------------

----------------------
----------------------
----- Expressions ----
----------------------
----------------------

-- Expressions are drawn from four categories determined by the presence
-- or absence of each of the following pairs of universal properties:
--
--  - Equalizers & coequalizers
--    (Categories with them are called "refined"; those without are "unrefined")
--  - Initial algebras & terminal coalgebras
--    (Categories with them are "first-order"; those without are "zeroth-order")
--
-- The zeroth-order categories may also be called "substitution" categories.
--
-- All four categories have each of the following pairs of universal properties:
--
--  - Initial objects & terminal objects
--  - Products & coproducts
--
-- All the types until the end of the `Expression` section are zeroth-order,
-- even though they _have_ initial algebras and terminal coalgebras, because
-- they are all defined in the style of "datatypes à la carte" -- in effect,
-- this means that we are programming in the category of polynomial functors
-- of the zeroth-order categories.  At the end of the `Expression` section,
-- we generate the full forms of expressions by taking the fixpoints and
-- cofixpoints of the datatypes previously defined; those types live only in
-- the first-order categories.

--------------------
---- Core types ----
--------------------

-- These types are members of at least the refined first-order category
-- (in some cases they are members of other categories as well).  They
-- may be used to help _define_ even categories which they are not themselves
-- objects of, because the _definitions_ all occur in the refined first-order
-- category.  (In particular, they all have initial algebras and terminal
-- coalgebras, which are present in the first-order categories but not the
-- zeroth-order categories.)

-------------------
---- Constants ----
-------------------

-- Given an object `a`, `Const a` is an endofunctor which takes all objects
-- to `a`.
public export
data ConstF : Type -> Type -> Type where
  InConst : a -> ConstF a carrier

public export
Bifunctor ConstF where
  bimap f _ (InConst x) = InConst (f x)

------------------
---- Products ----
------------------

-- `ProductF a b` is an operator on endofunctors which takes two endofunctors
-- to their product.  `ProductF` is therefore not itself an endofunctor; it
-- is a higher-order functor.  (If `Poly[C]` is the category of polynomial
-- endofunctors on some category `C` -- if all of `C`'s endofunctors are
-- polynomial, then `Poly[C]` is `[C,C]` -- then `ProductF` is an object of
-- [PolyC x PolyC, PolyC].  That is, it is a bifunctor on `Poly[C]`.)
public export
data ProductF : Type -> Type -> Type where
  InProduct : a -> b -> ProductF a b

public export
Bifunctor ProductF where
  bimap f g (InProduct x y) = InProduct (f x) (g y)

--------------------
---- Coproducts ----
--------------------

-- `CoproductF a b` is also in `[PolyC x PolyC, PolyC]`, and takes two
-- endofunctors to their coproduct.
public export
data CoproductF : Type -> Type -> Type where
  InCoproductLeft : a -> CoproductF a b
  InCoproductRight : b -> CoproductF a b

public export
Bifunctor CoproductF where
  bimap f _ (InCoproductLeft x) = InCoproductLeft (f x)
  bimap _ g (InCoproductRight y) = InCoproductRight (g y)

-------------------------
---- Natural numbers ----
-------------------------

public export
data NatF : Type -> Type where
  ZeroF : NatF carrier
  SuccF : carrier -> NatF carrier

public export
Functor NatF where
  map _ ZeroF = ZeroF
  map f (SuccF n) = SuccF $ f n

---------------
---- Lists ----
---------------

public export
data ListF : Type -> Type -> Type where
  NilF : ListF atom carrier
  ConsF : atom -> carrier -> ListF atom carrier

public export
Bifunctor ListF where
  bimap f g NilF = NilF
  bimap f g (ConsF a l) = ConsF (f a) (g l)

---------------------
---- Polynomials ----
---------------------

-- A univariate, finite-degree power.
public export
data PowerF : Type -> Type -> Type where
  FactorsF :
    ListF (coefficient, NatF carrier) carrier ->
    PowerF coefficient carrier

public export
Bifunctor PowerF where
  bimap f g (FactorsF l) = FactorsF $ bimap (bimap f $ map g) g l

export
powerFactors :
  PowerF coefficient carrier ->
  ListF (coefficient, NatF carrier) carrier
powerFactors (FactorsF l) = l

-- A univariate, finite-degree polynomial.
public export
data PolynomialF : Type -> Type -> Type where
  PolyTermsF :
    ListF (PowerF coefficient carrier) carrier ->
    PolynomialF coefficient carrier

public export
Bifunctor PolynomialF where
  bimap f g (PolyTermsF t) = PolyTermsF $ bimap (bimap f g) g t

export
polyTerms :
  PolynomialF coefficient carrier ->
  ListF (PowerF coefficient carrier) carrier
polyTerms (PolyTermsF t) = t

export
polyFactors :
  PolynomialF coefficient carrier ->
  ListF (ListF (coefficient, NatF carrier) carrier) carrier
polyFactors = mapFst powerFactors . polyTerms

-- Next, we introduce a way of interpreting polynomials as datatypes.
-- A polynomial endofunctor may be viewed as simply a polynomial, and
-- may be factored into one, but when representing types with
-- endofunctors, we may wish to factor out commonality amongst types
-- and compose them from smaller components. Such types could theoretically
-- be fully distributed into flat polynomials like `PolynomialF`, but
-- when using polynomials as types, we can gain expressivity with explicit
-- composition.
public export
data PolyTypeF : Type -> Type -> Type where
  PolyTypeComposeF : functor -> functor -> PolyTypeF type functor
  PolyTypeADTF : PolynomialF type functor -> PolyTypeF type functor

-- Next, we perform another recursion.  A programming language might define
-- an ADT as an initial algebra of a polynomial endofunctor.  So, we will
-- treat PolynomialF as representative of polynomial endofunctors, and
-- therefore potentially of ADTs.  To turn a polynomial endofunctor
-- which represents a non-recursive datatype into one which represents a
-- recursive type, we apply the above-defined higher-order functor,
-- `FreeMonad` (AKA `F*`).  So to generate polynomial _recursive_ types, we add
-- to `PolynomialF` the option of applying `FreeMonad` to an existing polynomial
-- type.
public export
data PolyRecTypeF : Type -> Type -> Type where
  PolyTypeFreeF :
    functor -> PolyRecTypeF type functor
  PolyRecTypeADTF :
    PolyTypeF type functor -> PolyRecTypeF type functor
