module LanguageDef.Term

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.Atom

%default total

-----------------------------------
-----------------------------------
---- Free equivalence in Idris ----
-----------------------------------
-----------------------------------

-- A type which represents witnesses to an equivalence relation.
-- A term of this type may be used as a rewrite rule.

public export
data FreeEquivF : Type -> Type -> Type where
  -- `EqRefl` represents the equivalence between some term `x` of type `a`
  -- and itself.  The reason it has _two_ parameters of type `a` is that
  -- a free generator of witnesses to an equivalence relation is in effect,
  -- and will be used as, a rewrite rule.  Asserting `EqRefl` between `x`
  -- and `y` is a claim that there is a _decidable_ equality between the two.
  EqRefl : a -> a -> FreeEquivF a carrier
  -- Given a term of `carrier`, which represents an equivalence bewteen
  -- terms `x` and `y` of `a`, `EqSym` represents an equivalence between
  -- `y` and `x`.
  EqSym : a -> a -> carrier -> FreeEquivF a carrier
  -- Given terms `eq` and `eq'` of type `carrier`, which respectively
  -- represent the equivalences of `x` and `y` and of `y` and `z` of type `a`,
  -- `EqTrans` represents the equivalence of `x` and `z`.
  EqTrans : a -> a -> a -> carrier -> carrier -> FreeEquivF a carrier

public export
Bifunctor FreeEquivF where
  bimap f _ (EqRefl x y) = EqRefl (f x) (f y)
  bimap f g (EqSym x y eq) = EqSym (f x) (f y) $ g eq
  bimap f g (EqTrans x y z eq eq') = EqTrans (f x) (f y) (f z) (g eq) (g eq')

-- Tests for the validity of a witness to an equivalence relation,
-- and if it is valid, returns which terms are being witnessed to be equivalent.
public export
checkFreeEquiv :
  Eq a =>
  ((a, a) -> Maybe (a, a)) ->
  FreeEquivF a (a, a) -> Maybe (a, a)
checkFreeEquiv eqa (EqRefl x y) = eqa (x, y)
checkFreeEquiv eqa (EqSym x y eq) =
  case eqa eq of
    Just (x', y') => if x == x' && y == y' then Just (y, x) else Nothing
    Nothing => Nothing
checkFreeEquiv eqa (EqTrans x y z eq eq') =
  case (eqa eq, eqa eq') of
    (Just (x', y'), Just (y'', z')) =>
      if x == x' && y == y' && y' == y'' && z == z' then
        Just (x, z)
      else
        Nothing
    (Nothing, _) => Nothing
    (_, Nothing) => Nothing

-------------------------
-------------------------
---- Free categories ----
-------------------------
-------------------------

-- When freely generating categories, we are producing _three_ types:
--
--  - Objects
--  - Morphisms
--  - Equalities
--
-- The equalities come from the identity and associativity laws.  When we
-- define categories in the usual way by proving that existing constructs
-- satisfy the axioms, we must supply proofs of those equalities.  But when
-- we freely generate a category, we must freely generate those equalities
-- to _make_ the generated category satisfy the axioms.
--
-- Consequently, throughout the rest of the development of expressions, the
-- algebras which typecheck objects and morphisms will _not_ use metalanguage
-- equalities -- they will use (and update) carrier types representing
-- free equivalence relations (see `FreeEquivF` above).  This must include
-- the expressions representing objects and morphisms -- our free generation
-- may produce some objects indirectly via morphisms, and since morphisms
-- may exhibit free equalities, objects may as well, unlike in traditional
-- category theory.  The typechecking of morphisms must respect a carrier
-- free equivalence on _objects_, because an equivalence of objects may allow a
-- composition which would not have been allowed by intensional equality
-- (meaning that the domain of the following morphism was not intensionally
-- equal to the codomain of the preceding morphism).
public export
data MorphismF : Type -> Type -> Type where
  -- An identity morphism is labeled by the object which is its
  -- domain and codomain.
  IdentityF :
    object -> MorphismF object carrier
  -- A composition is labeled by its source, intermediate object, and
  -- target, followed by the two morphisms being composed, with the
  -- following morphism listed first, as in usual mathematical notation.
  ComposeF :
    object -> object -> object -> carrier -> carrier -> MorphismF object carrier

public export
Bifunctor MorphismF where
  bimap f _ (IdentityF v) = IdentityF $ f v
  bimap f g (ComposeF s i t q p) = ComposeF (f s) (f i) (f t) (g q) (g p)

-- Free categories produce a free equivalence on morphisms, correpsonding to
-- the identity and associativity laws.
public export
data MorphismEqF : Type -> Type -> Type where
  -- Rewrite the morphism `(id . f)` to `f`.
  RewriteIDLeft : object -> carrier -> MorphismEqF object carrier
  -- Rewrite the morphism `(f . id)` to `f`.
  RewriteIDRight : object -> carrier -> MorphismEqF object carrier
  -- Rewrite the morphism `(f . g) . h` to `f . (g . h)`.
  RewriteAssoc : object -> object -> object -> object ->
    carrier -> carrier -> carrier -> MorphismEqF object carrier

-- Generate the free equivalence relation from the identity and associativity
-- laws.
public export
CoequalizedMorphismF : Type -> Type -> Type
CoequalizedMorphismF object carrier =
  FreeEquivF (MorphismEqF object carrier) carrier

-- Generate the refined type of morphisms quotiented by the rewrite rules
-- (which are the axioms of category theory).
public export
data RefinedMorphismF : Type -> Type -> Type where
  RawMorphism :
    MorphismF object carrier -> RefinedMorphismF object carrier
  CoequalizedMorphism :
    CoequalizedMorphismF object (RefinedMorphismF object carrier) ->
    RefinedMorphismF object carrier

----------------------------
----------------------------
---- Geb terms in Idris ----
----------------------------
----------------------------

-- Geb itself is a pure specification.  `GebTerm` is an Idris type whose
-- terms represent various concepts of Geb.  Because a term of `GebTerm`
-- might represent any of several different concepts, the type is indexed
-- by a type of atoms which classify which concept a given term represents.
-- This makes `GebTerm` a type family; it's effectively simulating a definition
-- by a large mutual recursion, but using an index intead of many different
-- Idris types allows us to interpret Geb in Idris by interpreting just that
-- one type.  I find it less confusing and more convenient than a big mutual
-- recursion.

-------------------------
---- Term definition ----
-------------------------

-- We define `GebTerm` -- an Idris type -- as a fixed point of a polynomial
-- endofunctor of Idris, in the same style in which we will define types of
-- Geb itself.  In particular, that will allow us to write a homoiconic
-- representation of `GebTerm` _as_ a term of `GebTerm` in a way which parallels
-- the Idris definition of `GebTerm`.
--
-- Because `GebTerm`, as described above, represents a number of different
-- concepts, we can view it as an object in a finite product category, where
-- each concept -- which we call a "class" in the context of defining
-- `GebTerm` -- is one of the categories.
--
-- So we first define `GebTermF`, a (polynomial) endofunctor in the product
-- category of all the classes.  Having defined that functor, we'll take a
-- fixed point of it (which we will be able to do because it is polynomial),
-- and then we'll have a `GebTerm` which comprises the Idris representation of
-- terms of Geb.
--
-- Below is the product category in which `GebTerm` lives; therefore it's the
-- category on which we will build an endofunctor, `GebTermF`, from which we
-- will derive `GebTerm` as a fixpoint (initial algebra).
--
-- We represent the product category as a function from a finite
-- index type rather than as, say, nested pairs or a list -- those are all
-- isomorphic, but I feel that the function representation produces the most
-- readable code.
--
-- The aspects of the product category that we define are its objects, its
-- morphisms, and its endofunctors.

public export
GebTermProductCatObject : Type
GebTermProductCatObject = ProductCatObject GTClass

-- A morphism in a product category is a product of morphisms.
-- (In an Idris category, morphisms are functions.)
public export
GebTermProductCatMorphism :
  GebTermProductCatObject -> GebTermProductCatObject -> Type
GebTermProductCatMorphism = ProductCatMorphism {idx=GTClass}

-- An endofunctor on the Idris product category in which Geb terms are defined
-- is a function on objects of the product category together with a function
-- on morphisms that respects it.

public export
GebTermProductCatObjectMap : Type
GebTermProductCatObjectMap = ProductCatObjectEndoMap GTClass

public export
GebTermProductCatMorphismMap : GebTermProductCatObjectMap -> Type
GebTermProductCatMorphismMap = ProductCatMorphismEndoMap

public export
GebTermProductCatEndofunctor : Type
GebTermProductCatEndofunctor = ProductCatEndofunctor GTClass

-- The object-map component of the endofunctor from which we shall define
-- `GebTerm` (as an initial algebra).
public export
data GebTermF_object : GebTermProductCatObjectMap where
  GTNat : GebTermF_object carrier GTCnat
  GTList : GebTermF_object carrier GTClist

-- The morphism-map component of the endofunctor from which we shall define
-- `GebTerm` (as an initial algebra).
public export GebTermF_morphism : GebTermProductCatMorphismMap GebTermF_object
GebTermF_morphism dom cod m GTCnat GTNat = GTNat
GebTermF_morphism dom cod m GTClist GTList = GTList

public export
GebTermF : GebTermProductCatEndofunctor
GebTermF = (GebTermF_object ** GebTermF_morphism)

----------------------
---- Term algebra ----
----------------------

public export
GebTermMu : GTClass -> Type
GebTermMu = MuProduct GebTermF_object

public export
GebTermNu : GTClass -> Type
GebTermNu = NuProduct GebTermF_object

----------------------------------
----------------------------------
----- Polynomial endofunctors ----
----------------------------------
----------------------------------

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

-------------------------------
---- Substitution category ----
-------------------------------

-- We bootstrap the type system starting with the polynomial endofunctors
-- (in fact, all the endofunctors are polynomial in this category) on the
-- zeroth-order unrefined category, or "substitution category".

public export
data SubstEndofunctorF : Type -> Type -> Type where
  SEndoConstVoid : SubstEndofunctorF obj carrier
  SEndoConstUnit : SubstEndofunctorF obj carrier
  SEndoConst : ConstF obj carrier -> SubstEndofunctorF obj carrier
  SEndoProduct : ProductF obj carrier -> SubstEndofunctorF obj carrier
  SEndoCoproduct : CoproductF obj carrier -> SubstEndofunctorF obj carrier

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
