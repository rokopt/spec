module LanguageDef.RefinedADT

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom

%default total

public export
LengthEquals : (carrier : Type) -> (Nat, List carrier) -> Type
LengthEquals _ (n, l) = n = length l

-- A list paired with its length (effectively, storing its length together
-- with the list at "runtime").
public export
ListN : Type -> Type
ListN carrier = (nl : (Nat, List carrier) ** LengthEquals carrier nl)

-- A finite-dimensional "matrix" with variable numbers of elements per row.
-- The parameter is the dimension minus one.
public export
VarMatrixD : (predDimension : Nat) -> Type -> Type
VarMatrixD Z carrier = ListN carrier
VarMatrixD (S n) carrier = ListN (VarMatrixD n carrier)

-- A finite-dimensional matrix of natural numbers.
-- The parameter is the dimension minus one.
VarMatrixN : (predDimension : Nat) -> Type
VarMatrixN = flip VarMatrixD Nat

-- Monomorphized types consisting of finite products and coproducts.
public export
data FinSetObj : Type -> Type where
  FinProduct : (n : Nat ** Tuple n (FinSetObj a)) -> FinSetObj a
  FinCoproduct : (n : Nat ** Tuple n (FinSetObj a)) -> FinSetObj a

public export
FinSetObjAlg : Type -> Type
FinSetObjAlg = Algebra FinSetObj

public export
FinSetObjCoalg : Type -> Type
FinSetObjCoalg = Coalgebra FinSetObj

public export
record FiniteShape where
  constructor MkFiniteShape
  numObjects : Nat
  numMorphisms : Nat
  domains : Vect numMorphisms (Fin numObjects)
  codomains : Vect numMorphisms (Fin numObjects)

-------------------------------
-------------------------------
---- Refined S-expressions ----
-------------------------------
-------------------------------

-- We define a category inductively through applications of the
-- following type constructors:
--
--  - `Atom` (for some given metalanguage atom type, which must be isomorphic
--  -         to the natural numbers or some subset of them, which in particular
--  -         means that they have a decidable equality)
--  - `Nat`
--  - `RefinedList` (indexed by number of atoms in the list)
--  - `RefinedSexp` (indexed by total number of atoms in the expression)
--
-- We define the category by treating the type constructors as
-- monads and comonads, and the function definitions as natural
-- transformations, which in turn are derived from compositions of
-- the units and counits of adjunctions.

public export
record RefinedSexpCarrier where
  constructor MkRefinedSexpCarrier
  RefinedSexpFunctorCarrier : Type
  RefinedSexpNatTransCarrier : Type
  RefinedSexpNatTransSignatureCarrier :
    RefinedSexpNatTransCarrier ->
    (RefinedSexpFunctorCarrier, RefinedSexpFunctorCarrier)

public export
data RefinedSexpFunctorF : (atom : Type) -> RefinedSexpCarrier -> Type where

public export
data RefinedSexpNatTransF : (atom : Type) -> RefinedSexpCarrier -> Type where

public export
RefinedSexpNatTransSignatureF : {atom : Type} ->
  (carrier : RefinedSexpCarrier) ->
  RefinedSexpNatTransF atom carrier ->
  (RefinedSexpNatTransF atom carrier, RefinedSexpNatTransF atom carrier)
RefinedSexpNatTransSignatureF {atom} carrier newNatTrans impossible

mutual
  public export
  data RefinedSexpFunctor : (atom : Type) -> Type where
    InRSF :
      RefinedSexpFunctorF atom (RefinedSexpData atom) ->
      RefinedSexpFunctor atom

  public export
  data RefinedSexpNatTrans : (atom : Type) -> Type where
    InRSNT :
      RefinedSexpNatTransF atom (RefinedSexpData atom) ->
      RefinedSexpNatTrans atom

  public export
  RefinedSexpNatTransSignature : {atom : Type} ->
    RefinedSexpNatTrans atom ->
    (RefinedSexpFunctor atom, RefinedSexpFunctor atom)
  RefinedSexpNatTransSignature (InRSNT _) impossible

  public export
  RefinedSexpData : (atom : Type) -> RefinedSexpCarrier
  RefinedSexpData atom =
    MkRefinedSexpCarrier
      (RefinedSexpFunctor atom)
      (RefinedSexpNatTrans atom)
      (RefinedSexpNatTransSignature {atom})

--------------------
--------------------
---- Core types ----
--------------------
--------------------

---------------
---- Lists ----
---------------

public export
ListAlg : Type -> Type -> Type
ListAlg = Algebra . ListF

public export
FreeList : Type -> Type -> Type
FreeList = FreeMonad' . ListF

public export
MuList : Type -> Type
MuList = Mu' . ListF

public export
ListCoalg : Type -> Type -> Type
ListCoalg = Coalgebra . ListF

public export
CofreeList : Type -> Type -> Type
CofreeList = CofreeComonad' . ListF

public export
NuList : Type -> Type
NuList = Nu' . ListF

-------------------------------------------------
-------------------------------------------------
---- The category of polynomial endofunctors ----
-------------------------------------------------
-------------------------------------------------

public export
record FinNatPoly where
  constructor MkFinNatPoly
  numTerms : Nat
  coefficients : LList Nat numTerms
  trimmed : Not (head' (llList coefficients) = Just 0)

public export
Show FinNatPoly where
  show (MkFinNatPoly _ c _) = show c

public export
InitFinNatPoly :
  (l : List Nat) -> {auto ok : (head' l /= Just 0) = True} -> FinNatPoly
InitFinNatPoly l {ok} = MkFinNatPoly (length l) (InitLList l) $
  \isz =>
    case replace {p=(\hl => (hl /= Just 0) = True)} isz ok of Refl impossible

public export
interpretFinNatPoly : FinNatPoly -> Nat -> Nat
interpretFinNatPoly (MkFinNatPoly d cs _) n =
  llCata (MkLLAlg Z (\i, c, acc => acc + c * (power n i))) cs

public export
record MultiVarTerm (constant, variable : Type) where
  PolyTerm : (constant, variable)

public export
mvConst : MultiVarTerm constant variable -> constant
mvConst = fst . PolyTerm

public export
mvVar : MultiVarTerm constant variable -> variable
mvVar = snd . PolyTerm

public export
record MultiVarPoly (constant, variable : Type) where
  PolyTerms : List (MultiVarTerm constant variable)

public export
numTerms : MultiVarPoly constant variable -> Nat
numTerms = length . PolyTerms

public export
mvNth :
  (mvp : MultiVarPoly constant variable) -> (n : Nat) ->
  {auto ok : InBounds n (PolyTerms mvp)} ->
  MultiVarTerm constant variable
mvNth mvp n = index n (PolyTerms mvp)

---------------
---------------
---- Paths ----
---------------
---------------

public export
EdgeProjectionType : Type -> Type -> Type
EdgeProjectionType vertex edge = edge -> (vertex, vertex)

public export
record PathCarrier (vertex : Type) where
  constructor EdgeFibration
  EdgeTotal : Type
  EdgeProjection : EdgeProjectionType vertex EdgeTotal

public export
edgeSource : {carrier : PathCarrier vertex} -> EdgeTotal carrier -> vertex
edgeSource {carrier} = fst . EdgeProjection carrier

public export
edgeTarget : {carrier : PathCarrier vertex} -> EdgeTotal carrier -> vertex
edgeTarget {carrier} = snd . EdgeProjection carrier

public export
data PathTotalF :
    (vEq : vertex -> vertex -> Type) -> PathCarrier vertex -> Type where
  LoopF :
    {carrier : PathCarrier vertex} ->
    vertex ->
    PathTotalF vEq carrier
  ConcatF :
    {carrier : PathCarrier vertex} ->
    (tail, head : EdgeTotal carrier) ->
    {auto valid :
      vEq (edgeSource {carrier} tail) (edgeTarget {carrier} head)} ->
    PathTotalF vEq carrier

public export
PathDomainF :
  {vertex : Type} ->
  {vEq : vertex -> vertex -> Type} ->
  (carrier : PathCarrier vertex) ->
  PathTotalF vEq carrier ->
  vertex
PathDomainF carrier (LoopF v) = v
PathDomainF carrier (ConcatF tail head) = edgeSource {carrier} head

public export
PathCodomainF :
  {vertex : Type} ->
  {vEq : vertex -> vertex -> Type} ->
  (carrier : PathCarrier vertex) ->
  PathTotalF vEq carrier ->
  vertex
PathCodomainF carrier (LoopF v) = v
PathCodomainF carrier (ConcatF tail head) = edgeTarget {carrier} tail

public export
PathProjectionF :
  {vertex : Type} ->
  {vEq : vertex -> vertex -> Type} ->
  (carrier : PathCarrier vertex) ->
  EdgeProjectionType vertex (PathTotalF vEq carrier)
PathProjectionF carrier edge =
  (PathDomainF carrier edge, PathCodomainF carrier edge)

public export
PathF : {vertex : Type} ->
  (vertex -> vertex -> Type) ->
  PathCarrier vertex ->
  PathCarrier vertex
PathF vEq carrier =
  EdgeFibration (PathTotalF vEq carrier) (PathProjectionF {vEq} carrier)

----------------------------
----------------------------
---- Geb terms in Idris ----
----------------------------
----------------------------

-- Geb itself is a pure specification.  `GebTerm` is an Idris type whose
-- terms represent various concepts of Geb.  Because a term of `GebTerm`
-- might represent any of several different concepts, the type is indexed
-- by a type of atoms which classify which concept a given term represents.
-- This makes `GebTerm` a type family; it's effectively simulating a
-- definition by a large mutual recursion, but using an index intead of many
-- different Idris types allows us to interpret Geb in Idris by interpreting
-- just that one type.  I find it less confusing and more convenient than a big
-- mutual recursion.

-------------------------
---- Term definition ----
-------------------------

-- We define `GebTerm` -- an Idris type -- as a fixed point of a
-- polynomial endofunctor of Idris, in the same style in which we will define
-- types of Geb itself.  In particular, that will allow us to write a homoiconic
-- representation of `GebTerm` _as_ a term of `GebTerm` in a way
-- which parallels the Idris definition of `GebTerm`.
--
-- Because `GebTerm`, as described above, represents a number of different
-- concepts, we can view it as an object in a finite product category, where
-- each concept -- which we call a "class" in the context of defining
-- `GebTerm` -- is one of the categories.
--
-- So we first define `GebTermF`, a (polynomial) endofunctor in the product
-- category of all the classes.  Having defined that functor, we'll take a
-- fixed point of it (which we will be able to do because it is polynomial),
-- and then we'll have a `GebTerm` which comprises the Idris
-- representation of terms of Geb.
--
-- Below is the product category in which `GebTerm` lives; therefore it's
-- the category on which we will build an endofunctor, `GebTermF`, from
-- which we will derive `GebTerm` as a fixpoint (initial algebra).
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
GebTermProductCatObject = ProductCatObject GebAtom

-- A morphism in a product category is a product of morphisms.
-- (In an Idris category, morphisms are functions.)
public export
GebTermProductCatMorphism :
  GebTermProductCatObject -> GebTermProductCatObject -> Type
GebTermProductCatMorphism = ProductCatMorphism {idx=GebAtom}

-- An endofunctor on the Idris product category in which Geb terms are defined
-- is a function on objects of the product category together with a function
-- on morphisms that respects it.

public export
GebTermProductCatObjectMap : Type
GebTermProductCatObjectMap = ProductCatObjectEndoMap GebAtom

public export
GebTermProductCatMorphismMap : GebTermProductCatObjectMap -> Type
GebTermProductCatMorphismMap = ProductCatMorphismEndoMap

public export
GebTermProductCatEndofunctor : Type
GebTermProductCatEndofunctor = ProductCatEndofunctor GebAtom

------------------------------------------
---- Term-checking and interpretation ----
------------------------------------------


---------------------------------
---------------------------------
---- Metalanguage fibrations ----
---------------------------------
---------------------------------

-----------------------------
-----------------------------
---- Metalanguage arrows ----
-----------------------------
-----------------------------

-- We refer to a pair of a pair of vertices in a directed graph and an edge
-- from the first vertex in the pair to the second vertex in the pair as an
-- "arrow".

----------------------------
----------------------------
---- Generalized arrows ----
----------------------------
----------------------------

-- We refer to a pair of a pair of vertices in a directed graph and an edge
-- from the first vertex in the pair to the second vertex in the pair as an
-- "arrow".

{-
public export
ArrowSig : Type -> Type
ArrowSig vertexType = (vertexType, vertexType)

public export
EdgeType : Type -> Type
EdgeType vertexType = ArrowSig vertexType -> Type

public export
Arrow : {vertexType : Type} -> EdgeType vertexType -> Type
Arrow {vertexType} arrowType = DPair (ArrowSig vertexType) arrowType

public export
arrowSig : {vertexType : Type} -> {arrowType : EdgeType vertexType} ->
  Arrow arrowType -> ArrowSig vertexType
arrowSig (sig ** _) = sig

public export
arrowEdge : {vertexType : Type} -> {arrowType : EdgeType vertexType} ->
  (arrow : Arrow arrowType) -> arrowType (arrowSig arrow)
arrowEdge (_ ** edge) = edge

public export
arrowSource : {vertexType : Type} -> {arrowType : EdgeType vertexType} ->
  Arrow arrowType -> vertexType
arrowSource = fst . arrowSig

public export
arrowTarget : {vertexType : Type} -> {arrowType : EdgeType vertexType} ->
  Arrow arrowType -> vertexType
arrowTarget = snd . arrowSig
-}

----------------------------------------
----------------------------------------
---- Equivalence and term rewriting ----
----------------------------------------
----------------------------------------

------------------------------------
---- Free equivalence relations ----
------------------------------------

-- A type which represents witnesses to an equivalence relation.
-- A term of this type may be used as a rewrite rule.

public export
data FreeEquivF : Type -> Type -> Type where
  -- `EqRefl` represents the equivalence between some term `x` of type `a`
  -- and itself.  The reason it has _two_ parameters of type `a` is that
  -- a free generator of witnesses to an equivalence relation is in effect,
  -- and will be used as, a rewrite rule.  Asserting `EqRefl` between `x`
  -- and `y` is a claim that there is a _decidable_ equality between the two
  -- which can be decided when the term is validated (typechecked).
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
checkFreeEquiv eqa (EqRefl x y) =
  case eqa (x, y) of
    Just (x', y') => if x == x' && y == y' then Just (x, y) else Nothing
    Nothing => Nothing
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

--------------------------
---- Rewritable terms ----
--------------------------

-- A rewritable term type is a term type accompanied with a (free) equivalence
-- relation, a witness to which may be used _as_ a term.
public export
data RewritableTermF : Type -> Type where
  Rewrite : FreeEquivF carrier carrier -> RewritableTermF carrier

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
checkMorphism :
  (Eq object, Eq carrier) =>
  (object -> Maybe object) ->
  (carrier -> Maybe (object, object)) ->
  (MorphismF object carrier -> Maybe (object, object))
checkMorphism checkObj checkMorph (IdentityF obj) =
  case checkObj obj of
    Just obj' => Just (obj', obj')
    Nothing => Nothing
checkMorphism checkObj checkMorph (ComposeF a b c g f) =
  case (checkObj a, checkObj b, checkObj c, checkMorph g, checkMorph f) of
    (Just a', Just b', Just c', Just (domg, codg), Just (domf, codf)) =>
      if a' == domf && b' == codf && b' == domg && c' == codg then
        Just (a', c')
      else
        Nothing
    _ => Nothing

public export
Bifunctor MorphismF where
  bimap f _ (IdentityF v) = IdentityF $ f v
  bimap f g (ComposeF s i t q p) = ComposeF (f s) (f i) (f t) (g q) (g p)

-- Free categories produce a free equivalence on morphisms, correpsonding to
-- the identity and associativity laws.
public export
data MorphismEqF : Type -> Type where
  -- Rewrite the morphism `(id . f)` to `f`.
  RewriteIDLeft : morphism -> MorphismEqF morphism
  -- Rewrite the morphism `(f . id)` to `f`.
  RewriteIDRight : morphism -> MorphismEqF morphism
  -- Rewrite the morphism `(f . g) . h` to `f . (g . h)`.
  RewriteAssoc : morphism -> morphism -> morphism -> MorphismEqF morphism

-- Generate the free equivalence relation from the identity and associativity
-- laws.
public export
CoequalizedMorphismF : Type -> Type
CoequalizedMorphismF carrier = FreeEquivF (MorphismEqF carrier) carrier

-- Generate the refined type of morphisms quotiented by the rewrite rules
-- (which are the axioms of category theory).
public export
data RefinedMorphismF : Type -> Type -> Type where
  RawMorphism :
    MorphismF object carrier -> RefinedMorphismF object carrier
  CoequalizedMorphism :
    CoequalizedMorphismF (RefinedMorphismF object carrier) ->
    RefinedMorphismF object carrier

----------------------------------
----------------------------------
---- Term-building categories ----
----------------------------------
----------------------------------

-- These are the categories we need in order to define the objects
-- and morphisms of the refined first-order ADT category -- the smallest one
-- in which there is an object which we can interpret in Idris as
-- `RefinedADTCat`.

-- Generate objects for a category which can support at least
-- substitution:  initial and terminal objects, and products and coproducts.
public export
data SubstCatObjF : Type -> Type where
  SubstInitial : SubstCatObjF carrier
  SubstTerminal : SubstCatObjF carrier
  SubstProduct : carrier -> carrier -> SubstCatObjF carrier
  SubstCoproduct : carrier -> carrier -> SubstCatObjF carrier

-- Generate morphisms for a category which can support at least substitution.
public export
data SubstCatMorphismF : Type -> Type -> Type where
  -- The left adjoint of the unique functor from the substitution category
  -- to the terminal category (which is the discrete one-object category).
  SubstFromInitial : object -> SubstCatMorphismF object carrier

  -- The right adjoint of the unique functor from the substitution category
  -- to the terminal category.
  SubstToTerminal : object -> SubstCatMorphismF object carrier

  -- The right adjoint of the diagonal functor (the diagonal functor goes
  -- from the substitution category to the product category, so its adjoints
  -- go from the product category to the substitution category).
  SubstProductIntro : (dom, cod, cod' : object) ->
    carrier -> carrier -> SubstCatMorphismF object carrier

  -- The left projection of the counit of the product adjunction
  -- (which is a morphism in the substitution category).
  SubstProductElimLeft : (dom, cod : object) ->
    carrier -> SubstCatMorphismF object carrier

  -- The right projection of the counit of the product adjunction.
  SubstProductElimRight : (dom, cod : object) ->
    carrier -> SubstCatMorphismF object carrier

  SubstCoproductIntroLeft : (dom, cod : object) ->
    carrier -> SubstCatMorphismF object carrier

  SubstCoproductIntroRight : (dom, cod : object) ->
    carrier -> SubstCatMorphismF object carrier

  SubstCoproductElim : (dom, dom', cod : object) ->
    carrier -> carrier -> SubstCatMorphismF object carrier

public export
data RefinedSubstObjF : Type -> Type -> Type where
  SubstEqualizer : object -> object -> morphism -> morphism ->
    RefinedSubstObjF object morphism

  SubstCoequalizer : object -> object -> morphism -> morphism ->
    RefinedSubstObjF object morphism

public export
data RefinedSubstMorphismF : Type -> Type -> Type where

public export
SubstCatObjFree : Type -> Type
SubstCatObjFree = FreeMonad' SubstCatObjF

public export
SubstCatObj : Type
SubstCatObj = Mu' SubstCatObjF

-----------------------------------------------------------
-----------------------------------------------------------
---- Substitution category in the metalanguage (Idris) ----
-----------------------------------------------------------
-----------------------------------------------------------

-- public export
-- data MetaSubstCatObjAlg : Type -> Type) where

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

----------------------------------
----------------------------------
----- Polynomial endofunctors ----
----------------------------------
----------------------------------

public export
data PolynomialFunctorF : Type -> Type -> Type where
  -- See https://ncatlab.org/nlab/show/polynomial+functor#definition :
  --
  -- In a category `C`, objects `W`, `X`, `Y`, `Z` and morphisms:
  --
  --  `f`: `X -> W`
  --  `g`: `X -> Y`
  --  `h`: `Y -> Z`
  --
  -- determine a polynomial endofunctor from `C/W` to `C/Z` comprised of
  -- the composition (domain to codomain):
  --
  --  `f*`: `C/W -> C/X` (pullback (or "base change") functor of `f`)
  --  `Pi(g)`: `C/X -> C/Y` (dependent product)
  --  `Sigma(h)`: `C/Y -> C/Z` (dependent sum)
  --
  -- (This is an endofunctor iff `W==Z`, and a non-dependent endofunctor
  -- iff furthermore `W==Z==1` (where `1` is the terminal object of `C`).
  PolyFunctorFromMorphisms : (w, x, y, z : object) -> (f, g, h : morphism) ->
    PolynomialFunctorF object morphism

public export
data CartesianTransformationF : Type -> Type -> Type -> Type where
  -- See
  -- https://ncatlab.org/nlab/show/equifibered%20natural%20transformation#properties:
  --
  -- Given a category `C` with a terminal object, a category `D` with all
  -- pullbacks, and a functor `G : C -> D`, then an object `F1` of `C` and
  -- a morphism `F[F1] -> G[1]` (where `1` is the terminal object of `C`)
  -- determine a functor `F : C -> D` and a natural transformation `F -> G`
  -- which is "equifibered" (also called "cartesian"), meaning that all of
  -- its naturality squares are pullbacks.  (The functor `F` itself is
  -- generated by taking pullbacks.)
    CartesianTransformationFromMorphism:
      (f1 : object) -> (f : morphism) -> (g : functor) ->
      CartesianTransformationF object morphism functor

public export
data AdjunctionF : Type -> Type -> Type where
  AdjunctionFromUnits : (l, r : functor) -> (unit, counit : natTrans) ->
    AdjunctionF functor natTrans

public export
data ConjugateNatTransF : Type -> Type where
  -- See
  -- https://unapologetic.wordpress.com/2007/07/30/transformations-of-adjoints/
  -- for the definition of "conjugate natural transformations" and how
  -- they can be used to transform adjoints.
  ConjugateNatTransFromPair :
    natTrans -> natTrans -> ConjugateNatTransF natTrans

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

---------------------------------------
---- Refined substitution category ----
---------------------------------------

-- Generate objects of the refined substitution category.
public export
data RSubstObjF :
    (obj, morph : Type) -> (domain, codomain : morph -> obj) -> Type where
  RSubstObjInitial : RSubstObjF obj morph domain codomain

public export
data RefinedExpClass : Type where
  RECl_Object : RefinedExpClass
  RECl_Morphism : RefinedExpClass
  RECl_PolyEndo : RefinedExpClass
  RECl_PolyNatTrans : RefinedExpClass

public export
record RefinedExpCategory_Obj where
  constructor RefinedExpClassTypes

  RECat_Object : Type
  RECat_Morphism : Type
  RECat_PolyEndo : Type
  RECat_PolyNatTrans : Type

  RECat_Morphism_Domain : RECat_Morphism -> RECat_Object
  RECat_Morphism_Codomain : RECat_Morphism -> RECat_Object
  RECat_PolyNatTrans_Domain : RECat_PolyNatTrans -> RECat_PolyEndo
  RECat_PolyNatTrans_Codomain : RECat_PolyNatTrans -> RECat_PolyEndo

public export
record RefinedExpCategory_Equiv (recat : RefinedExpCategory_Obj) where
  constructor RefinedExpCategory_Equivalences

  RECat_Object_Equiv : Type
  RECat_Morphism_Equiv : Type
  RECat_PolyEndo_Equiv : Type
  RECat_PolyNatTrans_Equiv : Type

  RECat_ObjectEquiv_Left :
    RECat_Object_Equiv -> RECat_Object recat
  RECat_ObjectEquiv_Right :
    RECat_Object_Equiv -> RECat_Object recat
  RECat_MorphismEquiv_Left :
    RECat_Morphism_Equiv -> RECat_Morphism recat
  RECat_MorphismEquiv_Right :
    RECat_Morphism_Equiv -> RECat_Morphism recat
  RECat_PolyEndoEquiv_Left :
    RECat_PolyEndo_Equiv -> RECat_PolyEndo recat
  RECat_PolyEndoEquiv_Right :
    RECat_PolyEndo_Equiv -> RECat_PolyEndo recat
  RECat_PolyNatTransEquiv_Left :
    RECat_PolyNatTrans_Equiv -> RECat_PolyNatTrans recat
  RECat_PolyNatTransEquiv_Right :
    RECat_PolyNatTrans_Equiv -> RECat_PolyNatTrans recat

public export
ObjectTypeInterpretation : Type -> Type
ObjectTypeInterpretation obj = obj -> Type

public export
TermTypeInterpretation : {obj : Type} -> ObjectTypeInterpretation obj -> Type
TermTypeInterpretation {obj} objInterp = (a : obj) -> () -> objInterp a

public export
MorphismTypeInterpretation : {obj : Type} -> ObjectTypeInterpretation obj ->
  (morph : Type) -> (domain, codomain : morph -> obj) -> Type
MorphismTypeInterpretation objInterp morph domain codomain =
  (m : morph) -> objInterp (domain m) -> objInterp (codomain m)

public export
MorphHasSig : {obj, morph : Type} ->
  (domain : morph -> obj) -> (codomain : morph -> obj) ->
  morph -> (obj, obj) -> Type
MorphHasSig domain codomain m (a, b) = (domain m = a, codomain m = b)

public export
FunctorObjmap : Type -> Type
FunctorObjmap obj = obj -> obj

public export
FunctorMorphmap : {obj, morph : Type} ->
  (domain : morph -> obj) -> (codomain : morph -> obj) ->
  FunctorObjmap obj -> Type
FunctorMorphmap {obj} {morph} domain codomain objmap =
  (m : morph) ->
  (fm : morph **
   MorphHasSig domain codomain fm (objmap (domain m), objmap (codomain m)))

public export
FunctorTypeInterpretation : {obj, morph : Type} ->
  {domain, codomain : morph -> obj} ->
  (objInterp : ObjectTypeInterpretation obj) ->
  MorphismTypeInterpretation objInterp morph domain codomain ->
  Type -> Type
FunctorTypeInterpretation {obj} {domain} {codomain}
  objInterp morphInterp functor =
    functor ->
      (objmap : FunctorObjmap obj ** FunctorMorphmap domain codomain objmap)

public export
record RefinedExpInterpretation (recat : RefinedExpCategory_Obj) where
  constructor RefinedExpInterpretations
  REInt_Object : ObjectTypeInterpretation (RECat_Object recat)
  REInt_Term : TermTypeInterpretation REInt_Object
  REInt_Morphism :
    MorphismTypeInterpretation
      REInt_Object (RECat_Morphism recat)
      (RECat_Morphism_Domain recat) (RECat_Morphism_Codomain recat)
  REInt_PolyEndo :
    FunctorTypeInterpretation REInt_Object REInt_Morphism (RECat_PolyEndo recat)

public export
record RefinedExpCategoryType where
  constructor RefinedExpCategoryComponents
  REC_Obj : RefinedExpCategory_Obj
  REC_Int : RefinedExpInterpretation REC_Obj

-------------------------
---- Natural numbers ----
-------------------------

public export
NatAlg : Type -> Type
NatAlg = Algebra NatF

public export
FreeNat : Type -> Type
FreeNat = FreeMonad' NatF

public export
MuNat : Type
MuNat = Mu' NatF

public export
NatCoalg : Type -> Type
NatCoalg = Coalgebra NatF

public export
CofreeNat : Type -> Type
CofreeNat = CofreeComonad' NatF

public export
NuNat : Type
NuNat = Nu' NatF

-----------------------
---- S-expressions ----
-----------------------

public export
data SexpClass : Type where
  SEXP : SexpClass
  SLIST : SexpClass

public export
SexpObject : Type
SexpObject = ProductCatObject SexpClass

public export
SexpObjectMap : Type
SexpObjectMap = ProductCatObjectEndoMap SexpClass

public export
data SexpFunctor :
    (atom : Type) -> (carrier : SexpObject) -> SexpObject where
  SexpF :
    atom -> carrier SLIST -> SexpFunctor atom carrier SEXP
  SlistF :
    ListF (carrier SEXP) (carrier SLIST) ->
    SexpFunctor atom carrier SLIST

public export
SexpAlg : Type -> SexpObject -> Type
SexpAlg = ProductCatAlgebra {idx=SexpClass} . SexpFunctor

public export
FreeSexp : Type -> SexpObject -> SexpObject
FreeSexp atom = ProductCatFreeMonad' {idx=SexpClass} (SexpFunctor atom)

public export
MuSexp : Type -> SexpObject
MuSexp atom = MuProduct {idx=SexpClass} (SexpFunctor atom)

public export
Sexp : Type -> Type
Sexp = flip MuSexp SEXP

public export
Slist : Type -> Type
Slist = flip MuSexp SLIST

public export
SexpCoalg : Type -> SexpObject -> Type
SexpCoalg = ProductCatCoalgebra {idx=SexpClass} . SexpFunctor

public export
CofreeSexp : Type -> SexpObject -> SexpObject
CofreeSexp atom = ProductCatCofreeComonad {idx=SexpClass} (SexpFunctor atom)

public export
NuSexp : Type -> SexpObject
NuSexp atom = NuProduct {idx=SexpClass} (SexpFunctor atom)

-------------------------------
---- "Fixed" S-expressions ----
-------------------------------

public export
ArityMap : Type -> Type
ArityMap atom = atom -> Nat

public export
data FSexpF : {atom : Type} -> ArityMap atom -> Type -> Type where
  FSop : {atom : Type} -> {arity : ArityMap atom} -> {carrier : Type} ->
    (a : atom) -> Tuple (arity a) carrier -> FSexpF {atom} arity carrier

public export
FSexpAlg : {atom : Type} -> ArityMap atom -> Type -> Type
FSexpAlg = Algebra . FSexpF

public export
FreeFSexp : {atom : Type} -> ArityMap atom -> Type -> Type
FreeFSexp = FreeMonad' . FSexpF

public export
MuFSexp : {atom : Type} -> ArityMap atom -> Type
MuFSexp = Mu' . FSexpF

public export
FSexpCoalg : {atom : Type} -> ArityMap atom -> Type -> Type
FSexpCoalg = Coalgebra . FSexpF

public export
CofreeFSexp : {atom : Type} -> ArityMap atom -> Type -> Type
CofreeFSexp = CofreeComonad' . FSexpF

public export
NuFSexp : {atom : Type} -> ArityMap atom -> Type
NuFSexp = Nu' . FSexpF

-----------------------------------------
---- Refined S-expressions and lists ----
-----------------------------------------

public export
RefineFSexpAlgResult : {atom : Type} -> ArityMap atom -> Type -> Type -> Type
RefineFSexpAlgResult arity left right =
  Either (FSexpF arity left) right

public export
RefineFSexpAlg : {atom : Type} -> ArityMap atom -> Type -> Type -> Type
RefineFSexpAlg arity left right =
  FSexpAlg arity (RefineFSexpAlgResult arity left right)

public export
FreeRefineFSexpAlg : {atom : Type} -> ArityMap atom -> Type -> Type -> Type
FreeRefineFSexpAlg arity left right =
  RefineFSexpAlg arity (FreeFSexp arity left) right

public export
FreeRefineFSexpResult : {atom : Type} -> ArityMap atom -> Type -> Type -> Type
FreeRefineFSexpResult arity left right =
  Either (FreeFSexp arity left) right

public export
FreeRefineFSexp : {atom : Type} -> ArityMap atom -> Type -> Type -> Type
FreeRefineFSexp arity left right =
  FreeFSexp arity left -> FreeRefineFSexpResult arity left right

-------------------------------------------------
---- S-expressions with natural number atoms ----
-------------------------------------------------

public export
data NSexpClass : Type where
  NSexpNat : NSexpClass
  NSEXP : NSexpClass
  NSLIST : NSexpClass

public export
NSexpObject : Type
NSexpObject = ProductCatObject NSexpClass

public export
data NSexpFunctor : (carrier : NSexpObject) -> NSexpObject where
  NSatomF :
    NatF (carrier NSexpNat) ->
    NSexpFunctor carrier NSexpNat
  NSexpF :
    carrier NSexpNat -> carrier NSLIST ->
    NSexpFunctor carrier NSEXP
  NSlistF :
    ListF (carrier NSEXP) (carrier NSLIST) ->
    NSexpFunctor carrier NSLIST

public export
NSexpType : NSexpClass -> Type
NSexpType = MuProduct NSexpFunctor

public export
NSNat : Type
NSNat = NSexpType NSexpNat

public export
NSexp : Type
NSexp = NSexpType NSEXP

public export
NSList : Type
NSList = NSexpType NSLIST

public export
nsexpCata : ProductFreeCatamorphism NSexpFunctor
nsexpCata v carrier alg type (InFreeProduct type term) = alg type $ case type of
  NSexpNat => nsexpCataNat term
  NSEXP => nsexpCataExp term
  NSLIST => nsexpCataList term
  where
  mutual
    nsexpCataNat :
      ProductCatTermFunctor
        NSexpFunctor v
        (ProductCatFreeMonad' NSexpFunctor v) NSexpNat
        ->
      ProductCatTermFunctor NSexpFunctor v carrier NSexpNat
    nsexpCataNat (ProductCatTermVar t) = ProductCatTermVar t
    nsexpCataNat (ProductCatTermComposite com) = ProductCatTermComposite $
      case com of
        NSatomF a => NSatomF $ case a of
          Left () => Left ()
          Right n => case n of
            InFreeProduct NSexpNat n =>
              Right $ alg NSexpNat $ nsexpCataNat n

    nsexpCataExp :
      ProductCatTermFunctor
        NSexpFunctor v
        (ProductCatFreeMonad' NSexpFunctor v) NSEXP
        ->
      ProductCatTermFunctor NSexpFunctor v carrier NSEXP
    nsexpCataExp (ProductCatTermVar v) = ProductCatTermVar v
    nsexpCataExp (ProductCatTermComposite com) = ProductCatTermComposite $
      case com of
        NSexpF (InFreeProduct NSexpNat n) l =>
          case l of
            InFreeProduct NSLIST l =>
              NSexpF
                (alg NSexpNat $ nsexpCataNat n) (alg NSLIST $ nsexpCataList l)

    nsexpCataList :
      ProductCatTermFunctor
        NSexpFunctor v
        (ProductCatFreeMonad' NSexpFunctor v) NSLIST
        ->
      ProductCatTermFunctor NSexpFunctor v carrier NSLIST
    nsexpCataList (ProductCatTermVar v) = ProductCatTermVar v
    nsexpCataList (ProductCatTermComposite com) = ProductCatTermComposite $
      case com of
        NSlistF l => NSlistF $ case l of
          Left () => Left ()
          Right ((InFreeProduct NSEXP x), l') =>
            case l' of
              InFreeProduct NSLIST l'' =>
                Right
                  ((alg NSEXP $ nsexpCataExp x),
                   (alg NSLIST $ nsexpCataList l''))

---------------------------------------------------------
---------------------------------------------------------
---- Interpretation of S-expressions into categories ----
---------------------------------------------------------
---------------------------------------------------------

public export
data UniversalProperty : Type where
  -- Equalizers and coequalizers.
  ConnectedLimits : UniversalProperty
  -- Initial algebras and terminal coalgebras of polynomial endofunctors.
  InductiveTypes : UniversalProperty

public export
data SexpCategory : Type where
  SubstCat : SexpCategory
  RefinedSubstCat : SexpCategory
  ADTCat : SexpCategory
  RefinedADTCat : SexpCategory

public export
hasProperty : UniversalProperty -> SexpCategory -> Bool
hasProperty ConnectedLimits SubstCat = False
hasProperty ConnectedLimits RefinedSubstCat = True
hasProperty ConnectedLimits ADTCat = False
hasProperty ConnectedLimits RefinedADTCat = True
hasProperty InductiveTypes SubstCat = False
hasProperty InductiveTypes RefinedSubstCat = False
hasProperty InductiveTypes ADTCat = True
hasProperty InductiveTypes RefinedADTCat = True

public export
SMorphismInterpretation : Type
SMorphismInterpretation =
  (domain : Type ** codomain : Type ** domain -> codomain)

public export
NatTransInterpretation : Type
NatTransInterpretation =
  (f : Type -> Type ** g : Type -> Type ** (x : Type) -> f x -> g x)

public export
data SexpInterpretation : NSexpClass -> Type where
  SnatAsNat : Nat -> SexpInterpretation NSexpNat
  SexpAsObject : Type -> SexpInterpretation NSEXP
  SexpAsMorphism : SMorphismInterpretation -> SexpInterpretation NSEXP
  SexpAsFunctor : (Type -> Type) -> SexpInterpretation NSEXP
  SexpAsNatTrans : NatTransInterpretation -> SexpInterpretation NSEXP
  SlistAsObjects : List Type -> SexpInterpretation NSLIST
  SlistAsMorphisms :
    List SMorphismInterpretation -> SexpInterpretation NSLIST
  SlistAsFunctors : List (Type -> Type) -> SexpInterpretation NSLIST
  SlistAsNatTrans : List NatTransInterpretation -> SexpInterpretation NSLIST

public export
record SexpCheckResult (inputType : NSexpClass) where
  constructor SexpInterpretations
  Input : NSexpType inputType
  InputInterpretation : Maybe (SexpInterpretation inputType)
  AllInterpretations :
    (type : NSexpClass) -> NSexpType type -> Maybe (SexpInterpretation type)

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
  bimap f g (FactorsF l) = FactorsF $ mapSnd (bimap (bimap f $ mapSnd g) g) l

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
  bimap f g (PolyTermsF t) = PolyTermsF $ mapSnd (bimap (bimap f g) g) t

export
polyTerms :
  PolynomialF coefficient carrier ->
  ListF (PowerF coefficient carrier) carrier
polyTerms (PolyTermsF t) = t

export
polyFactors :
  PolynomialF coefficient carrier ->
  ListF (ListF (coefficient, NatF carrier) carrier) carrier
polyFactors = mapSnd (mapFst powerFactors) . polyTerms

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
-- `FreeMonad'` (AKA `F*`).  So to generate polynomial _recursive_ types, we add
-- to `PolynomialF` the option of applying `FreeMonad'` to an existing polynomial
-- type.
public export
data PolyRecTypeF : Type -> Type -> Type where
  PolyTypeFreeF :
    functor -> PolyRecTypeF type functor
  PolyRecTypeADTF :
    PolyTypeF type functor -> PolyRecTypeF type functor
