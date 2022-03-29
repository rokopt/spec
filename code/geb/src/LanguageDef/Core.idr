module LanguageDef.Core

import Library.IdrisUtils

-- “Ah Love! could thou and I with Fate conspire
-- To grasp this sorry Scheme of Things entire,
-- Would not we shatter it to bits -- and then
-- Re-mould it nearer to the Heart's Desire!”
--  - _Rubaiyat of Omar Khayyam_ (tr. Edward FitzGerald)

%default total

-------------------------------------
---- Cartesian closed categories ----
-------------------------------------



-------------------------------------
-------------------------------------
---- Categorial algebra in Idris ----
-------------------------------------
-------------------------------------

--------------------
---- F-Algebras ----
--------------------

public export
Algebra : (Type -> Type) -> Type -> Type
Algebra f a = f a -> a

-- For a given functor `F`, form the functor `Fa` defined by
-- `Fa[x] = a + F[x]`.  We call it `TermFunctor` because it turns
-- an endofunctor which we can interpret as representing a datatype
-- into one which we can interpret as representing open terms of
-- that datatype with variables drawn from type `v`.
public export
data TermFunctor : (Type -> Type) -> Type -> (Type -> Type) where
  TermVar : {f : Type -> Type} ->
    a -> TermFunctor f a x
  TermComposite : {f : Type -> Type} ->
    f x -> TermFunctor f a x

public export
Functor f => Bifunctor (TermFunctor f) where
  bimap f' g' (TermVar x) = TermVar $ f' x
  bimap f' g' (TermComposite x) = TermComposite $ map g' x

-- An algebra on a functor representing a type of open terms (as generated
-- by `TermFunctor` above) may be viewed as a polymorphic algebra, because
-- for each object `v` it generates an `F[v]`-algebra on an any given carrier
-- object.  When `v` is the initial object (`Void`), it specializes to
-- generating `F`-algebras.
public export
TermAlgebra : (Type -> Type) -> Type -> Type -> Type
TermAlgebra f v a = Algebra (TermFunctor f v) a

-- If `F` has an initial algebra, then for every object `a`, the functor
-- `Fa` defined above also has an initial algebra, which is isomorphic
-- to `FreeMonad[F, a]`.  Thus `FreeMonad` allows us to create initial
-- `Fa`-algebras parameterized over arbitrary objects `a`, with the initial
-- algebra of `F` itself being the special case where `a` is the initial object
-- (`Void`).  `FreeMonad` is sometimes written `F*`.
--
-- Note that `FreeMonad` itself is a composition, but one which leaves
-- the category in which the endofunctors live before returning:  it is
-- the monad induced by the free-forgetful adjunction between the category
-- of endofunctors and the category of their F-algebras.  (The comonad
-- induced by the dual forgetful-cofree adjunction is `CofreeComonad`.)
public export
data FreeMonad : (Type -> Type) -> (Type -> Type) where
  InFree : (TermFunctor f a) (FreeMonad f a) -> FreeMonad f a

public export
inFreeVar : {f : Type -> Type} -> a -> FreeMonad f a
inFreeVar = InFree . TermVar

public export
inFreeComposite : {f : Type -> Type} -> f (FreeMonad f a) -> FreeMonad f a
inFreeComposite = InFree . TermComposite

public export
outFree : FreeMonad f a -> TermFunctor f a (FreeMonad f a)
outFree (InFree x) = x

-- Not all endofunctors have initial algebras.  If an endofunctor
-- _does_ have an initial algebra, then this is the signature of
-- its parameterized catamorphism (fold).
Catamorphism : (Type -> Type) -> Type -> Type -> Type
Catamorphism f v a = TermAlgebra f v a -> FreeMonad f v -> a

-- Special case of `FreeMonad` where `v` is `Void`.
-- This is the fixpoint of an endofunctor (if it exists).
public export
Mu : (Type -> Type) -> Type
Mu f = FreeMonad f Void

----------------------
---- F-Coalgebras ----
----------------------

public export
Coalgebra : (Type -> Type) -> Type -> Type
Coalgebra f a = a -> f a

-- For a given functor `F`, form the functor `Fa` defined by
-- `Fa[x] = a * F[x]`.  We call it `TreeFunctor` because it turns
-- an endofunctor which we can interpret as representing a datatype
-- into one which we can interpret as representing potentially infinite
-- tress of that datatype with labels drawn from type `v`.
public export
data TreeFunctor : (Type -> Type) -> Type -> (Type -> Type) where
  TreeNode : {f : Type -> Type} -> {0 a, x : Type} ->
    a -> f x -> TreeFunctor f a x

export
treeLabel : {f : Type -> Type} -> {a, x : Type} -> TreeFunctor f a x -> a
treeLabel (TreeNode a' _) = a'

export
treeSubtree : {f : Type -> Type} -> {a, x : Type} -> TreeFunctor f a x -> f x
treeSubtree (TreeNode _ fx) = fx

export
Functor f => Bifunctor (TreeFunctor f) where
  bimap f' g' (TreeNode x fx) = TreeNode (f' x) (map g' fx)

-- A coalgebra on a functor representing a type of labeled trees (as generated
-- by `TreeFunctor` above) may be viewed as a polymorphic coalgebra, because
-- for each object `v` it generates an `F[v]`-coalgebra on an any given carrier
-- object.  When `v` is the terminal object (`Unit`), it specializes to
-- generating `F`-coalgebras.
public export
TreeCoalgebra : (Type -> Type) -> Type -> Type -> Type
TreeCoalgebra f v a = Coalgebra (TreeFunctor f v) a

-- If `F` has a terminal coalgebra, then for every object `a`, the functor
-- `Fa` defined above also has a terminal coalgebra, which is isomorphic
-- to `CofreeComonad[F, a]`.  Thus `CofreeComonad` allows us to create terminal
-- `Fa`-coalgebras parameterized over arbitrary objects `a`, with the terminal
-- coalgebra of `F` itself being the special case where `a` is the terminal
-- object (`Unit`).  `CofreeComonad` is sometimes written `Finf`.
public export
data CofreeComonad : (Type -> Type) -> (Type -> Type) where
  InCofree :
    {f : Type -> Type} -> {a : Type} ->
    Inf (TreeFunctor f a (CofreeComonad f a)) -> CofreeComonad f a

public export
inCofreeTree : {a : Type} -> {f : Type -> Type} ->
  a -> f (CofreeComonad f a) -> CofreeComonad f a
inCofreeTree x fx = InCofree $ TreeNode x fx

public export
outCofree : {f : Type -> Type} -> {a : Type} ->
  CofreeComonad f a -> TreeFunctor f a (CofreeComonad f a)
outCofree (InCofree x) = x

-- Not all endofunctors have terminal coalgebras.  If an endofunctor
-- _does_ have a terminal coalgebra, then this is the signature of
-- its parameterized anamorphism (unfold).
Anamorphism : (Type -> Type) -> Type -> Type -> Type
Anamorphism f v a = TreeCoalgebra f v a -> a -> CofreeComonad f v

-- Special case of `CofreeComonad` where `v` is `Unit`.
-- This is the cofixpoint of an endofunctor (if it exists).
public export
Nu : (Type -> Type) -> Type
Nu f = CofreeComonad f ()

----------------
---- Magmas ----
----------------

-- A functor which generates binary combinations of its input type.
-- Note that this is a generator, not an interface -- the user does
-- not assert that some type implements the binary operation, but
-- rather calls the functor to _produce_ a type which has a binary
-- operation on the input type.
infixr 8 <>
public export
data MagmaF : Type -> Type where
  (<>) : a -> a -> MagmaF a

public export
Functor MagmaF where
  map f (x <> y) = f x <> f y

-------------------
---- Relations ----
-------------------

-- The Idris type of symmetric binary relations.
SymBinRel : Type -> Type
SymBinRel a = a -> a -> Type

-------------------------------
---- Equivalence relations ----
-------------------------------

-- Functors which generate an equivalence relation.
-- The bundle describes which elements are being asserted to be equivalent.
public export
data EquivTermF : Type -> Type -> Type where
  EqReflF : a -> EquivTermF a rel
  EqSymF : rel -> EquivTermF a rel
  EqTransF : rel -> rel -> EquivTermF a rel

public export
Bifunctor EquivTermF where
  bimap f _ (EqReflF a) = EqReflF $ f a
  bimap _ g (EqSymF rel) = EqSymF $ g rel
  bimap _ g (EqTransF rel rel') = EqTransF (g rel) (g rel')

--------------------
---- Semigroups ----
--------------------

infixr 8 <<>>
public export
data SemigroupOpF :
    ((Type -> Type), (Type -> Type -> Type)) -> (Type -> Type) where
  (<<>>) : a -> a -> SemigroupOpF (op, rel) a

-----------------
---- Monoids ----
-----------------

-- A functor whose free algebra generates a free monoid on the input type.
-- It expresses the identity and associativity laws by including terms
-- which express rewriting according to those laws, in the style of
-- a quotient type.
public export
data MonoidF : Type -> Type where
  MId : MonoidF a
  MOp : a -> a -> MonoidF a
  MCancelIdL : a -> MonoidF a
  MCancelIdR : a -> MonoidF a
  MShiftR : a -> a -> a -> MonoidF a

------------------------------------------
---- Slices, bundles, and refinements ----
------------------------------------------

SliceObj : Type -> Type
SliceObj c = (a : Type ** a -> c)

SliceObjDomain : {c : Type} -> SliceObj c -> Type
SliceObjDomain (a ** _) = a

SliceObjMap : {c : Type} -> (x : SliceObj c) -> (SliceObjDomain x -> c)
SliceObjMap (_ ** mx) = mx

ExtEq : {a, b : Type} -> (f, g : a -> b) -> Type
ExtEq {a} f g = (elem : a) -> f elem = g elem

SliceMorphism : {c : Type} -> SliceObj c -> SliceObj c -> Type
SliceMorphism x y =
  (w : SliceObjDomain x -> SliceObjDomain y **
   ExtEq (SliceObjMap y . w) (SliceObjMap x))

SliceMorphismMap : {c : Type} -> {x, y : SliceObj c} ->
  SliceMorphism x y -> SliceObjDomain x -> SliceObjDomain y
SliceMorphismMap (w ** _) = w

SliceMorphismEq : {c : Type} -> {x, y : SliceObj c} ->
  (f : SliceMorphism x y) ->
  ExtEq (SliceObjMap y . SliceMorphismMap {x} {y} f) (SliceObjMap x)
SliceMorphismEq (_ ** eq) = eq

SliceId : {c : Type} -> (w : SliceObj c) -> SliceMorphism w w
SliceId (a ** x) = (id ** \_ => Refl)

SliceCompose : {c : Type} -> {u, v, w : SliceObj c} ->
  SliceMorphism v w -> SliceMorphism u v -> SliceMorphism u w
SliceCompose {c} {u} {v} {w} g f =
  (SliceMorphismMap g . SliceMorphismMap f **
   \elem =>
    trans
      (SliceMorphismEq g (SliceMorphismMap f elem))
      (SliceMorphismEq f elem))

Bundle : Type
Bundle = (base : Type ** SliceObj base)

BundleBase : Bundle -> Type
BundleBase (base ** (_ ** _)) = base

BundleTotal : Bundle -> Type
BundleTotal (_ ** (tot ** _)) = tot

BundleProj :
  (bundle : Bundle) -> (BundleTotal bundle) -> (BundleBase bundle)
BundleProj (_ ** (_ ** proj)) = proj

BundleFiber : (bundle : Bundle) -> (baseElem : BundleBase bundle) -> Type
BundleFiber bundle baseElem =
  (totalElem : BundleTotal bundle ** (BundleProj bundle totalElem = baseElem))

RefinementBy : Type -> Type
RefinementBy = SliceObj . Maybe

Refinement : Type
Refinement = DPair Type RefinementBy

RefinementBundle : Refinement -> Bundle
RefinementBundle (base ** slice) = (Maybe base ** slice)

RefinementBase : Refinement -> Type
RefinementBase (base ** _) = base

RefinementTotal : Refinement -> Type
RefinementTotal = BundleTotal . RefinementBundle

RefinementProj :
  (r : Refinement) -> (RefinementTotal r) -> Maybe (RefinementBase r)
RefinementProj (_ ** (_ ** proj)) = proj

RefinementFiber :
  (r : Refinement) -> (baseElem : Maybe (RefinementBase r)) -> Type
RefinementFiber (base ** (tot ** proj)) baseElem =
  BundleFiber (Maybe base ** (tot ** proj)) baseElem

JustFiber : (r : Refinement) -> (baseElem : RefinementBase r) -> Type
JustFiber (base ** (tot ** proj)) baseElem =
  BundleFiber (Maybe base ** (tot ** proj)) (Just baseElem)

NothingFiber : (r : Refinement) -> Type
NothingFiber (base ** (tot ** proj)) =
  BundleFiber (Maybe base ** (tot ** proj)) Nothing

-------------------------------
---- Higher-order functors ----
-------------------------------

-- A bifunctor applied to a type is a functor.  This is simply the
-- currying adjunction in the category of functors -- the functor
-- categories `[C, [D, E]]` and `[C × D, E]` are equivalent.
public export
Bifunctor f => Functor (f a) where
  map = mapSnd

-- A bifunctor with its arguments flipped is a bifunctor.  This
-- reflects the symmetry of the product.
public export
Bifunctor f => Bifunctor (flip f) where
  bimap f g = bimap g f

-------------------------
---- Natural numbers ----
-------------------------

public export
data NatF : (carrier : Type) -> Type where
  ZeroF : NatF carrier
  SuccF : carrier -> NatF carrier

public export
Functor NatF where
  map _ ZeroF = ZeroF
  map f (SuccF n) = SuccF $ f n

public export
natCata : Catamorphism NatF v a
natCata alg (InFree t) = alg $ case t of
  TermVar x => TermVar x
  TermComposite n => TermComposite $ case n of
    ZeroF => ZeroF
    SuccF n' => SuccF $ natCata alg n'

---------------
---- Lists ----
---------------

public export
data ListF : (atom, carrier : Type) -> Type where
  NilF : ListF atom carrier
  ConsF : atom -> carrier -> ListF atom carrier

public export
Bifunctor ListF where
  bimap f g NilF = NilF
  bimap f g (ConsF a l) = ConsF (f a) (g l)

public export
listCata : Catamorphism (ListF atom) v a
listCata alg (InFree t) = alg $ case t of
  TermVar x => TermVar x
  TermComposite l => TermComposite $ case l of
    NilF => NilF
    ConsF a l' => ConsF a $ listCata alg l'

---------------------
---- Polynomials ----
---------------------

-- A univariate, finite-degree power.
public export
data PowerF : (coefficient, carrier : Type) -> Type where
  FactorsF :
    ListF (coefficient, NatF carrier) carrier ->
    PowerF coefficient carrier

public export
Bifunctor PowerF where
  bimap f g (FactorsF l) = FactorsF $ bimap (bimap f $ map g) g l

public export
powerToListAlg : Algebra (PowerF v) a -> Algebra (ListF (v, NatF a)) a
powerToListAlg alg = alg . FactorsF

export
powerFactors :
  PowerF coefficient carrier ->
  ListF (coefficient, NatF carrier) carrier
powerFactors (FactorsF l) = l

-- A univariate, finite-degree polynomial.
public export
data PolynomialF : (coefficient, carrier : Type) -> Type where
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

public export
polyToPowerAlg : Algebra (PolynomialF v) a -> Algebra (ListF (PowerF v a)) a
polyToPowerAlg alg = alg . PolyTermsF

public export
polyToListAlg :
  Algebra (PolynomialF v) a -> Algebra (ListF (ListF (v, NatF a) a)) a
polyToListAlg alg = polyToPowerAlg alg . mapFst FactorsF

-----------------------------
---- Polynomial algebras ----
-----------------------------

-- Although not _all_ endofunctors have initial algebras, there are some
-- _classes_ of endofunctors that can be guaranteed to have initial algebras.
-- Polynomials are one such class.

public export
powerCata : Catamorphism (PowerF coefficient) v a
powerCata alg (InFree t) = alg $ mapTerm t
where
  mutual
    mapTerm :
      TermFunctor (PowerF coefficient) v (FreeMonad (PowerF coefficient) v) ->
      TermFunctor (PowerF coefficient) v a
    mapTerm t = case t of
      TermVar x => TermVar x
      TermComposite t => TermComposite $ mapPower t

    mapPower :
      PowerF coefficient (FreeMonad (PowerF coefficient) v) ->
      PowerF coefficient a
    mapPower p = case p of
      FactorsF fs => FactorsF $ case fs of
        NilF => NilF
        ConsF (f', n') (InFree fs') =>
          ConsF (f', mapNat n') $ alg $ case fs' of
            TermVar x => TermVar x
            TermComposite fs' => TermComposite $ mapPower fs'

    mapNat : NatF (FreeMonad (PowerF coefficient) v) -> NatF a
    mapNat n = case n of
      ZeroF => ZeroF
      SuccF (InFree t) => SuccF $ alg $ case t of
        TermVar x => TermVar x
        TermComposite t => TermComposite $ mapPower t

public export
polyCata : Catamorphism (PolynomialF coefficient) v a
polyCata alg (InFree t) = alg $ mapTerm t
where
  mutual
    mapTerm :
      TermFunctor (PolynomialF coefficient) v
        (FreeMonad (PolynomialF coefficient) v) ->
      TermFunctor (PolynomialF coefficient) v a
    mapTerm t = case t of
      TermVar x => TermVar x
      TermComposite t => TermComposite $ mapPoly t

    mapPower :
      PowerF coefficient (FreeMonad (PolynomialF coefficient) v) ->
      PowerF coefficient a
    mapPower p = case p of
      FactorsF fs => FactorsF $ case fs of
        NilF => NilF
        ConsF (f', n') (InFree fs') => ConsF (f', mapNat n')
          $ alg $ case fs' of
            TermVar x => TermVar x
            TermComposite fs' => TermComposite $ mapPoly fs'

    mapPoly :
      PolynomialF coefficient (FreeMonad (PolynomialF coefficient) v) ->
      PolynomialF coefficient a
    mapPoly p = case p of
      PolyTermsF fs => PolyTermsF $ case fs of
        NilF => NilF
        ConsF f' (InFree fs') => ConsF (mapPower f') $ alg $ case fs' of
          TermVar x => TermVar x
          TermComposite fs' => TermComposite $ mapPoly fs'

    mapNat : NatF (FreeMonad (PolynomialF coefficient) v) -> NatF a
    mapNat n = case n of
      ZeroF => ZeroF
      SuccF (InFree t) => SuccF $ alg $ case t of
        TermVar x => TermVar x
        TermComposite t => TermComposite $ mapPoly t

-- Next, we introduce a way of interpreting polynomials as datatypes.
-- A polynomial endofunctor may be viewed as simply a polynomial, and
-- may be factored into one, but when representing types with
-- endofunctors, we may wish to factor out commonality amongst types
-- and compose them from smaller components. Such types could theoretically
-- be fully distributed into flat polynomials like `PolynomialF`, but
-- when using polynomials as types, we can gain expressivity with explicit
-- composition.
public export
data PolyTypeF : (type, functor : Type) -> Type where
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
data PolyRecTypeF : (type, functor : Type) -> Type where
  PolyTypeFreeF :
    functor -> PolyRecTypeF type functor
  PolyRecTypeADTF :
    PolyTypeF type functor -> PolyRecTypeF type functor

-----------------------------
---- Paths and morphisms ----
-----------------------------

-- A functor which generates paths through directed graphs.
public export
data PathF : Type -> Type -> Type where
  -- A loop is labeled by its sole endpoint.
  LoopF : vertex -> PathF vertex path
  -- A composition is labeled by its source, intermediate vertex, and
  -- target, followed by the two paths being composed, with the second
  -- path pointing to the first, as in composition of morphisms in categories.
  ComposeF : vertex -> vertex -> vertex -> path -> path -> PathF vertex path

public export
Bifunctor PathF where
  bimap f _ (LoopF v) = LoopF $ f v
  bimap f g (ComposeF s i t q p) = ComposeF (f s) (f i) (f t) (g q) (g p)

public export
pathCata : Catamorphism (PathF vertex) v a
pathCata alg (InFree t) = alg $ case t of
  TermVar x => TermVar x
  TermComposite x => TermComposite $ case x of
    LoopF v => LoopF $ v
    ComposeF s i t q p => ComposeF s i t (pathCata alg q) (pathCata alg p)

-------------
-------------
---- Geb ----
-------------
-------------

-- Geb is defined by doing category theory "in reverse":  rather than
-- defining some structures and then proving that they are categories,
-- we axiomatize the notions of categories, define some higher categories,
-- and then examine the lower-order categories which emerge necessarily
-- from our postulating the existence of the higher categories.
--
-- The higher categories are defined with with two primary goals:
--
--  - To be able to express all definitions as universal constructions,
--    so that _any_ correct interpreters for Geb must be isomorphic.
--  - To enable the definitions to be expressed in software in a homoiconic
--    and "à la carte" style, so that the languages (plural -- each category
--    is a language) may be extended, and new languages defined, either from
--    scratch or by extending existing ones, including Geb itself.
--
-- Any combination of universal properties defines a category inductively
-- as the smallest category which contains all objects and morphisms specified
-- by those universal constructions.  The high-level categorial construction
-- of Geb overall defines a category containing each combination of properties
-- by creating a defining two-category for it, generating other categories from
-- the root category (which is the category to be defined), such as product
-- categories, functor categories, and F-(co)algebra categories, and
-- specifying the functors, natural transformations, and adjunctions which
-- define the universal properties.  The objects and morphisms of the defined
-- category are therefore precisely the ones required for the specified
-- functors, natural transformations, and adjunctions to exist, and no more.
-- (This is the reverse of typical category theory, where we define various
-- collections of objects and morphisms and then investigate which functors,
-- natural transformations, and adjunctions can be found among them.)
--
-- The set of universal properties defined by the core language specification
-- of Geb is designed to be precisely those which are required to allow any
-- other possible universal constructions to be defined _in_ Geb, including
-- by extension of Geb itself within Geb (as well as devising new categories
-- from scratch).  Conveniently for programmers, that set is drawn from the
-- traditional constructions of programming languages -- initial and terminal
-- objects, products and coproducts, and initial algebras and terminal
-- coalgebras -- as well as constructions less common in the most popular
-- languages but ubiquitous in dependently-typed languages, such as equality
-- types, and (albeit, I think, less commonly) quotient types.
--
-- The set of universal properties required to be defined by the core of Geb
-- does _not_ include exponential objects (also known as currying, and also
-- known as the product-hom adjunction).  This is the categorial reflection
-- of Gödel's construction when proving the incompleteness theorems:  the
-- arithmetic required for self-representation does not need to be higher-order.
-- But self-representation does suffice to define what it _means_ to define
-- other, stronger languages correctly.  So it is in libraries written in Geb,
-- not in the core language definition, that extensions to strictly stronger
-- languages and logics can be made.  The self-representation remains, and
-- consequently, so does the well-typed (including dependently-typed)
-- metaprogramming.
--
-- In addition to well-typed metaprogramming, the explicit use of multiple
-- categories within the same language makes Geb a "programming language of
-- programming languages", intended particularly for uses such as correct-by-
-- construction compilers, and other language-design matters such as modular
-- language extension and algebraic effects.
--
-- The refinement types required to express statically-checked formal
-- properties can be expressed in two equivalent ways.
-- This equivalence translates between two different ways of constraining
-- the interpretation of ADTs:
--   - The categorial way: equalizers and coequalizers
--   - The programming-language way: a typechecker function
--
-- Refined types can be "compiled" to unrefined ones (by erasing the equalizers
-- and coequalizers, or equivalently, by using the categorial equivalence to map
-- from the refined category to the unrefined-plus-typechecker-morphism
-- category and then forgetting the typechecker morphism).
--
-- For any object `a` of any category `C` which has a terminal object, we
-- define the "term category" of `a` as the category whose objects are morphisms
-- of `C` from the terminal object (in `C`) into `a` and whose morphisms are the
-- endomorphisms (in `C`) of `a` which make the resulting diagrams commute.
-- This is a special case of a comma category where the two functors which
-- define the comma category are:
--  - The functor from the terminal category to `C` whose value (on its only
--    input) is the terminal object of `C`
--  - The inclusion functor into `C` from the full subcategory of `C` whose
--    only object is `a`)
-- Geb's notion of well-typed metaprogramming is that each category in its
-- mathematical definition is equivalent to the term category of one of its
-- objects (which is unique up to unique isomorphism, because it is isomorphic
-- to a mathematical object defined solely by universal constructions), and
-- that one of its objects can be interpreted as the type of all of its terms.
--
-- Note that those terms are heterogeneous -- some are categories, some are
-- functors, some are other, programming-related constructs entirely.  The
-- object emerges, after all, as a type in a software implementation.  So
-- while that object (or its term category) can be interpreted as a higher
-- category, because some of its term category's objects are categories, not
-- _all_ of its term category's objects are categories.  This is useful,
-- because it means that terms can represent heterogeneous functions; someone
-- could write, for example, a function from natural numbers to programming
-- languages, where the output of the function for input `n` is `n`-order
-- arithmetic.

mutual
  data GebUniversalPropF : Type -> Type where
    InitialObjectProp : GebUniversalPropF prop
    TerminalObjectProp : GebUniversalPropF prop
    ProductProp : GebUniversalPropF prop
    CoproductProp : GebUniversalPropF prop
    EqualizerProp : GebUniversalPropF prop
    CoequalizerProp : GebUniversalPropF prop
    FreeAlgebraProp : GebUniversalPropF prop
    CofreeAlgebraProp : GebUniversalPropF prop
    HigherOrderProp : GebUniversalPropF prop
    TuringCompleteProp : GebUniversalPropF prop

  -- The functor which defines the object of the refined first-order ADT
  -- category from which all other constructs of Geb can be extracted, and
  -- which can be extended to generate super-languages of Geb.
  data GebTermF : Type -> Type -> Type where
    GebUP : GebUniversalPropF prop -> GebTermF prop term

    -- The object in the category of first-order refined ADTs whose term
    -- category is isomorphic to the Idris GebTypeF (or that of any other
    -- correct interpreter in any host language).
    Geb : GebTermF prop term

FreeGebTerm : Type -> Type -> Type
FreeGebTerm prop = FreeMonad $ GebTermF prop

mutual
  gebCata : Catamorphism (GebTermF prop) v a
  gebCata alg (InFree x) = alg $ gebTermCata alg x

  gebTermCata :
    TermAlgebra f v a ->
    TermFunctor (GebTermF prop) v (FreeMonad (GebTermF prop) v) ->
    TermFunctor (GebTermF prop) v a
  gebTermCata alg t = case t of
    TermVar v' => TermVar v'
    TermComposite x' => TermComposite $ case x' of
      GebUP prop => GebUP prop
      Geb => Geb

CofreeGebTerm : Type -> Type -> Type
CofreeGebTerm prop = CofreeComonad $ GebTermF prop
