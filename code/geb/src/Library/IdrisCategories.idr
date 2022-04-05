module Library.IdrisCategories

import Library.IdrisUtils

%default total

------------------------------------------
------------------------------------------
---- Interpreting categories in Idris ----
------------------------------------------
------------------------------------------

public export
DigraphEdgeFibration : Type -> Type -> Type
DigraphEdgeFibration vertex edge = edge -> (vertex, vertex)

public export
record DirectedGraph where
  constructor DirectedGraphComponents
  VertexType : Type
  EdgeType : Type

  -- Returns the source and target.  This function therefore
  -- fibers the type of edges by the type of vertices (it
  -- forms a bundle from edges to vertices, with the type
  -- of edges as the total space, the type of vertices as
  -- the base space, and this function as the projection; if
  -- the vertex and edge types are objects of a category, then
  -- this fibration (which is a morphism) can also be viewed
  -- (together with the edge object) as an object of the slice
  -- category over the type of pairs of vertices).
  EdgeProjection : DigraphEdgeFibration VertexType EdgeType

public export
graphSource : {graph : DirectedGraph} -> EdgeType graph -> VertexType graph
graphSource {graph} = fst . EdgeProjection graph

public export
graphTarget : {graph : DirectedGraph} -> EdgeType graph -> VertexType graph
graphTarget {graph} = snd . EdgeProjection graph

-- Implementing this interface provides a way of interpreting a directed
-- graph into the Idris type system as a category.
public export
record DigraphCategoryInterpretation (graph : DirectedGraph) where
  constructor DigraphCategoryInterpretations
  VertexInterpretation : VertexType graph -> Type
  EdgeInterpretation :
    (m : EdgeType graph) ->
    (VertexInterpretation (graphSource {graph} m)) ->
    (VertexInterpretation (graphTarget {graph} m))

public export
record InterpretedDigraph where
  constructor InterpretedDigraphComponents
  UnderlyingGraph : DirectedGraph
  GraphInterpretation : DigraphCategoryInterpretation UnderlyingGraph

----------------------------------
----------------------------------
---- Idris product categories ----
----------------------------------
----------------------------------

-- The objects of a product category, where the product is represented by
-- a function from an index type (as opposed to by a pair or a list -- the
-- function type allows the assignment of names from a user-selected domain).
public export
ProductCatObject : Type -> Type
ProductCatObject idx = idx -> Type

public export
ProductCatMorphism : {idx : Type} ->
  ProductCatObject idx -> ProductCatObject idx -> Type
ProductCatMorphism {idx} dom cod = (i : idx) -> dom i -> cod i

public export
ProductCatObjectMap : Type -> Type -> Type
ProductCatObjectMap idx idx' = ProductCatObject idx -> ProductCatObject idx'

public export
ProductCatObjectEndoMap : Type -> Type
ProductCatObjectEndoMap idx = ProductCatObjectMap idx idx

public export
ProductCatMorphismMap :
  {idx, idx' : Type} -> ProductCatObjectMap idx idx' -> Type
ProductCatMorphismMap {idx} {idx'} objmap =
  (dom, cod : ProductCatObject idx) ->
  (m : ProductCatMorphism dom cod) ->
  ProductCatMorphism (objmap dom) (objmap cod)

public export
ProductCatMorphismEndoMap : {idx : Type} -> ProductCatObjectEndoMap idx -> Type
ProductCatMorphismEndoMap = ProductCatMorphismMap

public export
ProductCatFunctor : Type -> Type -> Type
ProductCatFunctor idx idx' =
  DPair (ProductCatObjectMap idx idx') ProductCatMorphismMap

public export
ProductCatEndofunctor : Type -> Type
ProductCatEndofunctor idx = ProductCatFunctor idx idx

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---- Categorial algebra on Idris universe categories and product categories ----
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

-------------------------------------
---- F-algebras and F-coalgebras ----
-------------------------------------

-- The categorial definition of an F-algebra.
public export
Algebra : (Type -> Type) -> Type -> Type
Algebra f a = f a -> a

-- The dual of an F-algebra:  an F-coalgebra.
public export
Coalgebra : (Type -> Type) -> Type -> Type
Coalgebra f a = a -> f a

-- The version of `Algebra` for an Idris product category.
public export
ProductCatAlgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> Type
ProductCatAlgebra f a = ProductCatMorphism (f a) a

public export
ProductCatCoalgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> Type
ProductCatCoalgebra f a = ProductCatMorphism a (f a)

--------------------------------------
---- Open terms and labeled trees ----
--------------------------------------

-- For a given functor `F` and object `v`, form the functor `Fv` defined by
-- `Fv[x] = v + F[x]`.  We call it `TermFunctor` because it turns
-- an endofunctor which we can interpret as representing a datatype
-- into one which we can interpret as representing open terms of
-- that datatype with variables drawn from type `v`.
public export
data TermFunctor : (Type -> Type) -> Type -> (Type -> Type) where
  TermVar : {f : Type -> Type} -> {0 v, a : Type} ->
    v -> TermFunctor f v a
  TermComposite : {f : Type -> Type} -> {0 v, a : Type} ->
    f a -> TermFunctor f v a

public export
Functor f => Bifunctor (TermFunctor f) where
  bimap f' g' (TermVar x) = TermVar $ f' x
  bimap f' g' (TermComposite x) = TermComposite $ map g' x

-- For a given functor `F`, form the functor `Fa` defined by
-- `Fa[x] = a * F[x]`.  We call it `TreeFunctor` because it turns
-- an endofunctor which we can interpret as representing a datatype
-- into one which we can interpret as representing potentially infinite
-- trees of that datatype with labels drawn from type `v`.
-- This is the dual of `TermFunctor`.
public export
data TreeFunctor : (Type -> Type) -> Type -> (Type -> Type) where
  TreeNode : {f : Type -> Type} -> {0 l, a : Type} ->
    l -> f a -> TreeFunctor f l a

export
Functor f => Bifunctor (TreeFunctor f) where
  bimap f' g' (TreeNode x fx) = TreeNode (f' x) (map g' fx)

-- The product-category version of `TermFunctor`.  In the case of just two
-- categories, for example, if `F` and `G` are the components of the input
-- functor, each going from the product category to one of the components,
-- and `v` and `w` are the components of the variable type, then this
-- expression becomes:
--
--  `FGvw[x,y] = (v + F[x,y], w + G[x,y])`
public export
data ProductCatTermFunctor : {idx : Type} ->
    ProductCatObjectEndoMap idx ->
    ProductCatObject idx ->
    ProductCatObjectEndoMap idx where
  ProductCatTermVar : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} ->
    {0 v, a : ProductCatObject idx} ->
    {i : idx} ->
    v i -> ProductCatTermFunctor f v a i
  ProductCatTermComposite : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} ->
    {0 v, a : ProductCatObject idx} ->
    {i : idx} ->
    f a i -> ProductCatTermFunctor f v a i

-- The dual of `ProductCatTermFunctor`, also known as the product-category
-- version of `TreeFunctor`.
public export
data ProductCatTreeFunctor : {idx : Type} ->
    ProductCatObjectEndoMap idx ->
    ProductCatObject idx ->
    ProductCatObjectEndoMap idx where
  ProductCatTreeNode : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} ->
    {0 l, a : ProductCatObject idx} ->
    {i : idx} ->
    l i -> f a i -> ProductCatTreeFunctor f l a i

export
treeLabel : {f : Type -> Type} -> {l, a : Type} -> TreeFunctor f l a -> l
treeLabel (TreeNode a' _) = a'

export
treeSubtree : {f : Type -> Type} -> {l, a : Type} -> TreeFunctor f l a -> f a
treeSubtree (TreeNode _ fx) = fx

export
treeLabelProduct : ProductCatTreeFunctor f l a i -> l i
treeLabelProduct (ProductCatTreeNode a' _) = a'

export
treeSubtreeProduct : ProductCatTreeFunctor f l a i -> f a i
treeSubtreeProduct (ProductCatTreeNode _ fx) = fx

-- An algebra on a functor representing a type of open terms (as generated
-- by `TermFunctor` above) may be viewed as a polymorphic algebra, because
-- for each object `v` it generates an `F[v]`-algebra on an any given carrier
-- object.  When `v` is the initial object (`Void`), it specializes to
-- generating `F`-algebras.
public export
FreeAlgebra : (Type -> Type) -> Type -> Type -> Type
FreeAlgebra f v a = Algebra (TermFunctor f v) a

public export
ProductCatFreeAlgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatFreeAlgebra f v a =
  ProductCatAlgebra (ProductCatTermFunctor f v) a

public export
TermCoalgebra : (Type -> Type) -> Type -> Type -> Type
TermCoalgebra f v a = Coalgebra (TermFunctor f v) a

public export
ProductCatTermCoalgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatTermCoalgebra f v a =
  ProductCatCoalgebra (ProductCatTermFunctor f v) a

-- A coalgebra on a functor representing a type of labeled trees (as generated
-- by `TreeFunctor` above) may be viewed as a polymorphic coalgebra, because
-- for each object `v` it generates an `F[v]`-coalgebra on an any given carrier
-- object.  When `v` is the terminal object (`Unit`), it specializes to
-- generating `F`-coalgebras.
public export
CofreeCoalgebra : (Type -> Type) -> Type -> Type -> Type
CofreeCoalgebra f v a = Coalgebra (TreeFunctor f v) a

public export
TreeAlgebra : (Type -> Type) -> Type -> Type -> Type
TreeAlgebra f v a = Algebra (TreeFunctor f v) a

public export
ProductCatTreeAlgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatTreeAlgebra f v a =
  ProductCatAlgebra (ProductCatTreeFunctor f v) a

--------------------------------------------------
---- Initial algebras and terminal coalgebras ----
--------------------------------------------------

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
  InFree : {f : Type -> Type} -> {0 a : Type} ->
    FreeAlgebra f a (FreeMonad f a)

-- The product-category version of `FreeMonad`.
public export
data ProductCatFreeMonad : {idx : Type} ->
    ProductCatObjectEndoMap idx -> ProductCatObjectEndoMap idx where
  InFreeProduct : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} -> {0 a : ProductCatObject idx} ->
    ProductCatFreeAlgebra f a (ProductCatFreeMonad f a)

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
data ProductCatCofreeComonad : {idx : Type} ->
    ProductCatObjectEndoMap idx -> ProductCatObjectEndoMap idx where
  InCofreeProduct : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} -> {l : ProductCatObject idx} ->
    {i : idx} ->
    Inf (ProductCatTreeFunctor f l (ProductCatCofreeComonad f l) i) ->
    ProductCatCofreeComonad f l i

public export
inFreeVar : {f : Type -> Type} -> Coalgebra (FreeMonad f) a
inFreeVar = InFree . TermVar

public export
inFreeVarProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {0 a : ProductCatObject idx} ->
  ProductCatCoalgebra (ProductCatFreeMonad f) a
inFreeVarProduct i = InFreeProduct i . ProductCatTermVar

public export
inFreeComposite : {f : Type -> Type} -> Algebra f (FreeMonad f a)
inFreeComposite = InFree . TermComposite

public export
inFreeCompositeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {a : ProductCatObject idx} ->
  ProductCatAlgebra f (ProductCatFreeMonad f a)
inFreeCompositeProduct i = InFreeProduct i . ProductCatTermComposite

public export
outFree : TermCoalgebra f a (FreeMonad f a)
outFree (InFree x) = x

public export
outFreeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {a : ProductCatObject idx} ->
  ProductCatTermCoalgebra f a (ProductCatFreeMonad f a)
outFreeProduct i (InFreeProduct i x) = x

public export
inCofreeTree : {a : Type} -> {f : Type -> Type} ->
  a -> Algebra f (CofreeComonad f a)
inCofreeTree x fx = InCofree $ TreeNode x fx

public export
outCofree : {f : Type -> Type} -> {a : Type} ->
  CofreeCoalgebra f a (CofreeComonad f a)
outCofree (InCofree x) = x

public export
outCofreeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {l : ProductCatObject idx} ->
  {i : idx} ->
  ProductCatCofreeComonad f l i ->
  ProductCatTreeFunctor f l (ProductCatCofreeComonad f l) i
outCofreeProduct (InCofreeProduct x) = x

-- Special case of `FreeMonad` where `v` is `Void`.
-- This is the fixpoint of an endofunctor (if it exists).
public export
Mu : (Type -> Type) -> Type
Mu f = FreeMonad f Void

public export
MuProduct : {idx : Type} -> ProductCatObjectEndoMap idx -> ProductCatObject idx
MuProduct f = ProductCatFreeMonad f (const Void)

-- Special case of `CofreeComonad` where `v` is `Unit`.
-- This is the cofixpoint of an endofunctor (if it exists).
public export
Nu : (Type -> Type) -> Type
Nu f = CofreeComonad f ()

public export
NuProduct : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx
NuProduct f = ProductCatCofreeComonad f (const ())

-- Not all endofunctors have initial algebras.  If an endofunctor
-- _does_ have an initial algebra, then this is the signature of
-- its catamorphism (fold).
public export
Catamorphism : (Type -> Type) -> Type -> Type -> Type
Catamorphism f v a = FreeAlgebra f v a -> FreeMonad f v -> a

public export
ProductCatamorphism : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> Type
ProductCatamorphism f a =
  ProductCatAlgebra f a -> ProductCatMorphism (MuProduct f) a

-- Not all endofunctors have terminal coalgebras.  If an endofunctor
-- _does_ have a terminal coalgebra, then this is the signature of
-- its anamorphism (unfold).
Anamorphism : (Type -> Type) -> Type -> Type -> Type
Anamorphism f v l = CofreeCoalgebra f v l -> l -> CofreeComonad f v

ProductAnamorphism : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> Type
ProductAnamorphism f l = ProductCatMorphism l (NuProduct f)

---------------------------------------------------------
---------------------------------------------------------
---- Relations, equivalences, and quotients in Idris ----
---------------------------------------------------------
---------------------------------------------------------

-------------------
---- Relations ----
-------------------

RelationOn : Type -> Type
RelationOn a = a -> a -> Type

EmptyRel : (t : Type) -> RelationOn t
EmptyRel t el el' = Void

VoidRel : RelationOn Void
VoidRel v _ = void v

FullRel : (t : Type) -> RelationOn t
FullRel t el el' = ()

UnitRel : RelationOn Unit
UnitRel = FullRel ()

ProductRelation : RelationOn a -> RelationOn b -> RelationOn (a, b)
ProductRelation rel rel' (el1, el1') (el2, el2') = (rel el1 el2, rel' el1' el2')

CoproductRelation : RelationOn a -> RelationOn b -> RelationOn (Either a b)
CoproductRelation rel rel' (Left el1) (Left el2) = rel el1 el2
CoproductRelation rel rel' (Left el1) (Right el2') = Void
CoproductRelation rel rel' (Right el1') (Left el2) = Void
CoproductRelation rel rel' (Right el1') (Right el2') = rel' el1' el2'

EqualOverRelation : {a, b : Type} ->
  RelationOn a -> RelationOn b -> (f, g : a -> b) -> Type
EqualOverRelation rel rel' f g =
  (el, el' : a) -> rel el el' -> rel' (f el) (g el')

PreservesRelation : {a, b : Type} ->
  RelationOn a -> RelationOn b -> (a -> b) -> Type
PreservesRelation rel rel' f = EqualOverRelation rel rel' f f

RelMorphism : {a, b : Type} -> RelationOn a -> RelationOn b -> Type
RelMorphism rel rel' = DPair (a -> b) (PreservesRelation rel rel')

RelFunctor : Type -> Type
RelFunctor t = RelationOn t -> RelationOn t

data RelationTermF : {t: Type} ->
    (f : RelFunctor t) -> (v : RelationOn t) -> RelFunctor t where
  RelationVar :
    {t : Type} -> {f : RelFunctor t} ->
    {v, carrier : RelationOn t} -> {el, el' : t} ->
    v el el' -> RelationTermF f {t} v carrier el el'
  RelationComposite :
    {t : Type} -> {f : RelFunctor t} ->
    {v, carrier : RelationOn t} -> {el, el' : t} ->
    f carrier el el' -> RelationTermF f v carrier el el'

RelationClosureF : {t: Type} -> RelFunctor t -> RelationOn t -> RelationOn t
RelationClosureF functor rel = RelationTermF functor rel rel

data FreeMRelation :
    {t : Type} -> RelFunctor t -> RelFunctor t where
  InFreeRelation :
    {t : Type} -> {f : RelFunctor t} -> {rel : RelationOn t} -> {el, el' : t} ->
    RelationTermF f rel (FreeMRelation f rel) el el' ->
    FreeMRelation f rel el el'

RelationMu : {t: Type} -> RelFunctor t -> RelationOn t
RelationMu {t} f = FreeMRelation f $ EmptyRel t

data RelationTreeF : {t: Type} ->
    (f : RelFunctor t) -> (v : RelationOn t) -> RelFunctor t where
  RelationNode :
    {t : Type} -> {f : RelFunctor t} ->
    {v, carrier : RelationOn t} -> {el, el' : t} ->
    v el el' -> f carrier el el' -> RelationTreeF f v carrier el el'

data CofreeCMRelation :
    {t : Type} -> RelFunctor t -> RelFunctor t where
  InCofreeRelation :
    {t : Type} -> {f : RelFunctor t} -> {rel : RelationOn t} -> {el, el' : t} ->
    Inf (RelationTreeF f rel (CofreeCMRelation f rel) el el') ->
    CofreeCMRelation f rel el el'

RelationNu : {t: Type} -> RelFunctor t -> RelationOn t
RelationNu {t} f = CofreeCMRelation f $ FullRel t

----------------------
---- Equivalences ----
----------------------

data EquivGenF : {t : Type} -> (carrier : RelationOn t) -> RelationOn t where
  EquivRefl : {t : Type} -> {carrier : RelationOn t} ->
    {el, el' : t} -> el = el' -> EquivGenF carrier el el
  EquivSym : {t : Type} -> {carrier : RelationOn t} -> {el, el' : t} ->
    carrier el el' -> EquivGenF carrier el' el
  EquivTrans : {t : Type} -> {carrier : RelationOn t} ->
    {el, el', el'' : t} ->
    carrier el el' -> carrier el' el'' -> EquivGenF carrier el el''

EquivClosureF : {t: Type} -> RelationOn t -> RelationOn t
EquivClosureF = RelationClosureF EquivGenF

FreeMEquiv : {t : Type} -> RelationOn t -> RelationOn t
FreeMEquiv = FreeMRelation EquivGenF

CofreeCMEquiv : {t : Type} -> RelationOn t -> RelationOn t
CofreeCMEquiv = CofreeCMRelation EquivGenF

EqualizerRelationGenF :
  (f, g : a -> b) -> RelationOn a -> RelationOn b -> RelationOn a
EqualizerRelationGenF f g rel rel' el el' =
  (rel el el', rel' (f el) (g el'))

FreeEqualizerRelation : {a, b : _} ->
  (f, g : a -> b) -> RelationOn a -> RelationOn b -> RelationOn a
FreeEqualizerRelation f g rel rel' =
  FreeMEquiv (EqualizerRelationGenF f g rel rel')

MappedFromRelated : {a, b: _} ->
  (f, g : a -> b) -> RelationOn a -> RelationOn b
MappedFromRelated {a} f g rel el el' =
  (ela : a ** ela' : a ** (rel ela ela, f ela = el, g ela' = el'))

CoequalizerRelationGenF : {a, b : _} ->
  (f, g : a -> b) -> RelationOn a -> RelationOn b -> RelationOn b
CoequalizerRelationGenF {a} {b} f g rel rel' el el' =
  Either (rel' el el') (MappedFromRelated f g rel el el')

FreeCoequalizerRelation : {a, b : _} ->
  (f, g : a -> b) -> RelationOn a -> RelationOn b -> RelationOn b
FreeCoequalizerRelation f g rel rel' =
  FreeMEquiv (CoequalizerRelationGenF f g rel rel')

ExtEq : {a, b : Type} -> (a -> b) -> (a -> b) -> Type
ExtEq {a} f g = (el : a) -> f el = g el

EqFunctionExt : {a, b : Type} -> (f, g: a -> b) -> f = g -> ExtEq f g
EqFunctionExt f f Refl _ = Refl

------------------------
---- Quotient types ----
------------------------

QuotientType : Type
QuotientType = DPair Type RelationOn

QuotientTot : QuotientType -> Type
QuotientTot (t ** _) = t

QuotientRelType : QuotientType -> Type
QuotientRelType t = RelationOn (QuotientTot t)

QuotientRel : (t : QuotientType) -> QuotientRelType t
QuotientRel (_ ** r) = r

QuotientMorphism : QuotientType -> QuotientType -> Type
QuotientMorphism (t ** r) (t' ** r') = (m : t -> t' ** PreservesRelation r r' m)

QuotientVoid : QuotientType
QuotientVoid = (Void ** VoidRel)

QuotientUnit : QuotientType
QuotientUnit = (Unit ** UnitRel)

QuotientProduct : QuotientType -> QuotientType -> QuotientType
QuotientProduct (t ** r) (t' ** r') =
  ((t, t') ** (ProductRelation r r'))

QuotientCoproduct : QuotientType -> QuotientType -> QuotientType
QuotientCoproduct (t ** r) (t' ** r') =
  (Either t t' ** (CoproductRelation r r'))

QuotientEqualizer :
  (dom, cod : QuotientType) -> (f, g : QuotientTot dom -> QuotientTot cod) ->
  QuotientType
QuotientEqualizer (domtot ** domrel) (_ ** codrel) f g =
  (domtot ** FreeEqualizerRelation f g domrel codrel)

QuotientCoequalizer :
  (dom, cod : QuotientType) -> (f, g : QuotientTot dom -> QuotientTot cod) ->
  QuotientType
QuotientCoequalizer (_ ** domrel) (codtot ** codrel) f g =
  (codtot ** FreeCoequalizerRelation f g domrel codrel)

QFunctor : Type
QFunctor = QuotientType -> QuotientType

QFunctorType : Type
QFunctorType = QuotientType -> Type

QFunctorRel : QFunctorType -> Type
QFunctorRel f = (t : QuotientType) -> RelationOn (f t)

QFunctorFromComponents : (f : QFunctorType) -> QFunctorRel f -> QFunctor
QFunctorFromComponents f fm qt = (f qt ** fm qt)

QuotientConstVoid : QFunctor
QuotientConstVoid _ = QuotientVoid

QuotientConstUnit : QFunctor
QuotientConstUnit _ = QuotientUnit

QuotientProductF : QFunctor -> QFunctor -> QFunctor
QuotientProductF f g qt = QuotientProduct (f qt) (g qt)

QuotientCoproductF : QFunctor -> QFunctor -> QFunctor
QuotientCoproductF f g qt = QuotientCoproduct (f qt) (g qt)

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
---- Slices, pullbacks, pushouts, base changes, bundles, and refinements ----
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

-----------------------
---- Slice objects ----
-----------------------

-- The category-theoretic notion of an object of a slice category.
SliceObj : Type -> Type
SliceObj c = (a : Type ** a -> c)

SliceObjDomain : {c : Type} -> SliceObj c -> Type
SliceObjDomain (a ** _) = a

SliceObjMap : {c : Type} -> (x : SliceObj c) -> (SliceObjDomain x -> c)
SliceObjMap (_ ** mx) = mx

-- We will parameterize the notion of morphisms over an equivalence relation.

TermRel : Type
TermRel = {a, b : Type} -> (el : a) -> (el' : b) -> Type

---------------------------------------------
---- Quotients over a global equivalence ----
---------------------------------------------

data QuotientClosure :
    (rel : TermRel) -> {a, b : Type} -> a -> b -> Type where
  QuotientRefl : {rel : TermRel} -> {a : Type} -> {el, el' : a} ->
    el = el' -> QuotientClosure rel {a} {b=a} el el'
  QuotientedTerm : {rel : TermRel} -> {a, b : Type} -> {el : a} -> {el' : b} ->
    rel el el' -> QuotientClosure rel el el'
  QuotientExt : {rel : TermRel} -> {a, b : Type} -> {f, g: a -> b} ->
    ((el : a) -> QuotientClosure rel (f el) (g el)) ->
    QuotientClosure rel f g
  QuotientApp : {rel : TermRel} -> {a, a', b, b' : Type} ->
    {f : a -> b} -> {f' : a' -> b'} ->
    {el : a} -> {el' : a'} ->
    QuotientClosure rel f f' ->
    QuotientClosure rel el el' ->
    QuotientClosure rel (f el) (f' el')
  QuotientSym : {rel : TermRel} -> {a, b : Type} -> {el : a} -> {el' : b} ->
    QuotientClosure rel el el' -> QuotientClosure rel el' el
  QuotientTrans : {rel : TermRel} -> {a, b, c : Type} ->
    {el : a} -> {el' : b} -> {el'' : c} ->
    QuotientClosure rel el el' -> QuotientClosure rel el' el'' ->
    QuotientClosure rel el el''
  QuotientErase : {rel : TermRel} -> {a, a', b, b' : Type} ->
    {ela : a} -> {ela' : a'} -> {elb : b} -> {elb' : b'} ->
    (qr : QuotientClosure rel ela elb) ->
    (qr' : QuotientClosure rel ela' elb') ->
    QuotientClosure rel qr qr'

QuotientExtEq : {rel : TermRel} -> {a, b : Type} -> {f, g : a -> b} ->
  ExtEq f g -> QuotientClosure rel f g
QuotientExtEq eqfg = QuotientExt $ \el => QuotientRefl $ eqfg el

QuotientCompose : {rel : TermRel} -> {a, b, c : Type} ->
  {f, f' : a -> b} -> {g, g': b -> c} ->
  QuotientClosure rel g g' ->
  QuotientClosure rel f f' ->
  QuotientClosure rel (g . f) (g' . f')
QuotientCompose {rel} geq feq =
  QuotientExt $ \el => QuotientApp geq $ QuotientApp feq $ QuotientRefl Refl

---------------------------------------------------
---- Slice morphisms over a global equivalence ----
---------------------------------------------------

-- The category-theoretic notion of a morphism of a slice category.
SliceMorphism : {c : Type} -> SliceObj c -> SliceObj c -> TermRel -> Type
SliceMorphism x y rel =
  (w : SliceObjDomain x -> SliceObjDomain y **
   QuotientClosure rel (SliceObjMap y . w) (SliceObjMap x))

SliceMorphismMap : {c : Type} -> {x, y : SliceObj c} -> {rel : TermRel} ->
  SliceMorphism x y rel -> SliceObjDomain x -> SliceObjDomain y
SliceMorphismMap (w ** _) = w

SliceMorphismEq : {c : Type} -> {x, y : SliceObj c} -> {rel : TermRel} ->
  (f : SliceMorphism x y rel) ->
  QuotientClosure rel
    (SliceObjMap y . SliceMorphismMap {x} {y} {rel} f) (SliceObjMap x)
SliceMorphismEq (_ ** eq) = eq

SliceId : {c : Type} -> {rel : TermRel} ->
  (w : SliceObj c) -> SliceMorphism w w rel
SliceId (a ** x) = (id ** QuotientRefl Refl)

SliceCompose : {c : Type} -> {u, v, w : SliceObj c} -> {rel : TermRel} ->
  SliceMorphism v w rel -> SliceMorphism u v rel -> SliceMorphism u w rel
SliceCompose {rel} g f =
  (SliceMorphismMap g . SliceMorphismMap f **
   QuotientTrans
    (QuotientCompose
      (SliceMorphismEq g)
      (QuotientRefl Refl))
    (SliceMorphismEq f))

---------------------------------------------------------------
---- Equalizers and coequalizers over a global equivalence ----
---------------------------------------------------------------

Equalizer : TermRel -> {a, b : Type} -> (f, g : a -> b) -> Type
Equalizer rel {a} {b} f g = (el : a ** QuotientClosure rel (f el) (g el))

equalizerElem : (rel : TermRel) -> {a, b : Type} -> {f, g : a -> b} ->
  Equalizer rel f g -> a
equalizerElem rel eq = fst eq

equalizerRel : (rel : TermRel) -> {a, b : Type} -> {f, g : a -> b} ->
  (eq : Equalizer rel f g) ->
  QuotientClosure rel (f (equalizerElem rel eq)) (g (equalizerElem rel eq))
equalizerRel rel eq = snd eq

data Coequalizer : TermRel -> {a, b: Type} -> (f, g : a -> b) -> TermRel where
  AlreadyEqual : (rel : TermRel) -> {a, b : Type} -> {f, g : a -> b} ->
    {el : a} -> {el' : b} -> rel {a} {b} el el' -> Coequalizer rel f g el el'
  Coequalized : (rel : TermRel) -> {a, b : Type} -> {f, g : a -> b} ->
    {el : a} -> {el' : b} ->
    QuotientClosure rel (f el) (g el) -> Coequalizer rel f g el el'

--------------------------------------------------------------
---- Pullbacks and base changes over a global equivalence ----
--------------------------------------------------------------

Pullback : TermRel -> {a, b, c : Type} -> (a -> c) -> (b -> c) -> Type
Pullback rel {a} {b} f g =
  (el : (a, b) ** QuotientClosure rel (f (fst el)) (g (snd el)))

pullbackProd : {rel : TermRel} -> {a, b, c : Type} ->
  {f : a -> c} -> {g : b -> c} -> (Pullback rel f g -> (a, b))
pullbackProd pb = fst pb

pullbackProj1 : {rel : TermRel} -> {a, b, c : Type} ->
  {f : a -> c} -> {g : b -> c} -> (Pullback rel f g -> a)
pullbackProj1 {f} {g} pb = fst $ pullbackProd {f} {g} pb

pullbackProj2 : {rel : TermRel} -> {a, b, c : Type} ->
  {f : a -> c} -> {g : b -> c} -> (Pullback rel f g -> b)
pullbackProj2 {f} {g} pb = snd $ pullbackProd {f} {g} pb

pullbackRel : {rel : TermRel} -> {a, b, c : Type} ->
  {f : a -> c} -> {g : b -> c} ->
  (pb : Pullback rel f g) ->
  QuotientClosure rel
    (f (pullbackProj1 {f} {g} pb)) (g (pullbackProj2 {f} {g} pb))
pullbackRel = DPair.snd

BaseChangeObj : TermRel ->
  {x, y : Type} -> (f : x -> y) -> SliceObj y -> SliceObj x
BaseChangeObj rel f u =
  (Pullback rel (SliceObjMap u) f ** pullbackProj2 {f=(SliceObjMap u)} {g=f})

BaseChangeMorphism : (rel : TermRel) ->
  {x, y : Type} -> (f : x -> y) -> {u, v : SliceObj y} ->
  SliceMorphism u v rel ->
  SliceMorphism (BaseChangeObj rel f u) (BaseChangeObj rel f v) rel
BaseChangeMorphism rel f {u=(uo ** um)} {v=(vo ** vm)} (muv ** eqmuv) =
  (\elpb =>
    ((muv $ pullbackProj1 {f=um} {g=f} elpb, pullbackProj2 {f=um} {g=f} elpb) **
      QuotientTrans
        (QuotientApp eqmuv $ QuotientRefl Refl)
        (pullbackRel {f=um} {g=f} elpb)) **
   QuotientRefl Refl)

-----------------
---- Bundles ----
-----------------

Bundle : Type
Bundle = (base : Type ** SliceObj base)

BundleBase : Bundle -> Type
BundleBase (base ** (_ ** _)) = base

BundleTotal : Bundle -> Type
BundleTotal (_ ** (tot ** _)) = tot

BundleProj :
  (bundle : Bundle) -> (BundleTotal bundle) -> (BundleBase bundle)
BundleProj (_ ** (_ ** proj)) = proj

BundleObject : (bundle : Bundle) -> SliceObj (BundleBase bundle)
BundleObject (base ** (tot ** proj)) = (tot ** proj)

BundleFiber : (bundle : Bundle) -> (baseElem : BundleBase bundle) -> Type
BundleFiber bundle baseElem =
  (totalElem : BundleTotal bundle ** (BundleProj bundle totalElem = baseElem))

----------------------------------------------------
---- Bundle morphisms over a global equivalence ----
----------------------------------------------------

BundleMorphism : (rel : TermRel) ->
  (b : Bundle) -> {b' : Type} -> (b' -> BundleBase b) -> Bundle
BundleMorphism rel (base ** (tot ** proj)) {b'} f =
  (b' ** BaseChangeObj rel f (tot ** proj))

---------------------
---- Refinements ----
---------------------

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

IsRefined : (r : Refinement) -> RefinementTotal r -> Type
IsRefined r = IsJust . RefinementProj r

IsUnrefined : (r : Refinement) -> RefinementTotal r -> Type
IsUnrefined r = Not . IsJust . RefinementProj r

RefinedType : Refinement -> Type
RefinedType r = DPair (RefinementTotal r) (IsRefined r)

RefinedToBase : {r : Refinement} -> RefinedType r -> RefinementBase r
RefinedToBase {r=(base ** (tot ** proj))} (t ** just) = fromJust $ proj t

JustBundle : Refinement -> Bundle
JustBundle r = (RefinementBase r ** (RefinedType r ** RefinedToBase))

UnrefinedType : Refinement -> Type
UnrefinedType r = DPair (RefinementTotal r) (IsUnrefined r)

NothingBundle : Refinement -> Bundle
NothingBundle r = (() ** (UnrefinedType r ** const ()))

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

-----------------------------------------------
-----------------------------------------------
---- Interpretation of categories in Idris ----
-----------------------------------------------
-----------------------------------------------

record EquivBundle (t : Type) where
  constructor MkEquivBundle
  EquivType : Type
  EquivLeft : EquivType -> t
  EquivRight : EquivType -> t

record CategoryData where
  constructor CategoryComponents
  CatObject : Type
  ObjEquiv : EquivBundle CatObject
  CatMorphism : Type
  MorphEquiv : EquivBundle CatMorphism
  MorphDomain : CatMorphism -> CatObject
  MorphCodomain : CatMorphism -> CatObject
  CatEndofunctor : Type
  FunctorEquiv : EquivBundle CatEndofunctor
  CatNatTrans : Type
  CatNatTransEquiv : EquivBundle CatNatTrans
  CatNatTransDom : CatNatTrans -> CatEndofunctor
  CatNatTransCod : CatNatTrans -> CatEndofunctor

record CategoryInterpretation (cat : CategoryData) where
  constructor CategoryInterpretations
  ObjInterp : CatObject cat -> Type
  MorphInterp : (m : CatMorphism cat) ->
    ObjInterp (MorphDomain cat m) -> ObjInterp (MorphCodomain cat m)
  FunctorInterpObj : CatEndofunctor cat -> CatObject cat -> CatObject cat
  FunctorInterpMorph : CatEndofunctor cat -> CatMorphism cat -> CatMorphism cat
  NatTransInterp : (nt : CatNatTrans cat) -> (a : CatObject cat) ->
    ObjInterp (FunctorInterpObj (CatNatTransDom cat nt) a) ->
    ObjInterp (FunctorInterpObj (CatNatTransCod cat nt) a)

------------------------------------------
------------------------------------------
---- Polynomial endofunctors in Idris ----
------------------------------------------
------------------------------------------

ITSProductF : (Type -> Type) -> (Type -> Type) -> (Type -> Type)
ITSProductF f g a = Pair (f a) (g a)

ITSCoproductF : (Type -> Type) -> (Type -> Type) -> (Type -> Type)
ITSCoproductF f g a = Either (f a) (g a)

public export
data IsPolynomial : (Type -> Type) -> Type where
  IdPoly : IsPolynomial Prelude.Basics.id
  ComposePoly : IsPolynomial g -> IsPolynomial f -> IsPolynomial (g . f)
  VoidPoly : IsPolynomial $ const Void
  UnitPoly : IsPolynomial $ const ()
  ProductPoly :
    IsPolynomial f -> IsPolynomial g -> IsPolynomial $ ITSProductF f g
  CoproductPoly :
    IsPolynomial f -> IsPolynomial g -> IsPolynomial $ ITSCoproductF f g
  FreePoly : IsPolynomial f -> IsPolynomial $ FreeMonad f
  CofreePoly : IsPolynomial f -> IsPolynomial $ CofreeComonad f
