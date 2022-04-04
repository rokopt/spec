module Library.IdrisCategories

import Library.IdrisUtils

%default total

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

ProductRelation : RelationOn a -> RelationOn b -> RelationOn (a, b)
ProductRelation rel rel' (el1, el1') (el2, el2') = (rel el1 el2, rel' el1' el2')

CoproductRelation : RelationOn a -> RelationOn b -> RelationOn (Either a b)
CoproductRelation rel rel' (Left el1) (Left el2) = rel el1 el2
CoproductRelation rel rel' (Left el1) (Right el2') = Void
CoproductRelation rel rel' (Right el1') (Left el2) = Void
CoproductRelation rel rel' (Right el1') (Right el2') = rel' el1' el2'

VoidRel : RelationOn Void
VoidRel v _ = void v

UnitRel : Type -> RelationOn Unit
UnitRel t () () = t

RelFunctor : Type -> Type
RelFunctor t = RelationOn t -> RelationOn t

data RelationTermF : {t: Type} ->
    (f : RelFunctor t) ->
    (v : RelationOn t) -> (carrier : RelationOn t) -> RelationOn t where
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
    {t : Type} -> RelFunctor t -> RelationOn t -> RelationOn t where
  InRelation :
    {t : Type} -> {f : RelFunctor t} -> {rel : RelationOn t} -> {el, el' : t} ->
    RelationTermF f rel (FreeMRelation f rel) el el' ->
    FreeMRelation f rel el el'

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

------------------------
---- Quotient types ----
------------------------

QuotientType : Type
QuotientType = DPair Type RelationOn

QuotientTot : QuotientType -> Type
QuotientTot (t ** _) = t

QuotientRelType : QuotientType -> Type
QuotientRelType t = RelationOn (QuotientTot t)

QuotientRelGen : (t : QuotientType) -> QuotientRelType t
QuotientRelGen (_ ** r) = r

QuotientVoid : QuotientType
QuotientVoid = (Void ** VoidRel)

QuotientUnit : QuotientType
QuotientUnit = (Unit ** UnitRel ())

QuotientProduct : QuotientType -> QuotientType -> QuotientType
QuotientProduct (t ** r) (t' ** r') =
  ((t, t') ** (ProductRelation r r'))

QuotientCoproduct : QuotientType -> QuotientType -> QuotientType
QuotientCoproduct (t ** r) (t' ** r') =
  (Either t t' ** (CoproductRelation r r'))

-----------------------------------------------
-----------------------------------------------
---- Interpretation of categories in Idris ----
-----------------------------------------------
-----------------------------------------------

-- An interpretation of the objects of some category into the Idris
-- type system ("ITS").
ITSObjectInterpretation : Type -> Type
ITSObjectInterpretation object = object -> Type

-- The type of morphisms between objects of some category.
ITSMorphismType : Type -> Type
ITSMorphismType object = object -> object -> Type

-- An interpretation of the morphism of some category into the Idris
-- type system.
ITSMorphismInterpretation : {object : Type} ->
  ITSMorphismType object -> ITSObjectInterpretation object -> Type
ITSMorphismInterpretation {object} morphism objInterp =
  (domain, codomain : object) ->
  morphism domain codomain ->
  (objInterp domain -> objInterp codomain)

ITSHasId :
  {object : Type} ->
  {morphism : ITSMorphismType object} ->
  {objInterp : ITSObjectInterpretation object} ->
  ITSMorphismInterpretation morphism objInterp -> Type
ITSHasId {object} {morphism} {objInterp} morphInterp =
  (a : object) ->
  (idm : morphism a a ** morphInterp a a idm = Prelude.Basics.id)

----------------------------
----------------------------
---- Fibration in Idris ----
----------------------------
----------------------------

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

------------------------------------------------
------------------------------------------------
---- Categorial algebra on Idris categories ----
------------------------------------------------
------------------------------------------------

-- The categorial definition of an algebra.
public export
Algebra : (Type -> Type) -> Type -> Type
Algebra f a = f a -> a

-- The version of `Algebra` for an Idris product category.
public export
ProductCatAlgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> Type
ProductCatAlgebra f a = ProductCatMorphism (f a) a

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

-- An algebra on a functor representing a type of open terms (as generated
-- by `TermFunctor` above) may be viewed as a polymorphic algebra, because
-- for each object `v` it generates an `F[v]`-algebra on an any given carrier
-- object.  When `v` is the initial object (`Void`), it specializes to
-- generating `F`-algebras.
public export
TermAlgebra : (Type -> Type) -> Type -> Type -> Type
TermAlgebra f v a = Algebra (TermFunctor f v) a

public export
ProductCatTermAlgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatTermAlgebra f v a = ProductCatAlgebra (ProductCatTermFunctor f v) a

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
    TermAlgebra f a (FreeMonad f a)

-- The product-category version of `FreeMonad`.
public export
data ProductCatFreeMonad : {idx : Type} ->
    ProductCatObjectEndoMap idx -> ProductCatObjectEndoMap idx where
  InFreeProduct : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} -> {0 a : ProductCatObject idx} ->
    ProductCatTermAlgebra f a (ProductCatFreeMonad f a)

public export
inFreeVar : {f : Type -> Type} -> a -> FreeMonad f a
inFreeVar = InFree . TermVar

public export
inFreeVarProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {0 a : ProductCatObject idx} ->
  ProductCatMorphism a (ProductCatFreeMonad f a)
inFreeVarProduct i = InFreeProduct i . ProductCatTermVar

public export
inFreeComposite : {f : Type -> Type} -> f (FreeMonad f a) -> FreeMonad f a
inFreeComposite = InFree . TermComposite

public export
inFreeCompositeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {a : ProductCatObject idx} ->
  ProductCatMorphism (f (ProductCatFreeMonad f a)) (ProductCatFreeMonad f a)
inFreeCompositeProduct i = InFreeProduct i . ProductCatTermComposite

public export
outFree : FreeMonad f a -> TermFunctor f a (FreeMonad f a)
outFree (InFree x) = x

public export
outFreeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {a : ProductCatObject idx} ->
  {i : idx} -> ProductCatFreeMonad f a i ->
  ProductCatTermFunctor f a (ProductCatFreeMonad f a) i
outFreeProduct (InFreeProduct i x) = x

-- Special case of `FreeMonad` where `v` is `Void`.
-- This is the fixpoint of an endofunctor (if it exists).
public export
Mu : (Type -> Type) -> Type
Mu f = FreeMonad f Void

public export
MuProduct : {idx : Type} -> ProductCatObjectEndoMap idx -> ProductCatObject idx
MuProduct f = ProductCatFreeMonad f (const Void)

-- Not all endofunctors have initial algebras.  If an endofunctor
-- _does_ have an initial algebra, then this is the signature of
-- its catamorphism (fold).
public export
Catamorphism : (Type -> Type) -> Type -> Type -> Type
Catamorphism f v a = TermAlgebra f v a -> FreeMonad f v -> a

public export
ProductCatamorphism : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> Type
ProductCatamorphism f a =
  ProductCatAlgebra f a -> ProductCatMorphism (MuProduct f) a

----------------------
---- F-Coalgebras ----
----------------------

public export
Coalgebra : (Type -> Type) -> Type -> Type
Coalgebra f a = a -> f a

public export
ProductCatCoalgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> Type
ProductCatCoalgebra f a = ProductCatMorphism a (f a)

-- For a given functor `F`, form the functor `Fa` defined by
-- `Fa[x] = a * F[x]`.  We call it `TreeFunctor` because it turns
-- an endofunctor which we can interpret as representing a datatype
-- into one which we can interpret as representing potentially infinite
-- tress of that datatype with labels drawn from type `v`.
public export
data TreeFunctor : (Type -> Type) -> Type -> (Type -> Type) where
  TreeNode : {f : Type -> Type} -> {0 l, a : Type} ->
    l -> f a -> TreeFunctor f l a

export
Functor f => Bifunctor (TreeFunctor f) where
  bimap f' g' (TreeNode x fx) = TreeNode (f' x) (map g' fx)

public export
data ProductCatTreeFunctor : {idx : Type} ->
    ProductCatObjectEndoMap idx ->
    ProductCatObject idx ->
    ProductCatObjectEndoMap idx where
  ProductCatTreeNode : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} -> {0 l, a : ProductCatObject idx} ->
    {i : idx} ->
    l i -> f a i -> ProductCatTreeFunctor f l a i

-- A coalgebra on a functor representing a type of labeled trees (as generated
-- by `TreeFunctor` above) may be viewed as a polymorphic coalgebra, because
-- for each object `v` it generates an `F[v]`-coalgebra on an any given carrier
-- object.  When `v` is the terminal object (`Unit`), it specializes to
-- generating `F`-coalgebras.
public export
TreeCoalgebra : (Type -> Type) -> Type -> Type -> Type
TreeCoalgebra f v a = Coalgebra (TreeFunctor f v) a

public export
ProductCatTreeCoalgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatTreeCoalgebra f v a =
  ProductCatCoalgebra (ProductCatTreeFunctor f v) a

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
inCofreeTree : {a : Type} -> {f : Type -> Type} ->
  a -> f (CofreeComonad f a) -> CofreeComonad f a
inCofreeTree x fx = InCofree $ TreeNode x fx

public export
outCofree : {f : Type -> Type} -> {a : Type} ->
  CofreeComonad f a -> TreeFunctor f a (CofreeComonad f a)
outCofree (InCofree x) = x

public export
outCofreeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {l : ProductCatObject idx} ->
  {i : idx} ->
  ProductCatCofreeComonad f l i ->
  ProductCatTreeFunctor f l (ProductCatCofreeComonad f l) i
outCofreeProduct (InCofreeProduct x) = x

-- Special case of `CofreeComonad` where `v` is `Unit`.
-- This is the cofixpoint of an endofunctor (if it exists).
public export
Nu : (Type -> Type) -> Type
Nu f = CofreeComonad f ()

public export
NuProduct : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx
NuProduct f = ProductCatCofreeComonad f (const ())

-- Not all endofunctors have terminal coalgebras.  If an endofunctor
-- _does_ have a terminal coalgebra, then this is the signature of
-- its anamorphism (unfold).
Anamorphism : (Type -> Type) -> Type -> Type -> Type
Anamorphism f v l = TreeCoalgebra f v l -> l -> CofreeComonad f v

ProductAnamorphism : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> Type
ProductAnamorphism f l = ProductCatMorphism l (NuProduct f)

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
