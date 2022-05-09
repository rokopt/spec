module Library.IdrisCategories

import Library.IdrisUtils

%default total

------------------------------------------------------
------------------------------------------------------
---- Idris sigma, product, and functor categories ----
------------------------------------------------------
------------------------------------------------------

public export
SigmaObject : {a : Type} -> (a -> Type) -> Type
SigmaObject {a} b = DPair a b

public export
SigmaMorphism : {a, a' : Type} ->
  (a -> Type) -> (a' -> Type) -> (a -> a') -> Type
SigmaMorphism {a} b b' f = (x : a) -> b x -> b' (f x)

public export
sigmaCompose : {a, a', a'' : Type} ->
  {b : a -> Type} -> {b' : a' -> Type} -> {b'' : a'' -> Type} ->
  {f' : a' -> a''} -> {f : a -> a'} ->
  SigmaMorphism b' b'' f' ->
  SigmaMorphism b b' f ->
  SigmaMorphism b b'' (f' . f)
sigmaCompose {f} m' m x y = m' (f x) $ m x y

-- The objects of a product category, where the product is represented by
-- a function from an index type (as opposed to by a pair or a list -- the
-- function type allows the assignment of names from a user-selected domain,
-- and the definition of the category of endofunctors on Idris's `Type`
-- by specializing the index to `Type`).
public export
ProductCatObject : Type -> Type
ProductCatObject idx = idx -> Type

public export
FunctorCatObject : Type
FunctorCatObject = ProductCatObject Type

public export
ProductCatMorphism : {idx : Type} ->
  ProductCatObject idx -> ProductCatObject idx -> Type
ProductCatMorphism {idx} dom cod = (i : idx) -> dom i -> cod i

public export
FunctorCatMorphism : FunctorCatObject -> FunctorCatObject -> Type
FunctorCatMorphism = ProductCatMorphism {idx=Type}

public export
ProductCatObjectMap : Type -> Type -> Type
ProductCatObjectMap idx idx' = ProductCatObject idx -> ProductCatObject idx'

public export
FunctorCatObjectMap : Type
FunctorCatObjectMap = ProductCatObjectMap Type Type

public export
ProductCatObjectEndoMap : Type -> Type
ProductCatObjectEndoMap idx = ProductCatObjectMap idx idx

public export
FunctorCatObjectEndoMap : Type
FunctorCatObjectEndoMap = ProductCatObjectEndoMap Type

public export
ProductCatMorphismMap :
  {idx, idx' : Type} -> ProductCatObjectMap idx idx' -> Type
ProductCatMorphismMap {idx} {idx'} objmap =
  (dom, cod : ProductCatObject idx) ->
  (m : ProductCatMorphism dom cod) ->
  ProductCatMorphism (objmap dom) (objmap cod)

public export
FunctorCatMorphismMap : FunctorCatObjectMap -> Type
FunctorCatMorphismMap = ProductCatMorphismMap {idx=Type} {idx'=Type}

public export
ProductCatMorphismEndoMap : {idx : Type} -> ProductCatObjectEndoMap idx -> Type
ProductCatMorphismEndoMap = ProductCatMorphismMap

public export
FunctorCatMorphismEndoMap : FunctorCatObjectEndoMap -> Type
FunctorCatMorphismEndoMap = ProductCatMorphismEndoMap {idx=Type}

public export
ProductCatFunctor : Type -> Type -> Type
ProductCatFunctor idx idx' =
  DPair (ProductCatObjectMap idx idx') ProductCatMorphismMap

public export
FunctorCatFunctor : Type
FunctorCatFunctor = ProductCatFunctor Type Type

public export
ProductCatEndofunctor : Type -> Type
ProductCatEndofunctor idx = ProductCatFunctor idx idx

public export
FunctorCatEndofunctor : Type
FunctorCatEndofunctor = ProductCatEndofunctor Type

------------------------------------------------
------------------------------------------------
---- Categorial algebra on Idris categories ----
------------------------------------------------
------------------------------------------------

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

-- The version of `Coalgebra` for an Idris product category.
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
TermAlgebra : (Type -> Type) -> Type -> Type -> Type
TermAlgebra f v a = Algebra (TermFunctor f v) a

public export
ProductCatTermAlgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatTermAlgebra f v a =
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
TreeCoalgebra : (Type -> Type) -> Type -> Type -> Type
TreeCoalgebra f v a = Coalgebra (TreeFunctor f v) a

public export
ProductCatTreeCoalgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatTreeCoalgebra f v a =
  ProductCatCoalgebra (ProductCatTreeFunctor f v) a

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
    TermAlgebra f a (FreeMonad f a)

public export
FreeAlgebra : (Type -> Type) -> Type -> Type
FreeAlgebra f a = Algebra f (FreeMonad f a)

public export
InitialAlgebra : (Type -> Type) -> Type
InitialAlgebra f = FreeAlgebra f Void

-- The product-category version of `FreeMonad`.
public export
data ProductCatFreeMonad : {idx : Type} ->
    ProductCatObjectEndoMap idx -> ProductCatObjectEndoMap idx where
  InFreeProduct : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} -> {0 a : ProductCatObject idx} ->
    ProductCatTermAlgebra f a (ProductCatFreeMonad f a)

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
CofreeCoalgebra : (Type -> Type) -> Type -> Type
CofreeCoalgebra f a = Coalgebra f (CofreeComonad f a)

public export
TerminalCoalgebra : (Type -> Type) -> Type
TerminalCoalgebra f = CofreeCoalgebra f Unit

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
inCofreeTreeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} ->
  {l : ProductCatObject idx} ->
  {i : idx} ->
  l i ->
  f (ProductCatCofreeComonad f l) i ->
  ProductCatCofreeComonad f l i
inCofreeTreeProduct x fx = InCofreeProduct $ ProductCatTreeNode x fx

public export
outCofree : {f : Type -> Type} -> {a : Type} ->
  TreeCoalgebra f a (CofreeComonad f a)
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
-- its parameterized catamorphism (fold).
public export
FreeCatamorphism : (Type -> Type) -> Type
FreeCatamorphism f =
  (v, a : Type) -> TermAlgebra f v a -> FreeMonad f v -> a

public export
ProductFreeCatamorphism : {idx : Type} -> ProductCatObjectEndoMap idx -> Type
ProductFreeCatamorphism f =
  (v, a : ProductCatObject idx) ->
  ProductCatTermAlgebra f v a ->
  ProductCatMorphism (ProductCatFreeMonad f v) a

-- Not all endofunctors have terminal coalgebras.  If an endofunctor
-- _does_ have a terminal coalgebra, then this is the signature of
-- its parameterized anamorphism (unfold).
FreeAnamorphism : (Type -> Type) -> Type
FreeAnamorphism f =
  (v, l : Type) -> TreeCoalgebra f v l -> l -> CofreeComonad f v

ProductFreeAnamorphism : {idx : Type} ->
  ProductCatObjectEndoMap idx ->
  Type
ProductFreeAnamorphism f =
  (v, l : ProductCatObject idx) ->
  ProductCatTreeCoalgebra f v l ->
  ProductCatMorphism (ProductCatCofreeComonad f v) l

-- Non-parameterized catamorphism (fold).
public export
Catamorphism : (Type -> Type) -> Type
Catamorphism f = (a : Type) -> Algebra f a -> Mu f -> a

public export
ProductCatamorphism : {idx : Type} -> ProductCatObjectEndoMap idx -> Type
ProductCatamorphism {idx} f =
  (a : ProductCatObject idx) ->
  ProductCatAlgebra f a ->
  ProductCatMorphism (MuProduct f) a

-- Non-parameterized anamorphism (unfold).
public export
Anamorphism : (Type -> Type) -> Type
Anamorphism f = (a : Type) -> Coalgebra f a -> a -> Nu f

public export
ProductAnamorphism : {idx : Type} -> ProductCatObjectEndoMap idx -> Type
ProductAnamorphism {idx} f =
  (a : ProductCatObject idx) ->
  ProductCatCoalgebra f a ->
  ProductCatMorphism a (NuProduct f)

--------------------
--------------------
---- Bifunctors ----
--------------------
--------------------

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

------------------------------------------
------------------------------------------
---- Polynomial endofunctors in Idris ----
------------------------------------------
------------------------------------------

------------------------------------------------------
---- Identity/composition in category of functors ----
------------------------------------------------------

public export
IdF : Type -> Type
IdF = id

public export
Functor IdF where
  map m = m

public export
ComposeF : (Type -> Type) -> (Type -> Type) -> Type -> Type
ComposeF = (.)

public export
(Functor g, Functor f) => Functor (ComposeF g f) where
  map = map . map

-------------------
---- Constants ----
-------------------

-- Given an object `a`, `Const a` is an endofunctor which takes all objects
-- to `a`.
public export
ConstF : Type -> Type -> Type
ConstF a _ = a

public export
Functor (ConstF a) where
  map = const id

public export
TerminalMonad : Type -> Type
TerminalMonad = ConstF Unit

public export
TerminalNTUnit : {a : Type} -> a -> TerminalMonad a
TerminalNTUnit = const ()

public export
VoidComonad : Type -> Type
VoidComonad = ConstF Void

public export
InitialNTCounit : {a : Type} -> VoidComonad a -> a
InitialNTCounit v = void v

------------------
---- Products ----
------------------

-- `ProductF` is an operator on endofunctors which takes two endofunctors
-- to their product.  `ProductF` is therefore not itself an endofunctor; it
-- is a higher-order functor.  (If `Poly[C]` is the category of polynomial
-- endofunctors on some category `C` -- if all of `C`'s endofunctors are
-- polynomial, then `Poly[C]` is `[C,C]` -- then `ProductF` is an object of
-- [PolyC x PolyC, PolyC].  That is, it is a bifunctor on `Poly[C]`.)
public export
ProductF : (Type -> Type) -> (Type -> Type) -> Type -> Type
ProductF f g a = (f a, g a)

public export
(Functor f, Functor g) => Functor (ProductF f g) where
  map m (x, y) = (map m x, map m y)

public export
ProductMonad : Type -> Type
ProductMonad a = Pair a a

public export
ProductNTUnit : {a : Type} -> a -> ProductMonad a
ProductNTUnit x = (x, x)

--------------------
---- Coproducts ----
--------------------

-- `CoproductF` is also in `[PolyC x PolyC, PolyC]`, and takes two
-- endofunctors to their coproduct.
public export
CoproductF : (Type -> Type) -> (Type -> Type) -> Type -> Type
CoproductF f g a = Either (f a) (g a)

public export
(Functor f, Functor g) => Functor (CoproductF f g) where
  map m (Left x) = Left $ map m x
  map m (Right y) = Right $ map m y

public export
CoproductComonad : Type -> Type
CoproductComonad a = Either a a

public export
CoproductNTCounit : {a : Type} -> CoproductComonad a -> a
CoproductNTCounit (Left x) = x
CoproductNTCounit (Right x) = x

---------------------------------------
---- Higher-order utility functors ----
---------------------------------------

public export
PairWithF : Type -> Type -> Type
PairWithF a = ProductF (ConstF a) IdF

public export
ChoiceBetweenF : Type -> Type -> Type
ChoiceBetweenF a = CoproductF (ConstF a) IdF

public export
MaybeF : Type -> Type
MaybeF = ChoiceBetweenF ()

public export
Functor MaybeF where
  map m (Left ()) = Left ()
  map m (Right x) = Right $ m x

public export
ProductFL : List (Type -> Type) -> Type -> Type
ProductFL = monoidFromList IdF ProductF

public export
CoproductFL : List (Type -> Type) -> Type -> Type
CoproductFL = monoidFromList IdF CoproductF

-------------------------
---- Natural numbers ----
-------------------------

public export
NatF : Type -> Type
NatF = MaybeF

----------------
---- Tuples ----
----------------

public export
TupleF : (natCarrier : Type) -> NatF natCarrier ->
  (carrier : natCarrier -> Type) -> (atom : Type) -> Type
TupleF natCarrier (Left ()) carrier = TerminalMonad
TupleF natCarrier (Right n) carrier = flip Pair (carrier n)

public export
Tuple : Nat -> Type -> Type
Tuple Z atom = ()
Tuple (S n) atom = PairWithF atom (Tuple n atom)

public export
toTuple : {atom : Type} -> (l : List atom) -> Tuple (length l) atom
toTuple [] = ()
toTuple (x :: xs) = (x, toTuple xs)

public export
mapTuple : {n : Nat} -> (f : a -> b) -> Tuple n a -> Tuple n b
mapTuple {n=Z} f () = ()
mapTuple {n=(S n)} f (x, t) = (f x, mapTuple f {n} t)

public export
(n : Nat) => Functor (Tuple n) where
  map = mapTuple

public export
tupleProj : {n : Nat} -> {atom : Type} -> (i : Nat) -> {auto ok : LT i n} ->
  Tuple n atom -> atom
tupleProj {n=Z} Z {ok} () = void $ succNotLTEzero ok
tupleProj {n=(S n)} Z {ok} (a, t) = a
tupleProj {n=(S n)} (S i) {ok} (a, t) = tupleProj i t {ok=(fromLteSucc ok)}

-----------------
---- Choices ----
-----------------

public export
ChoiceF : (natCarrier : Type) -> NatF natCarrier ->
  (carrier : natCarrier -> Type) -> (atom : Type) -> Type
ChoiceF natCarrier (Left ()) carrier = VoidComonad
ChoiceF natCarrier (Right n) carrier = flip Either (carrier n)

public export
Choice : Nat -> Type -> Type
Choice Z atom = Void
Choice (S n) atom = ChoiceBetweenF atom (Choice n atom)

public export
mapChoice : {n : Nat} -> (f : a -> b) -> Choice n a -> Choice n b
mapChoice {n=Z} f v = void v
mapChoice {n=(S n)} f (Left x) = Left (f x)
mapChoice {n=(S n)} f (Right t) = Right (mapChoice f {n} t)

public export
(n : Nat) => Functor (Choice n) where
  map = mapChoice

public export
choiceInj : {n : Nat} -> {atom : Type} -> (i : Nat) -> {auto ok : LT i n} ->
  atom -> Choice n atom
choiceInj {n=Z} Z {ok} a = void $ succNotLTEzero ok
choiceInj {n=(S n)} Z {ok} a = Left a
choiceInj {n=(S n)} (S i) {ok} t = Right $ choiceInj i t {ok=(fromLteSucc ok)}

---------------
---- Lists ----
---------------

public export
ListF : Type -> Type -> Type
ListF atom = MaybeF . (PairWithF atom)

public export
Bifunctor ListF where
  bimap f g (Left ()) = (Left ())
  bimap f g (Right p) = Right $ bimap f g p

--------------------------------------------------------------------
---- The category of zeroth-order Idris polynomial endofunctors ----
--------------------------------------------------------------------

public export
PolyFunctorF0 : Type -> Type
PolyFunctorF0 =
  CoproductFL [
    TerminalMonad, -- Identity
    ProductMonad, -- Composition
    TerminalMonad, -- Const-valued unit
    TerminalMonad, -- Const-valued void
    ProductMonad, -- Product
    ProductMonad -- Coproduct
  ]

public export
PolyFunctor0Alg : Type -> Type
PolyFunctor0Alg = Algebra PolyFunctorF0

public export
FreePolyFunctor0 : Type -> Type
FreePolyFunctor0 = FreeMonad PolyFunctorF0

public export
MuPolyFunctor0 : Type
MuPolyFunctor0 = Mu PolyFunctorF0

public export
interpretPoly0Alg : PolyFunctor0Alg (Type -> Type)
interpretPoly0Alg (Left ()) = IdF
interpretPoly0Alg (Right $ Left (g, f)) = ComposeF g f
interpretPoly0Alg (Right $ Right $ Left ()) = TerminalMonad
interpretPoly0Alg (Right $ Right $ Right $ Left ()) = VoidComonad
interpretPoly0Alg (Right $ Right $ Right $ Right $ Left (f, g)) =
  ProductF f g
interpretPoly0Alg (Right $ Right $ Right $ Right $ Right (f, g)) =
  CoproductF f g

---------------------------------------------------------------
---- Zeroth-order datatypes from zeroth-order endofunctors ----
---------------------------------------------------------------

------------------------------------------------------
------------------------------------------------------
---- Predicates, relations, equivalences in Idris ----
------------------------------------------------------
------------------------------------------------------

--------------------
---- Predicates ----
--------------------

PredicateOn : Type -> Type
PredicateOn type = type -> Type

EmptyPred : (t : Type) -> PredicateOn t
EmptyPred t el = Void

VoidPred : PredicateOn Void
VoidPred v = void v

FullPred : (t : Type) -> PredicateOn t
FullPred t el = ()

UnitPred : PredicateOn Unit
UnitPred = FullPred ()

ProductPred : PredicateOn a -> PredicateOn b -> PredicateOn (a, b)
ProductPred p p' (el, el') = (p el, p' el')

CoproductPred : PredicateOn a -> PredicateOn b -> PredicateOn (Either a b)
CoproductPred p p' (Left el) = p el
CoproductPred p p' (Right el') = p' el'

SubPredicate : {a : Type} -> (sub, super : PredicateOn a) -> Type
SubPredicate {a} sub super = (el : a) -> sub el -> super el

PredEquiv : {a : Type} -> (p, p' : PredicateOn a) -> Type
PredEquiv {a} p p' = (SubPredicate p p', SubPredicate p' p)

PreservesPredicates : {a, b : Type} -> PredicateOn a -> PredicateOn b ->
  (a -> b) -> Type
PreservesPredicates p p' f = (el : a) -> p el -> p' (f el)

PredMorphism : {a, b : Type} -> PredicateOn a -> PredicateOn b -> Type
PredMorphism p p' = DPair (a -> b) (PreservesPredicates p p')

PredFunctor : Type -> Type
PredFunctor t = PredicateOn t -> PredicateOn t

data PredicateTermF : {t: Type} ->
    (f : PredFunctor t) -> (v : PredicateOn t) -> PredFunctor t where
  PredicateVar :
    {t : Type} -> {f : PredFunctor t} ->
    {v, carrier : PredicateOn t} -> {el : t} ->
    v el -> PredicateTermF f {t} v carrier el
  PredicateComposite :
    {t : Type} -> {f : PredFunctor t} ->
    {v, carrier : PredicateOn t} -> {el : t} ->
    f carrier el -> PredicateTermF f v carrier el

data FreeMPredicate :
    {t : Type} -> PredFunctor t -> PredFunctor t where
  InFreePredicate :
    {t : Type} -> {f : PredFunctor t} -> {rel : PredicateOn t} -> {el : t} ->
    PredicateTermF f rel (FreeMPredicate f rel) el ->
    FreeMPredicate f rel el

PredicateMu : {t: Type} -> PredFunctor t -> PredicateOn t
PredicateMu {t} f = FreeMPredicate f $ EmptyPred t

data PredicateTreeF : {t: Type} ->
    (f : PredFunctor t) -> (v : PredicateOn t) -> PredFunctor t where
  PredicateNode :
    {t : Type} -> {f : PredFunctor t} ->
    {v, carrier : PredicateOn t} -> {el : t} ->
    v el -> f carrier el -> PredicateTreeF f v carrier el

data CofreeCMPredicate :
    {t : Type} -> PredFunctor t -> PredFunctor t where
  InCofreePredicate :
    {t : Type} -> {f : PredFunctor t} -> {rel : PredicateOn t} -> {el : t} ->
    Inf (PredicateTreeF f rel (CofreeCMPredicate f rel) el) ->
    CofreeCMPredicate f rel el

PredicateNu : {t: Type} -> PredFunctor t -> PredicateOn t
PredicateNu {t} f = CofreeCMPredicate f $ FullPred t

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

SubRelation : {a : Type} -> (sub, super : RelationOn a) -> Type
SubRelation {a} sub super = (el1, el2 : a) -> sub el1 el2 -> super el1 el2

RelationEquiv : {a : Type} -> (r, r' : RelationOn a) -> Type
RelationEquiv r r' = (SubRelation r r', SubRelation r' r)

EqualOverRelations : {a, b : Type} ->
  RelationOn a -> RelationOn b -> (f, g : a -> b) -> Type
EqualOverRelations rel rel' f g =
  (el, el' : a) -> rel el el' -> rel' (f el) (g el')

PreservesRelations : {a, b : Type} ->
  RelationOn a -> RelationOn b -> (a -> b) -> Type
PreservesRelations rel rel' f = EqualOverRelations rel rel' f f

RelMorphism : {a, b : Type} -> RelationOn a -> RelationOn b -> Type
RelMorphism rel rel' = DPair (a -> b) (PreservesRelations rel rel')

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

-- Category theory's equalizer, parameterized over a relation on
-- the codomain (which serves as equality on the codomain, allowing
-- the representation of equalizers on types whose equality is not
-- that of the metalanguage (Idris)).
EqualizerRelationGenF : (f, g : a -> b) -> RelationOn b -> RelationOn a
EqualizerRelationGenF f g rel el el' = rel (f el) (g el')

-- Category theory's coequalizer, parameterized over a relation on
-- the domain (which serves as equality on the domain, allowing
-- the representation of coequalizers on types whose equality is not
-- that of the metalanguage (Idris)).
CoequalizerRelationGenF : {a, b: _} ->
  (f, g : a -> b) -> RelationOn a -> RelationOn b
CoequalizerRelationGenF {a} f g rel el el' =
  (elas : (a, a) **
   (rel (fst elas) (snd elas), f (fst elas) = el, g (snd elas) = el'))

----------------------
---- Equivalences ----
----------------------

data EquivGenF : {t : Type} -> RelFunctor t where
  EquivRefl : {t : Type} -> {carrier : RelationOn t} ->
    {el, el' : t} -> el = el' -> EquivGenF carrier el el
  EquivSym : {t : Type} -> {carrier : RelationOn t} -> {el, el' : t} ->
    carrier el el' -> EquivGenF carrier el' el
  EquivTrans : {t : Type} -> {carrier : RelationOn t} ->
    {el, el', el'' : t} ->
    carrier el el' -> carrier el' el'' -> EquivGenF carrier el el''

FreeMEquiv : {t : Type} -> RelFunctor t
FreeMEquiv = FreeMRelation EquivGenF

CofreeCMEquiv : {t : Type} -> RelFunctor t
CofreeCMEquiv = CofreeCMRelation EquivGenF

ExtEq : {a, b : Type} -> (a -> b) -> (a -> b) -> Type
ExtEq {a} f g = (el : a) -> f el = g el

EqFunctionExt : {a, b : Type} -> (f, g: a -> b) -> f = g -> ExtEq f g
EqFunctionExt f f Refl _ = Refl
