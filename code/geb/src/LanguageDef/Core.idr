module LanguageDef.Core

import Library.IdrisUtils

-- “Ah Love! could thou and I with Fate conspire
-- To grasp this sorry Scheme of Things entire,
-- Would not we shatter it to bits -- and then
-- Re-mould it nearer to the Heart's Desire!”
--  - _Rubaiyat of Omar Khayyam_ (tr. Edward FitzGerald)

%default total

-------------------------------------
-------------------------------------
---- Categorial algebra in Idris ----
-------------------------------------
-------------------------------------

------------------
---- Algebras ----
------------------

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

--------------------
---- Coalgebras ----
--------------------

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

-------------
-------------
---- Geb ----
-------------
-------------

-- The functor which defines the object of the refined first-order ADT
-- category from which all other constructs of Geb can be extracted, and
-- which can be extended to generate super-languages of Geb.
data GebTypeF : Type -> Type where
  Geb : GebTypeF carrier

Functor GebTypeF where
  map _ Geb = Geb

FreeGebType : Type -> Type
FreeGebType = FreeMonad GebTypeF

gebCata : Functor f => Catamorphism GebTypeF v a
gebCata alg (InFree x) = alg $ case x of
  TermVar v' => TermVar v'
  TermComposite t => TermComposite $ case t of
    Geb => Geb

CofreeGebType : Type -> Type
CofreeGebType = CofreeComonad GebTypeF
