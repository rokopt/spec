module Library.IdrisCategories

import Library.IdrisUtils

%default total

-----------------------------------------------
-----------------------------------------------
---- Categorial algebra on Idris's Type(0) ----
-----------------------------------------------
-----------------------------------------------

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
public export
Catamorphism : (Type -> Type) -> Type -> Type -> Type
Catamorphism f v a = TermAlgebra f v a -> FreeMonad f v -> a

-- Special case of `FreeMonad` where `v` is `Void`.
-- This is the fixpoint of an endofunctor (if it exists).
public export
Mu : (Type -> Type) -> Type
Mu f = FreeMonad f Void
