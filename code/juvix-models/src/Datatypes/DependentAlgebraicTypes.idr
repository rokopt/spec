module Datatypes.DependentAlgebraicTypes

import Library.FunctionsAndRelations
import Library.TypesAndFunctions
import public Datatypes.AlgebraicTypes

%default total

funExtUnit : {a : Type} -> FunctionalExtensionality () a
funExtUnit {a} = believe_me

public export
Incoming : (x, a : Type) -> Type
Incoming x a = (a -> x)

public export
SlicePi : Type -> Type
SlicePi x = DPair Type (Incoming x)

public export
SliceMorphism : {x : Type} -> SlicePi x -> SlicePi x -> Type
SliceMorphism (a ** f) (b ** g) = (h : (a -> b) ** (g . h = f))

public export
CatPi : Type -> Type
CatPi x = (() -> x) -> Type

public export
CatLambda : {x : Type} -> CatPi x -> Type
CatLambda {x} pi = (xv : () -> x) -> (() -> pi (\_ => xv ()))

public export
CatMorphism : {x : Type} -> CatPi x -> CatPi x -> Type
CatMorphism {x} pi pi' =
  (xv : () -> x) -> (() -> pi (\_ => xv ()) -> pi' (\_ => xv()))

public export
NativePi : Type -> Type
NativePi x = x -> Type

public export
NativeLambda : {x : Type} -> NativePi x -> Type
NativeLambda {x} pi = (xv : x) -> pi xv

public export
NativeMorphism : {x : Type} -> NativePi x -> NativePi x -> Type
NativeMorphism {x} pi pi' = (xv : x) -> pi xv -> pi' xv

public export
nativeToCatPi : {x : Type} -> NativePi x -> CatPi x
nativeToCatPi pi xv = pi (xv ())

public export
catToNativePi : {x : Type} -> CatPi x -> NativePi x
catToNativePi pi xv = pi (\_ => xv)

public export
nativeToCat_id : {x : Type} -> (pi : NativePi x) -> (xv : x) ->
  catToNativePi (nativeToCatPi pi) xv = pi xv
nativeToCat_id pi = \_ => Refl

public export
catToNative_id : {x : Type} -> (pi : CatPi x) -> (xv : () -> x) ->
  nativeToCatPi (catToNativePi pi) xv = pi xv
catToNative_id {x} pi =
  \_ => cong pi (funExtUnit (\u => case u of () => Refl))

public export
nativeToCatLambda : {x : Type} -> {pi : NativePi x} ->
  NativeLambda pi -> CatLambda (nativeToCatPi pi)
nativeToCatLambda lam xv _ = lam (xv ())

public export
catToNativeLambda : {x : Type} -> {pi : CatPi x} ->
  CatLambda pi -> NativeLambda (catToNativePi pi)
catToNativeLambda lam xv = lam (\_ => xv) ()

public export
nativeToCatMorphism : {x : Type} -> {dom, cod : NativePi x} ->
  NativeMorphism dom cod -> CatMorphism (nativeToCatPi dom) (nativeToCatPi cod)
nativeToCatMorphism f xv _ domxv = f (xv ()) domxv

public export
catToNativeMorphism : {x : Type} -> {dom, cod : CatPi x} ->
  CatMorphism dom cod -> NativeMorphism (catToNativePi dom) (catToNativePi cod)
catToNativeMorphism m xv domxv = m (\_ => xv) () domxv
