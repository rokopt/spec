module Library.IdrisUtils

import public Data.Maybe
import public Data.List
import public Data.Vect
import public Decidable.Equality
import public Control.Function

%default total

public export
DecEqPred : (a: Type) -> Type
DecEqPred a = (x, x': a) -> Dec (x = x')

export
encodingDecEq : {a, b : Type} ->
  (encode : a -> b) -> (decode : b -> Maybe a) ->
  (encodingIsCorrect : (x : a) -> decode (encode x) = Just x) ->
  (bDecEq : DecEqPred b) ->
  DecEqPred a
encodingDecEq encode decode encodingIsCorrect bDecEq x x' with
  (bDecEq (encode x) (encode x'))
    encodingDecEq encode decode encodingIsCorrect bDecEq x x' | Yes eq = Yes $
      injective $
        trans
          (sym (encodingIsCorrect x))
          (trans
            (cong decode eq)
            (encodingIsCorrect x'))
    encodingDecEq encode decode encodingIsCorrect bDecEq x x' | No neq =
      No $ \xeq => neq $ cong encode xeq

public export
mapIndexStart : (Nat -> a -> b) -> Nat -> Vect l a -> Vect l b
mapIndexStart _ _ [] = []
mapIndexStart f n (x :: xs) = f n x :: mapIndexStart f (S n) xs

public export
mapIndex : (Nat -> a -> b) -> Vect n a -> Vect n b
mapIndex f = mapIndexStart f Z

public export
foldIndexAccumStart : (Nat -> a -> b -> b) -> Nat -> b -> Vect len a -> b
foldIndexAccumStart _ _ acc [] = acc
foldIndexAccumStart f n acc (x :: xs) =
  foldIndexAccumStart f (S n) (f n x acc) xs

public export
foldIndexAccum : (Nat -> a -> b -> b) -> b -> Vect len a -> b
foldIndexAccum f acc v = foldIndexAccumStart f Z acc v
