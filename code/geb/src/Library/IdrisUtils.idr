module Library.IdrisUtils

import public Data.Maybe
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
