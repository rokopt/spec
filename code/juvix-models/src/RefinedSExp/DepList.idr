module RefinedSExp.DepList

import public RefinedSExp.List

%default total

public export
data DepList :
  {atom : Type} -> (depType : atom -> type) -> List atom -> Type where
    (|:|) : {atom : Type} -> {depType : atom -> Type} ->
            DepList depType []
    (:::) : {atom : Type} -> {depType : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            (da : depType a) -> (dl : DepList depType l) ->
            DepList depType (a :: l)
