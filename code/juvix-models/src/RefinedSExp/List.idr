module RefinedSExp.List

import public Data.List

%default total

public export
record
ListFoldSig {atom : Type} {contextType : List atom -> Type}
  (listPredicate :
    -- The most recent predecessor is the head of `predecessors`.
    (predecessors : List atom) ->
    (context : contextType predecessors) ->
    List atom ->
    Type) where
      constructor ListFoldArgs
      pushAtom :
        (a : atom) -> (l : List atom) -> contextType l -> contextType (a :: l)
      {- XXX
    nilElim :
      (contextUponEntry : contextType) ->
      (contextType, pred contextUponEntry [])
    consElim :
      (contextUponEntry : contextType) ->
      (a : atom) ->
      (processed : List atom) ->
      (accum : pred contextUponEntry processed) ->
      (remaining : List atom) ->
      (recursiveCall :
        ((context : contextType) -> (contextType, pred context remaining))) ->
      Void
      -}

public export
listFold : {atom : Type} -> {contextType : List atom -> Type} ->
  {listPredicate :
    (predecessors : List atom) ->
    (context : contextType predecessors) ->
    List atom ->
    Type} ->
  (signature : ListFoldSig listPredicate) ->
  {predecessors : List atom} ->
  (context : contextType predecessors) -> (l : List atom) ->
  (contextType l, listPredicate predecessors context l)
listFold signature context [] =
  ?listFold_hole_nil
listFold signature {predecessors} context (a :: l) =
  let recCall = listFold signature {predecessors=(a :: predecessors)} (pushAtom signature a predecessors context) l in
  ?listFold_hole_cons
