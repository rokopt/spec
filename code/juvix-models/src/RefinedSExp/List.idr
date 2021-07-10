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
      nilElim :
        (predecessors : List atom) -> (context : contextType predecessors) ->
        (contextType predecessors, listPredicate predecessors context [])
      consElim :
        (predecessors : List atom) ->
        (a : atom) -> (l : List atom) ->
        (recursiveCall :
          (calledContext : contextType (a :: predecessors)) ->
          (contextType (a :: predecessors),
           listPredicate (a :: predecessors) calledContext l)) ->
        (contextUponEntry : contextType predecessors) ->
        (contextType predecessors,
         listPredicate predecessors contextUponEntry (a :: l))

public export
listFoldFlip : {atom : Type} -> {contextType : List atom -> Type} ->
  {listPredicate :
    (predecessors : List atom) ->
    (context : contextType predecessors) ->
    List atom ->
    Type} ->
  (signature : ListFoldSig listPredicate) ->
  {predecessors : List atom} ->
  (l : List atom) ->
  (context : contextType predecessors) ->
  (contextType predecessors, listPredicate predecessors context l)
listFoldFlip signature {predecessors} [] =
  nilElim signature predecessors
listFoldFlip signature {predecessors} (a :: l) =
  consElim signature predecessors a l
    (listFoldFlip signature {predecessors=(a :: predecessors)} l)

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
  (contextType predecessors, listPredicate predecessors context l)
listFold signature context l = listFoldFlip signature l context
