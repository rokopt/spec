module RefinedSExp.List

import public Data.List

%default total

public export
record
ListDepFoldSig {atom : Type} {contextType : List atom -> Type}
  (listPredicate :
    -- The most recent predecessor is the head of `predecessors`.
    (predecessors : List atom) ->
    (context : contextType predecessors) ->
    List atom ->
    Type) where
      constructor ListDepFoldArgs
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
listDepFoldFlip : {atom : Type} -> {contextType : List atom -> Type} ->
  {listPredicate :
    (predecessors : List atom) ->
    (context : contextType predecessors) ->
    List atom ->
    Type} ->
  (signature : ListDepFoldSig listPredicate) ->
  {predecessors : List atom} ->
  (l : List atom) ->
  (context : contextType predecessors) ->
  (contextType predecessors, listPredicate predecessors context l)
listDepFoldFlip signature {predecessors} [] =
  nilElim signature predecessors
listDepFoldFlip signature {predecessors} (a :: l) =
  consElim signature predecessors a l
    (listDepFoldFlip signature {predecessors=(a :: predecessors)} l)

public export
listDepFold : {atom : Type} -> {contextType : List atom -> Type} ->
  {listPredicate :
    (predecessors : List atom) ->
    (context : contextType predecessors) ->
    List atom ->
    Type} ->
  (signature : ListDepFoldSig listPredicate) ->
  {predecessors : List atom} ->
  (context : contextType predecessors) -> (l : List atom) ->
  (contextType predecessors, listPredicate predecessors context l)
listDepFold signature context l = listDepFoldFlip signature l context
