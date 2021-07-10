module RefinedSExp.List

%default total

public export
record
ListContextIndSig {atom : Type} {contextType : List atom -> Type}
  (listPredicate :
    (predecessors : List atom) ->
    (context : contextType predecessors) ->
    List atom ->
    Type) where
      constructor ListContextIndArgs
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

public export
listContextInd : {contextType, atom : Type} ->
  {pred : contextType -> List atom -> Type} ->
  (signature : ListContextIndSig pred) ->
  (context : contextType) -> (l : List atom) ->
  (contextType, pred context l)
listContextInd signature context [] =
  nilElim signature context
listContextInd signature context (a :: l) =
  listContextInd signature ?listContextInd_hole_context l
  -}
