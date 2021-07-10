module RefinedSExp.List

import Library.FunctionsAndRelations
import public Data.List

%default total

public export
record ListFoldSig (atom, contextType, listPredicate : Type) where
  nilElim :
    (predecessors : List atom) -> (context : contextType) ->
    (contextType, listPredicate)
  consElim :
    (predecessors : List atom) ->
    (a : atom) -> (l : List atom) ->
    (recursiveCall :
      (calledContext : contextType) -> (contextType, listPredicate)) ->
    (contextUponEntry : contextType) ->
    (contextType, listPredicate)

public export
listFoldFlip : {atom, contextType, listPredicate : Type} ->
  (signature : ListFoldSig atom contextType listPredicate) ->
  (predecessors : List atom) ->
  (l : List atom) ->
  (context : contextType) ->
  (contextType, listPredicate)
listFoldFlip signature predecessors [] =
  nilElim signature predecessors
listFoldFlip signature predecessors (a :: l) =
  consElim signature predecessors a l
    (listFoldFlip signature (a :: predecessors) l)

public export
listFold : {atom, contextType, listPredicate : Type} ->
  (signature : ListFoldSig atom contextType listPredicate) ->
  (predecessors : List atom) ->
  (context : contextType) ->
  (l : List atom) ->
  (contextType, listPredicate)
listFold signature predecessors = flip (listFoldFlip signature predecessors)

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

public export
ListFoldNonDepSigToDepSig : {atom, contextType, listPredicate : Type} ->
  (signature : ListFoldSig atom contextType listPredicate) ->
  ListDepFoldSig
    {atom} {contextType=(\_ => contextType)} (\_, _, _ => listPredicate)
ListFoldNonDepSigToDepSig signature =
  ListDepFoldArgs (nilElim signature) (consElim signature)

export
listDepFoldFlipCorrect : {atom, contextType, listPredicate : Type} ->
  (signature : ListFoldSig atom contextType listPredicate) ->
  (predecessors : List atom) ->
  (l : List atom) ->
  listFoldFlip signature predecessors l =
    listDepFoldFlip
      {atom}
      {contextType=(\_ => contextType)}
      {listPredicate=(\_, _, _ => listPredicate)}
      (ListFoldNonDepSigToDepSig signature)
      {predecessors}
      l
listDepFoldFlipCorrect signature predecessors [] =
  Refl
listDepFoldFlipCorrect signature predecessors (a :: l) =
  let recCallEq = listDepFoldFlipCorrect signature (a :: predecessors) l in
  cong (consElim signature predecessors a l) recCallEq

export
listDepFoldCorrect : {atom, contextType, listPredicate : Type} ->
  (signature : ListFoldSig atom contextType listPredicate) ->
  (predecessors : List atom) ->
  (context : contextType) ->
  (l : List atom) ->
  listFold signature predecessors context l =
    listDepFold
      {atom}
      {contextType=(\_ => contextType)}
      {listPredicate=(\_, _, _ => listPredicate)}
      (ListFoldNonDepSigToDepSig signature)
      {predecessors}
      context
      l
listDepFoldCorrect signature predecessors context l =
  applyEq (listDepFoldFlipCorrect signature predecessors l)
