module RefinedSExp.List

import Library.FunctionsAndRelations
import public Data.List

%default total

-- This is not the induction principle that we'll use; it's here to help
-- picture why we need a context to write a _generic_ function which can be
-- tail-recursive (if `consElim` is) in an eagerly-evaluated language.
nonTailRecursiveListInd :
  {atom : Type} ->
  {listPredicate : List atom -> Type} ->
  (nilElim : listPredicate []) ->
  (consElim :
    (a : atom) -> (l : List atom) ->
    listPredicate l -> listPredicate (a :: l)) ->
  (l : List atom) -> listPredicate l
nonTailRecursiveListInd nilElim consElim [] =
  nilElim
nonTailRecursiveListInd nilElim consElim (a :: l) =
  consElim a l (nonTailRecursiveListInd nilElim consElim l)

public export
record ListFoldSig (atom, contextType, listPredicate : Type) where
  constructor ListFoldArgs
  nilElim :
    (context : contextType) -> (contextType, listPredicate)
  consElim :
    (a : atom) -> (l : List atom) ->
    (recursiveCall :
      (calledContext : contextType) -> (contextType, listPredicate)) ->
    (contextUponEntry : contextType) ->
    (contextType, listPredicate)

public export
listFoldFlip : {atom, contextType, listPredicate : Type} ->
  (signature : ListFoldSig atom contextType listPredicate) ->
  (l : List atom) ->
  (context : contextType) ->
  (contextType, listPredicate)
listFoldFlip signature [] =
  nilElim signature
listFoldFlip signature (a :: l) =
  consElim signature a l (listFoldFlip signature l)

public export
listFold : {atom, contextType, listPredicate : Type} ->
  (signature : ListFoldSig atom contextType listPredicate) ->
  (context : contextType) ->
  (l : List atom) ->
  (contextType, listPredicate)
listFold signature = flip (listFoldFlip signature)

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
  ListDepFoldArgs (\_ => nilElim signature) (\_ => consElim signature)

public export
listDepFoldFlipCorrect : {atom, contextType, listPredicate : Type} ->
  (signature : ListFoldSig atom contextType listPredicate) ->
  {predecessors : List atom} ->
  (l : List atom) ->
  listFoldFlip signature l =
    listDepFoldFlip
      {atom}
      {contextType=(\_ => contextType)}
      {listPredicate=(\_, _, _ => listPredicate)}
      (ListFoldNonDepSigToDepSig signature)
      {predecessors}
      l
listDepFoldFlipCorrect signature [] =
  Refl
listDepFoldFlipCorrect signature (a :: l) =
  cong (consElim signature a l) (listDepFoldFlipCorrect signature l)

public export
listDepFoldCorrect : {atom, contextType, listPredicate : Type} ->
  (signature : ListFoldSig atom contextType listPredicate) ->
  {predecessors : List atom} ->
  (context : contextType) ->
  (l : List atom) ->
  listFold signature context l =
    listDepFold
      {atom}
      {contextType=(\_ => contextType)}
      {listPredicate=(\_, _, _ => listPredicate)}
      (ListFoldNonDepSigToDepSig signature)
      {predecessors}
      context
      l
listDepFoldCorrect signature context l =
  applyEq (listDepFoldFlipCorrect signature l)

infixr 7 :::
public export
data ListForAll :
  {atom : Type} -> (depType : atom -> type) -> List atom -> Type where
    (|:|) : {atom : Type} -> {depType : atom -> Type} ->
            ListForAll depType []
    (:::) : {atom : Type} -> {depType : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            depType a -> ListForAll depType l ->
            ListForAll depType (a :: l)

public export
data ListExists :
  {atom : Type} -> (depType : atom -> type) -> List atom -> Type where
    (<::) : {atom : Type} -> {depType : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            depType a ->
            ListExists depType (a :: l)
    (>::) : {atom : Type} -> {depType : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            ListExists depType l ->
            ListExists depType (a :: l)

public export
record ListMetaFoldSig
  {atom : Type} {contextType : List atom -> Type}
  {lp :
    (predecessors : List atom) ->
    (context : contextType predecessors) ->
    List atom ->
    Type}
  (signature : ListDepFoldSig lp)
  (ldp :
    (predecessors : List atom) ->
    (context : contextType predecessors) ->
    (l : List atom) ->
    lp predecessors context l ->
    Type)
  where
  constructor ListMetaFoldArgs

public export
listMetaFold :
  {atom : Type} -> {contextType : List atom -> Type} ->
  {lp :
    (predecessors : List atom) ->
    (context : contextType predecessors) ->
    List atom ->
    Type} ->
  {signature : ListDepFoldSig lp} ->
  {ldp :
    (predecessors : List atom) ->
    (context : contextType predecessors) ->
    (l : List atom) ->
    lp predecessors context l ->
    Type} ->
  (metaSig : ListMetaFoldSig signature ldp) ->
  {predecessors : List atom} ->
  (context : contextType predecessors) -> (l : List atom) ->
  ldp predecessors context l
    (snd (listDepFold signature {predecessors} context l))
listMetaFold {signature} {ldp} metaSig context' l' =
  snd
    (listDepFold
      {listPredicate=(\predecessors, context, l =>
        ldp predecessors context l (snd (listDepFold signature {predecessors} context l)))}
      (ListDepFoldArgs
        (?listMetaFold_hole_nilElim)
        (?listMetaFold_hole_consElim))
     context'
     l')
