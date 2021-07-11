module RefinedSExp.List

import Library.FunctionsAndRelations
import public Data.List

%default total

-- This is not the induction principle that we'll use; it's here to help
-- picture why we need a context to write a _generic_ function which can be
-- tail-recursive (if `consElim` is) in an eagerly-evaluated language.
nonTailRecursiveListInd :
  {atom : Type} ->
  {lp : List atom -> Type} ->
  (nilElim : lp []) ->
  (consElim :
    (a : atom) -> (l : List atom) ->
    lp l -> lp (a :: l)) ->
  (l : List atom) -> lp l
nonTailRecursiveListInd nilElim consElim [] =
  nilElim
nonTailRecursiveListInd nilElim consElim (a :: l) =
  consElim a l (nonTailRecursiveListInd nilElim consElim l)

public export
record ListFoldSig (atom, contextType, lp : Type) where
  constructor ListFoldArgs
  nilElim :
    (context : contextType) -> (contextType, lp)
  consElim :
    (a : atom) -> (l : List atom) ->
    (recursiveCall :
      (calledContext : contextType) -> (contextType, lp)) ->
    (contextUponEntry : contextType) ->
    (contextType, lp)

public export
listFoldFlip : {atom, contextType, lp : Type} ->
  (signature : ListFoldSig atom contextType lp) ->
  (l : List atom) ->
  (context : contextType) ->
  (contextType, lp)
listFoldFlip signature [] =
  nilElim signature
listFoldFlip signature (a :: l) =
  consElim signature a l (listFoldFlip signature l)

public export
listFold : {atom, contextType, lp : Type} ->
  (signature : ListFoldSig atom contextType lp) ->
  (context : contextType) ->
  (l : List atom) ->
  (contextType, lp)
listFold signature = flip (listFoldFlip signature)

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
record ListForAllFoldSig (atom, contextType, ap : Type)
  where
    constructor ListForAllFoldArgs
    nilElim : contextType -> contextType
    pushAtom : atom -> contextType -> contextType
    consElim :
      (a : atom) -> (l : List atom) ->
      (contextType, List ap) ->
      (contextType, ap)

public export
ListForAllFoldSigToFoldSig : {atom, contextType, ap : Type} ->
  ListForAllFoldSig atom contextType ap ->
  ListFoldSig atom contextType (List ap)
ListForAllFoldSigToFoldSig signature =
  ListFoldArgs {lp=(List ap)}
    (\context => (nilElim signature context, []))
    (\a, l, recursiveCall, contextUponEntry =>
      let argumentsToInduction = pushAtom signature a contextUponEntry in
      let inductionOut = recursiveCall argumentsToInduction in
      let elimOut = consElim signature a l inductionOut in
      (fst elimOut, snd elimOut :: snd inductionOut))

public export
listForAllFold : {atom, contextType, ap : Type} ->
  (signature : ListForAllFoldSig atom contextType ap) ->
  (context : contextType) ->
  (l : List atom) -> (contextType, List ap)
listForAllFold signature = listFold (ListForAllFoldSigToFoldSig signature)

public export
record
ListDepFoldSig {atom : Type} {contextType : List atom -> Type}
  (lp :
    -- The most recent predecessor is the head of `predecessors`.
    (predecessors : List atom) ->
    (context : contextType predecessors) ->
    List atom ->
    Type) where
      constructor ListDepFoldArgs
      nilElim :
        (predecessors : List atom) -> (context : contextType predecessors) ->
        (contextType predecessors, lp predecessors context [])
      consElim :
        (predecessors : List atom) ->
        (a : atom) -> (l : List atom) ->
        (recursiveCall :
          (calledContext : contextType (a :: predecessors)) ->
          (contextType (a :: predecessors),
           lp (a :: predecessors) calledContext l)) ->
        (contextUponEntry : contextType predecessors) ->
        (contextType predecessors,
         lp predecessors contextUponEntry (a :: l))

public export
listDepFoldFlip : {atom : Type} -> {contextType : List atom -> Type} ->
  {lp :
    (predecessors : List atom) ->
    (context : contextType predecessors) ->
    List atom ->
    Type} ->
  (signature : ListDepFoldSig lp) ->
  {predecessors : List atom} ->
  (l : List atom) ->
  (context : contextType predecessors) ->
  (contextType predecessors, lp predecessors context l)
listDepFoldFlip signature {predecessors} [] =
  nilElim signature predecessors
listDepFoldFlip signature {predecessors} (a :: l) =
  consElim signature predecessors a l
    (listDepFoldFlip signature {predecessors=(a :: predecessors)} l)

public export
listDepFold : {atom : Type} -> {contextType : List atom -> Type} ->
  {lp :
    (predecessors : List atom) ->
    (context : contextType predecessors) ->
    List atom ->
    Type} ->
  (signature : ListDepFoldSig lp) ->
  {predecessors : List atom} ->
  (context : contextType predecessors) -> (l : List atom) ->
  (contextType predecessors, lp predecessors context l)
listDepFold signature context l = listDepFoldFlip signature l context

public export
ListFoldNonDepSigToDepSig : {atom, contextType, lp : Type} ->
  (signature : ListFoldSig atom contextType lp) ->
  ListDepFoldSig
    {atom} {contextType=(\_ => contextType)} (\_, _, _ => lp)
ListFoldNonDepSigToDepSig signature =
  ListDepFoldArgs (\_ => nilElim signature) (\_ => consElim signature)

public export
listDepFoldFlipCorrect : {atom, contextType, lp : Type} ->
  (signature : ListFoldSig atom contextType lp) ->
  {predecessors : List atom} ->
  (l : List atom) ->
  listFoldFlip signature l =
    listDepFoldFlip
      {atom}
      {contextType=(\_ => contextType)}
      {lp=(\_, _, _ => lp)}
      (ListFoldNonDepSigToDepSig signature)
      {predecessors}
      l
listDepFoldFlipCorrect signature [] =
  Refl
listDepFoldFlipCorrect signature (a :: l) =
  cong (consElim signature a l) (listDepFoldFlipCorrect signature l)

public export
listDepFoldCorrect : {atom, contextType, lp : Type} ->
  (signature : ListFoldSig atom contextType lp) ->
  {predecessors : List atom} ->
  (context : contextType) ->
  (l : List atom) ->
  listFold signature context l =
    listDepFold
      {atom}
      {contextType=(\_ => contextType)}
      {lp=(\_, _, _ => lp)}
      (ListFoldNonDepSigToDepSig signature)
      {predecessors}
      context
      l
listDepFoldCorrect signature context l =
  applyEq (listDepFoldFlipCorrect signature l)

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
    (contextType predecessors, lp predecessors context l) ->
    Type)
  where
    constructor ListMetaFoldArgs
    metaNilElim :
      (predecessors : List atom) -> (context : contextType predecessors) ->
      ldp predecessors context [] (nilElim signature predecessors context)
    metaConsElim :
      (predecessors : List atom) ->
      (a : atom) -> (l : List atom) ->
      (recursiveCall :
        (calledContext : contextType (a :: predecessors)) ->
        (contextType (a :: predecessors),
         ldp (a :: predecessors) calledContext l
          (listDepFoldFlip signature l calledContext))) ->
      (contextUponEntry : contextType predecessors) ->
      ldp predecessors contextUponEntry (a :: l)
        (consElim signature predecessors a l
          (listDepFoldFlip signature l) contextUponEntry)

public export
listMetaFoldArgs :
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
    (contextType predecessors, lp predecessors context l) ->
    Type} ->
  (metaSig : ListMetaFoldSig signature ldp) ->
  ListDepFoldSig
    {contextType=(\_ => ())}
    (\predecessors, _, l =>
      (context : contextType predecessors) ->
        ldp predecessors context l
          (listDepFold signature {predecessors} context l))
listMetaFoldArgs metaSig =
  (ListDepFoldArgs
    (\predecessors, _ =>
      ((),
       \contextUponEntry => metaNilElim metaSig predecessors contextUponEntry))
    (\predecessors, a, l, recursiveCall, _ =>
      ((),
       \contextUponEntry =>
        metaConsElim metaSig predecessors a l
          (\context => (context, snd (recursiveCall ()) context))
          contextUponEntry)))

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
    (contextUponEntry : contextType predecessors) ->
    (l : List atom) ->
    (contextType predecessors, lp predecessors contextUponEntry l) ->
    Type} ->
  (metaSig : ListMetaFoldSig signature ldp) ->
  {predecessors : List atom} ->
  (context : contextType predecessors) -> (l : List atom) ->
  ldp predecessors context l (listDepFold signature {predecessors} context l)
listMetaFold {signature} {ldp} metaSig context' l' =
  snd (listDepFold (listMetaFoldArgs metaSig) () l') context'
