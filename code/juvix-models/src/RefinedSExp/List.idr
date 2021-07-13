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
    (contextType -> (contextType, lp)) ->
    (contextType -> (contextType, lp))

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

public export
record
ListDepFoldSig {atom : Type} {contextType : Type}
  (lp : (context : contextType) ->
    List atom ->
    Type) where
      constructor ListDepFoldArgs
      nilElim :
        (context : contextType) -> (contextType, lp context [])
      consElim :
        (a : atom) -> (l : List atom) ->
        (recursiveCall :
          (calledContext : contextType) ->
          (contextType, lp calledContext l)) ->
        (contextUponEntry : contextType) ->
        (contextType, lp contextUponEntry (a :: l))

public export
listDepFoldFlip : {atom : Type} -> {contextType : Type} ->
  {lp :
    (context : contextType) ->
    List atom ->
    Type} ->
  (signature : ListDepFoldSig lp) ->
  (l : List atom) ->
  (context : contextType) ->
  (contextType, lp context l)
listDepFoldFlip signature [] =
  nilElim signature
listDepFoldFlip signature (a :: l) =
  consElim signature a l
    (listDepFoldFlip signature l)

public export
listDepFold : {atom : Type} -> {contextType : Type} ->
  {lp :
    (context : contextType) ->
    List atom ->
    Type} ->
  (signature : ListDepFoldSig lp) ->
  (context : contextType) -> (l : List atom) ->
  (contextType, lp context l)
listDepFold signature context l = listDepFoldFlip signature l context

public export
ListFoldNonDepSigToDepSig : {atom, contextType, lp : Type} ->
  (signature : ListFoldSig atom contextType lp) ->
  ListDepFoldSig
    {atom} {contextType} (\_, _ => lp)
ListFoldNonDepSigToDepSig signature =
  ListDepFoldArgs (nilElim signature) (consElim signature)

public export
listDepFoldFlipCorrect : {atom, contextType, lp : Type} ->
  (signature : ListFoldSig atom contextType lp) ->
  (l : List atom) ->
  listFoldFlip signature l =
    listDepFoldFlip
      {atom}
      {contextType}
      {lp=(\_, _ => lp)}
      (ListFoldNonDepSigToDepSig signature)
      l
listDepFoldFlipCorrect signature [] =
  Refl
listDepFoldFlipCorrect signature (a :: l) =
  cong (consElim signature a l) (listDepFoldFlipCorrect signature l)

public export
listDepFoldCorrect : {atom, contextType, lp : Type} ->
  (signature : ListFoldSig atom contextType lp) ->
  (context : contextType) ->
  (l : List atom) ->
  listFold signature context l =
    listDepFold
      {atom}
      {contextType}
      {lp=(\_, _ => lp)}
      (ListFoldNonDepSigToDepSig signature)
      context
      l
listDepFoldCorrect signature context l =
  applyEq (listDepFoldFlipCorrect signature l) Refl

public export
record
ListDepContextFreeFoldSig {atom : Type}
  (lp : List atom -> Type) where
    constructor ListDepContextFreeFoldArgs
    nilElim : lp []
    consElim :
      (a : atom) -> (l : List atom) -> (recursiveResult : lp l) -> lp (a :: l)

public export
ListDepContextFreeFoldSigToDepFoldSig :
  {atom : Type} -> {lp : List atom -> Type} ->
  ListDepContextFreeFoldSig lp ->
  ListDepFoldSig {atom} {contextType=()} (\_ => lp)
ListDepContextFreeFoldSigToDepFoldSig signature =
  ListDepFoldArgs
    (\_ => ((), nilElim signature))
    (\a, l, recursiveCall, _ =>
      ((), consElim signature a l (snd (recursiveCall ()))))

public export
listDepContextFreeFold : {atom : Type} ->
  {lp : List atom -> Type} ->
  (signature : ListDepContextFreeFoldSig lp) ->
  (l : List atom) -> lp l
listDepContextFreeFold signature l =
  snd
    (listDepFold
      (ListDepContextFreeFoldSigToDepFoldSig signature) () l)

infixr 7 :::
public export
data ListForAll :
  {atom : Type} -> (lp : atom -> Type) -> List atom -> Type where
    (|:|) : {atom : Type} -> {lp : atom -> Type} ->
            ListForAll lp []
    (:::) : {atom : Type} -> {lp : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            lp a -> ListForAll lp l ->
            ListForAll lp (a :: l)

prefix 11 <::
prefix 11 >::
public export
data ListExists :
  {atom : Type} -> (lp : atom -> Type) -> List atom -> Type where
    (<::) : {atom : Type} -> {lp : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            lp a ->
            ListExists lp (a :: l)
    (>::) : {atom : Type} -> {lp : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            ListExists lp l ->
            ListExists lp (a :: l)

NoExistsNil : {atom : Type} -> {lp : atom -> Type} -> Not (ListExists lp [])
NoExistsNil ((<::) _) impossible
NoExistsNil ((>::) _) impossible

NoExistsNeither : {atom : Type} -> {lp : atom -> Type} ->
  {a : atom} -> {l : List atom} ->
  Not (lp a) -> Not (ListExists lp l) ->
  Not (ListExists lp (a :: l))
NoExistsNeither noA _ ((<::) existsA) = noA existsA
NoExistsNeither _ noList ((>::) existsList) = noList existsList

public export
ListForAllConstruct : {atom : Type} ->
  {lp : atom -> Type} ->
  (f : (a : atom) -> lp a) -> (l : List atom) ->
  ListForAll lp l
ListForAllConstruct f =
  listDepContextFreeFold
    (ListDepContextFreeFoldArgs
      (|:|)
      (\a, _, lpl => f a ::: lpl))

public export
DecListForAll : {atom : Type} ->
  {lp : atom -> Type} ->
  (dec : (a : atom) -> Dec (lp a)) -> (l : List atom) ->
  Dec (ListForAll lp l)
DecListForAll dec =
  listDepContextFreeFold
    (ListDepContextFreeFoldArgs {lp=(Dec . ListForAll lp)}
      (Yes (|:|))
      (\a, _, decList =>
        case (dec a, decList) of
          (Yes yesA, Yes yesList) => Yes (yesA ::: yesList)
          (No noA, _) =>
            No (\yesList =>
              noA (case yesList of
                (|:|) impossible
                (yesA ::: _) => yesA))
          (_, No noList) =>
            No (\yesA =>
              noList (case yesA of
                (|:|) impossible
                (_ ::: yesList) => yesList))))

public export
DecListExists : {atom : Type} ->
  {lp : atom -> Type} ->
  (dec : (a : atom) -> Dec (lp a)) -> (l : List atom) ->
  Dec (ListExists lp l)
DecListExists dec =
  listDepContextFreeFold
    (ListDepContextFreeFoldArgs {lp=(Dec . ListExists lp)}
      (No NoExistsNil)
      (\a, _, decList =>
        case (dec a, decList) of
          (Yes yesA, _) => Yes (<:: yesA)
          (_, Yes existsList) => Yes (>:: existsList)
          (No noA, No noList) => No (NoExistsNeither noA noList)))

public export
record
ListForAllFoldSig {atom : Type}
  (ap : atom -> Type) where
    constructor ListForAllFoldArgs
    consElim :
      (a : atom) -> (l : List atom) ->
      (recursiveResult : ListForAll ap l) ->
      ListForAll ap (a :: l)

public export
ListForAllFoldSigToDepContextFreeFoldSig:
  {atom : Type} -> {ap : atom -> Type} ->
  ListForAllFoldSig {atom} ap ->
  ListDepContextFreeFoldSig (ListForAll ap)
ListForAllFoldSigToDepContextFreeFoldSig signature =
  ListDepContextFreeFoldArgs (|:|) (consElim signature)

public export
listForAllFold : {atom : Type} ->
  {ap : atom -> Type} ->
  (signature : ListForAllFoldSig ap) ->
  (l : List atom) -> ListForAll ap l
listForAllFold {atom} signature =
  listDepContextFreeFold (ListForAllFoldSigToDepContextFreeFoldSig signature)

public export
record ListMetaFoldSig
  {atom : Type} {contextType : Type}
  {lp :
    (context : contextType) ->
    List atom ->
    Type}
  (signature : ListDepFoldSig lp)
  {metaContextType : Type}
  (ldp :
    (metaContext : metaContextType) ->
    (context : contextType) ->
    (l : List atom) ->
    (contextType, lp context l) ->
    Type)
  where
    constructor ListMetaFoldArgs
    metaNilElim :
      (metaContext : metaContextType) ->
      (metaContextType,
       (context : contextType) ->
       ldp metaContext context [] (nilElim signature context))
    metaConsElim :
      (a : atom) -> (l : List atom) ->
      (recursiveCall :
        (calledMetaContext : metaContextType) ->
        (metaContextType,
         (calledContext : contextType) ->
          ldp calledMetaContext calledContext l
            (listDepFoldFlip signature l calledContext))) ->
      (metaContextUponEntry : metaContextType) ->
      (metaContextType,
       (contextUponEntry : contextType) ->
        ldp metaContextUponEntry contextUponEntry (a :: l)
        (consElim signature a l
          (listDepFoldFlip signature l) contextUponEntry))

public export
listMetaFoldArgs :
  {atom : Type} -> {contextType : Type} ->
  {lp :
    (context : contextType) ->
    List atom ->
    Type} ->
  {signature : ListDepFoldSig lp} ->
  {metaContextType : Type} ->
  {ldp :
    (metaContext : metaContextType) ->
    (context : contextType) ->
    (l : List atom) ->
    (contextType, lp context l) ->
    Type} ->
  (metaSig : ListMetaFoldSig signature ldp) ->
  ListDepFoldSig {contextType=metaContextType}
    (\metaContext, l =>
      (context : contextType) ->
        ldp metaContext context l
          (listDepFold signature context l))
listMetaFoldArgs metaSig =
  (ListDepFoldArgs {contextType=metaContextType}
    (metaNilElim metaSig) (metaConsElim metaSig))

public export
listMetaFold :
  {atom : Type} -> {contextType : Type} ->
  {lp :
    (context : contextType) ->
    List atom ->
    Type} ->
  {signature : ListDepFoldSig lp} ->
  {metaContextType : Type} ->
  {ldp :
    (metaContext : metaContextType) ->
    (contextUponEntry : contextType) ->
    (l : List atom) ->
    (contextType, lp contextUponEntry l) ->
    Type} ->
  (metaSig : ListMetaFoldSig signature ldp) ->
  (metaContext : metaContextType) ->
  (l : List atom) ->
  (metaContextType,
    (context : contextType) ->
     ldp metaContext context l (listDepFold signature context l))
listMetaFold {contextType} {signature} {metaContextType} {ldp} metaSig =
  listDepFold {contextType=metaContextType} (listMetaFoldArgs metaSig)
