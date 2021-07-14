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
record ListFoldSig {f : Type -> Type} (atom, contextType, lp : Type) where
  constructor ListFoldArgs
  nilElim :
    (context : contextType) -> f (contextType, lp)
  consElim :
    (a : atom) -> (l : List atom) ->
    (contextType -> f (contextType, lp)) ->
    (contextType -> f (contextType, lp))

public export
listFoldFlip : {f : Type -> Type} -> {atom, contextType, lp : Type} ->
  (signature : ListFoldSig {f} atom contextType lp) ->
  (l : List atom) ->
  (context : contextType) ->
  f (contextType, lp)
listFoldFlip {f} {lp} signature =
  nonTailRecursiveListInd {atom} {lp=(\_ => contextType -> f (contextType, lp))}
      (nilElim signature) (consElim signature)

public export
listFold : {f : Type -> Type} -> {atom, contextType, lp : Type} ->
  (signature : ListFoldSig {f} atom contextType lp) ->
  (context : contextType) ->
  (l : List atom) ->
  f (contextType, lp)
listFold signature = flip (listFoldFlip signature)

public export
record
ListDepFoldSig {f : Type -> Type} {atom : Type} {contextType : Type}
  (lp : (context : contextType) ->
    List atom ->
    Type) where
      constructor ListDepFoldArgs
      nilElim :
        (context : contextType) -> f (contextType, lp context [])
      consElim :
        (a : atom) -> (l : List atom) ->
        (recursiveCall :
          (calledContext : contextType) ->
          f (contextType, lp calledContext l)) ->
        (contextUponEntry : contextType) ->
        f (contextType, lp contextUponEntry (a :: l))

public export
listDepFoldFlip : {f : Type -> Type} -> {atom : Type} -> {contextType : Type} ->
  {lp :
    (context : contextType) ->
    List atom ->
    Type} ->
  (signature : ListDepFoldSig {f} lp) ->
  (l : List atom) ->
  (context : contextType) ->
  f (contextType, lp context l)
listDepFoldFlip {f} {lp} signature =
  nonTailRecursiveListInd {atom}
    {lp=(\l => (context : contextType) -> f (contextType, lp context l))}
      (nilElim signature) (consElim signature)

public export
listDepFold : {f : Type -> Type} -> {atom : Type} -> {contextType : Type} ->
  {lp :
    (context : contextType) ->
    List atom ->
    Type} ->
  (signature : ListDepFoldSig {f} lp) ->
  (context : contextType) -> (l : List atom) ->
  f (contextType, lp context l)
listDepFold {f} signature context l = listDepFoldFlip signature l context

public export
ListFoldNonDepSigToDepSig : {f : Type -> Type} ->
  {atom, contextType, lp : Type} ->
  (signature : ListFoldSig {f} atom contextType lp) ->
  ListDepFoldSig {f}
    {atom} {contextType} (\_, _ => lp)
ListFoldNonDepSigToDepSig signature =
  ListDepFoldArgs (nilElim signature) (consElim signature)

public export
listDepFoldFlipCorrect : {f : Type -> Type} -> {atom, contextType, lp : Type} ->
  (signature : ListFoldSig {f} atom contextType lp) ->
  (l : List atom) ->
  listFoldFlip {f} signature l =
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
listDepFoldCorrect : {f : Type -> Type} -> {atom, contextType, lp : Type} ->
  (signature : ListFoldSig atom contextType lp) ->
  (context : contextType) ->
  (l : List atom) ->
  listFold signature context l =
    listDepFold
      {atom}
      {contextType}
      {lp=(\_, _ => lp)}
      (ListFoldNonDepSigToDepSig {f} signature)
      context
      l
listDepFoldCorrect {f} signature context l =
  applyEq (listDepFoldFlipCorrect signature l) Refl

public export
record
ListDepContextFreeFoldSig {f : Type -> Type} {atom : Type}
  (lp : List atom -> Type) where
    constructor ListDepContextFreeFoldArgs
    nilElim : f (lp [])
    consElim :
      (a : atom) -> (l : List atom) -> (recursiveResult : f (lp l)) ->
      f (lp (a :: l))

public export
ListDepContextFreeFoldSigToDepFoldSig :
  {f : Type -> Type} -> Functor f => {atom : Type} -> {lp : List atom -> Type} ->
  ListDepContextFreeFoldSig {f} lp ->
  ListDepFoldSig {f} {atom} {contextType=()} (\_ => lp)
ListDepContextFreeFoldSigToDepFoldSig {f} signature =
  ListDepFoldArgs {f}
    (\_ => map (MkPair ()) (nilElim signature))
    (\a, l, recursiveCall, _ =>
      map (MkPair ()) (consElim signature a l (map snd (recursiveCall ()))))

public export
listDepContextFreeFold : {f : Type -> Type} -> Functor f =>
  {atom : Type} ->
  {lp : List atom -> Type} ->
  (signature : ListDepContextFreeFoldSig {f} lp) ->
  (l : List atom) -> f (lp l)
listDepContextFreeFold {f} signature l =
  map snd (listDepFold (ListDepContextFreeFoldSigToDepFoldSig signature) () l)

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

public export
NoExistsNil : {atom : Type} -> {lp : atom -> Type} -> Not (ListExists lp [])
NoExistsNil ((<::) _) impossible
NoExistsNil ((>::) _) impossible

public export
NoExistsNeither : {atom : Type} -> {lp : atom -> Type} ->
  {a : atom} -> {l : List atom} ->
  Not (lp a) -> Not (ListExists lp l) ->
  Not (ListExists lp (a :: l))
NoExistsNeither noA _ ((<::) existsA) = noA existsA
NoExistsNeither _ noList ((>::) existsList) = noList existsList

public export
ListForAllConstruct : {f : Type -> Type} -> Applicative f => {atom : Type} ->
  {lp : atom -> Type} ->
  (construct : (a : atom) -> f (lp a)) -> (l : List atom) ->
  f (ListForAll lp l)
ListForAllConstruct {f} {lp} construct =
  listDepContextFreeFold {f} {lp=(ListForAll lp)}
    (ListDepContextFreeFoldArgs {f}
      (pure (|:|))
      (\a, _, lpl => [| construct a ::: lpl |]))

infixr 7 :::
public export
ListForAllConsDec : {atom : Type} -> {lp : atom -> Type} ->
  {a : atom} -> {l : List atom} ->
  Dec (lp a) -> Dec (ListForAll lp l) ->
  Dec (ListForAll lp (a :: l))
ListForAllConsDec decHead decTail =
  case (decHead, decTail) of
    (Yes yesHead, Yes yesTail) => Yes (yesHead ::: yesTail)
    (No noHead, _) =>
      No (\yesTail =>
        case yesTail of
          (|:|) impossible
          (yesHead ::: _) => noHead yesHead)
    (_, No noTail) =>
      No (\yesHead =>
        case yesHead of
          (|:|) impossible
          (_ ::: yesTail) => noTail yesTail)

public export
DecListForAll : {atom : Type} -> {f : Type -> Type} -> Applicative f =>
  {lp : atom -> Type} ->
  (dec : (a : atom) -> f (Dec (lp a))) -> (l : List atom) ->
  f (Dec (ListForAll lp l))
DecListForAll dec =
  listDepContextFreeFold
    (ListDepContextFreeFoldArgs {lp=(Dec . ListForAll lp)}
      (pure (Yes (|:|)))
      (\a, _, decList => [| ListForAllConsDec (dec a) decList |] ))

public export
ListExistsEitherDec : {atom : Type} -> {lp : atom -> Type} ->
  {a : atom} -> {l : List atom} ->
  Dec (lp a) -> Dec (ListExists lp l) ->
  Dec (ListExists lp (a :: l))
ListExistsEitherDec decHead decTail =
  case (decHead, decTail) of
    (Yes yesA, _) => Yes (<:: yesA)
    (_, Yes existsList) => Yes (>:: existsList)
    (No noA, No noList) => No (NoExistsNeither noA noList)

public export
DecListExists : {f : Type -> Type} -> Applicative f => {atom : Type} ->
  {lp : atom -> Type} ->
  (dec : (a : atom) -> f (Dec (lp a))) -> (l : List atom) ->
  f (Dec (ListExists lp l))
DecListExists dec =
  listDepContextFreeFold
    (ListDepContextFreeFoldArgs {lp=(Dec . ListExists lp)}
      (pure (No NoExistsNil))
      (\a, _, decList => [| ListExistsEitherDec (dec a) decList |] ))

public export
record
ListForAllFoldSig {f : Type -> Type} {atom : Type}
  (ap : atom -> Type) where
    constructor ListForAllFoldArgs
    consElim :
      (a : atom) -> (l : List atom) ->
      (recursiveResult : f (ListForAll ap l)) ->
      f (ListForAll ap (a :: l))

public export
ListForAllFoldSigToDepContextFreeFoldSig :
  {f : Type -> Type} -> Applicative f => {atom : Type} -> {ap : atom -> Type} ->
  ListForAllFoldSig {f} {atom} ap ->
  ListDepContextFreeFoldSig {f} (ListForAll ap)
ListForAllFoldSigToDepContextFreeFoldSig signature =
  ListDepContextFreeFoldArgs (pure (|:|)) (consElim signature)

public export
listForAllFold : {f : Type -> Type} -> Applicative f => {atom : Type} ->
  {ap : atom -> Type} ->
  (signature : ListForAllFoldSig {f} ap) ->
  (l : List atom) -> f (ListForAll ap l)
listForAllFold {atom} signature =
  listDepContextFreeFold (ListForAllFoldSigToDepContextFreeFoldSig signature)

public export
record ListMetaFoldSig {f : Type -> Type}
  {atom : Type} {contextType : Type}
  {lp :
    (context : contextType) ->
    List atom ->
    Type}
  (signature : ListDepFoldSig {f} lp)
  {metaContextType : Type}
  (ldp :
    (metaContext : metaContextType) ->
    (context : contextType) ->
    (l : List atom) ->
    (f (contextType, lp context l)) ->
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
listMetaFoldArgs : {f : Type -> Type} ->
  {atom : Type} -> {contextType : Type} ->
  {lp :
    (context : contextType) ->
    List atom ->
    Type} ->
  {signature : ListDepFoldSig {f} lp} ->
  {metaContextType : Type} ->
  {ldp :
    (metaContext : metaContextType) ->
    (context : contextType) ->
    (l : List atom) ->
    f (contextType, lp context l) ->
    Type} ->
  (metaSig : ListMetaFoldSig {f} signature ldp) ->
  ListDepFoldSig {f=Prelude.Basics.id} {contextType=metaContextType}
    (\metaContext, l =>
      (context : contextType) ->
        ldp metaContext context l
          (listDepFold signature context l))
listMetaFoldArgs {f} metaSig =
  (ListDepFoldArgs {f=id} {contextType=metaContextType}
    (metaNilElim metaSig) (metaConsElim metaSig))

public export
listMetaFold : {f : Type -> Type} ->
  {atom : Type} -> {contextType : Type} ->
  {lp :
    (context : contextType) ->
    List atom ->
    Type} ->
  {signature : ListDepFoldSig {f} lp} ->
  {metaContextType : Type} ->
  {ldp :
    (metaContext : metaContextType) ->
    (contextUponEntry : contextType) ->
    (l : List atom) ->
    f (contextType, lp contextUponEntry l) ->
    Type} ->
  (metaSig : ListMetaFoldSig {f} signature ldp) ->
  (metaContext : metaContextType) ->
  (l : List atom) ->
  (metaContextType,
    (context : contextType) ->
     ldp metaContext context l (listDepFold signature context l))
listMetaFold {f} {contextType} {signature} {metaContextType} {ldp} metaSig =
  listDepFold {f=id} {contextType=metaContextType}
    {lp=(\metaContext, l =>
      (context : contextType) ->
      ldp metaContext context l (listDepFold signature context l))}
    (listMetaFoldArgs {f} metaSig)
