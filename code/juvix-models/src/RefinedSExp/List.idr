module RefinedSExp.List

import Library.FunctionsAndRelations
import public Data.List

%default total

public export
record ListEliminatorSig
  {atom : Type} (lp : List atom -> Type)
  where
    constructor ListEliminatorArgs
    nilElim : lp []
    consElim : (a : atom) -> (l : List atom) -> lp l -> lp (a :: l)

public export
listEliminator :
  {atom : Type} -> {lp : List atom -> Type} ->
  (signature : ListEliminatorSig lp) ->
  (l : List atom) -> lp l
listEliminator signature [] =
  nilElim signature
listEliminator signature (a :: l) =
  consElim signature a l (listEliminator signature l)

public export
ListDepFoldSig : (f : Type -> Type) -> {atom : Type} -> {contextType : Type} ->
  (lp : contextType -> List atom -> Type) -> Type
ListDepFoldSig f lp =
  ListEliminatorSig (\l =>
    (context : contextType) -> f (contextType, lp context l))

public export
listDepFoldFlip : {f : Type -> Type} -> {atom : Type} -> {contextType : Type} ->
  {lp : (context : contextType) -> List atom -> Type} ->
  (signature : ListDepFoldSig f lp) ->
  (l : List atom) -> (context : contextType) ->
  f (contextType, lp context l)
listDepFoldFlip {f} {lp} = listEliminator

public export
listDepFold : {f : Type -> Type} -> {atom : Type} -> {contextType : Type} ->
  {lp : (context : contextType) -> List atom -> Type} ->
  (signature : ListDepFoldSig f lp) ->
  (context : contextType) -> (l : List atom) ->
  f (contextType, lp context l)
listDepFold {f} {lp} signature context l =
  listDepFoldFlip {f} {lp} signature l context

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
  listEliminator {lp=(f . ListForAll lp)}
    (ListEliminatorArgs
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
DecListForAll {f} {lp} dec =
  listEliminator
    {lp=(\l => f (Dec (ListForAll lp l)))}
    (ListEliminatorArgs
      (pure (Yes (|:|)))
      (\a, _, decList => [| ListForAllConsDec {lp} (dec a) decList |] ))

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
DecListExists {f} {lp} dec =
  listEliminator
    {lp=(\l => f (Dec (ListExists lp l)))}
    (ListEliminatorArgs
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
  ListEliminatorSig (f . (ListForAll ap))
ListForAllFoldSigToDepContextFreeFoldSig signature =
  ListEliminatorArgs (pure (|:|)) (consElim signature)

public export
listForAllFold : {f : Type -> Type} -> Applicative f => {atom : Type} ->
  {ap : atom -> Type} ->
  (signature : ListForAllFoldSig {f} ap) ->
  (l : List atom) -> f (ListForAll ap l)
listForAllFold {atom} signature =
  listEliminator (ListForAllFoldSigToDepContextFreeFoldSig signature)

public export
record ListMetaFoldSig {f : Type -> Type}
  {atom : Type} {contextType : Type}
  {lp : (context : contextType) -> List atom -> Type}
  (signature : ListDepFoldSig f lp)
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
            (listDepFoldFlip {f} {lp} signature l calledContext))) ->
      (metaContextUponEntry : metaContextType) ->
      (metaContextType,
       (contextUponEntry : contextType) ->
        ldp metaContextUponEntry contextUponEntry (a :: l)
        (consElim signature a l
          (listDepFoldFlip {f} {lp} signature l) contextUponEntry))

public export
listMetaFoldArgs : {f : Type -> Type} ->
  {atom : Type} -> {contextType : Type} ->
  {lp :
    (context : contextType) ->
    List atom ->
    Type} ->
  {signature : ListDepFoldSig f lp} ->
  {metaContextType : Type} ->
  {ldp :
    (metaContext : metaContextType) ->
    (context : contextType) ->
    (l : List atom) ->
    f (contextType, lp context l) ->
    Type} ->
  (metaSig : ListMetaFoldSig {f} {lp} signature ldp) ->
  ListDepFoldSig Prelude.Basics.id {contextType=metaContextType}
    (\metaContext, l =>
      (context : contextType) ->
        ldp metaContext context l
          (listDepFold {f} {lp} signature context l))
listMetaFoldArgs {f} metaSig =
  (ListEliminatorArgs (metaNilElim metaSig) (metaConsElim metaSig))

public export
listMetaFold : {f : Type -> Type} ->
  {atom : Type} -> {contextType : Type} ->
  {lp :
    (context : contextType) ->
    List atom ->
    Type} ->
  {signature : ListDepFoldSig f lp} ->
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
     ldp metaContext context l (listDepFold {f} {lp} signature context l))
listMetaFold {f} {contextType} {signature} {metaContextType} {ldp} metaSig =
  listDepFold {f=Prelude.Basics.id} {contextType=metaContextType}
    {lp=(\metaContext, l =>
      (context : contextType) ->
      ldp metaContext context l (listDepFold {f} {lp} signature context l))}
    (listMetaFoldArgs {f} metaSig)
