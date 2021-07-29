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
  {atom : Type} -> {lp : !- (List atom)} ->
  (signature : ListEliminatorSig lp) ->
  List atom ~> lp
listEliminator signature [] =
  nilElim signature
listEliminator signature (a :: l) =
  consElim signature a l (listEliminator signature l)

public export
listParameterizedEliminator :
  {atom : Type} -> {lp : (!- (List atom)) -> (!- (List atom))} ->
  (signature : ((!- (List atom)) ~> (ListEliminatorSig . lp))) ->
  (parameter : !- (List atom)) -> (List atom ~> lp parameter)
listParameterizedEliminator {lp} signature parameter x =
  listEliminator
    {lp=(\l => ((parameter : (!- (List atom))) -> lp parameter l))}
    (ListEliminatorArgs
      (\parameter => (nilElim (signature parameter)))
      (\a, l, parameterizedPred, parameter =>
        consElim (signature parameter) a l (parameterizedPred parameter))
    ) x parameter

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
  {atom : Type} -> (ap : atom -> Type) -> List atom -> Type where
    (|:|) : {atom : Type} -> {ap : atom -> Type} ->
            ListForAll ap []
    (:::) : {atom : Type} -> {ap : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            ap a -> ListForAll ap l ->
            ListForAll ap (a :: l)

prefix 11 <::
prefix 11 >::
public export
data ListExists :
  {atom : Type} -> (ap : atom -> Type) -> List atom -> Type where
    (<::) : {atom : Type} -> {ap : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            ap a ->
            ListExists ap (a :: l)
    (>::) : {atom : Type} -> {ap : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            ListExists ap l ->
            ListExists ap (a :: l)

public export
ListForAllConstruct : {f : Type -> Type} -> Applicative f => {atom : Type} ->
  {ap : atom -> Type} ->
  (construct : (a : atom) -> f (ap a)) -> (l : List atom) ->
  f (ListForAll ap l)
ListForAllConstruct {f} {ap} construct =
  listEliminator {lp=(f . ListForAll ap)}
    (ListEliminatorArgs
      (pure (|:|))
      (\a, _, lpl => [| construct a ::: lpl |]))

infixr 7 :::
public export
ListForAllConsDec : {atom : Type} -> {ap : atom -> Type} ->
  {a : atom} -> {l : List atom} ->
  Dec (ap a) -> Dec (ListForAll ap l) ->
  Dec (ListForAll ap (a :: l))
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
  {ap : atom -> Type} ->
  (dec : (a : atom) -> f (Dec (ap a))) -> (l : List atom) ->
  f (Dec (ListForAll ap l))
DecListForAll {f} {ap} dec =
  listEliminator
    {lp=(\l => f (Dec (ListForAll ap l)))}
    (ListEliminatorArgs
      (pure (Yes (|:|)))
      (\a, _, decList => [| ListForAllConsDec {ap} (dec a) decList |] ))

public export
NoExistsNil : {atom : Type} -> {ap : atom -> Type} -> Not (ListExists ap [])
NoExistsNil ((<::) _) impossible
NoExistsNil ((>::) _) impossible

public export
NoExistsNeither : {atom : Type} -> {ap : atom -> Type} ->
  {a : atom} -> {l : List atom} ->
  Not (ap a) -> Not (ListExists ap l) ->
  Not (ListExists ap (a :: l))
NoExistsNeither noA _ ((<::) existsA) = noA existsA
NoExistsNeither _ noList ((>::) existsList) = noList existsList

public export
ListExistsEitherDec : {atom : Type} -> {ap : atom -> Type} ->
  {a : atom} -> {l : List atom} ->
  Dec (ap a) -> Dec (ListExists ap l) ->
  Dec (ListExists ap (a :: l))
ListExistsEitherDec decHead decTail =
  case (decHead, decTail) of
    (Yes yesA, _) => Yes (<:: yesA)
    (_, Yes existsList) => Yes (>:: existsList)
    (No noA, No noList) => No (NoExistsNeither noA noList)

public export
DecListExists : {f : Type -> Type} -> Applicative f => {atom : Type} ->
  {ap : atom -> Type} ->
  (dec : (a : atom) -> f (Dec (ap a))) -> (l : List atom) ->
  f (Dec (ListExists ap l))
DecListExists {f} {ap} dec =
  listEliminator
    {lp=(\l => f (Dec (ListExists ap l)))}
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
      f (ap a)

public export
ListForAllFoldSigToEliminatorSig :
  {f : Type -> Type} -> Applicative f =>
  {atom : Type} -> {ap : atom -> Type} ->
  ListForAllFoldSig {f} {atom} ap ->
  ListEliminatorSig (f . (ListForAll ap))
ListForAllFoldSigToEliminatorSig {f} {atom} {ap} signature =
  ListEliminatorArgs {lp=(f . ListForAll ap)}
    (pure {f} (|:|))
    (\a, l, forAll => (map (:::) (consElim signature a l forAll)) <*> forAll)

public export
listForAllFold : {f : Type -> Type} -> Applicative f => {atom : Type} ->
  {ap : atom -> Type} ->
  (signature : ListForAllFoldSig {f} ap) ->
  List atom ~> f . (ListForAll ap)
listForAllFold {atom} signature =
  listEliminator (ListForAllFoldSigToEliminatorSig signature)

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
