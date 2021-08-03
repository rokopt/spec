module RefinedSExp.New.List

import Library.FunctionsAndRelations
import public Data.List

%default total

public export
ListPred : Type -> Type
ListPred atom = !- (List atom)

public export
ListPi : {atom : Type} -> ListPred atom -> Type
ListPi {atom} lp = List atom ~> lp

public export
record ListEliminatorSig {atom : Type} (lp : ListPred atom) where
  constructor ListEliminatorArgs
  nilElim : lp []
  consElim : (a : atom) -> (l : List atom) -> lp l -> lp (a :: l)

public export
listEliminator :
  {atom : Type} -> {lp : ListPred atom} ->
  (signature : ListEliminatorSig lp) ->
  ListPi lp
listEliminator signature [] =
  nilElim signature
listEliminator signature (a :: l) =
  consElim signature a l (listEliminator signature l)

public export
ListMetaPred : {atom : Type} -> ListPred atom -> Type
ListMetaPred {atom} lp = (l : List atom) -> lp l -> Type

public export
ListMetaPredToPred : {atom : Type} -> {lp : ListPred atom} ->
  ListMetaPred lp -> ListPred atom
ListMetaPredToPred {lp} lmp = \l => lp l ~> lmp l

public export
ListMetaPi : {atom : Type} -> {lp : ListPred atom} ->
  ListMetaPred lp -> Type
ListMetaPi {atom} {lp} lmp = (l : List atom) -> (lpl : lp l) -> lmp l lpl

public export
ListSigToMetaPred : {atom : Type} -> {lp : ListPred atom} ->
  ListEliminatorSig lp -> ListMetaPred lp -> ListPred atom
ListSigToMetaPred signature lmp = \l => lmp l (listEliminator signature l)

public export
ListSigPi : {atom : Type} -> {lp : ListPred atom} ->
  ListEliminatorSig lp -> ListMetaPred lp -> Type
ListSigPi signature lmp = ListPi (ListSigToMetaPred signature lmp)

public export
ListSigEliminatorSig : {atom : Type} -> {lp : ListPred atom} ->
  ListEliminatorSig lp -> ListMetaPred lp -> Type
ListSigEliminatorSig signature lmp =
  ListEliminatorSig (ListSigToMetaPred signature lmp)

public export
record ListMetaEliminatorSig
  {atom : Type} {lp : ListPred atom}
  (signature : ListEliminatorSig lp)
  (lmp : ListMetaPred lp)
  where
    constructor ListMetaEliminatorArgs
    metaNilElim : lmp [] (nilElim signature)
    metaConsElim :
      (a : atom) -> (l : List atom) ->
      (lmpl : lmp l (listEliminator signature l)) ->
      lmp (a :: l) (consElim signature a l (listEliminator signature l))

public export
ListMetaEliminatorSigToEliminatorSig :
  {atom : Type} -> {lp : ListPred atom} ->
  {signature : ListEliminatorSig lp} ->
  {lmp : ListMetaPred lp} ->
  ListMetaEliminatorSig signature lmp ->
  ListSigEliminatorSig signature lmp
ListMetaEliminatorSigToEliminatorSig metaSig =
  ListEliminatorArgs (metaNilElim metaSig) (metaConsElim metaSig)

public export
listMetaEliminator :
  {atom : Type} -> {lp : ListPred atom} ->
  {signature : ListEliminatorSig lp} ->
  {lmp : ListMetaPred lp} ->
  ListMetaEliminatorSig signature lmp ->
  ListSigPi signature lmp
listMetaEliminator = listEliminator . ListMetaEliminatorSigToEliminatorSig
