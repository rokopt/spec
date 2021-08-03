module RefinedSExp.New.SExp

import public RefinedSExp.New.List
import Library.FunctionsAndRelations
import Library.Decidability
import public Category.Category

%default total

mutual
  prefix 11 $^
  prefix 11 $|
  public export
  data SExp : (atom : Type) -> Type where
    ($^) : atom -> SExp atom
    ($|) : SList atom -> SExp atom

  public export
  SList : (atom : Type) -> Type
  SList = List . SExp

public export
SExpPred : Type -> Type
SExpPred atom = !- (SExp atom)

public export
SListPred : Type -> Type
SListPred atom = !- (SList atom)

public export
SExpPreds : Type -> Type
SExpPreds atom = (SExpPred atom, SListPred atom)

public export
sexpPredsCompose : {atom : Type} ->
  (Type -> Type) -> SExpPreds atom -> SExpPreds atom
sexpPredsCompose f sps = (f . fst sps, f . snd sps)

public export
SPredsExp : {atom : Type} -> SExpPreds atom -> SExpPred atom
SPredsExp = fst

public export
SPredsList : {atom : Type} -> SExpPreds atom -> SListPred atom
SPredsList = snd

public export
SExpPi : {atom : Type} -> SExpPred atom -> Type
SExpPi sp = SExp atom ~> sp

public export
SListPi : {atom : Type} -> SListPred atom -> Type
SListPi sp = SList atom ~> sp

public export
SPisExp : {atom : Type} -> (sps : SExpPreds atom) -> Type
SPisExp = SExpPi . SPredsExp

public export
SPisList : {atom : Type} -> (sps : SExpPreds atom) -> Type
SPisList = SListPi . SPredsList

public export
SPredPis : {atom : Type} -> SExpPreds atom -> Type
SPredPis sps = (SPisExp sps, SPisList sps)

public export
record SExpEliminatorSig
  {atom : Type} (sps : SExpPreds atom)
  where
    constructor SExpEliminatorArgs
    atomElim : (a : atom) ->
      SPredsExp sps ($^ a)
    listElim : (l : SList atom) ->
      SPredsList sps l -> SPredsExp sps ($| l)
    nilElim :
      SPredsList sps []
    consElim :
      (x : SExp atom) -> (l : SList atom) ->
      SPredsExp sps x -> SPredsList sps l -> SPredsList sps (x :: l)

mutual
  public export
  sexpEliminator :
    {0 atom : Type} -> {0 sps : SExpPreds atom} ->
    (signature : SExpEliminatorSig sps) ->
    SPisExp sps
  sexpEliminator signature ($^ a) =
    atomElim signature a
  sexpEliminator signature ($| l) =
    listElim signature l (slistEliminator signature l)

  public export
  slistEliminator :
    {0 atom : Type} -> {0 sps : SExpPreds atom} ->
    (signature : SExpEliminatorSig sps) ->
    SPisList sps
  slistEliminator signature [] =
    nilElim signature
  slistEliminator signature (x :: l) =
    consElim signature x l
      (sexpEliminator signature x) (slistEliminator signature l)

public export
sexpEliminators :
  {0 atom : Type} -> {0 sps : SExpPreds atom} ->
  (signature : SExpEliminatorSig sps) ->
  SPredPis sps
sexpEliminators signature =
  (sexpEliminator signature, slistEliminator signature)

public export
SExpPredsToListPred :
  {atom : Type} -> (sps : SExpPreds atom) -> ListPred (SExp atom)
SExpPredsToListPred sps [] = SPredsList sps []
SExpPredsToListPred sps (x :: l) = SPredsExp sps x -> SPredsList sps (x :: l)

public export
SListPiToListPi :
  {atom : Type} ->
  {sps : SExpPreds atom} ->
  (signature : SExpEliminatorSig sps) ->
  (l : SList atom) ->
  SExpPredsToListPred sps l ->
  SPredsList sps l
SListPiToListPi signature [] pred = pred
SListPiToListPi signature (x :: l) pred = pred (sexpEliminator signature x)

public export
SExpSigToListSig :
  {atom : Type} -> {sps : SExpPreds atom} ->
  SExpEliminatorSig sps ->
  ListEliminatorSig (SExpPredsToListPred sps)
SExpSigToListSig signature =
  ListEliminatorArgs
    (nilElim signature)
    (\x, l, pred, spx =>
      consElim signature x l spx (SListPiToListPi signature l pred))

export
slistEliminatorMatchesListFold :
  {atom : Type} ->
  {sps : SExpPreds atom} ->
  (signature : SExpEliminatorSig sps) ->
  (l : SList atom) ->
  slistEliminator signature l =
    SListPiToListPi {sps} signature l
      (listEliminator (SExpSigToListSig signature) l)
slistEliminatorMatchesListFold signature [] =
  Refl
slistEliminatorMatchesListFold signature (x :: l) =
  applyEq {f=(consElim signature x l (sexpEliminator signature x))} Refl
    (slistEliminatorMatchesListFold signature l)

public export
SExpMetaPred : {atom : Type} -> SExpPred atom -> Type
SExpMetaPred {atom} sp = (x : SExp atom) -> sp x -> Type

public export
SListMetaPred : {atom : Type} -> SListPred atom -> Type
SListMetaPred {atom} lp = (l : SList atom) -> lp l -> Type

public export
SExpPredsMetaExp : {atom : Type} -> SExpPreds atom -> Type
SExpPredsMetaExp = SExpMetaPred . SPredsExp

public export
SExpPredsMetaList : {atom : Type} -> SExpPreds atom -> Type
SExpPredsMetaList = SListMetaPred . SPredsList

public export
SExpMetaPreds : {atom : Type} -> SExpPreds atom -> Type
SExpMetaPreds sps = (SExpPredsMetaExp sps, SExpPredsMetaList sps)

public export
SExpMetaPredToPred : {atom : Type} -> {sp : SExpPred atom} ->
  SExpMetaPred sp -> SExpPred atom
SExpMetaPredToPred {sp} smp = \l => sp l ~> smp l

public export
SListMetaPredToPred : {atom : Type} -> {lp : SListPred atom} ->
  SListMetaPred lp -> SListPred atom
SListMetaPredToPred {lp} lmp = \l => lp l ~> lmp l

public export
SExpMetaPi : {atom : Type} -> {sp : SExpPred atom} ->
  SExpMetaPred sp -> Type
SExpMetaPi {atom} {sp} smp = (x : SExp atom) -> (spx : sp x) -> smp x spx

public export
SListMetaPi : {atom : Type} -> {lp : SListPred atom} ->
  SListMetaPred lp -> Type
SListMetaPi {atom} {lp} lmp = (l : SList atom) -> (lpl : lp l) -> lmp l lpl

public export
SExpSigToMetaPred : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpEliminatorSig sps -> SExpPredsMetaExp sps -> SExpPred atom
SExpSigToMetaPred signature smp = \x => smp x (sexpEliminator signature x)

public export
SListSigToMetaPred : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpEliminatorSig sps -> SExpPredsMetaList sps -> SListPred atom
SListSigToMetaPred signature lmp = \l => lmp l (slistEliminator signature l)

public export
SExpMetaPredsExp : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpMetaPreds sps -> SExpPredsMetaExp sps
SExpMetaPredsExp = fst

public export
SExpMetaPredsList : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpMetaPreds sps -> SExpPredsMetaList sps
SExpMetaPredsList = snd

public export
SExpSigToMetaPredExp : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpEliminatorSig sps -> SExpMetaPreds sps -> SExpPred atom
SExpSigToMetaPredExp signature smps =
  SExpSigToMetaPred signature (SExpMetaPredsExp smps)

public export
SExpSigToMetaPredList : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpEliminatorSig sps -> SExpMetaPreds sps -> SListPred atom
SExpSigToMetaPredList signature smps =
  SListSigToMetaPred signature (SExpMetaPredsList smps)

public export
SExpSigToMetaPreds : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpEliminatorSig sps -> SExpMetaPreds sps -> SExpPreds atom
SExpSigToMetaPreds signature smps =
  (SExpSigToMetaPredExp signature smps, SExpSigToMetaPredList signature smps)

public export
SExpSigPi : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpEliminatorSig sps -> SExpMetaPred (SPredsExp sps) -> Type
SExpSigPi signature smp = SExpPi (SExpSigToMetaPred signature smp)

public export
SListSigPi : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpEliminatorSig sps -> SListMetaPred (SPredsList sps) -> Type
SListSigPi signature lmp = SListPi (SListSigToMetaPred signature lmp)

public export
SExpSigEliminatorSig : {atom : Type} -> {sps : SExpPreds atom} ->
  SExpEliminatorSig sps -> SExpMetaPreds sps -> Type
SExpSigEliminatorSig signature smps =
  SExpEliminatorSig (SExpSigToMetaPreds signature smps)

public export
record SExpMetaEliminatorSig
  {0 atom : Type} {0 sps : SExpPreds atom}
  (signature : SExpEliminatorSig sps)
  (smps : SExpMetaPreds sps)
  where
    constructor SExpMetaEliminatorArgs
    metaAtomElim : (a : atom) ->
      SExpMetaPredsExp {sps} smps ($^ a) (atomElim signature a)
    metaListElim : (l : SList atom) ->
      SExpMetaPredsList {sps} smps l (slistEliminator signature l) ->
      SExpMetaPredsExp {sps} smps
        ($| l) (listElim signature l (slistEliminator signature l))
    metaNilElim :
      SExpMetaPredsList {sps} smps [] (nilElim signature)
    metaConsElim : (x : SExp atom) -> (l : SList atom) ->
      SExpMetaPredsExp {sps} smps x (sexpEliminator signature x) ->
      SExpMetaPredsList {sps} smps l (slistEliminator signature l) ->
      SExpMetaPredsList {sps} smps (x :: l)
        (consElim signature x l
          (sexpEliminator signature x)
          (slistEliminator signature l))

public export
SExpMetaEliminatorSigToEliminatorSig :
  {0 atom : Type} -> {0 sps : SExpPreds atom} ->
  {signature : SExpEliminatorSig sps} ->
  {0 smps : SExpMetaPreds sps} ->
  SExpMetaEliminatorSig signature smps ->
  SExpSigEliminatorSig signature smps
SExpMetaEliminatorSigToEliminatorSig metaSig =
  SExpEliminatorArgs
    (metaAtomElim metaSig)
    (metaListElim metaSig)
    (metaNilElim metaSig)
    (metaConsElim metaSig)

public export
SExpSignatureComposeSig :
  {f : Type -> Type} ->
  {da : DependentApplicative f} ->
  {atom : Type} ->
  {sps : SExpPreds atom} ->
  (signature : f (SExpEliminatorSig sps)) ->
  SExpEliminatorSig (sexpPredsCompose f sps)
SExpSignatureComposeSig {da} signature =
  SExpEliminatorArgs {sps=(sexpPredsCompose f sps)}
    (\a => dpure da (afmap {da} atomElim signature) a)
    (\l, flpl => afapply da (dpure da (afmap {da} listElim signature) l) flpl)
    (afmap {da} nilElim signature)
    (\x, l, fspx, flpl =>
      afapply da (afapply da
        (dpure da (dpure da (afmap {da} consElim signature) x) l) fspx) flpl)

public export
sexpSignatureCompose :
  {f : Type -> Type} ->
  {da : DependentApplicative f} ->
  {atom : Type} ->
  {sps : SExpPreds atom} ->
  (signature : f (SExpEliminatorSig sps)) ->
  SPredPis (sexpPredsCompose f sps)
sexpSignatureCompose {da} = sexpEliminators . SExpSignatureComposeSig {da}

public export
sexpParameterizedEliminators :
  {0 atom : Type} ->
  {0 sps : List (SExpPreds atom) -> SExpPreds atom} ->
  (parameterizedSignature : List (SExpPreds atom) ~> SExpEliminatorSig . sps) ->
  List (SExpPreds atom) ~> SPredPis . sps
sexpParameterizedEliminators parameterizedSignature params =
  sexpEliminators (parameterizedSignature params)

public export
SExpConstPred : {atom : Type} -> Type -> SExpPred atom
SExpConstPred type _ = type

public export
SListConstPred : {atom : Type} -> Type -> SListPred atom
SListConstPred type _ = type

public export
SExpConstPreds : {atom : Type} -> Type -> Type -> SExpPreds atom
SExpConstPreds sp lp = (SExpConstPred sp, SListConstPred lp)

public export
sexpConstEliminators :
  {0 atom : Type} -> {0 sp : Type} -> {0 lp : Type} ->
  (signature : SExpEliminatorSig {atom} (SExpConstPreds sp lp)) ->
  (SExp atom -> sp, SList atom -> lp)
sexpConstEliminators = sexpEliminators

public export
sexpMaps : {0 a, b : Type} -> (a -> b) -> (SExp a -> SExp b, SList a -> SList b)
sexpMaps f =
  sexpConstEliminators
    (SExpEliminatorArgs
      (($^) . f)
      (\_ => ($|))
      []
      (\_, _ => (::)))

public export
sexpMap : {0 a, b : Type} -> (a -> b) -> SExp a -> SExp b
sexpMap = fst . sexpMaps

public export
slistMap : {0 a, b : Type} -> (a -> b) -> SList a -> SList b
slistMap = snd . sexpMaps

Functor SExp where
  map = sexpMap

{- XXX dependent applicative instance -}
