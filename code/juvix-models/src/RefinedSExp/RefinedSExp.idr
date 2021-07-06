module RefinedSExp.RefinedSExp

import public RefinedSExp.InductiveSExp
import public Library.Decidability

%default total

public export
SDecisionP : {atom : Type} -> (predicate : SPredicate atom) -> Type
SDecisionP predicate = (x : SExp atom) -> Dec (predicate x)

public export
SLDecisionP : {atom : Type} -> (predicate : SLPredicate atom) -> Type
SLDecisionP predicate = (l : SList atom) -> Dec (predicate l)

prefix 11 $#
public export
($#) : {atom : Type} -> (predicate : SPredicate atom) -> Type
($#) = SDecisionP

prefix 11 $:#
public export
($:#) : {atom : Type} -> (predicate : SLPredicate atom) -> Type
($:#) = SLDecisionP

public export
SatisfiesSPred : {atom : Type} -> {predicate : SPredicate atom} ->
  (decide : $# predicate) -> SExp atom -> Type
SatisfiesSPred decide x = IsYes (decide x)

prefix 11 $&
public export
($&) : {atom : Type} -> {predicate : SPredicate atom} ->
  (decide : $# predicate) -> SExp atom -> Type
($&) = SatisfiesSPred

public export
SatisfiesSLPred : {atom : Type} -> {predicate : SLPredicate atom} ->
  (decide : $:# predicate) -> SList atom -> Type
SatisfiesSLPred decide l = IsYes (decide l)

prefix 11 $:&
public export
($:&) : {atom : Type} -> {predicate : SLPredicate atom} ->
  (decide : $:# predicate) -> SList atom -> Type
($:&) = SatisfiesSLPred

prefix 11 $~
public export
($~) : {atom : Type} -> {predicate : SPredicate atom} ->
  (decide : $# predicate) -> Type
($~) decide = DPair (SExp atom) (SatisfiesSPred decide)

prefix 11 $:~
public export
($:~) : {atom : Type} -> {predicate : SLPredicate atom} ->
  (decide : $:# predicate) -> Type
($:~) decide = DPair (SList atom) (SatisfiesSLPred decide)

public export
record TypecheckPredicate (atom : Type) where
  constructor MkTypecheckPredicate
  SuccessType : SPredicate atom
  FailureType : SPredicate atom

public export
data TypecheckResult : {atom : Type} -> (predicate : TypecheckPredicate atom) ->
    SExp atom -> Type where
  TypecheckSuccess : {predicate : TypecheckPredicate atom} -> {x : SExp atom} ->
    SuccessType predicate x -> TypecheckResult predicate x
  TypecheckFailure : {predicate : TypecheckPredicate atom} -> {x : SExp atom} ->
    FailureType predicate x -> TypecheckResult predicate x

export
TypecheckSuccessInjective : {atom : Type} ->
  {predicate : TypecheckPredicate atom} ->
  {x : SExp atom} -> {result, result' : SuccessType predicate x} ->
  TypecheckSuccess {x} {predicate} result =
    TypecheckSuccess {x} {predicate} result' ->
  result = result'
TypecheckSuccessInjective Refl = Refl

export
TypecheckFailureInjective : {atom : Type} ->
  {predicate : TypecheckPredicate atom} ->
  {x : SExp atom} -> {result, result' : FailureType predicate x} ->
  TypecheckFailure {x} {predicate} result =
    TypecheckFailure {x} {predicate} result' ->
  result = result'
TypecheckFailureInjective Refl = Refl

public export
data IsSuccess : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
    {x : SExp atom} -> TypecheckResult predicate x -> Type where
  Successful : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
    {x : SExp atom} -> (result : SuccessType predicate x) ->
    IsSuccess {x} {predicate} (TypecheckSuccess result)

export
IsSuccessExtract : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
  {x : SExp atom} -> {result : TypecheckResult predicate x} ->
  IsSuccess result -> SuccessType predicate x
IsSuccessExtract (Successful success) = success

export
IsSuccessExtractElim : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
  {x : SExp atom} -> {result : TypecheckResult predicate x} ->
  (succeeded : IsSuccess result) ->
  result = TypecheckSuccess (IsSuccessExtract succeeded)
IsSuccessExtractElim (Successful _) = Refl

export
SuccessIsSuccessful : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
  {x : SExp atom} -> {success : SuccessType predicate x} ->
  {result : TypecheckResult predicate x} ->
  result = TypecheckSuccess {x} {predicate} success ->
  IsSuccess {x} {predicate} result
SuccessIsSuccessful {x} {success} Refl = Successful success

public export
isSuccess : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
  {x : SExp atom} -> (result : TypecheckResult predicate x) ->
  Dec (IsSuccess result)
isSuccess (TypecheckSuccess success) = Yes (Successful success)
isSuccess (TypecheckFailure _) =
  No (\success => case success of Successful _ impossible)

public export
data IsFailure : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
    {x : SExp atom} -> TypecheckResult predicate x -> Type where
  Failed : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
    {x : SExp atom} -> (result : FailureType predicate x) ->
    IsFailure {x} {predicate} (TypecheckFailure result)

export
IsFailureExtract : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
  {x : SExp atom} -> {result : TypecheckResult predicate x} ->
  IsFailure result -> FailureType predicate x
IsFailureExtract (Failed failure) = failure

export
IsFailureExtractElim : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
  {x : SExp atom} -> {result : TypecheckResult predicate x} ->
  (succeeded : IsFailure result) ->
  result = TypecheckFailure (IsFailureExtract succeeded)
IsFailureExtractElim (Failed _) = Refl

public export
isFailure : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
  {x : SExp atom} -> (result : TypecheckResult predicate x) ->
  Dec (IsFailure result)
isFailure (TypecheckSuccess _) =
  No (\failed => case failed of Failed _ impossible)
isFailure (TypecheckFailure failed) = Yes (Failed failed)

public export
record InductiveTypecheck {atom : Type}
    (predicate : TypecheckPredicate atom) where
  constructor MkInductiveTypecheck
  typecheckOne : (a : atom) -> (l : SList atom) ->
    SLForAll (SuccessType predicate) l -> TypecheckResult predicate (a $: l)
  AllFailures : Type
  firstFailure : (x : SExp atom) -> FailureType predicate x -> AllFailures
  laterFailure : (x : SExp atom) -> FailureType predicate x -> AllFailures ->
    AllFailures

public export
data TypechecksAs : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
    InductiveTypecheck predicate ->
    (x : SExp atom) -> SuccessType predicate x -> Type where
  AllSubtermsTypecheckAs : {atom : Type} ->
    {predicate : TypecheckPredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {a : atom} -> {l : SList atom} ->
    (subtermsCheck : SLForAll (SDepPredPair (TypechecksAs check)) l) ->
    (checkedType : SuccessType predicate (a $: l)) ->
    (termChecks :
      typecheckOne check a l (SLPairsFst subtermsCheck) =
        TypecheckSuccess {predicate} checkedType) ->
    TypechecksAs check (a $: l) checkedType

public export
TypechecksAsSubterms : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {a : atom} -> {l : SList atom} ->
    {checkedType : SuccessType predicate (a $: l)} ->
    TypechecksAs check (a $: l) checkedType ->
    SLForAll (SDepPredPair (TypechecksAs check)) l
TypechecksAsSubterms (AllSubtermsTypecheckAs subtermsCheck _ _) = subtermsCheck

public export
Typechecks : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
  InductiveTypecheck predicate -> (x : SExp atom) -> Type
Typechecks check x = DPair (SuccessType predicate x) (TypechecksAs check x)

mutual
  export
  CheckedTypesUnique : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {x : SExp atom} -> {type, type' : SuccessType predicate x} ->
    (typechecksAs : TypechecksAs check x type) ->
    (typechecksAs' : TypechecksAs check x type') ->
    type = type'
  CheckedTypesUnique {check}
    (AllSubtermsTypecheckAs subtermsCheck checkedType termChecks)
    (AllSubtermsTypecheckAs subtermsCheck' checkedType' termChecks') =
      case ListTypechecksUnique {check} subtermsCheck subtermsCheck' of
        Refl => TypecheckSuccessInjective (trans (sym termChecks) termChecks')

  export
  TypechecksAsUnique :
    {atom : Type} -> {predicate : TypecheckPredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {a : atom} -> {l : SList atom} ->
    {type, type' : SuccessType predicate (a $: l)} ->
    (typechecksAs : TypechecksAs check (a $: l) type) ->
    (typechecksAs' : TypechecksAs check (a $: l) type) ->
    typechecksAs = typechecksAs'
  TypechecksAsUnique {check}
    (AllSubtermsTypecheckAs subtermsCheck checkedType termChecks)
    (AllSubtermsTypecheckAs subtermsCheck' checkedType termChecks') =
      case SLForAllUnique subtermsCheck subtermsCheck'
        (\x, typechecks, typechecks' => case x of
          (a $: l) => TypechecksUnique typechecks typechecks') of
        Refl => case uip termChecks termChecks' of Refl => Refl

  export
  HeterogeneousTypechecksAsUnique :
    {atom : Type} -> {predicate : TypecheckPredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {a : atom} -> {l : SList atom} ->
    {type, type' : SuccessType predicate (a $: l)} ->
    (typechecksAs : TypechecksAs check (a $: l) type) ->
    (typechecksAs' : TypechecksAs check (a $: l) type') ->
    typechecksAs = typechecksAs'
  HeterogeneousTypechecksAsUnique {type} {type'} typechecksAs typechecksAs' =
    case CheckedTypesUnique typechecksAs typechecksAs' of
      Refl => TypechecksAsUnique {type} {type'=type} typechecksAs typechecksAs'

  export
  TypechecksUnique : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {a : atom} -> {l : SList atom} ->
    (typechecks, typechecks' : Typechecks check (a $: l)) ->
    typechecks = typechecks'
  TypechecksUnique (type ** typechecksAs) (type' ** typechecksAs') =
    case CheckedTypesUnique typechecksAs typechecksAs' of
      Refl =>
        cong
          (MkDPair type)
          (TypechecksAsUnique {type} {type'=type} typechecksAs typechecksAs')

  export
  ListTypechecksUnique : {atom : Type} ->
    {predicate : TypecheckPredicate atom} ->
    {check : InductiveTypecheck predicate} -> {l : SList atom} ->
    (typecheckList, typecheckList' : SLForAll (Typechecks check) l) ->
    typecheckList = typecheckList'
  ListTypechecksUnique SLForAllEmpty SLForAllEmpty = Refl
  ListTypechecksUnique SLForAllEmpty (SLForAllCons _ _) impossible
  ListTypechecksUnique (SLForAllCons _ _) SLForAllEmpty impossible
  ListTypechecksUnique
    (SLForAllCons {x=(a $: l)} head tail)
    (SLForAllCons head' tail') =
      case TypechecksUnique {check} head head' of
        Refl =>
          replace
            {p=(\tail'' => SLForAllCons head tail = SLForAllCons head tail'')}
            (ListTypechecksUnique tail tail')
            Refl

public export
CheckResult : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
  (check : InductiveTypecheck predicate) -> (x : SExp atom) -> Type
CheckResult check = Dec . (Typechecks check)

public export
ListCheckResult : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
  (check : InductiveTypecheck predicate) -> (l : SList atom) -> Type
ListCheckResult check = Dec . (SLForAll (Typechecks check))

public export
SLForAllConsDec : {atom : Type} -> {sp : SPredicate atom} ->
  {x : SExp atom} -> {l : SList atom} ->
  Dec (sp x) -> Dec (SLForAll sp l) -> Dec (SLForAll sp (x $+ l))
SLForAllConsDec (Yes spx) (Yes forAll) = Yes (SLForAllCons spx forAll)
SLForAllConsDec (No spxFails) _ =
  No (\forAllCons => case forAllCons of
    SLForAllEmpty impossible
    SLForAllCons spx _ => spxFails spx)
SLForAllConsDec _ (No forAllFails) =
  No (\forAllCons => case forAllCons of
    SLForAllEmpty impossible
    SLForAllCons _ forAll => forAllFails forAll)

public export
typecheck : {atom : Type} -> {predicate : TypecheckPredicate atom} ->
  (check : InductiveTypecheck predicate) ->
  ((x : SExp atom) -> CheckResult check x,
   (l : SList atom) -> ListCheckResult check l)
typecheck check =
  sInd {lp=(ListCheckResult check)}
    (\a, l, lCheck => case lCheck of
      Yes lChecks =>
        case isSuccess
          (typecheckOne check a l (SLPairsFst lChecks)) of
            Yes termChecks =>
              Yes (IsSuccessExtract termChecks **
                   AllSubtermsTypecheckAs
                     lChecks
                     (IsSuccessExtract termChecks)
                     (IsSuccessExtractElim termChecks))
            No termFails =>
              No (\termChecks => case termChecks of
                (_ ** typechecks) => case typechecks of
                  AllSubtermsTypecheckAs subtermsCheck checkedType termChecks =>
                    termFails
                      (replace
                        {p=(\subtermsCheck' =>
                          IsSuccess (typecheckOne check a l
                            (SLPairsFst
                              {sdp=(TypechecksAs check)} subtermsCheck')))}
                        (ListTypechecksUnique subtermsCheck lChecks)
                         (SuccessIsSuccessful termChecks)))
      No lFails => No (\typedTerm => case typedTerm of
        (_ ** typechecks) => case typechecks of
          AllSubtermsTypecheckAs subtermsCheck _ _ =>
            lFails subtermsCheck))
    (Yes SLForAllEmpty)
    (\_, _ => SLForAllConsDec)

-- Refined S-expression.
public export
RExp : {atom : Type} -> {predicate : SPredicate atom} ->
  (decide : $# predicate) -> Type
RExp decide = DPair (SExp atom) ($& decide)

-- Refined S-list.
public export
RList : {atom : Type} -> {predicate : SLPredicate atom} ->
  (decide : $:# predicate) -> Type
RList decide = DPair (SList atom) ($:& decide)

RExpProofInsensitive : {atom : Type} -> {predicate : SPredicate atom} ->
  {decide : $# predicate} -> {rx, rx' : RExp decide} -> (fst rx = fst rx') ->
  rx = rx'
RExpProofInsensitive {decide} = YesDPairInjective {dec=decide}

RListProofInsensitive : {atom : Type} -> {predicate : SLPredicate atom} ->
  {decide : $:# predicate} -> {rl, rl' : RList decide} -> (fst rl = fst rl') ->
  rl = rl'
RListProofInsensitive {decide} = YesDPairInjective {dec=decide}
