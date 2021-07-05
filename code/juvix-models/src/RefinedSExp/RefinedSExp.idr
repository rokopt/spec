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
InductiveTypecheck : {atom : Type} -> (candidateType : SPredicate atom) -> Type
InductiveTypecheck {atom} candidateType =
  (a : atom) -> (l : SList atom) ->
    SLForAll candidateType l -> Maybe (candidateType (a $: l))

public export
data TypechecksAs : {atom : Type} -> {candidateType : SPredicate atom} ->
    InductiveTypecheck candidateType ->
    (x : SExp atom) -> candidateType x -> Type where
  AllSubtermsTypecheckAs : {atom : Type} -> {candidateType : SPredicate atom} ->
    {check : InductiveTypecheck candidateType} ->
    {a : atom} -> {l : SList atom} ->
    (subtermsCheck : SLForAll (SDepPredPair (TypechecksAs check)) l) ->
    (checkedType : candidateType (a $: l)) ->
    (termChecks : check a l (SLPairsFst subtermsCheck) = Just checkedType) ->
    TypechecksAs check (a $: l) checkedType

public export
TypechecksAsSubterms : {atom : Type} -> {candidateType : SPredicate atom} ->
    {check : InductiveTypecheck candidateType} ->
    {a : atom} -> {l : SList atom} -> {checkedType : candidateType (a $: l)} ->
    TypechecksAs check (a $: l) checkedType ->
    SLForAll (SDepPredPair (TypechecksAs check)) l
TypechecksAsSubterms (AllSubtermsTypecheckAs subtermsCheck _ _) = subtermsCheck

public export
Typechecks : {atom : Type} -> {candidateType : SPredicate atom} ->
  InductiveTypecheck candidateType -> (x : SExp atom) -> Type
Typechecks check x = DPair (candidateType x) (TypechecksAs check x)

mutual
  export
  CheckedTypesUnique : {atom : Type} -> {candidateType : SPredicate atom} ->
    {check : InductiveTypecheck candidateType} ->
    {x : SExp atom} -> {type, type' : candidateType x} ->
    (typechecksAs : TypechecksAs check x type) ->
    (typechecksAs' : TypechecksAs check x type') ->
    type = type'
  CheckedTypesUnique {check}
    (AllSubtermsTypecheckAs subtermsCheck checkedType termChecks)
    (AllSubtermsTypecheckAs subtermsCheck' checkedType' termChecks') =
      case ListTypechecksUnique {check} subtermsCheck subtermsCheck' of
        Refl => justInjective (trans (sym termChecks) termChecks')

  export
  TypechecksAsUnique :
    {atom : Type} -> {candidateType : SPredicate atom} ->
    {check : InductiveTypecheck candidateType} ->
    {a : atom} -> {l : SList atom} -> {type, type' : candidateType (a $: l)} ->
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
    {atom : Type} -> {candidateType : SPredicate atom} ->
    {check : InductiveTypecheck candidateType} ->
    {a : atom} -> {l : SList atom} -> {type, type' : candidateType (a $: l)} ->
    (typechecksAs : TypechecksAs check (a $: l) type) ->
    (typechecksAs' : TypechecksAs check (a $: l) type') ->
    typechecksAs = typechecksAs'
  HeterogeneousTypechecksAsUnique {type} {type'} typechecksAs typechecksAs' =
    case CheckedTypesUnique typechecksAs typechecksAs' of
      Refl => TypechecksAsUnique {type} {type'=type} typechecksAs typechecksAs'

  export
  TypechecksUnique : {atom : Type} -> {candidateType : SPredicate atom} ->
    {check : InductiveTypecheck candidateType} ->
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
  ListTypechecksUnique : {atom : Type} -> {candidateType : SPredicate atom} ->
    {check : InductiveTypecheck candidateType} -> {l : SList atom} ->
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
CheckResult : {atom : Type} -> {candidateType : SPredicate atom} ->
  (check : InductiveTypecheck candidateType) -> (x : SExp atom) -> Type
CheckResult check = Dec . (Typechecks check)

public export
ListCheckResult : {atom : Type} -> {candidateType : SPredicate atom} ->
  (check : InductiveTypecheck candidateType) -> (l : SList atom) -> Type
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
typecheck : {atom : Type} -> {candidateType : SPredicate atom} ->
  (check : InductiveTypecheck candidateType) ->
  ((x : SExp atom) -> CheckResult check x,
   (l : SList atom) -> ListCheckResult check l)
typecheck check =
  sInd {lp=(ListCheckResult check)}
    (\a, l, lCheck => case lCheck of
      Yes lChecks =>
        case isJustIsTrueDec
          (check a l (SLPairsFst {sdp=(TypechecksAs check)} lChecks)) of
            Yes termChecks =>
              Yes (isJustElim termChecks **
                   AllSubtermsTypecheckAs
                     lChecks
                     (isJustElim termChecks)
                     (isJustElimElim termChecks))
            No termFails =>
              No (\termChecks => case termChecks of
                (_ ** typechecks) => case typechecks of
                  AllSubtermsTypecheckAs subtermsCheck checkedType termChecks =>
                    termFails
                      (replace
                        {p=(\subtermsCheck' =>
                          isJust (check a l
                            (SLPairsFst
                              {sdp=(TypechecksAs check)} subtermsCheck')) =
                          True)}
                        (ListTypechecksUnique subtermsCheck lChecks)
                        (IsJustToTrue
                          (replace {p=IsJust} (sym termChecks) ItIsJust))))
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
