module RefinedSExp.RefinedSExp

import public RefinedSExp.SExp
import public Library.Decidability

%default total

mutual
  public export
  sExpEq : {atom : Type} -> DecEqPred atom -> DecEqPred (SExp atom)
  sExpEq deq (a $: l) (a' $: l') = case (deq a a', sListEq deq l l') of
    (Yes Refl, Yes Refl) => Yes Refl
    (No neq, _) => No (\eq => case eq of Refl => neq Refl)
    (_ , No neq) => No (\eq => case eq of Refl => neq Refl)

  public export
  sListEq : {atom : Type} -> DecEqPred atom -> DecEqPred (SList atom)
  sListEq deq ($|) ($|) = Yes Refl
  sListEq deq (x $+ l) ($|) = No (\eq => case eq of Refl impossible)
  sListEq deq ($|) (x $+ l) = No (\eq => case eq of Refl impossible)
  sListEq deq (x $+ l) (x' $+ l') = case (sExpEq deq x x', sListEq deq l l') of
    (Yes Refl, Yes Refl) => Yes Refl
    (No neq, _) => No (\eq => case eq of Refl => neq Refl)
    (_ , No neq) => No (\eq => case eq of Refl => neq Refl)

DepEither : {a : Type} -> (b, c : a -> Type) -> a -> Type
DepEither {a} b c = \x : a => Either (b x) (c x)

DepLeft : {a : Type} -> {b, c : a -> Type} -> {x : a} -> b x -> DepEither b c x
DepLeft bx = Left bx

DepRight : {a : Type} -> {b, c : a -> Type} -> {x : a} -> c x -> DepEither b c x
DepRight cx = Right cx

DPairEither : {a : Type} -> (b, c : a -> Type) -> Type
DPairEither {a} b c = Either (DPair a b) (DPair a c)

public export
record SEitherIndSig {atom : Type}
  (sp, sp' : SPredicate atom)
  (lp, lp' : SLPredicate atom) where
    constructor SEitherIndArgs
    expElimL : (a : atom) -> (l : SList atom) -> lp l ->
      Either (sp (a $: l)) (sp' (a $: l))
    expElimR : (a : atom) -> (l : SList atom) -> lp' l ->
      Either (sp (a $: l)) (sp' (a $: l))
    nilElim : Either (lp ($|)) (lp' ($|))
    consElimLL :
      (x : SExp atom) -> (l : SList atom) -> sp x -> lp l ->
        Either (lp (x $+ l)) (lp' (x $+ l))
    consElimLR :
      (x : SExp atom) -> (l : SList atom) -> sp x -> lp' l ->
        Either (lp (x $+ l)) (lp' (x $+ l))
    consElimRL :
      (x : SExp atom) -> (l : SList atom) -> sp' x -> lp l ->
        Either (lp (x $+ l)) (lp' (x $+ l))
    consElimRR :
      (x : SExp atom) -> (l : SList atom) -> sp' x -> lp' l ->
        Either (lp (x $+ l)) (lp' (x $+ l))

public export
sEitherInd : {atom : Type} ->
  {sp, sp' : SPredicate atom} -> {lp, lp' : SLPredicate atom} ->
  SEitherIndSig sp sp' lp lp' ->
  ((x : SExp atom) -> DepEither sp sp' x,
   (l : SList atom) -> DepEither lp lp' l)
sEitherInd signature =
  sInd
    {sp=(DepEither sp sp')}
    {lp=(DepEither lp lp')}
    (SIndArgs
      (\a, l, lpl => case lpl of
        Left lplL => expElimL signature a l lplL
        Right lplR => expElimR signature a l lplR)
      (nilElim signature)
      (\x, l, spx, lpl => case (spx, lpl) of
        (Left spxL, Left lplL) => consElimLL signature x l spxL lplL
        (Left spxL, Right lplR) => consElimLR signature x l spxL lplR
        (Right spxR, Left lplL) => consElimRL signature x l spxR lplL
        (Right spxR, Right lplR) => consElimRR signature x l spxR lplR))

public export
record SLeftIndSig {atom : Type}
  (sp, sp' : SPredicate atom)
  (lp, lp' : SLPredicate atom) where
    constructor SLeftIndArgs
    expElimL : (a : atom) -> (l : SList atom) -> lp l ->
      Either (sp (a $: l)) (sp' (a $: l))
    expElimR : (a : atom) -> (l : SList atom) -> lp' l ->
      sp' (a $: l)
    nilElim : lp ($|)
    consElimLL :
      (x : SExp atom) -> (l : SList atom) -> sp x -> lp l ->
        Either (lp (x $+ l)) (lp' (x $+ l))
    consElimLR :
      (x : SExp atom) -> (l : SList atom) -> sp x -> lp' l -> (lp' (x $+ l))
    consElimRL :
      (x : SExp atom) -> (l : SList atom) -> sp' x -> lp l -> (lp' (x $+ l))
    consElimRR :
      (x : SExp atom) -> (l : SList atom) -> sp' x -> lp' l -> (lp' (x $+ l))

mutual
  public export
  sLeftExpInd : {atom : Type} ->
    {sp, sp' : SPredicate atom} -> {lp, lp' : SLPredicate atom} ->
    SLeftIndSig sp sp' lp lp' ->
    (x : SExp atom) -> DepEither sp sp' x
  sLeftExpInd signature (a $: l) =
    case sLeftListInd signature l of
      Left lplL => expElimL signature a l lplL
      Right lplR => Right (expElimR signature a l lplR)

  public export
  sLeftListInd : {atom : Type} ->
    {sp, sp' : SPredicate atom} -> {lp, lp' : SLPredicate atom} ->
    SLeftIndSig sp sp' lp lp' ->
    (l : SList atom) -> DepEither lp lp' l
  sLeftListInd signature ($|) = Left (nilElim signature)
  sLeftListInd signature (x $+ l) =
    case (sLeftExpInd signature x,
          sLeftListInd signature l) of
       (Left spxL, Left lplL) => consElimLL signature x l spxL lplL
       (Left spxL, Right lplR) => Right (consElimLR signature x l spxL lplR)
       (Right spxR, Left lplL) => Right (consElimRL signature x l spxR lplL)
       (Right spxR, Right lplR) => Right (consElimRR signature x l spxR lplR)

public export
sLeftInd : {atom : Type} ->
  {sp, sp' : SPredicate atom} -> {lp, lp' : SLPredicate atom} ->
  SLeftIndSig sp sp' lp lp' ->
  ((x : SExp atom) -> DepEither sp sp' x,
   (l : SList atom) -> DepEither lp lp' l)
sLeftInd signature = (sLeftExpInd signature, sLeftListInd signature)

public export
record SLeftIndForAllSig {atom : Type} (sp, sp' : SPredicate atom) where
  constructor SLeftIndForAllArgs
  expElimL : (a : atom) -> (l : SList atom) -> SLForAll sp l ->
    DepEither sp sp' (a $: l)

public export
sLeftIndForAll : {atom : Type} ->
  {sp, sp' : SPredicate atom} ->
  SLeftIndForAllSig sp sp' ->
  ((x : SExp atom) -> Either (sp x) (List (DPair (SExp atom) sp')),
   (l : SList atom) -> Either (SLForAll sp l) (List (DPair (SExp atom) sp')))
sLeftIndForAll {sp} {sp'} signature =
  sLeftInd
    {sp} {sp'=(\_ => List (DPair (SExp atom) sp'))}
    {lp=(SLForAll sp)} {lp'=(\_ => List (DPair (SExp atom) sp'))}
    (SLeftIndArgs
      (\a, l, lpl => case expElimL signature a l lpl of
        Left spal => Left spal
        Right failure => Right [ (a $: l ** failure) ])
      (\_, _, failures => failures)
      SLForAllEmpty
      (\_, _, spx, lpl => Left (SLForAllCons spx lpl))
      (\_, _, _, failures => failures)
      (\_, _, failures, _ => failures)
      (\_, _, failuresL, failuresR => failuresL ++ failuresR))

infixr 4 **<
(**<) : {a : Type} -> {b, c : a -> Type} -> (x : a) -> b x ->
  DPairEither b c
x **< bx = Left (x ** bx)

infixr 4 **>
(**>) : {a : Type} -> {b, c : a -> Type} -> (x : a) -> c x ->
  DPairEither b c
x **> cx = Right (x ** cx)

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
record DecidablePredicate (atom : Type) where
  constructor ResultPredicates
  SuccessType : SPredicate atom
  FailureType : SPredicate atom

public export
data TypecheckResult : {atom : Type} -> (predicate : DecidablePredicate atom) ->
    SExp atom -> Type where
  TypecheckSuccess : {predicate : DecidablePredicate atom} -> {x : SExp atom} ->
    SuccessType predicate x -> TypecheckResult predicate x
  TypecheckFailure : {predicate : DecidablePredicate atom} -> {x : SExp atom} ->
    FailureType predicate x -> TypecheckResult predicate x

public export
TypecheckSuccessInjective : {atom : Type} ->
  {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result, result' : SuccessType predicate x} ->
  TypecheckSuccess {x} {predicate} result =
    TypecheckSuccess {x} {predicate} result' ->
  result = result'
TypecheckSuccessInjective Refl = Refl

public export
TypecheckFailureInjective : {atom : Type} ->
  {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result, result' : FailureType predicate x} ->
  TypecheckFailure {x} {predicate} result =
    TypecheckFailure {x} {predicate} result' ->
  result = result'
TypecheckFailureInjective Refl = Refl

public export
data IsSuccess : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {x : SExp atom} -> TypecheckResult predicate x -> Type where
  Successful : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {x : SExp atom} -> (result : SuccessType predicate x) ->
    IsSuccess {x} {predicate} (TypecheckSuccess result)

public export
IsSuccessExtract : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : TypecheckResult predicate x} ->
  IsSuccess result -> SuccessType predicate x
IsSuccessExtract (Successful success) = success

public export
IsSuccessExtractElim : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : TypecheckResult predicate x} ->
  (succeeded : IsSuccess result) ->
  result = TypecheckSuccess (IsSuccessExtract succeeded)
IsSuccessExtractElim (Successful _) = Refl

public export
SuccessIsSuccessful : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {success : SuccessType predicate x} ->
  {result : TypecheckResult predicate x} ->
  result = TypecheckSuccess {x} {predicate} success ->
  IsSuccess {x} {predicate} result
SuccessIsSuccessful {x} {success} Refl = Successful success

public export
isSuccess : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> (result : TypecheckResult predicate x) ->
  Dec (IsSuccess result)
isSuccess (TypecheckSuccess success) = Yes (Successful success)
isSuccess (TypecheckFailure _) =
  No (\success => case success of Successful _ impossible)

public export
NotSuccessExtract : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : TypecheckResult predicate x} ->
  Not (IsSuccess result) -> FailureType predicate x
NotSuccessExtract {result=(TypecheckSuccess success)} notSuccess =
  void (notSuccess (Successful success))
NotSuccessExtract {result=(TypecheckFailure failure)} _ = failure

public export
data IsFailure : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {x : SExp atom} -> TypecheckResult predicate x -> Type where
  Failed : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {x : SExp atom} -> (result : FailureType predicate x) ->
    IsFailure {x} {predicate} (TypecheckFailure result)

public export
IsFailureExtract : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : TypecheckResult predicate x} ->
  IsFailure result -> FailureType predicate x
IsFailureExtract (Failed failure) = failure

public export
IsFailureExtractElim : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : TypecheckResult predicate x} ->
  (succeeded : IsFailure result) ->
  result = TypecheckFailure (IsFailureExtract succeeded)
IsFailureExtractElim (Failed _) = Refl

public export
isFailure : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> (result : TypecheckResult predicate x) ->
  Dec (IsFailure result)
isFailure (TypecheckSuccess _) =
  No (\failed => case failed of Failed _ impossible)
isFailure (TypecheckFailure failed) = Yes (Failed failed)

public export
NotFailureExtract : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : TypecheckResult predicate x} ->
  Not (IsFailure result) -> SuccessType predicate x
NotFailureExtract {result=(TypecheckSuccess success)} _ = success
NotFailureExtract {result=(TypecheckFailure failure)} notFailure =
  void (notFailure (Failed failure))

public export
record InductiveTypecheck {atom : Type}
    (predicate : DecidablePredicate atom) where
  constructor MkInductiveTypecheck
  typecheckOne : (a : atom) -> (l : SList atom) ->
    SLForAll (SuccessType predicate) l -> TypecheckResult predicate (a $: l)
  MergedFailures : Type
  firstFailure : (x : SExp atom) -> FailureType predicate x -> MergedFailures
  mergeFailures : MergedFailures -> MergedFailures -> MergedFailures

public export
data TypechecksAs : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    InductiveTypecheck predicate ->
    (x : SExp atom) -> SuccessType predicate x -> Type where
  AllSubtermsTypecheckAs : {atom : Type} ->
    {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {a : atom} -> {l : SList atom} ->
    (subtermsCheck : SLForAll (SDepPredPair (TypechecksAs check)) l) ->
    (checkedType : SuccessType predicate (a $: l)) ->
    (termChecks :
      typecheckOne check a l (SLPairsFst subtermsCheck) =
        TypecheckSuccess {predicate} checkedType) ->
    TypechecksAs check (a $: l) checkedType

public export
TypechecksAsSubterms : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {a : atom} -> {l : SList atom} ->
    {checkedType : SuccessType predicate (a $: l)} ->
    TypechecksAs check (a $: l) checkedType ->
    SLForAll (SDepPredPair (TypechecksAs check)) l
TypechecksAsSubterms (AllSubtermsTypecheckAs subtermsCheck _ _) = subtermsCheck

public export
Typechecks : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  InductiveTypecheck predicate -> (x : SExp atom) -> Type
Typechecks check x = DPair (SuccessType predicate x) (TypechecksAs check x)

public export
TypecheckedTerm : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  InductiveTypecheck predicate -> Type
TypecheckedTerm check = DPair (SExp atom) (Typechecks check)

mutual
  public export
  CheckedTypesUnique : {atom : Type} -> {predicate : DecidablePredicate atom} ->
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

  public export
  TypechecksAsUnique :
    {atom : Type} -> {predicate : DecidablePredicate atom} ->
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

  public export
  HeterogeneousTypechecksAsUnique :
    {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} ->
    {a : atom} -> {l : SList atom} ->
    {type, type' : SuccessType predicate (a $: l)} ->
    (typechecksAs : TypechecksAs check (a $: l) type) ->
    (typechecksAs' : TypechecksAs check (a $: l) type') ->
    typechecksAs = typechecksAs'
  HeterogeneousTypechecksAsUnique {type} {type'} typechecksAs typechecksAs' =
    case CheckedTypesUnique typechecksAs typechecksAs' of
      Refl => TypechecksAsUnique {type} {type'=type} typechecksAs typechecksAs'

  public export
  TypechecksUnique : {atom : Type} -> {predicate : DecidablePredicate atom} ->
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

  public export
  ListTypechecksUnique : {atom : Type} ->
    {predicate : DecidablePredicate atom} ->
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
data CheckResult : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    (check : InductiveTypecheck predicate) -> (x : SExp atom) -> Type where
  CheckSuccess : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} -> {x : SExp atom} ->
    Typechecks check x -> CheckResult check x
  CheckFailure : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} -> {x : SExp atom} ->
    Not (Typechecks check x) -> MergedFailures check -> CheckResult check x

public export
isCheckSuccess : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {check : InductiveTypecheck predicate} -> {x : SExp atom} ->
  CheckResult check x -> Bool
isCheckSuccess (CheckSuccess _) = True
isCheckSuccess (CheckFailure _ _) = False

public export
isCheckFailure : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {check : InductiveTypecheck predicate} -> {x : SExp atom} ->
  CheckResult check x -> Bool
isCheckFailure = not . isCheckSuccess

public export
data ListCheckResult : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    (check : InductiveTypecheck predicate) -> (l : SList atom) -> Type where
  ListCheckSuccess : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} -> {l : SList atom} ->
    SLForAll (Typechecks check) l ->
    ListCheckResult check l
  ListCheckFailure : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {check : InductiveTypecheck predicate} -> {l : SList atom} ->
    Not (SLForAll (Typechecks check) l) -> MergedFailures check ->
    ListCheckResult check l

public export
isListCheckSuccess : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {check : InductiveTypecheck predicate} -> {l : SList atom} ->
  ListCheckResult check l -> Bool
isListCheckSuccess (ListCheckSuccess _) = True
isListCheckSuccess (ListCheckFailure _ _) = False

public export
isListCheckFailure : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {check : InductiveTypecheck predicate} -> {l : SList atom} ->
  ListCheckResult check l -> Bool
isListCheckFailure = not . isListCheckSuccess

public export
CheckResultCons : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {check : InductiveTypecheck predicate} ->
  {x : SExp atom} -> {l : SList atom} ->
  CheckResult check x -> ListCheckResult check l ->
  ListCheckResult check (x $+ l)
CheckResultCons (CheckSuccess head) (ListCheckSuccess tail) =
  ListCheckSuccess (SLForAllCons head tail)
CheckResultCons (CheckFailure head headFailure) (ListCheckSuccess tail) =
  ListCheckFailure
    (\success => case success of
      SLForAllEmpty impossible
      SLForAllCons headSuccess tailSuccess => head headSuccess)
    headFailure
CheckResultCons (CheckSuccess head) (ListCheckFailure tail tailFailure) =
  ListCheckFailure
    (\success => case success of
      SLForAllEmpty impossible
      SLForAllCons headSuccess tailSuccess => tail tailSuccess)
    tailFailure
CheckResultCons
  (CheckFailure head headFailure) (ListCheckFailure tail tailFailure) =
    ListCheckFailure
      (\success => case success of
        SLForAllEmpty impossible
        SLForAllCons headSuccess tailSuccess => head headSuccess)
      (mergeFailures check headFailure tailFailure)

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
typecheck : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  (check : InductiveTypecheck predicate) ->
  ((x : SExp atom) -> CheckResult check x,
   (l : SList atom) -> ListCheckResult check l)
typecheck check =
  sInd {lp=(ListCheckResult check)} (SIndArgs
    (\a, l, lCheck => case lCheck of
      ListCheckSuccess lChecks =>
        case isSuccess
          (typecheckOne check a l (SLPairsFst lChecks)) of
            Yes termChecks =>
              CheckSuccess (IsSuccessExtract termChecks **
                   AllSubtermsTypecheckAs
                     lChecks
                     (IsSuccessExtract termChecks)
                     (IsSuccessExtractElim termChecks))
            No termFails =>
              CheckFailure (\termChecks => case termChecks of
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
               (firstFailure check (a $: l) (NotSuccessExtract termFails))
      ListCheckFailure lFails mergedFailure =>
        CheckFailure (\typedTerm => case typedTerm of
          (_ ** typechecks) => case typechecks of
            AllSubtermsTypecheckAs subtermsCheck _ _ =>
              lFails subtermsCheck)
          mergedFailure)
    (ListCheckSuccess SLForAllEmpty)
    (\_, _ => CheckResultCons))

public export
data FAtom : (domainAtom, codomainAtom : Type) -> Type where
  FDA : domainAtom -> FAtom domainAtom codomainAtom
  CDA : codomainAtom -> FAtom domainAtom codomainAtom

public export
FExp : (domainAtom, codomainAtom : Type) -> Type
FExp domainAtom codomainAtom = SExp (FAtom domainAtom codomainAtom)

public export
FList : (domainAtom, codomainAtom : Type) -> Type
FList domainAtom codomainAtom = SList (FAtom domainAtom codomainAtom)

public export
record TypecheckFunctionPredicate {atom, atom' : Type}
    (domain : DecidablePredicate atom)
    (codomain : DecidablePredicate atom') where
  constructor MkTypecheckFunctionPredicate
  DomainCheck : InductiveTypecheck domain
  CodomainCheck : InductiveTypecheck codomain

public export
FunctionSuccessType : {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  TypecheckFunctionPredicate domain codomain ->
  SPredicate (FAtom atom atom')
FunctionSuccessType predicate x = ?FunctionSuccessType_hole

public export
FunctionFailureType : {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  TypecheckFunctionPredicate domain codomain ->
  SPredicate (FAtom atom atom')
FunctionFailureType predicate x = ?FunctionFailureType_hole

public export
FunctionDecidablePredicate : {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  TypecheckFunctionPredicate domain codomain ->
  DecidablePredicate (FAtom atom atom')
FunctionDecidablePredicate predicate =
  ResultPredicates
    (FunctionSuccessType predicate)
    (FunctionFailureType predicate)

public export
FunctionTypecheckOne : {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  (predicate : TypecheckFunctionPredicate domain codomain) ->
  (a : FAtom atom atom') ->
  (l : FList atom atom') ->
  SLForAll (FunctionSuccessType predicate) l ->
  TypecheckResult (FunctionDecidablePredicate predicate) (a $: l)
FunctionTypecheckOne predicate a l subtermsCheck = ?FunctionTypecheckOne_hole

public export
data FunctionMergedFailures : {atom, atom' : Type} ->
    {domain : DecidablePredicate atom} ->
    {codomain : DecidablePredicate atom'} ->
    (predicate : TypecheckFunctionPredicate domain codomain) -> Type where
  DomainFailure :
    {domain : DecidablePredicate atom} ->
    {codomain : DecidablePredicate atom'} ->
    (predicate : TypecheckFunctionPredicate domain codomain) ->
    MergedFailures (DomainCheck predicate) ->
    FunctionMergedFailures {domain} {codomain} predicate
  CodomainFailure :
    {domain : DecidablePredicate atom} ->
    {codomain : DecidablePredicate atom'} ->
    (predicate : TypecheckFunctionPredicate domain codomain) ->
    MergedFailures (CodomainCheck predicate) ->
    FunctionMergedFailures {domain} {codomain} predicate

public export
FunctionFirstFailure : {atom, atom' : Type} ->
    {domain : DecidablePredicate atom} ->
    {codomain : DecidablePredicate atom'} ->
    {predicate : TypecheckFunctionPredicate domain codomain} ->
    (x : FExp atom atom') -> FunctionFailureType predicate x ->
    FunctionMergedFailures predicate
FunctionFirstFailure x failure = ?FunctionFirstFailure_hole

public export
FunctionMergeFailures : {atom, atom' : Type} ->
    {domain : DecidablePredicate atom} ->
    {codomain : DecidablePredicate atom'} ->
    {predicate : TypecheckFunctionPredicate domain codomain} ->
    FunctionMergedFailures predicate ->
    FunctionMergedFailures predicate ->
    FunctionMergedFailures predicate
FunctionMergeFailures x failure = ?FunctionMergeFailures_hole

public export
FunctionTypecheckInductive : {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  (predicate : TypecheckFunctionPredicate domain codomain) ->
  InductiveTypecheck (FunctionDecidablePredicate predicate)
FunctionTypecheckInductive predicate =
  MkInductiveTypecheck
    (FunctionTypecheckOne predicate)
    (FunctionMergedFailures predicate)
    (FunctionFirstFailure {predicate})
    (FunctionMergeFailures {predicate})

public export
CheckFunctionResult : {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  (predicate : TypecheckFunctionPredicate domain codomain) ->
  FExp atom atom' -> Type
CheckFunctionResult predicate =
  CheckResult (FunctionTypecheckInductive predicate)

public export
ListCheckFunctionResult : {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  (predicate : TypecheckFunctionPredicate domain codomain) ->
  FList atom atom' -> Type
ListCheckFunctionResult predicate =
  ListCheckResult (FunctionTypecheckInductive predicate)

public export
typecheckFunction :
  {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  (predicate : TypecheckFunctionPredicate domain codomain) ->
  ((x : FExp atom atom') -> CheckFunctionResult predicate x,
   (l : FList atom atom') -> ListCheckFunctionResult predicate l)
typecheckFunction predicate = typecheck (FunctionTypecheckInductive predicate)

public export
FTypechecks :
  {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  (predicate : TypecheckFunctionPredicate domain codomain) ->
  (x : FExp atom atom') -> Type
FTypechecks check = Typechecks (FunctionTypecheckInductive check)

public export
generatedFunction :
  {atom, atom' : Type} ->
  {domain : DecidablePredicate atom} ->
  {codomain : DecidablePredicate atom'} ->
  {predicate : TypecheckFunctionPredicate domain codomain} ->
  TypecheckedTerm (FunctionTypecheckInductive predicate) ->
  TypecheckedTerm (DomainCheck predicate) ->
  TypecheckedTerm (CodomainCheck predicate)
generatedFunction (fx ** (ftype ** fchecks)) (dx ** (dtype ** dchecks)) =
  (?generatedFunction_hole_cx **
  (?generatedFunction_hole_ctype **
   ?generatedFunction_hole_cchecks))
