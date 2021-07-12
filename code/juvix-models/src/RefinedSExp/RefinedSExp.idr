module RefinedSExp.RefinedSExp

import public RefinedSExp.RefinedList
import public RefinedSExp.SExp
import public Library.Decidability

%default total

public export
record DecidablePredicate (atom : Type) where
  constructor ResultPredicates
  SuccessPredicate : SExp atom -> Type
  FailurePredicate : SExp atom -> Type

public export
data DecisionResult : {atom : Type} ->
    (predicate : DecidablePredicate atom) -> SExp atom -> Type where
  DecisionSuccess : {predicate : DecidablePredicate atom} -> {x : SExp atom} ->
    SuccessPredicate predicate x -> DecisionResult predicate x
  DecisionFailure : {predicate : DecidablePredicate atom} -> {x : SExp atom} ->
    FailurePredicate predicate x -> DecisionResult predicate x

public export
DecisionSuccessInjective : {atom : Type} ->
  {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result, result' : SuccessPredicate predicate x} ->
  DecisionSuccess {x} {predicate} result =
    DecisionSuccess {x} {predicate} result' ->
  result = result'
DecisionSuccessInjective Refl = Refl

public export
DecisionFailureInjective : {atom : Type} ->
  {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result, result' : FailurePredicate predicate x} ->
  DecisionFailure {x} {predicate} result =
    DecisionFailure {x} {predicate} result' ->
  result = result'
DecisionFailureInjective Refl = Refl

public export
data IsSuccess : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {x : SExp atom} -> DecisionResult predicate x -> Type where
  Successful : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {x : SExp atom} -> (result : SuccessPredicate predicate x) ->
    IsSuccess {x} {predicate} (DecisionSuccess result)

public export
IsSuccessExtract : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : DecisionResult predicate x} ->
  IsSuccess result -> SuccessPredicate predicate x
IsSuccessExtract (Successful success) = success

public export
IsSuccessExtractElim : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : DecisionResult predicate x} ->
  (succeeded : IsSuccess result) ->
  result = DecisionSuccess (IsSuccessExtract succeeded)
IsSuccessExtractElim (Successful _) = Refl

public export
SuccessIsSuccessful : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {success : SuccessPredicate predicate x} ->
  {result : DecisionResult predicate x} ->
  result = DecisionSuccess {x} {predicate} success ->
  IsSuccess {x} {predicate} result
SuccessIsSuccessful {x} {success} Refl = Successful success

public export
isSuccess : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> (result : DecisionResult predicate x) ->
  Dec (IsSuccess result)
isSuccess (DecisionSuccess success) = Yes (Successful success)
isSuccess (DecisionFailure _) =
  No (\success => case success of Successful _ impossible)

public export
NotSuccessExtract : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : DecisionResult predicate x} ->
  Not (IsSuccess result) -> FailurePredicate predicate x
NotSuccessExtract {result=(DecisionSuccess success)} notSuccess =
  void (notSuccess (Successful success))
NotSuccessExtract {result=(DecisionFailure failure)} _ = failure

public export
data IsFailure : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {x : SExp atom} -> DecisionResult predicate x -> Type where
  Failed : {atom : Type} -> {predicate : DecidablePredicate atom} ->
    {x : SExp atom} -> (result : FailurePredicate predicate x) ->
    IsFailure {x} {predicate} (DecisionFailure result)

public export
IsFailureExtract : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : DecisionResult predicate x} ->
  IsFailure result -> FailurePredicate predicate x
IsFailureExtract (Failed failure) = failure

public export
IsFailureExtractElim : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : DecisionResult predicate x} ->
  (succeeded : IsFailure result) ->
  result = DecisionFailure (IsFailureExtract succeeded)
IsFailureExtractElim (Failed _) = Refl

public export
isFailure : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> (result : DecisionResult predicate x) ->
  Dec (IsFailure result)
isFailure (DecisionSuccess _) =
  No (\failed => case failed of Failed _ impossible)
isFailure (DecisionFailure failed) = Yes (Failed failed)

public export
NotFailureExtract : {atom : Type} -> {predicate : DecidablePredicate atom} ->
  {x : SExp atom} -> {result : DecisionResult predicate x} ->
  Not (IsFailure result) -> SuccessPredicate predicate x
NotFailureExtract {result=(DecisionSuccess success)} _ = success
NotFailureExtract {result=(DecisionFailure failure)} notFailure =
  void (notFailure (Failed failure))

public export
record InductiveDecisionSig
  {atom : Type}
  (predicate : DecidablePredicate atom)
  (contextType : Type) where
    constructor InductiveDecisionArgs
    initialContext : contextType
    decideOne :
      (a : atom) -> (l : SList atom) ->
      SListForAll (SuccessPredicate predicate) l ->
      (contextType -> (contextType, DecisionResult predicate (a $: l)))
    failOne :
      DPair (SExp atom) (FailurePredicate predicate) ->
      contextType -> contextType

public export
inductiveDecide : {atom : Type} ->
  {predicate : DecidablePredicate atom} -> {contextType : Type} ->
  InductiveDecisionSig predicate contextType ->
  (x : SExp atom) -> Maybe (SExpForAll (SuccessPredicate predicate) x)
inductiveDecide decisionSig x' =
  snd (fst
    (sexpDepFoldsContextIndependent
      {sp=(\x => Maybe (SExpForAll (SuccessPredicate predicate) x))}
      {lp=(\x => Maybe (SListForAll (SuccessPredicate predicate) x))}
      (SExpDepFoldContextIndependentArgs
        (\a, l, tail, context =>
          let
            (tailContext, tailDecision) = tail context
          in
          case tailDecision of
            Just tailSuccess =>
              case decideOne decisionSig a l tailSuccess tailContext of
                (returnContext, DecisionSuccess headSuccess) =>
                  (returnContext, Just (headSuccess :$: tailSuccess))
                (failureContext, DecisionFailure headFailure) =>
                  (failOne decisionSig ((a $: l) ** headFailure) failureContext,
                   Nothing)
            Nothing => (tailContext, Nothing))
        (\context => (context, Just (|:|)))
        (\x, l, head, tail, context =>
          let
            (headContext, headForAll) = head context
          in
          case headForAll of
            Just headSuccess =>
              let (tailContext, tailForAll) = tail headContext in
              case tailForAll of
                Just tailSuccess =>
                  (tailContext, Just (headSuccess ::: tailSuccess))
                Nothing => (tailContext, Nothing)
            Nothing => (headContext, Nothing)))
      (initialContext decisionSig)
    )
  x')

public export
Checks : {atom : Type} ->
  {predicate : DecidablePredicate atom} -> {contextType : Type} ->
  InductiveDecisionSig predicate contextType ->
  SExp atom -> Type
Checks signature x = IsJust (inductiveDecide signature x)

public export
Checked : {atom : Type} ->
  {predicate : DecidablePredicate atom} -> {contextType : Type} ->
  InductiveDecisionSig predicate contextType ->
  Type
Checked signature = DPair (SExp atom) (Checks signature)

public export
decChecked : {atom : Type} ->
  {predicate : DecidablePredicate atom} -> {contextType : Type} ->
  (signature : InductiveDecisionSig predicate contextType) ->
  (x : SExp atom) -> Dec (Checks signature x)
decChecked signature x = IsJustDec (inductiveDecide signature x)

public export
checksInjective : {atom : Type} ->
  {predicate : DecidablePredicate atom} -> {contextType : Type} ->
  {signature : InductiveDecisionSig predicate contextType} ->
  {x : SExp atom} -> (checks, checks' : Checks signature x) ->
  checks = checks'
checksInjective = IsJustUnique

public export
checkedInjective : {atom : Type} ->
  {predicate : DecidablePredicate atom} -> {contextType : Type} ->
  {signature : InductiveDecisionSig predicate contextType} ->
  {checked, checked' : Checked signature} ->
  (fst checked = fst checked') ->
  checked = checked'
checkedInjective {signature} =
  JustDPairInjective {dec=(inductiveDecide signature)}
