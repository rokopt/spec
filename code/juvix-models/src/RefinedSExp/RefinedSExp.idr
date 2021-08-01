module RefinedSExp.RefinedSExp

import public RefinedSExp.RefinedList
import public RefinedSExp.SExp
import public Library.Decidability

%default total

public export
record SExpEitherFoldSig {atom : Type} (m : Type -> Type)
  (sl, sr : SExp atom -> Type) where
    constructor SExpEitherFoldArgs
    expElim : (a : atom) -> (l : SList atom) -> SListForAll sl l ->
      m (DepEither sl sr (a $: l))

public export
sexpEitherFolds :
  {atom : Type} ->
  {m : Type -> Type} -> Monad m =>
  {sl, sr : SExp atom -> Type} ->
  (signature : SExpEitherFoldSig m sl sr) ->
  ((x : SExp atom) -> m (SExpEitherForAll sl sr x),
   (l : SList atom) -> m (SListEitherForAll sl sr l))
sexpEitherFolds {atom} {m} {sl} {sr} signature =
  sexpEliminators
    (SExpEliminatorArgs
      (\a, l, mEither =>
        mEither >>= (\either =>
          case either of
            Left allLeft =>
              map
                (\exp => case exp of
                  Left expLeft => Left (expLeft :$: allLeft)
                  Right expRight => Right (SExpExistsCons ((<$:) expRight) []))
                (expElim signature a l allLeft)
            Right existsRight => pure (Right (slistExistsExp existsRight))))
      (pure (Left (|:|)))
      (\_, _ => SExpEitherForAllCons))

public export
sexpEitherFold :
  {atom : Type} ->
  {m : Type -> Type} -> Monad m =>
  {sl, sr : SExp atom -> Type} ->
  (signature : SExpEitherFoldSig m sl sr) ->
  (x : SExp atom) -> m (SExpEitherForAll sl sr x)
sexpEitherFold {atom} {m} {sl} {sr} signature =
  fst (sexpEitherFolds signature)

public export
slistEitherFold :
  {atom : Type} ->
  {m : Type -> Type} -> Monad m =>
  {sl, sr : SExp atom -> Type} ->
  (signature : SExpEitherFoldSig m sl sr) ->
  (l : SList atom) -> m (SListEitherForAll sl sr l)
slistEitherFold {atom} {m} {sl} {sr} signature =
  snd (sexpEitherFolds signature)

public export
SExpRefinements :
  {atom : Type} ->
  {m : Type -> Type} -> Monad m =>
  {sl, sr : SExp atom -> Type} ->
  (selector : SExpEitherFoldSig m sl sr) ->
  (SExp atom -> m Type, SList atom -> m Type)
SExpRefinements selector =
  let folds = sexpEitherFolds selector in
  (\x => map IsLeft (fst folds x), \l => map IsLeft (snd folds l))

public export
SExpRefinement :
  {atom : Type} ->
  {m : Type -> Type} -> Monad m =>
  {sl, sr : SExp atom -> Type} ->
  (selector : SExpEitherFoldSig m sl sr) ->
  SExp atom -> m Type
SExpRefinement = fst . SExpRefinements

public export
SListRefinement :
  {atom : Type} ->
  {m : Type -> Type} -> Monad m =>
  {sl, sr : SExp atom -> Type} ->
  (selector : SExpEitherFoldSig m sl sr) ->
  SList atom -> m Type
SListRefinement = snd . SExpRefinements

public export
SExpLiftedRefinements :
  {atom : Type} ->
  {m : Type -> Type} -> {functionable : Functionable m} -> Monad m =>
  {sl, sr : SExp atom -> Type} ->
  (selector : SExpEitherFoldSig m sl sr) ->
  (m (SExp atom -> Type), m (SList atom -> Type))
SExpLiftedRefinements {functionable} selector =
  let refinements = SExpRefinements selector in
  (functionize functionable (fst refinements),
   functionize functionable (snd refinements))

public export
RefinedSExpTypes :
  {atom : Type} ->
  {m : Type -> Type} -> {functionable : Functionable m} -> Monad m =>
  {sl, sr : SExp atom -> Type} ->
  (selector : SExpEitherFoldSig m sl sr) ->
  (m Type, m Type)
RefinedSExpTypes {functionable} selector =
  let refinements = SExpLiftedRefinements {functionable} selector in
  (map (DPair (SExp atom)) (fst refinements),
   map (DPair (SList atom)) (snd refinements))

public export
RefinedSExp :
  {atom : Type} ->
  {m : Type -> Type} -> {functionable : Functionable m} -> Monad m =>
  {sl, sr : SExp atom -> Type} ->
  (selector : SExpEitherFoldSig m sl sr) ->
  m Type
RefinedSExp {functionable} selector =
  fst (RefinedSExpTypes {functionable} selector)

public export
RefinedSList :
  {atom : Type} ->
  {m : Type -> Type} -> {functionable : Functionable m} -> Monad m =>
  {sl, sr : SExp atom -> Type} ->
  (selector : SExpEitherFoldSig m sl sr) ->
  m Type
RefinedSList {functionable} selector =
  snd (RefinedSExpTypes {functionable} selector)

public export
record SExpEitherMetaFoldSig
  {atom : Type}
  {m : Type -> Type}
  {sl, sr : SExp atom -> Type}
  (signature : SExpEitherFoldSig m sl sr)
  (spp : (x : SExp atom) -> m (SExpEitherForAll sl sr x) -> Type)
  (lpp : (l : SList atom) -> m (SListEitherForAll sl sr l) -> Type)
  where
    constructor SExpEitherMetaFoldArgs

public export
sexpEitherMetaFolds :
  {atom : Type} ->
  {m : Type -> Type} -> Monad m =>
  {sl, sr : SExp atom -> Type} ->
  {signature : SExpEitherFoldSig m sl sr} ->
  {spp : (x : SExp atom) -> m (SExpEitherForAll sl sr x) -> Type} ->
  {lpp : (l : SList atom) -> m (SListEitherForAll sl sr l) -> Type} ->
  (metaSig : SExpEitherMetaFoldSig signature spp lpp) ->
  ((x : SExp atom) -> spp x (sexpEitherFold signature x),
   (l : SList atom) -> lpp l (slistEitherFold signature l))
sexpEitherMetaFolds = ?sexpEitherMetaFolds_hole

public export
record SExpRefinementEliminatorSig
  {atom : Type}
  {m : Type -> Type}
  {isMonad : Monad m}
  {mAlg : Algebra m Type}
  {sl, sr : SExp atom -> Type}
  (signature : SExpEitherFoldSig m sl sr)
  (srp : (x : SExp atom) -> mAlg (SExpRefinement signature x) -> Type)
  (lrp : (l : SList atom) -> mAlg (SListRefinement signature l) -> Type)
  where
    constructor SExpRefinementEliminatorArgs

public export
sexpRefinementEliminators :
  {atom : Type} ->
  {m : Type -> Type} -> {isMonad : Monad m} ->
  {mAlg : Algebra m Type} ->
  {sl, sr : SExp atom -> Type} ->
  {signature : SExpEitherFoldSig m sl sr} ->
  {srp : (x : SExp atom) -> mAlg (SExpRefinement signature x) -> Type} ->
  {lrp : (l : SList atom) -> mAlg (SListRefinement signature l) -> Type} ->
  (metaSig : SExpRefinementEliminatorSig {isMonad} {mAlg} signature srp lrp) ->
  ((x : SExp atom) -> (rx : mAlg (SExpRefinement signature x)) -> srp x rx,
   (l : SList atom) -> (rl : mAlg (SListRefinement signature l)) -> lrp l rl)
sexpRefinementEliminators = ?sexpRefinementEliminators_hole

public export
record RefinedSExpEliminatorSig
  {atom : Type}
  {m : Type -> Type}
  {isMonad : Monad m} {functionable: Functionable m} {mAlg : Algebra m Type}
  {sl, sr : SExp atom -> Type}
  (signature : SExpEitherFoldSig m sl sr)
  (srp : mAlg (RefinedSExp {functionable} signature) -> Type)
  (lrp : mAlg (RefinedSList {functionable} signature) -> Type)
  where
    constructor RefinedSExpEliminatorArgs

public export
refinedSExpEliminators :
  {atom : Type} ->
  {m : Type -> Type} ->
  {isMonad : Monad m} ->
  {functionable : Functionable m} ->
  {mAlg : Algebra m Type} ->
  {sl, sr : SExp atom -> Type} ->
  {signature : SExpEitherFoldSig m sl sr} ->
  {srp : mAlg (RefinedSExp {functionable} signature) -> Type} ->
  {lrp : mAlg (RefinedSList {functionable} signature) -> Type} ->
  (metaSig : RefinedSExpEliminatorSig
    {isMonad} {functionable} {mAlg} signature srp lrp) ->
  ((rx : mAlg (RefinedSExp {functionable} signature)) -> srp rx,
   (rl : mAlg (RefinedSList {functionable} signature)) -> lrp rl)
refinedSExpEliminators = ?refinedSExpEliminators_hole

public export
record RefinedSExpTransformerSig
  {m : Type -> Type}
  {isMonad : Monad m}
  {functionable : Functionable m}
  {mAlg : Algebra m Type}
  {atom, atom' : Type}
  {sl, sr, sl', sr' : SExp atom -> Type}
  (signature : SExpEitherFoldSig m sl sr)
  (signature' : SExpEitherFoldSig m sl' sr')
  where
    constructor RefinedSExpTransformerArgs

public export
refinedSExpTransformers :
  {m : Type -> Type} ->
  {isMonad : Monad m} ->
  {functionable : Functionable m} ->
  {mAlg : Algebra m Type} ->
  {atom, atom' : Type} ->
  {sl, sr, sl', sr' : SExp atom -> Type} ->
  {signature : SExpEitherFoldSig m sl sr} ->
  {signature' : SExpEitherFoldSig m sl' sr'} ->
  (transformSig : RefinedSExpTransformerSig
    {isMonad} {functionable} {mAlg} signature signature') ->
  (mAlg (RefinedSExp {functionable} signature) ->
    mAlg (RefinedSExp {functionable} signature'),
   mAlg (RefinedSList {functionable} signature) ->
    mAlg (RefinedSList {functionable} signature'))
refinedSExpTransformers = ?refinedSExpTransformers_hole

-- XXX depdendent transformers; dependently-typed programming languages;
-- elimination of refined sexps to dependently-typed programming languages;
-- elimination of refined sexps to dependently-typed programming languages;
-- parameterized (on other dependently-typed programming languages)
-- dependently-typed programming languages; elimination of refined sexps
-- to parameterized dependently-typed programming languages; elimination
-- of refined sexps to transformations between dependently-typed programming
-- languages; refined sexps _as_ a dependently-typed programming language;
-- dependently-typed metaprogramming

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
  Builtin.snd (fst
    (sexpDepFoldsContextIndependent
      {fs=(Prelude.Basics.id)} {fl=(Prelude.Basics.id)}
      {sp=(\x => Maybe (SExpForAll (SuccessPredicate predicate) x))}
      {lp=(\x => Maybe (SListForAll (SuccessPredicate predicate) x))}
      (SExpEliminatorArgs
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
            (tailContext, tailResult) = tail context
          in
          case tailResult of
            Just tailSuccess =>
              let (headContext, headResult) = head tailContext in
              case headResult of
                Just headSuccess =>
                  (headContext, Just (headSuccess ::: tailSuccess))
                Nothing => (headContext, Nothing)
            Nothing => (fst (head tailContext), Nothing)))
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
