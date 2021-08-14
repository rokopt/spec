module RefinedSExp.SExp

import Library.FunctionsAndRelations
import Library.Decidability
import Library.List
import public Category.Category

%default total

prefix 1 $:
infixr 7 $.
public export
data SExp : (atom : Type) -> Type where
  ($:) : atom -> SExp atom
  ($.) : SExp atom -> SExp atom -> SExp atom

prefix 1 $..
public export
($..) : PairOf (SExp atom) -> SExp atom
($..) p = fst p $. snd p

public export
SExpPred : (atom : Type) -> Type
SExpPred atom = !- (SExp atom)

public export
SExpPi : {atom : Type} -> SExpPred atom -> Type
SExpPi sp = SExp atom ~> sp

public export
SExpTypeConstructor : (atom : Type) -> Type
SExpTypeConstructor atom = DependentTypeConstructor (SExp atom)

public export
SExpPredList : (atom : Type) -> Type
SExpPredList atom = List (SExpPred atom)

public export
record SExpEliminatorSig {0 atom : Type} (0 sp : SExpPred atom) where
  constructor SExpEliminatorArgs
  atomElim : (a : atom) -> sp ($: a)
  pairElim : (x, x' : SExp atom) -> sp x -> sp x' -> sp (x $. x')

public export
sexpEliminator :
  {0 atom : Type} -> {0 sp : SExpPred atom} ->
  SExpEliminatorSig sp -> SExpPi sp
sexpEliminator signature ($: a) =
  atomElim signature a
sexpEliminator signature (x $. x') =
  pairElim signature x x'
    (sexpEliminator signature x) (sexpEliminator signature x')

public export
SExpSignatureComposeSig :
  {atom : Type} ->
  {f : Type -> Type} ->
  (app : Applicative f) ->
  {sp : SExpPred atom} ->
  f (SExpEliminatorSig sp) ->
  SExpEliminatorSig (f . sp)
SExpSignatureComposeSig app fsignature =
  SExpEliminatorArgs
    (dpure app (map {f} atomElim fsignature))
    (\x, x', fsx, fsx' =>
      ((dpure app (dpure app (map {f} pairElim fsignature) x) x') <*> fsx)
        <*> fsx')

public export
sexpEliminatorComposeSig :
  {atom : Type} ->
  {f : Type -> Type} ->
  (app : Applicative f) ->
  {sp : SExpPred atom} ->
  f (SExpEliminatorSig sp) ->
  SExpPi (f . sp)
sexpEliminatorComposeSig app = sexpEliminator . SExpSignatureComposeSig app

public export
SExpParameterize : (parameter : Type) -> Type -> Type
SExpParameterize parameter type = parameter -> type

public export
SExpParameterizedPred : (atom : Type) -> (parameter : Type) -> Type
SExpParameterizedPred atom parameter =
  SExp atom -> SExpParameterize parameter Type

public export
SExpParameterizedPredToPred : {0 atom : Type} -> {parameter : Type} ->
  (sp : SExpParameterizedPred atom parameter) -> SExpPred atom
SExpParameterizedPredToPred {parameter} sp = \x => parameter ~> sp x

public export
SExpParameterizedEliminatorSig : {0 atom : Type} -> {0 parameter : Type} ->
  (0 sp : SExpParameterizedPred atom parameter) -> Type
SExpParameterizedEliminatorSig sp =
  SExpEliminatorSig (SExpParameterizedPredToPred sp)

public export
SExpParameterizedPi : {atom : Type} -> {parameter : Type} ->
  (sp : SExpParameterizedPred atom parameter) -> Type
SExpParameterizedPi = SExpPi . SExpParameterizedPredToPred

{- XXX could we also do this using signature composition -}
sexpParameterizedEliminator :
  {0 atom : Type} -> {0 parameter : Type} ->
  {sp : SExpParameterizedPred atom parameter} ->
  SExpParameterizedEliminatorSig sp ->
  SExpParameterizedPi sp
sexpParameterizedEliminator = sexpEliminator

public export
SExpMetaPred : {atom : Type} -> (sp : SExpPred atom) -> Type
SExpMetaPred {atom} sp = (x : SExp atom) -> sp x -> Type

public export
SExpMetaPi : {atom : Type} -> {sp : SExpPred atom} ->
  (smp : SExpMetaPred sp) -> Type
SExpMetaPi {atom} {sp} smp = (x : SExp atom) -> (spx : sp x) -> smp x spx

public export
SExpMetaPredToPred : {0 atom : Type} -> {sp : SExpPred atom} ->
  SExpMetaPred sp -> SExpPred atom
SExpMetaPredToPred {sp} smp = \x => sp x ~> smp x

public export
sexpMetaPredCompose : {0 atom : Type} ->
  (f : Type -> Type) -> {0 sp : SExpPred atom} ->
  (smp : SExpMetaPred sp) -> SExpMetaPred sp
sexpMetaPredCompose f smp = \x, spx => f (smp x spx)

public export
SExpEliminatorPred : {0 atom : Type} -> {0 sp : SExpPred atom} ->
  SExpEliminatorSig sp -> SExpMetaPred sp -> SExpPred atom
SExpEliminatorPred signature smp = \x => smp x (sexpEliminator signature x)

public export
SExpEliminatorPi : {atom : Type} -> {0 sp : SExpPred atom} ->
  SExpEliminatorSig sp -> SExpMetaPred sp -> Type
SExpEliminatorPi signature smp = SExpPi (SExpEliminatorPred signature smp)

public export
SExpMetaEliminatorSig : {0 atom : Type} -> {0 sp : SExpPred atom} ->
  (0 signature : SExpEliminatorSig sp) -> (0 smp : SExpMetaPred sp) -> Type
SExpMetaEliminatorSig signature smp =
  SExpEliminatorSig (SExpEliminatorPred signature smp)

public export
sexpMetaEliminator :
  {0 atom : Type} -> {0 sp : SExpPred atom} ->
  {0 signature : SExpEliminatorSig sp} ->
  {0 smp : SExpMetaPred sp} ->
  (metaSig : SExpMetaEliminatorSig signature smp) ->
  SExpEliminatorPi signature smp
sexpMetaEliminator = sexpEliminator

public export
sexpMetaComposedSigEliminator :
  {0 atom : Type} ->
  {0 f : Type -> Type} -> {0 app : Applicative f} ->
  {0 sp : SExpPred atom} ->
  {0 smp : SExpMetaPred (f . sp)} ->
  {0 fsignature : f (SExpEliminatorSig sp)} ->
  SExpMetaEliminatorSig (SExpSignatureComposeSig app fsignature) smp ->
  SExpEliminatorPi (SExpSignatureComposeSig app fsignature) smp
sexpMetaComposedSigEliminator {smp} = sexpMetaEliminator {smp}

public export
sexpMetaEliminatorComposeSig :
  {atom : Type} ->
  {f : Type -> Type} -> (app : Applicative f) ->
  {0 sp : SExpPred atom} ->
  {smp : SExpMetaPred sp} ->
  {signature : SExpEliminatorSig sp} ->
  f (SExpMetaEliminatorSig signature smp) ->
  SExpEliminatorPi signature (sexpMetaPredCompose f smp)
sexpMetaEliminatorComposeSig app = sexpEliminatorComposeSig app

public export
SExpConstPred : {0 atom : Type} -> Type -> SExpPred atom
SExpConstPred type _ = type

public export
sexpConstEliminator :
  {0 atom : Type} -> {0 sp : Type} ->
  (signature : SExpEliminatorSig {atom} (SExpConstPred sp)) ->
  SExp atom -> sp
sexpConstEliminator = sexpEliminator

public export
SExpPair : (atom : Type) -> Type
SExpPair atom = (SExp atom, SExp atom)

public export
SExpPairPred : (atom : Type) -> Type
SExpPairPred atom = SExpPair atom -> Type

public export
record SExpWithPairPredEliminatorSig {0 atom : Type}
  (0 sp : SExpPred atom) (0 pp : SExpPairPred atom) where
    constructor SExpWithPairPredEliminatorArgs
    atomElim : (a : atom) -> sp ($: a)
    pairElim :
      (x, x' : SExp atom) -> sp x -> sp x' -> pp (x, x') -> sp (x $. x')
    atomPairIntro :
      (a, a' : atom) -> sp ($: a) -> sp ($: a') -> pp ($: a, $: a')
    expPairIntroLeft :
      (x, x', x'' : SExp atom) -> sp x -> sp x' -> sp x'' ->
        pp (x, x') -> pp ((x $. x'), x'')
    expPairIntroRight :
      (x, x', x'' : SExp atom) -> sp x -> sp x' -> sp x'' ->
        pp (x', x'') -> pp (x, (x' $. x''))

{- XXX pair-eliminator composer -}

public export
SExpPairPi : {atom : Type} -> SExpPairPred atom -> Type
SExpPairPi pp = SExpPair atom ~> pp

public export
SExpWithPairPi : {atom : Type} ->
  (expPred : SExpPred atom) -> (pairPred : SExpPairPred atom) -> Type
SExpWithPairPi expPred pairPred = (SExpPi expPred, SExpPairPi pairPred)

public export
SExpPredWithPairPred : {0 atom : Type} ->
  SExpPred atom -> SExpPairPred atom -> SExpPred atom
SExpPredWithPairPred expPred pairPred x =
  case x of
    ($:) a => expPred ($: a)
    x $. x' => (expPred x, expPred x', expPred (x $. x'), pairPred (x, x'))

public export
SExpPredWithPairPredToPred : {0 atom : Type} ->
  {0 sp : SExpPred atom} -> {0 spp : SExpPairPred atom} ->
  {x : SExp atom} -> SExpPredWithPairPred sp spp x ->
  sp x
SExpPredWithPairPredToPred {x=($: a)} sppx = sppx
SExpPredWithPairPredToPred {x=(x' $. x'')} sppx = proj43 sppx

sexpWithPairPredPairElim : {0 atom : Type} ->
  {0 expPred : SExpPred atom} -> {0 pairPred : SExpPairPred atom} ->
  SExpWithPairPredEliminatorSig expPred pairPred ->
  (x, x' : SExp atom) ->
  SExpPredWithPairPred expPred pairPred x ->
  SExpPredWithPairPred expPred pairPred x' ->
  SExpPredWithPairPred expPred pairPred (x $. x')
sexpWithPairPredPairElim signature ($: a) ($: a') spa spa' =
  let
    spaa' = atomPairIntro signature a a' spa spa'
    spp = pairElim signature ($: a) ($: a') spa spa' spaa'
  in
  (spa, spa', spp, spaa')
sexpWithPairPredPairElim signature ($: a) (x $. x') spa spxx' =
  let
    (spx, spx', spp, pp) = spxx'
    ppxx' = expPairIntroRight signature ($: a) x x' spa spx spx' pp
    spaxx' = pairElim signature ($: a) (x $. x') spa spp ppxx'
  in
  (spa, spp, spaxx', ppxx')
sexpWithPairPredPairElim signature (x $. x') y spxx' sppy =
  let
    (spx, spx', spp, pp) = spxx'
    spy = SExpPredWithPairPredToPred sppy
    ppxy = expPairIntroLeft signature x x' y spx spx' spy pp
    spxy = pairElim signature (x $. x') y spp spy ppxy
  in
  (spp, spy, spxy, ppxy)

SExpWithPairPredSigToEliminatorSig : {0 atom : Type} ->
  {0 expPred : SExpPred atom} -> {0 pairPred : SExpPairPred atom} ->
  SExpWithPairPredEliminatorSig expPred pairPred ->
  SExpEliminatorSig (SExpPredWithPairPred expPred pairPred)
SExpWithPairPredSigToEliminatorSig signature =
  SExpEliminatorArgs
    (atomElim signature)
    (sexpWithPairPredPairElim signature)

public export
SExpPiToWithPairPi : {0 atom : Type} ->
  {0 expPred : SExpPred atom} -> {0 pairPred : SExpPairPred atom} ->
  SExpPi (SExpPredWithPairPred expPred pairPred) ->
  SExpWithPairPi expPred pairPred
SExpPiToWithPairPi forAllExp =
  (\x => SExpPredWithPairPredToPred (forAllExp x),
   \p => case p of (x', x'') => proj44 (forAllExp (x' $. x'')))

sexpWithPairPredEliminators : {0 atom : Type} ->
  {0 expPred : SExpPred atom} -> {0 pairPred : SExpPairPred atom} ->
  SExpWithPairPredEliminatorSig expPred pairPred ->
  SExpWithPairPi expPred pairPred
sexpWithPairPredEliminators signature =
  SExpPiToWithPairPi
    (sexpEliminator (SExpWithPairPredSigToEliminatorSig signature))

sexpWithPairPredEliminator : {0 atom : Type} ->
  {0 expPred : SExpPred atom} -> {0 pairPred : SExpPairPred atom} ->
  SExpWithPairPredEliminatorSig expPred pairPred ->
  SExpPi expPred
sexpWithPairPredEliminator = fst . sexpWithPairPredEliminators

spairWithPairPredEliminator : {0 atom : Type} ->
  {0 expPred : SExpPred atom} -> {0 pairPred : SExpPairPred atom} ->
  SExpWithPairPredEliminatorSig expPred pairPred ->
  SExpPairPi pairPred
spairWithPairPredEliminator = snd . sexpWithPairPredEliminators

public export
SExpForAll :
  {0 atom : Type} -> (sp : SExpPred atom) -> SExpPred atom
SExpForAll sp =
  sexpConstEliminator {sp=Type}
    (SExpEliminatorArgs
      (sp . ($:))
      (\x, x', forAll, forAll' => (sp (x $. x'), forAll, forAll')))

public export
record SExpGeneralInductionSig {0 atom : Type} (0 sp : SExpPred atom) where
  constructor SExpGeneralInductionArgs
  atomElim : (a : atom) -> sp ($: a)
  pairElim :
    (x, x' : SExp atom) -> SExpForAll sp x -> SExpForAll sp x' -> sp (x $. x')

public export
SExpGeneralInductionSigToEliminatorSig :
  {0 atom : Type} -> {0 sp : SExpPred atom} ->
  (signature : SExpGeneralInductionSig sp) ->
  SExpEliminatorSig (SExpForAll sp)
SExpGeneralInductionSigToEliminatorSig signature =
  (SExpEliminatorArgs
    (atomElim signature)
    (\x, x', forAll, forAll' =>
      (pairElim signature x x' forAll forAll', forAll, forAll')))

public export
SExpForAllBoth : {0 atom : Type} -> (sp : SExpPred atom) -> SExpPairPred atom
SExpForAllBoth sp (x, x') = (SExpForAll sp x, SExpForAll sp x')

public export
SExpForAllPi : {atom : Type} -> (sp : SExpPred atom) -> Type
SExpForAllPi = SExpPi . SExpForAll

public export
sexpGeneralInduction : {0 atom : Type} -> {0 sp : SExpPred atom} ->
  SExpGeneralInductionSig sp ->
  SExpForAllPi sp
sexpGeneralInduction = sexpEliminator . SExpGeneralInductionSigToEliminatorSig

public export
SExpForAllWithPairPred : {0 atom : Type} -> (sp : SExpPred atom) ->
  SExpPred atom
SExpForAllWithPairPred sp = SExpPredWithPairPred sp (SExpForAllBoth sp)

public export
sexpForAllApplicationsPairElim :
  {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sp : SExp atom -> Type} ->
  (x, x' : SExp atom) ->
  (SExpForAll (f . sp) x -> f (SExpForAll sp x)) ->
  (SExpForAll (f . sp) x' -> f (SExpForAll sp x')) ->
  (SExpForAllBoth (f . sp) (x, x') -> f (SExpForAllBoth sp (x, x'))) ->
  SExpForAll (f . sp) (x $. x') ->
  f (SExpForAll sp (x $. x'))
sexpForAllApplicationsPairElim {f} {isApplicative} {sp}
  x x' mapForAll mapForAll' mapForAllBoth (fsp, forAll, forAll') =
    applyTriple
      fsp
      (mapForAll forAll)
      (mapForAll' forAll')

public export
sexpForAllApplicationsPairIntroLeft :
  {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sp : SExp atom -> Type} ->
  (x, x', x'' : SExp atom) ->
  (SExpForAll (f . sp) x -> f (SExpForAll sp x)) ->
  (SExpForAll (f . sp) x' -> f (SExpForAll sp x')) ->
  (SExpForAll (f . sp) x'' -> f (SExpForAll sp x'')) ->
  (SExpForAllBoth (f . sp) (x, x') -> f (SExpForAllBoth sp (x, x'))) ->
  SExpForAllBoth (f . sp) ((x $. x'), x'') ->
  f (SExpForAllBoth sp ((x $. x'), x''))
sexpForAllApplicationsPairIntroLeft {f} {isApplicative} {sp}
  x x' x'' mapForAll mapForAll' mapForAll'' mapForAllBoth forAllBoth =
    let ((fsp, fpp), forAll'') = forAllBoth in
    applyPair (applyPair
      fsp
      (mapForAllBoth fpp))
      (mapForAll'' forAll'')

public export
sexpForAllApplicationsPairIntroRight :
  {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sp : SExp atom -> Type} ->
  (x, x', x'' : SExp atom) ->
  (SExpForAll (f . sp) x -> f (SExpForAll sp x)) ->
  (SExpForAll (f . sp) x' -> f (SExpForAll sp x')) ->
  (SExpForAll (f . sp) x'' -> f (SExpForAll sp x'')) ->
  (SExpForAllBoth (f . sp) (x', x'') -> f (SExpForAllBoth sp (x', x''))) ->
  SExpForAllBoth (f . sp) (x, (x' $. x'')) ->
  f (SExpForAllBoth sp (x, (x' $. x'')))
sexpForAllApplicationsPairIntroRight {f} {isApplicative} {sp}
  x x' x'' mapForAll mapForAll' mapForAll'' mapForAllBoth forAllBoth =
    let (forAll, fsp, fpp) = forAllBoth in
    applyTriple
      (mapForAll forAll)
      fsp
      (mapForAllBoth fpp)

public export
sexpForAllApplications :
  {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sp : SExp atom -> Type} ->
  SExpWithPairPi
    (\x => SExpForAll (f . sp) x -> f (SExpForAll sp x))
    (\p => SExpForAllBoth (f . sp) p -> f (SExpForAllBoth sp p))
sexpForAllApplications {f} {isApplicative} {sp} =
  sexpWithPairPredEliminators
    (SExpWithPairPredEliminatorArgs
      (\_ => id)
      (sexpForAllApplicationsPairElim {f} {isApplicative} {sp})
      (\a, a', _, _, fp => applyPair (fst fp) (snd fp))
      (sexpForAllApplicationsPairIntroLeft {f} {isApplicative} {sp})
      (sexpForAllApplicationsPairIntroRight {f} {isApplicative} {sp})
    )

public export
sexpForAllApply :
  {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sp : SExp atom -> Type} ->
  (x : SExp atom) -> SExpForAll (f . sp) x -> f (SExpForAll sp x)
sexpForAllApply {isApplicative} {sp} =
  fst (sexpForAllApplications {isApplicative} {sp})

public export
spairForAllApply :
  {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sp : SExp atom -> Type} ->
  (p : SExpPair atom) -> SExpForAllBoth (f . sp) p -> f (SExpForAllBoth sp p)
spairForAllApply {isApplicative} {sp} =
  snd (sexpForAllApplications {isApplicative} {sp})

{- XXX general induction composer -}

{- XXX eliminator-generated-type eliminator (with signature composer) -}

{- XXX eliminator-generated-dependent-type eliminator (w/signature composer) -}

{- XXX forall eliminator (with signature composer) -}

{- XXX enhanced-with-applicative eliminator (with signature composer) -}

public export
SExpGeneralInductionComposeSig :
  {atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sp : SExpPred atom} ->
  f (SExpGeneralInductionSig sp) ->
  SExpGeneralInductionSig (f . sp)
SExpGeneralInductionComposeSig {f} {isApplicative} {sp} signature =
  SExpGeneralInductionArgs
    (\a => dpure isApplicative (map {f} atomElim signature) a)
    (\x, x', forAll, forAll' =>
      ((dpure isApplicative
        (dpure isApplicative (map {f} pairElim signature) x) x') <*>
          (sexpForAllApply {f} {isApplicative} {sp} x forAll)) <*>
          (sexpForAllApply {f} {isApplicative} {sp} x' forAll'))

public export
sexpGeneralInductionComposeSig :
  {atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sp : SExpPred atom} ->
  f (SExpGeneralInductionSig sp) ->
  SExpForAllPi (f . sp)
sexpGeneralInductionComposeSig {f} {sp} {isApplicative} =
  sexpGeneralInduction . SExpGeneralInductionComposeSig {f} {sp} {isApplicative}

public export
SExpForAllMetaPred : {atom : Type} -> SExpPred atom -> Type
SExpForAllMetaPred sp = (x : SExp atom) -> SExpForAll sp x -> Type

public export
SExpForAllMetaPi : {atom : Type} -> {sp : SExpPred atom} ->
  SExpForAllMetaPred sp -> SExpGeneralInductionSig sp -> Type
SExpForAllMetaPi {atom} smp signature =
  (x : SExp atom) -> smp x (sexpGeneralInduction signature x)

public export
sexpForAllMetaEliminator : {atom : Type} -> {sp : SExpPred atom} ->
  {smp : SExpForAllMetaPred sp} ->
  {signature : SExpGeneralInductionSig sp} ->
  SExpMetaEliminatorSig
    (SExpGeneralInductionSigToEliminatorSig signature) smp ->
  SExpForAllMetaPi smp signature
sexpForAllMetaEliminator {smp} = sexpMetaEliminator {smp}

public export
SExpExists :
  {0 atom : Type} -> (sp : SExpPred atom) -> SExpPred atom
SExpExists sp =
  sexpConstEliminator {sp=Type}
    (SExpEliminatorArgs
      (sp . ($:))
      (\x, x', exists, exists' =>
        Either (sp (x $. x')) (Either exists exists')))

public export
SExpExistsEither : {0 atom : Type} -> (sp : SExpPred atom) -> SExpPairPred atom
SExpExistsEither sp (x, x') = Either (SExpExists sp x) (SExpExists sp x')

public export
NonEmptySList : Type -> Type
NonEmptySList atom = NonEmptyList (SExp atom)

public export
SExpExistsSome : {0 atom : Type} -> SExpPred atom -> SExpPred atom
SExpExistsSome sp = NonEmptyList . SExpExists sp

public export
SExpDecForAll : {0 atom : Type} -> (sp : SExpPred atom) -> SExpPred atom
SExpDecForAll sp x = Either (SExpForAll sp x) (SExpExistsSome (Not . sp) x)

public export
sexpMap : {0 a, b : Type} -> (a -> b) -> (SExp a -> SExp b)
sexpMap f = sexpEliminator (SExpEliminatorArgs (($:) . f) (const (const ($.))))

public export
Functor SExp where
  map = sexpMap

public export
sexpApplyToAtom : {0 a, b : Type} -> SExp (a -> b) -> a -> SExp b
sexpApplyToAtom =
  sexpEliminator
    (SExpEliminatorArgs ((.) ($:)) (\_, _, app, app', v => (app v $. app' v)))

public export
sexpApply : {0 a, b : Type} -> SExp (a -> b) -> SExp a -> SExp b
sexpApply xab =
  sexpEliminator (SExpEliminatorArgs (sexpApplyToAtom xab) (\_, _ => ($.)))

Applicative SExp where
  pure = ($:)
  (<*>) = sexpApply

public export
sexpJoin : {0 a : Type} -> SExp (SExp a) -> SExp a
sexpJoin = sexpConstEliminator (SExpEliminatorArgs id (\_, _ => ($.)))

Monad SExp where
  join = sexpJoin

public export
sexpFoldR : {0 elem, acc : Type} ->
  (elem -> acc -> acc) -> acc -> SExp elem -> acc
sexpFoldR f = flip (sexpConstEliminator (SExpEliminatorArgs f (\_, _ => (.))))

Foldable SExp where
  foldr = sexpFoldR

public export
applySExpPair :
  {0 f : Type -> Type} -> Applicative f => {0 a : Type} ->
  f (SExp a) -> f (SExp a) -> f (SExp a)
applySExpPair fa fa' = map ($..) (applyPair fa fa')

sexpTraverse : {0 a, b : Type} -> {0 f : Type -> Type} ->
  Applicative f => (a -> f b) ->
  SExp a -> f (SExp b)
sexpTraverse {f} g =
  sexpEliminator (SExpEliminatorArgs (map ($:) . g) (\_, _ => applySExpPair))

Traversable SExp where
  traverse = sexpTraverse
