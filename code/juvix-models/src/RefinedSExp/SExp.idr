module RefinedSExp.SExp

import Library.FunctionsAndRelations
import Library.Decidability
import Library.List
import public Category.Category

%default total

prefix 1 $:
infixr 7 $.
public export
data SExp : (0 atom : Type) -> Type where
  ($:) : atom -> SExp atom
  ($.) : SExp atom -> SExp atom -> SExp atom

public export
SExpPred : (0 atom : Type) -> Type
SExpPred atom = !- (SExp atom)

public export
SExpPi : {0 atom : Type} -> SExpPred atom -> Type
SExpPi sp = SExp atom ~> sp

public export
SExpTypeConstructor : (0 atom : Type) -> Type
SExpTypeConstructor atom = DependentTypeConstructor (SExp atom)

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
  (da : DependentApplicative f) ->
  {sp : SExpPred atom} ->
  f (SExpEliminatorSig sp) ->
  SExpEliminatorSig (f . sp)
SExpSignatureComposeSig da fsignature =
  SExpEliminatorArgs
    (dpure da (afmap {da} atomElim fsignature))
    (\x, x', fsx, fsx' =>
      afapply da (afapply da
        (dpure da (dpure da (afmap {da} pairElim fsignature) x) x') fsx) fsx')

public export
sexpEliminatorComposeSig :
  {atom : Type} ->
  {f : Type -> Type} ->
  (da : DependentApplicative f) ->
  {sp : SExpPred atom} ->
  f (SExpEliminatorSig sp) ->
  SExpPi (f . sp)
sexpEliminatorComposeSig da = sexpEliminator . SExpSignatureComposeSig da

public export
SExpPredList : (0 atom : Type) -> Type
SExpPredList atom = List (SExpPred atom)

public export
SExpParameterize : (0 atom : Type) -> Type -> Type
SExpParameterize atom type = SExpPredList atom -> type

public export
SExpParameterizedPred : (0 atom : Type) -> Type
SExpParameterizedPred atom = SExp atom -> SExpParameterize atom Type

public export
SExpParameterizedPredToPred : {0 atom : Type} ->
  (sp : SExpParameterizedPred atom) -> SExpPred atom
SExpParameterizedPredToPred sp = \x => SExpPredList atom ~> sp x

public export
SExpParameterizedEliminatorSig : {0 atom : Type} ->
  (0 sp : SExpParameterizedPred atom) -> Type
SExpParameterizedEliminatorSig sp =
  SExpEliminatorSig (SExpParameterizedPredToPred sp)

public export
SExpParameterizedPi : {0 atom : Type} ->
  (sp : SExpParameterizedPred atom) -> Type
SExpParameterizedPi = SExpPi . SExpParameterizedPredToPred

sexpParameterizedEliminator :
  {0 atom : Type} ->
  {sp : SExpParameterizedPred atom} ->
  SExpParameterizedEliminatorSig sp ->
  SExpParameterizedPi sp
sexpParameterizedEliminator = sexpEliminator

public export
SExpMetaPred : {0 atom : Type} -> (sp : SExpPred atom) -> Type
SExpMetaPred {atom} sp = (x : SExp atom) -> sp x -> Type

public export
SExpMetaPi : {0 atom : Type} -> {sp : SExpPred atom} ->
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
SExpEliminatorPi : {0 atom : Type} -> {0 sp : SExpPred atom} ->
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
  {0 f : Type -> Type} -> {0 da : DependentApplicative f} ->
  {0 sp : SExpPred atom} ->
  {0 smp : SExpMetaPred (f . sp)} ->
  {0 fsignature : f (SExpEliminatorSig sp)} ->
  SExpMetaEliminatorSig (SExpSignatureComposeSig da fsignature) smp ->
  SExpEliminatorPi (SExpSignatureComposeSig da fsignature) smp
sexpMetaComposedSigEliminator {smp} = sexpMetaEliminator {smp}

public export
sexpMetaEliminatorComposeSig :
  {atom : Type} ->
  {f : Type -> Type} -> (da : DependentApplicative f) ->
  {0 sp : SExpPred atom} ->
  {smp : SExpMetaPred sp} ->
  {signature : SExpEliminatorSig sp} ->
  f (SExpMetaEliminatorSig signature smp) ->
  SExpEliminatorPi signature (sexpMetaPredCompose f smp)
sexpMetaEliminatorComposeSig da = sexpEliminatorComposeSig da

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
SExpPair : (0 atom : Type) -> Type
SExpPair atom = (SExp atom, SExp atom)

public export
SExpPairPred : (0 atom : Type) -> Type
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
SExpPairPi : {0 atom : Type} -> SExpPairPred atom -> Type
SExpPairPi pp = SExpPair atom ~> pp

public export
SExpWithPairPi : {0 atom : Type} ->
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
SExpForAllPi : {0 atom : Type} -> (sp : SExpPred atom) -> Type
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

{- XXX
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
        -}

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

{-
  let
    eliminator =
      sexpPairEliminator
        {atomPred=
          (\a : atom => SExpForAll (f . sp) ($: a) -> f (SExpForAll sp ($: a)))}
        {pairPred=
          (\x, x' : SExp atom =>
            (SExpForAll (f . sp) x, SExpForAll (f . sp) x') ->
            f (SExpForAll sp x, SExpForAll sp x'))}
        (SExpEliminatorArgs
          (\_ => id)
          (\x, x', mapForAll, mapForAll', sp, forAll, forAll' =>
          {-
            let
              boo = mapForAll sp
            in
            -}
            ?hole)
        )
  in
  (\x, forAll => case x of
    ($:) a => forAll
    x $. x' =>
      eliminator (x $. x') (fst forAll) (fst (snd forAll)) (snd (snd forAll)))
      -}

    {-
public export
SExpGeneralInductionComposeSig :
  {f : Type -> Type} -> {da : DependentApplicative f} ->
  {atom : Type} -> {sp : SExpPred atom} ->
  f (SExpGeneralInductionSig sp) ->
  SExpGeneralInductionSig (f . sp)
SExpForAllEliminatorComposeSig {f} {da} {sp} signature =
  SExpGeneralInductionArgs
    (\a => dpure da (afmap {da} atomElim signature) a)
    (\l, flpl =>
      afapply da (dpure da (afmap {da} (listElim {sp}) signature) l)
        (slistForAllApply {f} {isApplicative=(appApplicative da)} {sp} l flpl))

public export
sexpGeneralInductionComposeSig :
  {f : Type -> Type} -> {da : DependentApplicative f} ->
  {atom : Type} -> {sp : SExpPred atom} ->
  f (SExpGeneralInductionSig sp) ->
  SForAllPis (f . sp)
sexpGeneralInductionsComposeSig {f} {sp} {da} =
  sexpGeneralInductions . SExpForAllEliminatorComposeSig {f} {sp} {da}

export
sexpGeneralInductionsComposeSigConsistent :
  {f : Type -> Type} -> {da : DependentApplicative f} ->
  {atom : Type} -> {sp : SExpPred atom} ->
  (signature : f (SExpGeneralInductionSig sp)) ->
  ((x : SExp atom) ->
    sexpForAllApply {f} {isApplicative=(appApplicative da)} {sp}
      x (sexpGeneralInduction {sp=(f . sp)}
          (SExpForAllEliminatorComposeSig {da} {sp} signature) x) =
    sexpEliminator {sps=(f . SExpForAll sp, f . SListForAll sp)}
      (SExpSignatureComposeSig {sps=(SExpForAll sp, SListForAll sp)} {da}
        (afmap {da} SExpGeneralInductionSigToEliminatorSig signature))
      x,
   (l : SList atom) ->
    slistForAllApply {f} {isApplicative=(appApplicative da)} {sp}
      l (slistForAllEliminator {sp=(f . sp)}
          (SExpForAllEliminatorComposeSig {da} {sp} signature) l) =
    slistEliminator {sps=(f . SExpForAll sp, f . SListForAll sp)}
      (SExpSignatureComposeSig {sps=(SExpForAll sp, SListForAll sp)} {da}
        (afmap {da} SExpGeneralInductionSigToEliminatorSig signature))
      l)
sexpGeneralInductionsComposeSigConsistent {da} {sp} signature =
  sexpEliminators
    {sps=
      (\x =>
        sexpForAllApply {f} {isApplicative=(appApplicative da)} {sp}
          x (sexpGeneralInduction {sp=(f . sp)}
              (SExpForAllEliminatorComposeSig {da} {sp} signature) x) =
        sexpEliminator {sps=(f . SExpForAll sp, f . SListForAll sp)}
          (SExpSignatureComposeSig {sps=(SExpForAll sp, SListForAll sp)} {da}
            (afmap {da} SExpGeneralInductionSigToEliminatorSig signature))
          x,
       \l =>
        slistForAllApply {f} {isApplicative=(appApplicative da)} {sp}
          l (slistForAllEliminator {sp=(f . sp)}
              (SExpForAllEliminatorComposeSig {da} {sp} signature) l) =
        slistEliminator {sps=(f . SExpForAll sp, f . SListForAll sp)}
          (SExpSignatureComposeSig {sps=(SExpForAll sp, SListForAll sp)} {da}
            (afmap {da} SExpGeneralInductionSigToEliminatorSig signature))
          l)}
    (SExpEliminatorArgs
      (?sexpGeneralInductionsComposeSigConsistent_hole_atomElim)
      (?sexpGeneralInductionsComposeSigConsistent_hole_listElim)
      (?sexpGeneralInductionsComposeSigConsistent_hole_nilElim)
      (?sexpGeneralInductionsComposeSigConsistent_hole_consElim)
    )

public export
SExpForAllMetaPred : {atom : Type} -> SExpPred atom -> Type
SExpForAllMetaPred sp = (x : SExp atom) -> SExpForAll sp x -> Type

public export
SListForAllMetaPred : {atom : Type} -> SExpPred atom -> Type
SListForAllMetaPred sp = (l : SList atom) -> SListForAll sp l -> Type

public export
SExpForAllMetaPreds : {atom : Type} -> SExpPred atom -> Type
SExpForAllMetaPreds sp = (SExpForAllMetaPred sp, SListForAllMetaPred sp)

public export
SExpForAllMetaPi : {atom : Type} -> {sp : SExpPred atom} ->
  SExpForAllMetaPreds sp -> SExpGeneralInductionSig sp -> Type
SExpForAllMetaPi {atom} smps signature =
  (x : SExp atom) -> fst smps x (sexpGeneralInduction signature x)

public export
SListForAllMetaPi : {atom : Type} -> {sp : SExpPred atom} ->
  SExpForAllMetaPreds sp -> SExpGeneralInductionSig sp -> Type
SListForAllMetaPi {atom} smps signature =
  (l : SList atom) -> snd smps l (slistForAllEliminator signature l)

public export
SExpForAllMetaPis : {atom : Type} -> {sp : SExpPred atom} ->
  SExpForAllMetaPreds sp -> SExpGeneralInductionSig sp -> Type
SExpForAllMetaPis smps signature =
  (SExpForAllMetaPi smps signature, SListForAllMetaPi smps signature)

public export
sexpForAllMetaEliminators : {atom : Type} -> {sp : SExpPred atom} ->
  {smps : SExpForAllMetaPreds sp} ->
  {signature : SExpGeneralInductionSig sp} ->
  SExpMetaEliminatorSig smps
    (SExpGeneralInductionSigToEliminatorSig signature) ->
  SExpForAllMetaPis smps signature
sexpForAllMetaEliminators = sexpMetaEliminators

public export
SExpExistsTypes :
  {0 atom : Type} -> SExpPred atom -> SExpPreds atom
SExpExistsTypes sp =
  sexpConstEliminators {sp=Type} {lp=Type}
    (SExpEliminatorArgs
      (sp . ($^))
      (Either . sp . ($|))
      Void
      (const (const Either)))

public export
SExpExists : {0 atom : Type} -> SExpPred atom -> SExpPred atom
SExpExists = SPredsExp . SExpExistsTypes

public export
SListExists : {0 atom : Type} -> SExpPred atom -> SListPred atom
SListExists = SPredsList . SExpExistsTypes

public export
NonEmptySList : Type -> Type
NonEmptySList atom = NonEmptyList (SExp atom)

public export
SExpExistsSome : {0 atom : Type} -> SExpPred atom -> SExpPred atom
SExpExistsSome sp = NonEmptyList . SExpExists sp

public export
SListExistsSome : {0 atom : Type} -> SExpPred atom -> SListPred atom
SListExistsSome sp = NonEmptyList . SListExists sp

public export
SExpAllLeftOrExistsRight : {0 atom : Type} -> (sr, sl : SExpPred atom) ->
  SExpPred atom
SExpAllLeftOrExistsRight sr sl x =
  Either (SExpForAll sr x) (SExpExistsSome sl x)

public export
SListAllLeftOrExistsRight : {0 atom : Type} -> (sr, sl : SExpPred atom) ->
  SListPred atom
SListAllLeftOrExistsRight sr sl l =
  Either (SListForAll sr l) (SListExistsSome sl l)

public export
slistExistsSomeShift : {0 atom : Type} ->
  {sl, sr : SExpPred atom} ->
  {x : SExp atom} -> {l : SList atom} ->
  SListExistsSome sr l ->
  SListExistsSome sr (x :: l)
slistExistsSomeShift = neListMap Right

{- XXX write signature composer for this -}
public export
record SExpConstListEliminatorSig {0 atom : Type} (sp : Type) where
  constructor SExpConstListEliminatorArgs
  atomElim : atom -> sp
  listElim : (l : SList atom) -> List sp -> sp

public export
SExpConstListEliminatorSigToEliminatorSig :
  {0 atom : Type} -> {0 sp : Type} ->
  SExpConstListEliminatorSig {atom} sp ->
  SExpEliminatorSig {atom} (const sp, const (List sp))
SExpConstListEliminatorSigToEliminatorSig {atom} signature =
  (SExpEliminatorArgs {atom}
    (atomElim signature)
    (listElim signature)
    []
    (const (const (::))))

public export
sexpConstListEliminators :
  {0 atom : Type} -> {0 sp : Type} ->
  (signature : SExpConstListEliminatorSig {atom} sp) ->
  (SExp atom -> sp, SList atom -> List sp)
sexpConstListEliminators {atom} {sp} =
  sexpEliminators . SExpConstListEliminatorSigToEliminatorSig {atom} {sp}

public export
sexpMaps : {0 a, b : Type} -> (a -> b) -> (SExp a -> SExp b, SList a -> SList b)
sexpMaps f =
  sexpConstListEliminators (SExpConstListEliminatorArgs (($^) . f) (const ($|)))

public export
sexpMap : {0 a, b : Type} -> (a -> b) -> SExp a -> SExp b
sexpMap = fst . sexpMaps

public export
slistMap : {0 a, b : Type} -> (a -> b) -> SList a -> SList b
slistMap = snd . sexpMaps

Functor SExp where
  map = sexpMap

Functor SList where
  map = slistMap

public export
sexpApplicationsToAtom : {0 a, b : Type} ->
  SExp (a -> b) ->
  a -> SExp b
sexpApplicationsToAtom xab x =
  fst
    (sexpConstListEliminators
      (SExpConstListEliminatorArgs
        (\x' => $^ (x' x))
        (const ($|))))
  xab

public export
sexpApplications : {0 a, b : Type} ->
  SExp (a -> b) ->
  (SExp a -> SExp b, SList a -> SList b)
sexpApplications xab =
  sexpConstListEliminators
    (SExpConstListEliminatorArgs
      (sexpApplicationsToAtom xab)
      (const ($|)))

public export
sexpApply : {0 a, b : Type} -> SExp (a -> b) -> SExp a -> SExp b
sexpApply xab = fst (sexpApplications xab)

public export
sexpApplyList : {0 a, b : Type} -> SExp (a -> b) -> SList a -> SList b
sexpApplyList xab = snd (sexpApplications xab)

public export
slistApply : {0 a, b : Type} -> SList (a -> b) -> SList a -> SList b
slistApply =
  listEliminator {atom=(SExp (a -> b))} {lp=const (SList a -> SList b)}
    (ListEliminatorArgs
      (const [])
      (\xab, lab, lalb, la => sexpApplyList xab la ++ lalb la))

Applicative SExp where
  pure = ($^)
  (<*>) = sexpApply

Applicative SList where
  pure x = [ ($^ x) ]
  (<*>) = slistApply
  -}
