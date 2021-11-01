module RefinedSExp.SExp

import public Library.FunctionsAndRelations
import public Library.Decidability
import public RefinedSExp.List
import public Data.SortedMap
import public Data.SortedSet
import public Data.Vect
import public Control.Monad.Reader
import public Control.Monad.Identity

%default total

-----------------------
---- S-expressions ----
-----------------------

-- I continue to waffle over representations.  On the whole
-- I think I like this form with an atom and a list because
-- of the separation that it expresses between composition
-- and evaluation, between functional programming and
-- metaprogramming.  I might want to port some of the
-- machinery from the PairVariant, such as the many instances
-- and the well-founded induction (both performing well-founded
-- induction on S-expressions using their size, and using
-- S-expressions to perform well-founded induction on other
-- structures using the S-expressions' shape).

mutual
  infixr 7 $*
  public export
  data SExp : (atom : Type) -> Type where
    ($*) : atom -> SList atom -> SExp atom

  public export
  SList : (atom : Type) -> Type
  SList = List . SExp

prefix 11 $$
public export
($$) : {atom : Type} -> (atom, SList atom) -> SExp atom
($$) (a, l) = a $* l

prefix 11 $:
($:) : {atom : Type} -> (SExp atom, SList atom) -> SList atom
($:) (x, l) = x :: l

prefix 11 $<
public export
($<) : {atom : Type} -> SExp atom -> atom
($<) (a $* _) = a

prefix 11 $>
public export
($>) : {atom : Type} -> SExp atom -> SList atom
($>) (_ $* l) = l

prefix 11 $<>
public export
($<>) : {atom : Type} -> SExp atom -> (atom, SList atom)
($<>) (a $* l) = (a, l)

public export
recomposeSExp : {atom : Type} -> (p : SExp atom) -> ($$) (($<>) p) = p
recomposeSExp (_ $* _) = Refl

public export
recomposeSList : {atom : Type} -> (l : SList atom) -> map ($$) (map ($<>) l) = l
recomposeSList [] = Refl
recomposeSList (x :: l) =
  rewrite recomposeSList l in rewrite recomposeSExp x in Refl

prefix 11 $^
public export
($^) : {atom : Type} -> atom -> SExp atom
($^) a = a $* []

infixr 7 $^:
public export
($^:) : {atom : Type} -> atom -> SList atom -> SList atom
a $^: l = $^ a :: l

prefix 11 $*^
public export
($*^) : {atom : Type} -> atom -> SList atom
($*^) a = a $^: []

prefix 11 $**
public export
($**) : {atom : Type} -> SExp atom -> SList atom
($**) x = x :: []

infixr 7 $***
public export
($***) : {atom : Type} -> atom -> SExp atom -> SExp atom
a $*** x = a $* $** x

infixr 7 $:*
public export
($:*) : {atom : Type} -> SExp atom -> SExp atom -> SList atom
x $:* x' = x :: $** x'

infixr 7 $:^
public export
($:^) : {atom : Type} -> SExp atom -> atom -> SList atom
x $:^ a = x $:* $^ a

infixr 7 $^^
public export
($^^) : {atom : Type} -> atom -> atom -> SList atom
a $^^ a' = a $^: $*^ a'

infixr 7 $**^
public export
($**^) : {atom : Type} -> atom -> atom -> SExp atom
a $**^ a' = a $* $*^ a'

public export
record SExpMonadEliminatorSig
  (0 m : Type -> Type) {auto 0 isMonad : Monad m}
  {0 atom : Type}
  (0 sp : !- (m $ SExp atom)) (0 lp : !- (m $ SList atom))
  where
    constructor SExpMonadEliminatorArgs
    expElim : (a : m $ atom) -> (l : m $ SList atom) ->
      lp l -> sp (map {f=m} ($*) a <*> l)
    nilElim : lp $ pure {f=m} []
    consElim : (x : m $ SExp atom) -> (l : m $ SList atom) ->
      sp x -> lp l -> lp (map {f=m} (::) x <*> l)

public export
SPred : (atom : Type) -> Type
SPred atom = SExp atom -> Type

public export
SLPred : (atom : Type) -> Type
SLPred atom = SList atom -> Type

public export
record SExpEliminatorSig
  {atom : Type} (0 sp : SPred atom) (0 lp : SLPred atom)
  where
    constructor SExpEliminatorArgs
    expElim : (a : atom) -> (l : SList atom) -> lp l -> sp (a $* l)
    nilElim : lp []
    consElim : (x : SExp atom) -> (l : SList atom) ->
      sp x -> lp l -> lp (x :: l)

mutual
  public export
  sexpEliminator :
    {0 atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
    (signature : SExpEliminatorSig sp lp) ->
    SExp atom ~> sp
  sexpEliminator signature (a $* l) =
    expElim signature a l (slistEliminator signature l)

  public export
  slistEliminator :
    {0 atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
    (signature : SExpEliminatorSig sp lp) ->
    SList atom ~> lp
  slistEliminator signature [] =
    nilElim signature
  slistEliminator signature (x :: l) =
    consElim signature x l
      (sexpEliminator signature x) (slistEliminator signature l)

public export
sexpEliminators :
  {0 atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
  (signature : SExpEliminatorSig sp lp) ->
  (SExp atom ~> sp, SList atom ~> lp)
sexpEliminators signature =
  (sexpEliminator signature, slistEliminator signature)

public export
sexpShows : {atom : Type} -> (showAtom : atom -> String) ->
  (SExp atom -> String, SList atom -> String)
sexpShows {atom} showAtom =
  sexpEliminators $ SExpEliminatorArgs
    (\a, l, lString => case l of
      [] => showAtom a
      _ :: _ => "(" ++ showAtom a ++ " $* " ++ lString ++ ")")
    ""
    (\_, l, sx, sl => case l of
      [] => sx
      _ :: _ => sx ++ " : " ++ sl)

public export
[DefaultSExpShow] (atom : Type) => Show atom => Show (SExp atom) where
  show = fst $ sexpShows show

public export
[DefaultSListShow] (atom : Type) => Show atom => Show (SList atom) where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

mutual
  public export
  sexpDecEq :
    {0 atom : Type} -> (aEq : DecEqPred atom) -> DecEqPred (SExp atom)
  sexpDecEq aEq (a $* l) (a' $* l') =
    case (aEq a a', slistDecEq aEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No aNeq, _) => No $ \eq => case eq of Refl => aNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl

  public export
  slistDecEq :
    {0 atom : Type} -> (aEq : DecEqPred atom) -> DecEqPred (SList atom)
  slistDecEq aEq [] [] = Yes Refl
  slistDecEq aEq [] (x :: l) = No $ \eq => case eq of Refl impossible
  slistDecEq aEq (x :: l) [] = No $ \eq => case eq of Refl impossible
  slistDecEq aEq (x :: l) (x' :: l') =
    case (sexpDecEq aEq x x', slistDecEq aEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No xNeq, _) => No $ \eq => case eq of Refl => xNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl

public export
[DefaultSExpDecEq] (atom : Type) => DecEq atom => DecEq (SExp atom) where
  decEq = sexpDecEq decEq

public export
[DefaultSListDecEq] (atom : Type) => DecEq atom => DecEq (SList atom) where
  decEq = slistDecEq decEq

mutual
  public export
  sexpLessThan : {0 atom : Type} -> (aLessThan : atom -> atom -> Bool) ->
    SExp atom -> SExp atom -> Bool
  sexpLessThan aLessThan (a $* l) (a' $* l') =
    if (aLessThan a a') then True else slistLessThan aLessThan l l'

  public export
  slistLessThan : {0 atom : Type} -> (aLessThan : atom -> atom -> Bool) ->
    SList atom -> SList atom -> Bool
  slistLessThan _ [] [] = False
  slistLessThan _ [] (_ :: _) = True
  slistLessThan _ (_ :: _) [] = False
  slistLessThan aLessThan (x :: l) (x' :: l') =
    if (sexpLessThan aLessThan x x') then True else slistLessThan aLessThan l l'

public export
SExpGenerateForAllSig : {0 atom : Type} -> SPred atom ->
  SExpEliminatorSig {atom} (\_ => Type) (\_ => Type)
SExpGenerateForAllSig {atom} sp =
  SExpEliminatorArgs {atom}
    (\a, l => Pair $ sp (a $* l)) () (\_, _ => Pair)

public export
SExpGenerateExistsSig : {0 atom : Type} -> SPred atom ->
  SExpEliminatorSig {atom} (\_ => Type) (\_ => Type)
SExpGenerateExistsSig {atom} sp =
  SExpEliminatorArgs {atom}
    (\a, l => Either $ sp (a $* l)) Void (\_, _ => Either)

public export
SExpForAll : {0 atom : Type} -> SPred atom -> SPred atom
SExpForAll {atom} sp = sexpEliminator (SExpGenerateForAllSig sp)

public export
SListForAll : {0 atom : Type} -> SPred atom -> SLPred atom
SListForAll {atom} sp = slistEliminator (SExpGenerateForAllSig sp)

public export
sexpForAllHead : {0 atom : Type} -> {0 sp : SPred atom} -> {x : SExp atom} ->
  SExpForAll sp x -> sp x
sexpForAllHead {x=(_ $* _)} = fst

public export
sexpForAllTail : {0 atom : Type} -> {0 sp : SPred atom} ->
  {a : atom} -> {l : SList atom} -> SExpForAll sp (a $* l) -> SListForAll sp l
sexpForAllTail = snd

public export
SExpExists : {0 atom : Type} -> SPred atom -> SPred atom
SExpExists {atom} sp = sexpEliminator (SExpGenerateExistsSig sp)

public export
SListExists : {0 atom : Type} -> SPred atom -> SLPred atom
SListExists {atom} sp = slistEliminator (SExpGenerateExistsSig sp)

public export
record SExpForAllEliminatorSig
  {atom : Type} (0 sp : SPred atom)
  where
    constructor SExpForAllEliminatorArgs
    expElim : (a : atom) -> (l : SList atom) -> SListForAll sp l -> sp (a $* l)

public export
SExpForAllEliminatorSigToEliminatorSig :
  {atom : Type} -> {0 sp : SPred atom} ->
  SExpForAllEliminatorSig sp ->
  SExpEliminatorSig (SExpForAll sp) (SListForAll sp)
SExpForAllEliminatorSigToEliminatorSig {sp} signature =
  SExpEliminatorArgs {sp=(SExpForAll sp)} {lp=(SListForAll sp)}
    (\a, l, forAll => (expElim signature a l forAll, forAll))
    ()
    (\_, _ => MkPair)

public export
sexpForAllEliminator :
  {atom : Type} -> {0 sp : SPred atom} ->
  (signature : SExpForAllEliminatorSig sp) ->
  SExp atom ~> SExpForAll sp
sexpForAllEliminator signature =
  sexpEliminator (SExpForAllEliminatorSigToEliminatorSig signature)

public export
slistForAllEliminator :
  {atom : Type} -> {0 sp : SPred atom} ->
  (signature : SExpForAllEliminatorSig sp) ->
  SList atom ~> SListForAll sp
slistForAllEliminator signature =
  slistEliminator (SExpForAllEliminatorSigToEliminatorSig signature)

public export
sexpGeneralInduction :
  {atom : Type} -> {0 sp : SPred atom} ->
  (signature : SExpForAllEliminatorSig sp) ->
  SExp atom ~> sp
sexpGeneralInduction {sp} signature x =
  sexpForAllHead {sp} (sexpForAllEliminator {sp} signature x)

-- | Allows the use of a predicate on the output of a function -- such
-- | as a proof of some correctness condition(s) -- within the induction
-- | step.  For example, a proof of correctness of the output of the
-- | previous steps might allow the induction step to avoid having to
-- | handle some case that it would not be able to handle correctly if
-- | it ever happened, but which it can prove never happens.
public export
record SExpStrengthenedInductionSig
  {atom : Type} (0 sp : SPred atom)
  (spp : (x : SExp atom) -> sp x -> Type)
  where
    constructor SExpStrengthenedInductionArgs
    expElim : (a : atom) -> (l : SList atom) ->
      SListForAll (\x => (spx : sp x ** spp x (spx))) l ->
      sp (a $* l)
    stepCorrect : (a : atom) -> (l : SList atom) ->
      (lforAll : SListForAll (\x => (spx : sp x ** spp x (spx))) l) ->
      spp (a $* l) (expElim a l lforAll)

public export
sexpGeneralStrengthenedInduction :
  {atom : Type} -> {0 sp : SPred atom} ->
  {spp : (x : SExp atom) -> sp x -> Type} ->
  (signature : SExpStrengthenedInductionSig sp spp) ->
  (x : SExp atom) -> DPair (sp x) (spp x)
sexpGeneralStrengthenedInduction signature =
  sexpGeneralInduction
    (SExpForAllEliminatorArgs $
      \a, l, lforAll =>
        (expElim signature a l lforAll ** stepCorrect signature a l lforAll)
    )

public export
record SExpEitherInductionSig
  (m : Type -> Type)
  {atom : Type} (0 spl, spr : SPred atom) (0 lpl, lpr : SLPred atom)
  where
    constructor SExpEitherInductionArgs
    leftElim : (a : atom) -> (l : SList atom) -> (mlpl : m (lpl l)) ->
      m (Either (spl (a $* l)) (spr (a $* l)))
    rightElim : (a : atom) -> (l : SList atom) -> (mlpr : m (lpr l)) ->
      m (spr (a $* l))
    nilElim : m (Either (lpl []) (lpr []))
    consLeftLeft : (x : SExp atom) -> (l : SList atom) ->
      (mspl : m (spl x)) -> (mlpl : m (lpl l)) ->
      m (Either (lpl (x :: l)) (lpr (x :: l)))
    consLeftRight : (x : SExp atom) -> (l : SList atom) ->
      (mspl : m (spl x)) -> (mlpr : m (lpr l)) -> m (lpr (x :: l))
    consRightLeft : (x : SExp atom) -> (l : SList atom) ->
      (mspr : m (spr x)) -> (mlpl : m (lpl l)) -> m (lpr (x :: l))
    consRightRight : (x : SExp atom) -> (l : SList atom) ->
      (mspr : m (spr x)) -> (mlpr : m (lpr l)) -> m (lpr (x :: l))

public export
SExpEitherInductionSigToEliminatorSig :
  {m : Type -> Type} -> Monad m =>
  {atom : Type} -> {0 spl, spr : SPred atom} -> {0 lpl, lpr : SLPred atom} ->
  SExpEitherInductionSig m spl spr lpl lpr ->
  SExpEliminatorSig
    (\x => m (Either (spl x) (spr x)))
    (\l => m (Either (lpl l) (lpr l)))
SExpEitherInductionSigToEliminatorSig signature =
  SExpEliminatorArgs
    (\a, l, mlpl => do
      listResult <- mlpl
      case listResult of
        Left listLeft => leftElim signature a l $ pure listLeft
        Right listRight => map Right $ rightElim signature a l $ pure listRight)
    (nilElim signature)
    (\x, l, mspx, mlpl => do
      expResult <- mspx
      listResult <- mlpl
      case (expResult, listResult) of
        (Left expLeft, Left listLeft) =>
          consLeftLeft signature x l (pure expLeft) (pure listLeft)
        (Left expLeft, Right listRight) =>
          map Right $
            consLeftRight signature x l (pure expLeft) (pure listRight)
        (Right expRight, Left listLeft) =>
          map Right $
            consRightLeft signature x l (pure expRight) (pure listLeft)
        (Right expRight, Right listRight) =>
          map Right $
            consRightRight signature x l (pure expRight) (pure listRight))

public export
sexpEitherInduction :
  {m : Type -> Type} -> Monad m =>
  {atom : Type} -> {0 spl, spr : SPred atom} -> {0 lpl, lpr : SLPred atom} ->
  (signature : SExpEitherInductionSig m spl spr lpl lpr) ->
  (x : SExp atom) -> m $ Either (spl x) (spr x)
sexpEitherInduction signature =
  sexpEliminator (SExpEitherInductionSigToEliminatorSig signature)

public export
slistEitherInduction :
  {m : Type -> Type} -> Monad m =>
  {atom : Type} -> {0 spl, spr : SPred atom} -> {0 lpl, lpr : SLPred atom} ->
  (signature : SExpEitherInductionSig m spl spr lpl lpr) ->
  (l : SList atom) -> m $ Either (lpl l) (lpr l)
slistEitherInduction signature =
  slistEliminator (SExpEitherInductionSigToEliminatorSig signature)

public export
record SExpRefineIntroSig
  (m : Type -> Type)
  {atom : Type} (0 spl : SPred atom) (0 lpl : SLPred atom)
  where
    constructor SExpRefineIntroArgs
    expElim : (a : atom) -> (l : SList atom) ->
      m (lpl l) -> m $ Dec (spl (a $* l))
    notListElim : (a : atom) -> (l : SList atom) ->
      m $ Not (lpl l) -> Not (spl (a $* l))
    nilElim : m $ Dec (lpl [])
    consElim : (x : SExp atom) -> (l : SList atom) ->
      m (spl x) -> m (lpl l) -> m $ Dec (lpl (x :: l))
    notHeadElim : (x : SExp atom) -> (l : SList atom) ->
      m $ Not (spl x) -> Not (lpl (x :: l))
    notTailElim : (x : SExp atom) -> (l : SList atom) ->
      m $ Not (lpl l) -> Not (lpl (x :: l))

public export
SExpRefineIntroSigToEitherSig :
  {m : Type -> Type} -> Monad m =>
  {atom : Type} -> {spl : SPred atom} -> {lpl : SLPred atom} ->
  SExpRefineIntroSig m spl lpl ->
  SExpEitherInductionSig m spl (Not . spl) lpl (Not . lpl)
SExpRefineIntroSigToEitherSig signature =
  SExpEitherInductionArgs
    (\a, l, mlpl => map decToEither $ expElim signature a l mlpl)
    (\a, l, mnlpl => notListElim signature a l <*> mnlpl)
    (map decToEither $ nilElim signature)
    (\x, l, mspx, mlpl => map decToEither $ consElim signature x l mspx mlpl)
    (\x, l, _, mnlpl => notTailElim signature x l <*> mnlpl)
    (\x, l, mnspx, _ => notHeadElim signature x l <*> mnspx)
    (\x, l, mnspx, _ => notHeadElim signature x l <*> mnspx)

public export
sexpRefineIntro  :
  {m : Type -> Type} -> Monad m =>
  {atom : Type} -> {spl : SPred atom} -> {lpl : SLPred atom} ->
  (signature : SExpRefineIntroSig m spl lpl) ->
  (x : SExp atom) -> m $ Dec (spl x)
sexpRefineIntro signature x =
  map eitherToDec $
    sexpEitherInduction (SExpRefineIntroSigToEitherSig signature) x

public export
slistRefineIntro :
  {m : Type -> Type} -> Monad m =>
  {atom : Type} -> {spl : SPred atom} -> {lpl : SLPred atom} ->
  (signature : SExpRefineIntroSig m spl lpl) ->
  (l : SList atom) -> m $ Dec (lpl l)
slistRefineIntro signature l =
  map eitherToDec $
    slistEitherInduction (SExpRefineIntroSigToEitherSig signature) l

public export
sexpRefineIntroReader  :
  {m : Type -> Type} -> Monad m => {stateType : Type} ->
  {atom : Type} -> {spl : SPred atom} -> {lpl : SLPred atom} ->
  (signature : SExpRefineIntroSig (ReaderT stateType m) spl lpl) ->
  (x : SExp atom) -> (ReaderT stateType m) $ Dec (spl x)
sexpRefineIntroReader = sexpRefineIntro

public export
slistRefineIntroReader  :
  {m : Type -> Type} -> Monad m => {stateType : Type} ->
  {atom : Type} -> {spl : SPred atom} -> {lpl : SLPred atom} ->
  (signature : SExpRefineIntroSig (ReaderT stateType m) spl lpl) ->
  (l : SList atom) -> (ReaderT stateType m) $ Dec (lpl l)
slistRefineIntroReader = slistRefineIntro

public export
SExpRefineIntroIdSig : {atom : Type} ->
  (0 spl : SPred atom) -> (0 lpl : SLPred atom) -> Type
SExpRefineIntroIdSig spl lpl =
  SExpRefineIntroSig Prelude.Basics.id spl lpl

public export
sexpRefineIntroId :
  {atom : Type} -> {spl : SPred atom} -> {lpl : SLPred atom} ->
  (signature : SExpRefineIntroIdSig spl lpl) ->
  (x : SExp atom) -> Dec (spl x)
sexpRefineIntroId signature =
  let _ = IdentityIsMonad in sexpRefineIntro signature

public export
SExpRefinedPerAtomHandler : (m : Type -> Type) ->
  {atom : Type} -> (spl : SPred atom) -> (lpl : SLPred atom) ->
  (handledAtoms : List atom) -> atom -> Type
SExpRefinedPerAtomHandler m {atom} spl lpl handledAtoms a =
  (l : SList atom) -> m (lpl l) -> ListContains handledAtoms a ->
  m $ Dec (spl (a $*l))

public export
record SExpRefinePerAtomHandlerSig
  (m : Type -> Type)
  {atom : Type} (0 spl : SPred atom) (0 lpl : SLPred atom)
  where
    constructor SExpRefinePerAtomHandlerArgs
    handledAtoms : List atom
    perAtomHandlers :
      ListForAll (SExpRefinedPerAtomHandler m spl lpl handledAtoms) handledAtoms
    handlesOnlySpecifiedAtoms : (a : atom) -> (l : SList atom) ->
      m (spl (a $* l) -> ListContains handledAtoms a)
    notListElim : (a : atom) -> (l : SList atom) ->
      m $ Not (lpl l) -> Not (spl (a $* l))
    nilElim : m $ Dec (lpl [])
    consElim : (x : SExp atom) -> (l : SList atom) ->
      m (spl x) -> m (lpl l) -> m $ Dec (lpl (x :: l))
    notHeadElim : (x : SExp atom) -> (l : SList atom) ->
      m $ Not (spl x) -> Not (lpl (x :: l))
    notTailElim : (x : SExp atom) -> (l : SList atom) ->
      m $ Not (lpl l) -> Not (lpl (x :: l))

public export
sexpRefinePerAtomExpElim : {m : Type -> Type} -> Monad m =>
  {atom : Type} -> DecEq atom =>
  {spl : SPred atom} -> {lpl : SLPred atom} ->
  SExpRefinePerAtomHandlerSig m spl lpl ->
  (a : atom) -> (l : SList atom) ->
  m (lpl l) -> m $ Dec (spl (a $* l))
sexpRefinePerAtomExpElim {m} {spl} {lpl} signature a l mlpl with
  (listContainsDec (handledAtoms signature) a)
    sexpRefinePerAtomExpElim signature a l mlpl | Yes handled =
      listForAllGet handled
        {ap=(SExpRefinedPerAtomHandler m spl lpl $ handledAtoms signature)}
        (perAtomHandlers signature) l mlpl handled
    sexpRefinePerAtomExpElim signature a l mlpl | No notHandled =
      map No $ appCompose (pure notHandled) $
        handlesOnlySpecifiedAtoms signature a l

public export
SExpRefinePerAtomHandlerSigToIntroSig :
  {m : Type -> Type} -> Monad m =>
  {atom : Type} -> DecEq atom => {spl : SPred atom} -> {lpl : SLPred atom} ->
  SExpRefinePerAtomHandlerSig m spl lpl ->
  SExpRefineIntroSig m spl lpl
SExpRefinePerAtomHandlerSigToIntroSig signature =
  SExpRefineIntroArgs
    (sexpRefinePerAtomExpElim signature)
    (notListElim signature)
    (nilElim signature)
    (consElim signature)
    (notHeadElim signature)
    (notTailElim signature)

public export
sexpRefinePerAtomHandler  :
  {m : Type -> Type} -> Monad m =>
  {atom : Type} -> DecEq atom => {spl : SPred atom} -> {lpl : SLPred atom} ->
  (signature : SExpRefinePerAtomHandlerSig m spl lpl) ->
  (x : SExp atom) -> m $ Dec (spl x)
sexpRefinePerAtomHandler signature =
  sexpRefineIntro (SExpRefinePerAtomHandlerSigToIntroSig signature)

public export
slistRefinePerAtomHandler :
  {m : Type -> Type} -> Monad m =>
  {atom : Type} -> DecEq atom => {spl : SPred atom} -> {lpl : SLPred atom} ->
  (signature : SExpRefinePerAtomHandlerSig m spl lpl) ->
  (l : SList atom) -> m $ Dec (lpl l)
slistRefinePerAtomHandler signature =
  slistRefineIntro (SExpRefinePerAtomHandlerSigToIntroSig signature)

public export
sexpRefinePerAtomHandlerReader  :
  {m : Type -> Type} -> Monad m => {stateType : Type} ->
  {atom : Type} -> DecEq atom => {spl : SPred atom} -> {lpl : SLPred atom} ->
  (signature : SExpRefinePerAtomHandlerSig (ReaderT stateType m) spl lpl) ->
  (x : SExp atom) -> (ReaderT stateType m) $ Dec (spl x)
sexpRefinePerAtomHandlerReader = sexpRefinePerAtomHandler

public export
slistRefinePerAtomHandlerReader  :
  {m : Type -> Type} -> Monad m => {stateType : Type} ->
  {atom : Type} -> DecEq atom => {spl : SPred atom} -> {lpl : SLPred atom} ->
  (signature : SExpRefinePerAtomHandlerSig (ReaderT stateType m) spl lpl) ->
  (l : SList atom) -> (ReaderT stateType m) $ Dec (lpl l)
slistRefinePerAtomHandlerReader = slistRefinePerAtomHandler
