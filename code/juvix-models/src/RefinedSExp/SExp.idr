module RefinedSExp.SExp

import public Library.FunctionsAndRelations
import public Library.Decidability
import public RefinedSExp.List
import public Data.SortedMap
import public Data.SortedSet
import public Data.Vect

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
sexpForAllHead : {0 atom : Type} -> {sp : SPred atom} -> {x : SExp atom} ->
  SExpForAll sp x -> sp x
sexpForAllHead {x=(_ $* _)} = fst

public export
sexpForAllTail : {0 atom : Type} -> {sp : SPred atom} ->
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
  {atom : Type} -> {sp : SPred atom} ->
  SExpForAllEliminatorSig sp ->
  SExpEliminatorSig (SExpForAll sp) (SListForAll sp)
SExpForAllEliminatorSigToEliminatorSig {sp} signature =
  SExpEliminatorArgs {sp=(SExpForAll sp)} {lp=(SListForAll sp)}
    (\a, l, forAll => (expElim signature a l forAll, forAll))
    ()
    (\_, _ => MkPair)

public export
sexpForAllEliminator :
  {atom : Type} -> {sp : SPred atom} ->
  (signature : SExpForAllEliminatorSig sp) ->
  SExp atom ~> SExpForAll sp
sexpForAllEliminator signature =
  sexpEliminator (SExpForAllEliminatorSigToEliminatorSig signature)

public export
slistForAllEliminator :
  {atom : Type} -> {sp : SPred atom} ->
  (signature : SExpForAllEliminatorSig sp) ->
  SList atom ~> SListForAll sp
slistForAllEliminator signature =
  slistEliminator (SExpForAllEliminatorSigToEliminatorSig signature)

public export
sexpGeneralInduction :
  {atom : Type} -> {sp : SPred atom} ->
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
  {atom : Type} (sp : SPred atom)
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
  {atom : Type} -> {sp : SPred atom} ->
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
  (m : Type -> Type) {mMonad : Monad m}
  {atom : Type} (spl, spr : SPred atom) (lpl, lpr : SLPred atom)
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
  {m : Type -> Type} -> {mMonad : Monad m} ->
  {atom : Type} -> {spl, spr : SPred atom} -> {lpl, lpr : SLPred atom} ->
  SExpEitherInductionSig m {mMonad} spl spr lpl lpr ->
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
  {m : Type -> Type} -> {mMonad : Monad m} ->
  {atom : Type} -> {spl, spr : SPred atom} -> {lpl, lpr : SLPred atom} ->
  (signature : SExpEitherInductionSig m {mMonad} spl spr lpl lpr) ->
  (x : SExp atom) -> m $ Either (spl x) (spr x)
sexpEitherInduction signature =
  sexpEliminator (SExpEitherInductionSigToEliminatorSig signature)

public export
fromVoid : (type : Type) -> Void -> type
fromVoid _ = \v => void v

public export
toUnit : (type : Type) -> type -> ()
toUnit _ = \_ => ()

public export
SExpFlatMatch : Type -> Type
SExpFlatMatch atom = (() -> atom, List (SExp atom -> ()))

public export
SExpFlatMatchElim : {atom : Type} -> SExpFlatMatch atom -> Type -> Type
SExpFlatMatchElim {atom} (genericAtom, expMatchers) type =
  (l : SList atom) -> length l = length expMatchers -> type

public export
SExpFlatMatches : {atom : Type} -> SExpFlatMatch atom -> SExp atom -> Type
SExpFlatMatches {atom} (genericAtom, expMatchers) (a $* l) =
  (a = genericAtom (), length l = length expMatchers)

{-
public export
sexpFlatMatch : {atom, type: Type} -> {match : SExpFlatMatch atom} ->
  SExpFlatMatchElim match type ->
  (x : SExp atom) -> SExpFlatMatches match x -> type
sexpFlatMatch elim x matches = sexpFlatMatch_hole
-}

public export
SExpFlatRefinement : Type -> Type
SExpFlatRefinement = List . SExpFlatMatch

public export
SExpFlatRefinementElim : {atom : Type} ->
  SExpFlatRefinement atom -> Type -> Type
SExpFlatRefinementElim refinement =
  (flip ListForAll refinement) . (flip SExpFlatMatchElim)

public export
SExpFlatRefined : {atom : Type} -> SExpFlatRefinement atom -> SExp atom -> Type
SExpFlatRefined [] _ = Void
SExpFlatRefined (firstMatch :: laterMatches) x =
  Either (SExpFlatMatches firstMatch x) (SExpFlatRefined laterMatches x)

{-
public export
sexpFlatRefine : {atom, type : Type} ->
  {refinement : SExpFlatRefinement atom} ->
  SExpFlatRefinementElim refinement type ->
  (x : SExp atom) -> SExpFlatRefined refinement x -> type
sexpFlatRefine elim x refined = sexpFlatRefine_hole
-}

mutual
  infixr 7 $~:
  public export
  data STelescope :
    {0 fieldRepresentationAtom : Type} ->
    (0 fieldType :
      SExp fieldRepresentationAtom -> List (SList fieldRepresentationAtom) ->
      Type) ->
    (representation : SList fieldRepresentationAtom) ->
    (contexts : List $ SList fieldRepresentationAtom) ->
    Type where
      ($~|) :
        {0 fieldRepresentationAtom : Type} ->
        {0 fieldType :
          SExp fieldRepresentationAtom ->
          List (SList fieldRepresentationAtom) ->
          Type} ->
        {contexts : List $ SList fieldRepresentationAtom} ->
        STelescope fieldType [] contexts
      ($~:) :
        {0 fieldRepresentationAtom : Type} ->
        {0 fieldType :
          SExp fieldRepresentationAtom ->
          List (SList fieldRepresentationAtom) ->
          Type} ->
        {olderContexts : List $ SList fieldRepresentationAtom} ->
        {newestContext : SList fieldRepresentationAtom} ->
        {headRep : SExp fieldRepresentationAtom} ->
        {tailRep : SList fieldRepresentationAtom} ->
        fieldType headRep (newestContext :: olderContexts) ->
        STelescope fieldType tailRep
          ((newestContext ++ [headRep]) :: olderContexts) ->
        STelescope fieldType (headRep :: tailRep)
          (newestContext :: olderContexts)

infixr 7 :~:
public export
data Telescope :
  {0 fieldRepresentationType : Type} ->
  (0 fieldType :
    fieldRepresentationType -> List fieldRepresentationType -> Type) ->
  (representation : List fieldRepresentationType) ->
  (previousFields : List fieldRepresentationType) ->
  Type where
    (|~|) :
      {0 fieldRepresentationType : Type} ->
      {0 fieldType :
        fieldRepresentationType -> List fieldRepresentationType -> Type} ->
      {previousFields : List fieldRepresentationType} ->
      Telescope fieldType [] previousFields
    (:~:) :
      {0 fieldRepresentationType : Type} ->
      {0 fieldType :
        fieldRepresentationType -> List fieldRepresentationType -> Type} ->
      {previousFields : List fieldRepresentationType} ->
      {headRep : fieldRepresentationType} ->
      {tailRep : List fieldRepresentationType} ->
      fieldType headRep previousFields ->
      Telescope fieldType tailRep (previousFields ++ [headRep]) ->
      Telescope fieldType (headRep :: tailRep) previousFields

prefix 11 !~!
public export
(!~!) : {0 fieldRepresentationType : Type} ->
  {0 fieldType :
    fieldRepresentationType -> List fieldRepresentationType -> Type} ->
  {representation : fieldRepresentationType} ->
  {previousFields : List fieldRepresentationType} ->
  fieldType representation previousFields ->
  Telescope fieldType [representation] previousFields
(!~!) field = field :~: (|~|)

infixr 7 :~!
public export
(:~!) : {0 fieldRepresentationType : Type} ->
  {0 fieldType :
    fieldRepresentationType -> List fieldRepresentationType -> Type} ->
  {headRep, tailRep : fieldRepresentationType} ->
  {previousFields : List fieldRepresentationType} ->
  fieldType headRep previousFields ->
  fieldType tailRep (previousFields ++ [headRep]) ->
  Telescope fieldType [headRep, tailRep] previousFields
head :~! tail = head :~: !~! tail

public export
TelescopeTypeN :
  {0 fieldRepresentationType : Type} ->
  {fieldType :
    fieldRepresentationType -> List fieldRepresentationType -> Type} ->
  (representation : List fieldRepresentationType) ->
  (previousFields : List fieldRepresentationType) ->
  (n : Nat) ->
  {auto ok : InBounds n representation} ->
  Type
TelescopeTypeN {fieldType} representation previousFields n =
  fieldType (index n representation {ok})
    (previousFields ++ take n representation)

infixr 8 @~
public export
(@~) :
  {0 fieldRepresentationType : Type} ->
  {0 fieldType :
    fieldRepresentationType -> List fieldRepresentationType -> Type} ->
  {representation : List fieldRepresentationType} ->
  {previousFields : List fieldRepresentationType} ->
  Telescope fieldType representation previousFields ->
  (n : Nat) ->
  {auto ok : InBounds n representation} ->
  TelescopeTypeN {fieldType} representation previousFields n {ok}
(@~) {representation=(headRep :: _)} (head :~: _) Z {ok=InFirst} =
  rewrite appendNilRightNeutral previousFields in
  head
(@~) {representation=(headRep :: tailRep)}
  (field :~: telescope) (S n) {ok=(InLater _)} =
    rewrite appendAssociative previousFields [headRep] (take n tailRep) in
    telescope @~ n

public export
data KindAtom : (initialSort : Type) -> Type where
  KindAtomKind : {initialSort : Type} -> KindAtom initialSort
  KindAtomParameters : {initialSort : Type} -> KindAtom initialSort
  KindAtomArity : {initialSort : Type} -> KindAtom initialSort
  KindAtomExisting : {initialSort : Type} -> KindAtom initialSort
  KindAtomArguments : {initialSort : Type} -> KindAtom initialSort
  KindAtomStar : {initialSort : Type} -> initialSort -> KindAtom initialSort

public export
KindSExp : Type -> Type
KindSExp = SExp . KindAtom

public export
KindSList : Type -> Type
KindSList = SList . KindAtom

public export
KindParameterListRepresentation : {initialSort : Type} ->
  KindSList initialSort -> KindSExp initialSort
KindParameterListRepresentation sorts = KindAtomParameters $* sorts

public export
ArityRepresentation : {initialSort : Type} ->
  KindSList initialSort -> KindSExp initialSort
ArityRepresentation sorts = KindAtomArity $* sorts

public export
KindRepresentation : {initialSort : Type} ->
  (parameterListRepresentation, arityRepresentation : KindSList initialSort) ->
  KindSExp initialSort
KindRepresentation parameterListRepresentation arityRepresentation =
  KindAtomKind $*
    [KindParameterListRepresentation parameterListRepresentation,
     ArityRepresentation arityRepresentation]

public export
KindApplicationRepresentation : {initialSort : Type} ->
  (kindRepresentation : KindSExp initialSort) ->
  (argumentsToApply : KindSList initialSort) ->
  KindSExp initialSort
KindApplicationRepresentation kindRepresentation argumentsToApply =
  KindAtomExisting $*
    [kindRepresentation, KindAtomArguments $* argumentsToApply]

public export
StarSortRepresentation :
  {initialSort : Type} -> initialSort -> KindSExp initialSort
StarSortRepresentation sort = $^ (KindAtomStar sort)

public export
StarArityRepresentation :
  {initialSort : Type} -> initialSort -> KindSList initialSort
StarArityRepresentation sort = [StarSortRepresentation sort]

public export
StarKindRepresentation :
  {initialSort : Type} -> initialSort -> KindSExp initialSort
StarKindRepresentation sort =
   KindRepresentation [] (StarArityRepresentation sort)

mutual
  public export
  DependentKindList : {initialSort : Type} ->
    KindSList initialSort -> Type
  DependentKindList representation = Telescope DependentKind representation []

  public export
  DependentKindArity : {initialSort : Type} ->
    {parameterListRepresentation : KindSList initialSort} ->
    DependentKindList parameterListRepresentation ->
    KindSList initialSort ->
    Type
  DependentKindArity kindParameters representation =
    Telescope (DependentSort kindParameters) representation []

  public export
  data DependentKind :
    {initialSort : Type} ->
    (representation : KindSExp initialSort) ->
    (parameterListRepresentation : KindSList initialSort) ->
    Type
    where
      DependentKindSignature : {initialSort : Type} ->
        {parameterListRepresentation : KindSList initialSort} ->
        (dependentKindParameters :
          DependentKindList parameterListRepresentation) ->
        {arityRepresentation : KindSList initialSort} ->
        DependentKindArity dependentKindParameters arityRepresentation ->
        DependentKind
          (KindRepresentation parameterListRepresentation arityRepresentation)
          parameterListRepresentation

  public export
  dependentKindParameters :
    {initialSort : Type} ->
    {parameterListRepresentation : KindSList initialSort} ->
    {arityRepresentation : KindSList initialSort} ->
    (kind :
      DependentKind
        (KindRepresentation parameterListRepresentation arityRepresentation)
      parameterListRepresentation) ->
    DependentKindList parameterListRepresentation
  dependentKindParameters (DependentKindSignature params _) = params

  public export
  dependentKindArity :
    {initialSort : Type} ->
    {parameterListRepresentation : KindSList initialSort} ->
    {arityRepresentation : KindSList initialSort} ->
    (kind :
      DependentKind
        (KindRepresentation parameterListRepresentation arityRepresentation)
        parameterListRepresentation) ->
    DependentKindArity {parameterListRepresentation}
      (dependentKindParameters kind) arityRepresentation
  dependentKindArity {arityRepresentation} (DependentKindSignature _ arity) = arity

  public export
  data DependentSort :
    {initialSort : Type} ->
    {parameterListRepresentation : KindSList initialSort} ->
    (kindParameters : DependentKindList parameterListRepresentation) ->
    (representation : KindSExp initialSort) ->
    (previousSorts : KindSList initialSort) ->
    Type where
    {- -}
      DependentSortStar : {initialSort : Type} ->
        {parameterListRepresentation : KindSList initialSort} ->
        {kindParameters : DependentKindList parameterListRepresentation} ->
        {previousSorts : KindSList initialSort} ->
        (sort : initialSort) ->
        DependentSort kindParameters (StarSortRepresentation sort) previousSorts
      ApplyExistingKind :
        {initialSort : Type} ->
        {parameterListRepresentation : KindSList initialSort} ->
        {arityRepresentation : KindSList initialSort} ->
        {kind : DependentKind
          (KindRepresentation parameterListRepresentation arityRepresentation)
          parameterListRepresentation} ->
        {previousSorts : KindSList initialSort} ->
        {argumentsToApply : KindSList initialSort} ->
        KindApplication kind previousSorts argumentsToApply ->
        DependentSort
          (dependentKindParameters kind)
          (KindApplicationRepresentation
            (KindRepresentation parameterListRepresentation arityRepresentation)
            argumentsToApply)
          previousSorts
      {-
      ApplyKindParameter :
        {initialSort : Type} ->
        {parameterListRepresentation : KindSList initialSort} ->
        {kindParameters : DependentKindList parameterListRepresentation} ->
        {arityRepresentation : KindSList initialSort} ->
        (kindIndex : Nat) ->
        {auto ok : InBounds kindIndex parameterListRepresentation} ->
        {previousSorts : KindSList initialSort} ->
        {argumentsToApply : KindSList initialSort} ->
        KindApplication (kindParameters @~ kindIndex)
          previousSorts argumentsToApply ->
        DependentSort
          kindParameters
          (KindApplicationRepresentation
            (KindRepresentation parameterListRepresentation arityRepresentation)
            argumentsToApply)
          previousSorts
      -}

  public export
  data KindApplication :
    {initialSort : Type} ->
    {kindRepresentation : KindSExp initialSort} ->
    {parameterListRepresentation : KindSList initialSort} ->
    (kind : DependentKind kindRepresentation parameterListRepresentation) ->
    (previousSorts : KindSList initialSort) ->
    (argumentsToApply : KindSList initialSort) ->
    Type where

public export
DependentKindStar : {initialSort : Type} ->
  (sort : initialSort) -> DependentKind (StarKindRepresentation sort) []
DependentKindStar sort =
  DependentKindSignature (|~|) $ (!~!) (DependentSortStar sort)
