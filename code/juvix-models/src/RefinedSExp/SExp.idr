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
    {atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
    (signature : SExpEliminatorSig sp lp) ->
    SExp atom ~> sp
  sexpEliminator signature (a $* l) =
    expElim signature a l (slistEliminator signature l)

  public export
  slistEliminator :
    {atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
    (signature : SExpEliminatorSig sp lp) ->
    SList atom ~> lp
  slistEliminator signature [] =
    nilElim signature
  slistEliminator signature (x :: l) =
    consElim signature x l
      (sexpEliminator signature x) (slistEliminator signature l)

public export
sexpEliminators :
  {atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
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

mutual
  data SExpForAll : {0 atom : Type} -> SPred atom -> SPred atom where
    SExpAndList : {pred : SPred atom} -> pred (a $* l) -> SListForAll pred l ->
      SExpForAll pred (a $* l)

  data SListForAll : {0 atom : Type} -> SPred atom -> SLPred atom where
    SForAllNil : {pred : SPred atom} -> SListForAll pred []
    SForAllCons : {pred : SPred atom} ->
      SExpForAll pred x -> SListForAll pred l ->
      SListForAll pred (x :: l)

mutual
  data SExpExists : {0 atom : Type} -> SPred atom -> SPred atom where
    SExpThis : {pred : SPred atom} -> pred x -> SExpExists pred x
    SExpInList : {pred : SPred atom} -> SListExists pred l ->
      SExpExists pred (x $* l)

  data SListExists : {0 atom : Type} -> SPred atom -> SLPred atom where
    SExpHead : {pred : SPred atom} -> SExpExists pred x ->
      SListExists pred (x :: l)
    SExpTail : {pred : SPred atom} -> SListExists pred l ->
      SListExists pred (x :: l)

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
    (\a, l, forAll => SExpAndList (expElim signature a l forAll) forAll)
    (SForAllNil {pred=sp})
    (\_, _ => SForAllCons)

public export
sexpForAllEliminator :
  {atom : Type} -> {sp : SPred atom} ->
  (signature : SExpForAllEliminatorSig sp) ->
  SExp atom ~> SExpForAll sp
sexpForAllEliminator signature =
  sexpEliminator (SExpForAllEliminatorSigToEliminatorSig signature)

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

public export
sexpFlatMatch : {atom, type: Type} -> {match : SExpFlatMatch atom} ->
  SExpFlatMatchElim match type ->
  (x : SExp atom) -> SExpFlatMatches match x -> type
sexpFlatMatch elim x matches = ?sexpFlatMatch_hole

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

public export
sexpFlatRefine : {atom, type : Type} ->
  {refinement : SExpFlatRefinement atom} ->
  SExpFlatRefinementElim refinement type ->
  (x : SExp atom) -> SExpFlatRefined refinement x -> type
sexpFlatRefine elim x refined = ?sexpFlatRefine_hole

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
