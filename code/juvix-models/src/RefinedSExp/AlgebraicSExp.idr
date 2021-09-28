module RefinedSExp.AlgebraicSExp

import Library.FunctionsAndRelations
import Library.Decidability
import Library.List
import Category.ComputableCategories

%default total

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
SPred atom = !- (SExp atom)

public export
SLPred : (atom : Type) -> Type
SLPred atom = !- (SList atom)

public export
record SExpEliminatorSig
  {0 atom : Type} (0 sp : SPred atom) (0 lp : SLPred atom)
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
SExpInductivePredSig : (0 atom : Type) -> Type
SExpInductivePredSig atom = SExpEliminatorSig {atom} (\_ => Type) (\_ => Type)

public export
ForAllInductivePredSig :
  {0 atom : Type} -> SPred atom -> SExpInductivePredSig atom
ForAllInductivePredSig pred =
  SExpEliminatorArgs (\a, l, lpl => (pred (a $* l), lpl)) () (\_, _, head, allTail => (head, allTail))

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
data RefinedAtom : Type where
  RAVoid : RefinedAtom
  RAFromVoid : RefinedAtom
  RAUnit : RefinedAtom
  RAToUnit : RefinedAtom
  RAIdentity : RefinedAtom
  RACompose : RefinedAtom
  RAProduct : RefinedAtom
  RACoproduct : RefinedAtom
  RAExponential : RefinedAtom
  RATuple : RefinedAtom
  RAProject : RefinedAtom
  RACase : RefinedAtom
  RAInject : RefinedAtom
  RAZero : RefinedAtom
  RASuccessor : RefinedAtom
  RANat : RefinedAtom
  RAEval : RefinedAtom
  RACurry : RefinedAtom
  RARecursive : RefinedAtom
  RAFixpoint : RefinedAtom
  RAAtom : RefinedAtom
  RARExp : RefinedAtom
  RANil : RefinedAtom
  RACons : RefinedAtom
  RARList : RefinedAtom
  RARAtom : RefinedAtom
  RACorecursive : RefinedAtom
  RACofixpoint : RefinedAtom
  RABool : RefinedAtom
  RATrue : RefinedAtom
  RAFalse : RefinedAtom
  RAIf : RefinedAtom
  RAEqual : RefinedAtom
  RARefinement : RefinedAtom
  RARefinedBy : RefinedAtom
  RAListRefinement : RefinedAtom
  RAListRefinedBy : RefinedAtom
  RAMaybe : RefinedAtom
  RAJust : RefinedAtom
  RANothing : RefinedAtom
  RAMaybeRefinement : RefinedAtom

public export
raEncode : RefinedAtom -> Nat
raEncode RAVoid = 0
raEncode RAFromVoid = 1
raEncode RAUnit = 2
raEncode RAToUnit = 3
raEncode RAIdentity = 4
raEncode RACompose = 5
raEncode RAProduct = 6
raEncode RACoproduct = 7
raEncode RAExponential = 8
raEncode RATuple = 9
raEncode RAProject = 10
raEncode RACase = 11
raEncode RAInject = 12
raEncode RAZero = 13
raEncode RASuccessor = 14
raEncode RANat = 15
raEncode RAEval = 16
raEncode RACurry = 17
raEncode RARecursive = 18
raEncode RAFixpoint = 19
raEncode RAAtom = 20
raEncode RARExp = 21
raEncode RANil = 22
raEncode RACons = 23
raEncode RARList = 24
raEncode RARAtom = 25
raEncode RACorecursive = 26
raEncode RACofixpoint = 27
raEncode RABool = 28
raEncode RATrue = 29
raEncode RAFalse = 30
raEncode RAIf = 31
raEncode RAEqual = 32
raEncode RARefinement = 33
raEncode RARefinedBy = 34
raEncode RAListRefinement = 35
raEncode RAListRefinedBy = 36
raEncode RAMaybe = 37
raEncode RAJust = 38
raEncode RANothing = 39
raEncode RAMaybeRefinement = 40

public export
raDecode : Nat -> RefinedAtom
raDecode 0 = RAVoid
raDecode 1 = RAFromVoid
raDecode 2 = RAUnit
raDecode 3 = RAToUnit
raDecode 4 = RAIdentity
raDecode 5 = RACompose
raDecode 6 = RAProduct
raDecode 7 = RACoproduct
raDecode 8 = RAExponential
raDecode 9 = RATuple
raDecode 10 = RAProject
raDecode 11 = RACase
raDecode 12 = RAInject
raDecode 13 = RAZero
raDecode 14 = RASuccessor
raDecode 15 = RANat
raDecode 16 = RAEval
raDecode 17 = RACurry
raDecode 18 = RARecursive
raDecode 19 = RAFixpoint
raDecode 20 = RAAtom
raDecode 21 = RARExp
raDecode 22 = RANil
raDecode 23 = RACons
raDecode 24 = RARList
raDecode 25 = RARAtom
raDecode 26 = RACorecursive
raDecode 27 = RACofixpoint
raDecode 28 = RABool
raDecode 29 = RATrue
raDecode 30 = RAFalse
raDecode 31 = RAIf
raDecode 32 = RAEqual
raDecode 33 = RARefinement
raDecode 34 = RARefinedBy
raDecode 35 = RAListRefinement
raDecode 36 = RAListRefinedBy
raDecode 37 = RAMaybe
raDecode 38 = RAJust
raDecode 39 = RANothing
raDecode 40 = RAMaybeRefinement
raDecode _ = RAVoid

export
raDecodeIsLeftInverse :
  IsLeftInverseOf AlgebraicSExp.raEncode AlgebraicSExp.raDecode
raDecodeIsLeftInverse RAVoid = Refl
raDecodeIsLeftInverse RAFromVoid = Refl
raDecodeIsLeftInverse RAUnit = Refl
raDecodeIsLeftInverse RAToUnit = Refl
raDecodeIsLeftInverse RAIdentity = Refl
raDecodeIsLeftInverse RACompose = Refl
raDecodeIsLeftInverse RAProduct = Refl
raDecodeIsLeftInverse RACoproduct = Refl
raDecodeIsLeftInverse RAExponential = Refl
raDecodeIsLeftInverse RATuple = Refl
raDecodeIsLeftInverse RAProject = Refl
raDecodeIsLeftInverse RACase = Refl
raDecodeIsLeftInverse RAInject = Refl
raDecodeIsLeftInverse RAZero = Refl
raDecodeIsLeftInverse RASuccessor = Refl
raDecodeIsLeftInverse RANat = Refl
raDecodeIsLeftInverse RAEval = Refl
raDecodeIsLeftInverse RACurry = Refl
raDecodeIsLeftInverse RARecursive = Refl
raDecodeIsLeftInverse RAFixpoint = Refl
raDecodeIsLeftInverse RAAtom = Refl
raDecodeIsLeftInverse RARExp = Refl
raDecodeIsLeftInverse RANil = Refl
raDecodeIsLeftInverse RACons = Refl
raDecodeIsLeftInverse RARList = Refl
raDecodeIsLeftInverse RARAtom = Refl
raDecodeIsLeftInverse RACorecursive = Refl
raDecodeIsLeftInverse RACofixpoint = Refl
raDecodeIsLeftInverse RABool = Refl
raDecodeIsLeftInverse RATrue = Refl
raDecodeIsLeftInverse RAFalse = Refl
raDecodeIsLeftInverse RAIf = Refl
raDecodeIsLeftInverse RAEqual = Refl
raDecodeIsLeftInverse RARefinement = Refl
raDecodeIsLeftInverse RARefinedBy = Refl
raDecodeIsLeftInverse RAListRefinement = Refl
raDecodeIsLeftInverse RAListRefinedBy = Refl
raDecodeIsLeftInverse RAMaybe = Refl
raDecodeIsLeftInverse RAJust = Refl
raDecodeIsLeftInverse RANothing = Refl
raDecodeIsLeftInverse RAMaybeRefinement = Refl

export
raEncodeIsInjective : IsInjective AlgebraicSExp.raEncode
raEncodeIsInjective =
  leftInverseImpliesInjective raEncode {g=raDecode} raDecodeIsLeftInverse

public export
RAInjection : Injection RefinedAtom Nat
RAInjection = (raEncode ** raEncodeIsInjective)

public export
RACountable : Countable
RACountable = (RefinedAtom ** RAInjection)

public export
raDecEq : DecEqPred RefinedAtom
raDecEq = countableEq RACountable

public export
RefinedSExp : Type
RefinedSExp = SExp RefinedAtom

public export
RefinedSList : Type
RefinedSList = SList RefinedAtom

public export
rsDecEq : DecEqPred RefinedSExp
rsDecEq = sexpDecEq raDecEq

public export
rslDecEq : DecEqPred RefinedSList
rslDecEq = slistDecEq raDecEq

public export
DecEq RefinedSExp where
  decEq = rsDecEq

public export
DecEq RefinedSList where
  decEq = rslDecEq

public export
RSVoid : RefinedSExp
RSVoid = $^ RAVoid

public export
RSFromVoid : (codomainRep : RefinedSExp) -> RefinedSExp
RSFromVoid codomainRep = RAFromVoid $*** codomainRep

public export
RSUnit : RefinedSExp
RSUnit = $^ RAUnit

public export
RSToUnit : (domainRep : RefinedSExp) -> RefinedSExp
RSToUnit domainRep = RAToUnit $*** domainRep

public export
RSIdentity : (objectRep : RefinedSExp) -> RefinedSExp
RSIdentity objectRep = RAIdentity $*** objectRep

public export
RSCompose : (leftRep, rightRep : RefinedSExp) -> RefinedSExp
RSCompose leftRep rightRep = RACompose $* [leftRep, rightRep]

public export
RSProduct : (objects : RefinedSList) -> RefinedSExp
RSProduct objects = RAProduct $* objects

public export
RSCoproduct : (objects : RefinedSList) -> RefinedSExp
RSCoproduct objects = RACoproduct $* objects

public export
RSExponential : (domain, codomain : RefinedSExp) -> RefinedSExp
RSExponential domain codomain = RAExponential $* [domain, codomain]

public export
RSTuple : (fields : RefinedSList) -> RefinedSExp
RSTuple fields = RATuple $* fields

public export
RSProject : (index : RefinedSExp) -> (products : RefinedSList) -> RefinedSExp
RSProject index products = RAProject $* index :: products

public export
RSCase : (cases : RefinedSList) -> RefinedSExp
RSCase cases = RACase $* cases

public export
RSInject : (index : RefinedSExp) -> (codomains : RefinedSList) -> RefinedSExp
RSInject index codomains = RAInject $* index :: codomains

public export
RSZero : (domainRep : RefinedSExp) -> RefinedSExp
RSZero domainRep = RAZero $*** domainRep

public export
RSSuccessor : RefinedSExp
RSSuccessor = $^ RASuccessor

public export
RSNat : RefinedSExp
RSNat = $^ RANat

public export
RSEval : (domain, codomain : RefinedSExp) -> RefinedSExp
RSEval domain codomain = RAEval $* [domain, codomain]

public export
RSCurry : (morphism : RefinedSExp) -> RefinedSExp
RSCurry morphism = RACurry $*** morphism

public export
RSAtom : (atom : RefinedAtom) -> RefinedSExp
RSAtom atom = RAAtom $**^ atom

public export
RSSExp : RefinedSExp
RSSExp = $^ RARExp

public export
RSNil : (domainRep : RefinedSExp) -> RefinedSExp
RSNil domainRep = RANil $*** domainRep

public export
RSCons : (head, tail : RefinedSExp) -> RefinedSExp
RSCons head tail = RACons $* [head, tail]

public export
RSSList : RefinedSExp
RSSList = $^ RARList

public export
RSSAtom : RefinedSExp
RSSAtom = $^ RARAtom

public export
RSBool : RefinedSExp
RSBool = $^ RABool

public export
RSTrue : (domainRep : RefinedSExp) -> RefinedSExp
RSTrue domainRep = RATrue $*** domainRep

public export
RSFalse : (domainRep : RefinedSExp) -> RefinedSExp
RSFalse domainRep = RAFalse $*** domainRep

public export
RSIf : (test, trueCase, falseCase : RefinedSExp) -> RefinedSExp
RSIf test trueCase falseCase = RAIf $* [test, trueCase, falseCase]

public export
RSEqual : (x, x': RefinedSExp) -> RefinedSExp
RSEqual x x' = RAEqual $* [x, x']

public export
RSRefinement : (subject : RefinedSExp) -> RefinedSExp
RSRefinement subject = RARefinement $*** subject

public export
RSRefinedBy : (test : RefinedSExp) -> RefinedSExp
RSRefinedBy test = RARefinedBy $*** test

public export
RSListRefinement : (subject : RefinedSList) -> RefinedSExp
RSListRefinement subject = RARefinement $* subject

public export
RSListRefinedBy : (test : RefinedSExp) -> RefinedSExp
RSListRefinedBy test = RARefinedBy $*** test

public export
RSMaybe : (objectRep : RefinedSExp) -> RefinedSExp
RSMaybe objectRep = RAMaybe $*** objectRep

public export
RSJust : (objectRep : RefinedSExp) -> RefinedSExp
RSJust objectRep = RAJust $*** objectRep

public export
RSNothing : (domainRep, codomainRep : RefinedSExp) -> RefinedSExp
RSNothing domainRep codomainRep = RANothing $* [domainRep, codomainRep]

public export
RSMaybeRefinement :
  (objectRep, testCodomainRep, testRep : RefinedSExp) -> RefinedSExp
RSMaybeRefinement objectRep testCodomainRep testRep =
  RAMaybeRefinement $* [objectRep, testCodomainRep, testRep]

mutual
  public export
  data RefinedObject : (representation : RefinedSExp) -> Type where
        RefinedVoid : RefinedObject RSVoid
        RefinedUnit : RefinedObject RSUnit
        RefinedProduct : {representations : RefinedSList} ->
          ListForAll RefinedObject representations ->
          RefinedObject (RSProduct representations)
        RefinedCoproduct : {representations : RefinedSList} ->
          ListForAll RefinedObject representations ->
          RefinedObject (RSCoproduct representations)
        RefinedExponential : {domainRep, codomainRep : RefinedSExp} ->
          RefinedObject domainRep -> RefinedObject codomainRep ->
          RefinedObject (RSExponential domainRep codomainRep)
        RefinedNat : RefinedObject RSNat
        ReflectedAtom : RefinedObject RSSAtom
        ReflectedExp : RefinedObject RSSExp
        ReflectedList : RefinedObject RSSList
        RefinedMaybe : {objectRep : RefinedSExp} ->
          RefinedObject objectRep ->
          RefinedObject (RSMaybe objectRep)
        MaybeRefinement : {objectRep, testCodomainRep, testRep : RefinedSExp} ->
          RefinedObject objectRep ->
          RefinedObject testCodomainRep ->
          RefinedMorphism testRep objectRep (RSMaybe testCodomainRep) ->
          RefinedObject (RSMaybeRefinement objectRep testCodomainRep testRep)

  public export
  data RefinedMorphism :
    (representation, domainRep, codomainRep : RefinedSExp) -> Type where
        RefinedIdentity : {objectRep : RefinedSExp} ->
          RefinedObject objectRep ->
          RefinedMorphism (RSIdentity objectRep) objectRep objectRep
        RefinedCompose : {a, b, c, leftRep, rightRep : RefinedSExp} ->
          RefinedMorphism leftRep b c ->
          RefinedMorphism rightRep a b ->
          RefinedMorphism (RSCompose leftRep rightRep) a c
        RefinedFromVoid : {codomainRep : RefinedSExp} ->
          RefinedObject codomainRep ->
          RefinedMorphism (RSFromVoid codomainRep) RSVoid codomainRep
        RefinedToUnit : {domainRep : RefinedSExp} ->
          RefinedObject domainRep ->
          RefinedMorphism (RSToUnit domainRep) domainRep RSUnit
        RefinedZero : {domainRep : RefinedSExp} ->
          RefinedObject domainRep ->
          RefinedMorphism (RSZero domainRep) domainRep RSNat
        RefinedSuccessor :
          RefinedMorphism RSSuccessor RSNat RSNat
        RefinedNil : {domainRep : RefinedSExp} ->
          RefinedObject domainRep ->
          RefinedMorphism (RSNil domainRep) domainRep RSSList
        RefinedJust : {objectRep : RefinedSExp} ->
          RefinedObject objectRep ->
          RefinedMorphism (RSJust objectRep) objectRep (RSMaybe objectRep)
        RefinedNothing : {domainRep, codomainRep : RefinedSExp} ->
          RefinedObject domainRep -> RefinedObject codomainRep ->
          RefinedMorphism
            (RSNothing domainRep codomainRep) domainRep (RSMaybe codomainRep)

  public export
  data RefinedContract :
    (representation, domainRep, codomainRep, subjectMorphismRep :
      RefinedSExp) -> Type where

mutual
  public export
  sexpAsObject : (representation : RefinedSExp) ->
    Maybe (RefinedObject representation)
  sexpAsObject (RAVoid $* []) = Just RefinedVoid
  sexpAsObject (RAUnit $* []) = Just RefinedUnit
  sexpAsObject (RAProduct $* objectReps) =
    case slistAsObjects objectReps of
      Just objects => Just (RefinedProduct objects)
      Nothing => Nothing
  sexpAsObject (RACoproduct $* objectReps) =
    case slistAsObjects objectReps of
      Just objects => Just (RefinedCoproduct objects)
      Nothing => Nothing
  sexpAsObject (RAExponential $* [domainRep, codomainRep]) =
    case (sexpAsObject domainRep, sexpAsObject codomainRep) of
      (Just domain, Just codomain) => Just (RefinedExponential domain codomain)
      _ => Nothing
  sexpAsObject (RANat $* []) = Just RefinedNat
  sexpAsObject (RARAtom $* []) = Just ReflectedAtom
  sexpAsObject (RARExp $* []) = Just ReflectedExp
  sexpAsObject (RARList $* []) = Just ReflectedList
  sexpAsObject (RAMaybe $* [objectRep]) =
    case sexpAsObject objectRep of
      Just object => Just (RefinedMaybe object)
      Nothing => Nothing
  sexpAsObject (RAMaybeRefinement $* [objectRep, testCodomainRep, testRep]) =
    case (sexpAsObject objectRep,
          sexpAsObject testCodomainRep,
          sexpAsMorphism testRep) of
      (Just object,
       Just testCodomain,
       Just (objectRep' ** (RAMaybe $* [testCodomainRep']) ** test)) =>
        case (decEq objectRep objectRep',
              decEq testCodomainRep testCodomainRep') of
                (Yes Refl, Yes Refl) =>
                  Just (MaybeRefinement object testCodomain test)
                _ => Nothing
      _ => Nothing
  sexpAsObject _ = Nothing

  public export
  SExpRepresentsObject : RefinedSExp -> Type
  SExpRepresentsObject representation = IsJust $ sexpAsObject representation

  public export
  sexpRepresentsObjectUnique : {representation : RefinedSExp} ->
    {r, r' : SExpRepresentsObject representation} ->
    r = r'
  sexpRepresentsObjectUnique {r} {r'} = IsJustUnique r r'

  public export
  slistAsObjects : (representations : RefinedSList) ->
    Maybe (ListForAll RefinedObject representations)
  slistAsObjects [] = Just ListForAllEmpty
  slistAsObjects (headRep :: tailReps) =
    case (sexpAsObject headRep, slistAsObjects tailReps) of
      (Just headObject, Just tailObjects) =>
        Just (ListForAllCons headObject tailObjects)
      _ => Nothing

  public export
  SListRepresentsObjects : RefinedSList -> Type
  SListRepresentsObjects representations =
    IsJust $ slistAsObjects representations

  public export
  slistRepresentsObjectsUnique : {representations : RefinedSList} ->
    {r, r' : SListRepresentsObjects representations} ->
    r = r'
  slistRepresentsObjectsUnique {r} {r'} = IsJustUnique r r'

  public export
  sexpAsMorphism : (representation : RefinedSExp) ->
    Maybe
      (domainRep : RefinedSExp ** codomainRep : RefinedSExp **
       RefinedMorphism representation domainRep codomainRep)
  sexpAsMorphism (RAFromVoid $* [codomainRep]) =
    case sexpAsObject codomainRep of
      Just codomain => Just (RSVoid ** codomainRep ** RefinedFromVoid codomain)
      Nothing => Nothing
  sexpAsMorphism (RAToUnit $* [domainRep]) =
    case sexpAsObject domainRep of
      Just domain => Just (domainRep ** RSUnit ** RefinedToUnit domain)
      Nothing => Nothing
  sexpAsMorphism (RAIdentity $* [objectRep]) =
    case sexpAsObject objectRep of
      Just object => Just (objectRep ** objectRep ** RefinedIdentity object)
      Nothing => Nothing
  sexpAsMorphism (RACompose $* [leftRep, rightRep]) =
    case (sexpAsMorphism leftRep, sexpAsMorphism rightRep) of
      (Just (leftDomRep ** leftCodRep ** leftMorphism),
       Just (rightDomRep ** rightCodRep ** rightMorphism)) =>
        case decEq rightCodRep leftDomRep of
          Yes Refl =>
            Just (rightDomRep ** leftCodRep **
                  RefinedCompose leftMorphism rightMorphism)
          No _ => Nothing
      _ => Nothing
  sexpAsMorphism (RAZero $* [domainRep]) =
    case sexpAsObject domainRep of
      Just domain => Just (domainRep ** RSNat ** RefinedZero domain)
      Nothing => Nothing
  sexpAsMorphism (RASuccessor $* []) = Just (RSNat ** RSNat ** RefinedSuccessor)
  sexpAsMorphism (RANil $* [domainRep]) =
    case sexpAsObject domainRep of
      Just domain => Just (domainRep ** RSSList ** RefinedNil domain)
      Nothing => Nothing
  sexpAsMorphism (RAJust $* [objectRep]) =
    case sexpAsObject objectRep of
      Just object => Just (objectRep ** RSMaybe objectRep ** RefinedJust object)
      Nothing => Nothing
  sexpAsMorphism (RANothing $* [domainRep, codomainRep]) =
    case (sexpAsObject domainRep, sexpAsObject codomainRep) of
      (Just domain, Just codomain) =>
        Just (domainRep ** RSMaybe codomainRep **
              RefinedNothing domain codomain)
      _ => Nothing
  sexpAsMorphism _ = Nothing

  public export
  SExpRepresentsMorphism : RefinedSExp -> Type
  SExpRepresentsMorphism representation = IsJust $ sexpAsMorphism representation

  public export
  sexpRepresentsMorphismUnique : {representation : RefinedSExp} ->
    {r, r' : SExpRepresentsMorphism representation} ->
    r = r'
  sexpRepresentsMorphismUnique {r} {r'} = IsJustUnique r r'

  public export
  sexpAsContract : (representation : RefinedSExp) ->
    Maybe
      (domainRep : RefinedSExp ** codomainRep : RefinedSExp **
       subjectMorphismRep : RefinedSExp **
       RefinedContract representation domainRep codomainRep subjectMorphismRep)
  sexpAsContract _ = Nothing

  public export
  SExpRepresentsContract : RefinedSExp -> Type
  SExpRepresentsContract representation = IsJust $ sexpAsContract representation

  public export
  sexpRepresentsContractUnique : {representation : RefinedSExp} ->
    {r, r' : SExpRepresentsContract representation} ->
    r = r'
  sexpRepresentsContractUnique {r} {r'} = IsJustUnique r r'

  public export
  refinedMorphismDomain :
    {representation, domainRep, codomainRep : RefinedSExp} ->
    RefinedMorphism representation domainRep codomainRep ->
    RefinedObject domainRep
  refinedMorphismDomain (RefinedIdentity object) =
    object
  refinedMorphismDomain (RefinedCompose _ right) =
    refinedMorphismDomain right
  refinedMorphismDomain (RefinedFromVoid _) = RefinedVoid
  refinedMorphismDomain (RefinedToUnit domain) = domain
  refinedMorphismDomain (RefinedZero domain) = domain
  refinedMorphismDomain RefinedSuccessor = RefinedNat
  refinedMorphismDomain (RefinedNil domain) = domain
  refinedMorphismDomain (RefinedJust object) = object
  refinedMorphismDomain (RefinedNothing domain _) = domain

  public export
  refinedMorphismCodomain :
    {representation, domainRep, codomainRep : RefinedSExp} ->
    RefinedMorphism representation domainRep codomainRep ->
    RefinedObject codomainRep
  refinedMorphismCodomain (RefinedIdentity object) =
    object
  refinedMorphismCodomain (RefinedCompose left _) =
    refinedMorphismCodomain left
  refinedMorphismCodomain (RefinedFromVoid codomain) = codomain
  refinedMorphismCodomain (RefinedToUnit _) = RefinedUnit
  refinedMorphismCodomain (RefinedZero _) = RefinedNat
  refinedMorphismCodomain RefinedSuccessor = RefinedNat
  refinedMorphismCodomain (RefinedNil _) = ReflectedList
  refinedMorphismCodomain (RefinedJust object) = RefinedMaybe object
  refinedMorphismCodomain (RefinedNothing _ codomain) = RefinedMaybe codomain

  public export
  refinedContractSubjectMorphism :
    {representation, domainRep, codomainRep, subjectMorphismRep :
      RefinedSExp} ->
    RefinedContract representation domainRep codomainRep subjectMorphismRep ->
    RefinedMorphism subjectMorphismRep domainRep codomainRep
  refinedContractSubjectMorphism _ impossible

  public export
  refinedContractDomain :
    {representation, domainRep, codomainRep, subjectMorphismRep :
      RefinedSExp} ->
    RefinedContract representation domainRep codomainRep subjectMorphismRep ->
    RefinedObject domainRep
  refinedContractDomain =
    refinedMorphismDomain . refinedContractSubjectMorphism

  public export
  refinedContractCodomain :
    {representation, domainRep, codomainRep, subjectMorphismRep :
      RefinedSExp} ->
    RefinedContract representation domainRep codomainRep subjectMorphismRep ->
    RefinedObject codomainRep
  refinedContractCodomain =
    refinedMorphismCodomain . refinedContractSubjectMorphism

mutual
  export
  sexpAsObjectComplete : {representation : RefinedSExp} ->
    (obj : RefinedObject representation) ->
    sexpAsObject representation = Just obj
  sexpAsObjectComplete RefinedVoid = Refl
  sexpAsObjectComplete RefinedUnit = Refl
  sexpAsObjectComplete (RefinedProduct objects) =
    rewrite (slistAsObjectsComplete objects) in Refl
  sexpAsObjectComplete (RefinedCoproduct objects) =
    rewrite (slistAsObjectsComplete objects) in Refl
  sexpAsObjectComplete (RefinedExponential domain codomain) =
    rewrite (sexpAsObjectComplete domain) in
    rewrite (sexpAsObjectComplete codomain) in Refl
  sexpAsObjectComplete RefinedNat = Refl
  sexpAsObjectComplete ReflectedAtom = Refl
  sexpAsObjectComplete ReflectedExp = Refl
  sexpAsObjectComplete ReflectedList = Refl
  sexpAsObjectComplete (RefinedMaybe objectRep) =
    rewrite (sexpAsObjectComplete objectRep) in Refl
  sexpAsObjectComplete
    (MaybeRefinement {objectRep} {testCodomainRep} object testCodomain test) =
      rewrite sexpAsObjectComplete object in
      rewrite sexpAsObjectComplete testCodomain in
      rewrite sexpAsMorphismComplete test in
      rewrite decEqRefl decEq objectRep in
      rewrite decEqRefl decEq testCodomainRep in
      Refl

  export
  slistAsObjectsComplete : {representations : RefinedSList} ->
    (objects : ListForAll RefinedObject representations) ->
    slistAsObjects representations = Just objects
  slistAsObjectsComplete ListForAllEmpty = Refl
  slistAsObjectsComplete {representations=(x :: l)} (ListForAllCons head tail)
    with (sexpAsObject x, slistAsObjects l) proof p
      slistAsObjectsComplete {representations=(x :: l)}
        (ListForAllCons head tail) | (Just object, Just objects) =
          let
            pFst = PairFstEq p
            pSnd = PairSndEq p
            headComplete = sexpAsObjectComplete head
            tailComplete = slistAsObjectsComplete tail
            justHeadEq = trans (sym pFst) headComplete
            justTailEq = trans (sym pSnd) tailComplete
          in
          case justHeadEq of Refl => case justTailEq of Refl => cong Just Refl
      slistAsObjectsComplete {representations=(x :: l)}
        (ListForAllCons head tail) | (Nothing, _) =
          case trans (sym (PairFstEq p)) (sexpAsObjectComplete head) of
            Refl impossible
      slistAsObjectsComplete {representations=(x :: l)}
        (ListForAllCons head tail) | (Just _, Nothing) =
          case trans (sym (PairSndEq p)) (slistAsObjectsComplete tail) of
            Refl impossible

  export
  objectRepresentationUnique : {representation : RefinedSExp} ->
    (obj, obj' : RefinedObject representation) ->
    obj = obj'
  objectRepresentationUnique {representation} obj obj' =
    let
      complete = sexpAsObjectComplete obj
      complete' = sexpAsObjectComplete obj'
    in
    justInjective $ trans (sym complete) complete'

  public export
  refinedMorphismDomainCorrect :
    {representation, domainRep, codomainRep : RefinedSExp} ->
    (morphism : RefinedMorphism representation domainRep codomainRep) ->
    sexpAsObject domainRep = Just (refinedMorphismDomain morphism)
  refinedMorphismDomainCorrect (RefinedIdentity object) =
    sexpAsObjectComplete object
  refinedMorphismDomainCorrect (RefinedCompose _ f) =
    refinedMorphismDomainCorrect f
  refinedMorphismDomainCorrect (RefinedFromVoid _) =
    Refl
  refinedMorphismDomainCorrect (RefinedToUnit domainRep) =
    sexpAsObjectComplete domainRep
  refinedMorphismDomainCorrect (RefinedZero domainRep) =
    sexpAsObjectComplete domainRep
  refinedMorphismDomainCorrect RefinedSuccessor = Refl
  refinedMorphismDomainCorrect (RefinedNil domainRep) =
    sexpAsObjectComplete domainRep
  refinedMorphismDomainCorrect (RefinedJust object) =
    sexpAsObjectComplete object
  refinedMorphismDomainCorrect (RefinedNothing domain _) =
    sexpAsObjectComplete domain

  public export
  refinedMorphismCodomainCorrect :
    {representation, domainRep, codomainRep : RefinedSExp} ->
    (morphism : RefinedMorphism representation domainRep codomainRep) ->
    sexpAsObject codomainRep = Just (refinedMorphismCodomain morphism)
  refinedMorphismCodomainCorrect (RefinedIdentity object) =
    sexpAsObjectComplete object
  refinedMorphismCodomainCorrect (RefinedCompose g _) =
    refinedMorphismCodomainCorrect g
  refinedMorphismCodomainCorrect (RefinedFromVoid codomainRep) =
    sexpAsObjectComplete codomainRep
  refinedMorphismCodomainCorrect (RefinedToUnit _) = Refl
  refinedMorphismCodomainCorrect (RefinedZero _) = Refl
  refinedMorphismCodomainCorrect RefinedSuccessor = Refl
  refinedMorphismCodomainCorrect (RefinedNil _) = Refl
  refinedMorphismCodomainCorrect (RefinedJust object) =
    rewrite (sexpAsObjectComplete object) in Refl
  refinedMorphismCodomainCorrect (RefinedNothing _ codomain) =
    rewrite (sexpAsObjectComplete codomain) in Refl

  export
  sexpAsMorphismComplete :
    {representation, domainRep, codomainRep : RefinedSExp} ->
    (morphism : RefinedMorphism representation domainRep codomainRep) ->
    sexpAsMorphism representation = Just (domainRep ** codomainRep ** morphism)
  sexpAsMorphismComplete (RefinedFromVoid codomain) =
    rewrite (refinedMorphismCodomainCorrect (RefinedFromVoid codomain)) in Refl
  sexpAsMorphismComplete (RefinedToUnit domain) =
    rewrite (refinedMorphismDomainCorrect (RefinedToUnit domain)) in Refl
  sexpAsMorphismComplete (RefinedIdentity object) =
    rewrite (refinedMorphismDomainCorrect (RefinedIdentity object)) in Refl
  sexpAsMorphismComplete (RefinedCompose {b} left right)
    with (decEq b b) proof bRefl
      sexpAsMorphismComplete (RefinedCompose {b} left right) | Yes Refl =
        rewrite (sexpAsMorphismComplete left) in
        rewrite (sexpAsMorphismComplete right) in
        rewrite bRefl in
        Refl
      sexpAsMorphismComplete (RefinedCompose {b} left right) | No neq =
        void (neq Refl)
  sexpAsMorphismComplete (RefinedZero domain) =
    rewrite (refinedMorphismDomainCorrect (RefinedZero domain)) in Refl
  sexpAsMorphismComplete RefinedSuccessor = Refl
  sexpAsMorphismComplete (RefinedNil domain) =
    rewrite (refinedMorphismDomainCorrect (RefinedNil domain)) in Refl
  sexpAsMorphismComplete (RefinedJust object) =
    rewrite (sexpAsObjectComplete object) in
    Refl
  sexpAsMorphismComplete (RefinedNothing domain codomain) =
    rewrite (sexpAsObjectComplete domain) in
    rewrite (sexpAsObjectComplete codomain) in
    Refl

  export
  morphismRepresentationUnique :
    {representation, domainRep, domainRep', codomainRep, codomainRep' :
      RefinedSExp} ->
    (morphism : RefinedMorphism representation domainRep codomainRep) ->
    (morphism' : RefinedMorphism representation domainRep' codomainRep') ->
    morphism = morphism'
  morphismRepresentationUnique morphism morphism' =
    let
      complete = sexpAsMorphismComplete morphism
      complete' = sexpAsMorphismComplete morphism'
      completeEq = justInjective $ trans (sym complete) complete'
    in
    case completeEq of Refl => Refl

mutual
  public export
  refinedContractSubjectMorphismCorrect :
    {representation, domainRep, codomainRep, subjectMorphismRep :
      RefinedSExp} ->
    (contract :
      RefinedContract
        representation domainRep codomainRep subjectMorphismRep) ->
    sexpAsMorphism subjectMorphismRep =
      Just (refinedContractSubjectMorphism morphism)
  refinedContractSubjectMorphismCorrect _ impossible

  public export
  refinedContractDomainCorrect :
    {representation, domainRep, codomainRep, subjectMorphismRep :
      RefinedSExp} ->
    (contract :
      RefinedContract
        representation domainRep codomainRep subjectMorphismRep) ->
    sexpAsObject domainRep = Just (refinedContractDomain contract)
  refinedContractDomainCorrect _ impossible

  public export
  refinedContractCodomainCorrect :
    {representation, domainRep, codomainRep, subjectMorphismRep :
      RefinedSExp} ->
    (contract :
      RefinedContract
        representation domainRep codomainRep subjectMorphismRep) ->
    sexpAsObject codomainRep = Just (refinedContractCodomain contract)
  refinedContractCodomainCorrect _ impossible

mutual
  export
  sexpAsContractComplete :
    {representation, domainRep, codomainRep, subjectMorphismRep :
      RefinedSExp} ->
    (contract :
      RefinedContract
        representation domainRep codomainRep subjectMorphismRep) ->
    sexpAsContract representation =
      Just (domainRep ** codomainRep ** subjectMorphismRep ** contract)
  sexpAsContractComplete _ impossible

  export
  contractRepresentationUnique :
    {representation, domainRep, domainRep', codomainRep, codomainRep',
      subjectMorphismRep, subjectMorphismRep' : RefinedSExp} ->
    (contract :
      RefinedContract
        representation domainRep codomainRep subjectMorphismRep) ->
    (contract' :
      RefinedContract
        representation domainRep' codomainRep' subjectMorphismRep') ->
    contract = contract'
  contractRepresentationUnique _ impossible

public export
GeneralizedElement : (objectRep : RefinedSExp) -> Type
GeneralizedElement objectRep =
  (domainRep : RefinedSExp **
   domain : RefinedObject domainRep **
   morphismRep : RefinedSExp **
   RefinedMorphism morphismRep domainRep objectRep)

public export
CategorialElement : (objectRep : RefinedSExp) -> Type
CategorialElement objectRep =
  RefinedMorphism (RSToUnit objectRep) RSUnit objectRep
