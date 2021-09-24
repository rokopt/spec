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
  sexpAsObject _ = Nothing

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
  sexpAsMorphism _ = Nothing

  public export
  sexpAsContract : (representation : RefinedSExp) ->
    Maybe
      (domainRep : RefinedSExp ** codomainRep : RefinedSExp **
       subjectMorphismRep : RefinedSExp **
       RefinedContract representation domainRep codomainRep subjectMorphismRep)
  sexpAsContract _ = Nothing

mutual
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

mutual
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

mutual
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
