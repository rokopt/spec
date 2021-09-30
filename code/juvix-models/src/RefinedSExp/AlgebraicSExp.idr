module RefinedSExp.AlgebraicSExp

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public Category.ComputableCategories

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
data RefinedKeyword : Type where
  RKUnused : RefinedKeyword
  RKVoid : RefinedKeyword
  RKFromVoid : RefinedKeyword
  RKUnit : RefinedKeyword
  RKToUnit : RefinedKeyword

public export
rkEncode : RefinedKeyword -> Nat
rkEncode RKUnused = 0
rkEncode RKVoid = 1
rkEncode RKFromVoid = 2
rkEncode RKUnit = 3
rkEncode RKToUnit = 4

public export
rkDecode : Nat -> RefinedKeyword
rkDecode 1 = RKVoid
rkDecode 2 = RKFromVoid
rkDecode 3 = RKUnit
rkDecode 4 = RKToUnit
rkDecode _ = RKUnused

export
rkDecodeIsLeftInverse :
  IsLeftInverseOf AlgebraicSExp.rkEncode AlgebraicSExp.rkDecode
rkDecodeIsLeftInverse RKVoid = Refl
rkDecodeIsLeftInverse RKFromVoid = Refl
rkDecodeIsLeftInverse RKUnit = Refl
rkDecodeIsLeftInverse RKToUnit = Refl
rkDecodeIsLeftInverse RKUnused = Refl

export
rkEncodeIsInjective : IsInjective AlgebraicSExp.rkEncode
rkEncodeIsInjective =
  leftInverseImpliesInjective rkEncode {g=rkDecode} rkDecodeIsLeftInverse

public export
RKInjection : Injection RefinedKeyword Nat
RKInjection = (rkEncode ** rkEncodeIsInjective)

public export
RKCountable : Countable
RKCountable = (RefinedKeyword ** RKInjection)

public export
rkDecEq : DecEqPred RefinedKeyword
rkDecEq = countableEq RKCountable

public export
RefinedAtom : Type
RefinedAtom = RefinedKeyword

public export
raEncode : RefinedAtom -> Nat
raEncode = rkEncode

public export
raDecode : Nat -> RefinedAtom
raDecode = rkDecode

export
raDecodeIsLeftInverse :
  IsLeftInverseOf AlgebraicSExp.raEncode AlgebraicSExp.raDecode
raDecodeIsLeftInverse = rkDecodeIsLeftInverse

export
raEncodeIsInjective : IsInjective AlgebraicSExp.raEncode
raEncodeIsInjective = rkEncodeIsInjective

public export
RAInjection : Injection RefinedAtom Nat
RAInjection = (raEncode ** raEncodeIsInjective)

public export
RACountable : Countable
RACountable = (RefinedAtom ** RAInjection)

public export
raDecEq : DecEqPred RefinedAtom
raDecEq = rkDecEq

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
Eq RefinedSExp where
  x == x' = isYes $ rsDecEq x x'

public export
Eq RefinedSList where
  l == l' = isYes $ rslDecEq l l'

public export
RAVoid : RefinedAtom
RAVoid = RKVoid

public export
RSVoid : RefinedSExp
RSVoid = $^ RAVoid

public export
RAFromVoid : RefinedAtom
RAFromVoid = RKFromVoid

public export
RSFromVoid : (codomainRep : RefinedSExp) -> RefinedSExp
RSFromVoid codomainRep = RAFromVoid $*** codomainRep

public export
RAUnit : RefinedAtom
RAUnit = RKUnit

public export
RSUnit : RefinedSExp
RSUnit = $^ RAUnit

public export
RAToUnit : RefinedAtom
RAToUnit = RKToUnit

public export
RSToUnit : (domainRep : RefinedSExp) -> RefinedSExp
RSToUnit domainRep = RAToUnit $*** domainRep
