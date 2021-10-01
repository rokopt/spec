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
  RKIdentity : RefinedKeyword
  RKCompose : RefinedKeyword
  RKVoid : RefinedKeyword
  RKFromVoid : RefinedKeyword
  RKUnit : RefinedKeyword
  RKToUnit : RefinedKeyword

Show RefinedKeyword where
  show RKUnused = "RKUnused"
  show RKIdentity = "RKIdentity"
  show RKCompose = "RKCompose"
  show RKVoid = "RKVoid"
  show RKFromVoid = "RKFromVoid"
  show RKUnit = "RKUnit"
  show RKToUnit = "RKToUnit"

public export
rkEncode : RefinedKeyword -> Nat
rkEncode RKUnused = 0
rkEncode RKIdentity = 1
rkEncode RKCompose = 2
rkEncode RKVoid = 3
rkEncode RKFromVoid = 4
rkEncode RKUnit = 5
rkEncode RKToUnit = 6

public export
rkDecode : Nat -> RefinedKeyword
rkDecode 1 = RKIdentity
rkDecode 2 = RKCompose
rkDecode 3 = RKVoid
rkDecode 4 = RKFromVoid
rkDecode 5 = RKUnit
rkDecode 6 = RKToUnit
rkDecode _ = RKUnused

export
rkDecodeIsLeftInverse :
  IsLeftInverseOf AlgebraicSExp.rkEncode AlgebraicSExp.rkDecode
rkDecodeIsLeftInverse RKUnused = Refl
rkDecodeIsLeftInverse RKIdentity = Refl
rkDecodeIsLeftInverse RKCompose = Refl
rkDecodeIsLeftInverse RKVoid = Refl
rkDecodeIsLeftInverse RKFromVoid = Refl
rkDecodeIsLeftInverse RKUnit = Refl
rkDecodeIsLeftInverse RKToUnit = Refl

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
DecEq RefinedKeyword where
  decEq = rkDecEq

public export
data RefinedCustomSymbol : Type where
  RCNat : Nat -> RefinedCustomSymbol
  RCString : String -> RefinedCustomSymbol

Show RefinedCustomSymbol where
  show (RCNat n) = show n
  show (RCString s) = s

export
rcDecEq : DecEqPred RefinedCustomSymbol
rcDecEq (RCNat n) (RCNat n') = case decEq n n' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
rcDecEq (RCNat _) (RCString _) =
  No $ \eq => case eq of Refl impossible
rcDecEq (RCString _) (RCNat _) =
  No $ \eq => case eq of Refl impossible
rcDecEq (RCString s) (RCString s') = case decEq s s' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq RefinedCustomSymbol where
  decEq = rcDecEq

public export
data RefinedAtom : Type where
  RAKeyword : RefinedKeyword -> RefinedAtom
  RACustom : RefinedCustomSymbol -> RefinedAtom

Show RefinedAtom where
  show (RAKeyword k) = show k
  show (RACustom c) = show c

public export
raShow : RefinedAtom -> String
raShow = show

public export
raDecEq : DecEqPred RefinedAtom
raDecEq (RAKeyword n) (RAKeyword n') = case decEq n n' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
raDecEq (RAKeyword _) (RACustom _) =
  No $ \eq => case eq of Refl impossible
raDecEq (RACustom _) (RAKeyword _) =
  No $ \eq => case eq of Refl impossible
raDecEq (RACustom s) (RACustom s') = case decEq s s' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq RefinedAtom where
  decEq = raDecEq

public export
Eq RefinedAtom using decEqToEq where
  (==) = (==)

public export
RefinedSExp : Type
RefinedSExp = SExp RefinedAtom

public export
RefinedSList : Type
RefinedSList = SList RefinedAtom

public export
Show RefinedSExp where
  show = fst (sexpShows show)

public export
Show RefinedSList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

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
RANat : Nat -> RefinedAtom
RANat = RACustom . RCNat

public export
RSNat : Nat -> RefinedSExp
RSNat = ($^) . RANat

public export
RAString : String -> RefinedAtom
RAString = RACustom . RCString

public export
RSString : String -> RefinedSExp
RSString = ($^) . RAString

public export
atomIsNat : RefinedAtom -> Bool
atomIsNat (RACustom (RCNat _)) = True
atomIsNat _ = False

public export
atomIsString : RefinedAtom -> Bool
atomIsString (RACustom (RCString _)) = True
atomIsString _ = False

public export
RAVoid : RefinedAtom
RAVoid = RAKeyword RKVoid

public export
RSVoid : RefinedSExp
RSVoid = $^ RAVoid

public export
RAFromVoid : RefinedAtom
RAFromVoid = RAKeyword RKFromVoid

public export
RSFromVoid : (codomainRep : RefinedSExp) -> RefinedSExp
RSFromVoid codomainRep = RAFromVoid $*** codomainRep

public export
RAUnit : RefinedAtom
RAUnit = RAKeyword RKUnit

public export
RSUnit : RefinedSExp
RSUnit = $^ RAUnit

public export
RAToUnit : RefinedAtom
RAToUnit = RAKeyword RKToUnit

public export
RSToUnit : (domainRep : RefinedSExp) -> RefinedSExp
RSToUnit domainRep = RAToUnit $*** domainRep

public export
RACompose : RefinedAtom
RACompose = RAKeyword RKCompose

public export
RSCompose : (functions : RefinedSList) -> RefinedSExp
RSCompose = ($*) RACompose
