module RefinedSExp.AlgebraicSExp

import Library.FunctionsAndRelations
import Library.Decidability
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
data RefinedAtom : Type where
  RAVoid : RefinedAtom
  RAExFalso : RefinedAtom

public export
raDecEq : DecEqPred RefinedAtom
raDecEq RAVoid RAVoid = Yes Refl
raDecEq RAVoid RAExFalso = No $ \eq => case eq of Refl impossible
raDecEq RAExFalso RAVoid = No $ \eq => case eq of Refl impossible
raDecEq RAExFalso RAExFalso = Yes Refl

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
RSExFalso : (codomainRep : RefinedSExp) -> RefinedSExp
RSExFalso codomainRep = RAExFalso $*** codomainRep

mutual
  public export
  data RefinedObject : (representation : RefinedSExp) -> Type where
      RefinedVoid : RefinedObject RSVoid

  public export
  data RefinedMorphism :
    (representation, domainRep, codomainRep : RefinedSExp) -> Type where
      RefinedExFalso : (codomainRep : RefinedSExp) ->
        RefinedMorphism (RSExFalso codomainRep) RSVoid codomainRep

  public export
  data RefinedContract :
    (representation, domainRep, codomainRep, subjectMorphismRep :
      RefinedSExp) -> Type where

  public export
  sexpAsObject : (representation : RefinedSExp) ->
    Maybe (RefinedObject representation)
  sexpAsObject (RAVoid $* []) = Just RefinedVoid
  sexpAsObject _ = Nothing

  public export
  sexpAsMorphism : (representation, domainRep, codomainRep : RefinedSExp) ->
    Maybe (RefinedMorphism representation domainRep codomainRep)
  sexpAsMorphism (RAExFalso $* [codomainRep]) (RAVoid $* []) codomainRep' =
    case decEq codomainRep codomainRep' of
      Yes Refl => Just (RefinedExFalso codomainRep)
      No _ => Nothing
  sexpAsMorphism _ _ _ = Nothing

  public export
  sexpAsContract :
    (representation, domainRep, codomainRep, subjectMorphismRep :
      RefinedSExp) ->
    Maybe
      (RefinedContract representation domainRep codomainRep subjectMorphismRep)
  sexpAsContract _ _ _ _ = Nothing

  export
  sexpAsObjectComplete : {representation : RefinedSExp} ->
    (obj : RefinedObject representation) ->
    sexpAsObject representation = Just obj
  sexpAsObjectComplete RefinedVoid = Refl

  export
  sexpAsMorphismComplete :
    {representation, domainRep, codomainRep : RefinedSExp} ->
    (morphism : RefinedMorphism representation domainRep codomainRep) ->
    sexpAsMorphism representation domainRep codomainRep = Just morphism
  sexpAsMorphismComplete (RefinedExFalso codomainRep)
    with (decEq codomainRep codomainRep)
      sexpAsMorphismComplete (RefinedExFalso codomainRep) | Yes Refl =
        Refl
      sexpAsMorphismComplete (RefinedExFalso codomainRep) | No neq =
        void (neq Refl)

  export
  sexpAsContractComplete :
    {representation, domainRep, codomainRep, subjectMorphismRep :
      RefinedSExp} ->
    (morphism :
      RefinedContract
        representation domainRep codomainRep subjectMorphismRep) ->
    sexpAsContract representation = Just morphism
  sexpAsContractComplete _ impossible
