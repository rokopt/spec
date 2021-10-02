module RefinedSExp.ScopedExp

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public Category.ComputableCategories

%default total

mutual
  infixr 7 $*
  public export
  data SExp : (name : Type) -> Type where
    ($*) : name -> SList name -> SExp name

  public export
  SList : (name : Type) -> Type
  SList = List . SExp

prefix 11 $^
public export
($^) : {name : Type} -> name -> SExp name
($^) n = n $* []

infixr 7 $^:
public export
($^:) : {name : Type} -> name -> SList name -> SList name
n $^: l = $^ n :: l

prefix 11 $*^
public export
($*^) : {name : Type} -> name -> SList name
($*^) n = n $^: []

prefix 11 $**
public export
($**) : {name : Type} -> SExp name -> SList name
($**) x = x :: []

infixr 7 $***
public export
($***) : {name : Type} -> name -> SExp name -> SExp name
n $*** x = n $* $** x

infixr 7 $:*
public export
($:*) : {name : Type} -> SExp name -> SExp name -> SList name
x $:* x' = x :: $** x'

infixr 7 $:^
public export
($:^) : {name : Type} -> SExp name -> name -> SList name
x $:^ n = x $:* $^ n

infixr 7 $^^
public export
($^^) : {name : Type} -> name -> name -> SList name
n $^^ n' = n $^: $*^ n'

infixr 7 $**^
public export
($**^) : {name : Type} -> name -> name -> SExp name
n $**^ n' = n $* $*^ n'

public export
SPred : (name : Type) -> Type
SPred name = !- (SExp name)

public export
SLPred : (name : Type) -> Type
SLPred name = !- (SList name)

public export
record SExpEliminatorSig
  {name : Type} (0 sp : SPred name) (0 lp : SLPred name)
  where
    constructor SExpEliminatorArgs
    expElim : (n : name) -> (l : SList name) -> lp l -> sp (n $* l)
    nilElim : lp []
    consElim : (x : SExp name) -> (l : SList name) ->
      sp x -> lp l -> lp (x :: l)

mutual
  public export
  sexpEliminator :
    {name : Type} -> {0 sp : SPred name} -> {0 lp : SLPred name} ->
    (signature : SExpEliminatorSig sp lp) ->
    SExp name ~> sp
  sexpEliminator signature (n $* l) =
    expElim signature n l (slistEliminator signature l)

  public export
  slistEliminator :
    {name : Type} -> {0 sp : SPred name} -> {0 lp : SLPred name} ->
    (signature : SExpEliminatorSig sp lp) ->
    SList name ~> lp
  slistEliminator signature [] =
    nilElim signature
  slistEliminator signature (x :: l) =
    consElim signature x l
      (sexpEliminator signature x) (slistEliminator signature l)

public export
sexpEliminators :
  {name : Type} -> {0 sp : SPred name} -> {0 lp : SLPred name} ->
  (signature : SExpEliminatorSig sp lp) ->
  (SExp name ~> sp, SList name ~> lp)
sexpEliminators signature =
  (sexpEliminator signature, slistEliminator signature)

public export
sexpShows : {name : Type} -> (showName : name -> String) ->
  (SExp name -> String, SList name -> String)
sexpShows {name} showName =
  sexpEliminators $ SExpEliminatorArgs
    (\n, l, lString => case l of
      [] => showName n
      _ :: _ => "(" ++ showName n ++ " $* " ++ lString ++ ")")
    ""
    (\_, l, sx, sl => case l of
      [] => sx
      _ :: _ => sx ++ " : " ++ sl)

mutual
  public export
  sexpDecEq :
    {0 name : Type} -> (nEq : DecEqPred name) -> DecEqPred (SExp name)
  sexpDecEq nEq (n $* l) (n' $* l') =
    case (nEq n n', slistDecEq nEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No nNeq, _) => No $ \eq => case eq of Refl => nNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl

  public export
  slistDecEq :
    {0 name : Type} -> (nEq : DecEqPred name) -> DecEqPred (SList name)
  slistDecEq nEq [] [] = Yes Refl
  slistDecEq nEq [] (x :: l) = No $ \eq => case eq of Refl impossible
  slistDecEq nEq (x :: l) [] = No $ \eq => case eq of Refl impossible
  slistDecEq nEq (x :: l) (x' :: l') =
    case (sexpDecEq nEq x x', slistDecEq nEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No xNeq, _) => No $ \eq => case eq of Refl => xNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl

-- | Names are ways of accesssing the the context; put another way, a context
-- | is an interpretation of names.  Therefore, there is no interpretation
-- | of names outside of the notion of interpreting an S-expression:  for
-- | example, there is no inherent connection between the name "NNat 5" and
-- | the natunal number 5.  The only structure that names have is a decidable
-- | equality.
public export
data Name : Type where
  NNat : Nat -> Name
  NString : String -> Name

Show Name where
  show (NNat n) = show n
  show (NString s) = s

export
nDecEq : DecEqPred Name
nDecEq (NNat n) (NNat n') = case decEq n n' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
nDecEq (NNat _) (NString _) =
  No $ \eq => case eq of Refl impossible
nDecEq (NString _) (NNat _) =
  No $ \eq => case eq of Refl impossible
nDecEq (NString s) (NString s') = case decEq s s' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq Name where
  decEq = nDecEq

public export
Eq Name using decEqToEq where
  (==) = (==)

public export
Ord Name where
  NNat n < NNat n' = n < n'
  NNat _ < NString _ = True
  NString _ < NNat _ = False
  NString s < NString s' = s < s'

public export
NamedSExp : Type
NamedSExp = SExp Name

public export
NamedSList : Type
NamedSList = SList Name

public export
Show NamedSExp where
  show = fst (sexpShows show)

public export
Show NamedSList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
nsDecEq : DecEqPred NamedSExp
nsDecEq = sexpDecEq nDecEq

public export
nslDecEq : DecEqPred NamedSList
nslDecEq = slistDecEq nDecEq

public export
DecEq NamedSExp where
  decEq = nsDecEq

public export
DecEq NamedSList where
  decEq = nslDecEq

public export
Eq NamedSExp using decEqToEq where
  (==) = (==)
