module RefinedSExp.ScopedExp

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public Category.ComputableCategories
import public Data.SortedMap

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
SPred name = SExp name -> Type

public export
SLPred : (name : Type) -> Type
SLPred name = SList name -> Type

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

public export
data Keyword : Type where
  UnboundName : Keyword
  WithName : Keyword
  WithNameWrongArguments : Keyword
  NonFunctionalKeyword : Keyword

public export
keywordToString : Keyword -> String
keywordToString UnboundName = "UnboundName"
keywordToString WithName = "WithName"
keywordToString WithNameWrongArguments = "WithNameWrongArguments"
keywordToString NonFunctionalKeyword = "NonFunctionalKeyword"

public export
Show Keyword where
  show k = ":" ++ keywordToString k

public export
kEncode : Keyword -> Nat
kEncode UnboundName = 0
kEncode WithName = 1
kEncode WithNameWrongArguments = 2
kEncode NonFunctionalKeyword = 3

public export
kDecode : Nat -> Keyword
kDecode 0 = UnboundName
kDecode 1 = WithName
kDecode 2 = WithNameWrongArguments
kDecode 3 = NonFunctionalKeyword
kDecode _ = UnboundName

export
kDecodeIsLeftInverse :
  IsLeftInverseOf ScopedExp.kEncode ScopedExp.kDecode
kDecodeIsLeftInverse UnboundName = Refl
kDecodeIsLeftInverse WithName = Refl
kDecodeIsLeftInverse WithNameWrongArguments = Refl
kDecodeIsLeftInverse NonFunctionalKeyword = Refl

export
kEncodeIsInjective : IsInjective ScopedExp.kEncode
kEncodeIsInjective =
  leftInverseImpliesInjective kEncode {g=kDecode} kDecodeIsLeftInverse

public export
KInjection : Injection Keyword Nat
KInjection = (kEncode ** kEncodeIsInjective)

public export
KCountable : Countable
KCountable = (Keyword ** KInjection)

public export
kDecEq : DecEqPred Keyword
kDecEq = countableEq KCountable

public export
DecEq Keyword where
  decEq = kDecEq

public export
Eq Keyword using decEqToEq where
  (==) = (==)

public export
Ord Keyword where
  k < k' = kEncode k < kEncode k'

-- | Names are ways of accesssing the the context; put another way, a context
-- | is an interpretation of names.  Therefore, there is no interpretation
-- | of names outside of the notion of interpreting an S-expression:  for
-- | example, there is no inherent connection between the name "NNat 5" and
-- | the natural number 5.  The only structure that names have is a decidable
-- | equality.
public export
data Name : Type where
  NReflectedKeyword : Keyword -> Name
  NNat : Nat -> Name
  NString : String -> Name

public export
Show Name where
  show (NReflectedKeyword k) = "~" ++ keywordToString k
  show (NNat n) = show n
  show (NString s) = "'" ++ s

export
nDecEq : DecEqPred Name
nDecEq (NReflectedKeyword k) (NReflectedKeyword k') = case decEq k k' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
nDecEq (NReflectedKeyword _) (NNat _) =
  No $ \eq => case eq of Refl impossible
nDecEq (NReflectedKeyword _) (NString _) =
  No $ \eq => case eq of Refl impossible
nDecEq (NNat _) (NReflectedKeyword _) =
  No $ \eq => case eq of Refl impossible
nDecEq (NNat n) (NNat n') = case decEq n n' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
nDecEq (NNat _) (NString _) =
  No $ \eq => case eq of Refl impossible
nDecEq (NString _) (NReflectedKeyword _) =
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
  NReflectedKeyword k < NReflectedKeyword k' = k < k'
  NReflectedKeyword _ < NNat _ = True
  NReflectedKeyword _ < NString _ = True
  NNat _ < NReflectedKeyword _ = False
  NNat n < NNat n' = n < n'
  NNat _ < NString _ = True
  NString _ < NReflectedKeyword _ = False
  NString _ < NNat _ = False
  NString s < NString s' = s < s'

public export
data NameAtom : Type where
  NAKeyword : Keyword -> NameAtom
  NAName : Name -> NameAtom

public export
Show NameAtom where
  show (NAKeyword k) = show k
  show (NAName n) = show n

public export
naShow : NameAtom -> String
naShow = show

public export
naDecEq : DecEqPred NameAtom
naDecEq (NAKeyword n) (NAKeyword n') = case decEq n n' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
naDecEq (NAKeyword _) (NAName _) =
  No $ \eq => case eq of Refl impossible
naDecEq (NAName _) (NAKeyword _) =
  No $ \eq => case eq of Refl impossible
naDecEq (NAName s) (NAName s') = case decEq s s' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq NameAtom where
  decEq = naDecEq

public export
Eq NameAtom using decEqToEq where
  (==) = (==)

public export
Ord NameAtom where
  NAKeyword n < NAKeyword n' = n < n'
  NAKeyword _ < NAName _ = True
  NAName _ < NAKeyword _ = False
  NAName s < NAName s' = s < s'

public export
NAUnboundName : NameAtom
NAUnboundName = NAKeyword UnboundName

public export
NAWithName : NameAtom
NAWithName = NAKeyword WithName

public export
NAWithNameWrongArguments : NameAtom
NAWithNameWrongArguments = NAKeyword WithNameWrongArguments

public export
NANonFunctionalKeyword : NameAtom
NANonFunctionalKeyword = NAKeyword NonFunctionalKeyword

public export
NAReflectedKeyword : Keyword -> NameAtom
NAReflectedKeyword = NAName . NReflectedKeyword

public export
NANat : Nat -> NameAtom
NANat = NAName . NNat

public export
NAString : String -> NameAtom
NAString = NAName . NString

public export
NamedSExp : Type
NamedSExp = SExp NameAtom

public export
NamedSList : Type
NamedSList = SList NameAtom

public export
Show NamedSExp where
  show = fst (sexpShows show)

public export
Show NamedSList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
nsDecEq : DecEqPred NamedSExp
nsDecEq = sexpDecEq naDecEq

public export
nslDecEq : DecEqPred NamedSList
nslDecEq = slistDecEq naDecEq

public export
DecEq NamedSExp where
  decEq = nsDecEq

public export
DecEq NamedSList where
  decEq = nslDecEq

public export
Eq NamedSExp using decEqToEq where
  (==) = (==)

public export
NSUnboundName : NamedSExp
NSUnboundName = $^ NAUnboundName

public export
NSWithName : NamedSExp
NSWithName = $^ NAWithName

public export
NSWithNameWrongArguments : NamedSExp
NSWithNameWrongArguments = $^ NAWithNameWrongArguments

public export
NSNonFunctionalKeyword : NamedSExp
NSNonFunctionalKeyword = $^ NANonFunctionalKeyword

mutual
  public export
  data NamingContext : (name, term : Type) -> Type where
    ClosureMap : {name, term : Type} ->
      SortedMap name (Closure name term) -> NamingContext name term

  public export partial -- Show instance
  (Show name, Show term) => Show (NamingContext name term) where
    show (ClosureMap m) = show m

  public export
  record Closure (name, term : Type) where
    constructor NamedContext
    closureTerm : term
    closureContext : NamingContext name term

  public export partial -- Show instance
  (Show name, Show term) => Show (Closure name term) where
    show (NamedContext t c) = "(" ++ show t ++ ", " ++ show c ++ ")"

public export
NSContext : Type
NSContext = NamingContext Name NamedSExp

public export
metaInterpreterStep :
  (context : NSContext) ->
  (name : NameAtom) ->
  (arguments : NamedSList) ->
  NamedSExp
metaInterpreterStep (ClosureMap context) (NAName n) arguments =
  case lookup n context of
    Just x => ?metaInterpreterStep_hole_bound_name
    Nothing => NSUnboundName
metaInterpreterStep
  (ClosureMap context) (NAKeyword WithName) [name, definition] =
    ?metaInterpreterStep_hole_withName
metaInterpreterStep _ (NAKeyword WithName) _ =
  NSWithNameWrongArguments
metaInterpreterStep _ (NAKeyword _) _ = NSNonFunctionalKeyword

{-

public export
NSComputation : Type
NSComputation = NSContext -> NamedSList -> NamedSExp

-- | Interpret an expression as a computation.
public export
metaInterpreter : NamedSExp -> NSComputation
metaInterpreter =
  fst $ sexpEliminators $ SExpEliminatorArgs
    metaInterpreterStep
    []
    (\_, _ => (::))
-}
