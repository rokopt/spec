module RefinedSExp.Computation

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public Category.ComputableCategories
import public Data.SortedMap

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
  Fail : Keyword
  Compose : Keyword
  Identity : Keyword
  Const : Keyword
  Tuple : Keyword
  Project : Keyword
  Enum : Keyword
  Inject : Keyword
  Eval : Keyword
  Curry : Keyword
  Fix : Keyword
  Cofix : Keyword

public export
keywordToString : Keyword -> String
keywordToString Fail = "Fail"
keywordToString Compose = "Compose"
keywordToString Identity = "Identity"
keywordToString Const = "Const"
keywordToString Tuple = "Tuple"
keywordToString Project = "Project"
keywordToString Enum = "Enum"
keywordToString Inject = "Inject"
keywordToString Eval = "Eval"
keywordToString Curry = "Curry"
keywordToString Fix = "Fix"
keywordToString Cofix = "Cofix"

public export
Show Keyword where
  show k = ":" ++ keywordToString k

public export
kEncode : Keyword -> Nat
kEncode Fail = 0
kEncode Compose = 1
kEncode Identity = 2
kEncode Const = 3
kEncode Tuple = 4
kEncode Project = 5
kEncode Enum = 6
kEncode Inject = 7
kEncode Eval = 8
kEncode Curry = 9
kEncode Fix = 10
kEncode Cofix = 11

public export
kDecode : Nat -> Keyword
kDecode 0 = Fail
kDecode 1 = Compose
kDecode 2 = Identity
kDecode 3 = Const
kDecode 4 = Tuple
kDecode 5 = Project
kDecode 6 = Enum
kDecode 7 = Inject
kDecode 8 = Eval
kDecode 9 = Curry
kDecode 10 = Fix
kDecode 11 = Cofix
kDecode _ = Fail

export
kDecodeIsLeftInverse :
  IsLeftInverseOf Computation.kEncode Computation.kDecode
kDecodeIsLeftInverse Fail = Refl
kDecodeIsLeftInverse Compose = Refl
kDecodeIsLeftInverse Identity = Refl
kDecodeIsLeftInverse Const = Refl
kDecodeIsLeftInverse Tuple = Refl
kDecodeIsLeftInverse Project = Refl
kDecodeIsLeftInverse Enum = Refl
kDecodeIsLeftInverse Inject = Refl
kDecodeIsLeftInverse Eval = Refl
kDecodeIsLeftInverse Curry = Refl
kDecodeIsLeftInverse Fix = Refl
kDecodeIsLeftInverse Cofix = Refl

export
kEncodeIsInjective : IsInjective Computation.kEncode
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
NAFail : NameAtom
NAFail = NAKeyword Fail

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
NSFail : NamedSExp
NSFail = $^ NAFail

public export
ComputableFunction : Type
ComputableFunction = NamedSList -> NamedSExp

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
NameBinding : Type
NameBinding = NamingContext Name NamedSExp

public export
NameInterpretation : Type
NameInterpretation = NamingContext Name ComputableFunction
