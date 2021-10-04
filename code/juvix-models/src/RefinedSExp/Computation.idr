module RefinedSExp.Computation

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public Category.ComputableCategories
import public RefinedSExp.SExp
import public RefinedSExp.Data

%default total

public export
data Keyword : Type where
  -- | Represents failure of a general computable function application.
  Fail : Keyword
  -- | Composition of general computable functions.
  Compose : Keyword
  -- | The identity general computable function (which is total).
  Identity : Keyword
  -- | Polymorphic constant:  the constant general computable function
  -- | which always returns the parameter it's given.
  Const : Keyword
  -- | Product introduction for general compuatable functions:  form a function
  -- | which returns tuples from a tuple of functions (which must have the same
  -- | domain for this operation to make sense).
  Tuple : Keyword
  -- | Product elimination for general compuatable functions:  form a function
  -- | which returns tuples from a tuple of functions (which must have the same
  -- | domain for this operation to make sense).
  Project : Keyword
  -- | Coproduct introduction for general computable functions:  choose one
  -- | of one or more possible forms.
  Inject : Keyword
  -- | Coproduct elimination for general computable functions:  form a function
  -- | which accepts a coproduct and returns a case depending on which of the
  -- | coproduct's injections is passed in.
  Case : Keyword
  -- | The evaluation function associated with exponentials of general
  -- | computable functions.
  Eval : Keyword
  -- | The currying function associated with exponentials of general
  -- | computable functions.
  Curry : Keyword
  -- | General recursive fixpoint:  treat the input parameter to a function
  -- | as the function itself.
  Fix : Keyword
  -- | General recursive cofixpoint.
  Cofix : Keyword
  -- | Reflection:  atom introduction, forming a constant function which
  -- | returns a given atom.
  -- |
  -- | Given reflected atoms, we can fully reflect using S-expressions as
  -- | well:  an S-expression is a product, of an atom and a list of
  -- | S-expressions, and a list is a coproduct, of a constant function
  -- | ("nil" -- we can use, for example, the constant function returning
  -- | const!) and a product (of an element and a list).
  ReflectedAtom : Keyword
  -- | Decidable equality, which includes atom elimination.
  CompareAtoms : Keyword
  -- | Interpret:  a computable function whose arguments are an
  -- | S-expression and some arguments.
  Interpret : Keyword

public export
keywordToString : Keyword -> String
keywordToString Fail = "Fail"
keywordToString Compose = "Compose"
keywordToString Identity = "Identity"
keywordToString Const = "Const"
keywordToString Tuple = "Tuple"
keywordToString Project = "Project"
keywordToString Case = "Case"
keywordToString Inject = "Inject"
keywordToString Eval = "Eval"
keywordToString Curry = "Curry"
keywordToString Fix = "Fix"
keywordToString Cofix = "Cofix"
keywordToString ReflectedAtom = "ReflectedAtom"
keywordToString CompareAtoms = "CompareAtoms"
keywordToString Interpret = "Interpret"

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
kEncode Case = 6
kEncode Inject = 7
kEncode Eval = 8
kEncode Curry = 9
kEncode Fix = 10
kEncode Cofix = 11
kEncode ReflectedAtom = 12
kEncode CompareAtoms = 13
kEncode Interpret = 14

public export
kDecode : Nat -> Keyword
kDecode 0 = Fail
kDecode 1 = Compose
kDecode 2 = Identity
kDecode 3 = Const
kDecode 4 = Tuple
kDecode 5 = Project
kDecode 6 = Case
kDecode 7 = Inject
kDecode 8 = Eval
kDecode 9 = Curry
kDecode 10 = Fix
kDecode 11 = Cofix
kDecode 12 = ReflectedAtom
kDecode 13 = CompareAtoms
kDecode 14 = Interpret
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
kDecodeIsLeftInverse Case = Refl
kDecodeIsLeftInverse Inject = Refl
kDecodeIsLeftInverse Eval = Refl
kDecodeIsLeftInverse Curry = Refl
kDecodeIsLeftInverse Fix = Refl
kDecodeIsLeftInverse Cofix = Refl
kDecodeIsLeftInverse ReflectedAtom = Refl
kDecodeIsLeftInverse CompareAtoms = Refl
kDecodeIsLeftInverse Interpret = Refl

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

public export
data ComputeAtom : Type where
  CAKeyword : Keyword -> ComputeAtom
  CAData : Data -> ComputeAtom

public export
Show ComputeAtom where
  show (CAKeyword k) = show k
  show (CAData d) = show d

public export
caShow : ComputeAtom -> String
caShow = show

public export
caDecEq : DecEqPred ComputeAtom
caDecEq (CAKeyword k) (CAKeyword k') = case decEq k k' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
caDecEq (CAKeyword _) (CAData _) =
  No $ \eq => case eq of Refl impossible
caDecEq (CAData _) (CAKeyword _) =
  No $ \eq => case eq of Refl impossible
caDecEq (CAData d) (CAData d') = case decEq d d' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq ComputeAtom where
  decEq = caDecEq

public export
Eq ComputeAtom using decEqToEq where
  (==) = (==)

public export
Ord ComputeAtom where
  CAKeyword k < CAKeyword k' = k < k'
  CAKeyword _ < CAData _ = True
  CAData _ < CAKeyword _ = False
  CAData d < CAData d' = d < d'

public export
CAFail : ComputeAtom
CAFail = CAKeyword Fail

public export
CANat : Nat -> ComputeAtom
CANat = CAData . DNat

public export
CAString : String -> ComputeAtom
CAString = CAData . DString

public export
CExp : Type
CExp = SExp ComputeAtom

public export
CList : Type
CList = SList ComputeAtom

public export
Show CExp where
  show = fst (sexpShows show)

public export
Show CList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
csDecEq : DecEqPred CExp
csDecEq = sexpDecEq caDecEq

public export
cslDecEq : DecEqPred CList
cslDecEq = slistDecEq caDecEq

public export
DecEq CExp where
  decEq = csDecEq

public export
DecEq CList where
  decEq = cslDecEq

public export
Eq CExp using decEqToEq where
  (==) = (==)

public export
CSFail : CExp
CSFail = $^ CAFail

public export
cexpTransform : {changeDesc, context: Type} ->
  SExpTransformSignature changeDesc ComputeAtom context ->
  CExp -> context -> (context, SExpTransformResult changeDesc ComputeAtom)
cexpTransform = sexpTransform

public export
clistTransform : {changeDesc, context : Type} ->
  SExpTransformSignature changeDesc ComputeAtom context ->
  CList -> context -> (context, SListTransformResult changeDesc ComputeAtom)
clistTransform = slistTransform
