module RefinedSExp.Computation

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public Category.ComputableCategories
import public RefinedSExp.SExp
import public RefinedSExp.Data

%default total

-- | Atoms representing the built-in morphisms of the Geb language, which is:
-- |  - A Lisp variant, in that it includes what Lisp calls `quote` and `eval`
-- |    as primitives
-- |  - Point-free, like Backus's FP, to avoid having to define how names and
-- |    contexts should be implemented, most importantly in the context of
-- |    metaprogramming
-- |  - Category-theoretical; its semantics are defined operationally by
-- |    small-step interpretation of its S-expressions as general (i.e.
-- |    potentially partial, potentially non-terminating) computable functions
-- |    from its own S-expressions to its S-expressions.  Its atoms therefore
-- |    include both atoms representing morphisms in the one-object category of
-- |    general computable functions, and atoms representing elements of the
-- |    set of all S-expressions, using which its semantics may be defined.
-- |    The interpretation of an S-expression which itself represents an
-- |    interpretation, i.e., an element of the set of all expressions as
-- |    opposed to a morphism on computable functions on S-expressions, is a
-- |    computable function which fails on all inputs.  (In programming terms,
-- |    interpreting an S-expression that does not represent a morphism is an
-- |    attempt to execute something which is not a function.)
public export
data Keyword : Type where
  -- | Represents failure of a general computable function application.
  Fail : Keyword

  -- | Composition of general computable functions.
  Compose : Keyword

  -- | The identity general computable function (which is total).
  Identity : Keyword

  -- | Product introduction for general compuatable functions:  form a function
  -- | which returns tuples from a tuple of functions (which must have the same
  -- | domain for this operation to make sense).
  MakeTuple : Keyword

  -- | Product elimination for general computable functions:  form a function
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
  -- | computable functions.  It is named after Liskov because it is
  -- | implemented as substitution.  It is known as "eval" in the category
  -- | theory of exponential objects, but we use a different name to avoid
  -- | confusion with the "eval" of Lisp, which we call "Turing".
  Liskov : Keyword

  -- | The currying function associated with exponentials of general
  -- | computable functions.  It is the right adjoint to Liskov.
  Curry : Keyword

  -- | The combinator which gives us unconstrained general recursion:
  -- | we name it after Turing; it is the "eval" of Lisp, but we wish
  -- | to avoid confusion with the "eval" of the category theory of
  -- | exponential objects (which we call "Liskov").
  -- |
  -- | This combinator can be viewed as metaprogramming elimination.
  Turing : Keyword

  -- | General recursive cofixpoint.  Is this useful?  or can it
  -- | be implemented in terms of Turing, as Fix can?  I suspect so.
  -- XXX Cofix : Keyword
  -- | Reflection:  S-expression introduction, which takes a function which
  -- | returns an atom and a list of functions which return S-expressions
  -- | and produces a function which returns an S-expression.
  -- |
  -- | This combinator can be viewed as metaprogramming introduction.
  Gödel : Keyword

  -- | Decidable equality on S-expressions, which includes atom elimination.
  -- | This combinator could be viewed as constant elimination.
  TestEqual : Keyword

  -- | Introduce a constant-valued function.
  Const : Keyword

  -- | The interpretation of a product.
  Record : Keyword

  -- | The interpretation of a coproduct.
  Constructor : Keyword

public export
keywordToString : Keyword -> String
keywordToString Fail = "Fail"
keywordToString Compose = "Compose"
keywordToString Identity = "Identity"
keywordToString Const = "Const"
keywordToString MakeTuple = "MakeTuple"
keywordToString Project = "Project"
keywordToString Case = "Case"
keywordToString Inject = "Inject"
keywordToString Liskov = "Liskov"
keywordToString Curry = "Curry"
keywordToString Turing = "Turing"
-- keywordToString Cofix = "Cofix"
keywordToString Gödel = "Gödel"
keywordToString TestEqual = "TestEqual"
keywordToString Record = "Record"
keywordToString Constructor = "Constructor"

public export
Show Keyword where
  show k = ":" ++ keywordToString k

public export
kEncode : Keyword -> Nat
kEncode Fail = 0
kEncode Compose = 1
kEncode Identity = 2
kEncode Const = 3
kEncode MakeTuple = 4
kEncode Project = 5
kEncode Case = 6
kEncode Inject = 7
kEncode Liskov = 8
kEncode Curry = 9
kEncode Turing = 10
-- kEncode Cofix = 11
kEncode Gödel = 12
kEncode TestEqual = 13
kEncode Record = 15
kEncode Constructor = 16

public export
kDecode : Nat -> Keyword
kDecode 0 = Fail
kDecode 1 = Compose
kDecode 2 = Identity
kDecode 3 = Const
kDecode 4 = MakeTuple
kDecode 5 = Project
kDecode 6 = Case
kDecode 7 = Inject
kDecode 8 = Liskov
kDecode 9 = Curry
kDecode 10 = Turing
-- kDecode 11 = Cofix
kDecode 12 = Gödel
kDecode 13 = TestEqual
kDecode 15 = Record
kDecode 16 = Constructor
kDecode _ = Fail

export
kDecodeIsLeftInverse :
  IsLeftInverseOf Computation.kEncode Computation.kDecode
kDecodeIsLeftInverse Fail = Refl
kDecodeIsLeftInverse Compose = Refl
kDecodeIsLeftInverse Identity = Refl
kDecodeIsLeftInverse Const = Refl
kDecodeIsLeftInverse MakeTuple = Refl
kDecodeIsLeftInverse Project = Refl
kDecodeIsLeftInverse Case = Refl
kDecodeIsLeftInverse Inject = Refl
kDecodeIsLeftInverse Liskov = Refl
kDecodeIsLeftInverse Curry = Refl
kDecodeIsLeftInverse Turing = Refl
-- kDecodeIsLeftInverse Cofix = Refl
kDecodeIsLeftInverse Gödel = Refl
kDecodeIsLeftInverse TestEqual = Refl
kDecodeIsLeftInverse Record = Refl
kDecodeIsLeftInverse Constructor = Refl

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
