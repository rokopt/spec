module RefinedSExp.Computation

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public Category.ComputableCategories
import public RefinedSExp.SExp
import public RefinedSExp.Data

%default total

-- | Atoms representing the built-in morphisms of the Geb language, which is:
-- |
-- |  - Named as an homage to Hofstadter's _Gödel, Escher, Bach_
-- |  - A Lisp variant, in that it includes what Lisp calls `quote` and `eval`
-- |    as primitives
-- |  - Point-free, like Backus's FP, to avoid having to define how names and
-- |    contexts should be implemented, most importantly in the context of
-- |    metaprogramming (its built-in constructs are all combinators, not
-- |    lambdas, although names, contexts, and lambdas could all be defined in
-- |    terms of its primitive combinators, each in many different ways suitable
-- |    to different programming languages)
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
-- |  - A Turing machine, when the Turing operator (which is what Geb calls
-- |    its equivalent of Lisp's `eval`) is used without restrictions, or
-- |    with some restrictions but not enough to prevent the construction of
-- |    all general computable functions (including the partial and
-- |    non-terminating ones)
-- |  - A minimal metalogic -- just enough to be subject to Gödel's
-- |    incompleteness theorems -- when the Turing operator is not used at all.
-- |    It is possible, although unproven, that in this form it is equivalent
-- |    to Robinson arithmetic.
-- |  - A "potentially consistent metalogic" -- we can never refer to a
-- |    as absolutely consistent, in light of Gödel's results -- when the Turing
-- |    operator may be used, but only with restrictions which prevent any
-- |    S-expressions from being interpreted as non-total computable functions
-- |    (if the metalogic really is consistent, which, again, can not be
-- |    proven absolutely -- so we should say that all of its S-expressions
-- |    are interpreted as non-total computable functions _as far as anyone
-- |    knows_).  A given restriction of the Turing operator is known as the
-- |    type system -- type-checking an S-expression is equivalent to
-- |    claiming that all well-typed S-expressions are interpreted as total
-- |    computable functions.
-- |  - In light of the previous three points, a super-category of all
-- |    metalogics and programming languages (we are referring to a logic
-- |    strong enough to be subject to Gödel's incompleteness theorems, and
-- |    therefore to reflect and check typing derivations of other logics and
-- |    languages, including itself, as a "metalogic"), although it is itself,
-- |    as a complete category, unityped, in that its only object is that of
-- |    S-expressions (as Harper points out, "unityped" and "untyped" are
-- |    equivalent; in programming we also call this "dynamically typed")
-- |  - A category-theoretically unique construction, and therefore not only _a_
-- |    super-category of all metalogics and programming languages, but the
-- |    _only_ such super-category, up to isomorphism
-- |  - In light of the previous two points, a potential universal
-- |    "intermediate representation", or "open protocol description", for
-- |    all programming languages and metalogics, with which individual
-- |    compilers (and mathematical papers) could unambiguously and universally
-- |    define type systems for both potentially consistent metalogics and
-- |    programming languages and for Turing machines (which are inconsistent
-- |    when viewed as logics), unambiguously define notions of correct
-- |    transformations within and across metalogics and programming languages,
-- |    and unambiguously share definitions of metalogics and programming
-- |    languages with other compilers (and mathematical papers), in a way
-- |    which it itself can verify (in the sense of type-checking completely
-- |    enumerated alleged typing derivations), including the definition of
-- |    Geb itself.  As an open protocol description, it could also function
-- |    as a bridge between theorem provers / proof assistants / SMT solvers and
-- |    metalogics / programming languages:  defining the semantics of a
-- |    language or logic as a functor to a sub-category of Geb would allow
-- |    different theorem provers to prove results about it without requiring
-- |    any code to connect the specific language or logic to the specific proof
-- |    assistant
-- |  - Also in light of previous points, a potential component of compiler
-- |    architecture which allows as much of the compiler code as is possible
-- |    and efficient to be written in terms of category-theoretically unique
-- |    universal constructions, and therefore to be verified independently of
-- |    the specific type theory or theories (programming languages) which the
-- |    compiler is able to typecheck and compile.
-- |  - In light of the previous point, such a compiler architecture could also
-- |    be developed into a shared library usable by _all_ compilers which
-- |    adopt that architecture, allowing new programming languages to be
-- |    defined using that library, inheriting whichever concepts, constructs,
-- |    and theorems that its author wishes it to, and requiring the author
-- |    to write new code only for the concepts which distinguish the new
-- |    language from existing languages
-- |  - In light of its potential use as an open protocol, and a shared
-- |    "intermediate representation", a potential language for a shared library
-- |    of all formalizable knowledge -- a sort of symbolic Wikipedia -- whose
-- |    code could be checked by theorem provers and compiled directly into
-- |    executable programs
-- |  - Possibly a topos, although this is unproven (if so, then its internal
-- |    logic is inconsistent -- but the sub-categories of it which contain
-- |    only total computable functions, if there are any (if not, then
-- |    even a very weak (possibly Robinson) arithmetic is inconsistent), have
-- |    consistent internal logics)
-- |  - "Production-ready" upon initial release:  its category-theoretical
-- |    universality and uniqueness, together with its being defined solely
-- |    in terms of combinators whose semantics have been well-known and
-- |    unambiguously, formally defined for over sixty years (there's no new
-- |    math here!  Just a possibly-new software representation), and together
-- |    with the provable ability of Turing machines to define all programming
-- |    languages, and of Gödel-incomplete (i.e. reflective) metalogics to
-- |    check alleged proofs in all logics, mean that there is no alternative as
-- |    to how to define it, and no possibility of needing to extend the
-- |    language in order to allow define anything further to be defined _in_
-- |    it (assuming that computers are only ever able to execute those
-- |    functions that we currently know as "computable", i.e., those executable
-- |    by Turing machines).  All further Geb development can provably _only_ be
-- |    in libraries written in Geb; the language itself is provably
-- |    unchangeable.  (Any extension would no longer be category-theoretically
-- |    unique, and any restriction would either no longer be
-- |    category-theoretically unique or would no longer be a Turing machine.)
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

  -- | General recursive cofixpoint.  Whether this is useful, or whether it can
  -- | be implemented in terms of Turing, as Fix can, I'm not sure.
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

-- | Atoms from which are constructed the elements of the set of S-expressions
-- | which we interpret as the domain and the codomain of general computable
-- | functions when defining Geb's semantics by interpretation.
public export
data InterpretationAtom : Type where
  -- | The interpretation of the failure of the application of a partial
  -- | computable function to an S-expression outside of its domain.
  Failure : InterpretationAtom

  -- | Function application, which we perform only in the context of
  -- | interpretation.
  Apply : InterpretationAtom

  -- | The interpretation of a product.
  Record : InterpretationAtom

  -- | The interpretation of a coproduct.
  Constructor : InterpretationAtom

public export
interpretationToString : InterpretationAtom -> String
interpretationToString Failure = "Failure"
interpretationToString Apply = "Apply"
interpretationToString Record = "Record"
interpretationToString Constructor = "Constructor"

public export
Show InterpretationAtom where
  show i = "*" ++ interpretationToString i

public export
iEncode : InterpretationAtom -> Nat
iEncode Failure = 0
iEncode Apply = 1
iEncode Record = 2
iEncode Constructor = 3

public export
iDecode : Nat -> InterpretationAtom
iDecode 0 = Failure
iDecode 1 = Apply
iDecode 2 = Record
iDecode 3 = Constructor
iDecode _ = Failure

export
iDecodeIsLeftInverse :
  IsLeftInverseOf Computation.iEncode Computation.iDecode
iDecodeIsLeftInverse Failure = Refl
iDecodeIsLeftInverse Apply = Refl
iDecodeIsLeftInverse Record = Refl
iDecodeIsLeftInverse Constructor = Refl

export
iEncodeIsInjective : IsInjective Computation.iEncode
iEncodeIsInjective =
  leftInverseImpliesInjective iEncode {g=iDecode} iDecodeIsLeftInverse

public export
IInjection : Injection InterpretationAtom Nat
IInjection = (iEncode ** iEncodeIsInjective)

public export
ICountable : Countable
ICountable = (InterpretationAtom ** IInjection)

public export
iDecEq : DecEqPred InterpretationAtom
iDecEq = countableEq ICountable

public export
DecEq InterpretationAtom where
  decEq = iDecEq

public export
Eq InterpretationAtom using decEqToEq where
  (==) = (==)

public export
Ord InterpretationAtom where
  i < i' = iEncode i < iEncode i'

public export
data ComputeAtom : Type where
  CAKeyword : Keyword -> ComputeAtom
  CAInterpretation : InterpretationAtom -> ComputeAtom
  CAData : Data -> ComputeAtom

public export
Show ComputeAtom where
  show (CAKeyword k) = show k
  show (CAInterpretation i) = show i
  show (CAData d) = show d

public export
caShow : ComputeAtom -> String
caShow = show

public export
caDecEq : DecEqPred ComputeAtom
caDecEq (CAKeyword k) (CAKeyword k') = case decEq k k' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
caDecEq (CAKeyword _) (CAInterpretation _) =
  No $ \eq => case eq of Refl impossible
caDecEq (CAKeyword _) (CAData _) =
  No $ \eq => case eq of Refl impossible
caDecEq (CAInterpretation _) (CAKeyword _) =
  No $ \eq => case eq of Refl impossible
caDecEq (CAInterpretation i) (CAInterpretation i') = case decEq i i' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
caDecEq (CAInterpretation _) (CAData _) =
  No $ \eq => case eq of Refl impossible
caDecEq (CAData _) (CAKeyword _) =
  No $ \eq => case eq of Refl impossible
caDecEq (CAData _) (CAInterpretation _) =
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
  CAKeyword _ < CAInterpretation _ = True
  CAKeyword _ < CAData _ = True
  CAInterpretation _ < CAKeyword _ = False
  CAInterpretation i < CAInterpretation i' = i < i'
  CAInterpretation _ < CAData _ = True
  CAData _ < CAKeyword _ = False
  CAData _ < CAInterpretation _ = False
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
