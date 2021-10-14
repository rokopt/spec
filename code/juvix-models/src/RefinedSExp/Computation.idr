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
-- |    from S-expressions to S-expressions.  Its atoms therefore
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
data MorphismAtom : Type where
  -- | Represents failure of a general computable function application.
  Fail : MorphismAtom

  -- | Composition of general computable functions.
  Compose : MorphismAtom

  -- | The identity general computable function (which is total).
  Identity : MorphismAtom

  -- | Introduce a constant-valued function.
  Const : MorphismAtom

  -- | Product introduction for general compuatable functions:  form a function
  -- | which returns tuples from a tuple of functions (which must have the same
  -- | domain for this operation to make sense).
  MakeTuple : MorphismAtom

  -- | Product elimination for general computable functions:  select a
  -- | function from a tuple of functions.
  Project : MorphismAtom

  -- | Coproduct introduction for general computable functions:  choose one
  -- | of one or more possible forms.
  Inject : MorphismAtom

  -- | Coproduct elimination for general computable functions:  form a function
  -- | which accepts a coproduct and returns a case depending on which of the
  -- | coproduct's injections is passed in.
  Case : MorphismAtom

  -- | The evaluation function associated with exponentials of general
  -- | computable functions.  It is named after Liskov because it is
  -- | implemented as substitution.  It is known as "eval" in the category
  -- | theory of exponential objects, but we use a different name to avoid
  -- | confusion with the "eval" of Lisp, which we call "Turing".
  Liskov : MorphismAtom

  -- | The currying function associated with exponentials of general
  -- | computable functions.  It is the right adjoint to Liskov.
  Curry : MorphismAtom

  -- | The combinator which gives us unconstrained general recursion:
  -- | we name it after Turing; it is the "eval" of Lisp, but we wish
  -- | to avoid confusion with the "eval" of the category theory of
  -- | exponential objects (which we call "Liskov").
  -- |
  -- | This combinator can be viewed as metaprogramming elimination.
  Turing : MorphismAtom

  -- | Reflection:  S-expression introduction, which takes a function which
  -- | returns an atom and a list of functions which return S-expressions
  -- | and produces a function which returns an S-expression.
  -- |
  -- | This combinator can be viewed as metaprogramming introduction.
  Gödel : MorphismAtom

  -- | Decidable equality on S-expressions, which includes atom elimination.
  -- | This combinator could be viewed as constant elimination.
  TestEqual : MorphismAtom

public export
morphismToString : MorphismAtom -> String
morphismToString Fail = "Fail"
morphismToString Compose = "Compose"
morphismToString Identity = "Identity"
morphismToString Const = "Const"
morphismToString MakeTuple = "MakeTuple"
morphismToString Project = "Project"
morphismToString Case = "Case"
morphismToString Inject = "Inject"
morphismToString Liskov = "Liskov"
morphismToString Curry = "Curry"
morphismToString Turing = "Turing"
morphismToString Gödel = "Gödel"
morphismToString TestEqual = "TestEqual"

public export
Show MorphismAtom where
  show m = ":" ++ morphismToString m

public export
mEncode : MorphismAtom -> Nat
mEncode Fail = 0
mEncode Compose = 1
mEncode Identity = 2
mEncode Const = 3
mEncode MakeTuple = 4
mEncode Project = 5
mEncode Case = 6
mEncode Inject = 7
mEncode Liskov = 8
mEncode Curry = 9
mEncode Turing = 10
mEncode Gödel = 11
mEncode TestEqual = 12

public export
mDecode : Nat -> MorphismAtom
mDecode 0 = Fail
mDecode 1 = Compose
mDecode 2 = Identity
mDecode 3 = Const
mDecode 4 = MakeTuple
mDecode 5 = Project
mDecode 6 = Case
mDecode 7 = Inject
mDecode 8 = Liskov
mDecode 9 = Curry
mDecode 10 = Turing
mDecode 11 = Gödel
mDecode 12 = TestEqual
mDecode _ = Fail

export
mDecodeIsLeftInverse :
  IsLeftInverseOf Computation.mEncode Computation.mDecode
mDecodeIsLeftInverse Fail = Refl
mDecodeIsLeftInverse Compose = Refl
mDecodeIsLeftInverse Identity = Refl
mDecodeIsLeftInverse Const = Refl
mDecodeIsLeftInverse MakeTuple = Refl
mDecodeIsLeftInverse Project = Refl
mDecodeIsLeftInverse Case = Refl
mDecodeIsLeftInverse Inject = Refl
mDecodeIsLeftInverse Liskov = Refl
mDecodeIsLeftInverse Curry = Refl
mDecodeIsLeftInverse Turing = Refl
mDecodeIsLeftInverse Gödel = Refl
mDecodeIsLeftInverse TestEqual = Refl

export
mEncodeIsInjective : IsInjective Computation.mEncode
mEncodeIsInjective =
  leftInverseImpliesInjective mEncode {g=mDecode} mDecodeIsLeftInverse

public export
MInjection : Injection MorphismAtom Nat
MInjection = (mEncode ** mEncodeIsInjective)

public export
MCountable : Countable
MCountable = (MorphismAtom ** MInjection)

public export
mDecEq : DecEqPred MorphismAtom
mDecEq = countableEq MCountable

public export
DecEq MorphismAtom where
  decEq = mDecEq

public export
Eq MorphismAtom using decEqToEq where
  (==) = (==)

public export
Ord MorphismAtom where
  m < m' = mEncode m < mEncode m'

public export
MExp : Type
MExp = SExp MorphismAtom

public export
MList : Type
MList = SList MorphismAtom

public export
Show MExp where
  show = fst (sexpShows show)

public export
Show MList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
msDecEq : DecEqPred MExp
msDecEq = sexpDecEq mDecEq

public export
mslDecEq : DecEqPred MList
mslDecEq = slistDecEq mDecEq

public export
DecEq MExp where
  decEq = msDecEq

public export
DecEq MList where
  decEq = mslDecEq

public export
Eq MExp using decEqToEq where
  (==) = (==)

-- | Atoms from which are constructed the elements of the set of S-expressions
-- | which we interpret as the domain and the codomain of general computable
-- | functions when defining Geb's semantics by interpretation.
public export
data InterpretationAtom : Type where
  -- | The interpretation of the failure of the application of a partial
  -- | computable function to an S-expression outside of its domain.
  Failure : InterpretationAtom

  -- | Apply a function to an argument.
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
data ExtendedAtom : Type where
  EAMorphism : MorphismAtom -> ExtendedAtom
  EAInterpretation : InterpretationAtom -> ExtendedAtom
  EAData : Data -> ExtendedAtom

public export
Show ExtendedAtom where
  show (EAMorphism m) = show m
  show (EAInterpretation i) = show i
  show (EAData d) = show d

public export
eaShow : ExtendedAtom -> String
eaShow = show

public export
eaDecEq : DecEqPred ExtendedAtom
eaDecEq (EAMorphism m) (EAMorphism m') =
  case decEq m m' of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl
eaDecEq (EAMorphism _) (EAInterpretation _) =
  No $ \eq => case eq of Refl impossible
eaDecEq (EAMorphism _) (EAData _) =
  No $ \eq => case eq of Refl impossible
eaDecEq (EAInterpretation _) (EAMorphism _) =
  No $ \eq => case eq of Refl impossible
eaDecEq (EAInterpretation i) (EAInterpretation i') = case decEq i i' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
eaDecEq (EAInterpretation _) (EAData _) =
  No $ \eq => case eq of Refl impossible
eaDecEq (EAData _) (EAMorphism _) =
  No $ \eq => case eq of Refl impossible
eaDecEq (EAData _) (EAInterpretation _) =
  No $ \eq => case eq of Refl impossible
eaDecEq (EAData d) (EAData d') = case decEq d d' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq ExtendedAtom where
  decEq = eaDecEq

public export
Eq ExtendedAtom using decEqToEq where
  (==) = (==)

public export
Ord ExtendedAtom where
  EAMorphism m < EAMorphism m' = m < m'
  EAMorphism _ < EAInterpretation _ = True
  EAMorphism _ < EAData _ = True
  EAInterpretation _ < EAMorphism _ = False
  EAInterpretation i < EAInterpretation i' = i < i'
  EAInterpretation _ < EAData _ = True
  EAData _ < EAMorphism _ = False
  EAData _ < EAInterpretation _ = False
  EAData d < EAData d' = d < d'

public export
EAFail : ExtendedAtom
EAFail = EAMorphism Fail

public export
EANat : Nat -> ExtendedAtom
EANat = EAData . DNat

public export
EAString : String -> ExtendedAtom
EAString = EAData . DString

public export
EExp : Type
EExp = SExp ExtendedAtom

public export
EList : Type
EList = SList ExtendedAtom

public export
Show EExp where
  show = fst (sexpShows show)

public export
Show EList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
esDecEq : DecEqPred EExp
esDecEq = sexpDecEq eaDecEq

public export
eslDecEq : DecEqPred EList
eslDecEq = slistDecEq eaDecEq

public export
DecEq EExp where
  decEq = esDecEq

public export
DecEq EList where
  decEq = eslDecEq

public export
Eq EExp using decEqToEq where
  (==) = (==)

public export
ESFail : EExp
ESFail = $^ EAFail
