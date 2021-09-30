module RefinedSExp.AlgebraicSExpInterpretation

import public RefinedSExp.AlgebraicSExp
import Data.Maybe
import Library.List

%default total

-- | A computable function takes an argument and returns either a result or
-- | a failure.  Both results and failures are themselves represented by
-- | expressions -- the latter as a convenience to allow descriptions of errors.
-- | (For example, we might distinguish between arguments outside the domain of
-- | a partial function versus the non-termination of a function whose
-- | exact domain is undecidable, among other possibilities depending on the
-- | specific language in the context of which we interpret an expression.)
-- |
-- | When composing computable functions, any failure of the computation
-- | of any argument of the first function application must produce a
-- | failure in the computation of the second function application.
-- | Thus, our representation of computable functions includes an error
-- | propagation function which updates the representation of the failure
-- | in some way which is determined by the specific language in the context
-- | of which we interpret an expression.  The error-propagation function
-- | does not itself "fail", since its result will always be interpreted
-- | as a failure by future computations in any case.

public export
SymmetricSum : Type -> Type
SymmetricSum ty = Either ty ty

public export
PartialComputableFunction : Type
PartialComputableFunction = RefinedSExp -> SymmetricSum RefinedSExp

public export
PartialIsTotal : PartialComputableFunction -> Type
PartialIsTotal f = (x : RefinedSExp) -> IsLeft $ f x

-- | An equivalence on partial computable functions which ignores differences
-- | in the expressions describing failures (but does require that the
-- | functions succeed on the same sets of inputs).
infixl 1 #~~
public export
(#~~) : PartialComputableFunction -> PartialComputableFunction -> Type
f #~~ g =
  ((x : RefinedSExp) -> Either (IsLeft $ f x) (IsLeft $ g x) -> f x = g x)

-- | Extend the notion of computable functions to include error propagation,
-- | to allow arbitrary descriptions of the forms of failures in earlier
-- | steps of chains of composed functions.

public export
FailurePropagator : Type
FailurePropagator = Endofunction RefinedSExp

public export
ExtendedComputableFunction : Type
ExtendedComputableFunction = (PartialComputableFunction, FailurePropagator)

public export
IsTotal : ExtendedComputableFunction -> Type
IsTotal = PartialIsTotal . fst

-- | An equivalence on computable functions which ignores differences
-- | in the expressions describing failures (but does require that the
-- | functions succeed on the same sets of inputs).
infixl 1 #~-
public export
(#~-) : ExtendedComputableFunction -> ExtendedComputableFunction -> Type
(f, _) #~- (g, _) = f #~~ g

-- | Compose an extended computable function with a partial computable function.
-- | (See "railway-oriented programming"!)
infixl 1 ~.
public export
(~.) : ExtendedComputableFunction -> PartialComputableFunction ->
  PartialComputableFunction
(~.) g f x with (f x)
  (~.) g f x | Left fx = fst g fx
  (~.) g f x | Right fxFailure = Right $ snd g fxFailure

-- | Composition of extended computable functions according to the rules
-- | described above.  (See "railway-oriented programming" again!)
infixl 1 #.
public export
(#.) : ExtendedComputableFunction -> ExtendedComputableFunction ->
  ExtendedComputableFunction
g #. f = (g ~. fst f, snd g . snd f)

public export
Signature : Type
Signature = PairOf Type

-- | A typechecker in our top-level metalanguage -- in this case Idris-2 --
-- | is a function which decides whether any given expression represents
-- | a metalanguage function, and if so, of what type.
public export
Typechecker : Type
Typechecker = RefinedSExp -> Maybe Signature

public export
TypeFamily : Type
TypeFamily = (indexType : Type ** indexType -> Type)

-- | A compiler is, like any program that we can execute, a computable
-- | function.  What distinguishes a compiler from arbitrary computable
-- | functions is that if a compiler succeeds at compiling some expression,
-- | then the output expression may itself be interpreted as a computable
-- | function.
-- |
-- | Note that this definition admits the possibility that a single
-- | computable function might be interpreted as a compiler in more than
-- | one way.
public export
Compiler : PartialComputableFunction -> Type
Compiler f = (x : RefinedSExp) -> IsLeft (f x) -> PartialComputableFunction

-- | A strongly normalizing language is one whose functions all terminate.
-- | To interpret a computable function as a compiler for a strongly
-- | normalizing language therefore means interpreting all successful
-- | outputs as _total_ computable functions.  This could be treated as
-- | an expression of the notion that "well-typed programs never go wrong".
-- |
-- | Note that this definition does not require that the compiler _itself_
-- | be a total computable function.
public export
Normalizing : {c : PartialComputableFunction} -> Compiler c -> Type
Normalizing {c} interpret =
  (x : RefinedSExp) -> (checked : IsLeft (c x)) ->
  PartialIsTotal (interpret x checked)
