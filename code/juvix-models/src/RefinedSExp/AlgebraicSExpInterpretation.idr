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
FailurePropagator : Type
FailurePropagator = Endofunction RefinedSExp

public export
ComputableFunction : Type
ComputableFunction = (PartialComputableFunction, FailurePropagator)

-- | Composition of computable functions according to the rules described
-- | above.  To apply the output function, we must provide one input
-- | function for each argument of the output function.
infixl 1 #.
public export
(#.) : ComputableFunction -> ComputableFunction -> ComputableFunction
(left, leftFailurePropagator) #. (right, rightFailurePropagator) =
  (right >=> left, leftFailurePropagator . rightFailurePropagator)

public export
record RefinedLanguage where
  constructor Compiler
  check : ComputableFunction
  -- compile :
