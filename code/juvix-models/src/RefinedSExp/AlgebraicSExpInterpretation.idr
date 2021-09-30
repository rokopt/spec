module RefinedSExp.AlgebraicSExpInterpretation

import public RefinedSExp.AlgebraicSExp
import Data.Maybe
import Library.List

%default total

public export
ComputableFunction : Type
ComputableFunction = RefinedSExp -> Maybe RefinedSExp

infixl 1 #.
public export
(#.) : ComputableFunction -> ComputableFunction -> ComputableFunction
(#.) = flip (>=>)
