module RefinedSExp.Interpretation

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public RefinedSExp.Computation

%default total

-- | A computable function whose termination Idris-2 can prove.
-- | It still returns "maybe" because it might be partial (its
-- | domain might not include all of CExp).
public export
TerminatingComputableFunction : Type
TerminatingComputableFunction = CExp -> Maybe CExp

-- | When composing computable functions, any failure of the computation
-- | of any argument of the first function application must produce a
-- | failure in the computation of the second function application.
infixl 1 #.
public export
(#.) : TerminatingComputableFunction -> TerminatingComputableFunction ->
  TerminatingComputableFunction
(#.) = flip (>=>)

-- | A total computable function returns some input for every output
-- | (its domain is all S-expressions and it terminates on all inputs).
public export
IsTotal : TerminatingComputableFunction -> Type
IsTotal f = (x : CExp) -> IsJust $ f x

public export
TotalComputableFunction : Type
TotalComputableFunction = CExp -> CExp

public export
toTotal :
  {f : TerminatingComputableFunction} -> IsTotal f -> TotalComputableFunction
toTotal isTotal x = IsJustElim $ isTotal x

-- | Extensional equality on computable functions.
infixl 1 #~~
public export
(#~~) : TerminatingComputableFunction -> TerminatingComputableFunction -> Type
f #~~ g = ((x : CExp) -> f x = g x)
