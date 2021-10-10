module RefinedSExp.Interpretation

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public RefinedSExp.Computation

%default total

-- | A single function application, on two fully-evaluated terms (that
-- | full sub-evaluation is the caller's responsibility to guarantee).
mutual
  public export
  cexpApply : (f, x : CExp) -> CExp
  cexpApply (CAKeyword Fail $* _) _ = CSFail
  cexpApply (CAKeyword Compose $* fs) x = cCompositionEval fs x
  cexpApply (CAKeyword Identity $* []) x = x
  cexpApply (CAKeyword Identity $* _ :: _) x = CSFail
  cexpApply (CAKeyword Const $* [_]) (CAKeyword Fail $* _) = CSFail
  cexpApply (CAKeyword Const $* [c]) _ = c
  cexpApply (CAKeyword Const $* _) _ = CSFail
  cexpApply (CAInterpretation _ $* _) _ = CSFail
  cexpApply (CAData _ $* _) _ = CSFail
  cexpApply _ _ = ?cexpApply_hole

  public export
  cCompositionEval : (fs : CList) -> (x : CExp) -> CExp
  cCompositionEval [] x = x
  cCompositionEval (f :: fs') x =
    CAKeyword Liskov $* [f, CAKeyword Liskov $* [CAKeyword Compose $* fs', x]]

-- | A single (small) step of the CExp interpreter.
-- | The boolean part of the return value indicates whether anything changed.
-- | (If not, then the term is fully evaluated, meaning that there are no
-- | instances of "Eval" in it.)
mutual
  public export
  cexpInterpretStep : CExp -> (Bool, CExp)
  cexpInterpretStep (CAKeyword Liskov $* [f, x]) = case cexpInterpretStep f of
    (True, f') => (True, CAKeyword Liskov $* [f', x])
    (False, _) => case cexpInterpretStep x of
      (True, x') => (True, CAKeyword Liskov $* [f, x'])
      (False, _) => (True, cexpApply f x)
  cexpInterpretStep (CAKeyword Liskov $* _) = (True, CSFail)
  cexpInterpretStep (a $* l) = case clistInterpretStep l of
    (True, l') => (True, a $* l')
    (False, _) => (False, a $* l)

  public export
  clistInterpretStep : CList -> (Bool, CList)
  clistInterpretStep [] = (False, [])
  clistInterpretStep (x :: l) = case cexpInterpretStep x of
    (True, x') => (True, x' :: l)
    (False, _) => case clistInterpretStep l of
      (True, l') => (True, x :: l')
      (False, _) => (False, x :: l)

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
