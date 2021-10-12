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
  eexpApply : (f, x : EExp) -> EExp
  eexpApply (EAReflectedMorphism Fail $* _) _ = CSFail
  eexpApply (EAReflectedMorphism Compose $* fs) x = eCompositionApply fs x
  eexpApply (EAReflectedMorphism Identity $* []) x = x
  eexpApply (EAReflectedMorphism Identity $* _ :: _) x = CSFail
  eexpApply (EAReflectedMorphism Const $* [_]) (EAReflectedMorphism Fail $* _) =
    CSFail
  eexpApply (EAReflectedMorphism Const $* [c]) _ = c
  eexpApply (EAReflectedMorphism Const $* _) _ = CSFail
  eexpApply (EAInterpretation _ $* _) _ = CSFail
  eexpApply (EAData _ $* _) _ = CSFail
  eexpApply _ _ = ?eexpApply_hole

  public export
  eCompositionApply : (fs : EList) -> (x : EExp) -> EExp
  eCompositionApply [] x = x
  eCompositionApply (f :: fs') x =
    EAReflectedMorphism Liskov $* [f, EAReflectedMorphism Liskov $*
      [EAReflectedMorphism Compose $* fs', x]]

-- | A single (small) step of the EExp interpreter.
-- | The boolean part of the return value indicates whether anything changed.
-- | (If not, then the term is fully evaluated, meaning that there are no
-- | instances of "Eval" in it.)
mutual
  public export
  eexpInterpretStep : EExp -> (Bool, EExp)
  eexpInterpretStep (EAReflectedMorphism Liskov $* [f, x]) =
    case eexpInterpretStep f of
      (True, f') => (True, EAReflectedMorphism Liskov $* [f', x])
      (False, _) => case eexpInterpretStep x of
        (True, x') => (True, EAReflectedMorphism Liskov $* [f, x'])
        (False, _) => (True, eexpApply f x)
  eexpInterpretStep (EAReflectedMorphism Liskov $* _) = (True, CSFail)
  eexpInterpretStep (a $* l) = case elistInterpretStep l of
    (True, l') => (True, a $* l')
    (False, _) => (False, a $* l)

  public export
  elistInterpretStep : EList -> (Bool, EList)
  elistInterpretStep [] = (False, [])
  elistInterpretStep (x :: l) = case eexpInterpretStep x of
    (True, x') => (True, x' :: l)
    (False, _) => case elistInterpretStep l of
      (True, l') => (True, x :: l')
      (False, _) => (False, x :: l)

-- | A computable function whose termination Idris-2 can prove.
-- | It still returns "maybe" because it might be partial (its
-- | domain might not include all of EExp).
public export
TerminatingComputableFunction : Type
TerminatingComputableFunction = EExp -> Maybe EExp

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
IsTotal f = (x : EExp) -> IsJust $ f x

public export
TotalComputableFunction : Type
TotalComputableFunction = EExp -> EExp

public export
toTotal :
  {f : TerminatingComputableFunction} -> IsTotal f -> TotalComputableFunction
toTotal isTotal x = IsJustElim $ isTotal x

-- | Extensional equality on computable functions.
infixl 1 #~~
public export
(#~~) : TerminatingComputableFunction -> TerminatingComputableFunction -> Type
f #~~ g = ((x : EExp) -> f x = g x)
