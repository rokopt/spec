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
  eexpApply (EAMorphism Fail $* _) _ = ESFail
  eexpApply (EAMorphism Compose $* fs) x = eCompositionApply fs x
  eexpApply (EAMorphism Identity $* []) x = x
  eexpApply (EAMorphism Identity $* _ :: _) x = ESFail
  eexpApply (EAMorphism Const $* [_]) (EAMorphism Fail $* _) =
    ESFail
  eexpApply (EAMorphism Const $* [c]) _ = c
  eexpApply (EAMorphism Const $* _) _ = ESFail
  eexpApply (EAMorphism MakeTuple $* l) x =
    EAInterpretation Record $* eMakeTupleApply l x
  eexpApply (EAMorphism Project $* [EAData (DNat n) $* []])
    (EAInterpretation Record $* fields) =
      case indexElem n fields of
        Just (field ** _) => field
        Nothing => ESFail
  eexpApply (EAMorphism Project $* _) _ = ESFail
  eexpApply (EAMorphism Inject $* ([EAData (DNat n) $* [], f])) x =
    EAInterpretation Constructor $*
      [EAData (DNat n) $* [], EAMorphism Liskov $* [f, x]]
  eexpApply (EAMorphism Inject $* _) _ = ESFail
  eexpApply (EAMorphism Case $* []) _ = ESFail
  eexpApply (EAMorphism Case $* cases)
    (EAInterpretation Constructor $* [EAData (DNat n) $* [x]]) =
      case indexElem n cases of
        Just (f ** _) => EAMorphism Liskov $* [f, x]
        Nothing => ESFail
  eexpApply (EAMorphism Case $* _) _ = ESFail
  eexpApply (EAMorphism Liskov $* [f, a]) x = ?liskov_hole
  eexpApply (EAMorphism Liskov $* _) _ = ESFail
  eexpApply (EAMorphism Curry $* [f, a]) x = ?curry_hole
  eexpApply (EAMorphism Curry $* _) _ = ESFail
  eexpApply (EAMorphism Turing $* [f, a]) x = ?turing_hole
  eexpApply (EAMorphism Turing $* _) _ = ESFail
  eexpApply (EAMorphism Gödel $* (a :: fs)) x = ?gödel_hole
  eexpApply (EAMorphism Gödel $* _) _ = ESFail
  eexpApply (EAMorphism TestEqual $* [s, s', t, f]) x = ?testequal_hole
  eexpApply (EAMorphism TestEqual $* _) _ = ESFail
  eexpApply (EAInterpretation _ $* _) _ = ESFail
  eexpApply (EAData _ $* _) _ = ESFail

  public export
  eCompositionApply : (fs : EList) -> (x : EExp) -> EExp
  eCompositionApply [] x = x
  eCompositionApply (f :: fs') x =
    EAMorphism Liskov $* [f, EAMorphism Liskov $*
      [EAMorphism Compose $* fs', x]]

  public export
  eMakeTupleApply : (fs : EList) -> (x : EExp) -> EList
  eMakeTupleApply [] _ = []
  eMakeTupleApply (f :: fs) x =
    (EAMorphism Liskov $* [f, x]) :: eMakeTupleApply fs x

  public export
  eexpReduceOne : ExtendedAtom -> EList -> Maybe EExp
  eexpReduceOne = ?eexpReduceOne_hole

  public export
  eexpInterpretStep : EExp -> Maybe EExp
  eexpInterpretStep (a $* l) = case elistInterpretStep l of
    Just l' => Just (a $* l')
    Nothing => eexpReduceOne a l

  public export
  elistInterpretStep : EList -> Maybe EList
  elistInterpretStep [] = Nothing
  elistInterpretStep (x :: l) = case eexpInterpretStep x of
    Just x' => Just (x' :: l)
    Nothing => case elistInterpretStep l of
      Just l' => Just (x :: l')
      Nothing => Nothing

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
