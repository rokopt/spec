module RefinedSExp.HigherOrderRecursion

import Library.FunctionsAndRelations
import public RefinedSExp.InductiveTypeTheory
import public RefinedSExp.DependentInductiveTypeTheory

%default total

public export
data HigherOrderFunction :
  {penv : PrimitiveEnv} -> (pfenv : PrimitiveFuncEnv penv) ->
  AlgebraicType penv -> AlgebraicType penv -> Type where

public export
HigherOrderFuncEnv : {penv : PrimitiveEnv} ->
  PrimitiveFuncEnv penv -> PrimitiveFuncEnv penv
HigherOrderFuncEnv pfenv = PrimFuncs (HigherOrderFunction pfenv)

public export
interpretHigherOrderFunction :
  {penv : PrimitiveEnv} -> {pfenv : PrimitiveFuncEnv penv} ->
  {typeInterpretation : PrimitiveTypeInterpretation penv} ->
  (functionInterpretation :
    PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
  {domain, codomain : AlgebraicType penv} ->
  HigherOrderFunction pfenv domain codomain ->
  interpretAlgebraicFunctionType typeInterpretation domain codomain
interpretHigherOrderFunction functionInterpretation function x =
  ?interpretHigherOrderFunction_hole

public export
HigherOrderFuncInterpretation :
  {penv : PrimitiveEnv} ->
  {pfenv : PrimitiveFuncEnv penv} ->
  {typeInterpretation : PrimitiveTypeInterpretation penv} ->
  (functionInterpretation :
    PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
  PrimitiveFunctionInterpretation {penv}
    (HigherOrderFuncEnv pfenv) typeInterpretation
HigherOrderFuncInterpretation =
  PrimitiveFunctionInterpretations . interpretHigherOrderFunction
