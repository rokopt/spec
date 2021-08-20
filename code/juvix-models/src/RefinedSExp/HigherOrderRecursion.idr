module RefinedSExp.HigherOrderRecursion

import Library.FunctionsAndRelations
import public RefinedSExp.InductiveTypeTheory
import public RefinedSExp.DependentInductiveTypeTheory

%default total

public export
data HigherOrderType : (penv : PrimitiveEnv) -> Type where
  HigherOrderPrimitiveType : PrimType penv -> HigherOrderType penv
  HigherOrderNat : HigherOrderType penv

public export
HigherOrderPrimEnv : PrimitiveEnv -> PrimitiveEnv
HigherOrderPrimEnv = PrimArgs . HigherOrderType

public export
HigherOrderPrimFuncEnv : (penv : PrimitiveEnv) -> Type
HigherOrderPrimFuncEnv = PrimitiveFuncEnv . HigherOrderPrimEnv

public export
data HigherOrderFunction :
  {penv : PrimitiveEnv} ->
  (pfenv : HigherOrderPrimFuncEnv penv) ->
  AlgebraicType (HigherOrderPrimEnv penv) ->
  AlgebraicType (HigherOrderPrimEnv penv) ->
  Type where
    HigherOrderPrimitiveFunction :
      PrimFuncType pfenv domain codomain ->
      HigherOrderFunction pfenv domain codomain
    HigherOrderRecursion : Void -> -- XXX
      HigherOrderFunction pfenv domain codomain

public export
HigherOrderFuncEnv : {penv : PrimitiveEnv} ->
  HigherOrderPrimFuncEnv penv -> HigherOrderPrimFuncEnv penv
HigherOrderFuncEnv = PrimFuncs . HigherOrderFunction

public export
interpretHigherOrderFunction :
  {penv : PrimitiveEnv} -> {pfenv : HigherOrderPrimFuncEnv penv} ->
  {typeInterpretation :
    PrimitiveTypeInterpretation (HigherOrderPrimEnv penv)} ->
  (functionInterpretation :
    PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
  {domain, codomain : AlgebraicType (HigherOrderPrimEnv penv)} ->
  HigherOrderFunction pfenv domain codomain ->
  interpretAlgebraicFunctionType typeInterpretation domain codomain
interpretHigherOrderFunction functionInterpretation
  (HigherOrderPrimitiveFunction f) x =
    interpretPrimitiveFunction functionInterpretation f x
interpretHigherOrderFunction functionInterpretation
  (HigherOrderRecursion _) x =
    ?interpretHigherOrderFunction_hole_recursion

public export
HigherOrderFuncInterpretation :
  {penv : PrimitiveEnv} ->
  {pfenv : HigherOrderPrimFuncEnv penv} ->
  {typeInterpretation :
    PrimitiveTypeInterpretation (HigherOrderPrimEnv penv)} ->
  (functionInterpretation :
    PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
  PrimitiveFunctionInterpretation {penv=(HigherOrderPrimEnv penv)}
    (HigherOrderFuncEnv pfenv) typeInterpretation
HigherOrderFuncInterpretation =
  PrimitiveFunctionInterpretations . interpretHigherOrderFunction
