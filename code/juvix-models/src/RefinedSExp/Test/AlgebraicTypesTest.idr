module RefinedSExp.Test.AlgebraicTypesTest

import public RefinedSExp.AlgebraicTypes
import RefinedSExp.Test.TestLibrary
import Library.FunctionsAndRelations

%default total

public export
TestPrimEnv : PrimitiveEnv
TestPrimEnv = PrimArgs PrimitiveType

public export
TestPrimTypeInterpretation : AlgebraicTypeInterpretation TestPrimEnv
TestPrimTypeInterpretation = AlgebraicTypeInterpretations interpretPrimitiveType

-- At the moment, this test environment just provides all
-- metalanguage functions on the algebraic closure of the
-- primitive types as generator functions.
public export
TestPrimFuncEnv : PrimitiveFuncEnv TestPrimEnv
TestPrimFuncEnv = CompletePrimitiveFuncEnv TestPrimTypeInterpretation

public export
TestPrimFuncInterpretation :
  AlgebraicFunctionInterpretation TestPrimFuncEnv TestPrimTypeInterpretation
TestPrimFuncInterpretation =
  CompletePrimitiveFunctionInterpretation TestPrimTypeInterpretation

export
algebraicTypesTests : IO ()
algebraicTypesTests = pure ()
