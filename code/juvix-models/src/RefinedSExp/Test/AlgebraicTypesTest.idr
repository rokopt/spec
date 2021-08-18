module RefinedSExp.Test.AlgebraicTypesTest

import public RefinedSExp.AlgebraicTypes
import RefinedSExp.Test.TestLibrary
import Library.FunctionsAndRelations

%default total

TestPrimEnv : PrimitiveEnv
TestPrimEnv = PrimArgs PrimitiveType interpretPrimitiveType

-- At the moment, this test environment just provides all
-- metalanguage functions on the algebraic closure of the
-- primitive types as generator functions.
TestPrimFuncEnv : PrimitiveFuncEnv TestPrimEnv
TestPrimFuncEnv = PrimFuncs interpretAlgebraicFunctionType id

export
algebraicTypesTests : IO ()
algebraicTypesTests = pure ()
