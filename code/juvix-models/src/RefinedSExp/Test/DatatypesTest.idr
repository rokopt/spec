module RefinedSExp.Test.DatatypesTest

import public RefinedSExp.Datatypes
import RefinedSExp.Test.TestLibrary
import Library.FunctionsAndRelations

%default total

TestPrimEnv : PrimitiveEnv
TestPrimEnv = PrimArgs PrimitiveType interpretPrimitiveType

-- At the moment, this test environment just provides all
-- metalanguage functions on the algebraic closure of the
-- primitive types as generator functions.
TestPrimFuncEnv : PrimitiveFuncEnv TestPrimEnv
TestPrimFuncEnv =
  PrimFuncs
    (\domain, codomain =>
      compileAlgebraicType domain -> compileAlgebraicType codomain)
    id

export
datatypesTests : IO ()
datatypesTests = pure ()
