module RefinedSExp.Test.DatatypesTest

import public RefinedSExp.Datatypes
import public RefinedSExp.Test.AlgebraicTypesTest
import RefinedSExp.Test.TestLibrary
import Library.FunctionsAndRelations

%default total

TestDataType : Type
TestDataType = Datatype TestPrimEnv

TestRecord : Type
TestRecord = RecordType TestPrimEnv

export
datatypesTests : IO ()
datatypesTests = pure ()
