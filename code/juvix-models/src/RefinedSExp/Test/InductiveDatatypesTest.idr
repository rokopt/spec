module RefinedSExp.Test.InductiveDatatypesTest

import public RefinedSExp.InductiveDatatypes
import RefinedSExp.Test.TestLibrary
import Library.FunctionsAndRelations
import RefinedSExp.Test.DatatypesTest

%default total

unitType : TestDatatype
unitType = Algebraic AlgebraicUnit

unitConstructor : TestRecord
unitConstructor = Fields [ unitType ]

export
inductiveDatatypesTests : IO ()
inductiveDatatypesTests = pure ()
