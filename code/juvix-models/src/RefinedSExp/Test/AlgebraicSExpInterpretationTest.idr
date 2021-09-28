module RefinedSExp.Test.AlgebraicSExpInterpretationTest

import public RefinedSExp.AlgebraicSExpInterpretation
import RefinedSExp.Test.AlgebraicSExpTest
import Library.Test.TestLibrary

%default total

public export
interpretsVoid : interpretRefinement RSVoid = Void
interpretsVoid = Refl

export
algebraicSExpInterpretationTests : IO ()
algebraicSExpInterpretationTests = pure ()
