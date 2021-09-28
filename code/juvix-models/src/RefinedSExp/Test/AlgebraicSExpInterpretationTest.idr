module RefinedSExp.Test.AlgebraicSExpInterpretationTest

import public RefinedSExp.AlgebraicSExpInterpretation
import RefinedSExp.Test.AlgebraicSExpTest
import Library.Test.TestLibrary

%default total

public export
interpretsVoid : interpretRefinement RSVoid = Void
interpretsVoid = Refl

public export
interpretsUnit : interpretRefinement RSUnit = Unit
interpretsUnit = Refl

public export
interpretsList : interpretRefinementList [RSVoid, RSUnit] = [Void, Unit]
interpretsList = Refl

export
algebraicSExpInterpretationTests : IO ()
algebraicSExpInterpretationTests = pure ()
