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

public export
interpretsFromVoid : {x : RefinedSExp} -> (checked : CheckedRefinement x) ->
  interpretMorphism (RSFromVoid x) RSVoid x
    {checked=(decEqReflYes {deq=RefinedSExp.AlgebraicSExp.rsDecEq} {x})}
      = (\v => void v)
interpretsFromVoid _ = Refl

export
algebraicSExpInterpretationTests : IO ()
algebraicSExpInterpretationTests = pure ()
