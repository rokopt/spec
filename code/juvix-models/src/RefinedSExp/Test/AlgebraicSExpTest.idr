module RefinedSExp.Test.AlgebraicSExpTest

import public Library.Test.TestLibrary
import public RefinedSExp.AlgebraicSExp

%default total

public export
sexpNotationTest : SExp Nat
sexpNotationTest =
  0 $* (1 $* 2 $^^ 3) :: (4 $*** (5 $* (6 $*** (7 $**^ 8)) $:^ 9)) $:^ 10

public export
algebraicNatCorrect : sexpAsObject RSNat = Just RefinedNat
algebraicNatCorrect = Refl

public export
algebraicSuccessorCorrect :
  sexpAsMorphism RSSuccessor = Just (RSNat ** RSNat ** RefinedSuccessor)
algebraicSuccessorCorrect = Refl

public export
checkedVoid : CheckedRefinement RSVoid
checkedVoid = Refl

public export
checkedUnit : CheckedRefinement RSUnit
checkedUnit = Refl

public export
checkedTypeList : CheckedRefinementList [RSVoid, RSUnit]
checkedTypeList = Refl

public export
checkedFromVoid : {x : RefinedSExp} -> CheckedMorphism (RSFromVoid x) RSVoid x
checkedFromVoid = decEqReflYes {deq=decEq}

public export
checkedToUnit : {x : RefinedSExp} -> CheckedMorphism (RSToUnit x) x RSUnit
checkedToUnit = decEqReflYes {deq=decEq}

public export
checkedFunctionList : {x, x' : RefinedSExp} ->
  CheckedMorphismList [RSFromVoid x, RSToUnit x'] [RSVoid, x'] [x, RSUnit]
checkedFunctionList =
  andIntroduction (checkedFromVoid, andIntroduction (checkedToUnit, Refl))

export
algebraicSExpTests : IO ()
algebraicSExpTests = pure ()
