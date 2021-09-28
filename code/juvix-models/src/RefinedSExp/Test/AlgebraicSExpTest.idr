module RefinedSExp.Test.AlgebraicSExpTest

import Library.Test.TestLibrary
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

export
algebraicSExpTests : IO ()
algebraicSExpTests = pure ()
