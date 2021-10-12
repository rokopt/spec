module RefinedSExp.Test.ComputationTest

import public Library.Test.TestLibrary
import public RefinedSExp.Computation

%default total

public export
computationNotationTest : CExp
computationNotationTest =
  CANat 0 $* (CAReflectedMorphism Curry $* CAString "two" $^^ CANat 3) ::
    (CANat 4 $*** (CANat 5 $* (CANat 6 $*** (CAString "seven" $**^ CANat 8)) $:^
      CAReflectedMorphism Turing)) $:^ CAInterpretation Record

export
computationTests : IO ()
computationTests = do
  printLn "Begin computationTests:"
  printLn $ show computationNotationTest
  printLn "End computationTests."
  pure ()
