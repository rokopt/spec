module RefinedSExp.Test.InterpretationTest

import public Library.Test.TestLibrary
import public RefinedSExp.Interpretation
import public RefinedSExp.Test.ComputationTest

%default total

export
failMExp : MExp
failMExp = Fail $* []

export
failEExp : EExp
failEExp = MExpToEExp failMExp

export
testTerm : EExp
testTerm = EAInterpretation Pair $* [ESNat 1, ESString "a"]

export
failAppliedToTerm : EExp
failAppliedToTerm = ESApply failEExp testTerm

export
extraneousFailArgs : EExp
extraneousFailArgs = EAInterpretation Failure $* [ESNat 0]

export
testElimLeft : EExp
testElimLeft = ESApply (EAMorphism ProductElimLeft $* []) testTerm

export
testElimRight : EExp
testElimRight = ESApply (EAMorphism ProductElimRight $* []) testTerm

export
interpretationTests : IO ()
interpretationTests = do
  printLn "Beginning interpretationTests."
  printLn ("failMExp = " ++ show failMExp)
  printLn ("failEExp = " ++ show failEExp)
  printLn ("one step on failEExp = " ++ show (eexpInterpretStep failEExp))
  printLn ("testTerm = " ++ show testTerm)
  printLn ("failAppliedToTerm = " ++ show failAppliedToTerm)
  printLn ("one step on failAppliedToTerm = " ++
    show (eexpInterpretStep failAppliedToTerm))
  printLn ("two steps on failAppliedToTerm = " ++
    show (eexpInterpretSteps 2 failAppliedToTerm))
  printLn ("three steps on failAppliedToTerm = " ++
    show (eexpInterpretSteps 3 failAppliedToTerm))
  printLn ("extraneousFailArgs = " ++ show extraneousFailArgs)
  printLn ("one step on extraneousFailArgs = " ++
    show (eexpInterpretStep extraneousFailArgs))
  printLn ("four steps on extraneousFailArgs = " ++
    show (eexpInterpretSteps 4 extraneousFailArgs))
  printLn ("testElimLeft = " ++ show testElimLeft)
  printLn ("one step on testElimLeft = " ++
    show (eexpInterpretStep testElimLeft))
  printLn ("four steps on testElimLeft = " ++
    show (eexpInterpretSteps 4 testElimLeft))
  printLn ("two steps on testElimRight = " ++
    show (eexpInterpretSteps 2 testElimRight))
  printLn "Done with interpretationTests."
  pure ()
