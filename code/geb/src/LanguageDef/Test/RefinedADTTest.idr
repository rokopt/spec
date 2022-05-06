module LanguageDef.Test.RefinedADTTest

import Test.TestLibrary
import LanguageDef.RefinedADT

%default total

exampleFinNatPoly : FinNatPoly
exampleFinNatPoly = MkFinNatPoly 4 [3, 2, 0, 4, 0]

finNatPolyTest : Assertion
finNatPolyTest = Assert $ interpretFinNatPoly exampleFinNatPoly 7 == 1389

export
languageDefRefinedADTTest : IO ()
languageDefRefinedADTTest = do
  printLn "Begin languageDefRefinedADTTest:"
  printLn "End languageDefRefinedADTTest."
  pure ()
