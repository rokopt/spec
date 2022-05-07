module LanguageDef.Test.RefinedADTTest

import Test.TestLibrary
import LanguageDef.RefinedADT

%default total

exampleFinNatPoly : FinNatPoly
exampleFinNatPoly = InitFinNatPoly [4, 0, 2, 3]

finNatPolyTest : Assertion
finNatPolyTest = Assert $ interpretFinNatPoly exampleFinNatPoly 7 == 1389

export
languageDefRefinedADTTest : IO ()
languageDefRefinedADTTest = do
  printLn "Begin languageDefRefinedADTTest:"
  printLn $ show exampleFinNatPoly
  printLn "End languageDefRefinedADTTest."
  pure ()
