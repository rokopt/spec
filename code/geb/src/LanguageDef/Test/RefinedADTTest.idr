module LanguageDef.Test.RefinedADTTest

import Test.TestLibrary
import LanguageDef.RefinedADT

%default total

exampleFinNatPoly : FinNatPoly
exampleFinNatPoly = InitFinNatPoly [4, 0, 2, 3]

finNatPolyTest : Assertion
finNatPolyTest = Assert $ interpretFinNatPoly exampleFinNatPoly 7 == 1389

finOrdMorphTest1 : FinOrdMorph 3 2
finOrdMorphTest1 = MkFinOrdMorph 3 2 [0, 1, 1]

finOrdMorphTest2 : Assertion
finOrdMorphTest2 = Assert $ isNothing (listToFinOrdMorph 3 2 [0, 1, 2])

finOrdMorphTest3 : Assertion
finOrdMorphTest3 = Assert $ isNothing (listToFinOrdMorph 3 2 [0, 1, 0])

finOrdMorphTest4 : Assertion
finOrdMorphTest4 = Assert $ isNothing (listToFinOrdMorph 3 2 [1, 0, 1])

finOrdMorphTest5 : FinOrdMorph 0 0
finOrdMorphTest5 = MkFinOrdMorph 0 0 []

finOrdMorphTest6 : FinOrdMorph 0 1
finOrdMorphTest6 = MkFinOrdMorph 0 1 []

finOrdMorphTest7 : FinOrdMorph 0 2
finOrdMorphTest7 = MkFinOrdMorph 0 2 []

finOrdMorphTest8 : Assertion
finOrdMorphTest8 = Assert $ isNothing (listToFinOrdMorph 0 2 [0])

finOrdMorphTest9 : FinOrdMorph 5 20
finOrdMorphTest9 = MkFinOrdMorph 5 20 [3, 7, 7, 13, 19]

finOrdMorphTest10 : Assertion
finOrdMorphTest10 =
  Assert $ isNothing (listToFinOrdMorph 5 20 [3, 7, 6, 13, 19])

finOrdMorphTest11 : FinOrdMorph 0 0
finOrdMorphTest11 = finOrdId 0

finOrdMorphTest12 : FinOrdMorph 1 1
finOrdMorphTest12 = finOrdId 1

finOrdMorphTest13 : FinOrdMorph 2 2
finOrdMorphTest13 = finOrdId 2

finOrdMorphTest14 : FinOrdMorph 3 3
finOrdMorphTest14 = finOrdId 3

finOrdMorphTest15 : FinOrdMorph 4 4
finOrdMorphTest15 = finOrdId 4

export
languageDefRefinedADTTest : IO ()
languageDefRefinedADTTest = do
  printLn "Begin languageDefRefinedADTTest:"
  printLn $ show exampleFinNatPoly
  printLn $ show finOrdMorphTest1
  printLn $ show finOrdMorphTest5
  printLn $ show finOrdMorphTest6
  printLn $ show finOrdMorphTest7
  printLn $ show finOrdMorphTest9
  printLn $ show finOrdMorphTest11
  printLn $ show finOrdMorphTest12
  printLn $ show finOrdMorphTest13
  printLn $ show finOrdMorphTest14
  printLn $ show finOrdMorphTest15
  printLn "End languageDefRefinedADTTest."
  pure ()
