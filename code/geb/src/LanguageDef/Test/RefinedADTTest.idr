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

finOrdMorphTest16 : NatRangeMap 3 9 1 10
finOrdMorphTest16 = MkNatRange 3 9 1 10 2 [2, 4, 5, 5, 9, 10]

finOrdMorphTest17 : NatRangeMap 1 10 3 7
finOrdMorphTest17 = MkNatRange 1 10 3 7 3 [3, 3, 3, 3, 4, 5, 6, 6, 7]

finOrdMorphTest18 : NatRangeMap 3 9 3 7
finOrdMorphTest18 = natRangeCompose finOrdMorphTest17 finOrdMorphTest16

data TestType : Type where
  TestTypeN : Nat -> TestType

Show TestType where
  show (TestTypeN n) = "Fin-" ++ show n

interpTestType : TestType -> Type
interpTestType (TestTypeN n) = Fin n

testCovarHomFunc : CovarRepF TestType Void
testCovarHomFunc = CovarHom (TestTypeN 3)

TestCovarType : Type
TestCovarType =
  interpCovarRepF interpTestType testCovarHomFunc (TestTypeN 2)

testCovar : TestCovarType
testCovar FZ = FS (FS (FZ))
testCovar (FS FZ) = FZ

testContravarHomFunc : ContravarRepF TestType Void
testContravarHomFunc = ContravarHom (TestTypeN 3)

TestContravarType : Type
TestContravarType =
  interpContravarRepF interpTestType testContravarHomFunc (TestTypeN 2)

testContravar : TestContravarType
testContravar FZ = FS (FZ)
testContravar (FS FZ) = FZ
testContravar (FS (FS FZ)) = FS (FZ)

fsObjTest1 : MuS0EF
fsObjTest1 = (!+)

fsObjTest2 : MuS0EF
fsObjTest2 = :>: ((!+) :+: (!+) :+: (!*))

public export
adt0ShowTest : ADT0ObjF Void
adt0ShowTest = ADT0Initial

export
languageDefRefinedADTTest : IO ()
languageDefRefinedADTTest = do
  printLn "Begin languageDefRefinedADTTest:"
  {-
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
  printLn $ show finOrdMorphTest16
  printLn $ show finOrdMorphTest17
  printLn $ show finOrdMorphTest18
  printLn $ show testCovarHomFunc
  printLn $ show testContravarHomFunc
  printLn $ show fsObjTest1
  printLn $ show fsObjTest2
  printLn $ show fsObjTest2
  -}
  printLn $ show adt0ShowTest
  printLn "End languageDefRefinedADTTest."
  pure ()
