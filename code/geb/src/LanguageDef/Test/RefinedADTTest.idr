module LanguageDef.Test.RefinedADTTest

import Test.TestLibrary
import LanguageDef.RefinedADT

%default total

examplePolyList : List Nat
examplePolyList = [4, 0, 2, 3]

exampleFinNatPoly : FinNatPoly
exampleFinNatPoly = InitFinNatPoly examplePolyList

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
testCovar FZ = FS (FZ)
testCovar (FS FZ) = FZ
testCovar (FS (FS FZ)) = FS (FZ)

testContravarHomFunc : ContravarRepF TestType Void
testContravarHomFunc = ContravarHom (TestTypeN 3)

TestContravarType : Type
TestContravarType =
  interpContravarRepF interpTestType testContravarHomFunc (TestTypeN 2)

testContravar : TestContravarType
testContravar FZ = FS (FS (FZ))
testContravar (FS FZ) = FZ

fsObjTest1 : MuS0EF
fsObjTest1 = (!+)

fsObjTest2 : MuS0EF
fsObjTest2 = :>: ((!+) :+: (!+) :+: (!*))

adt0ShowTest : ADT0ObjF Void
adt0ShowTest = ADT0Initial

pzPolyFromObjList : List NatObj -> PZPoly
pzPolyFromObjList [] =
  MkPZPoly NatOZ (const NatOZ)
pzPolyFromObjList (x :: xs) =
  MkPZPoly (MetaToNatObj (length xs)) (sliceArrayFromList x xs)

pzPolyFromList : List Nat -> PZPoly
pzPolyFromList = pzPolyFromObjList . map MetaToNatObj

examplePzPoly : PZPoly
examplePzPoly = pzPolyFromList [3, 2, 0, 3]

examplePzPolyTest : Assertion
examplePzPolyTest = Assert $ pzApplyMeta examplePzPoly 7 == 1389

examplePzPolySum : Assertion
examplePzPolySum = Assert $ NatObjToMeta (pzSumCoeff examplePzPoly) == 9

exampleLongPzPoly : PZPoly
exampleLongPzPoly = pzPolyFromList [0, 1, 2, 3, 4, 5, 6, 7, 7]

exampleEmptyPzPoly : PZPoly
exampleEmptyPzPoly = pzPolyFromList []

exampleZeroPzPoly : PZPoly
exampleZeroPzPoly = pzPolyFromList [0]

exampleOnePzPoly : PZPoly
exampleOnePzPoly = pzPolyFromList [1]

exampleIncZeroPzPoly : PZPoly
exampleIncZeroPzPoly = pzPolyFromList [3, 0]

exampleIncOnePzPoly : PZPoly
exampleIncOnePzPoly = pzPolyFromList [3, 1]

pzArenaFromObjList : List NatObj -> PZArena
pzArenaFromObjList l =
  MkPZArena (MetaToNatObj (length l)) (prefixArrayFromList l)

pzArenaFromList : List Nat -> PZArena
pzArenaFromList = pzArenaFromObjList . map MetaToNatObj

exampleEmptyPzArena : PZArena
exampleEmptyPzArena = pzArenaFromList []

exampleSmallPzArena : PZArena
exampleSmallPzArena = pzArenaFromList [3]

exampleLongPzArena : PZArena
exampleLongPzArena = pzArenaFromList [11, 17, 3, 5, 10, 0, 2]

ex256p1 : PZPoly
ex256p1 = pzPolyFromList [0, 2, 0, 0]

ex256p2 : PZPoly
ex256p2 = pzPolyFromList [2, 0, 1, 0, 0]

ex256p1a : PZArena
ex256p1a = pzToArena ex256p1

ex256p2a : PZArena
ex256p2a = pzToArena ex256p2

ex256onPos : OnPosT RefinedADTTest.ex256p1a RefinedADTTest.ex256p2a
ex256onPos = InitPrefixMap 4 [0, 0, 3]

ex256onDir0List : List Nat
ex256onDir0List = [2, 0, 2, 2]

ex256onDir0 : MetaPrefixMap 4 3
ex256onDir0 = InitPrefixMap 3 ex256onDir0List

ex256onDir1List : List Nat
ex256onDir1List = [0, 0, 0, 0]

ex256onDir1 : MetaPrefixMap 4 1
ex256onDir1 = InitPrefixMap 1 ex256onDir1List

ex256onDir2List : List Nat
ex256onDir2List = []

ex256onDir2 : MetaPrefixMap 0 1
ex256onDir2 = InitPrefixMap 1 ex256onDir2List

ex256onDir :
  OnDirT
    {domain=(RefinedADTTest.ex256p1a)}
    {codomain=(RefinedADTTest.ex256p2a)}
    RefinedADTTest.ex256onPos
ex256onDir =
  InitOnDir {domain=ex256p1a} {codomain=ex256p2a}
    ex256onPos [ex256onDir0List, ex256onDir1List, ex256onDir2List]
    -- {ok=(Refl {x=isJust (onDirFromLists ex256onPos [ex256onDir0List, ex256onDir1List, ex256onDir2List])})}

ex256lens : PZLens RefinedADTTest.ex256p1a RefinedADTTest.ex256p2a
ex256lens = MkPZLens ex256onPos ex256onDir

export
languageDefRefinedADTTest : IO ()
languageDefRefinedADTTest = do
  printLn "Begin languageDefRefinedADTTest:"
  printLn $ show exampleFinNatPoly
  printLn "Begin pzPoly"
  printLn $ show examplePzPoly
  printLn $ show $ pzApplyMeta examplePzPoly 7
  printLn $ show $ pzSumCoeff examplePzPoly
  printLn $ show exampleLongPzPoly
  printLn $ show exampleEmptyPzPoly
  printLn $ show exampleZeroPzPoly
  printLn $ show exampleOnePzPoly
  printLn $ show exampleIncZeroPzPoly
  printLn $ show exampleIncOnePzPoly
  printLn "Begin pzArena"
  printLn $ show exampleEmptyPzArena
  printLn $ show exampleSmallPzArena
  printLn $ show exampleLongPzArena
  printLn "Begin pzPoly -> pzArena"
  printLn $ "Ex 2.56 1st poly: " ++ show ex256p1
  printLn $ "Ex 2.56 2nd poly: " ++ show ex256p2
  printLn $ "Ex 2.56 1st poly as arena: " ++ show ex256p1a
  printLn $ "Ex 2.56 2nd poly as arena: " ++ show ex256p2a
  printLn $ "Ex 2.56 lens onPos: " ++ showPrefixMap ex256onPos
  printLn $ "Ex 2.56 lens onDir[0](cod 0 -> dom 0): " ++ showPrefixMap ex256onDir0
  printLn $ "Ex 2.56 lens onDir[1](cod 0 -> dom 1): " ++ showPrefixMap ex256onDir1
  printLn $ "Ex 2.56 lens onDir[2](cod 3 -> dom 2): " ++ showPrefixMap ex256onDir2
  printLn $ "Ex 2.56 lens onDir: " ++
    showDepPrefixContraMap
      (pzNumDir ex256p1a) (pzNumDir ex256p2a) ex256onPos ex256onDir
  printLn $ "Ex 2.56 lens: " ++ showPZLens ex256lens
  {-
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
  printLn $ show adt0ShowTest
  -}
  printLn "End languageDefRefinedADTTest."
  pure ()
