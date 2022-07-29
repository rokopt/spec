module LanguageDef.Test.PolyCatTest

import Test.TestLibrary
import LanguageDef.PolyCat

%default total

testBN0 : BoundedNat 7
testBN0 = MkBoundedNat 5

testNT0 : NTuple Nat 3
testNT0 = MkNTuple [11, 0, 5]

testBL0 : BoundedList String 4
testBL0 = MkBoundedList []

testBL1 : BoundedList String 4
testBL1 = MkBoundedList ["a"]

testBL2 : BoundedList String 4
testBL2 = MkBoundedList ["a", "b"]

testBL3 : BoundedList String 4
testBL3 = MkBoundedList ["a", "b", "c"]

testBL4 : BoundedList String 4
testBL4 = MkBoundedList ["a", "b", "c", "d"]

testPoly0 : PolyShape
testPoly0 = [(5, 3), (4, 11), (2, 1)]

testPoly1 : PolyShape
testPoly1 = [(5, 3), (4, 11), (4, 1)]

testPoly2 : PolyShape
testPoly2 = [(5, 3), (1, 11), (6, 1)]

testPoly3 : PolyShape
testPoly3 = [(5, 3), (1, 11)]

testPoly4 : PolyShape
testPoly4 = [(5, 3)]

testPoly5 : PolyShape
testPoly5 = []

poly0Descending : Assertion
poly0Descending = Assert $ descendingPowers testPoly0 == True

poly1Descending : Assertion
poly1Descending = Assert $ descendingPowers testPoly1 == False

poly2Descending : Assertion
poly2Descending = Assert $ descendingPowers testPoly2 == False

poly3Descending : Assertion
poly3Descending = Assert $ descendingPowers testPoly3 == True

poly4Descending : Assertion
poly4Descending = Assert $ descendingPowers testPoly4 == True

poly5Descending : Assertion
poly5Descending = Assert $ descendingPowers testPoly4 == True

export
polyCatTest : IO ()
polyCatTest = do
  putStrLn ""
  putStrLn "=================="
  putStrLn "Begin polyCatTest:"
  putStrLn ""
  putStrLn "---- BoundedNat ----"
  putStrLn $ show testBN0
  putStrLn "--------------------"
  putStrLn ""
  putStrLn "---- NTuple ----"
  putStrLn $ show testNT0
  putStrLn "----------------"
  putStrLn ""
  putStrLn "---- BoundedList ----"
  putStrLn $ show testBL0
  putStrLn $ show testBL1
  putStrLn $ show testBL2
  putStrLn $ show testBL3
  putStrLn $ show testBL4
  putStrLn "---------------------"
  putStrLn ""
  putStrLn "---- Polynomial ----"
  putStrLn "--------------------"
  putStrLn ""
  putStrLn "End polyCatTest."
  putStrLn "=================="
  pure ()
