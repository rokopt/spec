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
testPoly3 = [(5, 3), (1, 11), (0, 3)]

testPoly4 : PolyShape
testPoly4 = [(5, 3)]

testPoly5 : PolyShape
testPoly5 = []

poly0Valid : Assertion
poly0Valid = Assert $ validPoly testPoly0 == False

poly1Valid : Assertion
poly1Valid = Assert $ validPoly testPoly1 == False

poly2Valid : Assertion
poly2Valid = Assert $ validPoly testPoly2 == False

poly3Valid : Assertion
poly3Valid = Assert $ validPoly testPoly3 == True

poly4Valid : Assertion
poly4Valid = Assert $ validPoly testPoly4 == False

poly5Valid : Assertion
poly5Valid = Assert $ validPoly testPoly4 == False

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
