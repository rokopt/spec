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

testPolyS0 : PolyShape
testPolyS0 = [(5, 3), (4, 11), (2, 1)]

testPolyS1 : PolyShape
testPolyS1 = [(5, 3), (4, 11), (4, 1)]

testPolyS2 : PolyShape
testPolyS2 = [(5, 3), (1, 11), (6, 1)]

testPolyS3 : PolyShape
testPolyS3 = [(5, 3), (1, 11), (0, 3)]

testPolyS4 : PolyShape
testPolyS4 = [(5, 3)]

testPolyS5 : PolyShape
testPolyS5 = []

testPolyS6 : PolyShape
testPolyS6 = [(3, 4), (1, 2), (0, 3)]

poly0Valid : Assertion
poly0Valid = Assert $ validPoly testPolyS0 == True

poly1Valid : Assertion
poly1Valid = Assert $ validPoly testPolyS1 == False

poly2Valid : Assertion
poly2Valid = Assert $ validPoly testPolyS2 == False

poly3Valid : Assertion
poly3Valid = Assert $ validPoly testPolyS3 == True

poly4Valid : Assertion
poly4Valid = Assert $ validPoly testPolyS4 == True

poly5Valid : Assertion
poly5Valid = Assert $ validPoly testPolyS5 == True

poly6Valid : Assertion
poly6Valid = Assert $ validPoly testPolyS6 == True

testPoly0 : Polynomial
testPoly0 = MkPolynomial testPolyS0

testPoly3 : Polynomial
testPoly3 = MkPolynomial testPolyS3

testPoly4 : Polynomial
testPoly4 = MkPolynomial testPolyS4

testPoly5 : Polynomial
testPoly5 = MkPolynomial testPolyS5

testPoly6 : Polynomial
testPoly6 = MkPolynomial testPolyS6

poly0Degree : Assertion
poly0Degree = Assert $ degree testPoly0 == 5

poly5Degree : Assertion
poly5Degree = Assert $ degree testPoly5 == 0

poly0SumCoeff : Assertion
poly0SumCoeff = Assert $ sumCoeff testPoly0 == 15

poly3SumCoeff : Assertion
poly3SumCoeff = Assert $ sumCoeff testPoly3 == 17

poly4SumCoeff : Assertion
poly4SumCoeff = Assert $ sumCoeff testPoly4 == 3

poly5SumCoeff : Assertion
poly5SumCoeff = Assert $ sumCoeff testPoly5 == 0

poly6SumCoeff : Assertion
poly6SumCoeff = Assert $ sumCoeff testPoly6 == 9

poly6Interp : Assertion
poly6Interp = Assert $ polyInterpNat testPoly6 7 == 1389

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
  putStrLn $ show testPoly0
  putStrLn "--------------------"
  putStrLn ""
  putStrLn "End polyCatTest."
  putStrLn "=================="
  pure ()
