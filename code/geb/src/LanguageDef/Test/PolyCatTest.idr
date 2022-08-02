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

powerByMultsTestTerm : PolyTerm
powerByMultsTestTerm = (6, 5)

powerByMultsTest : Assertion
powerByMultsTest = Assert $
  ptInterpNat powerByMultsTestTerm 2 ==
  ptInterpNatByMults powerByMultsTestTerm 2

polyS0Scaled : PolyShape
polyS0Scaled = scalePolyShape 3 testPolyS0

testPoly0Scale : Assertion
testPoly0Scale = Assert $ polyS0Scaled == [(5, 9), (4, 33), (2, 3)]

testPoly0ScaleZero : Assertion
testPoly0ScaleZero = Assert $ scalePolyShape 0 testPolyS0 == []

sumViaMu : Nat -> Nat -> Nat
sumViaMu m n = muToNat $ natSum (natToMu m) (natToMu n)

mulViaMu : Nat -> Nat -> Nat
mulViaMu m n = muToNat $ natMul (natToMu m) (natToMu n)

powViaMu : Nat -> Nat -> Nat
powViaMu m n = muToNat $ natPow (natToMu m) (natToMu n)

testMuNatSum0 : Assertion
testMuNatSum0 = Assert $ sumViaMu 0 0 == 0

testMuNatSum1 : Assertion
testMuNatSum1 = Assert $ sumViaMu 0 1 == 1

testMuNatSum2 : Assertion
testMuNatSum2 = Assert $ sumViaMu 1 0 == 1

testMuNatSum3 : Assertion
testMuNatSum3 = Assert $ sumViaMu 1 1 == 2

testMuNatSum4 : Assertion
testMuNatSum4 = Assert $ sumViaMu 1 2 == 3

testMuNatSum5 : Assertion
testMuNatSum5 = Assert $ sumViaMu 2 1 == 3

testMuNatSum6 : Assertion
testMuNatSum6 = Assert $ sumViaMu 2 2 == 4

testMuNatSum7 : Assertion
testMuNatSum7 = Assert $ sumViaMu 12 7 == 19

testMuNatMul0 : Assertion
testMuNatMul0 = Assert $ mulViaMu 0 0 == 0

testMuNatMul1 : Assertion
testMuNatMul1 = Assert $ mulViaMu 0 1 == 0

testMuNatMul2 : Assertion
testMuNatMul2 = Assert $ mulViaMu 1 0 == 0

testMuNatMul3 : Assertion
testMuNatMul3 = Assert $ mulViaMu 1 1 == 1

testMuNatMul4 : Assertion
testMuNatMul4 = Assert $ mulViaMu 1 2 == 2

testMuNatMul5 : Assertion
testMuNatMul5 = Assert $ mulViaMu 2 1 == 2

testMuNatMul6 : Assertion
testMuNatMul6 = Assert $ mulViaMu 2 2 == 4

testMuNatMul7 : Assertion
testMuNatMul7 = Assert $ mulViaMu 12 7 == 84

testMuNatPow0 : Assertion
testMuNatPow0 = Assert $ powViaMu 0 0 == 1

testMuNatPow1 : Assertion
testMuNatPow1 = Assert $ powViaMu 0 1 == 0

testMuNatPow2 : Assertion
testMuNatPow2 = Assert $ powViaMu 1 0 == 1

testMuNatPow3 : Assertion
testMuNatPow3 = Assert $ powViaMu 1 1 == 1

testMuNatPow4 : Assertion
testMuNatPow4 = Assert $ powViaMu 1 2 == 1

testMuNatPow5 : Assertion
testMuNatPow5 = Assert $ powViaMu 2 1 == 2

testMuNatPow6 : Assertion
testMuNatPow6 = Assert $ powViaMu 2 2 == 4

testMuNatPow7 : Assertion
testMuNatPow7 = Assert $ powViaMu 2 3 == 8

testMuNatPow8 : Assertion
testMuNatPow8 = Assert $ powViaMu 3 2 == 9

testMuNatPow9 : Assertion
testMuNatPow9 = Assert $ powViaMu 4 2 == 16

testMuNatPow10 : Assertion
testMuNatPow10 = Assert $ powViaMu 2 4 == 16

testMuNatPow11 : Assertion
testMuNatPow11 = Assert $ powViaMu 2 5 == 32

testMuNatPow12 : Assertion
testMuNatPow12 = Assert $ powViaMu 5 2 == 25

testMuNatPow13 : Assertion
testMuNatPow13 = Assert $ powViaMu 5 3 == 125

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
  putStrLn $ show testPoly6
  putStrLn "--------------------"
  putStrLn ""
  putStrLn "------------------------"
  putStrLn "Idris Nat implementation"
  putStrLn "------------------------"
  putStrLn $ show (power 2 0)
  putStrLn $ show (power 2 10)
  putStrLn $ show (power 2 20)
  putStrLn $ show (power 2 30)
  putStrLn $ show (power 2 40)
  putStrLn $ show (power 2 50)
  putStrLn $ show (power 2 60)
  putStrLn $ show (power 2 64)
  putStrLn $ show (power 2 65)
  putStrLn $ show (power 2 100)
  putStrLn $ show (power 2 1000)
  putStrLn $ show (power 2 10000)
  putStrLn $ show $ ptInterpNat powerByMultsTestTerm 2
  putStrLn ""
  putStrLn "------"
  putStrLn "MuNatO"
  putStrLn "------"
  putStrLn $ show (natToMu 10)
  putStrLn ""
  putStrLn "End polyCatTest."
  putStrLn "=================="
  pure ()
