module Library.Test.IdrisCategoriesTest

import Test.TestLibrary
import Library.IdrisCategories

%default total

testNat0 : NatObj
testNat0 = NatOZ

testNat1 : NatObj
testNat1 = NatO1

testNat2 : NatObj
testNat2 = MetaToNatObj 2

testNat3 : NatObj
testNat3 = MetaToNatObj 3

testNat4 : NatObj
testNat4 = MetaToNatObj 4

testNat5 : NatObj
testNat5 = MetaToNatObj 5

testNat9 : NatObj
testNat9 = MetaToNatObj 9

twoLteFiveMeta : LTE 2 5
twoLteFiveMeta with (isLTE 2 5) proof p
  twoLteFiveMeta | Yes lte = lte
  twoLteFiveMeta | No nlte = case p of Refl impossible

twoLteFive : NatLTMorph (MetaToNatObj 2, MetaToNatObj 5)
twoLteFive = LTEToNatMorph {mn=(2, 5)} twoLteFiveMeta

zeroPlusThree : Assertion
zeroPlusThree = Assert $ natObjSum testNat0 testNat3 == testNat3

threePlusZero : Assertion
threePlusZero = Assert $ natObjSum testNat3 testNat0 == testNat3

twoPlusThree : Assertion
twoPlusThree = Assert $ natObjSum testNat2 testNat3 == testNat5

threePlusTwo : Assertion
threePlusTwo = Assert $ natObjSum testNat2 testNat3 == testNat5

fiveMinusTwo : Assertion
fiveMinusTwo = Assert $ natObjMinus twoLteFive == testNat3

export
libraryIdrisCategoriesTest : IO ()
libraryIdrisCategoriesTest = do
  -- printLn "Begin libraryIdrisCategoriesTest:"
  -- printLn "End libraryIdrisCategoriesTest."
  pure ()
