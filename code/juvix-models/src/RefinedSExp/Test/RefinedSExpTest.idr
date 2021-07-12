module RefinedSExp.Test.RefinedSExpTest

import public RefinedSExp.RefinedSExp
import RefinedSExp.Test.SExpTest
import RefinedSExp.Test.TestLibrary

%default total

-- Provide a "default" primitive type.

public export
data PrimitiveType : Type where
  PrimTypeBool : PrimitiveType
  PrimTypeNat : PrimitiveType
  PrimTypeString : PrimitiveType

-- Haskell can just derive this.
export
primTypeEq : (primType, primType' : PrimitiveType) -> Dec (primType = primType')
primTypeEq PrimTypeBool PrimTypeBool = Yes Refl
primTypeEq PrimTypeBool PrimTypeNat = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeBool PrimTypeString = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeNat PrimTypeBool = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeNat PrimTypeNat = Yes Refl
primTypeEq PrimTypeNat PrimTypeString = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeBool = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeNat = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeString = Yes Refl

interpretPrimitiveType : PrimitiveType -> Type
interpretPrimitiveType PrimTypeBool = Bool
interpretPrimitiveType PrimTypeNat = Nat
interpretPrimitiveType PrimTypeString = String

public export
primitiveEq : (primType : PrimitiveType) ->
  (x, x' : interpretPrimitiveType primType) -> Dec (x = x')
primitiveEq PrimTypeBool = decEq
primitiveEq PrimTypeNat = decEq
primitiveEq PrimTypeString = decEq

public export
PrimitiveExp : Type
PrimitiveExp = DPair PrimitiveType interpretPrimitiveType

primExpEq : (primExp, primExp' : PrimitiveExp) -> Dec (primExp = primExp')
primExpEq (primType ** primExp) (primType' ** primExp') with
  (primTypeEq primType primType')
    primExpEq (primType ** primExp) (primType ** primExp') | Yes Refl =
      case primitiveEq primType primExp primExp' of
        Yes Refl => Yes Refl
        No neq => No (\eq => case eq of Refl => neq Refl)
    primExpEq (primType ** primExp) (primType' ** primExp') | No neq =
      No (\eq => case eq of Refl => neq Refl)

TestSExp : Type
TestSExp = SExp PrimitiveExp

TestSList : Type
TestSList = SList PrimitiveExp

sexpShows : {atom : Type} -> (showAtom : atom -> String) ->
  (SExp atom -> String, SList atom -> List String)
sexpShows showAtom =
  sexpNonDepContextFreeListFolds
    (SExpNonDepContextFreeFoldListArgs
      (\a, l, s => case l of
        [] => "$(" ++ showAtom a ++ ")"
        _ => "$(" ++ showAtom a ++ ":" ++
          (foldl Prelude.Strings.(++) "" s) ++ ")\n"))

Show atom => Show (SExp atom) where
  show x = show' x where
    show' : SExp atom -> String
    show' x = case x of (a $: _) => fst (sexpShows show) x

nilNotationTest : SList Nat
nilNotationTest = ($|)

bigNotationTest : SExp Nat
bigNotationTest =
  0 $:
  (1 $: 2 $:^ 3) $+
  (4 $: 5 $^+ (6 $: 7 $^+ (8 $: 9 $:^ 10) $+^ 11) $+ 12 $:^ 13) $+
  14 $^+
  15 $^+
  (16 $: 17 $:^ 18) $+
  (19 $^^ 20) $+^
  21

Show PrimitiveExp where
  show (PrimTypeBool ** b) = show b
  show (PrimTypeNat ** n) = show n
  show (PrimTypeString ** s) = s

testShowTestSExp : TestSExp
testShowTestSExp = $^ (PrimTypeBool ** True)

export
refinedSExpTests : IO ()
refinedSExpTests = do
  printLn nilNotationTest
  printLn bigNotationTest
  printLn testShowTestSExp
