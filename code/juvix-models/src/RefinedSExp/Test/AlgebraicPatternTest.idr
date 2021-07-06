module RefinedSExp.Test.AlgebraicPatternTest

import public RefinedSExp.AlgebraicPattern

%default total

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

TCP : Type
TCP = TypeConstructor PrimitiveType

ADTP : Type
ADTP = ADT PrimitiveType

DTP : Type
DTP = DataType PrimitiveType

TFP : Type
TFP = TypeFamily PrimitiveType

-- Empty constructor
Uc : TCP
Uc = |- []

-- Unit type
Ut : ADTP
Ut = |* [ Uc ]

-- Primitive boolean type
Bt : DTP
Bt = |. PrimTypeBool

-- Boolean equivalents without using primitive types
Bt' : ADTP
Bt' = |* [ Uc, Uc ]

Bt'' : DTP
Bt'' = |: Bt'

-- Test some notation

typeNotationTest : |:* [ Uc, Uc ] = |: (|* [ Uc, Uc ])
typeNotationTest = Refl

getConstructorTest_Bt'_0 : Bt' |*< 0 = Uc
getConstructorTest_Bt'_0 = Refl

getConstructorTest_Bt'_1 : Bt' |*< 1 = Uc
getConstructorTest_Bt'_1 = Refl

-- Successor
Sc : TCP
Sc = ?Sc_hole
