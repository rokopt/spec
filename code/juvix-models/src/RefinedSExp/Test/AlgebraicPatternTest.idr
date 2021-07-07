module RefinedSExp.Test.AlgebraicPatternTest

import public RefinedSExp.AlgebraicPattern
import Library.Decidability

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

TAtom : Type
TAtom = MAtom interpretPrimitiveType

TBool : Bool -> TAtom
TBool = MPrim {type=PrimTypeBool}

TNat : Nat -> TAtom
TNat = MPrim {type=PrimTypeNat}

TString : String -> TAtom
TString = MPrim {type=PrimTypeString}

TExp : Type
TExp = SExp TAtom

TList : Type
TList = SList TAtom

TCheckResult : TExp -> Type
TCheckResult =
  CheckResult (MatchesTypeInduction primTypeEq interpretPrimitiveType)

TListCheckResult : TList -> Type
TListCheckResult =
  ListCheckResult (MatchesTypeInduction primTypeEq interpretPrimitiveType)

public export
testMatch : (x : TExp) -> TCheckResult x
testMatch = matchSExp primTypeEq interpretPrimitiveType

testListMatch : (x : TList) -> TListCheckResult x
testListMatch = matchSList primTypeEq interpretPrimitiveType

-- Empty constructor
Uc : TCP
Uc = |- []

-- Unit type
Ut : ADTP
Ut = |* [ Uc ]

-- Primitive boolean type
Bt : DTP
Bt = |. PrimTypeBool

public export
primChecks : Bool
primChecks =
  isCheckSuccess (testMatch ($^ (TBool True))) &&
  isCheckSuccess (testMatch ($^ (TBool False))) &&
  isCheckSuccess (testMatch ($^ (TNat 0)))

-- Boolean equivalents without using primitive types
Bta : ADTP
Bta = |* [ Uc, Uc ]

Btd : DTP
Btd = |: Bta

public export
boolChecks : Bool
boolChecks =
  isCheckSuccess (testMatch ($^ (MAbst Bta 0))) &&
  isCheckSuccess (testMatch ($^ (MAbst Bta 1))) &&
  isCheckFailure (testMatch ($^ (MAbst Bta 2))) && -- out-of-bounds constructor
  isCheckFailure (testMatch (MAbst Bta 0 $^^ MAbst Bta 0)) -- extra parameter

-- Primitive natural number
Nt : DTP
Nt = |. PrimTypeNat

-- Primitive string
St : DTP
St = |. PrimTypeString

-- Constructor containing two natural numbers
N2c : TCP
N2c = |- [ |-> Nt , |-> Nt ]

-- Constructor containing one string
Sc : TCP
Sc = |- [ |-> St ]

-- ADT comprising either two natural numbers or one string
N2Sta : ADTP
N2Sta = |* [ N2c , Sc ]

N2Std : DTP
N2Std = |: N2Sta

adtChecks : Bool
adtChecks =
  isCheckFailure (testMatch ($^ (MAbst N2Sta 0)))

adtChecksCorrect : Assertion
adtChecksCorrect = Assert adtChecks

boolChecksCorrect : Assertion
boolChecksCorrect = Assert boolChecks

primChecksCorrect : Assertion
primChecksCorrect = Assert primChecks

-- Test some notation

typeNotationTest : |:* [ Uc, Uc ] = |: (|* [ Uc, Uc ])
typeNotationTest = Refl

getConstructorTest_Bta_0 : Bta |*< 0 = Uc
getConstructorTest_Bta_0 = Refl

getConstructorTest_Bta_1 : Bta |*< 1 = Uc
getConstructorTest_Bta_1 = Refl
