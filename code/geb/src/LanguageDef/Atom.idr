module LanguageDef.Atom

import Library.IdrisUtils

%default total

-- This module implements decidable equalities and ordering and such
-- on enumerated types -- the kind of thing that a `deriving`
-- mechanism would provide automatically.

------------------------------------------------
------------------------------------------------
---- Classification used in `RefinedADTCat` ----
------------------------------------------------
------------------------------------------------

public export
data RefinedCat : Type where
  RefinedSubst : RefinedCat
  RefinedADT : RefinedCat

public export
data RADTClass : Type where
  RADTCcat : RADTClass
  GTCObject : RADTClass
  RADTCobjOrder1 : RADTClass

public export
GebTermIndex : Type
GebTermIndex = (RefinedCat, RADTClass)

export
radtcEncode : RADTClass -> Nat
radtcEncode RADTCcat = 0
radtcEncode GTCObject = 1
radtcEncode RADTCobjOrder1 = 2

export
radtcDecode : Nat -> Maybe RADTClass
radtcDecode 0 = Just RADTCcat
radtcDecode 1 = Just GTCObject
radtcDecode 2 = Just RADTCobjOrder1
radtcDecode _ = Nothing

export
radtcDecodeEncodeIsJust :
  (a : RADTClass) -> radtcDecode (radtcEncode a) = Just a
radtcDecodeEncodeIsJust RADTCcat = Refl
radtcDecodeEncodeIsJust GTCObject = Refl
radtcDecodeEncodeIsJust RADTCobjOrder1 = Refl

export
radtcToString : RADTClass -> String
radtcToString RADTCcat = "Category"
radtcToString GTCObject = "SubstObject"
radtcToString RADTCobjOrder1 = "ADTObject"

export
Show RADTClass where
  show a = radtcToString a

export
radtcEq : RADTClass -> RADTClass -> Bool
radtcEq a a' = radtcEncode a == radtcEncode a'

export
Eq RADTClass where
  (==) = radtcEq

export
Ord RADTClass where
  a < a' = radtcEncode a < radtcEncode a'

export
radtcDecEq : (a, a' : RADTClass) -> Dec (a = a')
radtcDecEq = encodingDecEq radtcEncode radtcDecode radtcDecodeEncodeIsJust decEq

export
DecEq RADTClass where
  decEq = radtcDecEq
