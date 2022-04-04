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
data CategoryClass : Type where
  RefinedSubst : CategoryClass
  RefinedADT : CategoryClass

public export
data TermTypeClass : Type where
  RADTCcat : TermTypeClass
  GTCObject : TermTypeClass

public export
GebTermClass : Type
GebTermClass = (CategoryClass, TermTypeClass)

export
radtcEncode : TermTypeClass -> Nat
radtcEncode RADTCcat = 0
radtcEncode GTCObject = 1

export
radtcDecode : Nat -> Maybe TermTypeClass
radtcDecode 0 = Just RADTCcat
radtcDecode 1 = Just GTCObject
radtcDecode _ = Nothing

export
radtcDecodeEncodeIsJust :
  (a : TermTypeClass) -> radtcDecode (radtcEncode a) = Just a
radtcDecodeEncodeIsJust RADTCcat = Refl
radtcDecodeEncodeIsJust GTCObject = Refl

export
radtcToString : TermTypeClass -> String
radtcToString RADTCcat = "Category"
radtcToString GTCObject = "Object"

export
Show TermTypeClass where
  show a = radtcToString a

export
radtcEq : TermTypeClass -> TermTypeClass -> Bool
radtcEq a a' = radtcEncode a == radtcEncode a'

export
Eq TermTypeClass where
  (==) = radtcEq

export
Ord TermTypeClass where
  a < a' = radtcEncode a < radtcEncode a'

export
radtcDecEq : (a, a' : TermTypeClass) -> Dec (a = a')
radtcDecEq = encodingDecEq radtcEncode radtcDecode radtcDecodeEncodeIsJust decEq

export
DecEq TermTypeClass where
  decEq = radtcDecEq
