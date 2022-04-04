module LanguageDef.Atom

import Library.IdrisUtils

%default total

-- This module implements decidable equalities and ordering and such
-- on enumerated types -- the kind of thing that a `deriving`
-- mechanism would provide automatically.

------------------------------------------
------------------------------------------
---- Classification used in `RefinedADTCat` ----
------------------------------------------
------------------------------------------

public export
data RADTClass : Type where
  RADTCcat : RADTClass
  RADTCobj : RADTClass
  RADTCmorph : RADTClass

export
radtcEncode : RADTClass -> Nat
radtcEncode RADTCcat = 0
radtcEncode RADTCobj = 1
radtcEncode RADTCmorph = 2

export
radtcDecode : Nat -> Maybe RADTClass
radtcDecode 0 = Just RADTCcat
radtcDecode 1 = Just RADTCobj
radtcDecode 2 = Just RADTCmorph
radtcDecode _ = Nothing

export
radtcDecodeEncodeIsJust : (a : RADTClass) -> radtcDecode (radtcEncode a) = Just a
radtcDecodeEncodeIsJust RADTCcat = Refl
radtcDecodeEncodeIsJust RADTCobj = Refl
radtcDecodeEncodeIsJust RADTCmorph = Refl

export
radtcToString : RADTClass -> String
radtcToString RADTCcat = "Category"
radtcToString RADTCobj = "Object"
radtcToString RADTCmorph = "Morphism"

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
