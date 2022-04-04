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
gtcEncode : RADTClass -> Nat
gtcEncode RADTCcat = 0
gtcEncode RADTCobj = 1
gtcEncode RADTCmorph = 2

export
gtcDecode : Nat -> Maybe RADTClass
gtcDecode 0 = Just RADTCcat
gtcDecode 1 = Just RADTCobj
gtcDecode 2 = Just RADTCmorph
gtcDecode _ = Nothing

export
gtcDecodeEncodeIsJust : (a : RADTClass) -> gtcDecode (gtcEncode a) = Just a
gtcDecodeEncodeIsJust RADTCcat = Refl
gtcDecodeEncodeIsJust RADTCobj = Refl
gtcDecodeEncodeIsJust RADTCmorph = Refl

export
gtcToString : RADTClass -> String
gtcToString RADTCcat = "Category"
gtcToString RADTCobj = "Object"
gtcToString RADTCmorph = "Morphism"

export
Show RADTClass where
  show a = gtcToString a

export
gtcEq : RADTClass -> RADTClass -> Bool
gtcEq a a' = gtcEncode a == gtcEncode a'

export
Eq RADTClass where
  (==) = gtcEq

export
Ord RADTClass where
  a < a' = gtcEncode a < gtcEncode a'

export
gtcDecEq : (a, a' : RADTClass) -> Dec (a = a')
gtcDecEq = encodingDecEq gtcEncode gtcDecode gtcDecodeEncodeIsJust decEq

export
DecEq RADTClass where
  decEq = gtcDecEq
