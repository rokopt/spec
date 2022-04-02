module LanguageDef.Atom

import Library.IdrisUtils

%default total

-- This module implements decidable equalities and ordering and such
-- on enumerated types -- the kind of thing that a `deriving`
-- mechanism would provide automatically.

------------------------------------------
------------------------------------------
---- Classification used in `GebTerm` ----
------------------------------------------
------------------------------------------

public export
data GTClass : Type where
  GTCcat : GTClass
  GTCobj : GTClass
  GTCmorph : GTClass

export
gtcEncode : GTClass -> Nat
gtcEncode GTCcat = 0
gtcEncode GTCobj = 1
gtcEncode GTCmorph = 2

export
gtcDecode : Nat -> Maybe GTClass
gtcDecode 0 = Just GTCcat
gtcDecode 1 = Just GTCobj
gtcDecode 2 = Just GTCmorph
gtcDecode _ = Nothing

export
gtcDecodeEncodeIsJust : (a : GTClass) -> gtcDecode (gtcEncode a) = Just a
gtcDecodeEncodeIsJust GTCcat = Refl
gtcDecodeEncodeIsJust GTCobj = Refl
gtcDecodeEncodeIsJust GTCmorph = Refl

export
gtcToString : GTClass -> String
gtcToString GTCcat = "Category"
gtcToString GTCobj = "Object"
gtcToString GTCmorph = "Morphism"

export
Show GTClass where
  show a = gtcToString a

export
gtcEq : GTClass -> GTClass -> Bool
gtcEq a a' = gtcEncode a == gtcEncode a'

export
Eq GTClass where
  (==) = gtcEq

export
Ord GTClass where
  a < a' = gtcEncode a < gtcEncode a'

export
gtcDecEq : (a, a' : GTClass) -> Dec (a = a')
gtcDecEq = encodingDecEq gtcEncode gtcDecode gtcDecodeEncodeIsJust decEq

export
DecEq GTClass where
  decEq = gtcDecEq
