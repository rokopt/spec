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
  GTCnat : GTClass
  GTClist : GTClass

export
gtcEncode : GTClass -> Nat
gtcEncode GTCnat = 0
gtcEncode GTClist = 1

export
gtcDecode : Nat -> Maybe GTClass
gtcDecode 0 = Just GTCnat
gtcDecode 1 = Just GTClist
gtcDecode _ = Nothing

export
gtcDecodeEncodeIsJust : (a : GTClass) -> gtcDecode (gtcEncode a) = Just a
gtcDecodeEncodeIsJust GTCnat = Refl
gtcDecodeEncodeIsJust GTClist = Refl

export
gtcToString : GTClass -> String
gtcToString GTCnat = "Nat"
gtcToString GTClist = "List"

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
