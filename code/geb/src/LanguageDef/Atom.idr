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
data CategoryClass : Type where
  RefinedSubst : CategoryClass
  RefinedADT : CategoryClass

public export
data TermTypeClass : Type where
  TTCcat : TermTypeClass
  TTCobject : TermTypeClass

public export
GebTermClass : Type
GebTermClass = (CategoryClass, TermTypeClass)

export
gtcEncode : GebTermClass -> Nat
gtcEncode (RefinedSubst, TTCcat) = 0
gtcEncode (RefinedSubst, TTCobject) = 1
gtcEncode (RefinedADT, TTCcat) = 2
gtcEncode (RefinedADT, TTCobject) = 3

export
gtcDecode : Nat -> Maybe GebTermClass
gtcDecode 0 = Just (RefinedSubst, TTCcat)
gtcDecode 1 = Just (RefinedSubst, TTCobject)
gtcDecode 2 = Just (RefinedADT, TTCcat)
gtcDecode 3 = Just (RefinedADT, TTCobject)
gtcDecode _ = Nothing

export
gtcDecodeEncodeIsJust :
  (a : GebTermClass) -> gtcDecode (gtcEncode a) = Just a
gtcDecodeEncodeIsJust (RefinedSubst, TTCcat) = Refl
gtcDecodeEncodeIsJust (RefinedSubst, TTCobject) = Refl
gtcDecodeEncodeIsJust (RefinedADT, TTCcat) = Refl
gtcDecodeEncodeIsJust (RefinedADT, TTCobject) = Refl

export
gtcToString : GebTermClass -> String
gtcToString (RefinedSubst, TTCcat) = "RefinedSubstCat"
gtcToString (RefinedSubst, TTCobject) = "RefinedSubstObject"
gtcToString (RefinedADT, TTCcat) = "RefinedADTCat"
gtcToString (RefinedADT, TTCobject) = "RefinedADTObject"

export
Show GebTermClass where
  show a = gtcToString a

export
gtcEq : GebTermClass -> GebTermClass -> Bool
gtcEq a a' = gtcEncode a == gtcEncode a'

export
Eq GebTermClass where
  (==) = gtcEq

export
Ord GebTermClass where
  a < a' = gtcEncode a < gtcEncode a'

export
gtcDecEq : (a, a' : GebTermClass) -> Dec (a = a')
gtcDecEq = encodingDecEq gtcEncode gtcDecode gtcDecodeEncodeIsJust decEq

export
DecEq GebTermClass where
  decEq = gtcDecEq
