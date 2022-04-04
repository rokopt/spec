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
  TTCcat : TermTypeClass
  TTCobject : TermTypeClass

public export
GebTermClass : Type
GebTermClass = (CategoryClass, TermTypeClass)

export
gtcEncode : TermTypeClass -> Nat
gtcEncode TTCcat = 0
gtcEncode TTCobject = 1

export
gtcDecode : Nat -> Maybe TermTypeClass
gtcDecode 0 = Just TTCcat
gtcDecode 1 = Just TTCobject
gtcDecode _ = Nothing

export
gtcDecodeEncodeIsJust :
  (a : TermTypeClass) -> gtcDecode (gtcEncode a) = Just a
gtcDecodeEncodeIsJust TTCcat = Refl
gtcDecodeEncodeIsJust TTCobject = Refl

export
gtcToString : TermTypeClass -> String
gtcToString TTCcat = "Category"
gtcToString TTCobject = "Object"

export
Show TermTypeClass where
  show a = gtcToString a

export
gtcEq : TermTypeClass -> TermTypeClass -> Bool
gtcEq a a' = gtcEncode a == gtcEncode a'

export
Eq TermTypeClass where
  (==) = gtcEq

export
Ord TermTypeClass where
  a < a' = gtcEncode a < gtcEncode a'

export
gtcDecEq : (a, a' : TermTypeClass) -> Dec (a = a')
gtcDecEq = encodingDecEq gtcEncode gtcDecode gtcDecodeEncodeIsJust decEq

export
DecEq TermTypeClass where
  decEq = gtcDecEq
