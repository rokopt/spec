module LanguageDef.Atom

import Library.IdrisUtils

%default total

-- This module implements decidable equalities and ordering and such
-- on enumerated types -- the kind of thing that a `deriving`
-- mechanism would provide automatically.

---------------------------------
---------------------------------
---- Atoms used in `GebTerm` ----
---------------------------------
---------------------------------

public export
data CategoryClass : Type where
  Subst : CategoryClass
  RefinedSubst : CategoryClass
  ADT : CategoryClass
  RefinedADT : CategoryClass

public export
data TermClass : Type where
  TCterm : TermClass
  TCtype : TermClass
  TCfunction : TermClass

public export
GebTermClass : Type
GebTermClass = (CategoryClass, TermClass)

export
gtcEncode : GebTermClass -> Nat
gtcEncode (Subst, TCterm) = 0
gtcEncode (Subst, TCtype) = 1
gtcEncode (Subst, TCfunction) = 2
gtcEncode (RefinedSubst, TCterm) = 3
gtcEncode (RefinedSubst, TCtype) = 4
gtcEncode (RefinedSubst, TCfunction) = 5
gtcEncode (ADT, TCterm) = 6
gtcEncode (ADT, TCtype) = 7
gtcEncode (ADT, TCfunction) = 8
gtcEncode (RefinedADT, TCterm) = 9
gtcEncode (RefinedADT, TCtype) = 10
gtcEncode (RefinedADT, TCfunction) = 11

export
gtcDecode : Nat -> Maybe GebTermClass
gtcDecode 0 = Just (Subst, TCterm)
gtcDecode 1 = Just (Subst, TCtype)
gtcDecode 2 = Just (Subst, TCfunction)
gtcDecode 3 = Just (RefinedSubst, TCterm)
gtcDecode 4 = Just (RefinedSubst, TCtype)
gtcDecode 5 = Just (RefinedSubst, TCfunction)
gtcDecode 6 = Just (ADT, TCterm)
gtcDecode 7 = Just (ADT, TCtype)
gtcDecode 8 = Just (ADT, TCfunction)
gtcDecode 9 = Just (RefinedADT, TCterm)
gtcDecode 10 = Just (RefinedADT, TCtype)
gtcDecode 11 = Just (RefinedADT, TCfunction)
gtcDecode _ = Nothing

export
gtcDecodeEncodeIsJust :
  (a : GebTermClass) -> gtcDecode (gtcEncode a) = Just a
gtcDecodeEncodeIsJust (Subst, TCterm) = Refl
gtcDecodeEncodeIsJust (Subst, TCtype) = Refl
gtcDecodeEncodeIsJust (Subst, TCfunction) = Refl
gtcDecodeEncodeIsJust (RefinedSubst, TCterm) = Refl
gtcDecodeEncodeIsJust (RefinedSubst, TCtype) = Refl
gtcDecodeEncodeIsJust (RefinedSubst, TCfunction) = Refl
gtcDecodeEncodeIsJust (ADT, TCterm) = Refl
gtcDecodeEncodeIsJust (ADT, TCtype) = Refl
gtcDecodeEncodeIsJust (ADT, TCfunction) = Refl
gtcDecodeEncodeIsJust (RefinedADT, TCterm) = Refl
gtcDecodeEncodeIsJust (RefinedADT, TCtype) = Refl
gtcDecodeEncodeIsJust (RefinedADT, TCfunction) = Refl

export
gtcToString : GebTermClass -> String
gtcToString (Subst, TCterm) = "SubstTerm"
gtcToString (Subst, TCtype) = "SubstType"
gtcToString (Subst, TCfunction) = "SubstFunction"
gtcToString (RefinedSubst, TCterm) = "RefinedSubstTerm"
gtcToString (RefinedSubst, TCtype) = "RefinedSubstType"
gtcToString (RefinedSubst, TCfunction) = "RefinedSubstFunction"
gtcToString (ADT, TCterm) = "ADTTerm"
gtcToString (ADT, TCtype) = "ADTType"
gtcToString (ADT, TCfunction) = "ADTFunction"
gtcToString (RefinedADT, TCterm) = "RefinedADTTerm"
gtcToString (RefinedADT, TCtype) = "RefinedADTType"
gtcToString (RefinedADT, TCfunction) = "RefinedADTFunction"

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
