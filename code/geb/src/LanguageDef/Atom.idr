module LanguageDef.Atom

import Library.IdrisUtils

%default total

---------------------------------
---------------------------------
---- Atoms used in `GebTerm` ----
---------------------------------
---------------------------------

public export
data GebAtom : Type where
  GANat : GebAtom
  GAList : GebAtom

export
gaEncode : GebAtom -> Nat
gaEncode GANat = 0
gaEncode GAList = 1

export
gaDecode : Nat -> Maybe GebAtom
gaDecode 0 = Just GANat
gaDecode 1 = Just GAList
gaDecode _ = Nothing

export
gaDecodeEncodeIsJust : (a : GebAtom) -> gaDecode (gaEncode a) = Just a
gaDecodeEncodeIsJust GANat = Refl
gaDecodeEncodeIsJust GAList = Refl

export
gaToString : GebAtom -> String
gaToString GANat = "Nat"
gaToString GAList = "List"

export
Show GebAtom where
  show a = gaToString a

export
gaEq : GebAtom -> GebAtom -> Bool
gaEq a a' = gaEncode a == gaEncode a'

export
Eq GebAtom where
  (==) = gaEq

export
Ord GebAtom where
  a < a' = gaEncode a < gaEncode a'

export
gaDecEq : (a, a' : GebAtom) -> Dec (a = a')
gaDecEq = encodingDecEq gaEncode gaDecode gaDecodeEncodeIsJust decEq

export
DecEq GebAtom where
  decEq = gaDecEq
