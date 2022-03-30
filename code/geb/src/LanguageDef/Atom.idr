module LanguageDef.Atom

import Library.IdrisUtils

%default total

------------------------------------
---- Atoms used in `Expression` ----
------------------------------------

public export
data ExprAtom : Type where
  EANat : ExprAtom
  EAList : ExprAtom

public export
eaEncode : ExprAtom -> Nat
eaEncode EANat = 0
eaEncode EAList = 1

public export
eaDecode : Nat -> Maybe ExprAtom
eaDecode 0 = Just EANat
eaDecode 1 = Just EAList
eaDecode _ = Nothing

export
eaDecodeEncodeIsJust : (a : ExprAtom) -> eaDecode (eaEncode a) = Just a
eaDecodeEncodeIsJust EANat = Refl
eaDecodeEncodeIsJust EAList = Refl

public export
objectAtomToString : ExprAtom -> String
objectAtomToString EANat = "Nat"
objectAtomToString EAList = "List"

public export
Show ExprAtom where
  show a = ":" ++ objectAtomToString a

public export
eaEq : ExprAtom -> ExprAtom -> Bool
eaEq a a' = eaEncode a == eaEncode a'

public export
Eq ExprAtom where
  (==) = eaEq

public export
Ord ExprAtom where
  a < a' = eaEncode a < eaEncode a'

export
eaDecEq : (a, a' : ExprAtom) -> Dec (a = a')
eaDecEq = encodingDecEq eaEncode eaDecode eaDecodeEncodeIsJust decEq

public export
DecEq ExprAtom where
  decEq = eaDecEq
