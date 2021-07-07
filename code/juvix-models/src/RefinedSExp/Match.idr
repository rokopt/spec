module RefinedSExp.Match

import public RefinedSExp.RefinedSExp

%default total

public export
sMap : {atom, atom' : Type} -> DecEqPred atom -> (atomMap : atom -> atom') ->
  ((x : SExp atom) -> SExp atom',
   (l : SList atom) -> SList atom')
sMap decEq atomMap = ?sMap_hole
