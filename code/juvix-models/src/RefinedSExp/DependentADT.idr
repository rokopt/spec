module RefinedSExp.DependentADT

import RefinedSExp.RefinedSExp

%default total

prefix 11 $$
data WithKeywords : Type -> Type where
  ($$) : {symbol : Type} -> symbol -> WithKeywords symbol
  WKADT : {symbol : Type} -> WithKeywords symbol
  WKFunc : {symbol : Type} -> WithKeywords symbol
