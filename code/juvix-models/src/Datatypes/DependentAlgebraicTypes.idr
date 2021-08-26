module Datatypes.DependentAlgebraicTypes

import Library.FunctionsAndRelations
import Library.TypesAndFunctions

%default total

mutual
  prefix 11 $:
  prefix 11 $::
  public export
  data SExp : (0 atom : Type) -> Type where
    ($:) : atom -> SExp atom
    ($::) : SList atom -> SExp atom

  SList : (0 atom : Type) -> Type
  SList atom = List (SExp atom)

public export
data TExp : Type where
  TNat : Nat -> TExp

public export
PartialComputable : Type
PartialComputable = TExp -> Maybe TExp
