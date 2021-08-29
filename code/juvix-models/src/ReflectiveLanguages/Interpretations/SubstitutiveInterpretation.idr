module ReflectiveLanguages.Interpretations.SubstitutiveInterpretation

import ReflectiveLanguages.Substitutive
import Library.FunctionsAndRelations
import Datatypes.DependentAlgebraicTypes
import Library.List
import Data.Vect

%default total

-- We can interpret Substitutive datatypes as the characteristic functions
-- of S-expressions with the unit atom.

public export
UnitSExp : Type
UnitSExp = SExp ()

mutual
  public export
  data UnitPattern : (numHoles : Nat) -> Type where
    MatchesNone : {numHoles : Nat} -> UnitPattern numHoles
    MatchesAll : {numHoles : Nat} -> UnitPattern numHoles
    MatchesHole : {numHoles : Nat} -> Fin numHoles -> UnitPattern numHoles
    MatchesSelected : {numHoles, len : Nat} ->
      UnitPatternList numHoles len -> Fin len -> UnitPattern numHoles
    MatchesEach : {numHoles, len : Nat} ->
      UnitPatternList numHoles len -> UnitPattern numHoles

  public export
  data UnitPatternList : (numHoles, len : Nat) -> Type where
    PatternVec : {numHoles, len : Nat} ->
      Vect len (UnitPattern numHoles) -> UnitPatternList numHoles len

mutual
  InterpretKind : SubstitutiveKind -> Type
  InterpretKind Star = Type
  InterpretKind (KindArrow ks k) = InterpretKinds ks -> InterpretKind k

  InterpretKinds : List SubstitutiveKind -> Type
  InterpretKinds [] = ()
  InterpretKinds (k :: ks) = (InterpretKind k, InterpretKinds ks)
