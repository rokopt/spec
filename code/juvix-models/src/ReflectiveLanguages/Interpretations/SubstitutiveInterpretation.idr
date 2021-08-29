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

public export
UnitSList : Type
UnitSList = SList ()

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
  public export
  data MatchesPattern :
    {numHoles : Nat} ->
    UnitPattern numHoles -> UnitSExp -> Type where

  public export
  data MatchesPatternList :
    {numHoles, len : Nat} ->
    UnitPatternList numHoles len -> UnitSList -> Type where

  public export
  matchesPattern :
    {numHoles : Nat} ->
    (pattern : UnitPattern numHoles) -> (x : UnitSExp) ->
    Dec (MatchesPattern pattern x)
  matchesPattern pattern x = No (\match => case match of _ impossible)

  public export
  matchesPatternList :
    {numHoles, len : Nat} ->
    (patterns : UnitPatternList numHoles len) -> (xs : UnitSList) ->
    Dec (MatchesPatternList patterns xs)
  matchesPatternList patterns xs = No (\match => case match of _ impossible)

public export
SExpCharacteristic :
  {numHoles : Nat} -> UnitPattern numHoles -> Type
SExpCharacteristic = DPair UnitSExp . MatchesPattern

public export
SListCharacteristic :
  {numHoles, len : Nat} -> UnitPatternList numHoles len -> Type
SListCharacteristic = DPair UnitSList . MatchesPatternList

mutual
  InterpretKind : SubstitutiveKind -> Type
  InterpretKind Star = !- UnitSExp
  InterpretKind (KindArrow ks k) = InterpretKinds ks -> InterpretKind k

  InterpretKinds : List SubstitutiveKind -> Type
  InterpretKinds [] = ()
  InterpretKinds (k :: ks) = (InterpretKind k, InterpretKinds ks)

mutual
  InterpretDatatype : {kind : SubstitutiveKind} -> {numConstructors : Nat} ->
    Datatype kind numConstructors -> InterpretKind kind
  InterpretDatatype type = ?InterpretDatatype_hole

  InterpretConstructor : {kind : SubstitutiveKind} -> {numFields : Nat} ->
    (ctor : Constructor kind numFields) ->
    InterpretKind kind
  InterpretConstructor ctor = ?InterpretConstructor_hole
