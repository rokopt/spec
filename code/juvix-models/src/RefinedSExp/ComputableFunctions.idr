module RefinedSExp.ComputableFunctions

import Library.FunctionsAndRelations
import Library.Decidability
import RefinedSExp.SExp
import Category.ComputableCategories

%default total

-------------------------
---- Representations ----
-------------------------

public export
data ComputableAtom : Type where
  -- | The initial object of the Substitution category (type system).
  CASVoid : ComputableAtom

  -- | The unique morphism from the initial object to a given object.
  CASFromVoid : ComputableAtom

  -- | The terminal object of the Substitution category.
  CASUnit : ComputableAtom

  -- | The unique morphism to the terminal object from a given object.
  CASToUnit : ComputableAtom

  -- | The unique term of the type interpretation of the terminal object.
  CASUnitTerm : ComputableAtom

public export
computableAtomToString : ComputableAtom -> String
computableAtomToString CASVoid = "SVoid"
computableAtomToString CASFromVoid = "SFromVoid"
computableAtomToString CASUnit = "SUnit"
computableAtomToString CASToUnit = "SToUnit"
computableAtomToString CASUnitTerm = "SUnitTerm"

public export
Show ComputableAtom where
  show a = ":" ++ computableAtomToString a

public export
caEncode : ComputableAtom -> Nat
caEncode CASVoid = 0
caEncode CASFromVoid = 1
caEncode CASUnit = 2
caEncode CASToUnit = 3
caEncode CASUnitTerm = 4

public export
caDecode : Nat -> ComputableAtom
caDecode 0 = CASVoid
caDecode 1 = CASFromVoid
caDecode 2 = CASUnit
caDecode 3 = CASToUnit
caDecode 4 = CASUnitTerm
caDecode _ = CASVoid

export
caDecodeIsLeftInverse :
  IsLeftInverseOf ComputableFunctions.caEncode ComputableFunctions.caDecode
caDecodeIsLeftInverse CASVoid = Refl
caDecodeIsLeftInverse CASFromVoid = Refl
caDecodeIsLeftInverse CASUnit = Refl
caDecodeIsLeftInverse CASToUnit = Refl
caDecodeIsLeftInverse CASUnitTerm = Refl

export
caEncodeIsInjective : IsInjective ComputableFunctions.caEncode
caEncodeIsInjective =
  leftInverseImpliesInjective caEncode {g=caDecode} caDecodeIsLeftInverse

public export
CAInjection : Injection ComputableAtom Nat
CAInjection = (caEncode ** caEncodeIsInjective)

public export
CACountable : Countable
CACountable = (ComputableAtom ** CAInjection)

public export
caDecEq : DecEqPred ComputableAtom
caDecEq = countableEq CACountable

public export
DecEq ComputableAtom where
  decEq = caDecEq

public export
Eq ComputableAtom using decEqToEq where
  (==) = (==)

public export
Ord ComputableAtom where
  a < a' = caEncode a < caEncode a'

public export
ComputableExp : Type
ComputableExp = SExp ComputableAtom

public export
ComputableList : Type
ComputableList = SList ComputableAtom

public export
Show ComputableExp where
  show = fst (sexpShows show)

public export
Show ComputableList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
csDecEq : DecEqPred ComputableExp
csDecEq = sexpDecEq caDecEq

public export
cslDecEq : DecEqPred ComputableList
cslDecEq = slistDecEq caDecEq

public export
DecEq ComputableExp where
  decEq = csDecEq

public export
DecEq ComputableList where
  decEq = cslDecEq

public export
Eq ComputableExp using decEqToEq where
  (==) = (==)

------------------------------------------------
---- The category of substitutive functions ----
------------------------------------------------
public export
data SubstitutionType : (representation : ComputableExp) -> Type where
    SVoid : SubstitutionType ($^ CASVoid)
    SUnit : SubstitutionType ($^ CASUnit)

public export
data SubstitutionMorphism : (representation : ComputableExp) ->
  {domainRep, codomainRep : ComputableExp} ->
  (domain : SubstitutionType domainRep) ->
  (codomain : SubstitutionType codomainRep) ->
  Type where
    SFromVoid : {codomainRep : ComputableExp} ->
      (codomain : SubstitutionType codomainRep) ->
      SubstitutionMorphism (CASFromVoid $* [codomainRep]) SVoid codomain
    SToUnit : {domainRep : ComputableExp} ->
      (domain : SubstitutionType domainRep) ->
      SubstitutionMorphism (CASToUnit $* [domainRep]) domain SUnit

public export
data SubstitutionTerm : (representation : ComputableExp) ->
  {typeRep : ComputableExp} -> SubstitutionType typeRep -> Type where
    SUnitTerm : SubstitutionTerm ($^ CASUnitTerm) SUnit

public export
checkSubstitutionType : (representation : ComputableExp) ->
  Maybe (SubstitutionType representation)
checkSubstitutionType (CASVoid $* []) = Just SVoid
checkSubstitutionType (CASUnit $* []) = Just SUnit
checkSubstitutionType _ = Nothing

public export
checkSubstitutionTypeComplete : {representation : ComputableExp} ->
  (type : SubstitutionType representation) ->
  checkSubstitutionType representation = Just type
checkSubstitutionTypeComplete SVoid = Refl
checkSubstitutionTypeComplete SUnit = Refl

public export
checkSubstitutionMorphism : (representation : ComputableExp) ->
  {domainRep, codomainRep : ComputableExp} ->
  (domain : SubstitutionType domainRep) ->
  (codomain : SubstitutionType codomainRep) ->
  Maybe (SubstitutionMorphism representation domain codomain)
checkSubstitutionMorphism
  (CASFromVoid $* [codomainRep']) {codomainRep} SVoid codomain =
    case decEq codomainRep' codomainRep of
      Yes Refl => Just (SFromVoid codomain)
      No _ => Nothing
checkSubstitutionMorphism
  (CASToUnit $* [domainRep']) {domainRep} domain SUnit =
    case decEq domainRep' domainRep of
      Yes Refl => Just (SToUnit domain)
      No _ => Nothing
checkSubstitutionMorphism _ _ _ = Nothing

public export
checkSubstitutionMorphismComplete :
  {representation, domainRep, codomainRep : ComputableExp} ->
  {domain : SubstitutionType domainRep} ->
  {codomain : SubstitutionType codomainRep} ->
  (morphism : SubstitutionMorphism representation domain codomain) ->
  checkSubstitutionMorphism representation domain codomain =
    Just morphism
checkSubstitutionMorphismComplete {codomainRep}
  (SFromVoid {codomainRep} codomain) with (decEqRefl decEq codomainRep)
    checkSubstitutionMorphismComplete {codomainRep}
      (SFromVoid {codomainRep} codomain) | eq = rewrite eq in Refl
checkSubstitutionMorphismComplete {domainRep}
  (SToUnit {domainRep} domain) with (decEqRefl decEq domainRep)
    checkSubstitutionMorphismComplete {domainRep}
      (SToUnit {domainRep} domain) | eq = rewrite eq in Refl

public export
checkSubstitutionTerm : (representation : ComputableExp) ->
  {typeRep : ComputableExp} -> (type : SubstitutionType typeRep) ->
  Maybe (SubstitutionTerm representation type)
checkSubstitutionTerm (CASUnitTerm $* []) SUnit = Just SUnitTerm
checkSubstitutionTerm _ _ = Nothing

public export
checkSubstitutionTermComplete : {representation, typeRep : ComputableExp} ->
  (term : SubstitutionTerm representation type) ->
  checkSubstitutionTerm representation type = Just term
checkSubstitutionTermComplete SUnitTerm = Refl

----------------------------------------------------------------------
---- The interpretation into Idris-2 of the substitutive category ----
----------------------------------------------------------------------
public export
interpretSubstitutionType : {representation : ComputableExp} ->
  SubstitutionType representation -> Type
interpretSubstitutionType SVoid = Void
interpretSubstitutionType SUnit = ()

public export
interpretSubstitutionMorphism :
  {representation, domainRep, codomainRep : ComputableExp} ->
  {domain : SubstitutionType domainRep} ->
  {codomain : SubstitutionType codomainRep} ->
  SubstitutionMorphism representation domain codomain ->
  interpretSubstitutionType domain -> interpretSubstitutionType codomain
interpretSubstitutionMorphism (SFromVoid codomain) v = void v
interpretSubstitutionMorphism (SToUnit domain) _ = ()

public export
interpretSubstitutionTerm :
  {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  SubstitutionTerm representation type ->
  interpretSubstitutionType type
interpretSubstitutionTerm SUnitTerm = ()

-----------------------------------------------------
---- Term reduction in the substitutive category ----
-----------------------------------------------------
public export
bigStepSubstitution : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  SubstitutionTerm representation type ->
  SubstitutionTerm representation type
bigStepSubstitution SUnitTerm = SUnitTerm

public export
bigStepSubstitutionCorrect : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (term : SubstitutionTerm representation type) ->
  interpretSubstitutionTerm (bigStepSubstitution term) =
    interpretSubstitutionTerm term
bigStepSubstitutionCorrect SUnitTerm = Refl

public export
bigStepSubstitutionIdempotent : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (term : SubstitutionTerm representation type) ->
  bigStepSubstitution (bigStepSubstitution term) = bigStepSubstitution term
bigStepSubstitutionIdempotent SUnitTerm = Refl

public export
smallStepSubstitution : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  SubstitutionTerm representation type ->
  SubstitutionTerm representation type
smallStepSubstitution SUnitTerm = SUnitTerm

public export
smallStepSubstitutionCorrect : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (term : SubstitutionTerm representation type) ->
  interpretSubstitutionTerm (smallStepSubstitution term) =
    interpretSubstitutionTerm term
smallStepSubstitutionCorrect SUnitTerm = Refl

public export
bigStepSubstitutionComplete : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (term : SubstitutionTerm representation type) ->
  smallStepSubstitution (bigStepSubstitution term) = bigStepSubstitution term
bigStepSubstitutionComplete SUnitTerm = Refl
