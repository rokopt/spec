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

  -- | The unique morphism from the initial object.
  CASFromVoid : ComputableAtom

public export
computableAtomToString : ComputableAtom -> String
computableAtomToString CASVoid = "SVoid"
computableAtomToString CASFromVoid = "SFromVoid"

public export
Show ComputableAtom where
  show a = ":" ++ computableAtomToString a

public export
caEncode : ComputableAtom -> Nat
caEncode CASVoid = 0
caEncode CASFromVoid = 1

public export
caDecode : Nat -> ComputableAtom
caDecode 0 = CASVoid
caDecode 1 = CASFromVoid
caDecode _ = CASVoid

export
caDecodeIsLeftInverse :
  IsLeftInverseOf ComputableFunctions.caEncode ComputableFunctions.caDecode
caDecodeIsLeftInverse CASVoid = Refl
caDecodeIsLeftInverse CASFromVoid = Refl

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

public export
data SubstitutionMorphism : (representation : ComputableExp) ->
  {domainRep, codomainRep : ComputableExp} ->
  (domain : SubstitutionType domainRep) ->
  (codomain : SubstitutionType codomainRep) ->
  Type where
    SFromVoid : {codomainRep : ComputableExp} ->
      (codomain : SubstitutionType codomainRep) ->
      SubstitutionMorphism (CASFromVoid $* [codomainRep]) SVoid codomain

public export
data SubstitutionTerm : (representation : ComputableExp) ->
  {typeRep : ComputableExp} -> SubstitutionType typeRep -> Type where

public export
checkSubstitutionType : (representation : ComputableExp) ->
  Maybe (SubstitutionType representation)
checkSubstitutionType (CASVoid $* []) = Just SVoid
checkSubstitutionType _ = Nothing

public export
checkSubstitutionTypeComplete : {representation : ComputableExp} ->
  (type : SubstitutionType representation) ->
  checkSubstitutionType representation = Just type
checkSubstitutionTypeComplete SVoid = Refl

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

public export
checkSubstitutionTerm : (representation : ComputableExp) ->
  {typeRep : ComputableExp} -> (type : SubstitutionType typeRep) ->
  Maybe (SubstitutionTerm representation type)
checkSubstitutionTerm _ _ = Nothing

public export
checkSubstitutionTermComplete : {representation, typeRep : ComputableExp} ->
  (term : SubstitutionTerm representation type) ->
  checkSubstitutionTerm representation type = Just term
checkSubstitutionTermComplete _ impossible

----------------------------------------------------------------------
---- The interpretation into Idris-2 of the substitutive category ----
----------------------------------------------------------------------
public export
interpretSubstitutionType : {representation : ComputableExp} ->
  SubstitutionType representation -> Type
interpretSubstitutionType SVoid = Void

public export
interpretSubstitutionMorphism :
  {representation, domainRep, codomainRep : ComputableExp} ->
  {domain : SubstitutionType domainRep} ->
  {codomain : SubstitutionType codomainRep} ->
  SubstitutionMorphism representation domain codomain ->
  interpretSubstitutionType domain -> interpretSubstitutionType codomain
interpretSubstitutionMorphism (SFromVoid codomain) v = void v

public export
interpretSubstitutionTerm :
  {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  SubstitutionTerm representation type ->
  interpretSubstitutionType type
interpretSubstitutionTerm _ impossible

-----------------------------------------------------
---- Term reduction in the substitutive category ----
-----------------------------------------------------
public export
smallStepSubstitution : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  SubstitutionTerm representation type ->
  SubstitutionTerm representation type
smallStepSubstitution _ impossible

public export
smallStepSubstitutionCorrect : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (term : SubstitutionTerm representation type) ->
  interpretSubstitutionTerm (smallStepSubstitution term) =
    interpretSubstitutionTerm term
smallStepSubstitutionCorrect _ impossible

public export
bigStepSubstitution : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  SubstitutionTerm representation type ->
  SubstitutionTerm representation type
bigStepSubstitution _ impossible

public export
bigStepSubstitutionCorrect : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (term : SubstitutionTerm representation type) ->
  interpretSubstitutionTerm (bigStepSubstitution term) =
    interpretSubstitutionTerm term
bigStepSubstitutionCorrect _ impossible

public export
bigStepSubstitutionComplete : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (term : SubstitutionTerm representation type) ->
  smallStepSubstitution (bigStepSubstitution term) = bigStepSubstitution term
bigStepSubstitutionComplete _ impossible

public export
bigStepSubstitutionIdempotent : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (term : SubstitutionTerm representation type) ->
  bigStepSubstitution (bigStepSubstitution term) = bigStepSubstitution term
bigStepSubstitutionIdempotent _ impossible
