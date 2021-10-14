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

  -- | The universal product type in the substitution category.
  CASProduct : ComputableAtom

  -- | Product introduction in the substitution category.
  CASProductIntro : ComputableAtom

  -- | Product elimination in the substitution category.
  CASProductElimLeft : ComputableAtom
  CASProductElimRight : ComputableAtom

  -- | A term of the type interpretation of a product object.
  CASPair : ComputableAtom

public export
computableAtomToString : ComputableAtom -> String
computableAtomToString CASVoid = "SVoid"
computableAtomToString CASFromVoid = "SFromVoid"
computableAtomToString CASUnit = "SUnit"
computableAtomToString CASToUnit = "SToUnit"
computableAtomToString CASUnitTerm = "SUnitTerm"
computableAtomToString CASProduct = "SProduct"
computableAtomToString CASProductIntro = "SProductIntro"
computableAtomToString CASProductElimLeft = "SProductElimLeft"
computableAtomToString CASProductElimRight = "SProductElimRight"
computableAtomToString CASPair = "SPair"

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
caEncode CASProduct = 5
caEncode CASProductIntro = 6
caEncode CASProductElimLeft = 7
caEncode CASProductElimRight = 8
caEncode CASPair = 9

public export
caDecode : Nat -> ComputableAtom
caDecode 0 = CASVoid
caDecode 1 = CASFromVoid
caDecode 2 = CASUnit
caDecode 3 = CASToUnit
caDecode 4 = CASUnitTerm
caDecode 5 = CASProduct
caDecode 6 = CASProductIntro
caDecode 7 = CASProductElimLeft
caDecode 8 = CASProductElimRight
caDecode 9 = CASPair
caDecode _ = CASVoid

export
caDecodeIsLeftInverse :
  IsLeftInverseOf ComputableFunctions.caEncode ComputableFunctions.caDecode
caDecodeIsLeftInverse CASVoid = Refl
caDecodeIsLeftInverse CASFromVoid = Refl
caDecodeIsLeftInverse CASUnit = Refl
caDecodeIsLeftInverse CASToUnit = Refl
caDecodeIsLeftInverse CASUnitTerm = Refl
caDecodeIsLeftInverse CASProduct = Refl
caDecodeIsLeftInverse CASProductIntro = Refl
caDecodeIsLeftInverse CASProductElimLeft = Refl
caDecodeIsLeftInverse CASProductElimRight = Refl
caDecodeIsLeftInverse CASPair = Refl

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
    SProduct : {leftRep, rightRep : ComputableExp} ->
      SubstitutionType leftRep -> SubstitutionType rightRep ->
      SubstitutionType (CASProduct $* [leftRep, rightRep])

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
    SProductIntro :
      {domainRep, codomainLeftRep, codomainRightRep,
        leftMorphismRep, rightMorphismRep : ComputableExp} ->
      {domain : SubstitutionType domainRep} ->
      {codomainLeft : SubstitutionType codomainLeftRep} ->
      {codomainRight : SubstitutionType codomainRightRep} ->
      SubstitutionMorphism leftMorphismRep domain codomainLeft ->
      SubstitutionMorphism rightMorphismRep domain codomainRight ->
      SubstitutionMorphism
        (CASProductIntro $* [leftMorphismRep, rightMorphismRep])
        domain (SProduct codomainLeft codomainRight)

public export
data SubstitutionTerm : (representation : ComputableExp) ->
  {typeRep : ComputableExp} -> SubstitutionType typeRep -> Type where
    SUnitTerm : SubstitutionTerm ($^ CASUnitTerm) SUnit
    SPair :
      {leftTypeRep, rightTypeRep, leftTermRep, rightTermRep : ComputableExp} ->
      {leftType : SubstitutionType leftTypeRep} ->
      {rightType : SubstitutionType rightTypeRep} ->
      SubstitutionTerm leftTermRep leftType ->
      SubstitutionTerm rightTermRep rightType ->
      SubstitutionTerm (CASPair $* [leftTermRep, rightTermRep])
        (SProduct leftType rightType)

public export
checkSubstitutionType : (representation : ComputableExp) ->
  Maybe (SubstitutionType representation)
checkSubstitutionType (CASVoid $* []) = Just SVoid
checkSubstitutionType (CASUnit $* []) = Just SUnit
checkSubstitutionType (CASProduct $* [leftRep, rightRep]) =
  case (checkSubstitutionType leftRep, checkSubstitutionType rightRep) of
    (Just leftType, Just rightType) => Just (SProduct leftType rightType)
    _ => Nothing
checkSubstitutionType _ = Nothing

public export
checkSubstitutionTypeComplete : {representation : ComputableExp} ->
  (type : SubstitutionType representation) ->
  checkSubstitutionType representation = Just type
checkSubstitutionTypeComplete SVoid = Refl
checkSubstitutionTypeComplete SUnit = Refl
checkSubstitutionTypeComplete (SProduct leftType rightType) =
  rewrite (checkSubstitutionTypeComplete leftType) in
  rewrite (checkSubstitutionTypeComplete rightType) in
  Refl

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
checkSubstitutionMorphismComplete (SProductIntro leftMorphism rightMorphism) =
  ?checkSubstitutionMorphismComplete_hole

public export
checkSubstitutionTerm : (representation : ComputableExp) ->
  {typeRep : ComputableExp} -> (type : SubstitutionType typeRep) ->
  Maybe (SubstitutionTerm representation type)
checkSubstitutionTerm (CASUnitTerm $* []) SUnit = Just SUnitTerm
checkSubstitutionTerm (CASPair $* [leftTermRep, rightTermRep])
  (SProduct leftType rightType) = ?checkSubstitutionTerm_hole
checkSubstitutionTerm _ _ = Nothing

public export
checkSubstitutionTermComplete : {representation, typeRep : ComputableExp} ->
  (term : SubstitutionTerm representation type) ->
  checkSubstitutionTerm representation type = Just term
checkSubstitutionTermComplete SUnitTerm = Refl
checkSubstitutionTermComplete (SPair leftTerm rightTerm) =
  ?checkSubstitutionTermComplete_hole

----------------------------------------------------------------------
---- The interpretation into Idris-2 of the substitutive category ----
----------------------------------------------------------------------
public export
interpretSubstitutionType : {representation : ComputableExp} ->
  SubstitutionType representation -> Type
interpretSubstitutionType SVoid = Void
interpretSubstitutionType SUnit = ()
interpretSubstitutionType (SProduct left right) =
  (interpretSubstitutionType left, interpretSubstitutionType right)

public export
interpretSubstitutionMorphism :
  {representation, domainRep, codomainRep : ComputableExp} ->
  {domain : SubstitutionType domainRep} ->
  {codomain : SubstitutionType codomainRep} ->
  SubstitutionMorphism representation domain codomain ->
  interpretSubstitutionType domain -> interpretSubstitutionType codomain
interpretSubstitutionMorphism (SFromVoid codomain) v = void v
interpretSubstitutionMorphism (SToUnit domain) _ = ()
interpretSubstitutionMorphism
  (SProductIntro leftMorphism rightMorphism) domainTerm =
    (interpretSubstitutionMorphism leftMorphism domainTerm,
     interpretSubstitutionMorphism rightMorphism domainTerm)

public export
interpretSubstitutionTerm :
  {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  SubstitutionTerm representation type ->
  interpretSubstitutionType type
interpretSubstitutionTerm SUnitTerm = ()
interpretSubstitutionTerm (SPair leftTerm rightTerm) =
  (interpretSubstitutionTerm leftTerm, interpretSubstitutionTerm rightTerm)

-----------------------------------------------------
---- Term reduction in the substitutive category ----
-----------------------------------------------------
public export
bigStepSubstitution : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  SubstitutionTerm representation type ->
  SubstitutionTerm representation type
bigStepSubstitution SUnitTerm = SUnitTerm
bigStepSubstitution (SPair leftTerm rightTerm) =
  SPair (bigStepSubstitution leftTerm) (bigStepSubstitution rightTerm)

public export
bigStepSubstitutionCorrect : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (term : SubstitutionTerm representation type) ->
  interpretSubstitutionTerm (bigStepSubstitution term) =
    interpretSubstitutionTerm term
bigStepSubstitutionCorrect SUnitTerm = Refl
bigStepSubstitutionCorrect (SPair leftTerm rightTerm) =
  rewrite bigStepSubstitutionCorrect leftTerm in
  rewrite bigStepSubstitutionCorrect rightTerm in
  Refl

public export
bigStepSubstitutionIdempotent : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (term : SubstitutionTerm representation type) ->
  bigStepSubstitution (bigStepSubstitution term) = bigStepSubstitution term
bigStepSubstitutionIdempotent SUnitTerm = Refl
bigStepSubstitutionIdempotent (SPair leftTerm rightTerm) =
  rewrite bigStepSubstitutionIdempotent leftTerm in
  rewrite bigStepSubstitutionIdempotent rightTerm in
  Refl

public export
smallStepSubstitution : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  SubstitutionTerm representation type ->
  Maybe (SubstitutionTerm representation type)
smallStepSubstitution SUnitTerm = Nothing
smallStepSubstitution (SPair leftTerm rightTerm) = ?smallStepSubstitution_hole

public export
smallStepSubstitutionCorrect : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (original, reduced : SubstitutionTerm representation type) ->
  smallStepSubstitution original = Just reduced ->
  interpretSubstitutionTerm original = interpretSubstitutionTerm reduced
smallStepSubstitutionCorrect SUnitTerm SUnitTerm Refl impossible
smallStepSubstitutionCorrect SUnitTerm (SPair _ _) Refl impossible
smallStepSubstitutionCorrect (SPair _ _) SUnitTerm Refl impossible
smallStepSubstitutionCorrect
  (SPair leftTerm rightTerm) (SPair leftTerm' rightTerm') just =
    ?smallStepSubstitutionCorrect_hole

public export
bigStepSubstitutionComplete : {representation, typeRep : ComputableExp} ->
  {type : SubstitutionType typeRep} ->
  (term : SubstitutionTerm representation type) ->
  smallStepSubstitution (bigStepSubstitution term) = Nothing
bigStepSubstitutionComplete SUnitTerm = Refl
bigStepSubstitutionComplete (SPair leftTerm rightTerm) =
  ?bigStepSubstitutionComplete_hole
