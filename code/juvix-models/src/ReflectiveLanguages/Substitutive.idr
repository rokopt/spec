module ReflectiveLanguages.Substitutive

import Library.FunctionsAndRelations
import Library.Decidability
import RefinedSExp.List
import public Datatypes.DependentAlgebraicTypes
import public Data.Nat

%default total

mutual
  prefix 11 *^
  prefix 11 *|
  infixr 7 *#

  -- | An S-expression whose only atoms are de Bruijn indices.
  -- | The "C" prefix is for "Context"; de Bruijn indices are references
  -- | to variables in a context.
  -- |
  -- | An S-expression may be either an atom or a list of S-expressions.
  public export
  data CSExp : (contextSize : Nat) -> Type where
    -- | An atom, which is a de Bruijn index.
    (*^) : {contextSize : Nat} -> (index : Nat) ->
      {auto indexValid : index `LT` contextSize} -> CSExp contextSize
    -- | A list of S-expressions.
    (*|) : {contextSize : Nat} -> CSList contextSize -> CSExp contextSize

  infixr 7 *-
  infixr 7 *:
  infixr 7 *~
  -- | The list form of S-expressions whose only atoms are de Bruijn indices.
  public export
  data CSList : (contextSize : Nat) -> Type where
    -- | The empty list, which may be formed in any context.
    (*-) : {contextSize : Nat} -> CSList contextSize
    -- | A non-empty list whose tail's context does not include the head.
    -- | This is a non-dependent list.
    (*:) : {contextSize : Nat} ->
      CSExp contextSize -> CSList contextSize -> CSList contextSize
    -- | A non-empty list whose tail's context includes the head.
    -- | This is a dependent list, also known as a telescope.
    (*~) : {contextSize : Nat} ->
      CSExp contextSize -> CSList (S contextSize) -> CSList contextSize

mutual
  -- | Introduce unused variables into the context of an S-expression.
  public export
  csIntro : {newVars, origContextSize : Nat} ->
    CSExp origContextSize -> CSExp (newVars + origContextSize)
  csIntro ((*^) index {indexValid}) =
    (*^) index {indexValid=(plusLteMonotone LTEZero indexValid)}
  csIntro (*| l) = *| (cslIntro l)

  -- | Introduce unused variables into the context of an S-list.
  public export
  cslIntro : {newVars, origContextSize : Nat} ->
    CSList origContextSize -> CSList (newVars + origContextSize)
  cslIntro (*-) = (*-)
  cslIntro (hd *: tl) = csIntro hd *: cslIntro tl
  cslIntro {newVars} {origContextSize} (hd *~ tl) =
    csIntro hd *~
    replace {p=CSList} (sym (plusSuccRightSucc newVars origContextSize))
      (cslIntro tl)

-- | Decide whether all members of a list of indices are in bounds.
isValidIndexList : (contextSize : Nat) -> List Nat -> Bool
isValidIndexList contextSize [] = True
isValidIndexList contextSize (index :: indices) =
  index < contextSize && isValidIndexList contextSize indices

-- | A proof that all members of a list of indices are in bounds.
IsValidIndexList : (contextSize : Nat) -> List Nat -> Type
IsValidIndexList contextSize indices =
  IsTrue (isValidIndexList contextSize indices)

public export
CSNPred : Nat -> Type
CSNPred contextSize = CSExp contextSize -> Bool

public export
CSPred : Type
CSPred = (contextSize : Nat) -> CSNPred contextSize

public export
CSLNPred : Nat -> Type
CSLNPred contextSize = CSList contextSize -> Bool

public export
CSLPred : Type
CSLPred = (contextSize : Nat) -> CSLNPred contextSize

{-
public export
SubstitutiveContext : Type
SubstitutiveContext = SList Void

public export
EmptyContext : SubstitutiveContext
EmptyContext = []

public export
ContextFromExp : SExp Void -> SubstitutiveContext
ContextFromExp ($^ _) impossible
ContextFromExp ($| l) = l

mutual
  prefix 11 *^
  prefix 11 *|
  infixr 7 *#

  public export
  data CSExp : (atom : Type) -> SubstitutiveContext -> Type where
    (*^) : {atom : Type} -> {context : SubstitutiveContext} ->
      atom -> CSExp atom context
    (*#) : {atom : Type} -> {context : SubstitutiveContext} ->
      (x : CSExp atom context) -> (n : Nat) ->
      {auto ok : InBounds n context} ->
      CSExp atom (ContextFromExp (index n context {ok}))
    (*|) : {atom : Type} -> {context : SubstitutiveContext} ->
      CSList atom context -> CSExp atom context

  infixr 7 *-
  infixr 7 *:
  infixr 7 *~
  public export
  data CSList : (atom : Type) -> SubstitutiveContext -> Type where
    (*-) : {atom : Type} -> {context : SubstitutiveContext} ->
      CSList atom context
    (*:) : {atom : Type} -> {context : SubstitutiveContext} ->
      CSExp atom context -> CSList atom context -> CSList atom context
    (*~) : {atom : Type} -> {context : SubstitutiveContext} ->
      CSExp atom ($| context :: context) -> CSList atom context ->
      CSList atom context

--------------------------------------
-- JUDGMENTS OF A MINIMAL METALOGIC --
--------------------------------------

-- A representation of expressions with a decidable equality which can be
-- constructed inductively by fixpoints and co-fixpoints of substitution.
-- These are specifically intended to be able to represent the judgments
-- which may be expressed in any metalogic in which Gödel's
-- incompleteness theorem can be derived.

public export
data SubstAtom : Type where
  ObjectAtom : SubstAtom
  MorphismAtom : SubstAtom

public export
SubstExp : Type
SubstExp = SExp SubstAtom

public export
SubstList : Type
SubstList = SList SubstAtom

mutual
  public export
  data SubstContext : (rep : SubstList) -> Type where
    SubstEmpty : SubstContext []
    SubstTelescope : {firstRep : SubstList} -> {secondRep : SubstExp} ->
      SubstContext firstRep -> SubstTerm firstRep secondRep ->
      SubstContext (secondRep :: firstRep)

  public export
  data SubstObject : (rep : SubstExp) -> Type where

  public export
  data SubstMorphism : (domain, codomain : SubstExp) ->
    (rep : SubstExp) -> Type where

  public export
  data ObjectInContext : (params : SubstList) -> (rep : SubstExp) -> Type where

  public export
  data MorphismInContext :
    (params : SubstList) -> (domain, codomain : SubstExp) ->
    (rep : SubstExp) -> Type where

  public export
  data SubstTerm : (params : SubstList) -> (rep : SubstExp) -> Type where
    ObjectTerm : {params : SubstList} -> {rep : SubstExp} ->
      SubstContext params -> ObjectInContext params rep ->
      SubstTerm params (ObjectAtom $^. rep)
    MorphismTerm : {params : SubstList} -> {domain, codomain, rep : SubstExp} ->
      SubstContext params -> MorphismInContext params domain codomain rep ->
      SubstTerm params (MorphismAtom $^. rep)

public export
data ConstructionAtom : Type where

public export
ConstructionExp : Type
ConstructionExp = SExp ConstructionAtom

public export
ConstructionList : Type
ConstructionList = SList ConstructionAtom

mutual
  public export
  data ConstructionObject :
    (inArities : List Nat) -> (outArity : Nat) -> Type where

  public export
  data ConstructionMorphism :
    (inArities : List Nat) -> (outArity : Nat) -> Type where
      ConstructionPair :
        (domain, codomain : ConstructionObject inArities outArity) ->
        ConstructionMorphism inArities outArity

  public export
  data Constructor :
    (inArities : List Nat) -> (outArity : Nat) -> Type where
      ConstructorObject : ConstructionObject inArities outArity ->
        Constructor inArities outArity
      ConstructorMorphism : ConstructionObject inArities outArity ->
        Constructor inArities outArity

  public export
  data ConstructionSystem : (inArities : List Nat) -> (outArity : Nat) ->
    (constructions : Nat) -> Type where
      ConstructionMorphisms :
        (inArities : List Nat) -> (outArity : Nat) -> (constructions : Nat) ->
        Vect constructions (Constructor inArities outArity) ->
        ConstructionSystem inArities outArity constructions
{-
mutual
  public export
  data ParameterList : Type where
    TEmpty : ParameterList
    TPair :
      (left : ParameterList) -> (right : Datatype) ->
      {auto domainMatch : ParameterListsEqual left (datatypeDomain right)} ->
      ParameterList

  public export
  parameterListsEqual : ParameterList -> ParameterList -> Bool
  parameterListsEqual TEmpty TEmpty = True
  parameterListsEqual TEmpty (TPair _ _) = False
  parameterListsEqual (TPair _ _) TEmpty = False
  parameterListsEqual (TPair l r) (TPair l' r') =
    parameterListsEqual l l' && datatypesEqual r r'

  public export
  ParameterListsEqual : ParameterList -> ParameterList -> Type
  ParameterListsEqual tel tel' = IsTrue (parameterListsEqual tel tel')

  public export
  data Datatype : Type where
    Coproduct : (types : List Datatype) ->
    -- XXX compose
    -- XXX fixpoint
    -- XXX co-fixpoint
    -- XXX sum-of-products
    -- XXX separate decidable types from others

  public export
  datatypesEqual : Datatype -> Datatype -> Bool
  datatypesEqual _ _ impossible

  public export
  DatatypesEqual : Datatype -> Datatype -> Type
  DatatypesEqual type type' = IsTrue (datatypesEqual type type')

  public export
  datatypeDomain : Datatype -> ParameterList
  datatypeDomain _ impossible

  public export
  data Constructor : Type where

  public export
  constructorsEqual : Constructor -> Constructor -> Bool
  constructorsEqual _ _ impossible

  public export
  ConstructorsEqual : Constructor -> Constructor -> Type
  ConstructorsEqual ctor ctor' = IsTrue (constructorsEqual ctor ctor')
  -}

{-
public export
data SubstitutiveKind : Type where
  Star : SubstitutiveKind
  KindArrow : List SubstitutiveKind -> SubstitutiveKind -> SubstitutiveKind

mutual
  ||| A type defined by a coproduct of products.
  |||
  ||| @numParams The number of parameters of the type, each of which might
  ||| be used by some other type as either a polymorphic variable (dependent
  ||| or not) or a carrier type.
  {- XXX maybe rename -}
  public export
  data Datatype :
    (kind : SubstitutiveKind) -> (numConstructors : Nat) -> Type where
      Coproduct : {kind : SubstitutiveKind} -> {numConstructors: Nat} ->
        Vect numConstructors (VarLenConstructor kind) ->
        Datatype kind numConstructors

      ||| A type produced by substitution, which may be viewed as
      ||| function application.
      Substitute :
        {domainHead, codomain : SubstitutiveKind} ->
        {domainTail : List SubstitutiveKind} ->
        {numConstructors : Nat} ->
        Datatype
          (KindArrow (domainHead :: domainTail) codomain) numConstructors ->
        VarLenDatatype domainhead ->
        Datatype (KindArrow domainTail codomain) numConstructors

      ConstElim : {codomain : SubstitutiveKind} -> {numConstructors : Nat} ->
        Datatype (KindArrow [] codomain) numConstructors ->
        Datatype codomain numConstructors

{- XXX
      PatternMatch : {kind : SubstitutiveKind} -> {numConstructors : Nat} ->
        {codomain : VarLenDatatype kind} ->
        (ctors : Vect numConstructors (VarLenConstructor kind)) ->
        {auto domainMatches : ListForAll MatchesVarLenConstructor ctors} ->
        {auto codomainMatches :
        Datatype (KindArrow )
        -}

  public export
  data Constructor :
    (kind : SubstitutiveKind) -> (numFields : Nat) -> Type where
      Product : {kind : SubstitutiveKind} -> {numFields : Nat} ->
        Vect numFields (VarLenDatatype kind) ->
        Constructor kind numFields

  public export
  data MatchesDatatype :
    {kind : SubstitutiveKind} -> {numConstructors : Nat} ->
    (pattern, candidate : Datatype kind numConstructors) ->
    Type where

  public export
  data MatchesConstructor :
    {kind : SubstitutiveKind} -> {numFields : Nat} ->
    (pattern, candidate : Constructor kind numFields) ->
    Type where

  public export
  matchesDatatype :
    {kind : SubstitutiveKind} -> {numConstructors : Nat} ->
    (pattern, candidate : Datatype kind numConstructors) ->
    Dec (MatchesDatatype pattern candidate)
  matchesDatatype pattern candidate =
    No (\match => case match of _ impossible)

  public export
  matchesConstructor :
    {kind : SubstitutiveKind} -> {numFields : Nat} ->
    (pattern, candidate : Constructor kind numFields) ->
    Dec (MatchesConstructor ctor type)
  matchesConstructor pattern candidate =
    No (\match => case match of _ impossible)

  public export
  data VarLenDatatype : SubstitutiveKind -> Type where
    DatatypeWithLength : {kind : SubstitutiveKind} -> {numConstructors : Nat} ->
      Datatype kind numConstructors -> VarLenDatatype kind

  public export
  data VarLenConstructor : SubstitutiveKind -> Type where
    ConstructorWithLength : {kind : SubstitutiveKind} -> {numFields : Nat} ->
      Constructor kind numFields -> VarLenConstructor kind
    Project : {kind : SubstitutiveKind} -> {numConstructors : Nat} ->
      Datatype kind numConstructors ->
      Fin numConstructors ->
      VarLenConstructor kind

  public export
  data MatchesVarLenDatatype :
    {kind : SubstitutiveKind} ->
    (pattern, candidate : VarLenDatatype kind) ->
    Type where

  public export
  matchesVarLenDatatype :
    {kind : SubstitutiveKind} ->
    (pattern, candidate : VarLenDatatype kind) ->
    Dec (MatchesVarLenDatatype pattern candidate)
  matchesVarLenDatatype pattern candidate =
    No (\match => case match of _ impossible)

  public export
  data MatchesVarLenConstructor :
    {kind : SubstitutiveKind} ->
    (pattern, candidate : VarLenConstructor kind) ->
    Type where

  public export
  matchesVarLenConstructor :
    {kind : SubstitutiveKind} ->
    (pattern, candidate : VarLenConstructor kind) ->
    Dec (MatchesVarLenConstructor pattern candidate)
  matchesVarLenConstructor pattern candidate =
    No (\match => case match of _ impossible)

public export
ConstructorFields : {kind : SubstitutiveKind} -> {numFields : Nat} ->
  Constructor kind numFields -> Vect numFields (VarLenDatatype kind)
ConstructorFields (Product fields) = fields
{-
    {- XXX add comment -}
    Fixpoint : {numParams : Nat} ->
      Datatype (S numParams) -> Datatype numParams

    {- XXX add comment -}
    Evaluator : Void {- XXX -} -> Datatype numParams

    {- XXX add comment -}
    Cofixpoint : {numParams : Nat} ->
      Datatype (S numParams) -> Datatype numParams

    {- XXX add comment -}
    Coevaluator : Void {- XXX -} -> Datatype numParams
    {- XXX check up on terms (initial/terminal algebras / cata/anamorphisms) -}
    {- XXX build docs to make sure I get comments right -}

  data InductiveType : (numParams : Nat) -> Type where
    -}
    -}
    -}
