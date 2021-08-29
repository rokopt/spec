module ReflectiveLanguages.Substitutive

import Library.FunctionsAndRelations
import Library.Decidability
import RefinedSExp.List
import Data.Vect
import Data.Fin

%default total

--------------------------------------
-- JUDGMENTS OF A MINIMAL METALOGIC --
--------------------------------------

-- A representation of expressions with a decidable equality which can be
-- constructed inductively by fixpoints and co-fixpoints of substitution.
-- These are specifically intended to be able to represent the judgments
-- which may be expressed in any metalogic in which Gödel's
-- incompleteness theorem can be derived.

public export
data SubstitutiveKind : Type where
  Star : SubstitutiveKind
  KindArrow : {numParams : Nat} ->
    (domain: Vect numParams SubstitutiveKind) ->
    (codomain : SubstitutiveKind) ->
    SubstitutiveKind

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
        {numParams : Nat} ->
        {domainTail : Vect n SubstitutiveKind} ->
        {numConstructors : Nat} ->
        Datatype
          (KindArrow (domainHead :: domainTail) codomain) numConstructors ->
        VarLenDatatype domainhead ->
        Datatype (KindArrow domainTail codomain) numConstructors

      ConstElim : {codomain : SubstitutiveKind} -> {numConstructors : Nat} ->
        Datatype (KindArrow [] codomain) numConstructors ->
        Datatype codomain numConstructors

  public export
  data Constructor :
    (kind : SubstitutiveKind) -> (numFields : Nat) -> Type where
      Product : {kind : SubstitutiveKind} -> {numFields : Nat} ->
        Vect numFields (VarLenDatatype kind) ->
        Constructor kind numFields

  public export
  data MatchesDatatype :
    {kind : SubstitutiveKind} -> {numConstructors : Nat} -> {numFields : Nat} ->
    Datatype kind numConstructors ->
    Constructor kind numFields ->
    Type where

  public export
  data MatchesConstructor :
    {kind : SubstitutiveKind} -> {numFields : Nat} -> {numConstructors : Nat} ->
    Constructor kind numFields ->
    Datatype kind numConstructors ->
    Type where

  public export
  matchesDatatype :
    {kind : SubstitutiveKind} -> {numConstructors : Nat} -> {numFields : Nat} ->
    (type : Datatype kind numConstructors) ->
    (ctor : Constructor kind numFields) ->
    Dec (MatchesDatatype type ctor)
  matchesDatatype type ctor = No (\match => case match of _ impossible)

  public export
  matchesConstructor :
    {kind : SubstitutiveKind} -> {numFields : Nat} -> {numConstructors : Nat} ->
    (ctor : Constructor kind numFields) ->
    (type : Datatype kind numConstructors) ->
    Dec (MatchesConstructor ctor type)
  matchesConstructor ctor type = No (\match => case match of _ impossible)

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
