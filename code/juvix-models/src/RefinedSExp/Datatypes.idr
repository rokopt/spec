module RefinedSExp.Datatypes

import Library.FunctionsAndRelations
import Library.Decidability
import Category.Category
import Control.WellFounded
import RefinedSExp.List
import RefinedSExp.SExp

%default total

-- The inductive-datatype system is parameterized on primitive types provided
-- by the type theory in which it is embedded.
public export
record PrimitiveEnv where
  constructor PrimArgs
  PrimType : Type
  PrimExp : PrimType -> Type

-- Standard algebraic data types, with the primitive types added as
-- generators.  We will compile record types and inductive types to
-- these to show that record types and inductive types do not extend
-- the underlying theory (which is that of standard algebraic data types).
public export
data AlgebraicType : (penv : PrimitiveEnv) -> Type where
  AlgebraicTypeGenerator : PrimType penv -> AlgebraicType penv
  AlgebraicVoid : AlgebraicType penv
  AlgebraicUnit : AlgebraicType penv
  AlgebraicProduct : List (AlgebraicType penv) -> AlgebraicType penv
  AlgebraicCoproduct : List (AlgebraicType penv) -> AlgebraicType penv
  AlgebraicExponential :
    (domain, codomain : AlgebraicType penv) -> AlgebraicType penv

public export
typeProduct : List Type -> Type
typeProduct = foldr Pair ()

public export
typeCoproduct : List Type -> Type
typeCoproduct = foldr Either Void

mutual
  -- Compile an algebraic data type to a metalanguage (Idris) type.
  public export
  compileAlgebraicType : {penv : PrimitiveEnv} -> AlgebraicType penv -> Type
  compileAlgebraicType (AlgebraicTypeGenerator primType) = PrimExp penv primType
  compileAlgebraicType AlgebraicVoid = Void
  compileAlgebraicType AlgebraicUnit = ()
  compileAlgebraicType (AlgebraicProduct types) =
    typeProduct (compileAlgebraicTypeList types)
  compileAlgebraicType (AlgebraicCoproduct types) =
    typeCoproduct (compileAlgebraicTypeList types)
  compileAlgebraicType (AlgebraicExponential domain codomain) =
    compileAlgebraicType domain -> compileAlgebraicType codomain

  public export
  compileAlgebraicTypeList :
    {penv : PrimitiveEnv} -> List (AlgebraicType penv) -> List Type
  compileAlgebraicTypeList [] = []
  compileAlgebraicTypeList (type :: types) =
    compileAlgebraicType type :: compileAlgebraicTypeList types

mutual
  public export
  data GeneralType : (penv : PrimitiveEnv) -> Type where
    GeneralAlgebraic : AlgebraicType penv -> GeneralType penv
    GeneralRecord : RecordType penv -> GeneralType penv
    GeneralInductive : InductiveType penv -> GeneralType penv

  public export
  data RecordType : (penv : PrimitiveEnv) -> Type where
    Fields : List (GeneralType penv) -> RecordType penv

  public export
  data InductiveType : (penv : PrimitiveEnv) -> Type where
    Constructors : List (RecordType penv) -> InductiveType penv

mutual
  public export
  compileGeneralType : {penv : PrimitiveEnv} ->
    GeneralType penv -> AlgebraicType penv
  compileGeneralType (GeneralAlgebraic type) = type
  compileGeneralType (GeneralRecord type) = compileRecordType type
  compileGeneralType (GeneralInductive type) = compileInductiveType type

  public export
  compileGeneralTypeList : {penv : PrimitiveEnv} ->
    List (GeneralType penv) -> List (AlgebraicType penv)
  compileGeneralTypeList [] = []
  compileGeneralTypeList (type :: types) =
    compileGeneralType type :: compileGeneralTypeList types

  public export
  compileRecordType : {penv : PrimitiveEnv} ->
    RecordType penv -> AlgebraicType penv
  compileRecordType (Fields types) =
    AlgebraicProduct (compileGeneralTypeList types)

  public export
  compileRecordTypeList : {penv : PrimitiveEnv} ->
    List (RecordType penv) -> List (AlgebraicType penv)
  compileRecordTypeList [] = []
  compileRecordTypeList (type :: types) =
    compileRecordType type :: compileRecordTypeList types

  public export
  compileInductiveType : {penv : PrimitiveEnv} ->
    InductiveType penv -> AlgebraicType penv
  compileInductiveType (Constructors types) =
    AlgebraicCoproduct (compileRecordTypeList types)

  public export
  compileInductiveTypeList : {penv : PrimitiveEnv} ->
    List (InductiveType penv) -> List (AlgebraicType penv)
  compileInductiveTypeList [] = []
  compileInductiveTypeList (type :: types) =
    compileInductiveType type :: compileInductiveTypeList types

public export
evalType : {penv : PrimitiveEnv} -> GeneralType penv -> Type
evalType = compileAlgebraicType . compileGeneralType

-- The theory is also parameterized on primitive _functions_ provided
-- by the system.  We allow the system to provide primitive functions on
-- the algebraic closure of the primitive types, so that the system
-- doesn't need to provide primitive types that would be redundant with
-- algebraic types (such as if it wants to provide a primitive (+) function
-- which takes a pair as an argument).
public export
record PrimitiveFuncEnv (penv : PrimitiveEnv) where
  constructor PrimFuncs
  PrimFuncType : (domain, codomain : AlgebraicType penv) -> Type
  PrimFunc : {domain, codomain : AlgebraicType penv} ->
    PrimFuncType domain codomain ->
    compileAlgebraicType domain -> compileAlgebraicType codomain

public export
data AlgebraicFunction : {penv : PrimitiveEnv} ->
  (pfenv : PrimitiveFuncEnv env) -> (domain, codomain : AlgebraicType penv) ->
  Type where
    AlgebraicCompose : {a, b, c : AlgebraicType penv} ->
      AlgebraicFunction pfenv b c ->
      AlgebraicFunction pfenv a b ->
      AlgebraicFunction pfenv a c

    AlgebraicFunctionGenerator :
      PrimFuncType pfenv domain codomain ->
      AlgebraicFunction pfenv domain codomain

    AlgebraicExFalso : AlgebraicFunction pfenv AlgebraicVoid codomain

    AlgebraicConstant : AlgebraicFunction pfenv domain AlgebraicUnit

public export
compileAlgebraicFunction : {penv : PrimitiveEnv} ->
  {pfenv : PrimitiveFuncEnv penv} -> {domain, codomain : AlgebraicType penv} ->
  AlgebraicFunction pfenv domain codomain ->
  compileAlgebraicType domain -> compileAlgebraicType codomain
compileAlgebraicFunction (AlgebraicCompose g f) =
  compileAlgebraicFunction g . compileAlgebraicFunction f
compileAlgebraicFunction (AlgebraicFunctionGenerator f) =
  PrimFunc pfenv f
compileAlgebraicFunction AlgebraicExFalso =
  \v => void v
compileAlgebraicFunction AlgebraicConstant =
  \_ => ()
