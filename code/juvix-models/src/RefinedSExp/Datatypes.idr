module RefinedSExp.Datatypes

import Library.FunctionsAndRelations
import Library.Decidability
import Category.Category
import Control.WellFounded
import RefinedSExp.List
import RefinedSExp.SExp
import public RefinedSExp.AlgebraicTypes

%default total

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
