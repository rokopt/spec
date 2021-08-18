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
  data Datatype : (penv : PrimitiveEnv) -> Type where
    Primitive : PrimType penv -> Datatype penv
    Record : RecordType penv -> Datatype penv
    Constructors : List (RecordType penv) -> Datatype penv

  public export
  data RecordType : (penv : PrimitiveEnv) -> Type where
    Fields : List (Datatype penv) -> RecordType penv

mutual
  public export
  compileDatatype : {penv : PrimitiveEnv} ->
    Datatype penv -> AlgebraicType penv
  compileDatatype = ?compileDatatype_hole

  public export
  compileDatatypeList : {penv : PrimitiveEnv} ->
    List (Datatype penv) -> List (AlgebraicType penv)
  compileDatatypeList = ?compileDatatypeList_hole

  public export
  compileRecordType : {penv : PrimitiveEnv} ->
    RecordType penv -> AlgebraicType penv
  compileRecordType (Fields types) =
    AlgebraicProduct (compileDatatypeList types)

  public export
  compileRecordTypeList : {penv : PrimitiveEnv} ->
    List (RecordType penv) -> List (AlgebraicType penv)
  compileRecordTypeList [] = []
  compileRecordTypeList (type :: types) =
    compileRecordType type :: compileRecordTypeList types

public export
interpretDatatype : {penv : PrimitiveEnv} -> Datatype penv -> Type
interpretDatatype = interpretAlgebraicType . compileDatatype
