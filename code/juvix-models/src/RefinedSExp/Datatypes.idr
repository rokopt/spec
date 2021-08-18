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
    FunctionType : (domain, codomain : Datatype penv) -> Datatype penv

  public export
  data RecordType : (penv : PrimitiveEnv) -> Type where
    Fields : List (Datatype penv) -> RecordType penv

mutual
  public export
  compileDatatype : {penv : PrimitiveEnv} ->
    Datatype penv -> AlgebraicType penv
  compileDatatype (Primitive primType) = AlgebraicTypeGenerator primType
  compileDatatype (Record rt) = compileRecordType rt
  compileDatatype (Constructors records) =
    AlgebraicCoproduct (compileRecordTypeList records)
  compileDatatype (FunctionType domain codomain) =
    AlgebraicExponential (compileDatatype domain) (compileDatatype codomain)

  public export
  compileDatatypeList : {penv : PrimitiveEnv} ->
    List (Datatype penv) -> List (AlgebraicType penv)
  compileDatatypeList [] = []
  compileDatatypeList (t :: ts) = compileDatatype t :: compileDatatypeList ts

  public export
  compileRecordType : {penv : PrimitiveEnv} ->
    RecordType penv -> AlgebraicType penv
  compileRecordType (Fields types) =
    AlgebraicProduct (compileDatatypeList types)

  public export
  compileRecordTypeList : {penv : PrimitiveEnv} ->
    List (RecordType penv) -> List (AlgebraicType penv)
  compileRecordTypeList [] = []
  compileRecordTypeList (t :: ts) =
    compileRecordType t :: compileRecordTypeList ts

public export
data DatatypeFunction : {penv : PrimitiveEnv} ->
  (pfenv : PrimitiveFuncEnv penv) -> (domain, codomain : Datatype penv) ->
  Type where
    DatatypeCompose : {a, b, c : Datatype penv} ->
      {pfenv : PrimitiveFuncEnv penv} -> {domain, codomain : Datatype penv} ->
      DatatypeFunction pfenv b c ->
      DatatypeFunction pfenv a b ->
      DatatypeFunction pfenv a c

    DatatypeFunctionGenerator :
      {pfenv : PrimitiveFuncEnv penv} -> {domain, codomain : Datatype penv} ->
      PrimFuncType pfenv (compileDatatype domain) (compileDatatype codomain) ->
      DatatypeFunction pfenv domain codomain

    -- PatternMatch : XXX

public export
compileDatatypeFunction : {penv : PrimitiveEnv} ->
  {pfenv : PrimitiveFuncEnv penv} -> {domain, codomain : Datatype penv} ->
  DatatypeFunction pfenv domain codomain ->
  AlgebraicFunction pfenv (compileDatatype domain) (compileDatatype codomain)
compileDatatypeFunction (DatatypeCompose g f) =
  AlgebraicCompose (compileDatatypeFunction g) (compileDatatypeFunction f)
compileDatatypeFunction (DatatypeFunctionGenerator f) =
  AlgebraicFunctionGenerator f

public export
interpretDatatype : {penv : PrimitiveEnv} ->
  AlgebraicTypeInterpretation penv -> Datatype penv -> Type
interpretDatatype interpretation =
  interpretAlgebraicType interpretation . compileDatatype

public export
interpretDatatypeFunction : {penv : PrimitiveEnv} ->
  {pfenv : PrimitiveFuncEnv penv} ->
  {typeInterpretation : AlgebraicTypeInterpretation penv} ->
  (functionInterpretation :
    AlgebraicFunctionInterpretation pfenv typeInterpretation) ->
  {domain, codomain : Datatype penv} ->
  DatatypeFunction pfenv domain codomain ->
  interpretAlgebraicFunctionType typeInterpretation
    (compileDatatype domain) (compileDatatype codomain)
interpretDatatypeFunction functionInterpretation =
  interpretAlgebraicFunction functionInterpretation . compileDatatypeFunction
