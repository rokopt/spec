module RefinedSExp.Datatypes

import Library.FunctionsAndRelations
import Library.Decidability
import Category.Category
import Control.WellFounded
import Library.List
import public RefinedSExp.AlgebraicTypes

%default total

mutual
  public export
  data Datatype : (penv : PrimitiveEnv) -> Type where
    Algebraic : AlgebraicType penv -> Datatype penv
    Record : RecordType penv -> Datatype penv
    Constructors : List (RecordType penv) -> Datatype penv
    FunctionType : (domain, codomain : Datatype penv) -> Datatype penv

  public export
  data RecordType : (penv : PrimitiveEnv) -> Type where
    Fields : List (Datatype penv) -> RecordType penv

public export
Primitive : {penv : PrimitiveEnv} -> PrimType penv -> Datatype penv
Primitive = Algebraic . AlgebraicTypeGenerator

mutual
  public export
  compileDatatype : {penv : PrimitiveEnv} ->
    Datatype penv -> AlgebraicType penv
  compileDatatype (Algebraic primType) = primType
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
    DatatypeFromAlgebraic :
      {penv : PrimitiveEnv} -> {pfenv : PrimitiveFuncEnv penv} ->
      {domain, codomain : Datatype penv} ->
      AlgebraicFunction pfenv
        (compileDatatype domain) (compileDatatype codomain) ->
      DatatypeFunction pfenv domain codomain

    PatternMatch :
      {penv : PrimitiveEnv} -> {pfenv : PrimitiveFuncEnv penv} ->
      {constructors : List (RecordType penv)} ->
      {codomain : Datatype penv} ->
      ListForAll (flip (AlgebraicFunction pfenv) (compileDatatype codomain))
        (compileRecordTypeList constructors) ->
      DatatypeFunction pfenv (Constructors constructors) codomain

public export
compileDatatypeFunction : {penv : PrimitiveEnv} ->
  {pfenv : PrimitiveFuncEnv penv} -> {domain, codomain : Datatype penv} ->
  DatatypeFunction pfenv domain codomain ->
  AlgebraicFunction pfenv (compileDatatype domain) (compileDatatype codomain)
compileDatatypeFunction (DatatypeFromAlgebraic f) = f
compileDatatypeFunction (PatternMatch {codomain} patterns) =
  AlgebraicFunctionCoproduct patterns

public export
DatatypeCompose : {penv : PrimitiveEnv} -> {pfenv : PrimitiveFuncEnv penv} ->
  {a, b, c : Datatype penv} ->
  DatatypeFunction pfenv b c ->
  DatatypeFunction pfenv a b ->
  DatatypeFunction pfenv a c
DatatypeCompose f g =
  DatatypeFromAlgebraic
    (AlgebraicCompose (compileDatatypeFunction f) (compileDatatypeFunction g))

public export
DatatypeFunctionGenerator : {penv : PrimitiveEnv} ->
  {pfenv : PrimitiveFuncEnv penv} -> {domain, codomain : Datatype penv} ->
  PrimFuncType pfenv (compileDatatype domain) (compileDatatype codomain) ->
  DatatypeFunction pfenv domain codomain
DatatypeFunctionGenerator = DatatypeFromAlgebraic . AlgebraicFunctionGenerator

public export
interpretDatatype : {penv : PrimitiveEnv} ->
  PrimitiveTypeInterpretation penv -> Datatype penv -> Type
interpretDatatype interpretation =
  interpretAlgebraicType interpretation . compileDatatype

public export
interpretDatatypeFunction : {penv : PrimitiveEnv} ->
  {pfenv : PrimitiveFuncEnv penv} ->
  {typeInterpretation : PrimitiveTypeInterpretation penv} ->
  (functionInterpretation :
    PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
  {domain, codomain : Datatype penv} ->
  DatatypeFunction pfenv domain codomain ->
  interpretAlgebraicFunctionType typeInterpretation
    (compileDatatype domain) (compileDatatype codomain)
interpretDatatypeFunction functionInterpretation =
  interpretAlgebraicFunction functionInterpretation . compileDatatypeFunction
