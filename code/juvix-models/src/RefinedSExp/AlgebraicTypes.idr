module RefinedSExp.AlgebraicTypes

import Library.FunctionsAndRelations

%default total

-- The inductive-datatype system is parameterized on primitive types provided
-- by the type theory in which it is embedded.
public export
record PrimitiveEnv where
  constructor PrimArgs
  PrimType : Type

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

    {- XXX product, projections, coproduct, injections -}

-- The inputs required to interpret algebraic types as metalanguage
-- (Idris) types.
public export
record AlgebraicTypeInterpretation (penv : PrimitiveEnv) where
  constructor AlgebraicTypeInterpretations
  interpretPrimitiveType : PrimType penv -> Type

mutual
  -- Interpret an algebraic data type as a metalanguage (Idris) type.
  public export
  interpretAlgebraicType : {penv : PrimitiveEnv} ->
    (interpretation : AlgebraicTypeInterpretation penv) ->
    AlgebraicType penv -> Type
  interpretAlgebraicType interpretation (AlgebraicTypeGenerator primType) =
    interpretPrimitiveType interpretation primType
  interpretAlgebraicType interpretation AlgebraicVoid = Void
  interpretAlgebraicType interpretation AlgebraicUnit = ()
  interpretAlgebraicType interpretation (AlgebraicProduct types) =
    typeProduct (interpretAlgebraicTypeList interpretation types)
  interpretAlgebraicType interpretation (AlgebraicCoproduct types) =
    typeCoproduct (interpretAlgebraicTypeList interpretation types)
  interpretAlgebraicType interpretation (AlgebraicExponential domain codomain) =
    interpretAlgebraicType interpretation domain ->
    interpretAlgebraicType interpretation codomain

  public export
  interpretAlgebraicTypeList : {penv : PrimitiveEnv} ->
    (interpretation : AlgebraicTypeInterpretation penv) ->
    List (AlgebraicType penv) -> List Type
  interpretAlgebraicTypeList interpretation [] = []
  interpretAlgebraicTypeList interpretation (type :: types) =
    interpretAlgebraicType interpretation type ::
      interpretAlgebraicTypeList interpretation types

{-
 - This environment provides all metalanguage types as primitive types.
 - closure of the primitive types.
 -}
public export
CompletePrimitiveTypeEnv : PrimitiveEnv
CompletePrimitiveTypeEnv = PrimArgs Type

public export
CompletePrimitiveTypeInterpretation :
  AlgebraicTypeInterpretation CompletePrimitiveTypeEnv
CompletePrimitiveTypeInterpretation = AlgebraicTypeInterpretations id

public export
interpretAllMetaLanguageAlgebraicTypes :
  AlgebraicType CompletePrimitiveTypeEnv -> Type
interpretAllMetaLanguageAlgebraicTypes =
  interpretAlgebraicType CompletePrimitiveTypeInterpretation

public export
interpretAlgebraicFunctionType : {penv : PrimitiveEnv} ->
  (interpretation : AlgebraicTypeInterpretation penv) ->
  (domain, codomain : AlgebraicType penv) -> Type
interpretAlgebraicFunctionType interpretation domain codomain =
  interpretAlgebraicType interpretation domain ->
  interpretAlgebraicType interpretation codomain

-- The inputs required to interpret algebraic functions as metalanguage
-- (Idris) functions.
public export
record AlgebraicFunctionInterpretation {penv : PrimitiveEnv}
  (pfenv : PrimitiveFuncEnv penv)
  (typeInterpretation : AlgebraicTypeInterpretation penv) where
    constructor AlgebraicFunctionInterpretations
    interpretPrimitiveFunction : {domain, codomain : AlgebraicType penv} ->
      PrimFuncType pfenv domain codomain ->
      interpretAlgebraicType typeInterpretation domain ->
      interpretAlgebraicType typeInterpretation codomain

public export
interpretAlgebraicFunction : {penv : PrimitiveEnv} ->
  {pfenv : PrimitiveFuncEnv penv} ->
  {typeInterpretation : AlgebraicTypeInterpretation penv} ->
  (functionInterpretation :
    AlgebraicFunctionInterpretation pfenv typeInterpretation) ->
  {domain, codomain : AlgebraicType penv} ->
  AlgebraicFunction pfenv domain codomain ->
  interpretAlgebraicFunctionType typeInterpretation domain codomain
interpretAlgebraicFunction functionInterpretation (AlgebraicCompose g f) =
  interpretAlgebraicFunction functionInterpretation g .
    interpretAlgebraicFunction functionInterpretation f
interpretAlgebraicFunction functionInterpretation
  (AlgebraicFunctionGenerator f) =
    interpretPrimitiveFunction functionInterpretation f
interpretAlgebraicFunction _ AlgebraicExFalso =
  \v => void v
interpretAlgebraicFunction _ AlgebraicConstant =
  \_ => ()

-- This environment provides all metalanguage functions on the algebraic
-- closure of the primitive types.
public export
CompletePrimitiveFuncEnv : {penv : PrimitiveEnv} ->
  (typeInterpretation : AlgebraicTypeInterpretation penv) ->
  PrimitiveFuncEnv penv
CompletePrimitiveFuncEnv typeInterpretation =
  PrimFuncs (interpretAlgebraicFunctionType typeInterpretation)

public export
CompletePrimitiveFunctionInterpretation : {penv : PrimitiveEnv} ->
  (typeInterpretation : AlgebraicTypeInterpretation penv) ->
  AlgebraicFunctionInterpretation
    (CompletePrimitiveFuncEnv typeInterpretation) typeInterpretation
CompletePrimitiveFunctionInterpretation typeInterpretation =
  AlgebraicFunctionInterpretations id

public export
interpretAllMetaLanguageAlgebraicFunctions : {penv : PrimitiveEnv} ->
  (typeInterpretation : AlgebraicTypeInterpretation penv) ->
  {domain, codomain : AlgebraicType penv} ->
  AlgebraicFunction (CompletePrimitiveFuncEnv typeInterpretation)
    domain codomain ->
  interpretAlgebraicFunctionType typeInterpretation domain codomain
interpretAllMetaLanguageAlgebraicFunctions typeInterpretation f =
  interpretAlgebraicFunction
    (CompletePrimitiveFunctionInterpretation typeInterpretation) f
