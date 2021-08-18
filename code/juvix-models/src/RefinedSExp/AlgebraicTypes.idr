module RefinedSExp.AlgebraicTypes

import Library.FunctionsAndRelations

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
  interpretAlgebraicType : {penv : PrimitiveEnv} -> AlgebraicType penv -> Type
  interpretAlgebraicType (AlgebraicTypeGenerator primType) = PrimExp penv primType
  interpretAlgebraicType AlgebraicVoid = Void
  interpretAlgebraicType AlgebraicUnit = ()
  interpretAlgebraicType (AlgebraicProduct types) =
    typeProduct (interpretAlgebraicTypeList types)
  interpretAlgebraicType (AlgebraicCoproduct types) =
    typeCoproduct (interpretAlgebraicTypeList types)
  interpretAlgebraicType (AlgebraicExponential domain codomain) =
    interpretAlgebraicType domain -> interpretAlgebraicType codomain

  public export
  interpretAlgebraicTypeList :
    {penv : PrimitiveEnv} -> List (AlgebraicType penv) -> List Type
  interpretAlgebraicTypeList [] = []
  interpretAlgebraicTypeList (type :: types) =
    interpretAlgebraicType type :: interpretAlgebraicTypeList types

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
    interpretAlgebraicType domain -> interpretAlgebraicType codomain

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

public export
interpretAlgebraicFunctionType : {penv : PrimitiveEnv} ->
  (domain, codomain : AlgebraicType penv) -> Type
interpretAlgebraicFunctionType domain codomain =
  interpretAlgebraicType domain -> interpretAlgebraicType codomain

public export
interpretAlgebraicFunction : {penv : PrimitiveEnv} ->
  {pfenv : PrimitiveFuncEnv penv} -> {domain, codomain : AlgebraicType penv} ->
  AlgebraicFunction pfenv domain codomain ->
  interpretAlgebraicFunctionType domain codomain
interpretAlgebraicFunction (AlgebraicCompose g f) =
  interpretAlgebraicFunction g . interpretAlgebraicFunction f
interpretAlgebraicFunction (AlgebraicFunctionGenerator f) =
  PrimFunc pfenv f
interpretAlgebraicFunction AlgebraicExFalso =
  \v => void v
interpretAlgebraicFunction AlgebraicConstant =
  \_ => ()
