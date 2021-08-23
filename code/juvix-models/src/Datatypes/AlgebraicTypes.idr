module Datatypes.AlgebraicTypes

import public Library.FunctionsAndRelations
import public Library.List

%default total

-- The inductive-datatype system is parameterized on primitive types provided
-- by the type theory in which it is embedded.
public export
record PrimitiveEnv where
  constructor PrimArgs
  PrimType : Type

public export
PrimitiveEnvFunctor : Type
PrimitiveEnvFunctor = PrimitiveEnv -> PrimitiveEnv

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
PrimitiveFuncEnvFunctor : PrimitiveEnvFunctor -> Type
PrimitiveFuncEnvFunctor f =
  {penv : PrimitiveEnv} -> PrimitiveFuncEnv penv -> PrimitiveFuncEnv (f penv)

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

    AlgebraicFunctionProduct :
      {domain : AlgebraicType penv} ->
      {codomains : List (AlgebraicType penv)} ->
      ListForAll (AlgebraicFunction pfenv domain) codomains ->
      AlgebraicFunction pfenv domain (AlgebraicProduct codomains)

    AlgebraicFunctionProjection :
      (domains : List (AlgebraicType penv)) ->
      (n : Nat) -> {auto ok : InBounds n domains} ->
      AlgebraicFunction pfenv
        (AlgebraicProduct domains)
        (index n domains {ok})

    AlgebraicFunctionCoproduct :
      {domains : List (AlgebraicType penv)} ->
      {codomain : AlgebraicType penv} ->
      ListForAll (\domain => AlgebraicFunction pfenv domain codomain) domains ->
      AlgebraicFunction pfenv (AlgebraicCoproduct domains) codomain

    AlgebraicFunctionInjection :
      (codomains : List (AlgebraicType penv)) ->
      (n : Nat) -> {auto ok : InBounds n codomains} ->
      AlgebraicFunction pfenv
        (index n codomains {ok})
        (AlgebraicCoproduct codomains)

    AlgebraicFunctionEval : (domain, codomain : AlgebraicType penv) ->
      AlgebraicFunction pfenv
        (AlgebraicProduct [(AlgebraicExponential domain codomain), domain])
        codomain

    AlgebraicFunctionCurry :
      {domLeft, domRight, codomain : AlgebraicType penv} ->
      AlgebraicFunction pfenv (AlgebraicProduct [domLeft, domRight]) codomain ->
      AlgebraicFunction pfenv domLeft (AlgebraicExponential domRight codomain)

-- The inputs required to interpret algebraic types as metalanguage
-- (Idris) types.
public export
record PrimitiveTypeInterpretation (penv : PrimitiveEnv) where
  constructor PrimitiveTypeInterpretations
  interpretPrimitiveType : PrimType penv -> Type

public export
TypeInterpretationFunctor : PrimitiveEnvFunctor -> Type
TypeInterpretationFunctor f = {penv : PrimitiveEnv} ->
  PrimitiveTypeInterpretation penv -> PrimitiveTypeInterpretation (f penv)

mutual
  -- Interpret an algebraic data type as a metalanguage (Idris) type.
  public export
  interpretAlgebraicType : {penv : PrimitiveEnv} ->
    (interpretation : PrimitiveTypeInterpretation penv) ->
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
    (interpretation : PrimitiveTypeInterpretation penv) ->
    List (AlgebraicType penv) -> List Type
  interpretAlgebraicTypeList interpretation [] = []
  interpretAlgebraicTypeList interpretation (type :: types) =
    interpretAlgebraicType interpretation type ::
      interpretAlgebraicTypeList interpretation types

{-
 - This environment provides all metalanguage types as primitive types.
 -}
public export
CompletePrimitiveTypeEnv : PrimitiveEnv
CompletePrimitiveTypeEnv = PrimArgs Type

public export
CompletePrimitiveTypeInterpretation :
  PrimitiveTypeInterpretation CompletePrimitiveTypeEnv
CompletePrimitiveTypeInterpretation = PrimitiveTypeInterpretations id

public export
interpretAllMetaLanguageAlgebraicTypes :
  AlgebraicType CompletePrimitiveTypeEnv -> Type
interpretAllMetaLanguageAlgebraicTypes =
  interpretAlgebraicType CompletePrimitiveTypeInterpretation

public export
interpretAlgebraicFunctionType : {penv : PrimitiveEnv} ->
  (interpretation : PrimitiveTypeInterpretation penv) ->
  (domain, codomain : AlgebraicType penv) -> Type
interpretAlgebraicFunctionType interpretation domain codomain =
  interpretAlgebraicType interpretation domain ->
  interpretAlgebraicType interpretation codomain

-- The inputs required to interpret algebraic functions as metalanguage
-- (Idris) functions.
public export
record PrimitiveFunctionInterpretation {penv : PrimitiveEnv}
  (pfenv : PrimitiveFuncEnv penv)
  (typeInterpretation : PrimitiveTypeInterpretation penv) where
    constructor PrimitiveFunctionInterpretations
    interpretPrimitiveFunction : {domain, codomain : AlgebraicType penv} ->
      PrimFuncType pfenv domain codomain ->
      interpretAlgebraicType typeInterpretation domain ->
      interpretAlgebraicType typeInterpretation codomain

public export
FunctionInterpretationFunctor : {fenv : PrimitiveEnvFunctor} ->
  {ftype : TypeInterpretationFunctor fenv} ->
  (ffenv : PrimitiveFuncEnvFunctor fenv) ->
  {penv : PrimitiveEnv} ->
  PrimitiveFuncEnv penv ->
  (itype : PrimitiveTypeInterpretation penv) ->
  Type
FunctionInterpretationFunctor {fenv} {ftype} ffenv {penv} pfenv itype =
  PrimitiveFunctionInterpretation {penv} pfenv itype ->
  PrimitiveFunctionInterpretation
    {penv=(fenv penv)} (ffenv {penv} pfenv) (ftype itype)

mutual
  public export
  interpretAlgebraicFunction : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} ->
    {typeInterpretation : PrimitiveTypeInterpretation penv} ->
    (functionInterpretation :
      PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
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
  interpretAlgebraicFunction interpretation (AlgebraicFunctionProduct fs) =
    interpretAlgebraicFunctionProduct interpretation fs
  interpretAlgebraicFunction interpretation
    (AlgebraicFunctionProjection domains n) =
      interpretAlgebraicFunctionProjection interpretation domains n
  interpretAlgebraicFunction interpretation (AlgebraicFunctionCoproduct fs) =
    interpretAlgebraicFunctionCoproduct interpretation fs
  interpretAlgebraicFunction interpretation
    (AlgebraicFunctionInjection codomains n) =
      interpretAlgebraicFunctionInjection interpretation codomains n
  interpretAlgebraicFunction interpretation
    (AlgebraicFunctionEval domain codomain) =
      \(eval, x, ()) => eval x
  interpretAlgebraicFunction interpretation
    (AlgebraicFunctionCurry f) =
      (\x, y => interpretAlgebraicFunction interpretation f (x, y, ()))

  public export
  interpretAlgebraicFunctionProduct : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} ->
    {typeInterpretation : PrimitiveTypeInterpretation penv} ->
    (functionInterpretation :
      PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
    {domain : AlgebraicType penv} ->
    {codomains : List (AlgebraicType penv)} ->
    ListForAll (AlgebraicFunction pfenv domain) codomains ->
    interpretAlgebraicFunctionType typeInterpretation
      domain (AlgebraicProduct codomains)
  interpretAlgebraicFunctionProduct interpretation ListForAllEmpty =
    \x => ()
  interpretAlgebraicFunctionProduct interpretation (ListForAllCons f fs) =
    \x =>
      (interpretAlgebraicFunction interpretation f x,
       interpretAlgebraicFunctionProduct interpretation fs x)

  public export
  interpretAlgebraicFunctionProjection : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} ->
    {typeInterpretation : PrimitiveTypeInterpretation penv} ->
    (functionInterpretation :
      PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
    (domains : List (AlgebraicType penv)) ->
    (n : Nat) -> {auto ok : InBounds n domains} ->
    interpretAlgebraicFunctionType typeInterpretation
      (AlgebraicProduct domains) (index n domains {ok})
  interpretAlgebraicFunctionProjection interpretation [] _ impossible
  interpretAlgebraicFunctionProjection interpretation
    (d :: ds) Z {ok=InFirst} = fst
  interpretAlgebraicFunctionProjection interpretation
    (d :: ds) Z {ok=InLater _} impossible
  interpretAlgebraicFunctionProjection interpretation
    (d :: ds) (S _) {ok=InFirst} impossible
  interpretAlgebraicFunctionProjection interpretation
    (d :: ds) (S n) {ok=(InLater ok)} =
      interpretAlgebraicFunctionProjection interpretation ds n {ok} . snd

  public export
  interpretAlgebraicFunctionCoproduct : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} ->
    {typeInterpretation : PrimitiveTypeInterpretation penv} ->
    (functionInterpretation :
      PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
    {domains : List (AlgebraicType penv)} ->
    {codomain : AlgebraicType penv} ->
    ListForAll (flip (AlgebraicFunction pfenv) codomain) domains ->
    interpretAlgebraicFunctionType typeInterpretation
      (AlgebraicCoproduct domains) codomain
  interpretAlgebraicFunctionCoproduct interpretation ListForAllEmpty =
    \x => void x
  interpretAlgebraicFunctionCoproduct interpretation (ListForAllCons f fs) =
    \x => case x of
      Left x' => interpretAlgebraicFunction interpretation f x'
      Right x' => interpretAlgebraicFunctionCoproduct interpretation fs x'

  public export
  interpretAlgebraicFunctionInjection : {penv : PrimitiveEnv} ->
    {pfenv : PrimitiveFuncEnv penv} ->
    {typeInterpretation : PrimitiveTypeInterpretation penv} ->
    (functionInterpretation :
      PrimitiveFunctionInterpretation pfenv typeInterpretation) ->
    (codomains : List (AlgebraicType penv)) ->
    (n : Nat) -> {auto ok : InBounds n codomains} ->
    interpretAlgebraicFunctionType typeInterpretation
      (index n codomains {ok}) (AlgebraicCoproduct codomains)
  interpretAlgebraicFunctionInjection interpretation [] _ impossible
  interpretAlgebraicFunctionInjection interpretation
    (c :: cs) Z {ok=InFirst} = Left
  interpretAlgebraicFunctionInjection interpretation
    (c :: cs) Z {ok=InLater _} impossible
  interpretAlgebraicFunctionInjection interpretation
    (c :: cs) (S _) {ok=InFirst} impossible
  interpretAlgebraicFunctionInjection interpretation
    (c :: cs) (S n) {ok=(InLater ok)} =
      Right . interpretAlgebraicFunctionInjection interpretation cs n {ok}

-- This environment provides all metalanguage functions on the algebraic
-- closure of the primitive types.
public export
CompletePrimitiveFuncEnv : {penv : PrimitiveEnv} ->
  (typeInterpretation : PrimitiveTypeInterpretation penv) ->
  PrimitiveFuncEnv penv
CompletePrimitiveFuncEnv typeInterpretation =
  PrimFuncs (interpretAlgebraicFunctionType typeInterpretation)

public export
CompletePrimitiveFunctionInterpretation : {penv : PrimitiveEnv} ->
  (typeInterpretation : PrimitiveTypeInterpretation penv) ->
  PrimitiveFunctionInterpretation
    (CompletePrimitiveFuncEnv typeInterpretation) typeInterpretation
CompletePrimitiveFunctionInterpretation typeInterpretation =
  PrimitiveFunctionInterpretations id

public export
interpretAllMetaLanguageAlgebraicFunctions : {penv : PrimitiveEnv} ->
  (typeInterpretation : PrimitiveTypeInterpretation penv) ->
  {domain, codomain : AlgebraicType penv} ->
  AlgebraicFunction (CompletePrimitiveFuncEnv typeInterpretation)
    domain codomain ->
  interpretAlgebraicFunctionType typeInterpretation domain codomain
interpretAllMetaLanguageAlgebraicFunctions typeInterpretation f =
  interpretAlgebraicFunction
    (CompletePrimitiveFunctionInterpretation typeInterpretation) f
