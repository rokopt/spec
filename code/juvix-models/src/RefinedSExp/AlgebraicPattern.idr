module RefinedSExp.AlgebraicPattern

import public Data.Nat
import public RefinedSExp.RefinedSExp
import public Library.List

%default total

mutual
  prefix 11 |->
  public export
  data ConstructorParam : (primitive : Type) -> Type where
    (|->) : DataType primitive -> ConstructorParam primitive

  prefix 11 |-
  public export
  data TypeConstructor : (primitive : Type) -> Type where
    (|-) : {primitive : Type} -> List (ConstructorParam primitive) ->
      TypeConstructor primitive

  prefix 11 |-#
  public export
  (|-#) : {primitive : Type} -> TypeConstructor primitive -> Nat
  (|-#) = length . typeParams

  prefix 11 |*
  public export
  data ADT : (primitive : Type) -> Type where
    (|*) : {primitive : Type} -> List (TypeConstructor primitive) ->
      ADT primitive

  prefix 11 |*#
  public export
  (|*#) : {primitive : Type} -> ADT primitive -> Nat
  (|*#) = length . constructors

  prefix 11 |.
  prefix 11 |:
  public export
  data DataType : (primitive : Type) -> Type where
    (|.) : primitive -> DataType primitive
    (|:) : ADT primitive -> DataType primitive

  prefix 11 |:*
  public export
  (|:*) : {primitive : Type} -> List (TypeConstructor primitive) ->
    DataType primitive
  (|:*) = (|:) . (|*)

  public export
  typeParams : {primitive : Type} -> TypeConstructor primitive ->
    List (ConstructorParam primitive)
  typeParams (|- l) = l

  infixr 7 |-<
  public export
  (|-<) : {primitive : Type} -> (tc : TypeConstructor primitive) -> (n : Nat) ->
    {auto ok : InBounds n (typeParams tc)} -> ConstructorParam primitive
  tc |-< n = index n (typeParams tc)

  public export
  constructors : {primitive : Type} -> (adt : ADT primitive) ->
    List (TypeConstructor primitive)
  constructors (|* l) = l

  infixr 7 |*<
  public export
  (|*<) : {primitive : Type} -> (adt : ADT primitive) -> (n : Nat) ->
    {auto ok : InBounds n (constructors adt)} -> TypeConstructor primitive
  adt |*< n = index n (constructors adt)

prefix 11 |**
public export
data TypeFamily : (primitive : Type) -> Type where
  (|**) : {primitive : Type} -> List (ADT primitive) -> TypeFamily primitive

public export
familyTypes : {primitive : Type} -> (family : TypeFamily primitive) ->
  List (ADT primitive)
familyTypes (|** l) = l

prefix 11 |**#
public export
(|**#) : {primitive : Type} -> TypeFamily primitive -> Nat
(|**#) = length . familyTypes

infixr 7 |**<
public export
(|**<) : {primitive : Type} -> (family : TypeFamily primitive) -> (n : Nat) ->
  {auto ok : InBounds n (familyTypes family)} -> ADT primitive
family |**< n = index n (familyTypes family)

mutual
  -- Atoms of matchable S-expressions.
  data MAtom : {primType : Type} -> (primExp : primType -> Type) -> Type where
    MPrim : {primType : Type} -> {primExp : primType -> Type} ->
      {type : primType} -> primExp type -> MAtom primExp
    MAbst : {primType : Type} -> {primExp : primType -> Type} ->
      (adt : ADT primType) -> (constructorIndex : Nat) -> MAtom primExp

  data MatchesType : {primType : Type} -> {primExp : primType -> Type} ->
      DataType primType -> SExp (MAtom primExp) -> Type where
    MatchesPrimType : {primType : Type} -> {primExp : primType -> Type} ->
      {type : primType} ->
      (p : primExp type) -> MatchesType (|. type) ($^ (MPrim {type} {primExp} p))
    MatchesAbstractType : {primType : Type} -> {primExp : primType -> Type} ->
      (adt : ADT primType) -> (constructorIndex : Nat) ->
      (constructorParams : SList (MAtom primExp)) ->
      {auto ok : InBounds constructorIndex (constructors adt)} ->
      MatchesParams
        adt (typeParams (adt |*< constructorIndex)) constructorParams ->
      MatchesType (|: adt) (MAbst adt constructorIndex $: constructorParams)

  data MatchesParams : {primType : Type} -> {primExp : primType -> Type} ->
      ADT primType -> List (ConstructorParam primType) ->
      SList (MAtom primExp) -> Type where
    MatchesParamsEmpty : {primType : Type} -> {primExp : primType -> Type} ->
      {adt : ADT primType} ->
      MatchesParams {primType} {primExp} adt [] ($|)
    MatchesParamsCons : {primType : Type} -> {primExp : primType -> Type} ->
      {adt : ADT primType} ->
      {param : ConstructorParam primType} ->
      {params : List (ConstructorParam primType)} ->
      {x : SExp (MAtom primExp)} -> {l : SList (MAtom primExp)} ->
      MatchesParam adt param x ->
      MatchesParams adt params l ->
      MatchesParams {primType} {primExp} adt (param :: params) (x $+ l)

  data MatchesParam : {primType : Type} -> {primExp : primType -> Type} ->
      ADT primType -> ConstructorParam primType ->
      SExp (MAtom primExp) -> Type where
    MatchesDataType : {primType : Type} -> {primExp : primType -> Type} ->
      {adt : ADT primType} ->
      {type : DataType primType} -> {x : SExp (MAtom primExp)} ->
      MatchesType type x -> MatchesParam adt (|-> type) x
