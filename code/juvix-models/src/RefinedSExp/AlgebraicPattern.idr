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
