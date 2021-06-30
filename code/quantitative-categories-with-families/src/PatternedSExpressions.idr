module PatternedSExpressions

import Decidable.Equality
import List

%default total

data PrimitiveType : Type where
  PrimTypeBool : PrimitiveType
  PrimTypeNat : PrimitiveType
  PrimTypeString : PrimitiveType

-- Haskell can just derive this.
primTypeEq : (primType, primType' : PrimitiveType) -> Dec (primType = primType')
primTypeEq PrimTypeBool PrimTypeBool = Yes Refl
primTypeEq PrimTypeBool PrimTypeNat = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeBool PrimTypeString = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeNat PrimTypeBool = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeNat PrimTypeNat = Yes Refl
primTypeEq PrimTypeNat PrimTypeString = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeBool = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeNat = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeString = Yes Refl

interpretPrimitiveType : PrimitiveType -> Type
interpretPrimitiveType PrimTypeBool = Bool
interpretPrimitiveType PrimTypeNat = Nat
interpretPrimitiveType PrimTypeString = String

primitiveEq : (primType : PrimitiveType) ->
  (x, x' : interpretPrimitiveType primType) -> Dec (x = x')
primitiveEq PrimTypeBool = decEq
primitiveEq PrimTypeNat = decEq
primitiveEq PrimTypeString = decEq

PrimitiveExp : Type
PrimitiveExp = DPair PrimitiveType interpretPrimitiveType

primExpEq : (primExp, primExp' : PrimitiveExp) -> Dec (primExp = primExp')
primExpEq (primType ** primExp) (primType' ** primExp') with
  (primTypeEq primType primType')
    primExpEq (primType ** primExp) (primType ** primExp') | Yes Refl =
      case primitiveEq primType primExp primExp' of
        Yes Refl => Yes Refl
        No neq => No (\eq => case eq of Refl => neq Refl)
    primExpEq (primType ** primExp) (primType' ** primExp') | No neq =
      No (\eq => case eq of Refl => neq Refl)

mutual
  data SExp : Type where
    SAtom : PrimitiveExp -> SExp
    SList : SExpList -> SExp

  SExpList : Type
  SExpList = List SExp

SExpPred : Type -> Type
SExpPred codomain = SExp -> codomain

mutual
  sexpEq : (sexp, sexp' : SExp) -> Dec (sexp = sexp')
  sexpEq (SAtom exp) (SAtom exp') with (primExpEq exp exp')
    sexpEq (SAtom exp) (SAtom exp) | Yes Refl = Yes Refl
    sexpEq (SAtom exp) (SAtom exp') | No neq = No (\eq => case eq of Refl => neq Refl)
  sexpEq (SAtom _) (SList _) = No (\eq => case eq of Refl impossible)
  sexpEq (SList _) (SAtom _) = No (\eq => case eq of Refl impossible)
  sexpEq (SList sexpList) (SList sexpList') =
    case sexpListEq sexpList sexpList' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)

  sexpListEq : (sexpList, sexpList' : SExpList) -> Dec (sexpList = sexpList')
  sexpListEq = let _ = sexpListDecEq in decEq

  [sexpDecEq] DecEq SExp where
    decEq = sexpEq

  [sexpListDecEq] DecEq SExpList where
    decEq = sexpListEq

mutual
  data Pattern : Type where
    DefaultPat : Pattern
    PrimPat : PrimitiveType -> Pattern
    ProductPat : List Pattern -> Pattern
    SumPat : List Pattern -> Pattern

  PatternList : Type
  PatternList = List Pattern

mutual
  patternEq : (pattern, pattern' : Pattern) -> Dec (pattern = pattern')
  patternEq DefaultPat DefaultPat = Yes Refl
  patternEq DefaultPat (PrimPat _) = No (\eq => case eq of Refl impossible)
  patternEq DefaultPat (ProductPat _) = No (\eq => case eq of Refl impossible)
  patternEq DefaultPat (SumPat _) = No (\eq => case eq of Refl impossible)
  patternEq (PrimPat _) DefaultPat = No (\eq => case eq of Refl impossible)
  patternEq (PrimPat primType) (PrimPat primType') =
    case primTypeEq primType primType' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)
  patternEq (PrimPat _) (ProductPat _) = No (\eq => case eq of Refl impossible)
  patternEq (PrimPat _) (SumPat _) = No (\eq => case eq of Refl impossible)
  patternEq (ProductPat _) DefaultPat = No (\eq => case eq of Refl impossible)
  patternEq (ProductPat _) (PrimPat _) = No (\eq => case eq of Refl impossible)
  patternEq (ProductPat patternList) (ProductPat patternList') =
    case patternListEq patternList patternList' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)
  patternEq (ProductPat _) (SumPat _) = No (\eq => case eq of Refl impossible)
  patternEq (SumPat _) DefaultPat = No (\eq => case eq of Refl impossible)
  patternEq (SumPat _) (PrimPat _) = No (\eq => case eq of Refl impossible)
  patternEq (SumPat _) (ProductPat _) = No (\eq => case eq of Refl impossible)
  patternEq (SumPat patternList) (SumPat patternList') =
    case patternListEq patternList patternList' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)

  patternListEq :(patternList, patternList' : PatternList) ->
    Dec (patternList = patternList')
  patternListEq = let _ = patternListDecEq in decEq

  [patternDecEq] DecEq Pattern where
    decEq = patternEq

  [patternListDecEq] DecEq PatternList where
    decEq = patternListEq

mutual
  data MatchesExp : Pattern -> SExp -> Type where
    MatchesDefault : (sexp : SExp) -> MatchesExp DefaultPat sexp
    MatchesPrim : (primExp : PrimitiveExp) ->
      MatchesExp (PrimPat (fst primExp)) (SAtom primExp)
    MatchesProduct : {patternList : PatternList} -> {sexpList : SExpList} ->
      MatchesList patternList sexpList ->
      MatchesExp (ProductPat patternList) (SList sexpList)
    MatchesSum : {patternList : PatternList} -> {sexp : SExp} ->
      MatchesSome patternList sexp ->
      MatchesExp (ProductPat patternList) sexp

  MatchesList : PatternList -> SExpList -> Type
  MatchesList = ListPairForAll MatchesExp

  MatchesSome : PatternList -> SExp -> Type
  MatchesSome = flip (ListExists . (flip MatchesExp))

MatchedSExp : Pattern -> Type
MatchedSExp pattern = DPair SExp (MatchesExp pattern)

MatchedSExpPred : Type -> Pattern -> Type
MatchedSExpPred codomain pattern =
  MatchedSExp pattern -> codomain

MatchedListPred : Type -> PatternList -> Type
MatchedListPred codomain patternList =
  (ListForAll MatchedSExp patternList) -> codomain

MatchedSExpPredList : Type -> PatternList -> Type
MatchedSExpPredList codomain patternList =
  ListForAll (MatchedSExpPred codomain) patternList

mutual
  matchesExp : (pattern : Pattern) -> (sexp : SExp) ->
    Dec (MatchesExp pattern sexp)
  matchesExp pattern sexp = ?matchesExp_hole

  matchesList : (patternList : PatternList) -> (sexpList : SExpList) ->
    Dec (MatchesList patternList sexpList)
  matchesList patternList sexpList = ?matchesList_hole

  matchesSome : (patternList : PatternList) -> (sexp : SExp) ->
    Dec (MatchesSome patternList sexp)
  matchesSome patternList sexp = ?matchesSome_hole

mutual
  data IsSubPattern : (sub, super : Pattern) -> Type where
    SubDefault : (sub : Pattern) -> IsSubPattern sub DefaultPat
    SubPrimitive : (primType : PrimitiveType) ->
      IsSubPattern (PrimPat primType) (PrimPat primType)
    SubProduct : (sub, super : PatternList) ->
      IsSubPatternList sub super ->
      IsSubPattern (ProductPat sub) (ProductPat super)
    SubSum : (sub, super : PatternList) ->
      IsSubPatternList sub super ->
      IsSubPattern (SumPat sub) (SumPat super)

  data IsSubPatternList : (sub, super : PatternList) -> Type where
    SubNil : IsSubPatternList [] []
    SubCons :
      {headSub : Pattern} -> {headSuper : Pattern} ->
      {tailSub : PatternList} -> {tailSuper : PatternList} ->
      IsSubPattern headSub headSuper ->
      IsSubPatternList tailSub tailSuper ->
      IsSubPatternList (headSub :: tailSub) (headSuper :: tailSuper)

mutual
  isSubPattern :
    (sub, super : Pattern) -> Dec (IsSubPattern sub super)
  isSubPattern sub super = ?isSubPattern_hole

  isSubPatternList :
    (sub, super : PatternList) -> Dec (IsSubPatternList sub super)
  isSubPatternList sub super = ?isSubPatternList_hole

mutual
  subPatternReflexive :
    (pattern : Pattern) -> IsSubPattern pattern pattern
  subPatternReflexive = ?subPatternReflexive_hole

  subPatternListReflexive :
    (patternList : PatternList) -> IsSubPatternList patternList patternList
  subPatternListReflexive = ?subPatternListReflexive_hole

mutual
  subPatternTransitive :
    {patternA, patternB, patternC : Pattern} ->
    IsSubPattern patternA patternB ->
    IsSubPattern patternB patternC ->
    IsSubPattern patternA patternC
  subPatternTransitive subAB subBC = ?subPatternTransitive_hole

  subPatternListTransitive :
    {patternListA, patternListB, patternListC : PatternList} ->
    IsSubPatternList patternListA patternListB ->
    IsSubPatternList patternB patternC ->
    IsSubPatternList patternListA patternListC
  subPatternListTransitive subAB subBC = ?subPatternListTransitive_hole

mutual
  patternMatchTransitive :
    {sub, super : Pattern} ->
    IsSubPattern sub super ->
    {sexp : SExp} ->
    MatchesExp sub sexp ->
    MatchesExp super sexp
  patternMatchTransitive isSub matches = ?patternMatchTransitive_hole

  patternMatchProductTransitive :
    {sub, super : PatternList} ->
    IsSubPatternList sub super ->
    {sexp : SExp} ->
    MatchesExp (ProductPat sub) sexp ->
    MatchesExp (ProductPat super) sexp
  patternMatchProductTransitive isSub matches =
    ?patternMatchProductTransitive_hole

  patternMatchSumTransitive :
    {sub, super : PatternList} ->
    IsSubPatternList sub super ->
    {sexp : SExp} ->
    MatchesExp (SumPat sub) sexp ->
    MatchesExp (SumPat super) sexp
  patternMatchSumTransitive isSub matches =
    ?patternMatchSumTransitive_hole

data Consumer : (domain : Pattern) -> (codomain : Type) -> Type where
  ConsumeDefault :
    {codomain : Type} -> SExpPred codomain -> Consumer DefaultPat codomain
  ConsumePrimitive : {domain : PrimitiveType} -> {codomain : Type} ->
    (interpretPrimitiveType domain -> codomain) ->
    Consumer (PrimPat domain) codomain
  ConsumeProduct : {patternList : PatternList} -> {codomain : Type} ->
    ((ListForAll MatchedSExp patternList) -> codomain) ->
    Consumer (ProductPat patternList) codomain
  ConsumeSum : {patternList : PatternList} -> {codomain : Type} ->
    MatchedSExpPredList codomain patternList ->
    Consumer (SumPat patternList) codomain

data Producer : (domain : Type) -> (codomain : Pattern) -> Type where

data Transformer : (domain, codomain : Pattern) -> Type where

transform : {domain, codomain : Pattern} -> Transformer domain codomain ->
  MatchedSExp domain -> MatchedSExp codomain
transform transformer (sexp ** matchesDomain) = ?transform_hole
