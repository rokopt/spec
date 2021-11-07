module Geb.Geb

import Library.FunctionsAndRelations
import Library.Decidability
import public RefinedSExp.SExp
import public Data.SortedSet
import public Data.SortedMap
import public Data.DPair
import public Geb.GebAtom

%default total

-- | Straight from _Representations of First-Order Function Types
-- | as Terminal Coalgebras_.
public export
data BTree : Type where
  BTLeaf : BTree
  BTBranch : BTree -> BTree -> BTree

public export
data BTFun : Type -> Type where
  BTCase : {output : Type} -> (leafCase : output) ->
    (branchCase : Lazy (BTFun (BTFun output))) -> BTFun output

{-
 - Not total.
public export
lamBT : {a : Type} -> (BTree -> a) -> BTFun a
lamBT f = BTCase (f BTLeaf) (lamBT (\t => lamBT (\u => f (BTBranch t u)))
-}

public export
appBT : {output : Type} -> BTFun output -> BTree -> output
appBT (BTCase leafCase _) BTLeaf = leafCase
appBT (BTCase _ f) (BTBranch left right) = appBT (appBT f left) right

-- | Also from the above paper, but for this one they only gave the
-- | math, not the code.  So here's my attempt at the code.  These
-- | strongly resemble S-expressions.
public export
data FTree : Type -> Type where
  FLeaf : {atom : Type} -> atom -> FTree atom
  FBranch : {atom : Type} -> FTree atom -> List (FTree atom) -> FTree atom

mutual
  public export
  data FTFun : Type -> Type -> Type where
    FTCase : {atom, output : Type} -> (leafCase : atom -> output) ->
      (branchCase : Lazy (FTFun atom (LFTFun atom output))) -> FTFun atom output

  public export
  data LFTFun : Type -> Type -> Type where
    LFTCase : {atom, output : Type} -> (nilCase : output) ->
      (consCase : Lazy (FTFun atom (LFTFun atom output))) -> LFTFun atom output

mutual
  public export
  appFT : {atom, output : Type} -> FTFun atom output -> FTree atom -> output
  appFT (FTCase leafCase _) (FLeaf a) = leafCase a
  appFT (FTCase _ f) (FBranch tree list) = appLFT (appFT f tree) list

  public export
  appLFT : {atom, output : Type} -> LFTFun atom output -> List (FTree atom) ->
    output
  appLFT (LFTCase nilCase _) [] = nilCase
  appLFT (LFTCase _ f) (tree :: list) = appLFT (appFT f tree) list

-- | My modifications:
-- | Done below:
-- |   - Add atoms
-- |   - Convert to S-expressions (my atom + list representation)
-- | Still to do:
-- |   - Index them by S-expressions and then write them in S-expressions
-- |     themselves so that I can use "App" and make them manifestly finitary
-- |   - Try to uncurry the type and function
-- |   - Try to make them dependent
-- |     - If that works, add the restriction to refined well-founded
-- |       S-expressions, with the dependent types available to validate
-- |     - If it fails, do refinement to well-founded trees with finite
-- |       pattern matches first, and find out whether that makes
-- |       type dependency easier
-- |   - Interpret them in Idris:
-- |     - Refined S-expressions with big-step evaluation
-- |     - Small-step evaluation for well-typed Turing machines using the
-- |       coinductive version
-- |   - Write them in themselves
-- |   - Use that reflection together with the duality to implement
-- |     algebraic effects (perhaps using models and comodels)

mutual
  public export
  data GExp : Type -> Type where
    GXIntro : {atom : Type} -> atom -> GList atom -> GExp atom

  public export
  data GList : Type -> Type where
    GNil : {atom : Type} -> GList atom
    GCons : {atom : Type} -> GExp atom -> GList atom -> GList atom

mutual
  public export
  data GXFun : (atom, output : Type) -> Type where
    GXCase : {atom, output : Type} ->
      (expCase : atom -> Lazy (GXFun atom (GLFun atom output))) ->
      GXFun atom output

  public export
  data GLFun : (atom, output : Type) -> Type where
    GLCase : {atom, output : Type} -> (nilCase : output) ->
      (consCase : Lazy (GLFun atom (GXFun atom output))) -> GLFun atom output

mutual
  public export
  appGX : {atom, output : Type} -> GXFun atom output -> GExp atom -> output
  appGX (GXCase f) (GXIntro a list) = appGL (appGX (f a) (GXIntro a list)) list

  public export
  appGL : {atom, output : Type} -> GLFun atom output -> GList atom -> output
  appGL (GLCase nilCase _) GNil = nilCase
  appGL (GLCase _ f) (GCons exp list) = appGX (appGL f list) exp

mutual
  public export
  data ZerothOrderType : Type where
    ZerothInitial : ZerothOrderType
    ZerothTerminal : ZerothOrderType
    ZerothProduct : ZerothOrderType -> ZerothOrderType -> ZerothOrderType
    ZerothCoproduct : ZerothOrderType -> ZerothOrderType -> ZerothOrderType

mutual
  public export
  data ZerothOrderTerm : Type where
    ZerothUnit : ZerothOrderTerm
    ZerothPair : ZerothOrderTerm -> ZerothOrderTerm -> ZerothOrderTerm
    ZerothLeft : ZerothOrderTerm -> ZerothOrderTerm
    ZerothRight : ZerothOrderTerm -> ZerothOrderTerm

mutual
  public export
  data MatchesType : ZerothOrderType -> ZerothOrderTerm -> Type where
    MatchesUnit : MatchesType ZerothTerminal ZerothUnit

    MatchesPair : (firstTerm, secondTerm : ZerothOrderTerm) ->
      {firstType, secondType : ZerothOrderType} ->
      {auto firstMatch : MatchesType firstType firstTerm} ->
      {auto secondMatch : MatchesType secondType secondTerm} ->
      MatchesType
        (ZerothProduct firstType secondType) (ZerothPair firstTerm secondTerm)

    MatchesLeft : (term : ZerothOrderTerm) ->
      {leftType, rightType : ZerothOrderType} ->
      {auto leftMatch : MatchesType leftType term} ->
      MatchesType (ZerothCoproduct leftType rightType) (ZerothLeft term)

    MatchesRight : (term : ZerothOrderTerm) ->
      {leftType, rightType : ZerothOrderType} ->
      {auto rightMatch : MatchesType rightType term} ->
      MatchesType (ZerothCoproduct leftType rightType) (ZerothRight term)

----------------------------------------------------------------
---- General definition of programming language / metalogic ----
----------------------------------------------------------------

public export
gebIndexList : Nat -> GebSList
gebIndexList 0 = $*^ GAIndexFirst
gebIndexList (S n) = GAIndexNext $^: gebIndexList n

public export
checkIndexListCertified : (indexList : GebSList) ->
  Maybe (n : Nat ** gebIndexList n = indexList)
checkIndexListCertified [GAIndexFirst $* []] = Just (0 ** Refl)
checkIndexListCertified ((GAIndexNext $* []) :: tail) with
  (checkIndexListCertified tail)
    checkIndexListCertified ((GAIndexNext $* []) :: tail) |
      Just (n ** consistent) =
        case consistent of Refl => Just (S n ** Refl)
    checkIndexListCertified ((GAIndexNext $* []) :: tail) | Nothing = Nothing
checkIndexListCertified _ = Nothing

public export
checkIndexList : (indexList : GebSList) -> Maybe Nat
checkIndexList indexList with (checkIndexListCertified indexList)
  checkIndexList indexList | Just (n ** _) = Just n
  checkIndexList indexList | _ = Nothing

public export
checkIndexListConsistent : {indexList : GebSList} ->
  (consistentIndex : IsJust (checkIndexList indexList)) ->
  gebIndexList (IsJustElim consistentIndex) = indexList
checkIndexListConsistent just with (checkIndexListCertified indexList) proof p
  checkIndexListConsistent ItIsJust | Just (n ** consistentIndex) =
    consistentIndex
  checkIndexListConsistent ItIsJust | Nothing impossible

mutual
  public export
  data GebPOrder : GebSExp -> Type where
    FiniteOrder : (n : Nat) ->
      GebPOrder $ GAFiniteOrder $* (gebIndexList n)
    TuringComplete : GebPOrder $ $^ GATuringComplete

  public export
  data GebPType : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
    (type : GebSExp) -> Type where
      PromoteFinite : {order : GebSExp} -> {n : Nat} -> {type : GebSExp} ->
        GebPType (FiniteOrder n) type ->
        GebPType (FiniteOrder (S n)) $ (GAPromoteFinite $*** type)
      PromoteTuringComplete : {order : GebSExp} -> {n : Nat} ->
        {type : GebSExp} -> GebPType (FiniteOrder n) type ->
        GebPType TuringComplete $ (GAPromoteTuringComplete $*** type)
      PatternType : {matrix : GebSExp} -> {order : GebSExp} ->
        {checkedOrder : GebPOrder order} ->
        GebPTypeMatrix checkedOrder matrix ->
        GebPType checkedOrder $ GAPatternType $*** matrix

  public export
  data GebPTypeList : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
    (types : GebSExp) -> Type where
      EmptyTypeList : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
        GebPTypeList checkedOrder ($^ GATypeList)
      ConsTypeList : {type : GebSExp} -> {types : GebSList} ->
        {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
        GebPType checkedOrder type ->
        GebPTypeList checkedOrder (GATypeList $* types) ->
        GebPTypeList checkedOrder $ GATypeList $* (type :: types)

  public export
  data GebPTypeMatrix : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
    (matrix : GebSExp) -> Type where
      EmptyTypeMatrix : GebPTypeMatrix checkedOrder ($^ GATypeMatrix)
      ConsTypeMatrix : {row : GebSExp} -> {matrix : GebSList} ->
        {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
        GebPTypeList checkedOrder row ->
        GebPTypeMatrix checkedOrder (GATypeMatrix $* matrix) ->
        GebPTypeMatrix checkedOrder $ GATypeMatrix $* (row :: matrix)

  public export
  data GebMatrixIndex : {matrix : GebSExp} -> {order : GebSExp} ->
    {checkedOrder : GebPOrder order} ->
    GebPTypeMatrix checkedOrder matrix -> GebSExp -> Type where
      MatrixFirst : {row : GebSExp} -> {matrix : GebSList} ->
        {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
        {checkedMatrix : GebPTypeMatrix checkedOrder $
          GATypeMatrix $* (row :: matrix)} ->
        GebMatrixIndex checkedMatrix (GAMatrixIndex $**^ GAIndexFirst)
      MatrixNext : {row : GebSExp} -> {matrix : GebSList} ->
        {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
        {checkedTypeList : GebPTypeList checkedOrder row} ->
        {checkedMatrix :
          GebPTypeMatrix checkedOrder $ GATypeMatrix $* matrix} ->
        {indexList : GebSList} ->
        GebMatrixIndex checkedMatrix (GAMatrixIndex $* indexList) ->
        GebMatrixIndex (ConsTypeMatrix checkedTypeList checkedMatrix)
          (GAMatrixIndex $* $^ GAIndexNext :: indexList)

  public export
  matrixIndexTypeListExp : {matrix : GebSExp} ->
    {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
    (checkedMatrix : GebPTypeMatrix checkedOrder matrix) -> {index : GebSExp} ->
    GebMatrixIndex checkedMatrix index ->
    GebSExp
  matrixIndexTypeListExp (ConsTypeMatrix {row} _ _) MatrixFirst = row
  matrixIndexTypeListExp (ConsTypeMatrix _ tail) (MatrixNext index) =
    matrixIndexTypeListExp tail index

  public export
  matrixIndexTypeList : {matrix : GebSExp} ->
    {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
    (checkedMatrix : GebPTypeMatrix checkedOrder matrix) -> {index : GebSExp} ->
    (checkedIndex : GebMatrixIndex checkedMatrix index) ->
    GebPTypeList
      checkedOrder (matrixIndexTypeListExp checkedMatrix checkedIndex)
  matrixIndexTypeList (ConsTypeMatrix head _) MatrixFirst = head
  matrixIndexTypeList (ConsTypeMatrix _ tail) (MatrixNext index) =
    matrixIndexTypeList tail index

  public export
  data GebPTerm : {type : GebSExp} -> {order : GebSExp} ->
    {checkedOrder : GebPOrder order} ->
    GebPType checkedOrder type -> (term : GebSExp) -> Type where
      Inject : {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
        {matrix : GebSExp} ->
        (checkedMatrix : GebPTypeMatrix checkedOrder matrix) ->
        {index : GebSExp} ->
        (checkedIndex : GebMatrixIndex checkedMatrix index) ->
        {terms : GebSExp} ->
        GebPTermList (matrixIndexTypeList checkedMatrix checkedIndex) terms ->
        GebPTerm (PatternType checkedMatrix) $ GAInjectTerm $* [index, terms]

  public export
  data GebPTermList : {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
    {types : GebSExp} ->
    GebPTypeList checkedOrder types -> (terms : GebSExp) -> Type where
      EmptyTermList : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
        GebPTermList (EmptyTypeList checkedOrder) ($^ GATermList)
      ConsTermList : {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
        {type : GebSExp} -> {checkedType : GebPType checkedOrder type} ->
        {term : GebSExp} -> GebPTerm checkedType term ->
        {types : GebSList} ->
        {checkedTypes : GebPTypeList checkedOrder (GATypeList $* types)} ->
        {terms : GebSList} ->
        GebPTermList checkedTypes (GATermList $* terms) ->
        GebPTermList (ConsTypeList checkedType checkedTypes) $
          GATermList $* (term :: terms)

mutual
  public export
  checkOrder : (order : GebSExp) -> Maybe (GebPOrder order)
  checkOrder (GAFiniteOrder $* indexList) with
    (checkIndexListCertified indexList)
      checkOrder (GAFiniteOrder $* indexList) | Just (n ** consistentIndex) =
        case consistentIndex of Refl => Just $ FiniteOrder n
      checkOrder (GAFiniteOrder $* indexList) | Nothing = Nothing
  checkOrder (GATuringComplete $* []) = Just TuringComplete
  checkOrder _ = Nothing

  public export
  checkType : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
    (type : GebSExp) -> Maybe (GebPType checkedOrder type)
  checkType checkedOrder (GAPatternType $* [GATypeMatrix $* matrix]) with
    (checkTypeMatrix checkedOrder matrix)
      checkType checkedOrder (GAPatternType $* [GATypeMatrix $* matrix]) |
        Just checkedMatrix = Just $ PatternType checkedMatrix
      checkType checkedOrder (GAPatternType $* [GATypeMatrix $* matrix]) | _ =
        Nothing
  checkType _  _= Nothing

  public export
  checkTypeList : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
    (types : GebSList) ->
    Maybe (GebPTypeList checkedOrder $ GATypeList $* types)
  checkTypeList checkedOrder [] = Just (EmptyTypeList checkedOrder)
  checkTypeList checkedOrder (type :: types) =
    case (checkType checkedOrder type, checkTypeList checkedOrder types) of
      (Just checkedType, Just checkedTypeList) =>
        Just (ConsTypeList checkedType checkedTypeList)
      _ => Nothing

  public export
  checkTypeMatrix : {order : GebSExp} -> (checkedOrder : GebPOrder order) ->
    (matrix : GebSList) ->
    Maybe $ GebPTypeMatrix checkedOrder (GATypeMatrix $* matrix)
  checkTypeMatrix checkedOrder [] = Just $ EmptyTypeMatrix {checkedOrder}
  checkTypeMatrix checkedOrder ((GATypeList $* row) :: matrix) =
    case (checkTypeList checkedOrder row,
      checkTypeMatrix checkedOrder matrix) of
        (Just checkedRow, Just checkedMatrix) =>
          Just $ ConsTypeMatrix checkedRow checkedMatrix
        _ => Nothing
  checkTypeMatrix _ _ = Nothing

  public export
  checkMatrixIndex : {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
    {matrix : GebSExp} ->
    (checkedMatrix : GebPTypeMatrix checkedOrder matrix) ->
    (index : GebSExp) -> Maybe (GebMatrixIndex checkedMatrix index)
  checkMatrixIndex
    (ConsTypeMatrix _ _) (GAMatrixIndex $* [GAIndexFirst $* []]) =
      Just MatrixFirst
  checkMatrixIndex
    (ConsTypeMatrix _ tail) (GAMatrixIndex $* (GAIndexNext $* []) :: next) =
      case checkMatrixIndex tail (GAMatrixIndex $* next) of
        Just checkedIndex => Just $ MatrixNext checkedIndex
        _ => Nothing
  checkMatrixIndex _ _ = Nothing

  public export
  checkAgainstType : {order : GebSExp} -> {checkedOrder : GebPOrder order} ->
    {type : GebSExp} -> (checkedType : GebPType checkedOrder type) ->
    (term : GebSExp) -> Maybe (GebPTerm checkedType term)
  checkAgainstType
    (PatternType checkedMatrix) (GAInjectTerm $* [index, GATermList $* terms]) =
      case checkMatrixIndex checkedMatrix index of
        Just checkedIndex =>
          case checkAgainstTypeList
            (matrixIndexTypeList checkedMatrix checkedIndex) terms of
              Just checkedTerms =>
                Just $ Inject checkedMatrix checkedIndex checkedTerms
              _ => Nothing
        _ => Nothing
  checkAgainstType _ _ = Nothing

  public export
  checkAgainstTypeList : {order : GebSExp} ->
    {checkedOrder : GebPOrder order} -> {types : GebSExp} ->
    (checkedTypes : GebPTypeList checkedOrder types) -> (terms : GebSList) ->
    Maybe $ GebPTermList checkedTypes $ GATermList $* terms
  checkAgainstTypeList (EmptyTypeList checkedOrder) [] =
    Just $ EmptyTermList checkedOrder
  checkAgainstTypeList (EmptyTypeList _) (_ :: _) = Nothing
  checkAgainstTypeList (ConsTypeList _ _) [] = Nothing
  checkAgainstTypeList (ConsTypeList type types) (term :: terms) =
    case (checkAgainstType type term, checkAgainstTypeList types terms) of
      (Just checkedTerm, Just checkedTerms) =>
        Just $ ConsTermList checkedTerm checkedTerms
      _ => Nothing

public export
checkOrderAndType : (order, type : GebSExp) ->
  Maybe (checkedOrder : GebPOrder order ** GebPType checkedOrder type)
checkOrderAndType order type =
  case checkOrder order of
    Just checkedOrder => case checkType checkedOrder type of
      Just checkedType => Just (checkedOrder ** checkedType)
      _ => Nothing
    _ => Nothing

public export
checkTerm : (order, type, term : GebSExp) ->
  Maybe (checkedOrder : GebPOrder order **
         checkedType : GebPType checkedOrder type **
         GebPTerm checkedType term)
checkTerm order type term = case checkOrderAndType order type of
  Just (checkedOrder ** checkedType) =>
    case checkAgainstType checkedType term of
      Just checkedTerm => Just (checkedOrder ** checkedType ** checkedTerm)
      _ => Nothing
  _ => Nothing

public export
checkTermList : (order : GebSExp) -> (types, terms : GebSList) ->
  Maybe (checkedOrder : GebPOrder order **
         checkedTypeList : GebPTypeList checkedOrder (GATypeList $* types) **
         GebPTermList checkedTypeList $ GATermList $* terms)
checkTermList order types terms =
  case checkOrder order of
    Just checkedOrder => case checkTypeList checkedOrder types of
      Just checkedTypes => case checkAgainstTypeList checkedTypes terms of
        Just checkedTerms => Just (checkedOrder ** checkedTypes ** checkedTerms)
        _ => Nothing
      _ => Nothing
    _ => Nothing

public export
compileOrder : (order : GebSExp) ->
  {auto compiles : IsJust $ checkOrder order} -> GebPOrder order
compileOrder _ {compiles} = IsJustElim compiles

public export
compileType : (order, type : GebSExp) ->
  {auto orderCompiles : IsJust $ checkOrder order} ->
  {auto typeCompiles : IsJust $ checkType (IsJustElim orderCompiles) type} ->
  GebPType (IsJustElim orderCompiles) type
compileType _ _ {orderCompiles} {typeCompiles} = IsJustElim typeCompiles

public export
compileTypeList : (order, types : GebSExp) ->
  {auto isTypeList : ($<) types = GATypeList} ->
  {auto orderCompiles : IsJust $ checkOrder order} ->
  {auto typeListCompiles :
    IsJust $ checkTypeList (IsJustElim orderCompiles) $ ($>) types} ->
  GebPTypeList (IsJustElim orderCompiles) types
compileTypeList {isTypeList=Refl} {orderCompiles} {typeListCompiles}
  _ (_ $* _) = IsJustElim typeListCompiles

public export
compileTypeMatrix : (order, matrix : GebSExp) ->
  {auto isTypeMatrix : ($<) matrix = GATypeMatrix} ->
  {auto orderCompiles : IsJust $ checkOrder order} ->
  {auto compiles :
    IsJust $ checkTypeMatrix (IsJustElim orderCompiles) $ ($>) matrix} ->
  GebPTypeMatrix (IsJustElim orderCompiles) matrix
compileTypeMatrix {isTypeMatrix=Refl} {orderCompiles} {compiles} _ (_ $* _) =
  IsJustElim compiles

public export
compileMatrixIndex : {order, matrix : GebSExp} ->
  {auto orderCompiles : IsJust $ checkOrder order} ->
  (checkedMatrix : GebPTypeMatrix (IsJustElim orderCompiles) matrix) ->
  (index : GebSExp) ->
  {auto compiles : IsJust $ checkMatrixIndex checkedMatrix index} ->
  GebMatrixIndex checkedMatrix index
compileMatrixIndex {orderCompiles} {compiles} _ _ = IsJustElim compiles

public export
gebMatrixIndexExp : Nat -> GebSExp
gebMatrixIndexExp n = GAMatrixIndex $* gebIndexList n

public export
compileTerm : {order, type : GebSExp} ->
  {auto orderCompiles : IsJust $ checkOrder order} ->
  (checkedType : GebPType (IsJustElim orderCompiles) type) ->
  (term : GebSExp) ->
  {auto compiles : IsJust $ checkAgainstType checkedType term} ->
  GebPTerm checkedType term
compileTerm _ _ {orderCompiles} {compiles} = IsJustElim compiles

public export
compileTermList : {order, types : GebSExp} ->
  {auto orderCompiles : IsJust $ checkOrder order} ->
  (checkedTypes : GebPTypeList (IsJustElim orderCompiles) types) ->
  (terms : GebSExp) ->
  {auto isTermList : ($<) terms = GATermList} ->
  {auto compiles : IsJust $ checkAgainstTypeList checkedTypes $ ($>) terms} ->
  GebPTermList checkedTypes terms
compileTermList {isTermList=Refl} {orderCompiles} {compiles} _ (_ $* _) =
  IsJustElim compiles

public export
showType : {order, type : GebSExp} -> {checkedOrder : GebPOrder order} ->
  GebPType checkedOrder type -> String
showType {type} _ = show type

public export
showTypeList : {order, types : GebSExp} -> {checkedOrder : GebPOrder order} ->
  GebPTypeList checkedOrder types -> String
showTypeList {types} _ = show types

public export
showTypeMatrix : {order, matrix : GebSExp} ->
  {checkedOrder : GebPOrder order} ->
  GebPTypeMatrix checkedOrder matrix -> String
showTypeMatrix {matrix} _ = show matrix

public export
showTerm : {order, type : GebSExp} -> {checkedOrder : GebPOrder order} ->
  {checkedType : GebPType checkedOrder type} ->
  {term : GebSExp} -> GebPTerm checkedType term -> String
showTerm {type} {term} _ = "(" ++ show term ++ " :: " ++ show type ++ ")"

public export
showTermList : {order, types, terms : GebSExp} ->
  {checkedOrder : GebPOrder order} ->
  {checkedTypes : GebPTypeList checkedOrder types} ->
  GebPTermList checkedTypes terms -> String
showTermList {types} {terms} _ =
  "((" ++ show terms ++ ") :: (" ++ show types ++ "))"

mutual
  public export
  data GebCategory : GebSExp -> Type where
    MinimalReflective : GebCategory ($^ GAMinimal)

  public export
  data GebObject : (representation : GebSExp) -> {catRep : GebSExp} ->
    GebCategory catRep -> Type where

      AtomObject : {catRep : GebSExp} -> (category : GebCategory catRep) ->
        GebObject (GAAtomObject $*** catRep) category
      SExpObject : {catRep : GebSExp} -> (category : GebCategory catRep) ->
        GebObject (GASExpObject $*** catRep) category
      SListObject : {catRep : GebSExp} -> (category : GebCategory catRep) ->
        GebObject (GASListObject $*** catRep) category

      ObjectReflection : {hostCatRep, targetCatRep : GebSExp} ->
        (hostCat : GebCategory hostCatRep) ->
        (targetCat : GebCategory targetCatRep) ->
        GebObject (GAObjectReflection $* [hostCatRep, targetCatRep]) hostCat
      MorphismReflection : {hostCatRep, targetCatRep : GebSExp} ->
        {hostCat : GebCategory hostCatRep} ->
        {targetCat : GebCategory targetCatRep} ->
        {domainRep, codomainRep : GebSExp} ->
        GebObject domainRep targetCat -> GebObject codomainRep targetCat ->
        GebObject
          (GAMorphismReflection $*
            [hostCatRep, targetCatRep, domainRep, codomainRep]) hostCat

  public export
  data GebMorphism : (representation : GebSExp) -> {catRep : GebSExp} ->
    {domainRep, codomainRep : GebSExp} -> {category : GebCategory catRep} ->
    GebObject domainRep category -> GebObject codomainRep category ->
    Type where
      TypecheckObjectElim : {hostCatRep, targetCatRep : GebSExp} ->
        {hostCat : GebCategory hostCatRep} ->
        {targetCat : GebCategory targetCatRep} ->
        {domainRep, codomainRep, inputRep,
         checkCaseRep, failCaseRep : GebSExp} ->
        {domain : GebObject domainRep hostCat} ->
        {codomain : GebObject codomainRep hostCat} ->
        GebMorphism inputRep domain
          (SExpObject hostCat) ->
        GebMorphism checkCaseRep
          (ObjectReflection hostCat targetCat) codomain ->
        GebMorphism failCaseRep (SExpObject hostCat) codomain ->
        GebMorphism (GATypecheckObjectElim $*
          [hostCatRep, targetCatRep, domainRep, codomainRep,
           inputRep, checkCaseRep, failCaseRep]) domain codomain

mutual
  public export
  data WellTypedExp : GebSExp -> Type where
    IsAtomicRefinement : WellTypedExp (GARefinementSort $* [])

  public export
  data WellTypedList : GebSList -> Type where
    EmptyList : WellTypedList []
    ListCons : {x : GebSExp} -> {l : GebSList} ->
      WellTypedExp x -> WellTypedList l -> WellTypedList (x :: l)

  public export
  data WellTypedFunctionExp : GebSExp -> Type where

  public export
  data GebAtomicContext : GebSExp -> Type where

  public export
  data GebParameterizedContext : GebSExp -> Type where
    GebContextFunction :
      {functionRepresentation : GebSExp} ->
      (gebFunction :
        WellTypedFunctionExp $
          GAMorphismRefinement $*
            [GAExpressionObject $**^ GASExpObject,
             GAExpressionObject $* [GAMaybeFunctor $**^ GASExpObject]]) ->
      GebParameterizedContext $
        GAParameterizedContext $*** functionRepresentation

  public export
  data GebContext : GebSExp -> Type where
    AtomicContext : {x : GebSExp} -> GebAtomicContext x -> GebContext x
    ParameterizedContext : {x : GebSExp} ->
      GebParameterizedContext x -> GebContext x

public export
HandledAtomsList : List GebAtom
HandledAtomsList =
  [
    GARefinementSort
  , GASortSort
  ]

mutual
  -- | These types exist to carry validation of the Geb algorithms, as
  -- | opposed to just the expressions, whose validations are carried
  -- | by the "WellTyped" types above.

  public export
  data TypecheckExpSuccess : GebSExp -> Type where
    CheckedTerm : {a : GebAtom} -> {l : GebSList} ->
      (handled : ListContains HandledAtomsList a) ->
      (listSuccess : TypecheckListSuccess l) ->
      WellTypedExp (a $* l) ->
      TypecheckExpSuccess (a $* l)

  public export
  data TypecheckListSuccess : GebSList -> Type where
    CheckedEmptyList : WellTypedList [] -> TypecheckListSuccess []
    CheckedListCons : TypecheckExpSuccess x -> TypecheckListSuccess l ->
      WellTypedList (x :: l) -> TypecheckListSuccess (x :: l)

public export
successAtomSucceeds : {x : GebSExp} -> TypecheckExpSuccess x ->
  ListContains HandledAtomsList (($<) x)
successAtomSucceeds (CheckedTerm handled _ _) = handled

public export
successListSucceeds : {x : GebSExp} -> TypecheckExpSuccess x ->
  TypecheckListSuccess (($>) x)
successListSucceeds (CheckedTerm _ listSuccess _) = listSuccess

public export
checkedExp : {x : GebSExp} -> TypecheckExpSuccess x -> WellTypedExp x
checkedExp (CheckedTerm _ _ exp) = exp

public export
successHeadSucceeds : {x : GebSExp} -> {l : GebSList} ->
  TypecheckListSuccess (x :: l) ->
  TypecheckExpSuccess x
successHeadSucceeds (CheckedEmptyList _) impossible
successHeadSucceeds (CheckedListCons success _ _) = success

public export
successTailSucceeds : {x : GebSExp} -> {l : GebSList} ->
  TypecheckListSuccess (x :: l) ->
  TypecheckListSuccess l
successTailSucceeds (CheckedEmptyList _) impossible
successTailSucceeds (CheckedListCons _ success _) = success

public export
checkedList : {l : GebSList} ->
  TypecheckListSuccess l -> WellTypedList l
checkedList (CheckedEmptyList _) = EmptyList
checkedList (CheckedListCons _ _ list) = list

public export
GebMonad : Type -> Type
GebMonad = Prelude.Basics.id

public export
GebContextMonad : Type -> Type
GebContextMonad = ReaderT (DPair GebSExp GebContext) GebMonad

public export
CompileResult : GebSExp -> Type
CompileResult x = GebContextMonad $ Dec $ TypecheckExpSuccess x

public export
ListCompileResult : GebSList -> Type
ListCompileResult l = GebContextMonad $ Dec $ TypecheckListSuccess l

public export
AtomHandler : GebAtom -> Type
AtomHandler a =
  (l : GebSList) -> GebContextMonad (TypecheckListSuccess l) ->
  ListContains HandledAtomsList a -> CompileResult (a $* l)

public export
GARefinementSortHandled : ListContains HandledAtomsList GARefinementSort
GARefinementSortHandled = Left Refl

public export
gebRefinementHandler : AtomHandler GARefinementSort
gebRefinementHandler [] _ _ =
  pure $ Yes $ CheckedTerm
    GARefinementSortHandled (CheckedEmptyList EmptyList) IsAtomicRefinement
gebRefinementHandler (_ :: _) _ _ = pure $ No $ \success => case success of
  IsAtomicRefinement (_ $* (_ :: _)) impossible

public export
GASortSortHandled : ListContains HandledAtomsList GARefinementSort
GASortSortHandled = Left Refl

public export
gebSortSortHandler : AtomHandler GASortSort
gebSortSortHandler _ _ _ = pure $ No $ \success =>
  case success of (IsAtomicRefinement _) impossible

public export
AtomHandlerList : ListForAll AtomHandler HandledAtomsList
AtomHandlerList =
  (
    gebRefinementHandler
  , gebSortSortHandler
  , ()
  )

public export
gebHandlesOnlySpecifiedAtoms : (a : GebAtom) -> (l : GebSList) ->
  GebContextMonad (TypecheckExpSuccess (a $* l) -> ListContains HandledAtomsList a)
gebHandlesOnlySpecifiedAtoms a l = pure successAtomSucceeds

public export
gebCompileNotListElim :
  (a : GebAtom) -> (l : GebSList) ->
  GebContextMonad $
    Not (TypecheckListSuccess l) -> Not (TypecheckExpSuccess (a $* l))
gebCompileNotListElim a l = let _ = IdentityIsMonad in do
  pure $ \listFail, expSuccess => listFail $ successListSucceeds expSuccess

public export
gebCompileNilElim : ListCompileResult []
gebCompileNilElim = pure $ Yes (CheckedEmptyList EmptyList)

public export
gebCompileCertifiedConsElim :
  (x : GebSExp) -> (l : GebSList) ->
  GebContextMonad (TypecheckExpSuccess x) ->
  GebContextMonad (TypecheckListSuccess l) ->
  ListCompileResult (x :: l)
gebCompileCertifiedConsElim x l mi mli = let _ = IdentityIsMonad in do
  i <- mi
  li <- mli
  pure $ Yes $ CheckedListCons i li (ListCons (checkedExp i) (checkedList li))

public export
gebCompileNotHeadElim : (x : GebSExp) -> (l : GebSList) ->
  GebContextMonad $
    Not (TypecheckExpSuccess x) -> Not (TypecheckListSuccess (x :: l))
gebCompileNotHeadElim x l =
  pure $ \headFail, listSuccess => headFail $ successHeadSucceeds listSuccess

public export
gebCompileNotTailElim : (x : GebSExp) -> (l : GebSList) ->
  GebContextMonad $
    Not (TypecheckListSuccess l) -> Not (TypecheckListSuccess (x :: l))
gebCompileNotTailElim x l =
  pure $ \tailFail, listSuccess => tailFail $ successTailSucceeds listSuccess

public export
GebCompileSignature :
  SExpRefinePerAtomHandlerSig
    GebContextMonad
    TypecheckExpSuccess
    TypecheckListSuccess
GebCompileSignature =
  SExpRefinePerAtomHandlerArgs
    HandledAtomsList
    AtomHandlerList
    gebHandlesOnlySpecifiedAtoms
    gebCompileNotListElim
    gebCompileNilElim
    gebCompileCertifiedConsElim
    gebCompileNotHeadElim
    gebCompileNotTailElim

public export
gebCompile : GebSExp ~> CompileResult
gebCompile =
  let _ = IdentityIsMonad in sexpRefinePerAtomHandlerReader GebCompileSignature

public export
AnyErased : Type
AnyErased = Exists {type=Type} id

public export
idrisInterpretWellTypedExp : (a : GebAtom) -> (l : GebSList) ->
  (TypecheckListSuccess l -> List AnyErased) ->
  (handled : ListContains HandledAtomsList a) ->
  (listSuccess : TypecheckListSuccess l) ->
  WellTypedExp (a $* l) ->
  AnyErased
idrisInterpretWellTypedExp GARefinementSort [] successToAnyErased _ _
  IsAtomicRefinement =
    Evidence Type (GebSExp -> Bool)

public export
idrisInterpretExpElim : (a : GebAtom) -> (l : GebSList) ->
  (TypecheckListSuccess l -> List AnyErased) ->
  TypecheckExpSuccess (a $* l) ->
  AnyErased
idrisInterpretExpElim a l success
  (CheckedTerm handled listSuccess refinement) =
    idrisInterpretWellTypedExp
      a l success handled listSuccess refinement

public export
idrisInterpretNilElim : TypecheckListSuccess [] -> List AnyErased
idrisInterpretNilElim (CheckedEmptyList _) = []

public export
idrisInterpretConsElim : (x : GebSExp) -> (l : GebSList) ->
  (TypecheckExpSuccess x -> AnyErased) ->
  (TypecheckListSuccess l -> List AnyErased) ->
  TypecheckListSuccess (x :: l) ->
  List AnyErased
idrisInterpretConsElim x l i li (CheckedListCons sx sl _) = i sx :: li sl

public export
idrisInterpretations :
  ((x : GebSExp) -> TypecheckExpSuccess x -> AnyErased,
   (l : GebSList) -> TypecheckListSuccess l -> List AnyErased)
idrisInterpretations =
  sexpEliminators
    {sp=(\x => TypecheckExpSuccess x -> AnyErased)}
    {lp=(\l => TypecheckListSuccess l -> List AnyErased)}
    $ SExpEliminatorArgs
      idrisInterpretExpElim
      idrisInterpretNilElim
      idrisInterpretConsElim

public export
GebSExpTransform : GebSExp -> Type
GebSExpTransform x = WellTypedExp x -> DPair GebSExp WellTypedExp

public export
GebSListTransform : GebSList -> Type
GebSListTransform l = WellTypedList l -> DPair GebSList WellTypedList

public export
record GebTransformSig where
  constructor GebTransformArgs
  transformRefinementSort : DPair GebSExp WellTypedExp
  transformNil : WellTypedList [] -> DPair GebSList WellTypedList
  transformCons : (x : GebSExp) -> (l : GebSList) ->
    WellTypedList (x :: l) -> DPair GebSList WellTypedList

mutual
  public export
  gebSExpTransform : GebTransformSig -> GebSExp ~> GebSExpTransform
  gebSExpTransform signature (GARefinementSort $* []) IsAtomicRefinement =
    transformRefinementSort signature

  public export
  gebSListTransform : GebTransformSig -> GebSList ~> GebSListTransform
  gebSListTransform signature [] EmptyList = transformNil signature EmptyList
  gebSListTransform signature (x :: l) (ListCons typedExp typedList) =
    let transformedExp = gebSExpTransform signature x typedExp in
    let transformedList = gebSListTransform signature l typedList in
    transformCons signature (fst transformedExp) (fst transformedList) $
      ListCons (snd transformedExp) (snd transformedList)

public export
gebTransforms : GebTransformSig ->
  (GebSExp ~> GebSExpTransform, GebSList ~> GebSListTransform)
gebTransforms signature =
  (gebSExpTransform signature, gebSListTransform signature)

{-

----------------------------------------------------------------
---- General definition of programming language / metalogic ----
----------------------------------------------------------------

-- | A "Language" (short in this case for "programming language") is a category
-- | which is capable of performing computation and can be defined solely by
-- | computation.  It can be viewed as having morphisms which represent
-- | computable functions with computably-representable effects.
-- |
-- | By "capable of performing computation", we mean that Gödel's
-- | incompleteness theorems apply to the category.  In other words, it can
-- | express metalogic; we could also say that it can reflect itself, in that
-- | it can define functions on its own expressions.  (So perhaps we might
-- | say something like "computable metacategory" rather than "programming
-- | language".)  A combination of products, coproducts, and decidable
-- | equality gives us the ability to perform substitution, which in turn
-- | allows us to represent function application -- the fundamental
-- | computation in any programming language.
-- |
-- | A language is unsuitable as a metalogic if it is inconsistent -- if its
-- | operational semantics allow non-termination, or if it has any partial
-- | functions.  Of course, one consequence of Gödel's incompleteness theorems
-- | is that we can never be sure that there _are_ any languages that are
-- | suitable as metalogics in that sense!
-- |
-- | So there is a minimal programming language, with this definition:  just
-- | what is required for Gödel's incompleteness theorems to apply.  There is
-- | also a maximal programming language:  the universal Turing machine,
-- | with non-terminating and partial functions.
-- |
-- | Our definitions of languages below all take the form of a
-- | category-theoretical, point-free (termless) definition of syntax and
-- | type system, and an operational definition of semantics using an
-- | interpretation of objects as the types and morphisms as the functions
-- | of a programming language which does have terms.  The functions of the
-- | language are general computable functions with effects, the terms are
-- | S-expressions, and the types are specifications of the domains,
-- | codomains, input-output behavior, and the effects of functions.

mutual
  -- | Takes no parameters.
  public export
  data Language : GebSExp -> GebSList -> Type where
    Minimal : Language ($^ GAMinimal) []
    HigherOrder : Language ($^ GAHigherOrder) []

  public export
  data LanguageHasExponentials : {lang : GebSExp} ->
    Language lang [] -> Type where
      HigherOrderHasExponentials : LanguageHasExponentials HigherOrder

  -- | Takes one parameter, a language.
  public export
  data Object : GebSExp -> GebSList -> Type where
    Initial :
      {lang : GebSExp} -> Language lang [] ->
      Object (GAInitial $*** lang) [lang]
    Terminal :
      {lang : GebSExp} -> Language lang [] ->
      Object (GATerminal $*** lang) [lang]
    Product :
      {lang, left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      Object left [lang] -> Object right [lang] ->
      Object (GAProduct $* [left, right]) [lang]
    Coproduct :
      {lang, left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      Object left [lang] -> Object right [lang] ->
      Object (GACoproduct $* [left, right]) [lang]
    Exponential : {lang, left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {auto hasExponentials : LanguageHasExponentials isLanguage} ->
      Object left [lang] -> Object right [lang] ->
      Object (GAExponential $* [left, right]) [lang]

    RefinementObject : {lang, refined, pass, fail, test : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {refinedObject : Object refined [lang]} ->
      {passObject : Object pass [lang]} ->
      {failObject : Object fail [lang]} ->
      (testMorphism :
        Morphism test [lang, refined, GACoproduct $* [pass, fail]]) ->
      Object (GARefinementObject $* [refined, pass, fail, test]) [lang]

    -- | Reflects expressions of each refinement into each language.
    -- | (In particular, this might reflect into language X an expression
    -- | of language Y, or an expression of Geb itself.)
    ExpressionObject : {lang, sort, refinement : GebSExp} ->
      Language lang [] -> Sort sort [] -> Refinement refinement [sort] ->
      Object (GAExpressionObject $* [lang, refinement]) [lang]

  -- | Takes an "implicit" language parameter and two explicit
  -- | object parameters, which must have the same language.
  public export
  data Morphism : GebSExp -> GebSList -> Type where
    Identity : {lang, obj : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      Object obj [lang] -> Morphism (GAIdentity $*** obj) [lang, obj, obj]
    Compose : {lang, a, b, c, g, f : GebSExp} ->
      {auto isLanguage : Language lang []} -> {objA : Object a [lang]} ->
      {objB : Object b [lang]} -> {objC : Object c [lang]} ->
      Morphism g [lang, b, c] -> Morphism f [lang, a, b] ->
      Morphism (GACompose $* [g, f]) [lang, a, c]
    FromInitial : {lang, obj : GebSExp} ->
      {auto isLanguage : Language lang []} -> Object obj [lang] ->
      Morphism (GAFromInitial $*** obj) [lang, GAInitial $*** lang, obj]
    ToTerminal : {lang, obj : GebSExp} ->
      {auto isLanguage : Language lang []} -> Object obj [lang] ->
      Morphism (GAToTerminal $*** obj) [lang, obj, GATerminal $*** lang]
    ProductIntro : {lang, domain, codomainLeft, codomainRight,
        left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {domainObject : Object domain [lang]} ->
      {codomainLeftObject : Object codomainLeft [lang]} ->
      {codomainRightObject : Object codomainRight [lang]} ->
      Morphism left [lang, domain, codomainLeft] ->
      Morphism right [lang, domain, codomainRight] ->
      Morphism (GAProductIntro $* [left, right])
        [lang, domain, GAProduct $* [codomainLeft, codomainRight]]
    ProductElimLeft : {lang, left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      Object left [lang] -> Object right [lang] ->
      Morphism (GAProductElimLeft $* [left, right])
        [lang, GAProduct $* [left, right], left]
    ProductElimRight : {lang, left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      Object left [lang] -> Object right [lang] ->
      Morphism (GAProductElimRight $* [left, right])
        [lang, GAProduct $* [left, right], right]
    CoproductIntroLeft : {lang, left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      Object left [lang] -> Object right [lang] ->
      Morphism (GACoproductIntroLeft $* [left, right])
        [lang, left, GACoproduct $* [left, right]]
    CoproductIntroRight : {lang, left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      Object left [lang] -> Object right [lang] ->
      Morphism (GACoproductIntroRight $* [left, right])
        [lang, right, GACoproduct $* [left, right]]
    CoproductElim : {lang, domainLeft, domainRight, codomain,
        left, right : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {domainLeftObject : Object domainLeft [lang]} ->
      {domainRightObject : Object domainRight [lang]} ->
      {codomainObject : Object codomain [lang]} ->
      Morphism left [lang, domainLeft, codomain] ->
      Morphism right [lang, domainRight, codomain] ->
      Morphism (GACoproductElim $* [left, right])
        [lang, GACoproduct $* [domainLeft, domainRight], codomain]
    ExponentialEval : {lang, domain, codomain : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {hasExponentials : LanguageHasExponentials isLanguage} ->
      Object domain [lang] -> Object codomain [lang] ->
      Morphism (GAExponentialEval $* [domain, codomain])
        [lang,
         GAProduct $* [GAExponential $* [domain, codomain], domain], codomain]
    Curry : {lang, domainLeft, domainRight, codomain, morphism : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {hasExponentials : LanguageHasExponentials isLanguage} ->
      {domainLeftObject : Object domainLeft [lang]} ->
      {domainRightObject : Object domainRight [lang]} ->
      {codomainObject : Object codomain [lang]} ->
      Morphism morphism
        [lang, GAProduct $* [domainLeft, domainRight], codomain] ->
      Morphism (GACurry $*** morphism)
        [lang, domainLeft, GAExponential $* [domainRight, codomain]]

  -- | Takes no parameters.
  -- | These are "refinement families" (by analogy to "type families").
  public export
  data Sort : GebSExp -> GebSList -> Type where
    SortSort : Sort ($^ GASortSort) []
    RefinementSort : Sort ($^ GARefinementSort) []
    ExpressionSort : Sort ($^ GAExpressionSort) []
    LanguageSort : Sort ($^ GALanguageSort) []
    ObjectSort : Sort ($^ GAObjectSort) []
    MorphismSort : Sort ($^ GAMorphismSort) []

  -- | Takes one parameter, a sort.  Refinements are analogous to types --
  -- | a refinement may be viewed as the type of S-expressions which
  -- | are selected by it (the refinement in this view is a characteristic
  -- | function on S-expressions).
  public export
  data Refinement : GebSExp -> GebSList -> Type where
    SortRefinement : Refinement ($^ GASortRefinement) [$^ GASortSort]
    RefinementRefinement : {s : GebSExp} -> Sort s [] ->
      Refinement (GARefinementRefinement $*** s) [$^ GARefinementSort]
    ExpressionRefinement : {s, r : GebSExp} ->
      Refinement r [s] ->
      Refinement (GAExpressionRefinement $* [s, r]) [$^ GAExpressionSort]
    LanguageRefinement :
      Refinement ($^ GALanguageRefinement) [$^ GALanguageSort]
    ObjectRefinement : {lang : GebSExp} ->
      Language lang [] ->
      Refinement (GAObjectRefinement $*** lang) [$^ GAObjectSort]
    MorphismRefinement : {lang, domain, codomain : GebSExp} ->
      Object domain [lang] -> Object codomain [lang] ->
      Refinement
        (GAMorphismRefinement $* [lang, domain, codomain]) [$^ GAMorphismSort]

  -- | Takes two parameters, an "implicit" sort and a refinement of
  -- | that sort.  An expression consists of refinement _constructors_;
  -- | it may be viewed as an S-expression which is selected by its
  -- | refinement parameter.
  public export
  data Expression : GebSExp -> GebSList -> Type where
    SortExpression : {s : GebSExp} -> Sort s [] ->
      Expression (GASortExpression $*** s) [$^ GASortSort, $^ GASortRefinement]
    RefinementExpression : {s, r : GebSExp} ->
      Refinement r [GARefinementRefinement $*** s] ->
      Expression (GARefinementExpression $*** r)
        [$^ GARefinementSort, GARefinementRefinement $*** s]
    LanguageExpression : {lang : GebSExp} ->
      Language lang [] ->
      Expression (GALanguageExpression $*** lang)
        [$^ GALanguageSort, $^ GALanguageRefinement]
    ObjectExpression : {lang, object : GebSExp} ->
      Object object [lang] ->
      Expression (GAObjectExpression $*** object)
        [$^ GAObjectSort, GAObjectRefinement $*** lang]
    MorphismExpression : {lang, domain, codomain, morphism : GebSExp} ->
      Morphism morphism [lang, domain, codomain] ->
      Expression (GAMorphismExpression $*** morphism)
        [$^ GAMorphismSort, GAMorphismRefinement $* [lang, domain, codomain]]

-----------------------------------------------------
---- Type-checking in Idris-2 of Geb expressions ----
-----------------------------------------------------

mutual
  public export
  objectUnique : {lang, object : GebSExp} ->
    (obj, obj' : Object object [lang]) ->
    obj = obj'
  objectUnique obj obj' = objectUnique_hole

  public export
  checkExpression : (expression : GebSExp) -> (refinement : GebSList) ->
    Dec $ Expression expression refinement
  checkExpression x r = checkExpression_hole

  public export
  checkExpressionCorrect : {x : GebSExp} -> {l : GebSList} ->
    (exp : Expression x l) -> checkExpression x l = Yes exp
  checkExpressionCorrect {x} {l} exp = checkExpressionCorrect_hole

  public export
  expressionUnique : {x : GebSExp} -> {l : GebSList} ->
    (exp, exp' : Expression x l) -> exp = exp'
  expressionUnique {x} {l} exp exp' = expressionUnique_hole

--------------------------------------------------------
---- Interpretation into Idris-2 of Geb expressions ----
--------------------------------------------------------

mutual
  public export
  interpretObject : {lang, obj : GebSExp} ->
    {isLanguage : Language lang []} -> Object obj [lang] -> Type
  interpretObject (Initial _) = Void
  interpretObject (Terminal _) = ()
  interpretObject (Product left right) =
    (interpretObject {isLanguage} left, interpretObject {isLanguage} right)
  interpretObject (Coproduct left right) =
    Either
      (interpretObject {isLanguage} left)
      (interpretObject {isLanguage} right)
  interpretObject (Exponential domain codomain) =
    interpretObject {isLanguage} domain -> interpretObject {isLanguage} codomain
  interpretObject (RefinementObject
    {refinedObject} {passObject} {failObject} testMorphism) =
      interpretRefinementObject {isLanguage}
        refinedObject passObject failObject testMorphism
  interpretObject (ExpressionObject {sort} {refinement} _ _ _) =
    (x : GebSExp ** Expression x [sort, refinement])

  public export
  interpretRefinementObject : {lang, refined, pass, fail, morphism : GebSExp} ->
    {isLanguage : Language lang []} ->
    Object refined [lang] -> Object pass [lang] -> Object fail [lang] ->
    (testMorphism :
      Morphism morphism [lang, refined, GACoproduct $* [pass,fail]]) -> Type
  interpretRefinementObject {isLanguage}
    refinedObject passObject failObject testMorphism =
      (x : interpretObject {isLanguage} refinedObject **
       IsLeft {a=(interpretObject passObject)} {b=(interpretObject failObject)}
        $ interpretMorphism
            {domainObject=refinedObject}
            {codomainObject=(Coproduct passObject failObject)}
            testMorphism x)

  public export
  interpretMorphism : {lang, domain, codomain, morphism : GebSExp} ->
    {isLanguage : Language lang []} ->
    {domainObject : Object domain [lang]} ->
    {codomainObject : Object codomain [lang]} ->
    (isMorphism : Morphism morphism [lang, domain, codomain]) ->
    interpretObject {isLanguage} domainObject ->
    interpretObject {isLanguage} codomainObject
  interpretMorphism m = interpretMorphism_hole

  public export
  interpretRefinement : {s, r : GebSExp} ->
    Refinement r [s] -> (GebSExp -> Bool)
  interpretRefinement {s} {r} isRefinement x = interpretRefinement_hole

------------------------------------------------------
---- Morphism transformations ("compiler passes") ----
------------------------------------------------------

ObjectMap : {sourceLang, targetLang : GebSExp} ->
  Language sourceLang [] -> Language targetLang [] ->
  Type
ObjectMap {sourceLang} {targetLang} _ _ =
  (sourceObj : GebSExp) -> Object sourceObj [sourceLang] ->
  (targetObj : GebSExp ** Object targetObj [targetLang])

LanguageFunctor : {sourceLang, targetLang : GebSExp} ->
  {sourceIsLanguage : Language sourceLang []} ->
  {targetIsLanguage : Language targetLang []} ->
  (objectMap : ObjectMap sourceIsLanguage targetIsLanguage) ->
  Type
LanguageFunctor {sourceLang} {targetLang} {sourceIsLanguage} {targetIsLanguage}
  objectMap =
    (domain, codomain : GebSExp) ->
    (domainObject : Object domain [sourceLang]) ->
    (codomainObject : Object codomain [sourceLang]) ->
    (morphism : GebSExp) ->
    (isMorphism : Morphism morphism [sourceLang, domain, codomain]) ->
    (transformed : GebSExp **
     Morphism transformed
      [targetLang,
       fst (objectMap domain domainObject),
       fst (objectMap codomain codomainObject)])

-- | A correct compiler pass is a functor whose morphism map
-- | preserves extensional equality.
-- |
-- | It might be a useful generalization for this definition to require only
-- | isomorphism, not equality.

ObjectMapPreservesInterpretation : {sourceLang, targetLang : GebSExp} ->
  {sourceIsLanguage : Language sourceLang []} ->
  {targetIsLanguage : Language targetLang []} ->
  ObjectMap sourceIsLanguage targetIsLanguage ->
  Type
ObjectMapPreservesInterpretation {sourceLang} {targetLang}
  {sourceIsLanguage} {targetIsLanguage} objectMap =
    (object : GebSExp) -> (isObject : Object object [sourceLang]) ->
    interpretObject {isLanguage=sourceIsLanguage} isObject =
      interpretObject {isLanguage=targetIsLanguage}
        (snd (objectMap object isObject))

FunctorPreservesInterpretation : {sourceLang, targetLang : GebSExp} ->
  {sourceIsLanguage : Language sourceLang []} ->
  {targetIsLanguage : Language targetLang []} ->
  (objectMap : ObjectMap sourceIsLanguage targetIsLanguage) ->
  (preservesObjects : ObjectMapPreservesInterpretation
    {sourceIsLanguage} {targetIsLanguage} objectMap) ->
  LanguageFunctor {sourceIsLanguage} {targetIsLanguage} objectMap ->
  Type
FunctorPreservesInterpretation {sourceLang} {targetLang}
  {sourceIsLanguage} {targetIsLanguage} objectMap preservesObjects functor =
    (domain, codomain : GebSExp) ->
    (domainObject : Object domain [sourceLang]) ->
    (codomainObject : Object codomain [sourceLang]) ->
    (morphism : GebSExp) ->
    (isMorphism : Morphism
      morphism [sourceLang, domain, codomain]) ->
    (x : interpretObject {isLanguage=sourceIsLanguage} domainObject) ->
    interpretMorphism {isLanguage=sourceIsLanguage}
     {domainObject} {codomainObject} isMorphism x =
      (rewrite preservesObjects codomain codomainObject in
       (interpretMorphism
        {isLanguage=targetIsLanguage}
        {domainObject=(snd (objectMap domain domainObject))}
        (snd (functor
          domain codomain domainObject codomainObject morphism isMorphism))
        (rewrite sym (preservesObjects domain domainObject) in x)))

------------------------------------------------------
---- Operational semantics through term reduction ----
------------------------------------------------------

-- | Above, we define the semantics of Geb through interpretation into
-- | Idris-2.  Here, we do so through more explicit operational semantics,
-- | with representation of terms.  This allows us to examine interpretation
-- | step-by-step, and also, through small-step semantics, to interpret
-- | non-terminating functions.

public export
data TermSort : {lang : GebSExp} -> Language lang [] -> Type where
  TermSortType :
    {lang, object : GebSExp} -> {auto isLanguage : Language lang []} ->
    (isObject : Object object [lang]) -> TermSort isLanguage
  TermSortFunction :
    {lang, domain, codomain : GebSExp} ->
    {auto isLanguage : Language lang []} ->
    (domainObject : Object domain [lang]) ->
    (codomainObject : Object codomain [lang]) ->
    TermSort isLanguage

public export
data Term : {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  (numApplications : Nat) -> TermSort isLanguage -> Type where
    UnappliedMorphismTerm :
      {lang, domain, codomain, morphism : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {domainObject : Object domain [lang]} ->
      {codomainObject : Object codomain [lang]} ->
      (isMorphism : Morphism morphism [lang, domain, codomain]) ->
      Term 0 $ TermSortFunction domainObject codomainObject
    Application :
      {lang, domain, codomain : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {domainObject : Object domain [lang]} ->
      {codomainObject : Object codomain [lang]} ->
      {morphismApplications, termApplications : Nat} ->
      Term morphismApplications
        (TermSortFunction domainObject codomainObject) ->
      Term termApplications (TermSortType domainObject) ->
      Term
        (S $ morphismApplications + termApplications)
        (TermSortType codomainObject)
    UnitTerm : {lang : GebSExp} -> (isLanguage : Language lang []) ->
      Term 0 $ TermSortType (Terminal isLanguage)

public export
FullyAppliedTerm : {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  TermSort isLanguage -> Type
FullyAppliedTerm = Term 0

public export
termSortToExp : {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  TermSort isLanguage -> GebSExp
termSortToExp sort = termSortToExp_hole

public export
termToExp : {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  {numApplications : Nat} -> {sort : TermSort isLanguage} ->
  Term numApplications sort -> GebSExp
termToExp term = termToExp_hole

public export
(lang : GebSExp) => (isLanguage : Language lang []) =>
  Show (TermSort isLanguage) where
    show = show . termSortToExp

public export
(lang : GebSExp) => (isLanguage : Language lang []) =>
  (s : TermSort isLanguage) => (n : Nat) => Show (Term n s) where
    show = show . termToExp

public export
interpretTermSort :
  {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  TermSort isLanguage -> Type
interpretTermSort {isLanguage} (TermSortType object) =
  interpretObject {isLanguage} object
interpretTermSort {isLanguage} (TermSortFunction domain codomain) =
  interpretObject {isLanguage} domain -> interpretObject {isLanguage} codomain

public export
interpretTerm :
  {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  {sort : TermSort isLanguage} -> {numApplications : Nat} ->
  Term numApplications sort ->
  interpretTermSort sort
interpretTerm term = interpretTerm_hole

public export
smallStepMorphismReduction :
  {lang, domain, codomain, morphism : GebSExp} ->
  {auto isLanguage : Language lang []} ->
  {domainObject : Object domain [lang]} ->
  {codomainObject : Object codomain [lang]} ->
  (isMorphism : Morphism morphism [lang, domain, codomain]) ->
  {numApplications : Nat} ->
  Term numApplications (TermSortType domainObject) ->
  (remainingApplications : Nat **
   Term remainingApplications (TermSortType codomainObject))
smallStepMorphismReduction = smallStepMorphismReduction_hole

public export
smallStepTermReduction : {lang : GebSExp} ->
  {auto isLanguage : Language lang []} ->
  {sort : TermSort isLanguage} -> {numApplications : Nat} ->
  Term numApplications sort ->
  (remainingApplications : Nat ** Term remainingApplications sort)
smallStepTermReduction = smallStepTermReduction_hole

public export
data SmallStepTermReductionCompletes :
  {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  {sort : TermSort isLanguage} -> {numApplications : Nat} ->
  (term : Term numApplications sort) ->
  (reduced : FullyAppliedTerm sort) -> Type
  where
    SmallStepReductionLastStep :
      {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
      {sort : TermSort isLanguage} -> {numApplications : Nat} ->
      {term : Term numApplications sort} ->
      {reduced : FullyAppliedTerm sort} ->
      smallStepTermReduction term = Left reduced ->
      SmallStepTermReductionCompletes term reduced
    SmallStepReductionPreviousStep :
      {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
      {sort : TermSort isLanguage} ->
      {numApplications, intermediateNumApplications : Nat} ->
      {term : Term numApplications sort} ->
      {intermediateTerm : Term intermediateNumApplications sort} ->
      {reduced : FullyAppliedTerm sort} ->
      smallStepTermReduction term = Right intermediateTerm ->
      SmallStepTermReductionCompletes intermediateTerm reduced ->
      SmallStepTermReductionCompletes term reduced

public export
data IsNormalizing : {lang : GebSExp} -> Language lang [] -> Type where
  MinimalIsNormalizing : IsNormalizing Minimal
  HigherOrderIsNormalizing : IsNormalizing HigherOrder

public export
smallStepTermReductionCompletes :
  {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  {isNormalizing : IsNormalizing isLanguage} ->
  {sort : TermSort isLanguage} -> {numApplications : Nat} ->
  (term : Term numApplications sort) ->
  Subset (FullyAppliedTerm sort) (SmallStepTermReductionCompletes term)
smallStepTermReductionCompletes {sort} {numApplications} term =
  smallStepTermReductionCompletes_hole

public export
smallStepTermReductionCorrect :
  {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  {isNormalizing : IsNormalizing isLanguage} ->
  {sort : TermSort isLanguage} -> {numApplications : Nat} ->
  (term : Term numApplications sort) ->
  interpretTerm (fst (smallStepTermReductionCompletes {isNormalizing} term)) =
    interpretTerm term
smallStepTermReductionCorrect term = smallStepTermReductionCorrect_hole

-}
