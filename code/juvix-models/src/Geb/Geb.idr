module Geb.Geb

import Library.FunctionsAndRelations
import Library.Decidability
import public RefinedSExp.SExp
import public Data.SortedSet
import public Data.SortedMap
import public Data.DPair
import public Geb.GebAtom

%default total

----------------------------------------------------------------
---- General definition of programming language / metalogic ----
----------------------------------------------------------------

mutual
  public export
  data GebType : (type : GebSExp) -> Type where
    PatternType : {matrix : GebSExp} -> GebTypeMatrix matrix ->
      GebType $ GAPatternType $*** matrix

  public export
  data GebTypeList : (types : GebSExp) -> Type where
    EmptyTypeList : GebTypeList ($^ GATypeList)
    ConsTypeList : {type : GebSExp} -> {types : GebSList} ->
      GebType type -> GebTypeList (GATypeList $* types) ->
      GebTypeList $ GATypeList $* (type :: types)

  public export
  data GebTypeMatrix : (matrix : GebSExp) -> Type where
    EmptyTypeMatrix : GebTypeMatrix ($^ GATypeMatrix)
    ConsTypeMatrix : {row : GebSExp} -> {matrix : GebSList} ->
      GebTypeList row -> GebTypeMatrix (GATypeMatrix $* matrix) ->
      GebTypeMatrix $ GATypeMatrix $* (row :: matrix)

  public export
  data GebMatrixIndex : {matrix : GebSExp} -> GebTypeMatrix matrix ->
    GebSExp -> Type where
      MatrixFirst : {row : GebSExp} -> {matrix : GebSList} ->
        {checkedMatrix : GebTypeMatrix $ GATypeMatrix $* (row :: matrix)} ->
        GebMatrixIndex checkedMatrix (GAMatrixIndex $**^ GAIndexFirst)
      MatrixNext : {row : GebSExp} -> {matrix : GebSList} ->
        {checkedTypeList : GebTypeList row} ->
        {checkedMatrix : GebTypeMatrix $ GATypeMatrix $* matrix} ->
        {indexList : GebSList} ->
        GebMatrixIndex checkedMatrix (GAMatrixIndex $* indexList) ->
        GebMatrixIndex (ConsTypeMatrix checkedTypeList checkedMatrix)
          (GAMatrixIndex $* $^ GAIndexNext :: indexList)

  public export
  matrixIndexTypeListExp : {matrix : GebSExp} ->
    (checkedMatrix : GebTypeMatrix matrix) -> {index : GebSExp} ->
    GebMatrixIndex checkedMatrix index ->
    GebSExp
  matrixIndexTypeListExp (ConsTypeMatrix {row} _ _) MatrixFirst = row
  matrixIndexTypeListExp (ConsTypeMatrix _ tail) (MatrixNext index) =
    matrixIndexTypeListExp tail index

  public export
  matrixIndexTypeList : {matrix : GebSExp} ->
    (checkedMatrix : GebTypeMatrix matrix) -> {index : GebSExp} ->
    (checkedIndex : GebMatrixIndex checkedMatrix index) ->
    GebTypeList (matrixIndexTypeListExp checkedMatrix checkedIndex)
  matrixIndexTypeList (ConsTypeMatrix head _) MatrixFirst = head
  matrixIndexTypeList (ConsTypeMatrix _ tail) (MatrixNext index) =
    matrixIndexTypeList tail index

  public export
  data GebTerm :
    {type : GebSExp} -> GebType type -> (term : GebSExp) -> Type where
      Inject :
        {matrix : GebSExp} -> (checkedMatrix : GebTypeMatrix matrix) ->
        {index : GebSExp} ->
        (checkedIndex : GebMatrixIndex checkedMatrix index) ->
        {terms : GebSExp} ->
        GebTermList (matrixIndexTypeList checkedMatrix checkedIndex) terms ->
        GebTerm (PatternType checkedMatrix) $ GAInjectTerm $* [index, terms]

  public export
  data GebTermList : {types : GebSExp} ->
    GebTypeList types -> (terms : GebSExp) -> Type where
      EmptyTermList : GebTermList EmptyTypeList ($^ GATermList)
      ConsTermList :
        {type : GebSExp} -> {checkedType : GebType type} ->
        {term : GebSExp} -> GebTerm checkedType term ->
        {types : GebSList} ->
        {checkedTypes : GebTypeList (GATypeList $* types)} ->
        {terms : GebSList} ->
        GebTermList checkedTypes (GATermList $* terms) ->
        GebTermList (ConsTypeList checkedType checkedTypes) $
          GATermList $* (term :: terms)

mutual
  public export
  checkType : (type : GebSExp) -> Maybe (GebType type)
  checkType (GAPatternType $* [GATypeMatrix $* matrix]) with
    (checkTypeMatrix matrix)
      checkType (GAPatternType $* [GATypeMatrix $* matrix]) |
        Just checkedMatrix = Just $ PatternType checkedMatrix
      checkType (GAPatternType $* [GATypeMatrix $* matrix]) | _ =
        Nothing
  checkType _ = Nothing

  public export
  checkTypeList : (types : GebSList) ->
    Maybe (GebTypeList $ GATypeList $* types)
  checkTypeList [] = Just EmptyTypeList
  checkTypeList (type :: types) =
    case (checkType type, checkTypeList types) of
      (Just checkedType, Just checkedTypeList) =>
        Just (ConsTypeList checkedType checkedTypeList)
      _ => Nothing

  public export
  checkTypeMatrix : (matrix : GebSList) ->
    Maybe $ GebTypeMatrix (GATypeMatrix $* matrix)
  checkTypeMatrix [] = Just EmptyTypeMatrix
  checkTypeMatrix ((GATypeList $* row) :: matrix) =
    case (checkTypeList row, checkTypeMatrix matrix) of
      (Just checkedRow, Just checkedMatrix) =>
        Just $ ConsTypeMatrix checkedRow checkedMatrix
      _ => Nothing
  checkTypeMatrix _ = Nothing

  public export
  checkMatrixIndex : {matrix : GebSExp} ->
    (checkedMatrix : GebTypeMatrix matrix) ->
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
  checkAgainstType : {type : GebSExp} -> (checkedType : GebType type) ->
    (term : GebSExp) -> Maybe (GebTerm checkedType term)
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
  checkAgainstTypeList : {types : GebSExp} ->
    (checkedTypes : GebTypeList types) -> (terms : GebSList) ->
    Maybe $ GebTermList checkedTypes $ GATermList $* terms
  checkAgainstTypeList EmptyTypeList [] = Just EmptyTermList
  checkAgainstTypeList EmptyTypeList (_ :: _) = Nothing
  checkAgainstTypeList (ConsTypeList _ _) [] = Nothing
  checkAgainstTypeList (ConsTypeList type types) (term :: terms) =
    case (checkAgainstType type term, checkAgainstTypeList types terms) of
      (Just checkedTerm, Just checkedTerms) =>
        Just $ ConsTermList checkedTerm checkedTerms
      _ => Nothing

public export
checkTerm : (type, term : GebSExp) ->
  Maybe (checkedType : GebType type ** GebTerm checkedType term)
checkTerm type term with (checkType type)
  checkTerm type term | Just checkedType =
    case checkAgainstType checkedType term of
      Just checkedTerm => Just (checkedType ** checkedTerm)
      _ => Nothing
  checkTerm type term | _ = Nothing

public export
checkTermList : (types, terms : GebSList) ->
  Maybe (checkedTypeList : GebTypeList (GATypeList $* types) **
         GebTermList checkedTypeList $ GATermList $* terms)
checkTermList types terms with (checkTypeList types)
  checkTermList types terms | Just checkedTypes =
    case checkAgainstTypeList checkedTypes terms of
      Just checkedTerms => Just (checkedTypes ** checkedTerms)
      _ => Nothing
  checkTermList types terms | _ = Nothing

public export
compileType : (type : GebSExp) ->{auto compiles : IsJust $ checkType type} ->
  GebType type
compileType _ {compiles} = IsJustElim compiles

public export
compileTypeList : (types : GebSExp) ->
  {auto isTypeList : ($<) types = GATypeList} ->
  {auto compiles : IsJust $ checkTypeList $ ($>) types} ->
  GebTypeList $ types
compileTypeList {isTypeList=Refl} {compiles} (_ $* _) = IsJustElim compiles

public export
compileTypeMatrix : (matrix : GebSExp) ->
  {auto isTypeMatrix : ($<) matrix = GATypeMatrix} ->
  {auto compiles : IsJust $ checkTypeMatrix $ ($>) matrix} ->
  GebTypeMatrix $ matrix
compileTypeMatrix {isTypeMatrix=Refl} {compiles} (_ $* _) = IsJustElim compiles

public export
compileMatrixIndex : {matrix : GebSExp} ->
  (checkedMatrix : GebTypeMatrix matrix) -> (index : GebSExp) ->
  {auto compiles : IsJust $ checkMatrixIndex checkedMatrix $ index} ->
  GebMatrixIndex checkedMatrix index
compileMatrixIndex {compiles} _ _ = IsJustElim compiles

public export
gebIndexList : Nat -> GebSList
gebIndexList 0 = $*^ GAIndexFirst
gebIndexList (S n) = GAIndexNext $^: gebIndexList n

public export
gebMatrixIndexExp : Nat -> GebSExp
gebMatrixIndexExp n = GAMatrixIndex $* gebIndexList n

public export
compileTerm : {type : GebSExp} -> (checkedType : GebType type) ->
  (term : GebSExp) ->
  {auto compiles : IsJust $ checkAgainstType checkedType term} ->
  GebTerm checkedType term
compileTerm _ _ {compiles} = IsJustElim compiles

public export
compileTermList : {types : GebSExp} -> (checkedTypes : GebTypeList types) ->
  (terms : GebSExp) ->
  {auto isTermList : ($<) terms = GATermList} ->
  {auto compiles : IsJust $ checkAgainstTypeList checkedTypes $ ($>) terms} ->
  GebTermList checkedTypes terms
compileTermList {isTermList=Refl} {compiles} _ (_ $* _) = IsJustElim compiles

public export
showType : {type : GebSExp} -> GebType type -> String
showType {type} _ = show type

public export
showTypeList : {types : GebSExp} -> GebTypeList types -> String
showTypeList {types} _ = show types

public export
showTypeMatrix : {matrix : GebSExp} -> GebTypeMatrix matrix -> String
showTypeMatrix {matrix} _ = show matrix

public export
showTerm : {type : GebSExp} -> {checkedType : GebType type} ->
  {term : GebSExp} -> GebTerm checkedType term -> String
showTerm {type} {term} _ = "(" ++ show term ++ " :: " ++ show type ++ ")"

public export
showTermList : {types, terms : GebSExp} -> {checkedTypes : GebTypeList types} ->
  GebTermList checkedTypes terms -> String
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
