module Geb.Geb

import Library.FunctionsAndRelations
import Library.Decidability
import public RefinedSExp.SExp
import public Data.SortedSet
import public Data.SortedMap
import public Data.DPair

%default total

--------------------------------------------
---- S-expression representation of Geb ----
--------------------------------------------

-- | Having a representation of all Geb expressions as S-expressions allows
-- | us to define, check, and interpret them in uniform ways, without having
-- | to use custom ADTs in different metalanguages (where in this case
-- | "metalanguages" refers to programming languages in which we might interpret
-- |
-- | We begin with this definition even though it might not be clear before
-- | programming languages have been defined below, because we will use the
-- | existence of an S-expression representation to define some functions
-- | (such as decidable equalities and Show instances) below.  These reflect
-- | the reasons for having an S-expression representation of types (objects),
-- | functions (morphisms), and terms (operational semantics given by
-- | interpretation of morphisms as computable functions with effects) within
-- | a compiler.
public export
data GebAtom : Type where
  -- | The notion of sort of refinement -- such as language, object,
  -- | morphism, or even refinement itself.  (One sort of refinement
  -- | is "is a refinement".)
  GARefinementSort : GebAtom
  GALanguageSort : GebAtom
  GASortSort : GebAtom
  GAObjectSort : GebAtom
  GAMorphismSort : GebAtom
  GAExpressionSort : GebAtom

  -- | The notion of a language itself.
  GALanguageRefinement : GebAtom

  -- | The notion of a sort.
  GASortRefinement : GebAtom

  -- | The notion of a refinement.
  GARefinementRefinement : GebAtom

  -- | The notion of an expression.
  GAExpressionRefinement : GebAtom

  -- | The minimal programming language.
  GAMinimal : GebAtom

  -- | Higher-order computable functions.
  GAHigherOrder : GebAtom

  -- | Geb itself.
  GAGeb : GebAtom

  -- | The notion of an object of any programming language.
  GAObjectRefinement : GebAtom

  -- | Objects common to all programming languages.
  GAInitial : GebAtom
  GATerminal : GebAtom
  GAProduct : GebAtom
  GACoproduct : GebAtom
  GAExponential : GebAtom
  GARefinementObject : GebAtom
  GAExpressionObject : GebAtom

  GAObjectExpression : GebAtom
  GAMorphismExpression : GebAtom
  GARefinementExpression : GebAtom
  GASortExpression : GebAtom
  GALanguageExpression : GebAtom

  -- | The notion of a morphism of any programming language.
  GAMorphismRefinement : GebAtom

  -- | Morphisms common to all programming languages.
  GAIdentity : GebAtom
  GACompose : GebAtom
  GAFromInitial : GebAtom
  GAToTerminal : GebAtom
  GAProductIntro : GebAtom
  GAProductElimLeft : GebAtom
  GAProductElimRight : GebAtom
  GACoproductElim : GebAtom
  GACoproductIntroLeft : GebAtom
  GACoproductIntroRight : GebAtom
  GAExpressionIntro : GebAtom
  GAExpressionElim : GebAtom
  GAExponentialEval : GebAtom
  GACurry : GebAtom

  -- | The notion of a term of any programming language.
  GATerm : GebAtom

  -- | Terms common to all programming languages.
  GAExFalsoTerm : GebAtom
  GAUnitTerm : GebAtom
  GAPairTerm : GebAtom
  GALeftTerm : GebAtom
  GARightTerm : GebAtom
  GAExpressionTerm : GebAtom
  GAMorphismTerm : GebAtom
  GAApplication : GebAtom

public export
gaEncode : GebAtom -> Nat
gaEncode GALanguageRefinement = 0
gaEncode GAMinimal = 1
gaEncode GAObjectRefinement = 2
gaEncode GAInitial = 3
gaEncode GATerminal = 4
gaEncode GAProduct = 5
gaEncode GACoproduct = 6
gaEncode GAObjectExpression = 7
gaEncode GAMorphismRefinement = 8
gaEncode GATerm = 9
gaEncode GAUnitTerm = 10
gaEncode GAMorphismTerm = 11
gaEncode GAApplication = 12
gaEncode GAFromInitial = 13
gaEncode GAToTerminal = 14
gaEncode GAIdentity = 15
gaEncode GACompose = 16
gaEncode GAProductIntro = 17
gaEncode GAProductElimLeft = 18
gaEncode GAProductElimRight = 19
gaEncode GACoproductElim = 20
gaEncode GACoproductIntroLeft = 21
gaEncode GACoproductIntroRight = 22
gaEncode GAExpressionIntro = 23
gaEncode GAExpressionElim = 24
gaEncode GAPairTerm = 25
gaEncode GALeftTerm = 26
gaEncode GARightTerm = 27
gaEncode GAExpressionTerm = 28
gaEncode GAExFalsoTerm = 29
gaEncode GAMorphismExpression = 30
gaEncode GAHigherOrder = 31
gaEncode GAGeb = 32
gaEncode GARefinementRefinement = 33
gaEncode GARefinementSort = 34
gaEncode GALanguageSort = 35
gaEncode GASortSort = 36
gaEncode GASortRefinement = 37
gaEncode GAObjectSort = 38
gaEncode GAMorphismSort = 39
gaEncode GARefinementExpression = 40
gaEncode GASortExpression = 41
gaEncode GALanguageExpression = 42
gaEncode GAExpressionSort = 43
gaEncode GAExpressionRefinement = 44
gaEncode GAExpressionObject = 45
gaEncode GAExponential = 46
gaEncode GAExponentialEval = 47
gaEncode GACurry = 48
gaEncode GARefinementObject = 49

public export
gaDecode : Nat -> Maybe GebAtom
gaDecode 0 = Just GALanguageRefinement
gaDecode 1 = Just GAMinimal
gaDecode 2 = Just GAObjectRefinement
gaDecode 3 = Just GAInitial
gaDecode 4 = Just GATerminal
gaDecode 5 = Just GAProduct
gaDecode 6 = Just GACoproduct
gaDecode 7 = Just GAObjectExpression
gaDecode 8 = Just GAMorphismRefinement
gaDecode 9 = Just GATerm
gaDecode 10 = Just GAUnitTerm
gaDecode 11 = Just GAMorphismTerm
gaDecode 12 = Just GAApplication
gaDecode 13 = Just GAFromInitial
gaDecode 14 = Just GAToTerminal
gaDecode 15 = Just GAIdentity
gaDecode 16 = Just GACompose
gaDecode 17 = Just GAProductIntro
gaDecode 18 = Just GAProductElimLeft
gaDecode 19 = Just GAProductElimRight
gaDecode 20 = Just GACoproductElim
gaDecode 21 = Just GACoproductIntroLeft
gaDecode 22 = Just GACoproductIntroRight
gaDecode 23 = Just GAExpressionIntro
gaDecode 24 = Just GAExpressionElim
gaDecode 25 = Just GAPairTerm
gaDecode 26 = Just GALeftTerm
gaDecode 27 = Just GARightTerm
gaDecode 28 = Just GAExpressionTerm
gaDecode 29 = Just GAExFalsoTerm
gaDecode 30 = Just GAMorphismExpression
gaDecode 31 = Just GAHigherOrder
gaDecode 32 = Just GAGeb
gaDecode 33 = Just GARefinementRefinement
gaDecode 34 = Just GARefinementSort
gaDecode 35 = Just GALanguageSort
gaDecode 36 = Just GASortSort
gaDecode 37 = Just GASortRefinement
gaDecode 38 = Just GAObjectSort
gaDecode 39 = Just GAMorphismSort
gaDecode 40 = Just GARefinementExpression
gaDecode 41 = Just GASortExpression
gaDecode 42 = Just GALanguageExpression
gaDecode 43 = Just GAExpressionSort
gaDecode 44 = Just GAExpressionRefinement
gaDecode 45 = Just GAExpressionObject
gaDecode 46 = Just GAExponential
gaDecode 47 = Just GAExponentialEval
gaDecode 48 = Just GACurry
gaDecode 49 = Just GARefinementObject
gaDecode _ = Nothing

export
gaDecodeEncodeIsJust : (a : GebAtom) -> gaDecode (gaEncode a) = Just a
gaDecodeEncodeIsJust GALanguageRefinement = Refl
gaDecodeEncodeIsJust GAMinimal = Refl
gaDecodeEncodeIsJust GAObjectRefinement = Refl
gaDecodeEncodeIsJust GAInitial = Refl
gaDecodeEncodeIsJust GATerminal = Refl
gaDecodeEncodeIsJust GAProduct = Refl
gaDecodeEncodeIsJust GACoproduct = Refl
gaDecodeEncodeIsJust GAObjectExpression = Refl
gaDecodeEncodeIsJust GAMorphismRefinement = Refl
gaDecodeEncodeIsJust GATerm = Refl
gaDecodeEncodeIsJust GAUnitTerm = Refl
gaDecodeEncodeIsJust GAMorphismTerm = Refl
gaDecodeEncodeIsJust GAApplication = Refl
gaDecodeEncodeIsJust GAFromInitial = Refl
gaDecodeEncodeIsJust GAToTerminal = Refl
gaDecodeEncodeIsJust GAIdentity = Refl
gaDecodeEncodeIsJust GACompose = Refl
gaDecodeEncodeIsJust GAProductIntro = Refl
gaDecodeEncodeIsJust GAProductElimLeft = Refl
gaDecodeEncodeIsJust GAProductElimRight = Refl
gaDecodeEncodeIsJust GACoproductElim = Refl
gaDecodeEncodeIsJust GACoproductIntroLeft = Refl
gaDecodeEncodeIsJust GACoproductIntroRight = Refl
gaDecodeEncodeIsJust GAExpressionIntro = Refl
gaDecodeEncodeIsJust GAExpressionElim = Refl
gaDecodeEncodeIsJust GAPairTerm = Refl
gaDecodeEncodeIsJust GALeftTerm = Refl
gaDecodeEncodeIsJust GARightTerm = Refl
gaDecodeEncodeIsJust GAExpressionTerm = Refl
gaDecodeEncodeIsJust GAExFalsoTerm = Refl
gaDecodeEncodeIsJust GAMorphismExpression = Refl
gaDecodeEncodeIsJust GAHigherOrder = Refl
gaDecodeEncodeIsJust GAGeb = Refl
gaDecodeEncodeIsJust GARefinementRefinement = Refl
gaDecodeEncodeIsJust GARefinementSort = Refl
gaDecodeEncodeIsJust GALanguageSort = Refl
gaDecodeEncodeIsJust GASortSort = Refl
gaDecodeEncodeIsJust GASortRefinement = Refl
gaDecodeEncodeIsJust GAObjectSort = Refl
gaDecodeEncodeIsJust GAMorphismSort = Refl
gaDecodeEncodeIsJust GARefinementExpression = Refl
gaDecodeEncodeIsJust GASortExpression = Refl
gaDecodeEncodeIsJust GALanguageExpression = Refl
gaDecodeEncodeIsJust GAExpressionSort = Refl
gaDecodeEncodeIsJust GAExpressionRefinement = Refl
gaDecodeEncodeIsJust GAExpressionObject = Refl
gaDecodeEncodeIsJust GAExponential = Refl
gaDecodeEncodeIsJust GAExponentialEval = Refl
gaDecodeEncodeIsJust GACurry = Refl
gaDecodeEncodeIsJust GARefinementObject = Refl

public export
gebAtomToString : GebAtom -> String
gebAtomToString GALanguageRefinement = "Language"
gebAtomToString GAMinimal = "Minimal"
gebAtomToString GAObjectRefinement = "ObjectRefinement"
gebAtomToString GAInitial = "Initial"
gebAtomToString GATerminal = "Terminal"
gebAtomToString GAProduct = "Product"
gebAtomToString GACoproduct = "Coproduct"
gebAtomToString GAObjectExpression = "ObjectExpression"
gebAtomToString GAMorphismRefinement = "MorphismRefinement"
gebAtomToString GATerm = "Term"
gebAtomToString GAUnitTerm = "UnitTerm"
gebAtomToString GAMorphismTerm = "MorphismTerm"
gebAtomToString GAApplication = "Application"
gebAtomToString GAFromInitial = "FromInitial"
gebAtomToString GAToTerminal = "ToTerminal"
gebAtomToString GAIdentity = "Identity"
gebAtomToString GACompose = "Compose"
gebAtomToString GAProductIntro = "ProductIntro"
gebAtomToString GAProductElimLeft = "ProductElimLeft"
gebAtomToString GAProductElimRight = "ProductElimRight"
gebAtomToString GACoproductElim = "CoproductElim"
gebAtomToString GACoproductIntroLeft = "CoproductIntroLeft"
gebAtomToString GACoproductIntroRight = "CoproductIntroRight"
gebAtomToString GAExpressionIntro = "ExpressionIntro"
gebAtomToString GAExpressionElim = "ExpressionElim"
gebAtomToString GAPairTerm = "PairTerm"
gebAtomToString GALeftTerm = "LeftTerm"
gebAtomToString GARightTerm = "RightTerm"
gebAtomToString GAExpressionTerm = "ExpressionTerm"
gebAtomToString GAExFalsoTerm = "ExFalsoTerm"
gebAtomToString GAMorphismExpression = "MorphismExpression"
gebAtomToString GAHigherOrder = "HigherOrder"
gebAtomToString GAGeb = "Geb"
gebAtomToString GARefinementRefinement = "RefinementRefinement"
gebAtomToString GARefinementSort = "RefinementSort"
gebAtomToString GALanguageSort = "LanguageSort"
gebAtomToString GASortSort = "SortSort"
gebAtomToString GASortRefinement = "SortRefinement"
gebAtomToString GAObjectSort = "ObjectSort"
gebAtomToString GAMorphismSort = "MorphismSort"
gebAtomToString GARefinementExpression = "RefinementExpression"
gebAtomToString GASortExpression = "SortExpression"
gebAtomToString GALanguageExpression = "LanguageExpression"
gebAtomToString GAExpressionSort = "ExpressionSort"
gebAtomToString GAExpressionRefinement = "ExpressionRefinement"
gebAtomToString GAExpressionObject = "ExpressionObject"
gebAtomToString GAExponential = "Exponential"
gebAtomToString GAExponentialEval = "ExponentialEval"
gebAtomToString GACurry = "Curry"
gebAtomToString GARefinementObject = "RefinementObject"

public export
Show GebAtom where
  show a = ":" ++ gebAtomToString a

public export
gaEq : GebAtom -> GebAtom -> Bool
gaEq a a' = gaEncode a == gaEncode a'

public export
Eq GebAtom where
  (==) = gaEq

public export
Ord GebAtom where
  a < a' = gaEncode a < gaEncode a'

export
gaDecEq : (a, a' : GebAtom) -> Dec (a = a')
gaDecEq = encodingDecEq gaEncode gaDecode gaDecodeEncodeIsJust decEq

public export
DecEq GebAtom where
  decEq = gaDecEq

public export
GebSExp : Type
GebSExp = SExp GebAtom

public export
GebSList : Type
GebSList = SList GebAtom

public export
Show GebSExp using DefaultSExpShow where
  show = show

public export
Show GebSList using DefaultSListShow where
  show = show

public export
DecEq GebSExp using DefaultSExpDecEq where
  decEq = decEq

public export
DecEq GebSList using DefaultSListDecEq where
  decEq = decEq

public export
gsDecEq : DecEqPred GebSExp
gsDecEq = decEq

public export
Eq GebSExp using decEqToEq where
  (==) = (==)

public export
Ord GebSExp where
  (<) = sexpLessThan (<)

public export
Ord GebSList where
  (<) = slistLessThan (<)

public export
GebSet : Type
GebSet = SortedSet GebSExp

public export
gebSet : GebSList -> GebSet
gebSet = fromList

public export
GebMap : Type
GebMap = SortedMap GebAtom GebSList

public export
gebMap : List (GebAtom, GebSList) -> GebMap
gebMap = fromList

----------------------------------------------------------------
---- General definition of programming language / metalogic ----
----------------------------------------------------------------

mutual
  public export
  data TypecheckSuccess : GebSExp -> Type where

  public export
  data TypecheckError : GebSExp -> Type where
    NewError : (a : GebAtom) -> (l : GebSList) ->
      (sl : TypecheckSuccessList l) ->
      TypecheckNewError a l sl -> TypecheckError (a $* l)
    SubexpressionFailed : (a : GebAtom) -> (l : GebSList) ->
      TypecheckErrors l -> TypecheckError (a $* l)

  public export
  data TypecheckSuccessList : GebSList -> Type where
    EmptySuccessList : TypecheckSuccessList []
    SuccessListCons : (x : GebSExp) -> (l : GebSList) ->
      TypecheckSuccess x -> TypecheckSuccessList l ->
      TypecheckSuccessList (x :: l)

  public export
  data TypecheckNewError : (a : GebAtom) -> (l : GebSList) ->
    TypecheckSuccessList l -> Type where
      UnimplementedAtom : (a : GebAtom) -> (l : GebSList) ->
        (sl : TypecheckSuccessList l) -> TypecheckNewError a l sl

  public export
  data TypecheckErrors : GebSList -> Type where
    FirstError : (x : GebSExp) -> (l : GebSList) ->
      TypecheckError x -> TypecheckSuccessList l -> TypecheckErrors (x :: l)
    NoNewError : (x : GebSExp) -> (l : GebSList) ->
      TypecheckErrors l -> TypecheckErrors (x :: l)
    AdditionalError : (x : GebSExp) -> (l : GebSList) ->
      TypecheckError x -> TypecheckErrors l -> TypecheckErrors (x :: l)

public export
CompileResult : GebSExp -> Type
CompileResult x = Either (TypecheckSuccess x) (TypecheckError x)

public export
ListCompileResult : GebSList -> Type
ListCompileResult l = Either (TypecheckSuccessList l) (TypecheckErrors l)

public export
record SuccessIsCorrect (x : GebSExp) (i : TypecheckSuccess x) where
  constructor SuccessCorrectnessConditions
  TypecheckSuccessComplete : (i' : TypecheckSuccess x) -> i = i'
  TypecheckSuccessEnsuresNoError : (e : TypecheckError x) -> Void

public export
record FailureIsCorrect (x : GebSExp) (e : TypecheckError x) where
  constructor FailureCorrectnessConditions
  TypecheckErrorComplete : (e' : TypecheckError x) -> e = e'
  TypecheckErrorEnsuresNoSuccess : (i : TypecheckSuccess x) -> Void

public export
record ListSuccessIsCorrect (l : GebSList) (i : TypecheckSuccessList l) where
  constructor ListSuccessCorrectnessConditions
  ListTypecheckSuccessComplete : (i' : TypecheckSuccessList l) -> i = i'
  ListTypecheckSuccessEnsuresNoError : (le : TypecheckErrors l) -> Void

public export
record ListFailureIsCorrect (l : GebSList) (e : TypecheckErrors l) where
  constructor ListFailureCorrectnessConditions
  ListTypecheckErrorComplete : (e' : TypecheckErrors l) -> e = e'
  ListTypecheckErrorEnsuresNoSuccesses :
    (li : TypecheckSuccessList l) -> Void

public export
CorrectSuccess : GebSExp -> Type
CorrectSuccess x = Subset (TypecheckSuccess x) (SuccessIsCorrect x)

public export
CorrectListSuccess : GebSList -> Type
CorrectListSuccess l = Subset (TypecheckSuccessList l) (ListSuccessIsCorrect l)

public export
CorrectFailure : GebSExp -> Type
CorrectFailure x = Subset (TypecheckError x) (FailureIsCorrect x)

public export
CorrectListFailure : GebSList -> Type
CorrectListFailure l = Subset (TypecheckErrors l) (ListFailureIsCorrect l)

public export
CorrectCompilation : GebSExp -> Type
CorrectCompilation x = Either (CorrectSuccess x) (CorrectFailure x)

public export
CorrectListCompilation : GebSList -> Type
CorrectListCompilation l = Either (CorrectListSuccess l) (CorrectListFailure l)

public export
gebCompileCertifiedLeftElim :
  (a : GebAtom) -> (l : GebSList) ->
  Subset (TypecheckSuccessList l) (ListSuccessIsCorrect l) ->
  CorrectCompilation (a $* l)
gebCompileCertifiedLeftElim a l (Element li correct) =
  Right
    (Element (NewError a l li $ UnimplementedAtom a l li) $
     FailureCorrectnessConditions
      (\e' => case e' of
        NewError a' l' li' e'' =>
          rewrite ListTypecheckSuccessComplete correct li' in
          case e'' of
            UnimplementedAtom a'' l'' sl'' => Refl
        SubexpressionFailed a' l' le =>
          void (ListTypecheckSuccessEnsuresNoError correct le))
      (\i => case i of _ impossible)
    )

public export
gebCompileCertifiedRightElim :
  (a : GebAtom) -> (l : GebSList) ->
  Subset (TypecheckErrors l) (ListFailureIsCorrect l) ->
  Subset (TypecheckError (a $* l)) (FailureIsCorrect (a $* l))
gebCompileCertifiedRightElim a l (Element le correct) =
  (Element (SubexpressionFailed a l le) $
   FailureCorrectnessConditions
    (\e' => case e' of
      NewError a' l' le' _ =>
        void $ ListTypecheckErrorEnsuresNoSuccesses correct le'
      SubexpressionFailed a' l' le' =>
        rewrite ListTypecheckErrorComplete correct le' in Refl)
    (\i => case i of _ impossible)
  )

public export
gebCompileNilElim : CorrectListCompilation []
gebCompileNilElim =
  Left
    (Element EmptySuccessList $
     ListSuccessCorrectnessConditions
      (\li => case li of EmptySuccessList => Refl)
      (\le => case le of _ impossible)
    )

public export
gebCompileCertifiedConsLeftLeft :
  (x : GebSExp) -> (l : GebSList) ->
  Subset (TypecheckSuccess x) (SuccessIsCorrect x) ->
  Subset (TypecheckSuccessList l) (ListSuccessIsCorrect l) ->
  CorrectListCompilation (x :: l)
gebCompileCertifiedConsLeftLeft x l
  (Element i expCorrect) (Element li listCorrect) =
    Left $ Element (SuccessListCons x l i li)
      (ListSuccessCorrectnessConditions
        (\sl => case sl of
          EmptySuccessList impossible
          SuccessListCons x' l' i' li' =>
            rewrite TypecheckSuccessComplete expCorrect i' in
            rewrite ListTypecheckSuccessComplete listCorrect li' in
            Refl)
        (\le => case le of
          FirstError _ _ e'' _ =>
            void $ TypecheckSuccessEnsuresNoError expCorrect e''
          NoNewError _ _ li' =>
            void $ ListTypecheckSuccessEnsuresNoError listCorrect li'
          AdditionalError _ _ e'' _ =>
            void $ TypecheckSuccessEnsuresNoError expCorrect e''))

public export
gebCompileCertifiedConsLeftRight :
  (x : GebSExp) -> (l : GebSList) ->
  Subset (TypecheckSuccess x) (SuccessIsCorrect x) ->
  Subset (TypecheckErrors l) (ListFailureIsCorrect l) ->
  Subset (TypecheckErrors (x :: l)) (ListFailureIsCorrect (x :: l))
gebCompileCertifiedConsLeftRight x l
  (Element i expCorrect) (Element le listCorrect) =
  (Element (NoNewError x l le) $
    ListFailureCorrectnessConditions
      (\e' => case e' of
        FirstError _ _ e'' li' =>
          void $ ListTypecheckErrorEnsuresNoSuccesses listCorrect li'
        NoNewError _ _ li' =>
          rewrite ListTypecheckErrorComplete listCorrect li' in
          Refl
        AdditionalError _ _ e'' _ =>
          void $ TypecheckSuccessEnsuresNoError expCorrect e'')
      (\xls => case xls of
        SuccessListCons _ _ xs ls =>
          void $ ListTypecheckErrorEnsuresNoSuccesses listCorrect ls))

public export
gebCompileCertifiedConsRightLeft :
  (x : GebSExp) -> (l : GebSList) ->
  Subset (TypecheckError x) (FailureIsCorrect x) ->
  Subset (TypecheckSuccessList l) (ListSuccessIsCorrect l) ->
  Subset (TypecheckErrors (x :: l)) (ListFailureIsCorrect (x :: l))
gebCompileCertifiedConsRightLeft x l
  (Element e expCorrect) (Element li listCorrect) =
    (Element (FirstError x l e li) $
    ListFailureCorrectnessConditions
      (\e' => case e' of
        FirstError _ _ e'' li' =>
          rewrite TypecheckErrorComplete expCorrect e'' in
          rewrite ListTypecheckSuccessComplete listCorrect li' in
          Refl
        NoNewError _ _ li' =>
          void $ ListTypecheckSuccessEnsuresNoError listCorrect li'
        AdditionalError _ _ e'' li' =>
          void $ ListTypecheckSuccessEnsuresNoError listCorrect li')
      (\xls => case xls of
        SuccessListCons _ _ xs ls =>
          void $ TypecheckErrorEnsuresNoSuccess expCorrect xs))

public export
gebCompileCertifiedConsRightRight :
  (x : GebSExp) -> (l : GebSList) ->
  Subset (TypecheckError x) (FailureIsCorrect x) ->
  Subset (TypecheckErrors l) (ListFailureIsCorrect l) ->
  Subset (TypecheckErrors (x :: l)) (ListFailureIsCorrect (x :: l))
gebCompileCertifiedConsRightRight x l
  (Element e expCorrect) (Element le listCorrect) =
  (Element (AdditionalError x l e le) $
    ?gebCompileCertifiedConsRightRight_hole)

public export
GebCompileSignature :
  SExpEitherInductionSig
    Prelude.Basics.id
    CorrectSuccess
    CorrectFailure
    CorrectListSuccess
    CorrectListFailure
GebCompileSignature =
  SExpEitherInductionArgs
    gebCompileCertifiedLeftElim
    gebCompileCertifiedRightElim
    gebCompileNilElim
    gebCompileCertifiedConsLeftLeft
    gebCompileCertifiedConsLeftRight
    gebCompileCertifiedConsRightLeft
    gebCompileCertifiedConsRightRight

public export
gebCompileCertified : GebSExp ~> CorrectCompilation
gebCompileCertified =
  sexpEitherInduction {mMonad=IdentityIsMonad} GebCompileSignature

public export
gebCompile : GebSExp ~> CompileResult
gebCompile x with (gebCompileCertified x)
  gebCompile x | Left (Element i _) = Left i
  gebCompile x | Right (Element e _) = Right e

public export
gebCompileCorrect :
  (x : GebSExp) -> case gebCompile x of
    Left i => CorrectSuccess x
    Right e => CorrectFailure x
gebCompileCorrect x with (gebCompileCertified x)
  gebCompileCorrect x | (Left (Element i correct)) = Element i correct
  gebCompileCorrect x | (Right (Element e correct)) = Element e correct

public export
compileSuccessComplete : (x : GebSExp) -> (i : TypecheckSuccess x) ->
  gebCompile x = Left i
compileSuccessComplete x i with (gebCompileCertified x)
  compileSuccessComplete _ i' | (Left (Element _ correct)) =
    rewrite TypecheckSuccessComplete correct i' in Refl
  compileSuccessComplete _ i' | (Right (Element _ correct)) =
    void $ TypecheckErrorEnsuresNoSuccess correct i'

public export
idrisInterpretationUnique : (x : GebSExp) -> (i, i' : TypecheckSuccess x) ->
  i = i'
idrisInterpretationUnique x i i' =
  case
    trans
    (sym $ compileSuccessComplete x i)
    (compileSuccessComplete x i') of
      Refl => Refl

public export
typecheckErrorComplete : (x : GebSExp) -> (0 e : TypecheckError x) ->
  gebCompile x = Right e
typecheckErrorComplete x e with (gebCompileCertified x)
  typecheckErrorComplete _ e' | (Left (Element _ correct)) =
    void $ TypecheckSuccessEnsuresNoError correct e'
  typecheckErrorComplete _ e' | (Right (Element _ correct)) =
    rewrite TypecheckErrorComplete correct e' in Refl

public export
typecheckErrorUnique : (x : GebSExp) -> (e, e' : TypecheckError x) ->
  e = e'
typecheckErrorUnique x e e' =
  case
    trans
    (sym $ typecheckErrorComplete x e)
    (typecheckErrorComplete x e') of
      Refl => Refl

public export
compileSuccessAndTypecheckErrorMutuallyExclusive : (x : GebSExp) ->
  (i : TypecheckSuccess x) -> (e : TypecheckError x) -> Void
compileSuccessAndTypecheckErrorMutuallyExclusive x i e =
  case
    trans
    (sym $ compileSuccessComplete x i)
    (typecheckErrorComplete x e) of
      Refl impossible

public export
AnyErased : Type
AnyErased = Exists {type=Type} id

public export
idrisInterpretExpElim : (a : GebAtom) -> (l : GebSList) ->
  (TypecheckSuccessList l -> List AnyErased) ->
  TypecheckSuccess (a $* l) ->
  AnyErased
idrisInterpretExpElim a l li i = case li of _ impossible

public export
idrisInterpretNilElim : TypecheckSuccessList [] -> List AnyErased
idrisInterpretNilElim EmptySuccessList = []

public export
idrisInterpretConsElim : (x : GebSExp) -> (l : GebSList) ->
  (TypecheckSuccess x -> AnyErased) ->
  (TypecheckSuccessList l -> List AnyErased) ->
  TypecheckSuccessList (x :: l) ->
  List AnyErased
idrisInterpretConsElim x l i li (SuccessListCons _ _ sx sl) = i sx :: li sl

public export
idrisInterpretations :
  ((x : GebSExp) -> TypecheckSuccess x -> AnyErased,
   (l : GebSList) -> TypecheckSuccessList l -> List AnyErased)
idrisInterpretations =
  sexpEliminators
    {sp=(\x => TypecheckSuccess x -> AnyErased)}
    {lp=(\l => TypecheckSuccessList l -> List AnyErased)}
    $ SExpEliminatorArgs
      idrisInterpretExpElim
      idrisInterpretNilElim
      idrisInterpretConsElim

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
  objectUnique obj obj' = ?objectUnique_hole

  public export
  checkExpression : (expression : GebSExp) -> (refinement : GebSList) ->
    Dec $ Expression expression refinement
  checkExpression x r = ?checkExpression_hole

  public export
  checkExpressionCorrect : {x : GebSExp} -> {l : GebSList} ->
    (exp : Expression x l) -> checkExpression x l = Yes exp
  checkExpressionCorrect {x} {l} exp = ?checkExpressionCorrect_hole

  public export
  expressionUnique : {x : GebSExp} -> {l : GebSList} ->
    (exp, exp' : Expression x l) -> exp = exp'
  expressionUnique {x} {l} exp exp' = ?expressionUnique_hole

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
  interpretMorphism m = ?interpretMorphism_hole

  public export
  interpretRefinement : {s, r : GebSExp} ->
    Refinement r [s] -> (GebSExp -> Bool)
  interpretRefinement {s} {r} isRefinement x = ?interpretRefinement_hole

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
termSortToExp sort = ?termSortToExp_hole

public export
termToExp : {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  {numApplications : Nat} -> {sort : TermSort isLanguage} ->
  Term numApplications sort -> GebSExp
termToExp term = ?termToExp_hole

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
interpretTerm term = ?interpretTerm_hole

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
smallStepMorphismReduction = ?smallStepMorphismReduction_hole

public export
smallStepTermReduction : {lang : GebSExp} ->
  {auto isLanguage : Language lang []} ->
  {sort : TermSort isLanguage} -> {numApplications : Nat} ->
  Term numApplications sort ->
  (remainingApplications : Nat ** Term remainingApplications sort)
smallStepTermReduction = ?smallStepTermReduction_hole

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
  ?smallStepTermReductionCompletes_hole

public export
smallStepTermReductionCorrect :
  {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
  {isNormalizing : IsNormalizing isLanguage} ->
  {sort : TermSort isLanguage} -> {numApplications : Nat} ->
  (term : Term numApplications sort) ->
  interpretTerm (fst (smallStepTermReductionCompletes {isNormalizing} term)) =
    interpretTerm term
smallStepTermReductionCorrect term = ?smallStepTermReductionCorrect_hole
