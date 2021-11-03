module Geb.GebAtom

import Library.FunctionsAndRelations
import Library.Decidability
import public RefinedSExp.SExp
import public Data.SortedSet
import public Data.SortedMap

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

  GAAtomObject : GebAtom
  GASExpObject : GebAtom
  GASListObject : GebAtom
  GAContext : GebAtom
  GAParameterizedContext : GebAtom
  GAMaybeFunctor : GebAtom
  GAObjectReflection : GebAtom
  GAMorphismReflection : GebAtom

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
  GATypecheckObjectElim : GebAtom

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
gaEncode GAAtomObject = 50
gaEncode GASExpObject = 51
gaEncode GASListObject = 52
gaEncode GAContext = 53
gaEncode GAMaybeFunctor = 54
gaEncode GAParameterizedContext = 55
gaEncode GAObjectReflection = 56
gaEncode GAMorphismReflection = 57
gaEncode GATypecheckObjectElim = 58

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
gaDecode 50 = Just GAAtomObject
gaDecode 51 = Just GASExpObject
gaDecode 52 = Just GASListObject
gaDecode 53 = Just GAContext
gaDecode 54 = Just GAMaybeFunctor
gaDecode 55 = Just GAParameterizedContext
gaDecode 56 = Just GAObjectReflection
gaDecode 57 = Just GAMorphismReflection
gaDecode 58 = Just GATypecheckObjectElim
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
gaDecodeEncodeIsJust GAAtomObject = Refl
gaDecodeEncodeIsJust GASExpObject = Refl
gaDecodeEncodeIsJust GASListObject = Refl
gaDecodeEncodeIsJust GAContext = Refl
gaDecodeEncodeIsJust GAMaybeFunctor = Refl
gaDecodeEncodeIsJust GAParameterizedContext = Refl
gaDecodeEncodeIsJust GAObjectReflection = Refl
gaDecodeEncodeIsJust GAMorphismReflection = Refl
gaDecodeEncodeIsJust GATypecheckObjectElim = Refl

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
gebAtomToString GAAtomObject = "AtomObject"
gebAtomToString GASExpObject = "SExpObject"
gebAtomToString GASListObject = "ListObject"
gebAtomToString GAContext = "Context"
gebAtomToString GAMaybeFunctor = "MaybeFunctor"
gebAtomToString GAParameterizedContext = "ParameterizedContext"
gebAtomToString GAObjectReflection = "ObjectReflection"
gebAtomToString GAMorphismReflection = "MorphismReflection"
gebAtomToString GATypecheckObjectElim = "TypecheckObjectElim"

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
gebSExpShow : GebSExp -> String
gebSExpShow = show

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
