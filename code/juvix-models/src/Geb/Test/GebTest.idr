module Geb.Test.GebTest

import public Library.Test.TestLibrary
import public Geb.Geb

%default total

{-
unitPair : MinimalTerm 0 (MinimalTypeTerm (Product Terminal Terminal))
unitPair = PairTerm UnitTerm UnitTerm

backAndForth : String
backAndForth = case (gebExpToMinimalTerm $ gebMinimalTermToExp unitPair) of
  Just term => "Just " ++ show (snd term)
  Nothing => "Nothing"

public export
GebCategoryObjects : ObjectMap GebAtom
GebCategoryObjects =
  fromList [
      (GAInitial, 0)
    , (GATerminal, 0)
    , (GAProduct, 2)
    , (GACoproduct, 2)
    , (GAObjectExpression, 0)
  ]

public export
GebCategoryMorphisms : MorphismMap GebAtom
GebCategoryMorphisms = fromList []

public export
GebCategoryGenerator : SCategoryGenerator GebAtom
GebCategoryGenerator =
  SCategoryArgs
    GAIdentity
    GACompose
    GebCategoryObjects
    GebCategoryMorphisms

public export
GebObjectArity : SortArity GebAtom
GebObjectArity = empty

public export
GebMorphismArity : SortArity GebAtom
GebMorphismArity = [$^ GAObject, $^ GAObject]

public export
GebAlgebraArity : AlgebraArity GebAtom
GebAlgebraArity = fromList
  [
    (GAObject, GebObjectArity)
  , (GAMorphism, GebMorphismArity)
  ]

public export
GebInitialConstructor : SExpConstructor GebAtom
GebInitialConstructor = ([], [])

public export
GebTerminalConstructor : SExpConstructor GebAtom
GebTerminalConstructor = ([], [])

public export
GAlgAtom : Type
GAlgAtom = SAlgAtom GebAtom

public export
GAlgExp : Type
GAlgExp = SAlgExp GebAtom

public export
GAlgList : Type
GAlgList = SAlgList GebAtom

public export
GAlgObject : GAlgAtom
GAlgObject = SACustom GAObject

public export
GebObjectArgument : GAlgExp
GebObjectArgument = $^ GAlgObject

public export
GebTwoObjectArgConstructor : SExpConstructor GebAtom
GebTwoObjectArgConstructor = ([], [GebObjectArgument, GebObjectArgument])

public export
GebProductConstructor : SExpConstructor GebAtom
GebProductConstructor = GebTwoObjectArgConstructor

public export
GebCoproductConstructor : SExpConstructor GebAtom
GebCoproductConstructor = GebTwoObjectArgConstructor

public export
GebObjectConstructorMap : SExpConstructorMap GebAtom
GebObjectConstructorMap = fromList
  [
    (GAInitial, GebInitialConstructor)
  , (GATerminal, GebTerminalConstructor)
  , (GAProduct, GebProductConstructor)
  , (GACoproduct, GebProductConstructor)
  ]

public export
GebObjectSortConstructor : SortConstructor GebAtom
GebObjectSortConstructor = SortSignature [] GebObjectConstructorMap

public export
GAlgMorphism : GAlgAtom
GAlgMorphism = SACustom GAMorphism

public export
GebMorphismArgument : GAlgExp -> GAlgExp -> GAlgExp
GebMorphismArgument domain codomain = GAlgMorphism $* [domain, codomain]

public export
GebIdentityConstructor : SExpConstructor GebAtom
GebIdentityConstructor =
  ([GebObjectArgument], [SExpConstructorArg 0, SExpConstructorArg 0])

public export
GebComposeConstructor : SExpConstructor GebAtom
GebComposeConstructor =
  ([GebObjectArgument, GebObjectArgument, GebObjectArgument,
    GebMorphismArgument (SExpConstructorArg 1) (SExpConstructorArg 2),
    GebMorphismArgument (SExpConstructorArg 0) (SExpConstructorArg 1)],
   [SExpConstructorArg 0, SExpConstructorArg 2])

public export
GebMorphismConstructorMap : SExpConstructorMap GebAtom
GebMorphismConstructorMap = fromList
  [
    (GAIdentity, GebIdentityConstructor)
  , (GACompose, GebComposeConstructor)
  ]

public export
GebMorphismSortConstructor : SortConstructor GebAtom
GebMorphismSortConstructor =
  SortSignature [GebObjectArgument, GebObjectArgument] GebMorphismConstructorMap

public export
GebSortConstructors : SortConstructors GebAtom
GebSortConstructors = fromList
  [
    (GAObject, GebObjectSortConstructor)
  , (GAMorphism, GebMorphismSortConstructor)
  ]

public export
GebAlgebra : SExpAlgebra GebAtom
GebAlgebra = SExpAlgebraSignature
  []
  GebAlgebraArity
  GebSortConstructors

-}

export
gebTests : IO ()
gebTests = do
  printLn "Begin gebTests:"
  {-
  printLn $ "unitPair=" ++ show unitPair
  printLn $ "backandforth=" ++ backAndForth
  printLn $ "lookup=" ++ show (lookup GAInitial GebCategoryObjects)
  printLn $ "sobject initial=" ++
    show (sobject GebCategoryGenerator ($^ GAInitial))
  printLn $ "sobject random=" ++
    show (sobject GebCategoryGenerator ($^ GALanguage))
  printLn $ "sobject too many params=" ++
    show (sobject GebCategoryGenerator (GALanguage $* [$^ GAInitial]))
  printLn $ "product void/unit=" ++
    show (sobject GebCategoryGenerator
      (GAProduct $* [$^ GAInitial, $^ GATerminal]))
  printLn $ "coproduct of a couple products=" ++
    show (sobject GebCategoryGenerator
      (GACoproduct $*
          [GAProduct $* [$^ GAInitial, $^ GATerminal]
        ,  GAProduct $*
             [GACoproduct $* [$^ GATerminal, $^ GAObjectExpression]
             , $^ GATerminal]]))
  printLn $ "again with a wrong parameter count=" ++
    show (sobject GebCategoryGenerator
      (GACoproduct $*
          [GAProduct $* [$^ GAInitial, $^ GATerminal]
        ,  GAProduct $*
             [GACoproduct $* [$^ GATerminal, GAObjectExpression $*
              [$^ GAObjectExpression]]
             , $^ GATerminal]]))
  -}
  printLn "End gebTests."
  pure ()
