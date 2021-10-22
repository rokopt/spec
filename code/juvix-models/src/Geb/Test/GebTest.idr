module Geb.Test.GebTest

import public Library.Test.TestLibrary
import public Geb.Geb

%default total

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
    , (GAExpression, 0)
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

GebObjectSortConstructor : SortConstructor GebAtom
GebObjectSortConstructor = SortSignature [] GebObjectConstructorMap

public export
GebIdentityConstructor : SExpConstructor GebAtom
GebIdentityConstructor =
  ([GebObjectArgument, GebObjectArgument], [GebObjectArgument])

public export
GebMorphismConstructorMap : SExpConstructorMap GebAtom
GebMorphismConstructorMap = fromList
  [
    (GAIdentity, GebIdentityConstructor)
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

-- public export

export
gebTests : IO ()
gebTests = do
  printLn "Begin gebTests:"
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
             [GACoproduct $* [$^ GATerminal, $^ GAExpression]
             , $^ GATerminal]]))
  printLn $ "again with a wrong parameter count=" ++
    show (sobject GebCategoryGenerator
      (GACoproduct $*
          [GAProduct $* [$^ GAInitial, $^ GATerminal]
        ,  GAProduct $*
             [GACoproduct $* [$^ GATerminal, GAExpression $* [$^ GAExpression]]
             , $^ GATerminal]]))
  printLn "End gebTests."
  pure ()
