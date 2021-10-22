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
