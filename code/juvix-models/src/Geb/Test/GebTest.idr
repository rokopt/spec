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
    (GAInitial, 0),
    (GATerminal, 0)
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
  printLn "End gebTests."
  pure ()
