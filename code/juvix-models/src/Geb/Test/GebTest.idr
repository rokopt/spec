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

export
gebTests : IO ()
gebTests = do
  printLn "Begin gebTests:"
  printLn "End gebTests."
  printLn $ "unitPair=" ++ show unitPair
  printLn $ "backandforth=" ++ backAndForth
  pure ()
