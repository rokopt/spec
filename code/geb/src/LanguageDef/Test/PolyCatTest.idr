module LanguageDef.Test.PolyCatTest

import Test.TestLibrary
import LanguageDef.PolyCat

%default total

export
polyCatTest : IO ()
polyCatTest = do
  printLn "Begin polyCatTest:"
  printLn "End polyCatTest."
  pure ()
