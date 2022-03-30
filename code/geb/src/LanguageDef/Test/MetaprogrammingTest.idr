module LanguageDef.Test.MetaprogrammingTest

import Test.TestLibrary
import LanguageDef.Metaprogramming

%default total

export
languageDefMetaprogrammingTest : IO ()
languageDefMetaprogrammingTest = do
  printLn "Begin languageDefMetaprogrammingTest:"
  printLn "End languageDefMetaprogrammingTest."
  pure ()
