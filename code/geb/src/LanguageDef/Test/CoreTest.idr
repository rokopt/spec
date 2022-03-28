module LanguageDef.Test.CoreTest

import Test.TestLibrary
import LanguageDef.Core

%default total

export
languageDefCoreTest : IO ()
languageDefCoreTest = do
  printLn "Begin languageDefCoreTest:"
  printLn "End languageDefCoreTest."
  pure ()
