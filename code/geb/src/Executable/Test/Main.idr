module Executable.Test.Main

import LanguageDef.Test.CoreTest
import Library.Test.IdrisUtilsTest
import Test.TestLibrary

%default total

export
main : IO ()
main = do
  LanguageDef.Test.CoreTest.languageDefCoreTest
  Library.Test.IdrisUtilsTest.idrisUtilsTest
  Test.TestLibrary.testLibraryTest
