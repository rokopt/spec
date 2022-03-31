module Executable.Test.Main

import Library.Test.IdrisUtilsTest
import Test.TestLibrary
import LanguageDef.Test.AtomTest
import LanguageDef.Test.TermTest
import LanguageDef.Test.ExpressionTest
import LanguageDef.Test.FoundationalTheoryTest
import LanguageDef.Test.InterpretationTest
import LanguageDef.Test.SyntaxTest
import LanguageDef.Test.MetaprogrammingTest
import LanguageDef.Test.LogicTest
import LanguageDef.Test.ComputationalEffectsTest
import LanguageDef.Test.EmbeddedTest
import Library.Test.IdrisCategoriesTest
import Library.Test.CategoryTheoryTest

%default total

export
main : IO ()
main = do
  Library.Test.IdrisUtilsTest.idrisUtilsTest
  Test.TestLibrary.testLibraryTest
  LanguageDef.Test.AtomTest.languageDefAtomTest
  LanguageDef.Test.TermTest.languageDefTermTest
  LanguageDef.Test.ExpressionTest.languageDefExpressionTest
  LanguageDef.Test.FoundationalTheoryTest.languageDefFoundationalTheoryTest
  LanguageDef.Test.InterpretationTest.languageDefInterpretationTest
  LanguageDef.Test.SyntaxTest.languageDefSyntaxTest
  LanguageDef.Test.MetaprogrammingTest.languageDefMetaprogrammingTest
  LanguageDef.Test.LogicTest.languageDefLogicTest
  LanguageDef.Test.ComputationalEffectsTest.languageDefComputationalEffectsTest
  LanguageDef.Test.EmbeddedTest.languageDefEmbeddedTest
  Library.Test.IdrisCategoriesTest.libraryIdrisCategoriesTest
  Library.Test.CategoryTheoryTest.libraryCategoryTheoryTest
