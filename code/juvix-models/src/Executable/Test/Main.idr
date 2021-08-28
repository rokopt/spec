module Executable.Test.Main

import Library.Test.TestLibrary
import RefinedSExp.Test.ListTest
import RefinedSExp.Test.SExpTest
import RefinedSExp.Test.SExpApplicativesTest
import RefinedSExp.Test.RefinedSExpTest
import Datatypes.Test.AlgebraicTypesTest
import Datatypes.Test.DatatypesTest
import Datatypes.Test.InductiveDatatypesTest
import Datatypes.Test.DependentAlgebraicTypesTest
import Datatypes.Test.DependentInductiveDatatypesTest
import Theories.Test.AlgebraicTheoryTest
import Theories.Test.DependentAlgebraicTheoryTest
import Theories.Test.HigherOrderRecursionTest
import Theories.Test.InductiveTypeTheoryTest
import Theories.Test.DependentInductiveTypeTheoryTest
import RefinedSExp.Old.Test.TestLibrary
import RefinedSExp.Old.Test.ListTest
import RefinedSExp.Old.Test.RefinedListTest
import RefinedSExp.Old.Test.SExpTest
import RefinedSExp.Old.Test.RefinedSExpTest
import RefinedSExp.Old.Test.OldSExpTest
import RefinedSExp.Old.Test.ADTTest
import RefinedSExp.ListVariant.Test.TestLibrary
import RefinedSExp.ListVariant.Test.ListTest
import RefinedSExp.ListVariant.Test.RefinedListTest
import RefinedSExp.ListVariant.Test.SExpTest
import RefinedSExp.ListVariant.Test.RefinedSExpTest
import ReflectiveLanguages.Test.SubstitutiveTest

%default total

main : IO ()
main = do
  RefinedSExp.Test.ListTest.listTests
  RefinedSExp.Test.SExpTest.sExpTests
  RefinedSExp.Test.SExpApplicativesTest.sExpApplicativesTests
  RefinedSExp.Test.RefinedSExpTest.refinedSExpTests
  Datatypes.Test.AlgebraicTypesTest.algebraicTypesTests
  Datatypes.Test.DatatypesTest.datatypesTests
  Datatypes.Test.InductiveDatatypesTest.inductiveDatatypesTests
  Datatypes.Test.DependentAlgebraicTypesTest.dependentAlgebraicTypesTests
  Datatypes.Test.DependentInductiveDatatypesTest.dependentInductiveDatatypesTests
  Theories.Test.AlgebraicTheoryTest.algebraicTheoryTests
  Theories.Test.DependentAlgebraicTheoryTest.dependentAlgebraicTheoryTests
  Theories.Test.HigherOrderRecursionTest.higherOrderRecursionTests
  Theories.Test.InductiveTypeTheoryTest.inductiveTypeTheoryTests
  Theories.Test.DependentInductiveTypeTheoryTest.dependentInductiveTypeTheoryTests
  RefinedSExp.Old.Test.ListTest.listTests
  RefinedSExp.Old.Test.RefinedListTest.refinedListTests
  RefinedSExp.Old.Test.SExpTest.sExpTests
  RefinedSExp.Old.Test.RefinedSExpTest.refinedSExpTests
  RefinedSExp.ListVariant.Test.ListTest.listTests
  RefinedSExp.ListVariant.Test.RefinedListTest.refinedListTests
  RefinedSExp.ListVariant.Test.SExpTest.sExpTests
  RefinedSExp.ListVariant.Test.RefinedSExpTest.refinedSExpTests
  ReflectiveLanguages.Test.SubstitutiveTest.substitutiveTests
