module Executable.Test.Main

import RefinedSExp.Test.TestLibrary
import RefinedSExp.Test.ListTest
import RefinedSExp.Test.RefinedListTest
import RefinedSExp.Test.SExpTest
import RefinedSExp.Test.RefinedSExpTest
import RefinedSExp.Test.OldSExpTest
import RefinedSExp.Test.ADTTest
import RefinedSExp.New.Test.TestLibrary
import RefinedSExp.New.Test.ListTest
import RefinedSExp.New.Test.RefinedListTest
import RefinedSExp.New.Test.SExpTest
import RefinedSExp.New.Test.RefinedSExpTest

%default total

main : IO ()
main = do
  RefinedSExp.Test.ListTest.listTests
  RefinedSExp.Test.RefinedListTest.refinedListTests
  RefinedSExp.Test.SExpTest.sExpTests
  RefinedSExp.Test.RefinedSExpTest.refinedSExpTests
  RefinedSExp.New.Test.ListTest.listTests
  RefinedSExp.New.Test.RefinedListTest.refinedListTests
  RefinedSExp.New.Test.SExpTest.sExpTests
  RefinedSExp.New.Test.RefinedSExpTest.refinedSExpTests
