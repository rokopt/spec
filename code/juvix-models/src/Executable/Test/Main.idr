module Executable.Test.Main

import RefinedSExp.Old.Test.TestLibrary
import RefinedSExp.Old.Test.ListTest
import RefinedSExp.Old.Test.RefinedListTest
import RefinedSExp.Old.Test.SExpTest
import RefinedSExp.Old.Test.RefinedSExpTest
import RefinedSExp.Old.Test.OldSExpTest
import RefinedSExp.Old.Test.ADTTest
import RefinedSExp.New.Test.TestLibrary
import RefinedSExp.New.Test.ListTest
import RefinedSExp.New.Test.RefinedListTest
import RefinedSExp.New.Test.SExpTest
import RefinedSExp.New.Test.RefinedSExpTest

%default total

main : IO ()
main = do
  RefinedSExp.Old.Test.ListTest.listTests
  RefinedSExp.Old.Test.RefinedListTest.refinedListTests
  RefinedSExp.Old.Test.SExpTest.sExpTests
  RefinedSExp.Old.Test.RefinedSExpTest.refinedSExpTests
  RefinedSExp.New.Test.ListTest.listTests
  RefinedSExp.New.Test.RefinedListTest.refinedListTests
  RefinedSExp.New.Test.SExpTest.sExpTests
  RefinedSExp.New.Test.RefinedSExpTest.refinedSExpTests
