module Executable.Test.Main

import RefinedSExp.Test.TestLibrary
import RefinedSExp.Test.ListTest
import RefinedSExp.Test.RefinedListTest
import RefinedSExp.Test.SExpTest
import RefinedSExp.Test.RefinedSExpTest
import RefinedSExp.Test.OldSExpTest
import RefinedSExp.Test.ADTTest

%default total

main : IO ()
main = do
  ListTest.listTests
  RefinedListTest.refinedListTests
  SExpTest.sExpTests
  RefinedSExpTest.refinedSExpTests
