module RefinedSExp.Test.RefinedSExpTest

import public RefinedSExp.RefinedSExp
import RefinedSExp.Test.SExpTest
import Library.Test.TestLibrary
import public Data.Vect
import public Data.Fin

%default total

public export
structListTest : StructList 3 2
structListTest =
  ($>) $: ($| (($| ($<+ 1 $: $<+0 $:- ($>))) $:- $<+ 2)) $:- $<+ 4

public export
structExpTest : StructExp 3 2
structExpTest = $| structListTest

public export
structNthTest : StructExp 4 1
structNthTest = structListTest $# 1

export
refinedSExpTests : IO ()
refinedSExpTests = pure ()
