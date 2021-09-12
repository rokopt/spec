module RefinedSExp.Test.RefinedSExpTest

import public RefinedSExp.RefinedSExp
import RefinedSExp.Test.SExpTest
import Library.Test.TestLibrary
import public Data.Vect
import public Data.Fin

%default total

public export
structExpTest : StructExp 3 2
structExpTest =
  $| (($>) $: ($| (($| ($<+ 1 $: $<+0 $:- ($>))) $:- $<+ 2)) $:- $<+ 4)

export
refinedSExpTests : IO ()
refinedSExpTests = pure ()
