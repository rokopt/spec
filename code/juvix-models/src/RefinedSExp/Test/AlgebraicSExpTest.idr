module RefinedSExp.Test.AlgebraicSExpTest

import Library.Test.TestLibrary
import public RefinedSExp.AlgebraicSExp

%default total

public export
sexpNotationTest : SExp Nat
sexpNotationTest = 0 $* (1 $* 2 $^: 3 $^: []) :: []

export
algebraicSExpTests : IO ()
algebraicSExpTests = pure ()
