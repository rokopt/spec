module RefinedSExp.Test.AlgebraicSExpInterpretationTest

import public RefinedSExp.AlgebraicSExpInterpretation
import RefinedSExp.Test.AlgebraicSExpTest
import Library.Test.TestLibrary
import Data.Vect

%default total

public export
VectTypeFamily : Type -> TypeFamily
VectTypeFamily a = (Nat ** flip Vect a)

export
algebraicSExpInterpretationTests : IO ()
algebraicSExpInterpretationTests = pure ()
