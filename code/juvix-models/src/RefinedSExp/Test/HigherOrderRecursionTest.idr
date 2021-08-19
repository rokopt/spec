module RefinedSExp.Test.HigherOrderRecursionTest

import public RefinedSExp.HigherOrderRecursion
import public RefinedSExp.Test.InductiveDatatypesTest
import RefinedSExp.Test.TestLibrary
import Library.FunctionsAndRelations

%default total

public export
data HigherOrderType : (penv : PrimitiveEnv) -> Type where
  HigherOrderPrimitive :
    PrimType penv -> HigherOrderType penv
  HigherOrderFunction :
    (domain, codomain : HigherOrderType penv) -> HigherOrderType penv

public export
HigherOrderEnv : PrimitiveEnv -> PrimitiveEnv
HigherOrderEnv = PrimArgs . HigherOrderType

export
higherOrderRecursionTests : IO ()
higherOrderRecursionTests = pure ()
