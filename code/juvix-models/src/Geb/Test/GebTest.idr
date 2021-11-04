module Geb.Test.GebTest

import public Library.Test.TestLibrary
import public Geb.Geb

%default total

emptyTypeListExp : GebSExp
emptyTypeListExp = $^ GATypeList

emptyTypeList : GebTypeList GebTest.emptyTypeListExp
emptyTypeList = compileTypeList emptyTypeListExp

emptyTypeMatrixExp : GebSExp
emptyTypeMatrixExp = $^ GATypeMatrix

emptyTypeMatrix : GebTypeMatrix GebTest.emptyTypeMatrixExp
emptyTypeMatrix = compileTypeMatrix emptyTypeMatrixExp

voidTypeExp : GebSExp
voidTypeExp = GAPatternType $*** emptyTypeMatrixExp

voidType : GebType GebTest.voidTypeExp
voidType = compileType voidTypeExp

singletonTypeMatrixExp : GebSExp
singletonTypeMatrixExp = GATypeMatrix $*** emptyTypeListExp

singletonTypeMatrix : GebTypeMatrix GebTest.singletonTypeMatrixExp
singletonTypeMatrix = compileTypeMatrix singletonTypeMatrixExp

unitTypeExp : GebSExp
unitTypeExp = GAPatternType $*** singletonTypeMatrixExp

unitType : GebType GebTest.unitTypeExp
unitType = compileType unitTypeExp

unitTermIndexExp : GebSExp
unitTermIndexExp = gebMatrixIndexExp 0

unitTermExp : GebSExp
unitTermExp = GAInjectTerm $* [unitTermIndexExp, $^ GATermList]

unitTerm : GebTerm GebTest.unitType GebTest.unitTermExp
unitTerm = compileTerm unitType unitTermExp

unitTypeListExp : GebSExp
unitTypeListExp = GATypeList $*** unitTypeExp

boolTypeMatrixExp : GebSExp
boolTypeMatrixExp = GATypeMatrix $* [unitTypeListExp, unitTypeListExp]

boolTypeMatrix : GebTypeMatrix GebTest.boolTypeMatrixExp
boolTypeMatrix = compileTypeMatrix boolTypeMatrixExp

boolTypeExp : GebSExp
boolTypeExp = GAPatternType $*** boolTypeMatrixExp

boolType : GebType GebTest.boolTypeExp
boolType = compileType boolTypeExp

unitTermList : GebSExp
unitTermList = GATermList $* [unitTermExp]

falseTermIndexExp : GebSExp
falseTermIndexExp = gebMatrixIndexExp 0

trueTermIndexExp : GebSExp
trueTermIndexExp = gebMatrixIndexExp 1

falseTermIndex : GebMatrixIndex GebTest.boolTypeMatrix (gebMatrixIndexExp 0)
falseTermIndex = compileMatrixIndex boolTypeMatrix (gebMatrixIndexExp 0)

falseTermExp : GebSExp
falseTermExp = GAInjectTerm $* [falseTermIndexExp, unitTermList]

trueTermExp : GebSExp
trueTermExp = GAInjectTerm $* [trueTermIndexExp, unitTermList]

falseTerm : GebTerm GebTest.boolType GebTest.falseTermExp
falseTerm = compileTerm boolType falseTermExp

trueTerm : GebTerm GebTest.boolType GebTest.trueTermExp
trueTerm = compileTerm boolType trueTermExp

pairBoolTypeListExp : GebSExp
pairBoolTypeListExp = GATypeList $* [boolTypeExp, boolTypeExp]

pairBoolTypeMatrixExp : GebSExp
pairBoolTypeMatrixExp = GATypeMatrix $*** pairBoolTypeListExp

pairBoolTypeMatrix : GebTypeMatrix GebTest.pairBoolTypeMatrixExp
pairBoolTypeMatrix = compileTypeMatrix pairBoolTypeMatrixExp

pairBoolTypeExp : GebSExp
pairBoolTypeExp = GAPatternType $*** pairBoolTypeMatrixExp

pairBoolType : GebType GebTest.pairBoolTypeExp
pairBoolType = compileType pairBoolTypeExp

export
gebTests : IO ()
gebTests = do
  printLn "Begin gebTests:"
  printLn $ "Empty type list = " ++ showTypeList emptyTypeList
  printLn $ "Empty type matrix = " ++ showTypeMatrix emptyTypeMatrix
  printLn $ "Singleton type matrix = " ++ showTypeMatrix singletonTypeMatrix
  printLn $ "Bool type matrix = " ++ showTypeMatrix boolTypeMatrix
  printLn $ "Pair-of-bool type matrix = " ++ showTypeMatrix pairBoolTypeMatrix
  printLn $ "Pair-of-bool type = " ++ showType pairBoolType
  printLn "End gebTests."
  pure ()
