module Geb.Test.GebTest

import public Library.Test.TestLibrary
import public Geb.Geb

%default total

zerothOrderExp : GebSExp
zerothOrderExp = GAFiniteOrder $**^ GAIndexFirst

zerothOrder : GebOrder GebTest.zerothOrderExp
zerothOrder = compileOrder zerothOrderExp

emptyTypeListExp : GebSExp
emptyTypeListExp = $^ GATypeList

emptyTypeList : GebPTypeList GebTest.zerothOrder GebTest.emptyTypeListExp
emptyTypeList = compileTypeList zerothOrderExp emptyTypeListExp

emptyTypeMatrixExp : GebSExp
emptyTypeMatrixExp = $^ GATypeMatrix

emptyTypeMatrix : GebPTypeMatrix GebTest.zerothOrder GebTest.emptyTypeMatrixExp
emptyTypeMatrix = compileTypeMatrix zerothOrderExp emptyTypeMatrixExp

voidTypeExp : GebSExp
voidTypeExp = GAPatternType $*** emptyTypeMatrixExp

voidType : GebPType GebTest.zerothOrder GebTest.voidTypeExp
voidType = compileType zerothOrderExp voidTypeExp

singletonTypeMatrixExp : GebSExp
singletonTypeMatrixExp = GATypeMatrix $*** emptyTypeListExp

singletonTypeMatrix : GebPTypeMatrix
  GebTest.zerothOrder GebTest.singletonTypeMatrixExp
singletonTypeMatrix = compileTypeMatrix zerothOrderExp singletonTypeMatrixExp

unitTypeExp : GebSExp
unitTypeExp = GAPatternType $*** singletonTypeMatrixExp

unitType : GebPType GebTest.zerothOrder GebTest.unitTypeExp
unitType = compileType zerothOrderExp unitTypeExp

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

boolTypeMatrix : GebPTypeMatrix GebTest.zerothOrder GebTest.boolTypeMatrixExp
boolTypeMatrix = compileTypeMatrix zerothOrderExp boolTypeMatrixExp

boolTypeExp : GebSExp
boolTypeExp = GAPatternType $*** boolTypeMatrixExp

boolType : GebPType GebTest.zerothOrder GebTest.boolTypeExp
boolType = compileType zerothOrderExp boolTypeExp

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

pairBoolTypeMatrix :
  GebPTypeMatrix GebTest.zerothOrder GebTest.pairBoolTypeMatrixExp
pairBoolTypeMatrix = compileTypeMatrix zerothOrderExp pairBoolTypeMatrixExp

pairBoolTypeExp : GebSExp
pairBoolTypeExp = GAPatternType $*** pairBoolTypeMatrixExp

pairBoolType : GebPType GebTest.zerothOrder GebTest.pairBoolTypeExp
pairBoolType = compileType zerothOrderExp pairBoolTypeExp

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
