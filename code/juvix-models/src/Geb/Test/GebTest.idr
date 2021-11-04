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

singletonTypeMatrixExp : GebSExp
singletonTypeMatrixExp = GATypeMatrix $*** emptyTypeListExp

singletonTypeMatrix : GebTypeMatrix GebTest.singletonTypeMatrixExp
singletonTypeMatrix = compileTypeMatrix singletonTypeMatrixExp

boolTypeMatrixExp : GebSExp
boolTypeMatrixExp = GATypeMatrix $* [emptyTypeListExp, emptyTypeListExp]

boolTypeMatrix : GebTypeMatrix GebTest.boolTypeMatrixExp
boolTypeMatrix = compileTypeMatrix boolTypeMatrixExp

boolTypeExp : GebSExp
boolTypeExp = GAPatternType $*** boolTypeMatrixExp

boolType : GebType GebTest.boolTypeExp
boolType = compileType boolTypeExp

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
