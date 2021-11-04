module Geb.Test.GebTest

import public Library.Test.TestLibrary
import public Geb.Geb

%default total

emptyTypeListExp : GebSExp
emptyTypeListExp = $^ GATypeList

emptyTypeList : GebTypeList GebTest.emptyTypeListExp
emptyTypeList = IsJustElim {m=(checkTypeList [])} ItIsJust

emptyTypeMatrixList : GebSList
emptyTypeMatrixList = []

emptyTypeMatrixExp : GebSExp
emptyTypeMatrixExp = GATypeMatrix $* emptyTypeMatrixList

emptyTypeMatrix : GebTypeMatrix GebTest.emptyTypeMatrixExp
emptyTypeMatrix =
  IsJustElim {m=(checkTypeMatrix emptyTypeMatrixList)} ItIsJust

singletonTypeMatrixList : GebSList
singletonTypeMatrixList = [emptyTypeListExp]

singletonTypeMatrixExp : GebSExp
singletonTypeMatrixExp = GATypeMatrix $* singletonTypeMatrixList

singletonTypeMatrix : GebTypeMatrix GebTest.singletonTypeMatrixExp
singletonTypeMatrix =
  IsJustElim {m=(checkTypeMatrix singletonTypeMatrixList)} ItIsJust

boolTypeMatrixList : GebSList
boolTypeMatrixList = [emptyTypeListExp, emptyTypeListExp]

boolTypeMatrixExp : GebSExp
boolTypeMatrixExp = GATypeMatrix $* boolTypeMatrixList

boolTypeMatrix : GebTypeMatrix GebTest.boolTypeMatrixExp
boolTypeMatrix =
  IsJustElim {m=(checkTypeMatrix boolTypeMatrixList)} ItIsJust

boolPatternTypeExp : GebSExp
boolPatternTypeExp = GAPatternType $*** boolTypeMatrixExp

boolPatternType : GebType GebTest.boolPatternTypeExp
boolPatternType =
  IsJustElim {m=(checkType boolPatternTypeExp)} ItIsJust

pairBoolTypeList : GebSList
pairBoolTypeList = [boolPatternTypeExp, boolPatternTypeExp]

pairBoolTypeListExp : GebSExp
pairBoolTypeListExp = GATypeList $* pairBoolTypeList

pairBoolTypeMatrixList : GebSList
pairBoolTypeMatrixList = [pairBoolTypeListExp]

pairBoolTypeMatrixExp : GebSExp
pairBoolTypeMatrixExp = GATypeMatrix $* pairBoolTypeMatrixList

pairBoolTypeMatrix : GebTypeMatrix GebTest.pairBoolTypeMatrixExp
pairBoolTypeMatrix =
  IsJustElim {m=(checkTypeMatrix pairBoolTypeMatrixList)} ItIsJust

export
gebTests : IO ()
gebTests = do
  printLn "Begin gebTests:"
  printLn $ "Empty type list = " ++ showTypeList emptyTypeList
  printLn $ "Empty type matrix = " ++ showTypeMatrix emptyTypeMatrix
  printLn $ "Singleton type matrix = " ++ showTypeMatrix singletonTypeMatrix
  printLn $ "Bool type matrix = " ++ showTypeMatrix boolTypeMatrix
  printLn $ "Pair-of-bool type matrix = " ++ showTypeMatrix pairBoolTypeMatrix
  printLn "End gebTests."
  pure ()
