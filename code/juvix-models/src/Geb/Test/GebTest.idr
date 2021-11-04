module Geb.Test.GebTest

import public Library.Test.TestLibrary
import public Geb.Geb

%default total

emptyTypeListExp : GebSExp
emptyTypeListExp = $^ GATypeList

emptyTypeList : GebTypeList GebTest.emptyTypeListExp
emptyTypeList = IsJustElim {m=(checkTypeList [])} ItIsJust

singletonTypeMatrixList : GebSList
singletonTypeMatrixList = [emptyTypeListExp]

singletonTypeMatrixExp : GebSExp
singletonTypeMatrixExp = GATypeMatrix $* singletonTypeMatrixList

singletonTypeMatrix : GebTypeMatrix GebTest.singletonTypeMatrixExp
singletonTypeMatrix =
  IsJustElim {m=(checkTypeMatrix singletonTypeMatrixList)} ItIsJust

export
gebTests : IO ()
gebTests = do
  printLn "Begin gebTests:"
  printLn $ "Empty type list = " ++ showTypeList emptyTypeList
  printLn $ "Singleton type matrix = " ++ showTypeMatrix singletonTypeMatrix
  printLn "End gebTests."
  pure ()
