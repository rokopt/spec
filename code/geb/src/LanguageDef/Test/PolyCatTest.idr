module LanguageDef.Test.PolyCatTest

import Test.TestLibrary
import LanguageDef.PolyCat

%default total

testBN0 : BoundedNat 7
testBN0 = MkBoundedNat 5

export
polyCatTest : IO ()
polyCatTest = do
  putStrLn "=================="
  printLn "Begin polyCatTest:"
  putStrLn ""
  printLn "---- BoundedNat ----"
  printLn $ show testBN0
  printLn ""
  printLn "End polyCatTest."
  printLn "=================="
  pure ()
