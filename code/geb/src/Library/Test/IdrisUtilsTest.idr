module Library.Test.IdrisUtilsTest

import Test.TestLibrary
import Library.IdrisUtils

%default total

export
idrisUtilsTest : IO ()
idrisUtilsTest = do
  printLn "Begin idrisUtilsTest:"
  printLn "End idrisUtilsTest."
  pure ()
