module Test.TestLibrary

import public Library.IdrisUtils

%default total

export
testLibraryTest : IO ()
testLibraryTest = do
  printLn "Begin testLibraryTest:"
  printLn "End testLibraryTest."
  pure ()
