module Test.TestLibrary

import public Library.IdrisUtils

%default total

public export
Assertion : Type
Assertion = ()

public export
Assert : (b : Bool) -> if b then () else List ()
Assert True = ()
Assert False = []

export
testLibraryTest : IO ()
testLibraryTest = do
  -- printLn "Begin testLibraryTest:"
  -- printLn "End testLibraryTest."
  pure ()
