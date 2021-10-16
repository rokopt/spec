module Geb.Test.GebTest

import public Library.Test.TestLibrary
import public Geb.Geb

%default total

export
gebTests : IO ()
gebTests = do
  printLn "Begin gebTests:"
  printLn "End gebTests."
  pure ()
