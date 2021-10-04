module RefinedSExp.Test.NamingTest

import public Library.Test.TestLibrary
import public RefinedSExp.Naming
import public RefinedSExp.Computation

%default total

public export
emptyContext : NamingContext Data CExp
emptyContext = ClosureMap empty

export
partial namingTests : IO ()
namingTests = do
  printLn "Begin namingTests:"
  printLn $ "The empty context looks like: " ++ show emptyContext
  printLn "End namingTests."
  pure ()
