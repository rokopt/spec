module RefinedSExp.Test.NamingTest

import public Library.Test.TestLibrary
import public RefinedSExp.Naming
import public RefinedSExp.SExp
import public RefinedSExp.Data

%default total

public export
emptyContext : NamingContext Data (SExp Data)
emptyContext = ClosureMap empty

export
partial namingTests : IO ()
namingTests = do
  printLn "Begin namingTests:"
  printLn $ "The empty context looks like: " ++ show emptyContext
  printLn "End namingTests."
  pure ()
