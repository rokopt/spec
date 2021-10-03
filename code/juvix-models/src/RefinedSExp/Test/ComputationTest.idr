module RefinedSExp.Test.ComputationTest

import public Library.Test.TestLibrary
import public RefinedSExp.Computation

%default total

public export
computationNotationTest : DSExp
computationNotationTest =
  DANat 0 $* (DAKeyword Curry $* DAString "two" $^^ DANat 3) ::
    (DANat 4 $*** (DANat 5 $* (DANat 6 $*** (DAString "seven" $**^ DANat 8)) $:^
      DAReflectedKeyword Cofix)) $:^ DANat 10

public export
emptyContext : NamingContext Data DSExp
emptyContext = ClosureMap empty

export
partial computationTests : IO ()
computationTests = do
  printLn "Begin computationTests:"
  printLn $ show computationNotationTest
  printLn $ "The empty context looks like: " ++ show emptyContext
  printLn "End computationTests."
  pure ()
