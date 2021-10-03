module RefinedSExp.Test.ComputationTest

import public Library.Test.TestLibrary
import public RefinedSExp.Computation

%default total

public export
computationNotationTest : NamedSExp
computationNotationTest =
  NANat 0 $* (NAKeyword Curry $* NAString "two" $^^ NANat 3) ::
    (NANat 4 $*** (NANat 5 $* (NANat 6 $*** (NAString "seven" $**^ NANat 8)) $:^
      NAReflectedKeyword Cofix)) $:^ NANat 10

public export
emptyContext : NameBinding
emptyContext = ClosureMap empty

export
partial computationTests : IO ()
computationTests = do
  printLn "Begin computationTests:"
  printLn $ show computationNotationTest
  printLn $ "The empty context looks like: " ++ show emptyContext
  printLn "End computationTests."
  pure ()
