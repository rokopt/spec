module RefinedSExp.Test.ScopedExpTest

import public Library.Test.TestLibrary
import public RefinedSExp.ScopedExp

%default total

public export
scopedExpNotationTest : NamedSExp
scopedExpNotationTest =
  NANat 0 $* (NAKeyword WithNameWrongArguments $* NAString "two" $^^ NANat 3) ::
    (NANat 4 $*** (NANat 5 $* (NANat 6 $*** (NAString "seven" $**^ NANat 8)) $:^
      NAReflectedKeyword WithName)) $:^ NANat 10

public export
emptyContext : PureNameContext
emptyContext = ClosureMap empty

export
partial scopedExpTests : IO ()
scopedExpTests = do
  printLn "Begin scopedSExpTests:"
  printLn $ show scopedExpNotationTest
  printLn "End scopedExpTests."
  printLn $ "The empty context looks like: " ++ show emptyContext
  pure ()
