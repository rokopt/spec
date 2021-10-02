module RefinedSExp.Test.ScopedExpTest

import public Library.Test.TestLibrary
import public RefinedSExp.ScopedExp

%default total

public export
scopedExpNotationTest : NamedSExp
scopedExpNotationTest =
  NANat 0 $* (NANat 1 $* NAString "two" $^^ NANat 3) ::
    (NANat 4 $*** (NANat 5 $* (NANat 6 $*** (NAString "seven" $**^ NANat 8)) $:^
      NANat 9)) $:^ NANat 10

export
scopedExpTests : IO ()
scopedExpTests = do
  printLn "Begin scopedSExpTests:"
  printLn $ show scopedExpNotationTest
  printLn "End scopedExpTests."
  pure ()
