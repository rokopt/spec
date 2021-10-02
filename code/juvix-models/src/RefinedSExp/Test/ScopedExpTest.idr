module RefinedSExp.Test.ScopedExpTest

import public Library.Test.TestLibrary
import public RefinedSExp.ScopedExp

%default total

public export
scopedExpNotationTest : NamedSExp
scopedExpNotationTest =
  NNat 0 $* (NNat 1 $* NString "two" $^^ NNat 3) ::
    (NNat 4 $*** (NNat 5 $* (NNat 6 $*** (NString "seven" $**^ NNat 8)) $:^
      NNat 9)) $:^ NNat 10

export
scopedExpTests : IO ()
scopedExpTests = do
  printLn "Begin scopedSExpTests:"
  printLn $ show scopedExpNotationTest
  printLn "End scopedExpTests."
  pure ()
