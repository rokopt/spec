module RefinedSExp.Test.ScopedExpTest

import public Library.Test.TestLibrary
import public RefinedSExp.ScopedExp

%default total

Show (SExp Nat) where
  show = fst $ sexpShows show

Show (SList Nat) where
  show = snd $ sexpShows show

public export
scopedExpNotationTest : SExp Nat
scopedExpNotationTest =
  0 $* (1 $* 2 $^^ 3) :: (4 $*** (5 $* (6 $*** (7 $**^ 8)) $:^ 9)) $:^ 10

export
scopedExpTests : IO ()
scopedExpTests = do
  printLn "Begin scopedSExpTests:"
  printLn $ show scopedExpNotationTest
  printLn "End scopedExpTests."
  pure ()
