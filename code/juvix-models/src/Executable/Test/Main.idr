module Executable.Test.Main

import RefinedSExp.Test.SExpTest
import RefinedSExp.Test.RefinedSExpTest
import RefinedSExp.Test.AlgebraicPatternTest
import RefinedSExp.Test.ADTTest
import RefinedSExp.Test.MatchTest

%default total

main : IO ()
main = do
  algebraicPatternTests
  ADTTests
  matchTests
