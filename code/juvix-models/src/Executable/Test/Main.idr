module Executable.Test.Main

import RefinedSExp.Test.SExpTest
import RefinedSExp.Test.RefinedSExpTest
import RefinedSExp.Test.AlgebraicPatternTest

%default total

main : IO ()
main = do
  algebraicPatternTests
