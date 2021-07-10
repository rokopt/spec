module Executable.Test.Main

import RefinedSExp.Test.ListTest
import RefinedSExp.Test.DepListTest
import RefinedSExp.Test.RefinedListTest
import RefinedSExp.Test.SExpTest
import RefinedSExp.Test.RefinedSExpTest
import RefinedSExp.Test.OldSExpTest
import RefinedSExp.Test.OldRefinedSExpTest
import RefinedSExp.Test.AlgebraicPatternTest
import RefinedSExp.Test.ADTTest
import RefinedSExp.Test.MatchTest

%default total

main : IO ()
main = putStrLn "No runtime tests yet"
