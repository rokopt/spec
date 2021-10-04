module RefinedSExp.Test.SExpTest

import public Library.Test.TestLibrary
import public RefinedSExp.SExp
import public RefinedSExp.Data

%default total

public export
sexpNotationTest : DExp
sexpNotationTest =
  DNat 0 $* (DString ":Curry" $* DString "two" $^^ DNat 3) ::
    (DNat 4 $*** (DNat 5 $* (DNat 6 $*** (DString "seven" $**^ DNat 8)) $:^
      DString "~Cofix")) $:^ DNat 10

export
sexpTests : IO ()
sexpTests = do
  printLn "Begin sexpTests:"
  printLn $ show sexpNotationTest
  printLn "End sexpTests."
  pure ()
