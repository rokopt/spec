module Geb.Test.GebTest

import public Library.Test.TestLibrary
import public Geb.Geb

%default total

public export
reflectiveSExp : GebSExp
reflectiveSExp = $^ GAObjectReflection

public export
reflectiveObject : CheckedAs GebTest.reflectiveSExp GebTest.reflectiveSExp
reflectiveObject = IsJustElim {m=(checkAsType reflectiveSExp)} ItIsJust

public export
initialSExp : GebSExp
initialSExp = $^ GAInitial

public export
initialObject : CheckedAs GebTest.reflectiveSExp GebTest.initialSExp
initialObject = IsJustElim {m=(checkAsType initialSExp)} ItIsJust

public export
reflectiveObjectNotInitialTerm :
  IsNothing $ checkAs GebTest.initialSExp GebTest.reflectiveSExp
reflectiveObjectNotInitialTerm = ItIsNothing

export
gebTests : IO ()
gebTests = do
  printLn "Begin gebTests:"
  printLn $ "Reflective object: " ++ showChecked reflectiveObject
  printLn $ "Initial object: " ++ showChecked initialObject
  printLn "End gebTests."
  pure ()
