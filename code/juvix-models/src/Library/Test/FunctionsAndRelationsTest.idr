module Library.Test.FunctionsAndRelationsTest

import public Library.FunctionsAndRelations
import Data.Vect

%default total

Telescope_test_1 : Type
Telescope_test_1 = Nat

Telescope_test_2 : Nat -> Type
Telescope_test_2 = (\n => Vect n String)

Telescope_test_3 : (n : Nat ** Vect n String) -> Type
Telescope_test_3 (n ** v) = Vect (S n) Nat

Telescope_test : Telescope
Telescope_test = |~ Telescope_test_1 *~ Telescope_test_2 *~ Telescope_test_3

telescope_val_1 : :~ (|~ Telescope_test_1)
telescope_val_1 = 2

telescope_val_2 : :~ (|~ Telescope_test_1 *~ Telescope_test_2)
telescope_val_2 = (telescope_val_1 ** ["hi", "there"])

telescope_val_3 : :~ Telescope_test
telescope_val_3 = (2 **~ ["hi", "there"] **~ [3, 4, 5])
