module IndProp

%access public export



data Ev : Nat -> Type where
  Ev_0 : Ev Z
  Ev_SS : {n : Nat} -> Ev n -> Ev (S (S n))


ev_4 : Ev 4
ev_4 = Ev_SS {n = 2} $ Ev_SS {n = 0} Ev_0

double : Nat -> Nat
double k = k * 2


ev_double : Ev (double n)
ev_double {n = Z}     = Ev_0
ev_double {n = (S k)} = Ev_SS ev_double

ev_8 : Ev 8
ev_8 = ev_double {n = 4}
