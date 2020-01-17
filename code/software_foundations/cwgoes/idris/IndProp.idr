module IndProp

import Prelude
import Logic

%access public export

%default total

data Ev : Nat -> Type where
  Ev_0  : Ev Z
  Ev_SS : {n : Nat} -> Ev n -> Ev (S (S n))

ev_4 : Ev 4
ev_4 = Ev_SS {n = 2} $ Ev_SS {n = 0} Ev_0

ev_plus4 : Ev n -> Ev (4 + n)
ev_plus4 x = Ev_SS $ Ev_SS x

double : Nat -> Nat
double Z      = Z
double (S k)  = S (S (double k))

-- 1.0.1

ev_double : (n : Nat) -> Ev (double n)
ev_double Z     = Ev_0
ev_double (S k) = Ev_SS { n = double k } (ev_double k)

-- 2. Using Evidence in Proofs

ev_minus2 : Ev n -> Ev (pred (pred n))
ev_minus2 Ev_0        = Ev_0
ev_minus2 (Ev_SS e')  = e'

one_not_even : Not (Ev 1)
one_not_even Ev_0 impossible
one_not_even (Ev_SS _) impossible

-- 2.2

SSSSev__even : Ev (S (S (S (S n)))) -> Ev n
SSSSev__even (Ev_SS (Ev_SS ev)) = ev

even5_nonsense : Ev 5 -> 2 + 2 = 9
even5_nonsense Ev_0 impossible
even5_nonsense (Ev_SS Ev_0) impossible
even5_nonsense (Ev_SS (Ev_SS ev)) = absurd $ one_not_even ev

ev_even : Ev n -> (k ** n = double k)
ev_even Ev_0 = (Z ** Refl)
ev_even (Ev_SS e') = I $ ev_even e'
  where
  I : (k' ** n' = double k') -> (k ** S (S n') = double k)
  I (k' ** prf) = (S k' ** cong {f = S} $ cong {f = S} prf)

-- 2.3: Induction on Evidence

ev_even' : Ev n -> (k ** n = double k)
ev_even' Ev_0 = (Z ** Refl)
ev_even' (Ev_SS e') =
  let (k ** prf) = ev_even e'
      cprf = cong {f=S} $ cong {f=S} prf
  in rewrite cprf in (S k ** Refl)

ev_even_iff : (Ev n) <-> (k ** n = double k)
ev_even_iff = (ev_even, fro)
  where
    fro : (k ** n = double k) -> (Ev n)
    fro (k ** prf) = rewrite prf in ev_double {n=k}

-- 2.3.1

ev_sum : {n' : Nat} -> {m' : Nat} -> Ev n' -> Ev m' -> Ev (n' + m')
ev_sum {m'} Ev_0 mev = mev
ev_sum {n'} nev Ev_0 = rewrite plusZeroRightNeutral n' in nev
ev_sum (Ev_SS nev {n=n}) (Ev_SS mev {n=m}) =
  rewrite (sym (plusSuccRightSucc n (S m))) in
  rewrite (sym (plusSuccRightSucc n m)) in
  Ev_SS (Ev_SS (ev_sum nev mev))

-- 2.4

data Ev' : Nat -> Type where
  Ev'_0 : Ev' Z
  Ev'_2 : Ev' 2
  Ev'_sum : Ev' n -> Ev' m -> Ev' (n + m)

ev'_ev : (Ev' n) <-> Ev n
ev'_ev = (ev'_ev_f, ev'_ev_r)
  where
    ev'_ev_f : Ev' n -> Ev n
    ev'_ev_f (Ev'_0) = Ev_0
    ev'_ev_f (Ev'_2) = Ev_SS Ev_0
    ev'_ev_f (Ev'_sum x y) = ev_sum (ev'_ev_f x) (ev'_ev_f y)

    ev'_ev_r : Ev n -> Ev' n
    ev'_ev_r Ev_0 = Ev'_0
    ev'_ev_r (Ev_SS Ev_0) = Ev'_2
    ev'_ev_r (Ev_SS ev) = Ev'_sum Ev'_2 (ev'_ev_r ev)

-- 2.5

ev_ev__ev : Ev (n + m) -> Ev n -> Ev m
ev_ev__ev = ?ev_ev__ev_rhs

-- 2.5.1

ev_plus_plus : Ev (n + m) -> Ev (n + p) -> Ev (m + p)
ev_plus_plus = ?ev_plus_plus_rhs

-- 3: Inductive Relations

data Le : Nat -> Nat -> Type where
  Le_n : Le n n
  Le_S : Le n m -> Le n (S m)

test_le1 : Le 3 3
test_le1 = Le_n

test_le2 : Le 3 6
test_le2 = Le_S $ Le_S $ Le_S Le_n

test_le3 : (Le 2 1) -> 2 + 2 = 5
test_le3 (Le_S Le_n) impossible
test_le3 (Le_S (Le_S _)) impossible

Lt : (n, m : Nat) -> Type
Lt n m = Le (S n) m

data Square_of : Nat -> Nat -> Type where
  Sq : Square_of n (n * n)

data Next_nat : Nat -> Nat -> Type where
  Nn : Next_nat n (S n)

data Next_even : Nat -> Nat -> Type where
  Ne_1 : Ev (S n) -> Next_even n (S n)
  Ne_2 : Ev (S (S n)) -> Next_even n (S (S n))

-- 3.0.1
