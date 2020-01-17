module Induction

import Prelude.Interfaces
import Prelude.Nat
import Prelude.Bool

%access public export

%default total

plus_n_Z : (n : Nat) -> n = n + 0
plus_n_Z Z     = Refl
plus_n_Z (S k) = rewrite (plus_n_Z k) in Refl

minus_diag : (n : Nat) -> minus n n = 0
minus_diag Z      = Refl
minus_diag (S k)  = minus_diag k

-- 1.0.1

mult_0_r : (n : Nat) -> n * 0 = 0
mult_0_r Z      = Refl
mult_0_r (S k)  = rewrite (mult_0_r k) in Refl

plus_n_Sm : (n, m : Nat) -> S (n + m) = n + (S m)
plus_n_Sm Z     m = Refl
plus_n_Sm (S k) m = rewrite (plus_n_Sm k m) in Refl

plus_comm : (n, m : Nat) -> n + m = m + n
plus_comm Z     n = rewrite plus_n_Z n in Refl
plus_comm (S k) n = rewrite plus_comm k n in rewrite plus_n_Sm n k in Refl

plus_assoc : (n, m, p : Nat) -> n + (m + p) = (n + m) + p
plus_assoc n Z     p = rewrite plus_n_Z n in rewrite plus_n_Z p in Refl
plus_assoc n (S k) p =
  rewrite plus_comm n (S k) in
  rewrite plus_n_Sm (k + n) p in
  rewrite plus_n_Sm k p in
  rewrite plus_comm k n in
  rewrite plus_assoc n k (S p) in
  Refl

-- 1.0.2

double : (n : Nat) -> Nat
double Z     = Z
double (S k) = S (S (double k))

double_plus : (n : Nat) -> double n = n + n
double_plus Z     = Refl
double_plus (S k) =
  let lemma1 = double_plus k
      lemma2 = plus_n_Sm k k
  in rewrite lemma1 in rewrite lemma2 in Refl

-- 1.0.3

evenb : (n : Nat) -> Bool
evenb Z     = True
evenb (S n) = not (evenb n)

evenb_S : (n : Nat) -> evenb (S n) = not (evenb n)
evenb_S n = Refl

mult_0_plus' : (n, m : Nat) -> (0 + n) * m = n * m
mult_0_plus' n m = Refl

plus_rearrange : (n, m, p, q : Nat) -> (n + m) + (p + q) = (m + n) + (p + q)
plus_rearrange n m p q = rewrite plus_comm n m in Refl

-- 3.0.1

-- Simplify this...
plus_swap : (n, m, p : Nat) -> n + (m + p) = m + (n + p)
plus_swap n m Z =
  rewrite plus_n_Z n in
  rewrite plus_n_Z m in
  rewrite plus_comm (plus n 0) (plus m 0) in
  Refl
plus_swap n m (S k) =
  rewrite plus_comm m (S k) in
  rewrite plus_comm n (S k) in
  rewrite plus_n_Sm k m in
  rewrite plus_n_Sm k n in
  rewrite plus_comm k (S m) in
  rewrite plus_comm k (S n) in
  rewrite plus_comm n (S (m + k)) in
  rewrite plus_comm m (S (n + k)) in
  rewrite plus_comm (m + k) n in
  rewrite plus_comm (n + k) m in
  rewrite plus_swap n m k in
  Refl

mult_incr : (m, n : Nat) -> m * (S n) = m + (m * n)
mult_incr Z     n = Refl
mult_incr (S k) n = rewrite mult_incr k n in
                    rewrite plus_swap k n (k * n) in
                    Refl

mult_comm : (m, n : Nat) -> m * n = n * m
mult_comm m Z     = rewrite mult_0_r m in Refl
mult_comm m (S k) =
  rewrite mult_incr m k in
  rewrite mult_comm m k in
  Refl

-- 3.0.2

lte_refl : (n : Nat) -> True = lte n n
lte_refl Z      = Refl
lte_refl (S k)  = rewrite lte_refl k in Refl

zero_nbeq_S : (n : Nat) -> 0 == (S n) = False
zero_nbeq_S n = Refl

andb_false_r : (b : Bool) -> b && False = False
andb_false_r True   = Refl
andb_false_r False  = Refl

plus_ble_compat_1 : (n, m, p : Nat) -> lte n m = True -> lte (p + n) (p + m) = True
plus_ble_compat_1 n m Z     prf = rewrite prf in Refl
plus_ble_compat_1 n m (S k) prf = rewrite plus_ble_compat_1 n m k prf in Refl

s_nbeq_0 : (n : Nat) -> (S n) == 0 = False
s_nbeq_0 n = Refl

mult_1_1 : (n : Nat) -> 1 * n = n
mult_1_1 n = rewrite plus_n_Z n in Refl

all3_spec : (b, c : Bool) -> (b && c) || ((not b) || (not c)) = True
all3_spec True  False = Refl
all3_spec False False = Refl
all3_spec False True  = Refl
all3_spec True  True  = Refl

mult_plus_distr_r : (n, m, p : Nat) -> (n + m) * p = (n * p) + (m * p)
mult_plus_distr_r n m Z     = rewrite mult_0_r n in rewrite mult_0_r m in rewrite mult_0_r (n + m) in Refl
mult_plus_distr_r n m (S k) =
  rewrite mult_incr n k in
  rewrite mult_incr m k in
  rewrite mult_incr (n + m) k in
  rewrite mult_plus_distr_r n m k in
  rewrite (sym (plus_assoc n (n * k) (m + (m * k)))) in
  rewrite plus_comm m (m * k) in
  rewrite plus_assoc (n * k) (m * k) m in
  rewrite plus_comm (n * k + m * k) m in
  rewrite (sym (plus_assoc n m (n * k + m * k))) in
  Refl

mult_assoc : (n, m, p : Nat) -> n * (m * p) = (n * m) * p
mult_assoc n m Z     =
  rewrite mult_0_r (n * m) in
  rewrite mult_0_r m in
  rewrite mult_0_r n in
  Refl
mult_assoc n m (S k) =
  rewrite mult_incr m k in
  rewrite mult_incr (n * m) k in
  rewrite mult_comm n (m + m * k) in
  rewrite mult_plus_distr_r m (m * k) n in
  rewrite mult_comm n m in
  rewrite (sym (mult_assoc m n k)) in
  rewrite mult_comm (m * k) n in
  rewrite mult_assoc m n k in
  rewrite mult_assoc n m k in
  rewrite mult_comm n m in
  Refl

-- 3.0.3

beq_nat_refl : (n : Nat) -> True = n == n
beq_nat_refl Z      = Refl
beq_nat_refl (S k)  = rewrite beq_nat_refl k in Refl

-- 3.0.4

{- Idris doesn't have a "replace" tactic, error in book? -}

-- 3.0.5

-- 3.0.6
