module Induction


import Chapter2

import Prelude.Interfaces
import Prelude.Nat

import Data.So
import Builtins
import IO


%access public export

%default total


plus_n_Z : (n : Nat) -> n = n + 0
plus_n_Z Z = Refl
plus_n_Z (S k) =
  let inductive_hypo = plus_n_Z k in
  rewrite inductive_hypo in Refl

minus_diag : (n : Nat) -> minus n n = 0
minus_diag Z     = Refl
minus_diag (S k) = minus_diag k

mult_0_r : (n : Nat) -> n * 0 = 0
mult_0_r Z     = Refl
mult_0_r (S k) = inductive_hypo
  where
    inductive_hypo = mult_0_r k

plus_n_Sm : (n, m : Nat) -> S (n + m) = n + (S m)
plus_n_Sm Z m     = Refl
plus_n_Sm (S k) m = rewrite plus_n_Sm k m in Refl


plus_comm : (n, m : Nat) -> n + m = m + n
plus_comm Z m = rewrite plus_n_Z m in Refl
plus_comm (S k) m = rewrite plus_comm k m in
                    rewrite plus_n_Sm m k in
                    Refl

plus_assoc : (n, m, p : Nat) -> n + (m + p) = (n + m) + p
plus_assoc Z m p     = Refl
plus_assoc (S k) m p = rewrite plus_assoc k m p in Refl


double : Nat -> Nat
double Z     = Z
double (S k) = S (S (double k))

double_plus : (n : Nat) -> double n = n + n
double_plus Z     = Refl
double_plus (S k) = rewrite double_plus k in
                    rewrite plus_comm k (S k) in
                    Refl

plus_rearrange : (n, m, p, q : Nat) -> (n + m) + (p + q) = (m + n) + (p + q)
plus_rearrange n m p q = rewrite plus_rearrange_lemma in Refl
  where
    plus_rearrange_lemma : n + m = m + n
    plus_rearrange_lemma = plus_comm n m


plus_swap : (n, m, p : Nat) -> n + (m + p) = m + (n + p)
plus_swap n m p = rewrite plus_assoc n m p in
                  rewrite plus_comm n m in
                  rewrite plus_assoc m n p in
                  Refl

mult_comm : (m, n : Nat) -> m * n = n * m
mult_comm Z n = mult_zero n
  where
    mult_zero : (n : Nat) -> 0 * n = n * 0
    mult_zero Z = Refl
    mult_zero (S k) = rewrite mult_zero k in Refl

mult_comm (S k) n = rewrite mult_comm k n in
                    plus_into_succ n k
  where
    plus_into_succ : (n, k : Nat) -> n + (n * k) = n * (S k)
    plus_into_succ Z j     = Refl
    plus_into_succ (S k) l = rewrite plus_swap k l (k * l) in
                             rewrite plus_into_succ k l in
                             Refl


lte_refl : (n : Nat) -> True = lte n n
lte_refl Z = Refl
lte_refl (S k) = rewrite lte_refl k in Refl

zero_nbeq_S : (n : Nat) -> 0 == (S n) = False
zero_nbeq_S n = Refl

S_nbeq_0 : (n : Nat) -> (S n) == 0 = False
S_nbeq_0 n = Refl

andgb_false_r : (b : Bool) -> b && False = False
andgb_false_r False = Refl
andgb_false_r True  = Refl

plus_ble_compat_l : (n, m, p : Nat) -> lte n m = True -> lte (p + n) (p + m) = True
plus_ble_compat_l n m Z     prf = prf
plus_ble_compat_l n m (S k) prf = rewrite plus_ble_compat_l n m k prf in Refl


mult_1_l : (n : Nat) -> 1 * n = n
mult_1_l n = rewrite plus_n_Z n in Refl

all3_spec : (b, c : Bool) -> (b && c) || (not b || not c) = True
all3_spec False c    = Refl
all3_spec True False = Refl
all3_spec True True  = Refl

beq_nat_refl : (n : Nat) -> True = n == n
beq_nat_refl Z     = Refl
beq_nat_refl (S k) = rewrite beq_nat_refl k in Refl


-- Natural Transformation time
binary_commute : (b : Bin) -> bin_to_nat (incr b) = S (bin_to_nat b)
binary_commute ZB     = Refl
binary_commute (ZS x) = Refl
binary_commute (B x)  = Refl

-- Easy, not worthy of the 3 stars!
