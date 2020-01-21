module Basics

%access public export

%default total

namespace Days

  data Day
    = Monday
    | Tuesday
    | Wednesday
    | Thursday
    | Friday
    | Saturday
    | Sunday

  %name Day day, day1, day2

  nextWeekday : Day -> Day
  nextWeekday Monday    = Tuesday
  nextWeekday Tuesday   = Wednesday
  nextWeekday Wednesday = Thursday
  nextWeekday Thursday  = Friday
  nextWeekday Friday    = Saturday
  nextWeekday Saturday  = Sunday
  nextWeekday Sunday    = Monday

  testNextWeekday : (nextWeekday (nextWeekday Saturday)) = Monday
  testNextWeekday = Refl

namespace Booleans

  data Bool : Type where
    True  : Bool
    False : Bool

  not : (b : Bool) -> Bool
  not True  = False
  not False = True

  andb : (b1 : Bool) -> (b2 : Bool) -> Bool
  andb True  b2 = b2
  andb False _  = False

  orb : (b1 : Bool) -> (b2 : Bool) -> Bool
  orb True _    = True
  orb _    True = True
  orb _    _    = False

  testOrb1 : (orb True False) = True
  testOrb1 = Refl

  testOrb2 : (orb False False) = False
  testOrb2 = Refl

  testOrb3 : (orb False True) = True
  testOrb3 = Refl

  testOrb4 : (orb True True) = True
  testOrb4 = Refl

  infixl 4 &&, ||

  (&&) : Bool -> Bool -> Bool
  (&&) = andb

  (||) : Bool -> Bool -> Bool
  (||) = orb

  testOrb5 : False || False || True = True
  testOrb5 = Refl

  -- 3.0.1

  nandb : (b1 : Bool) -> (b2 : Bool) -> Bool
  nandb b1 b2 = not (andb b1 b2)

  test_nandb1 : (nandb True False) = True
  test_nandb1 = Refl

  test_nandb2 : (nandb False False) = True
  test_nandb2 = Refl

  test_nandb3 : (nandb False True) = True
  test_nandb3 = Refl

  test_nandb4 : (nandb True True) = False
  test_nandb4 = Refl

  -- 3.0.2

  andb3 : (b1 : Bool) -> (b2 : Bool) -> (b3 : Bool) -> Bool
  andb3 True True True = True
  andb3 _    _    _    = False

  test_andb31 : (andb3 True True True) = True
  test_andb31 = Refl

  test_andb32 : (andb3 False True True) = False
  test_andb32 = Refl

  test_andb33 : (andb3 True False True) = False
  test_andb33 = Refl

  test_andb34 : (andb3 True True False) = False
  test_andb34 = Refl

namespace Numbers

  data Nat : Type where
    Z : Nat
    S : Nat -> Nat

  pred : (n : Nat) -> Nat
  pred Z      = Z
  pred (S k)  = k

  minusTwo : (n : Nat) -> Nat
  minusTwo Z          = Z
  minusTwo (S Z)      = Z
  minusTwo (S (S k))  = k

  evenb : (n : Nat) -> Bool
  evenb Z         = True
  evenb (S Z)     = False
  evenb (S (S k)) = evenb k

  oddb : (n : Nat) -> Bool
  oddb n = not (evenb n)

  testOddb1 : oddb (S Z) = True
  testOddb1 = Refl

  testOddb2 : oddb (S (S (S (S Z)))) = False
  testOddb2 = Refl

  plus : (n : Nat) -> (m : Nat) -> Nat
  plus Z m      = m
  plus (S k) m  = S (plus k m)

  mult : (n, m : Nat) -> Nat
  mult Z     _ = Z
  mult (S k) m = plus m (mult k m)

  testMult1 : (mult (S (S (S Z))) (S (S (S Z))) = (S (S (S (S (S (S (S (S (S Z))))))))))
  testMult1 = Refl

  minus : (n, m : Nat) -> Nat
  minus Z     _     = Z
  minus n     Z     = n
  minus (S k) (S j) = minus k j

  exp : (base, power : Nat) -> Nat
  exp base Z      = S Z
  exp base (S p)  = mult base (exp base p)

  -- 6.0.1

  factorial : (n : Nat) -> Nat
  factorial Z     = S Z
  factorial (S n) = mult (S n) (factorial n)

  testFactorial1 : factorial (S (S (S Z))) = (S (S (S (S (S (S Z))))))
  testFactorial1 = Refl

  twelve : Nat
  twelve = mult (S (S (S (S (S (S Z)))))) (S (S Z))

  ten : Nat
  ten = mult (S (S (S (S (S Z))))) (S (S Z))

  testFactorial2 : factorial (S (S (S (S (S Z))))) = mult Numbers.twelve Numbers.ten
  testFactorial2 = Refl

  syntax [x] "+" [y] = plus x y
  syntax [x] "-" [y] = minus x y
  syntax [x] "*" [y] = mult x y

  infixl 3 ==

  (==) : (n, m : Nat) -> Bool
  (==) Z      Z     = True
  (==) Z      (S j) = False
  (==) (S k)  Z     = False
  (==) (S k)  (S j) = (==) k j

  lte : (n, m : Nat) -> Bool
  lte Z     m     = True
  lte n     Z     = False
  lte (S k) (S j) = lte k j

  testLte1 : lte (S (S Z)) (S (S Z)) = True
  testLte1 = Refl

  testLte2 : lte (S (S Z)) (S (S (S (S Z)))) = True
  testLte2 = Refl

  testLte3 : lte (S (S (S (S Z)))) (S (S Z)) = False
  testLte3 = Refl

  -- 6.0.2

  blt_nat : (n, m : Nat) -> Bool
  blt_nat n m = lte (S n) m

  test_blt_nat_1 : blt_nat (S (S Z)) (S (S Z)) = False
  test_blt_nat_1 = Refl

  test_blt_nat_2 : blt_nat (S (S Z)) (S (S (S (S Z)))) = True
  test_blt_nat_2 = Refl

  test_blt_nat_3 : blt_nat (S (S (S (S Z)))) (S (S Z)) = False
  test_blt_nat_3 = Refl

  plus_Z_n : (n : Nat) -> (Z + n) = n
  plus_Z_n n = Refl

  plus_1_1 : (n : Nat) -> ((S Z) + n) = S n
  plus_1_1 n = Refl

  mult_0_1 : (n : Nat) -> mult Z n = Z
  mult_0_1 n = Refl

  plus_id_example : (n, m : Nat) -> (n = m) -> (n + n) = (m + m)
  plus_id_example n m prf = rewrite prf in Refl

  -- 8.0.1

  plus_id_exercise : (n, m, o : Nat) -> (n = m) -> (m = o) -> (n + m) = (m + o)
  plus_id_exercise n m o a b = rewrite a in (rewrite b in Refl)

  mult_0_plus : (n, m : Nat) -> ((Z + n) * m) = (n * (Z + m))
  mult_0_plus n m = Refl

  -- 8.0.2

  mult_S_1 : (n, m : Nat) -> (m = S n) -> (m * ((S Z) + n)) = m * m
  mult_S_1 n m prf = rewrite prf in Refl

  plus_1_neq_0 : (n : Nat) -> (n + (S Z)) == Z = False
  plus_1_neq_0 Z      = Refl
  plus_1_neq_0 (S k)  = Refl

  not_involutive : (b : Bool) -> not (not b) = b
  not_involutive True   = Refl
  not_involutive False  = Refl

  andb_commutative : (b, c : Bool) -> (b && c) = (c && b)
  andb_commutative True  True   = Refl
  andb_commutative True  False  = Refl
  andb_commutative False True   = Refl
  andb_commutative False False  = Refl

  andb_commutative'_rhs_1 : (c : Bool) -> c = (c && True)
  andb_commutative'_rhs_1 True  = Refl
  andb_commutative'_rhs_1 False = Refl

  andb_commutative'_rhs_2 : (c : Bool) -> False = (c && False)
  andb_commutative'_rhs_2 True  = Refl
  andb_commutative'_rhs_2 False = Refl

  andb_commutative' : (b, c : Bool) -> (b && c) = (c && b)
  andb_commutative' True  = andb_commutative'_rhs_1
  andb_commutative' False = andb_commutative'_rhs_2

  -- 9.0.1

  andb_true_elim_2 : (b, c : Bool) -> ((b && c) = True) -> c = True
  andb_true_elim_2 True  c     prf = rewrite prf in Refl
  andb_true_elim_2 False False prf = rewrite prf in Refl
  andb_true_elim_2 False True  prf = Refl

  -- 9.0.2

  eq_commutative : (n : Nat, m : Nat) -> (n == m) = (m == n)
  eq_commutative Z      Z     = Refl
  eq_commutative (S m)  Z     = Refl
  eq_commutative Z      (S j) = Refl
  eq_commutative (S k)  (S j) = eq_commutative k j

  zero_nbeq_plus_1 : (n : Nat) -> Z == (n + (S Z)) = False
  zero_nbeq_plus_1 n = rewrite (eq_commutative (Z) (plus n (S Z))) in rewrite (plus_1_neq_0 n) in Refl

  plus' : Nat -> Nat -> Nat
  plus' Z     r = r
  plus' (S l) r = S (plus' l r)

  -- 11.0.1

  identity_fn_applied_twice : (f : Bool -> Bool) -> ((x : Bool) -> f x = x) -> (b : Bool) -> f (f b) = b
  identity_fn_applied_twice f g b = rewrite (g b) in rewrite (g b) in Refl

  -- 11.0.2

  andb_eq_orb : (b, c : Bool) -> ((b && c) = (b || c)) -> b = c
  andb_eq_orb True  True  prf = Refl
  andb_eq_orb False False prf = Refl
  andb_eq_orb True  False prf = rewrite prf in Refl
  andb_eq_orb False True  prf = rewrite prf in Refl

  -- 11.0.3

  data Bin : Type where
    BZ  : Bin
    BT  : Bin -> Bin
    BTP : Bin -> Bin

  incr : Bin -> Bin
  incr BZ      = BTP BZ
  incr (BT b)  = BTP b
  incr (BTP b) = BT (incr b)

  test_bin_incr_1 : incr (BT BZ) = incr BZ
  test_bin_incr_1 = Refl

  test_bin_incr_2 : incr (BTP BZ) = BT (BTP BZ)
  test_bin_incr_2 = Refl

  test_bin_incr_3 : incr (incr (BT (BT (BTP BZ)))) = BT (BTP (BTP BZ))
  test_bin_incr_3 = Refl

  bin_to_nat : Bin -> Nat
  bin_to_nat BZ       = Z
  bin_to_nat (BT b)   = (S (S Z)) * (bin_to_nat b)
  bin_to_nat (BTP b)  = (S Z) + ((S (S Z)) * (bin_to_nat b))

  test_bin_to_nat_1 : bin_to_nat (incr BZ) = S Z
  test_bin_to_nat_1 = Refl

  test_bin_to_nat_2 : bin_to_nat (BT (BTP (BTP BZ))) = mult (S (S Z)) (S (S (S Z)))
  test_bin_to_nat_2 = Refl
