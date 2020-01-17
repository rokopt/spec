module Basics

%access public export


namespace Days
  data Day = Monday
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
  nextWeekday Friday    = Monday
  nextWeekday Saturday  = Monday
  nextWeekday Sunday    = Monday


testNextWeekday : (nextWeekday (nextWeekday Saturday)) = Tuesday
testNextWeekday = Refl


namespace Booleans
  -- verbose style
  data Boolean : Type where
    Trueb  : Boolean
    Falseb : Boolean
  notb : (b : Boolean) -> Boolean
  notb Falseb = Trueb
  notb Trueb  = Falseb

  andb : (b1 : Boolean) -> (b2 : Boolean) -> Boolean
  andb Trueb b2  = b2
  andb Falseb b2 = Falseb

  orb : Boolean -> Boolean -> Boolean
  orb Trueb y  = Trueb
  orb Falseb y = y

  testNotb1 : notb Falseb = Trueb
  testNotb1 = Refl

  testNotb2 : notb Trueb = Falseb
  testNotb2 = Refl

  testOrb1 : orb Trueb Falseb = Trueb
  testOrb1 = Refl


  infixl 4 &&&, ||&
  (&&&) : Boolean -> Boolean -> Boolean
  (&&&) = andb

  (||&) : Boolean -> Boolean -> Boolean
  (||&) = orb

  -- Exercise 1
  nandb : (b1 : Boolean) -> (b2 : Boolean) -> Boolean
  nandb b1 b2 = notb (b1 &&& b2)

  test_nandb1 : (nandb Trueb Falseb) = Trueb
  test_nandb1 = Refl
  test_nandb2 : (nandb Falseb Falseb) = Trueb
  test_nandb2 = Refl
  test_nandb3 : (nandb Falseb Trueb) = Trueb
  test_nandb3 = Refl
  test_nandb4 : (nandb Trueb Trueb) = Falseb
  test_nandb4 = Refl

  demorgans : (b1, b2 : Boolean) -> notb (b1 &&& b2) = notb b1 ||& notb b2
  demorgans Trueb Trueb   = Refl
  demorgans Trueb Falseb  = Refl
  demorgans Falseb Trueb  = Refl
  demorgans Falseb Falseb = Refl


namespace Numbers
  factorial : (n : Nat) -> Nat
  factorial Z     = 1
  factorial (S k) = (S k) * factorial k


  testFactorial1 : factorial 3 = 6
  testFactorial1 = Refl
  testFactorial2 : factorial 5 = mult 10 12
  testFactorial2 = Refl

  plus_id_example : (n,m : Nat) -> (n = m) -> n + n = m + m
  plus_id_example n m prf = rewrite prf in Refl

  plus_id_exercise : (n,m,o : Nat) -> (n = m) -> (m = o) -> n + m = m + o
  plus_id_exercise n m o prf prf1 = rewrite prf in (rewrite prf1 in Refl)

  plus_id_exercise_custom : (n,m,o : Nat) -> (n = o) -> n + m = m + o
  plus_id_exercise_custom n m o prf =
    rewrite prf in
    rewrite plusCommutative m o in
    Refl

  mult_0_plus : (n, m : Nat) -> (0 + n) * m = n * (0 + m)
  mult_0_plus n m = Refl

  mult_S_1 : (n, m : Nat) -> (m = S n) -> m * (1 + n) = m * m
  mult_S_1 n m prf = rewrite prf in Refl

  plus_1_neq_0_first_try_diff : (n : Nat) -> (n + 1) == 0 = False
  plus_1_neq_0_first_try_diff n = rewrite plusCommutative n 1 in Refl

  plus_1_neq_0 : (n : Nat) -> (n + 1) == 0 = False
  plus_1_neq_0 Z     = Refl
  plus_1_neq_0 (S k) = Refl


andb_true_elim_2 : (b, c : Boolean) -> (b &&& c = Trueb) -> c = Trueb
andb_true_elim_2 Trueb c prf = prf
andb_true_elim_2 Falseb Trueb  prf = Refl
andb_true_elim_2 Falseb Falseb prf = prf



-- 11.0.1
identity_fn_applied_twice : (f : Bool -> Bool)
                         -> ((x : Bool) -> f x = x)
                         -> (b : Bool)
                         -> f (f b) = b
identity_fn_applied_twice f g b = rewrite g b in rewrite g b in Refl

double_not : (b : Bool) -> not (not b) = b
double_not False = Refl
double_not True  = Refl

negation_fn_applied_twice : (f : Bool -> Bool)
                         -> ((x : Bool) -> f x = not x)
                         -> (b : Bool)
                         -> f (f b) = b
negation_fn_applied_twice f g b = rewrite g b in
                                  rewrite g (not b) in
                                  double_not b


namespace Bin
  data Bin : Type where
       ZB : Bin
       ZS : Bin -> Bin
       B  : Bin -> Bin

  bin_to_nat : Bin -> Nat
  bin_to_nat ZB     = Z
  bin_to_nat (ZS x) = S (bin_to_nat x)
  bin_to_nat (B x)  = S (S (bin_to_nat x))

  incr : Bin -> Bin
  incr ZB     = ZS ZB
  incr (ZS x) = B x
  incr (B x)  = ZS (B x)

  incl : (x : Bin) -> Bin
  incl ZB = ?incl_rhs_1
  incl (ZS x) = ?incl_rhs_2
  incl (B x) = ?incl_rhs_3
