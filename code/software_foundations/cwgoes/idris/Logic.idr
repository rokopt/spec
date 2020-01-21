module Logic

import Prelude

%access public export

%default total

Injective : (f : a -> b) -> Type
Injective {a} {b} f = (x, y : a) -> f x = f y -> x = y

succ_inj : Injective S
succ_inj x x Refl = Refl

and_example : (3 + 4 = 7, 2 * 2 = 4)
and_example = (Refl, Refl)

and_intro : a -> b -> (a, b)
and_intro = MkPair

plus_n_Z : (n : Nat) -> n = n + 0
plus_n_Z Z     = Refl
plus_n_Z (S k) = rewrite (plus_n_Z k) in Refl

plus_n_Sm : (n, m : Nat) -> S (n + m) = n + (S m)
plus_n_Sm Z     m = Refl
plus_n_Sm (S k) m = rewrite (plus_n_Sm k m) in Refl

plus_Z_Z : (n : Nat, m : Nat) -> n + m = 0 -> n = 0
plus_Z_Z n Z prf =
  rewrite (sym prf) in
  rewrite plus_n_Z n in
  Refl
plus_Z_Z (S k) _ Refl impossible
plus_Z_Z Z (S k) Refl impossible

and_exercise : (n, m : Nat) -> n + m = 0 -> (n = 0, m = 0)
and_exercise n m prf = (rewrite plus_Z_Z n m prf in Refl, rewrite plus_Z_Z m n (rewrite plusCommutative m n in prf) in Refl)

and_example2 : (n, m : Nat) -> (n = 0, m = 0) -> n + m = 0
and_example2 Z Z      (Refl, Refl) = Refl
and_example2 (S _) _  (Refl, _   ) impossible
and_example2 _ (S _)  (_,    Refl) impossible

and_example3 : (n, m : Nat) -> n + m = 0 -> n * m = 0
and_example3 n m prf =
  let (nz, _) = and_exercise n m prf in
  rewrite nz in Refl

and_commut : (p, q) -> (q, p)
and_commut (p, q) = (q, p)

or_example : (n, m : Nat) -> ((n = 0) `Either` (m = 0)) -> n * m = 0
or_example Z _ (Left Refl) = Refl
or_example (S _) _ (Left Refl) impossible
or_example n Z (Right Refl) = multZeroRightZero n
or_example _ (S _) (Right Refl) impossible

or_intro : a -> a `Either` b
or_intro = Left

zero_or_succ : (n : Nat) -> ((n = 0) `Either` (n = S (pred n)))
zero_or_succ Z      = Left Refl
zero_or_succ (S _)  = Right Refl

-- 1.2.1

mult_eq_0 : (n, m : Nat) -> n * m = 0 -> ((n = 0) `Either` (m = 0))
mult_eq_0 _ Z _ = Right Refl
mult_eq_0 Z (S _) Refl = Left Refl
mult_eq_0 (S _) (S _) Refl impossible

-- 1.2.2

or_commut : (p `Either` q) -> (q `Either` p)
or_commut (Left a)  = Right a
or_commut (Right b) = Left b

ex_falso_quodlibet : Void -> p
ex_falso_quodlibet = void

not_implies_our_not : Not p -> (q -> (p -> q))
not_implies_our_not prf = \q => (\p => void (prf p))

zero_not_one : Not (Z = S _)
zero_not_one = \Refl impossible

not_False : Not Void
not_False = absurd

contradiction_implies_anything : (p, Not p) -> q
contradiction_implies_anything (p, notp) = absurd $ notp p

double_neg : p -> Not $ Not p
double_neg p notp = notp p

contrapositive : (p -> q) -> (Not q -> Not p)
contrapositive pq = \notq => \p => notq (pq p)

not_both_true_and_false : Not (p, Not p)
not_both_true_and_false = \(p, notp) => notp p

not_true_is_false : (b : Bool) -> Not (b = True) -> b = False
not_true_is_false False h = Refl
not_true_is_false True  h = absurd $ h Refl

True_is_true : Unit
True_is_true = ()

namespace MyIff
  iff : {p, q : Type} -> Type
  iff {p} {q} = (p -> q, q -> p)

  syntax [p] "<->" [q] = iff {p} {q}

  infixl 6 <->

  iff_sym : (p <-> q) -> (q <-> p)
  iff_sym (pq, qp) = (qp, pq)

  not_true_iff_false : (Not (b = True)) <-> (b = False)
  not_true_iff_false {b} = (not_true_is_false b, not_true_and_false b)
    where
    not_true_and_false : (b : Bool) -> (b = False) -> Not (b = True)
    not_true_and_false False _ Refl impossible
    not_true_and_false True Refl _ impossible

  iff_refl : p <-> p
  iff_refl = (\p => p, \p => p)

  iff_trans : (p <-> q) -> (q <-> r) -> (p <-> r)
  iff_trans (pq, qp) (qr, rq) = (\p => qr (pq p), \r => qp (rq r))

  or_distributes_over_and : (p `Either` (q, r)) <-> (p `Either` q, p `Either` r)
  or_distributes_over_and = (p_either_qr_f, p_either_qr_r)
    where
    p_either_qr_f : (p `Either` (q, r)) -> (p `Either` q, p `Either` r)
    p_either_qr_f (Left p) = (Left p, Left p)
    p_either_qr_f (Right (q, r)) = (Right q, Right r)

    p_either_qr_r : (p `Either` q, p `Either` r) -> (p `Either` (q, r))
    p_either_qr_r (Left p,  _)        = (Left p)
    p_either_qr_r (Right q, Left p)   = (Left p)
    p_either_qr_r (Right q, Right r)  = (Right (q, r))

  mult_0 : (n * m = Z) <-> ((n = Z) `Either` (m = Z))
  mult_0 {n} {m} = (to n m, or_example n m)
    where
      to : (n, m : Nat) -> (n * m = Z) -> (n = 0) `Either` (m = 0)
      to Z _ Refl = Left Refl
      to (S _) Z _ = Right Refl
      to (S _) (S _) Refl impossible

  or_assoc : (p `Either` (q `Either` r)) <-> ((p `Either` q) `Either` r)
  or_assoc = (to, fro)
    where
      to : Either p (Either q r) -> Either (Either p q) r
      to (Left p) = Left $ Left p
      to (Right (Left q)) = Left $ Right q
      to (Right (Right r)) = Right r

      fro : Either (Either p q) r -> Either p (Either q r)
      fro (Left (Left p)) = Left p
      fro (Left (Right q)) = Right $ Left q
      fro (Right r) = Right (Right r)

  apply_iff_example : (n, m : Nat) -> n * m = Z -> ((n = Z) `Either` (m = Z))
  apply_iff_example n m = fst $ mult_0 {n} {m}

four_is_even : (n : Nat ** 4 = n + n)
four_is_even = (2 ** Refl)

exists_example_2 : (m : Nat ** n = 4 + m) -> (o : Nat ** n = 2 + o)
exists_example_2 (m ** prf) = (2 + m ** prf)

-- 1.6.1

dist_not_exists : {p : a -> Type} -> ((x : a) -> p x) -> Not (x ** Not (p x))
dist_not_exists f = (\(x ** n) => n (f x))

-- 1.6.2

dist_exists_or : {p, q : a -> Type} -> (x ** (p x `Either` q x)) <-> ((x ** p x) `Either` (x ** q x))
dist_exists_or = (dist_exists_or_f, dist_exists_or_r)
  where
  dist_exists_or_f : {p, q : a -> Type} -> (x ** (p x `Either` q x)) -> ((x ** p x) `Either` (x ** q x))
  dist_exists_or_f (x ** Left px)   = Left (x ** px)
  dist_exists_or_f (x ** Right qx)  = Right (x ** qx)

  dist_exists_or_r : {p, q : a -> Type} -> ((x ** p x) `Either` (x ** q x)) -> (x ** (p x `Either` q x))
  dist_exists_or_r (Left (x ** px))   = (x ** Left px)
  dist_exists_or_r (Right (x ** qx))  = (x ** Right qx)

-- 2: Programming with Propositions

In : (x : a) -> (l : List a) -> Type
In x [] = Void
In x (x' :: xs) = (x' = x) `Either` In x xs

In_example_1 : In 4 [1, 2, 3, 4, 5]
In_example_1 = Right $ Right $ Right $ Left Refl

In_example_2 : In n [2, 4] -> (n' : Nat ** n = 2 * n')
In_example_2 (Left Refl) = (1 ** Refl)
In_example_2 (Right $ Left Refl) = (2 ** Refl)
In_example_2 (Right $ Right prf) = absurd prf

In_map : (f : a -> b) -> (l : List a) -> (x : a) -> In x l -> In (f x) (map f l)
In_map _ [] _ ixl = absurd ixl
In_map f (x' :: xs) x (Left prf) = rewrite prf in Left Refl
In_map f (x' :: xs) x (Right r) = Right $ In_map f xs x r

-- 2.0.1

In_map_iff : (f : a -> b) -> (l : List a) -> (y : b) -> (In y (map f l)) <-> (x ** (f x = y, In x l))
In_map_iff f l y = (in_map_iff_f f l y, in_map_iff_r f l y)
  where
  in_map_iff_f : (f : a -> b) -> (l : List a) -> (y : b) -> In y (map f l) -> (x ** (f x = y, In x l))
  in_map_iff_f f []         y prf         = absurd prf
  in_map_iff_f f (x :: xs)  y (Left prf)  = (x ** (prf, Left Refl))
  in_map_iff_f f (x :: xs)  y (Right tl)  = let (x ** (eq, prf)) = in_map_iff_f f xs y tl in (x ** (eq, Right prf))

  in_map_iff_r : (f : a -> b) -> (l : List a) -> (y : b) -> (x ** (f x = y, In x l)) -> In y (map f l)
  in_map_iff_r f []           y (x ** (eq, prf)) = absurd prf
  in_map_iff_r f (x' :: xs')  y (x ** (eq, Left prf)) = rewrite prf in rewrite eq in Left Refl
  in_map_iff_r f (x' :: xs')  y (x ** (eq, Right tl)) = Right $ in_map_iff_r f xs' y (x ** (eq, tl))

-- 2.0.2

in_app_iff : (a : t, l : List t, l' : List t) ->  (In a (l ++ l')) <-> (In a l `Either` In a l')
in_app_iff a l l' = (in_app_iff_rhs_f a l l', in_app_iff_rhs_r a l l')
  where
  in_app_iff_rhs_f : (a : t, l : List t, l' : List t) -> (In a (l ++ l')) -> (In a l `Either` In a l')
  in_app_iff_rhs_f a [] [] void = absurd void
  in_app_iff_rhs_f a [] ys prf  = Right prf
  in_app_iff_rhs_f a (x :: xs) _  (Left eq) = Left (Left eq)
  in_app_iff_rhs_f a (x :: xs) ys (Right p) =
    case in_app_iff_rhs_f a xs ys p of
      Left l  => Left $ Right l
      Right r => Right r

  in_app_iff_rhs_r : (a : t, l : List t, l' : List t) -> (In a l `Either` In a l') -> (In a (l ++ l'))
  in_app_iff_rhs_r a [] ys (Left void)  = absurd void
  in_app_iff_rhs_r a [] ys (Right yprf) = yprf
  in_app_iff_rhs_r a (x :: xs) ys (Right yprf) = Right $ in_app_iff_rhs_r a xs ys (Right yprf)
  in_app_iff_rhs_r a (x :: xs) ys (Left (Left leq)) = Left leq
  in_app_iff_rhs_r a (x :: xs) ys (Left (Right rt)) = Right $ in_app_iff_rhs_r a xs ys (Left rt)

-- 2.0.3


All : (p : t -> Type) -> (l : List t) -> Type
All p []          = ()
All p (x :: xs)   = (p x, All p xs)

All_example_1 : All (\x => x = 2) [2]
All_example_1 = (Refl, ())

All_example_2 : All (\x => 2 = 2) [2, 3, 4]
All_example_2 = (Refl, Refl, Refl, ())

disjoint : (n : Nat) -> Z = S n -> Void
disjoint n p = replace {P = disjointTy} p ()
  where
    disjointTy : Nat -> Type
    disjointTy Z      = ()
    disjointTy (S k)  = Void

pred_eq : {n : Nat} -> {m : Nat} -> (n = m) -> (Prelude.pred n = Prelude.pred m)
pred_eq prf = rewrite prf in Refl

disjointS : (n : Nat) -> Not (n = S n)
disjointS Z     prf = disjoint 0 prf
disjointS (S k) prf = disjointS k (pred_eq prf)

disjointL : (x : t) -> [] = (x :: xs) -> Void
disjointL x p = replace {P = disjointTy} p ()
  where
    disjointTy : List t -> Type
    disjointTy [] = ()
    disjointTy (y :: ys) = Void

All_example_3 : Not (All (\x => x = 0) (the (List Nat) [3]))
All_example_3 = \(prf,()) => (disjoint 2 (sym prf))

All_In : (l : List t) -> ((x : t) -> In x l -> p x) <-> (All p l)
All_In l = (all_in_f l, all_in_r l)
  where
  all_in_f : (l : List t) -> ((x : t) -> In x l -> p x) -> (All p l)
  all_in_f [] func = ()
  all_in_f (x :: xs) func = (func x (Left Refl), all_in_f xs (\x, prf => func x (Right prf)))

  all_in_r : (l : List t) -> (All p l) -> ((x : t) -> In x l -> p x)
  all_in_r []         prf = (\x', inprf => absurd inprf)
  all_in_r {p} (x :: xs) (feq, rest) = \x', inprf =>
    case inprf of
      Left eq => rewrite (sym eq) in feq
      Right tl => all_in_r xs rest x' tl

-- 2.0.4

combine_odd_even : (podd, peven : Nat -> Type) -> (Nat -> Type)
combine_odd_even podd peven = \nat => podd nat `Either` peven nat

-- 3. Applying theorems to arguments

lemma_application_ex : (n : Nat) -> (ns : List Nat) -> In n (map (\m => m * 0) ns) -> n = 0
lemma_application_ex _ [] prf = absurd prf
lemma_application_ex _ (y :: _) (Left prf) = rewrite sym $ multZeroRightZero y in sym prf
lemma_application_ex n (_ :: xs) (Right prf) = lemma_application_ex n xs prf

-- 4. Idris vs Set Theory

function_equality_ex1 : plus 3 = plus (pred 4)
function_equality_ex1 = Refl

functional_extensionality : ((x : a) -> f x = g x) -> f = g
functional_extensionality = really_believe_me

function_equality_ex2 : (\x => plus x 1) = (\x => plus 1 x)
function_equality_ex2 = functional_extensionality $ \x => plusCommutative x 1

-- 4.1.1

rev_append : (l1, l2 : List x) -> List x
rev_append [] l2 = l2
rev_append (x :: xs) l2 = rev_append xs (x :: l2)

tr_rev : (l : List x) -> List x
tr_rev l = rev_append l []

rev : (l : List x) -> List x
rev []       = []
rev (h :: t) = (rev t) ++ [h]

tr_rev_correct : (x : List a) -> tr_rev x = rev x
tr_rev_correct []         = Refl
tr_rev_correct (x :: xs)  =
  rewrite rev_app xs [x] in
  Refl

  where
    app_assoc : (l1, l2, l3 : List t) -> ((l1 ++ l2) ++ l3) = (l1 ++ (l2 ++ l3))
    app_assoc [] l2 l3        = Refl
    app_assoc (n::l1') l2 l3  = rewrite app_assoc l1' l2 l3 in Refl

    rev_app : (l1, l2 : List t) -> rev_append l1 l2 = rev l1 ++ l2
    rev_app [] l2 = Refl
    rev_app (x :: xs) l2 =
      rewrite rev_app xs (x :: l2) in
      rewrite app_assoc (rev xs) [x] l2 in
      Refl

-- 4.2.1

-- TODO

-- 4.2.2

andb_true_iff : (b1, b2 : Bool) -> (b1 && b2 = True) <-> (b1 = True, b2 = True)
andb_true_iff b1 b2 = (andb_true_iff_f b1 b2, andb_true_iff_r b1 b2)
  where
  andb_true_iff_f : (b1, b2 : Bool) -> (b1 && b2 = True) -> (b1 = True, b2 = True)
  andb_true_iff_f True  True  prf = (Refl, Refl)
  andb_true_iff_f False True  prf = absurd prf
  andb_true_iff_f True  False prf = absurd prf
  andb_true_iff_f False False prf = absurd prf

  andb_true_iff_r : (b1, b2 : Bool) -> (b1 = True, b2 = True) -> (b1 && b2 = True)
  andb_true_iff_r True True (Refl, Refl) = Refl
  andb_true_iff_r False _ (Refl, _) impossible
  andb_true_iff_r _ False (_, Refl) impossible

orb_true_iff : (b1, b2 : Bool) -> (b1 || b2 = True) <-> ((b1 = True) `Either` (b2 = True))
orb_true_iff b1 b2 = (orb_true_iff_f b1 b2, orb_true_iff_r b1 b2)
  where
  orb_true_iff_f : (b1, b2 : Bool) -> (b1 || b2 = True) -> ((b1 = True) `Either` (b2 = True))
  orb_true_iff_f True True Refl = Left Refl
  orb_true_iff_f True False Refl = Left Refl
  orb_true_iff_f False True Refl = Right Refl
  orb_true_iff_f False False Refl impossible

  orb_true_iff_r : (b1, b2 : Bool) -> ((b1 = True) `Either` (b2 = True)) -> (b1 || b2 = True)
  orb_true_iff_r True True (Right Refl) = Refl
  orb_true_iff_r True True (Left Refl) = Refl
  orb_true_iff_r False True (Right Refl) = Refl
  orb_true_iff_r True False (Left Refl) = Refl
  orb_true_iff_r True False (Right Refl) impossible
  orb_true_iff_r False True (Left Refl) impossible
  orb_true_iff_r False False (Left Refl) impossible
  orb_true_iff_r False False (Right Refl) impossible

beq_nat_false_iff : (x, y : Nat) -> (x == y = False) <-> (Not (x = y))
beq_nat_false_iff x y = (beq_nat_false_iff_f x y, beq_nat_false_iff_r x y)
  where
  beq_nat_false_iff_f : (x : Nat) -> (y : Nat) -> (x == y = False) -> Not (x = y)
  beq_nat_false_iff_f Z Z     prf     = absurd prf
  beq_nat_false_iff_f (S k) Z prf     = absurd
  beq_nat_false_iff_f Z (S l) prf     = absurd
  beq_nat_false_iff_f (S k) (S j) prf = \eq => beq_nat_false_iff_f k j (predneq k j prf) (predeq k j eq)
    where
    predneq : (a, b : Nat) -> (S a == S b = False) -> (a == b = False)
    predneq a b prf = rewrite prf in Refl

    predeq : (a, b : Nat) -> (S a = S b) -> (a = b)
    predeq a b prf = pred_eq {n=S a} {m=S b} prf

  beq_nat_false_iff_r : (x : Nat) -> (y : Nat) -> Not (x = y) -> (x == y = False)
  beq_nat_false_iff_r Z     Z not     = absurd (not Refl)
  beq_nat_false_iff_r (S k) Z _       = Refl
  beq_nat_false_iff_r Z (S l) _       = Refl
  beq_nat_false_iff_r (S k) (S l) not = succneq k l (beq_nat_false_iff_r k l (\pp => not (succeq k l pp)))
    where
    succeq : (x, y : Nat) -> (x = y) -> (S x = S y)
    succeq x y prf = rewrite prf in Refl

    succneq : (a, b : Nat) -> (a == b = False) -> (S a == S b = False)
    succneq a' b' prf = rewrite prf in Refl

split_and : {b1: Bool} -> {b2 : Bool} -> (b1 && b2 = True) -> (b1 = True, b2 = True)
split_and {b1=True} {b2=True} prf = (Refl, Refl)
split_and {b1=False} {b2=True} prf = absurd prf
split_and {b1=True} {b2=False} prf = absurd prf
split_and {b1=False} {b2=False} prf = absurd prf

-- 4.2.4

beq_list : (beq : a -> a -> Bool) -> (l1, l2 : List a) -> Bool
beq_list beq [] [] = True
beq_list beq (x :: xs) (y :: ys) = beq x y && beq_list beq xs ys
beq_list beq _ _ = False

headDef : (def : t, l : List t) -> t
headDef def []      = def
headDef _ (x :: _)  = x

eq_head : (x, y : List t) -> (z : t) -> (x = y) -> (headDef z x = headDef z y)
eq_head x y z prf = rewrite prf in Refl

tail'' : (l : List t) -> List t
tail'' [] = []
tail'' (x :: xs) = xs

eq_tail : (x, y: List t) -> (x = y) -> (tail'' x = tail'' y)
eq_tail x y prf = rewrite prf in Refl

split_cons : (x : t, xs : List t, y : t, ys : List t) -> (x :: xs = y :: ys) -> (x = y, xs = ys)
split_cons x xs y ys eq = (xy_eq, xs_ys_eq)
  where
    xy_eq : x = y
    xy_eq = rewrite eq_head (x :: xs) (y :: ys) x eq in Refl

    xs_ys_eq : xs = ys
    xs_ys_eq = rewrite eq_tail (x :: xs) (y :: ys) eq in Refl

beq_list_true_iff : (beq : a -> a -> Bool) -> ((a1, a2 : a) -> (beq a1 a2 = True) <-> (a1 = a2)) -> ((l1, l2 : List a) -> (beq_list beq l1 l2 = True) <-> (l1 = l2))
beq_list_true_iff beq f l1 l2 = (beq_list_true_iff_f beq f l1 l2, beq_list_true_iff_r beq f l1 l2)
  where
  beq_list_true_iff_f : (beq : a -> a -> Bool) -> ((a1, a2 : a) -> (beq a1 a2 = True) <-> (a1 = a2)) -> ((l1, l2 : List a) -> (beq_list beq l1 l2 = True) -> (l1 = l2))
  beq_list_true_iff_f beq _ [] [] eq = Refl
  beq_list_true_iff_f beq _ (x :: xs) [] eq = absurd eq
  beq_list_true_iff_f beq _ [] (y :: ys) eq = absurd eq
  beq_list_true_iff_f beq f (x :: xs) (y :: ys) eq =
    let (elem, rest) = split_and eq in
    rewrite (fst (f x y) elem) in
    rewrite (beq_list_true_iff_f beq f xs ys rest) in
    Refl

  beq_list_true_iff_r : (beq : a -> a -> Bool) -> ((a1, a2 : a) -> (beq a1 a2 = True) <-> (a1 = a2)) -> ((l1, l2 : List a) -> (l1 = l2) -> (beq_list beq l1 l2 = True))
  beq_list_true_iff_r beq _ [] [] eq = Refl
  beq_list_true_iff_r beq _ (x :: xs) [] eq = absurd $ disjointL x (sym eq)
  beq_list_true_iff_r beq _ [] (y :: ys) eq = absurd $ disjointL y eq
  beq_list_true_iff_r beq f (x :: xs) (y :: ys) eq =
    rewrite beq_x_y in
    rewrite beq_list_xs_ys in
    Refl

    where cons_eq : (x = y, xs = ys)
          cons_eq = split_cons x xs y ys eq

          beq_x_y : beq x y = True
          beq_x_y = (snd (f x y)) (fst cons_eq)

          beq_list_xs_ys : beq_list beq xs ys = True
          beq_list_xs_ys = beq_list_true_iff_r beq f xs ys (snd cons_eq)

-- 4.2.5

forallb : (test : x-> Bool) -> (l : List x) -> Bool
forallb _ [] = True
forallb test (x :: xs) = test x && forallb test xs

forallb_true_iff : (l : List x) -> (forallb test l = True) <-> (All (\x => test x = True) l)
forallb_true_iff l = (forallb_true_iff_f l, forallb_true_iff_r l)
  where
  forallb_true_iff_f : (l : List x) -> (forallb test l = True) -> (All (\x => test x = True) l)
  forallb_true_iff_f []         Refl = ()
  forallb_true_iff_f (x :: xs)  eqls = let (elem, rest) = split_and eqls in (elem, forallb_true_iff_f xs rest)

  forallb_true_iff_r : (l : List x) -> (All (\x => test x = True) l) -> (forallb test l = True)
  forallb_true_iff_r []         () = Refl
  forallb_true_iff_r (x :: xs)  (elem, rest) =
    rewrite elem in
    rewrite (sym (forallb_true_iff_r xs rest)) in
    Refl

excluded_middle : (p : Type) -> p `Either` (Not p)
excluded_middle p = really_believe_me p

restricted_excluded_middle : (p <-> b = True) -> p `Either` (Not p)
restricted_excluded_middle {b = True} (_, bp) = Left $ bp Refl
restricted_excluded_middle {b = False} (pb, _) = Right $ uninhabited . pb

-- 4.3.2

not_exists_dist : {p : a -> Type} -> Not (x ** Not $ p x) -> ((x : a) -> p x)
not_exists_dist {p} prf x =
  case excluded_middle (p x) of
    Left p    => p
    Right np  => absurd (prf (x ** np))

-- 4.3.3

peirce : ((p -> q) -> p) -> p
peirce {p} func =
  case excluded_middle p of
    Left  prf => prf
    Right not => func (\prf => absurd (not prf))

double_negation_elimination : Not $ Not p -> p
double_negation_elimination {p} notnot =
  case excluded_middle p of
    Left prf  => prf
    Right not => absurd (notnot not)

de_morgan_not_and_not : Not (Not p, Not q) -> p `Either` q
de_morgan_not_and_not notnpnq =
  case (excluded_middle p, excluded_middle q) of
    (Left pp, _) => Left pp
    (_, Left pq) => Right pq
    (Right np, Right nq) => absurd (notnpnq (np, nq))

implies_to_or : (p -> q) -> ((Not p) `Either` q)
implies_to_or {p} func =
  case excluded_middle p of
    Left prf  => Right (func prf)
    Right not => Left not
