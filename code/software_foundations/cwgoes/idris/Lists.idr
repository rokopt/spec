--totalmodule Lists

import Prelude

%hide Prelude.Basics.fst
%hide Prelude.Basics.snd
%hide Prelude.Nat.pred
%hide Prelude.List.(++)

%access public export
%default total

-- 1. Pairs of Numbers

data NatProd : Type where
  Pair : Nat -> Nat -> NatProd

fst : (p : NatProd) -> Nat
fst (Pair x _) = x

snd : (p : NatProd) -> Nat
snd (Pair _ y) = y

syntax "(" [x] "," [y] ")" = Pair x y

fst' : (p : NatProd) -> Nat
fst' (x, _) = x

snd' : (p : NatProd) -> Nat
snd' (_, y) = y

swap_pair : (p : NatProd) -> NatProd
swap_pair (x, y) = (y, x)

surjective_pairing' : (n, m : Nat) -> (n, m) = (fst (n, m), snd (n, m))
surjective_pairing' n m = Refl

surjective_pairing : (p : NatProd) -> p = (fst p, snd p)
surjective_pairing (n, m) = Refl

-- 1.1

snd_fst_is_swap : (p : NatProd) -> (snd p, fst p) = swap_pair p
snd_fst_is_swap (n, m) = Refl

-- 1.2

fst_swap_is_snd : (p : NatProd) -> fst (swap_pair p) = snd p
fst_swap_is_snd (n, m) = Refl

-- 2. Lists of Numbers

data NatList : Type where
  Nil   : NatList
  (::)  : Nat -> NatList -> NatList

mylist : NatList
mylist = (::) 1 ((::) 2 ((::) 3 Nil))

mylist2 : NatList
mylist2 = [1, 2, 3]

repeat : (n, count : Nat) -> NatList
repeat n Z     = []
repeat n (S k) = n :: repeat n k

length : (l : NatList) -> Nat
length []       = Z
length (h :: t) = S (length t)

app : (l1, l2 : NatList) -> NatList
app []       l2 = l2
app (h :: t) l2 = h :: app t l2

infixr 7 ++

(++) : (x, y : NatList) -> NatList
(++) = app

test_app1 : [1, 2, 3] ++ [4, 5, 6] = [1, 2, 3, 4, 5, 6]
test_app1 = Refl

test_app2 : [] ++ [4, 5] = [4, 5]
test_app2 = Refl

test_app3 : [1, 2, 3] ++ [] = [1, 2, 3]
test_app3 = Refl

hd : (default : Nat) -> (l : NatList) -> Nat
hd default []       = default
hd default (h :: t) = h

tl : (l : NatList) -> NatList
tl []       = []
tl (h :: t) = t

test_hd1 : hd 0 [1, 2, 3] = 1
test_hd1 = Refl

test_hd2 : hd 0 [] = 0
test_hd2 = Refl

test_tl : tl [1, 2, 3] = [2, 3]
test_tl = Refl

-- 2.5.1

nonzeros : (l : NatList) -> NatList
nonzeros []        = []
nonzeros (Z :: xs) = nonzeros xs
nonzeros (n :: xs) = n :: nonzeros xs

test_nonzeros : nonzeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3]
test_nonzeros = Refl

odd : (n : Nat) -> Bool
odd Z         = False
odd (S Z)     = True
odd (S (S n)) = odd n

oddmembers : (l : NatList) -> NatList
oddmembers []        = []
oddmembers (n :: xs) = if odd n then n :: oddmembers xs else oddmembers xs

test_oddmembers : oddmembers [0, 1, 0, 2, 3, 0, 0] = [1, 3]
test_oddmembers = Refl

countoddmembers : (l : NatList) -> Nat
countoddmembers = length . oddmembers

test_countoddmembers1 : countoddmembers [1, 0, 3, 1, 4, 5] = 4
test_countoddmembers1 = Refl

-- 2.5.2

alternate : (l1, l2 : NatList) -> NatList
alternate xs []               = xs
alternate [] ys               = ys
alternate (x :: xs) (y :: ys) = x :: y :: alternate xs ys 

test_alternate1 : alternate [1, 2, 3] [4, 5, 6] = [1, 4, 2, 5, 3, 6]
test_alternate1 = Refl

test_alternate2 : alternate [1] [4, 5, 6] = [1, 4, 5, 6]
test_alternate2 = Refl

test_alternate3 : alternate [1, 2, 3] [4] = [1, 4, 2, 3]
test_alternate3 = Refl

test_alternate4 : alternate [] [20, 30] = [20, 30]
test_alternate4 = Refl

Bag : Type
Bag = NatList

count : (v : Nat) -> (s : Bag) -> Nat
count v []        = 0
count v (x :: xs) = if v == x then 1 + count v xs else count v xs

test_count1 : count 1 [1, 2, 3, 1, 4, 1] = 3
test_count1 = Refl

test_count2 : count 6 [1, 2, 3, 1, 4, 1] = 0
test_count2 = Refl

sum : Bag -> Bag -> Bag
sum x y = x `app` y

test_sum1 : count 1 (sum [1, 2, 3] [1, 4, 1]) = 3
test_sum1 = Refl

add : (v : Nat) -> (s : Bag) -> Bag
add v s = (::) v s

test_add1 : count 1 (add 1 [1, 4, 1]) = 3
test_add1 = Refl

test_add2 : count 5 (add 1 [1, 4, 1]) = 0
test_add2 = Refl

member : (v : Nat) -> (s : Bag) -> Bool
member v []         = False
member v (x :: xs)  = if x == v then True else member v xs

test_member1 : member 1 [1, 4, 1] = True
test_member1 = Refl

test_member2 : member 2 [1, 4, 1] = False
test_member2 = Refl

-- 3.1

app_assoc : (l1, l2, l3 : NatList) -> ((l1 ++ l2) ++ l3) = (l1 ++ (l2 ++ l3))
app_assoc [] l2 l3        = Refl
app_assoc (n::l1') l2 l3  = rewrite app_assoc l1' l2 l3 in Refl

rev : (l : NatList) -> NatList
rev []       = []
rev (h :: t) = (rev t) ++ [h]

test_rev1 : rev [1, 2, 3] = [3, 2, 1]
test_rev1 = Refl

test_rev2 : rev [] = []
test_rev2 = Refl

app_length : (l1, l2 : NatList) -> length (l1 ++ l2) = (length l1) + (length l2)
app_length []         l2 = Refl
app_length (n :: l1') l2 = rewrite app_length l1' l2 in Refl

rev_length : (l : NatList) -> length (rev l) = length l
rev_length []        = Refl
rev_length (n :: l') =
  rewrite app_length (rev l') [n] in
  rewrite plusCommutative (length (rev l')) 1 in
  rewrite rev_length l' in
  Refl

-- 3.3.1

app_nil_r : (l : NatList) -> (l ++ []) = l
app_nil_r []      = Refl
app_nil_r (x::xs) = rewrite app_nil_r xs in Refl

rev_app_distr : (l1, l2 : NatList) -> rev (l1 ++ l2) = (rev l2) ++ (rev l1)
rev_app_distr []      [] = Refl
rev_app_distr (x::xs) [] = rewrite rev_app_distr xs [] in Refl
rev_app_distr [] (y::ys) =
  rewrite rev_app_distr [] ys in
  rewrite app_nil_r (rev ys) in
  rewrite app_nil_r (rev ys ++ [y]) in
  Refl
rev_app_distr (x::xs) (y::ys) =
  rewrite rev_app_distr xs (y::ys) in
  rewrite app_assoc ((rev ys) ++ [y]) (rev xs) [x] in
  Refl

rev_involutive : (l : NatList) -> rev (rev l) = l
rev_involutive []      = Refl
rev_involutive (x::xs) =
  rewrite rev_app_distr (rev xs) [x] in
  rewrite rev_involutive xs in
  Refl

app_assoc4 : (l1, l2, l3, l4 : NatList) -> (l1 ++ (l2 ++ (l3 ++ l4))) = (((l1 ++ l2) ++ l3) ++ l4)
app_assoc4 l1 l2 l3 l4 =
  rewrite app_assoc (l1 ++ l2) l3 l4 in
  rewrite (sym (app_assoc l1 l2 (l3 ++ l4))) in
  Refl

nonzeros_app : (l1, l2 : NatList) -> nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2)
nonzeros_app [] ys =
  Refl
nonzeros_app (Z::xs) ys =
  rewrite nonzeros_app xs ys in
  Refl
nonzeros_app ((S n)::xs) ys =
  rewrite nonzeros_app xs ys in
  Refl

-- 3.3.2

beq_NatList : (l1, l2 : NatList) -> Bool
beq_NatList [] []           = True
beq_NatList (x::xs) []      = False
beq_NatList [] (y::ys)      = False
beq_NatList (x::xs) (y::ys) = if x == y then beq_NatList xs ys else False

test_beq_NatList1 : beq_NatList [] [] = True
test_beq_NatList1 = Refl

test_beq_NatList2 : beq_NatList [1, 2, 3] [1, 2, 3] = True
test_beq_NatList2 = Refl

test_beq_NatList3 : beq_NatList [1, 2, 3] [1, 2, 4] = False
test_beq_NatList3 = Refl

beq_NatList_refl : (l : NatList) -> True = beq_NatList l l
beq_NatList_refl [] = Refl
beq_NatList_refl (x::xs) =
  rewrite beq_NatList_refl xs in
  rewrite eq_reflexive x in
  Refl
  where eq_reflexive : (x : Nat) -> x == x = True
        eq_reflexive Z      = Refl
        eq_reflexive (S n)  = rewrite eq_reflexive n in Refl

-- 3.4.1

count_member_nonzero : (s : Bag) -> lte 1 (count 1 (1 :: s)) = True
count_member_nonzero xs = Refl

ble_n_Sn : (n : Nat) -> lte n (S n) = True
ble_n_Sn Z      = Refl
ble_n_Sn (S n)  = rewrite ble_n_Sn n in Refl

remove_one : Nat -> Bag -> Bag
remove_one n [] = []
remove_one n (x::xs) = if n == x then xs else x :: remove_one n xs

remove_decreases_count : (s : Bag) -> lte (count 0 (remove_one 0 s)) (count 0 s) = True
remove_decreases_count [] = Refl
remove_decreases_count (Z::xs) =
  rewrite ble_n_Sn (count 0 xs) in
  Refl
remove_decreases_count ((S k)::xs) = remove_decreases_count xs

-- 3.4.2

isEq : (a, b : Nat) -> Dec ((a == b) = True)
isEq Z      Z     = Yes Refl
isEq (S k) (S j)  = isEq k j
isEq (S k) Z      = No absurd
isEq Z     (S j)  = No absurd

ifEq : (a : ty) -> (b : ty) -> (cond = True) -> ((if cond then a else b) = a)
ifEq a b prf = rewrite prf in Refl

ifNeq : (a : ty) -> (b : ty) -> (cond = False) -> ((if cond then a else b) = b)
ifNeq a b prf = rewrite prf in Refl

notFalse : (cond : Bool) -> ((cond = True) -> Void) -> (cond = False)
notFalse True prf = absurd (prf Refl)
notFalse False _  = Refl

bag_count_sum : (a : Bag, b : Bag, n : Nat) -> count n a + count n b = count n (sum a b)
bag_count_sum []      bs n = Refl
bag_count_sum (a::as) bs n =
  case isEq n a of
    Yes prf =>
      rewrite ifEq (1 + count n as) (count n as) prf in
      rewrite ifEq (1 + count n (as ++ bs)) (count n (as ++ bs)) prf in
      rewrite bag_count_sum as bs n in
      Refl
    No  con =>
      rewrite ifNeq (1 + count n as) (count n as) (notFalse (n == a) con) in
      rewrite ifNeq (1 + count n (as ++ bs)) (count n (as ++ bs)) (notFalse (n == a) con) in
      rewrite bag_count_sum as bs n in
      Refl

-- 3.4.3

rev_injective : (l1, l2 : NatList) -> rev l1 = rev l2 -> l1 = l2
rev_injective l1 l2 prf =
  rewrite (sym (rev_involutive l1)) in
  rewrite (sym (rev_involutive l2)) in
  rewrite prf in
  Refl

-- 4. Options

data NatOption : Type where
  Some : Nat -> NatOption
  None : NatOption

nth_error : (l : NatList) -> (n : Nat) -> NatOption
nth_error Nil n       = None
nth_error (a :: l') n =
  case n == 0 of
    True  => Some a
    False => nth_error l' (pred n)

test_nth_error_1 : nth_error [4, 5, 6, 7] 0 = Some 4
test_nth_error_1 = Refl

test_nth_error_2 : nth_error [4, 5, 6, 7] 3 = Some 7
test_nth_error_2 = Refl

test_nth_error_3 : nth_error [4, 5, 6, 7] 9 = None
test_nth_error_3 = Refl

nth_error' : (l : NatList) -> (n : Nat) -> NatOption
nth_error' Nil n       = None
nth_error' (a :: l') n =
  if n == 0 then Some a else nth_error' l' (pred n)

option_elim : (d : Nat) -> (o : NatOption) -> Nat
option_elim d (Some k) = k
option_elim d None     = d

-- 4.0.1

hd_error : (l : NatList) -> NatOption
hd_error [] = None
hd_error (x :: xs) = Some x

test_hd_error1 : hd_error [] = None
test_hd_error1 = Refl

test_hd_error2 : hd_error [1] = Some 1
test_hd_error2 = Refl

test_hd_error3 : hd_error [5, 6] = Some 5
test_hd_error3 = Refl

-- 4.0.2

option_elim_hd : (l : NatList) -> (default : Nat) -> hd default l = option_elim default (hd_error l)
option_elim_hd []         default = Refl
option_elim_hd (x :: xs)  default = Refl

-- 5. Partial Maps

data Id : Type where
  MkId : Nat -> Id

beq_id : (x1, x2 : Id) -> Bool
beq_id (MkId n1) (MkId n2) = n1 == n2

-- 5.0.1

beq_id_refl : (x : Id) -> True = beq_id x x
beq_id_refl (MkId n) =
  rewrite eqReflexive n
  in Refl
  where
    eqReflexive : (n : Nat) -> (n == n) = True
    eqReflexive Z = Refl
    eqReflexive (S k) = eqReflexive k

namespace PartialMap

  data PartialMap : Type where
    Empty : PartialMap
    Record : Id -> Nat -> PartialMap -> PartialMap

  update : (d : PartialMap) -> (x : Id) -> (value : Nat) -> PartialMap
  update d x value = Record x value d

  find : (x : Id) -> (d : PartialMap) -> NatOption
  find x Empty = None
  find x (Record y v d') = if beq_id x y then Some v else find x d'

  -- 5.0.2

  update_eq : (d : PartialMap) -> (x : Id) -> (v : Nat) -> find x (update d x v) = Some v
  update_eq d x v =
    rewrite (sym (beq_id_refl x)) in
    Refl

  -- 5.0.3

  update_neq : (d : PartialMap) -> (x, y : Id) -> (o : Nat) -> beq_id x y = False -> find x (update d y o) = find x d
  update_neq d x y o prf =
    rewrite (ifNeq (Some o) (find x d) prf) in
    Refl

  -- 5.0.4

  data Baz : Type where
    Baz1 : Baz -> Baz
    Baz2 : Baz -> Bool -> Baz

  -- Baz has zero elements.
