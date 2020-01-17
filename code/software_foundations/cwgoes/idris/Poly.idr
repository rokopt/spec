module Poly

import Prelude

%hide Prelude.List.List
%hide Prelude.List.Nil
%hide Prelude.List.(::)
%hide Prelude.List.length
%hide Prelude.List.filter
%hide Prelude.List.partition
%hide Prelude.Functor.map
%hide Prelude.Nat.pred

%access public export

%default total

data List : (x : Type) -> Type where
  Nil   : List x
  Cons  : x -> List x -> List x

(::) : x -> List x -> List x
(::) = Cons

repeat : (x_ty : Type) -> (x : x_ty) -> (count : Nat) -> List x_ty
repeat x_ty x Z     = Nil
repeat x_ty x (S k) = Cons x (repeat x_ty x k)

test_repeat1 : repeat Nat 4 2 = Cons 4 (Cons 4 Nil)
test_repeat1 = Refl

test_repeat2 : repeat Bool False 1 = Cons False Nil
test_repeat2 = Refl

namespace MumbleGrumble

  data Mumble : Type where
    A : Mumble
    B : Mumble -> Nat -> Mumble
    C : Mumble

  data Grumble : (x : Type) -> Type where
    D : Mumble -> Grumble x
    E : x -> Grumble x

repeat' : {x_ty : Type} -> (x : x_ty) -> (count : Nat) -> List x_ty
repeat' x Z     = Nil
repeat' x (S k) = Cons x (repeat' x k)

repeat'' : (x : x_ty) -> (count : Nat) -> List x_ty
repeat'' x Z     = Nil
repeat'' x (S k) = Cons x (repeat'' x k)

app : (l1, l2 : List x) -> List x
app Nil         l2 = l2
app (Cons h t)  l2 = Cons h (app t l2)

rev : (l : List x) -> List x
rev Nil         = Nil
rev (Cons h t)  = app (rev t) (Cons h Nil)

length : (l : List x) -> Nat
length Nil = Z
length (Cons _ t) = S (length t)

test_rev1 : rev (Cons 1 (Cons 2 Nil)) = Cons 2 (Cons 1 Nil)
test_rev1 = Refl

test_rev2 : rev (Cons True Nil) = Cons True Nil
test_rev2 = Refl

test_length1 : length (Cons 1 (Cons 2 (Cons 3 Nil))) = 3
test_length1 = Refl

list123''' : List Nat
list123''' = [1, 2, 3]

app_nil_r : (l : List x) -> app l [] = l
app_nil_r []          = Refl
app_nil_r (Cons x xs) = rewrite app_nil_r xs in Refl

app_assoc : (l, m, n : List a) -> app l (app m n) = app (app l m) n
app_assoc []        m n = Refl
app_assoc (Cons x xs) m n = rewrite app_assoc xs m n in Refl

app_length : (l1, l2 : List x) -> length (app l1 l2) = length l1 + length l2
app_length []         l2 = Refl
app_length (Cons x xs)  l2 = rewrite app_length xs l2 in Refl

rev_app_distr : (l1, l2 : List x) -> rev (app l1 l2) = app (rev l2) (rev l1)
rev_app_distr [] [] = Refl
rev_app_distr (Cons x xs) [] = rewrite rev_app_distr xs [] in Refl
rev_app_distr [] (Cons y ys) =
  rewrite rev_app_distr [] ys in
  rewrite app_nil_r (rev ys) in
  rewrite app_nil_r (app (rev ys) [y]) in
  Refl
rev_app_distr (Cons x xs) (Cons y ys) =
  rewrite rev_app_distr xs (Cons y ys) in
  rewrite app_assoc (app (rev ys) [y]) (rev xs) [x] in
  Refl

rev_involutive : (l : List x) -> rev (rev l) = l
rev_involutive [] = Refl
rev_involutive (Cons x xs) =
  rewrite rev_app_distr (rev xs) [x] in
  rewrite rev_involutive xs in
  Refl

data Prod : (x, y : Type) -> Type where
  PPair : x -> y -> Prod x y

syntax "(" [x] "," [y] ")" = PPair x y

syntax [x_ty] "*" [y_ty] = Prod x_ty y_ty

fst : (p : x * y) -> x
fst (x, _) = x

snd : (p : x * y) -> y
snd (_, y) = y

zip : (lx : List x) -> (ly : List y) -> List (x * y)
zip []          _           = []
zip _           []          = []
zip (Cons x tx) (Cons y ty) = (x, y) :: zip tx ty

split : (l : List (x * y)) -> (List x) * (List y)
split Nil             = (Nil, Nil)
split (Cons (a, b) t) = let (as, bs) = split t in (Cons a as, Cons b bs)

test_split : (split [(1, False), (2, False)]) = ([1, 2], [False, False])
test_split = Refl

data Option : (x : Type) -> Type where
  Some : x -> Option x
  None : Option x

nth_error : (l : List x) -> (n : Nat) -> Option x
nth_error []          n = None
nth_error (Cons a t)  n = if n == 0 then Some a else nth_error t (pred n)

test_nth_error1 : nth_error [4, 5, 6, 7] 0 = Some 4
test_nth_error1 = Refl

test_nth_error2 : nth_error [[1], [2]] 1 = Some [2]
test_nth_error2 = Refl

test_nth_error3 : nth_error [True] 2 = None
test_nth_error3 = Refl

hd_error : (l : List x) -> Option x
hd_error []         = None
hd_error (Cons x _) = Some x

test_hd_error1 : hd_error [1, 2] = Some 1
test_hd_error1 = Refl

test_hd_error2 : hd_error [[1], [2]] = Some [1]
test_hd_error2 = Refl

doit3times : (f : x -> x) -> (n : x) -> x
doit3times f n = f (f (f n))

test_doit3times : doit3times (\x => pred (pred x)) 9 = 3
test_doit3times = Refl

test_doit3times' : doit3times Bool.not True = False
test_doit3times' = Refl

filter  : (test : x -> Bool) -> (l : List x) -> List x
filter test Nil         = Nil
filter test (Cons h t)  = if test h then Cons h (filter test t) else filter test t

test_filter1 : filter (\x => x == 1) [1, 2, 3] = [1]
test_filter1 = Refl

test_anon_fun' : doit3times (\n => mult n n) 2 = 256
test_anon_fun' = Refl

partition : (test : x -> Bool) -> (l : List x) -> (List x) * (List x)
partition test Nil = (Nil, Nil)
partition test (Cons h t) =
  let (y, n) = partition test t in
  if test h then (Cons h y, n) else (y, Cons h n)

test_partition2 : (partition (\x => False) [5, 9, 0]) = ([], [5, 9, 0])
test_partition2 = Refl

map : (f : x -> y) -> (l : List x) -> List y
map f Nil         = Nil
map f (Cons h t)  = Cons (f h) (map f t)

test_map1 : (map (\x => plus 3 x) [2, 0, 2]) = [5, 3, 5]
test_map1 = Refl

map_rev : (f : x -> y) -> (l : List x) -> map f (rev l) = rev (map f l)
map_rev f []          = Refl
map_rev f (Cons x xs) =
  rewrite (sym (map_rev f xs)) in
  rewrite map_app f (rev xs) (Cons x Nil) in
  Refl

  where map_app : (f : t -> u) -> (l1 : List t) -> (l2 : List t) -> map f (app l1 l2) = app (map f l1) (map f l2)
        map_app f [] l2 = Refl
        map_app f (Cons x xs) l2 = rewrite map_app f xs l2 in Refl

flat_map : (f : x -> List y) -> (l : List x) -> List y
flat_map f []           = []
flat_map f (Cons x xs)  = app (f x) (flat_map f xs)

test_flat_map1 : flat_map (\n => [n, n, n]) [1, 5, 4] = [1,1,1,5,5,5,4,4,4]
test_flat_map1 = Refl

option_map : (f : x -> y) -> (xo : Option x) -> Option y
option_map f None     = None
option_map f (Some x) = Some (f x)

fold : (f : x -> y -> y) -> (l : List x) -> (b : y) -> y
fold f Nil        b = b
fold f (Cons h t) b = f h (fold f t b)

fold_example1 : fold (*) [1, 2, 3, 4] 1 = 24
fold_example1 = Refl

fold_example3 : fold Poly.app [[1],[],[2,3],[4]] [] = [1, 2, 3, 4]
fold_example3 = Refl

constfun : (x : x_ty) -> Nat -> x_ty
constfun x = \k => x

ftrue : Nat -> Bool
ftrue = constfun True

constfun_example1 : ftrue 0 = True
constfun_example1 = Refl

constfun_example2 : (constfun 5) 99 = 5
constfun_example2 = Refl

plus3 : Nat -> Nat
plus3 = plus 3

test_plus3 : plus3 4 = 7
test_plus3 = Refl

test_plus3' : doit3times Poly.plus3 0 = 9
test_plus3' = Refl

test_plus3'' : doit3times (plus 3) 0 = 9
test_plus3'' = Refl

namespace Exercises

  -- 3.0.1

  fold_length : (l : List x) -> Nat
  fold_length l = fold (\_, n => S n) l 0

  test_fold_length1 : fold_length [4, 7, 0] = 3
  test_fold_length1 = Refl

  fold_length_correct : (l : List x) -> fold_length l = length l
  fold_length_correct [] = Refl
  fold_length_correct (Cons x xs) =
    rewrite fold_length_correct xs in
    Refl

  -- 3.0.2

  fold_map : (f : x -> y) -> (l : List x) -> List y
  fold_map f l = fold (\a, x => Cons (f a) x) l []

  fold_map_correct : (f : x -> y) -> (l : List x) -> fold_map f l = map f l
  fold_map_correct f [] = Refl
  fold_map_correct f (Cons x xs) =
    rewrite fold_map_correct f xs in
    Refl

  -- 3.0.3

  prod_curry : (f : (x * y) -> z) -> (x_val : x) -> (y_val : y) -> z
  prod_curry f x_val y_val = f (x_val, y_val)

  prod_uncurry : (f : x -> y -> z) -> (p : x * y) -> z
  prod_uncurry f (x, y) = f x y

  -- 3.0.4

  -- TODO informal proof of nth_error

namespace Church
  Nat' : {x : Type} -> Type
  Nat' {x} = (x -> x) -> x -> x

  one : Nat'
  one f x = f x

  two : Nat'
  two f x = f (f x)

  zero : Nat'
  zero f x = x

  three : Nat'
  three = doit3times

  succ' : (n : Nat' {x}) -> Nat' {x}
  succ' n = \f, x => n f (f x)

  zero_nat : zero S Z = 0
  zero_nat = Refl

  succ_zero : (succ' zero) S Z = zero S 1
  succ_zero = Refl

  succ_one : (succ' one) S Z = one S 1
  succ_one = Refl

  plus' : (n, m : Nat' {x}) -> Nat' {x}
  plus' n m = \f, x => n f (m f x)

  -- Proofs don't really work, Idris doesn't seem to evaluate.

  mult' : (n, m : Nat' {x}) -> Nat' {x}
  mult' n m = \f, x => n (m f) x

  -- Proofs don't really work, Idris doesn't seem to evaluate.

  exp' : (n : Nat' {x}) -> (m : Nat' {x=x->x}) -> Nat' {x}
  exp' n m = m n

  -- Proofs don't really work, Idris doesn't seem to evaluate.
