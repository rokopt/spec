module Rel

import Logic
import IndProp
import Prelude

-- Some parts of this chapter are missing, I think.

Relation : Type -> Type
Relation t = t -> t -> Type

-- 1. Basic Properties

Partial_function : (r : Relation t) -> Type
Partial_function {t} r = (x, y1, y2 : t) -> r x y1 -> r x y2 -> y1 = y2

next_nat_partial_function : Partial_function Next_nat
next_nat_partial_function x (S x) (S x) Nn Nn = Refl

le_not_a_partial_function : Not (Partial_function Le)
le_not_a_partial_function f = absurd $ f 0 0 1 Le_n (Le_S Le_n)

-- 1.2

Reflexive : (r : Relation t) -> Type
Reflexive {t} r = (a : t) -> r a a

le_reflexive : Reflexive Le
le_reflexive n = Le_n {n}

-- 1.3

Transitive : (r : Relation t) -> Type
Transitive {t} r = (a, b, c : t) -> r a b -> r b c -> r a c

le_trans : Transitive Le
le_trans _ _ _      lab Le_n        = lab
le_trans a b (S c)  lab (Le_S lbc)  = Le_S $ le_trans a b c lab lbc

-- 1.4

Symmetric : (r : Relation t) -> Type
Symmetric {t} r = (a, b : t) -> r a b -> r b a

le_not_symmetric : Not (Symmetric Le)
le_not_symmetric = ?le_not_symmetric_rhs

Antisymmetric : (r : Relation t) -> Type
Antisymmetric {t} r = (a, b : t) -> r a b -> r b a -> a = b

le_antisymmetric : Antisymmetric Le
le_antisymmetric = ?le_antisymmetric_rhs

-- 1.5

Equivalence : (r : Relation t) -> Type
Equivalence r = (Reflexive r, Symmetric r, Transitive r)

-- 1.6

Order : (r : Relation t) -> Type
Order r = (Reflexive r, Antisymmetric r, Transitive r)

Preorder : (r : Relation t) -> Type
Preorder r = (Reflexive r, Transitive r)

le_order : Order Le
le_order = ?le_order

data Clos_refl_trans : (r : Relation t) -> Relation t where
  Rt_step : r x y -> Clos_refl_trans r x y
  Rt_refl : Clos_refl_trans r x x
  Rt_trans : Clos_refl_trans r x y -> Clos_refl_trans r y z ->
             Clos_refl_trans r x z

-- TODO next_nat_closure_is_le

data Clos_refl_trans_1n : (r : Relation t) -> (x : t) -> t -> Type where
  Rt1n_refl : Clos_refl_trans_1n r x x
  Rt1n_trans : r x y -> Clos_refl_trans_1n r y z -> Clos_refl_trans_1n r x z

rsc_R : r x y -> Clos_refl_trans_1n r x y
rsc_R rxy = Rt1n_trans rxy Rt1n_refl

-- 2.0.1

rsc_trans : Clos_refl_trans_1n r x y -> Clos_refl_trans_1n r y z -> Clos_refl_trans_1n r x z
rsc_trans crxy cryz = ?rsc_trans_rhs

rtc_rsc_coincide : (Clos_refl_trans r x y) <-> (Clos_refl_trans_1n r x y)
rtc_rsc_coincide = ?rtc_rsc_coincide_rhs
