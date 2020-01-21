module ProofObjects

import Prelude
import Logic
import IndProp

-- 1.0.1

ev_8 : Ev 8
ev_8 = Ev_SS $ Ev_SS $ Ev_SS $ Ev_SS $ Ev_0

-- 1.0.2

ev_plus4 : Ev n -> Ev (4 + n)
ev_plus4 x = Ev_SS $ Ev_SS x

ev_plus2 : Type
ev_plus2 = (n : Nat) -> (e : Ev n) -> Ev (n + 2)

ev_plus2' : Type
ev_plus2' = (n : Nat) -> Ev n -> Ev (n + 2)

data And : (p, q : Type) -> Type where
  Conj : p -> q -> And p q

and_comm : (And p q) <-> (And q p)
and_comm = (\(Conj x y) => Conj y x, \(Conj y x) => Conj x y)

and_comm'_aux : And p q -> And q p
and_comm'_aux (Conj x y) = Conj y x

and_comm' : (And p q) <-> (And q p)
and_comm' {p} {q} = (and_comm'_aux {p} {q}, and_comm'_aux {p=q} {q=p})

-- 3.1.1

conj_fact : And p q -> And q r -> And p r
conj_fact (Conj p _) (Conj _ r) = (Conj p r)

-- 3.2: Disjunction

data Or : (p, q : Type) -> Type where
  IntroL : p -> Or p q
  IntroR : q -> Or p q

-- 3.2.1

or_comm : Or p q -> Or q p
or_comm (IntroL x) = IntroR x
or_comm (IntroR y) = IntroL y

data Ex : (p : a -> Type) -> Type where
  ExIntro : (x : a) -> p x -> Ex p

some_nat_is_even : Ex (\n => Ev n)
some_nat_is_even = ExIntro 4 (Ev_SS $ Ev_SS Ev_0)

-- 3.3.1

ex_ev_Sn : Ex (\n => Ev (S n))
ex_ev_Sn = ExIntro 1 (Ev_SS Ev_0)

-- 3.4

data Unit' : Type where
  Un : Unit'

data Void : Type where

data PropEq : {t : Type} -> t -> t -> Type where
  EqRefl : PropEq x x

syntax [x] "='" [y] = PropEq x y

four : (2 + 2) =' (1 + 3)
four = EqRefl

singleton : ([] ++ [x]) =' (x :: [])
singleton = EqRefl

quiz6 : Ex (\x => (x + 3) =' 4)
quiz6 = ExIntro 1 EqRefl

-- 4.0.1

-- Note: Idris does not seem to rewrite with ='
equality__leibniz_equality : (x = y) -> ((p : t -> Type) -> p x -> p y)
equality__leibniz_equality eq p px = rewrite (sym eq) in px

-- 4.0.2

leibniz_equality__equality : ((p : t -> Type) -> p x -> p y) -> (x = y)
leibniz_equality__equality {x} {y} pxy = pxy ((=) x) Refl
