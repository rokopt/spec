
%default total

data Vec : Nat -> Type -> Type where
  Nil  : Vec 0 a
  (::) : a -> Vec n a -> Vec (S n) a

data Fin : Nat -> Type where
  Z : Fin (S n)
  S : Fin n -> Fin (S n)

lookup : (0 n : Nat) -> Vec n a -> Fin n -> a
lookup (S n) (x :: y) Z = x
lookup (S n) (x :: xs) (S i) = lookup n xs i
