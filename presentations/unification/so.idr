
data So : Bool -> Type where Oh : So True
  -- in Data.So in the stdlib
  -- i don't know why the data constructor is called "oh!"

total
safeDiv : (x, y : Integer) -> (prf : So (y /= 0)) -> Integer
safeDiv x y prf with (y /= 0)
  safeDiv x y Oh | False impossible
  safeDiv x y Oh | True = x `div` y

ok : safeDiv 4 2 Oh = 2
-- bad : safeDiv 4 0 Oh = ?
