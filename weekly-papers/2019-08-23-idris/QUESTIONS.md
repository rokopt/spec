Discussion Questions:

- General thoughts on the paper, any questions
- Comparisions to Juvix
- `Type` stands for type of type. Can it go deeper? E.g. what is type of `Type`? Does it have universes? (the answer is further down the paper in 3.1 TT syntax)
- In vector declaration, the type variable `a` on first line appears only as the type `Type` (it is not named `a`). Does the name `a` have to be the same in different constructors?
```idris
data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a
```
