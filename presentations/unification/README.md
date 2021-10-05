# how to run `firstorder.hs` and `staticpattern.hs`

- there are quasiquoters for types/terms (`ty`/`tm`)
  and problems (`pb`)
- metavariables look like `?a`
- base types are `Nat`, `Bool`, `List a`
  (`List` must be applied to something)
- "≐" is written "`===`"
- you can run the unifier like `unify [pb| ... |]`
  - in `firstorder` also `unifyST` for the ST one
- problems, substitutions, terms, errors can be pretty-printed
  with `ppr`

```
$ ghci firstorder.hs
>>> [ty| Nat -> Nat -> List ?a |]
B Nat :-> (B Nat :-> List (V "a"))
>>> ppr it
Nat -> Nat -> List ?a
>>> [pb| Nat === ?a; ?b === List ?b |]
P (fromList [B Nat :?: V "a",V "b" :?: List (V "b")])
>>> ppr $ unify it
metavariable ?b occurs in List ?b
```

```
$ ghci staticpattern.hs
>>> [tm| (?a x, ?b) |]
(Meta (M "a") :@: Bound (V "x")) :&: Meta (M "b")
>>> ppr it
(?a x, ?b)
>>> ppr $ unify [pb| ?a x y === (x, y, y, y); ?b === ?a true false |]
{?a |-> (\x y. (x, y, y, y)); ?b |-> (true, false, false, false)}
```
