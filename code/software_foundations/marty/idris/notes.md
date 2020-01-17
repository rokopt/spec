# Wednesday, January 8, 2020

Going through more exercises in software foundation idris:

```
> beq_NatList : (l1, l2 : NatList) -> Bool
> beq_NatList [] [] =True
> beq_NatList [] (k :: x) =False
> beq_NatList (k :: x) [] = True
> beq_NatList (k :: x) (j :: y) = if lte j k then beq_NatList x y else False

> test_beq_NatList1 : beq_NatList Nil Nil = True
> test_beq_NatList1 = Refl

> test_beq_NatList2 : beq_NatList [1,2,3] [1,2,3] = True
> test_beq_NatList2 = Refl

> test_beq_NatList3 : beq_NatList [1,2,3] [1,2,4] = False
> test_beq_NatList3 = Refl

> beq_NatList_refl : (l : NatList) -> True = beq_NatList l l
> beq_NatList_refl [] = Refl
> beq_NatList_refl (k :: x) = let inductiveHypothesis = beq_NatList_refl x in
>   rewrite inductiveHypothesis in Refl
```

with error:
```
When checking right hand side of beq_NatList_refl with expected type
        True = beq_NatList (k :: x) (k :: x)

When checking an application of function rewrite__impl:
        Type mismatch between
                if lte k k then beq_NatList x x else False =
                if lte k k then beq_NatList x x else False (Type of Refl)
        and
                (\replaced =>
                   replaced =
                   if lte k k then beq_NatList x x else False) (beq_NatList x
                                                                            x) (Expected type)
        
        Specifically:
                Type mismatch between
                        if lte k k then beq_NatList x x else False
                and
                        beq_NatList x x
```

But lte k k is True obviously! So the first one should rewrite to beq_NatList x x!!!

# Monday, January 13, 2020

## Tasks

It seems I need to proof that `if p then x else y` simplifies to `x` when `p=True`! 

```
>   update_eq : (d : PartialMap) -> (x : Id) -> (v : Nat) ->
>               find x (update d x v) = Some v
>   update_eq d (MkId Z) v = Refl
>   update_eq d (MkId (S k)) v = rewrite beq_id_refl (MkId (S k)) in Refl
```
or `rewrite beq_id_refl x in Refl`

result in errors:

```
Lists.lidr:1026:34-73:
     |
1026 | >   update_eq d (MkId (S k)) v = rewrite beq_id_refl (MkId (S k)) in Refl
     |                                  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When checking right hand side of update_eq with expected type

        find (MkId (S k)) (update d (MkId (S k)) v) = Some v

rewriting True to Prelude.Nat.Nat implementation of Prelude.Interfaces.Eq, method == k
                                                                                     k did not change type if Prelude.Nat.Nat implementation of Prelude.Interfaces.Eq, method == k k
                                                                                                             then Some v
                                                                                                             else find (MkId (S k)) d =
                                                                                                           Some v
```

# Tuesday, January 14, 2020

## Tasks

Idris doesn't know `app` is equivalent to `++`?

```
> app : (l1, l2 : List x) -> List x
> app Nil l2 = l2
> app (h::t) l2 = h :: app t l2

> rev_involutive : (l : List x) -> rev (rev l) = l
> rev_involutive [] = Refl
> rev_involutive (y :: xs) = --?rhsrev_involutive
>   let inductiveHypothesis = rev_involutive xs in
>     rewrite rev_app_distr (rev xs) [y] in rewrite inductiveHypothesis in Refl
```
gives error
```
Poly.lidr:403:5-404:79:
    |
403 | >   let inductiveHypothesis = rev_involutive xs in
    |     ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ...
When checking right hand side of rev_involutive with expected type
        rev (rev (y :: xs)) = y :: xs

rewriting rev (rev xs ++ [y]) to y :: rev (rev xs) did not change type rev (app (rev xs) [y]) = y :: xs
```

My deduction was correct! Replacing `rev`'s definition with `++` instead pf `app` made the below proof work!

> rev : (l : List x) -> List x
> rev [] = []
> rev (h::t) = (rev t) ++ (h::Nil)

> rev_involutive : (l : List x) -> rev (rev l) = l
> rev_involutive [] = Refl
> rev_involutive (y :: xs) = 
>   let inductiveHypothesis = rev_involutive xs in
>     rewrite rev_app_distr (rev xs) [y] in rewrite inductiveHypothesis in Refl

# Wednesday, January 15, 2020

## Tasks
Going through Idris software foundation Logic chapter. Idris is running quite slow when importing 3 or so modules of the earlier chapters. Proof search also is quite broken.


> and_exercise : (n, m : Nat) -> n + m = 0 -> (n = 0, m = 0)
> and_exercise Z m prf = (Refl,rewrite prf in Refl)
> and_exercise (S _) m prf = (,?rhs_22)
> and_exercise n Z prf = (rewrite plus_n_Z n in prf,Refl)
> and_exercise Z Z prf = (Refl,Refl)


when n > 0 it is impossible to proof that n = 0, but idris won't accept that.
Also, it says that I haven't proved some cases if I don't mention S _!!! So I dunno what to do! Tried `void`, `absurd`, and `impossible`. None of them work.

Also tried saying that prf  (n+m = 0) is impossible

> and_exercise (S _) _ impossible
 
Got error:

Type checking ./Logic.lidr
Logic.lidr:150:24-33:
    |
150 | > and_exercise (S _) _ impossible
    |                        ~~~~~~~~~~
and_exercise (S _) _ is a valid case

OK got it, you have to write that prf is Refl first and then said it's impossible. This is accepted:

> and_exercise : (n, m : Nat) -> n + m = 0 -> (n = 0, m = 0)
> and_exercise Z m prf = (Refl,rewrite prf in Refl)
> and_exercise (S _) m (Refl) impossible

From ch6 of software foundations in idris, part 4, it describes that some proofs are awkward because Idris doesn't have built in extentional equality and excluded middle. It suggested using `really_believe_me` for proofs that require those. Note that `really_believe_me` is just a hole that we tell idris to not bug us about. It's not ideal. The proof search function does not work well also. I'm moving away from Idris and exploring Agda to see if we can do better with that. Next target would be Coq.