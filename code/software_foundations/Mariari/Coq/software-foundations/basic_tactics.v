
Require Coq.Lists.List.

Import Coq.Lists.List.

Import ListNotations.

Require Import basics.
Require Import lists.

Theorem silly1 : forall (n m o p : nat),
    n = m
    -> [n;o] = [n;p]
    -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

(* Theorem silly2 : forall (n m o p : nat), *)
(*    (q,q) = (r,r) -> [q] = [r] -> *)
(*      [n] = [m]. *)
(* Proof. *)
(*   intros n m eq1 eq2. *)
(*   apply eq2. *)
(*   apply eq1. *)
(* Qed. *)

Theorem silly3_firsttry : forall n : nat,
    true = (eqb n 5)
    -> (eqb (S (S n)) 7) = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l'
     -> l' = rev l.
Proof.
  intros l l' H.
  rewrite -> H.
  symmetry.
  apply rev_involutive.
Qed.

Search rev.


Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.


Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c;d]). (* ( m := ) is often not needed! *)
  apply eq1.
  apply eq2.
Qed.


Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.


Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j
    -> y :: l = x :: j
    -> x = y.
Proof.
  intros X x y z l j H1 H2.
  injection H2 as xeqY.
  rewrite -> xeqY.
  reflexivity.
Qed.


Theorem eqb_0_l : forall n,
   eqb 0 n = true -> n = 0.
Proof.
  intros n.

(** We can proceed by case analysis on [n]. The first case is
    trivial. *)

  intros H.
  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity.

(** However, the second one doesn't look so simple: assuming [0
    =? (S n') = true], we must show [S n' = 0]!  The way forward is to
    observe that the assumption itself is nonsensical: *)

  - (* n = S n' *)
(** If we use [discriminate] on this hypothesis, Coq confirms
    that the subgoal we are working on is impossible and removes it
    from further consideration. *)
    discriminate H.
Qed.

Theorem discriminate_ex1 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.


Theorem S_inJ : forall (n m : nat) (b : bool),
    eqb (S n) (S m) = b
    -> eqb n m = b.
Proof.
  intros.
  simpl in H.
  apply H.
Qed.


Theorem silly3' : forall (n : nat),
  (eqb n 5 = true -> eqb (S (S n)) 7 = true) ->
  true = (eqb n 5)  ->
  true = eqb (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.  Qed.

(** * An Aside in using Q *)

(* Require Coq.QArith.QArith_base. *)

(* Import Coq.QArith.QArith_base. *)

(* Theorem div_same_plus_m : forall n m, *)
(*     ~ n == 0 *)
(*     -> (n / n) + m == 1 + m. *)
(* Proof. *)
(*   intros n m. *)
(*   rewrite Qplus_inj_r. *)
(*   apply Qmult_inv_r. *)
(* Qed. *)

(* ################################################################# *)
(** * Back to your regularly scheduled lesson *)

Require Import basics.


(* Here I am doing induction for all n for a specific m, so it ends horribly *)
(* Theorem double_injective_FAILED : forall n m, *)
(*       n + n = m + m -> *)
(*      n = m. *)
(* Proof. *)
(*   intros n m. induction n as [| n']. *)
(*   - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E. *)
(*     + (* m = O *) refl. *)
(*     + (* m = O *) discriminate eq. *)
(*     + (* m = S m' *) apply f_equal. *)
(* Abort. *)

Search map.

Theorem double_injective : forall n m,
    n + n = m + m
    -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  - (* n = O *)
    simpl.
    intros m eq.
    destruct m as [| m'] eqn:E.
    + (* m = O *)
      reflexivity.
    + (* m = S m' *)
      discriminate eq.
  - (* n = S n' *)
    simpl.
    intros m eq.
    destruct m as [| m'] eqn:E.
    + discriminate eq.
    + f_equal.
      apply IHn'.
      simpl in eq. (* not needed, but shows it better *)
      do 2 rewrite <- Peano.plus_n_Sm in eq.
      injection eq as goal.
      apply goal.
Qed.


Definition sillyfun (n : nat) : bool :=
  if eqb n 3 then false
  else if eqb n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (eqb n 3) eqn:E1.
  - (* n =? 3 = true *)
    reflexivity.
  - (* n =? 3 = false *)
    destruct (eqb n 5) eqn:E2.
    + (* n =? 5 = true *) reflexivity.
    + (* n =? 5 = false *) reflexivity.
Qed.

Search combine.

Check combine.


Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.


Lemma eq_remove_cons : forall (X:Type) (l1 l2: list X) (x: X),
  l1 = l2 -> x :: l1 = x :: l2.
Proof.
  intros X l1 l2 x H.
  apply (f_equal (cons x)) in H.
  apply H.
Qed.

Lemma empty : forall (A : Type) (x : A) (xs : list A),
    [x] = x :: xs -> xs = [].
Proof.
  intros.
  destruct xs.
  - reflexivity.
  - discriminate H.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
    split l = (l1, l2)
    -> combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| [x y] ns IHn].
  - intros l1 l2 H.
    simpl in H.
    inversion H.
    simpl.
    reflexivity.
  - intros l1 l2 H.
    simpl in H.
    (** Copying proofs *)
    (* pose proof H as H'. *)
    (* apply (f_equal fst) in H'. *)
    (* simpl in H'. *)
    (* rewrite <- H'. *)
    destruct split eqn:E1 in H.
    inversion H.
    simpl.
    f_equal.
    apply IHn.
    apply E1.
Qed.
