Require Extraction.

Require Import basics.

(* Set Extraction Optimize. *)

(* Extract Inductive nat => "Z.t" ["Z.zero" "Z.succ"] "(fun f0 fs n -> if n = Z.zero then f0 () else fs (n-1))". *)

(* Extraction Language OCaml. *)

(* Extraction Library basics. *)

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem plus_n_O' : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    trivial.
  - (* n = S n' *)
    trivial.
Qed.


Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl.
    rewrite <- plus_n_O.
    reflexivity.
  - simpl.
    rewrite <- plus_n_Sm.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem plus_1_neq_0 : forall n : nat,
  eqb (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.


Fixpoint double (n : nat) :=
  match n with
  | 0   => 0
  | S n => S (S (double n))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intro n.
  induction n as [| n IHn].
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intro n.
  induction n as [| n IHn].
  - simpl.
    reflexivity.
  - rewrite -> IHn.
    rewrite -> negb_involutive.
    simpl.
    reflexivity.
Qed.

Theorem mult0_plus : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H : 0 + n = n). {
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.


Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like plus_comm should do the trick! *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrites the wrong plus! *)
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.
