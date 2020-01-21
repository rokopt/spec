
Theorem surjective_pairing : forall (p : prod nat nat),
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Variable A : Type.
Variable B : Type.

Definition swap_pair (p : prod A B) := (snd p, fst p).

Theorem snd_fst_is_swap : forall (p : prod A B),
  (snd p, fst p) = swap_pair p.
Proof.
  intro p.
  destruct p as [f s].
  simpl.
  reflexivity. (* can I reduce swap_pair somehow.. Ιknow reflexivity does it *)
Qed.

Theorem fst_swap_is_snd : forall (p : prod A B),
  fst (swap_pair p) = snd p.
Proof.
  intro p.
  destruct p as [f s].
  simpl.
  reflexivity.
Qed.


Require Coq.Lists.List.

Import Coq.Lists.List.

Import ListNotations.

Check [1; 2].

Compute (hd []).

Theorem tl_length_pred : forall (A : Type) (l : list A),
  pred (length l) = length (tl l).
Proof.
  intros A l.
  destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    cbn.
    reflexivity.
Qed.

Theorem app_assoc : forall (A : Type) (l1 l2 l3 : list A),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros A l1 l2 l3.
  induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    simpl.
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.

Search map.

Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C) l,
  map g (map f l) = map (fun x => g (f x)) l.
Proof.
  induction l.
  - (* l = nil *)
    simpl.
    reflexivity.
  - (* l = cons n l *)
    simpl.
    rewrite IHl.
    reflexivity.
Qed.


Theorem app_nil_r : forall (A : Type) (l : list A),
  l ++ [] = l.
Proof.
  intros A l.
  induction l as [| n l IHl].
  - reflexivity.
  - simpl.
    rewrite -> IHl.
    reflexivity.
Qed.


Theorem rev_involutive : forall (A : Type) (l : list A),
  rev (rev l) = l.
Proof.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    (* exercise in using assert! *)
    assert (rev_dist : forall (A : Type) (l1 l2 : list A), rev (l1 ++ l2) = rev l2 ++ rev l1).
    + intros A l1 l2.
      induction l1 as [| n l1 IHl1].
      * (* l1 = nil *)
        simpl.
        rewrite -> app_nil_r.
        reflexivity.
      * (* l1 = cons n l1 *)
        simpl.
        rewrite -> IHl1.
        rewrite app_assoc.
        reflexivity.
    + rewrite -> rev_dist.
      simpl.
      rewrite IHl.
      reflexivity.
Qed.


Check (cons 3 (nil)).
