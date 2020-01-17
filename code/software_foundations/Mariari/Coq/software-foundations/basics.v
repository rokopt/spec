Require Extraction.

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday d :=
  match d with
  | monday    => tuesday
  | tuesday   => friday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Compute (2 + 2).


Compute (2 + 3).

Compute (next_weekday  saturday).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof.
  simpl.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Booleans *)

Inductive bool :=
  | true
  | false.

Definition negb b :=
  match b with
  | true  => false
  | false => true
  end.

Definition andb b1 b2 :=
  match b1 with
  | true  => b2
  | false => false
  end.

Definition orb b1 b2 :=
  match b1 with
  | true  => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb b1 b2 :=
  negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. cbn. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. cbn. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. cbn. reflexivity. Qed.

(* FILL IN HERE  Admitted. *)

Check true.

Check negb true.

Inductive rgb :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).


Definition monochrome c :=
  match c with
  | black => true
  | white => true
  | primary q => false
  end.

Compute (S 10) + 2.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O    => O
    | S n' => plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9.
Proof. cbn. reflexivity. Qed.


Fixpoint factorial (n:nat) : nat :=
  match n with
  | 0    => 1
  | S n' => n * factorial n'
  end.


Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O    => false
      | S m' => leb n' m'
      end
  end.

Definition ltb (n m : nat) : bool := leb (S n) m.

Example test_ltb1: (ltb 2 2) = false.
Proof. cbn. reflexivity. Qed.

Example test_ltb2: (ltb 2 4) = true.
Proof. reflexivity. Qed.

Example test_ltb3: (ltb 4 2) = false.
Proof. cbn. reflexivity. Qed.

Theorem plus_0_n : forall n : nat,
    0 + n = n.

Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

Theorem plus_1_l : forall n : nat,
    1 + n = S n.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

Theorem plus_id_example : forall n m : nat,
    n = m -> n + n = m + m.
Proof.
  intros n m P.
  rewrite <- P. (* ← means apply right side not left (by default!) *)
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o nm mo.
  rewrite nm.
  rewrite <- mo.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite plus_O_n.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
    m = S n
    -> m * (1 + n) = m * m.
Proof.
  intros n m mSn.
  rewrite -> plus_1_l.
  rewrite <- mSn.
  reflexivity.
Qed.
