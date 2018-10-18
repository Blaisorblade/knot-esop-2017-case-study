Set Implicit Arguments.

Require Export Arith Max.

(** Some basic properties about max. *)

Lemma S_plus_1 : forall (n:nat), S n = n + 1.
Proof.
  intro n; rewrite plus_comm; reflexivity.
Qed.

Lemma le_max_S_l : forall n m : nat, max n m <= max (S n) m.
Proof.
  induction n; simpl; intros; destruct m; auto with arith.
  destruct m; apply le_n_S.
  rewrite max_l; auto with arith.
  rewrite max_SS; auto.
Qed.

Lemma le_max_S_r : forall n m : nat, max n m <= max n (S m).
Proof.
  induction n; simpl; intros; auto with arith.
  destruct m; auto with arith.
Qed.

Hint Resolve S_plus_1 le_max_S_l le_max_S_r : arith.

Lemma lt_max_S_l : forall n m : nat, n < S (max n m).
Proof.
  intros; auto with arith.
Qed.

Lemma lt_max_S_r : forall n m : nat, m < S (max n m).
Proof.
  intros; auto with arith.
Qed.

Lemma lt_max_SS_l : forall n m : nat, n < S (max n (S m)).
Proof.
  intros; auto with arith.
Qed.

Lemma lt_max_SS_r : forall n m : nat, m < S (max n (S m)).
Proof.
  intros; auto with arith.
Qed.

Hint Resolve lt_max_S_l lt_max_S_r lt_max_SS_l lt_max_SS_r : arith.

Lemma max_lt_1 : forall n m k : nat, max n m < k -> n < k.
Proof.
  intros; apply le_lt_trans with (max n m); auto with arith.
Qed.

Lemma max_lt_2 : forall n m k : nat, max n m < k -> m < k.
Proof.
  intros; apply le_lt_trans with (max n m); auto with arith.
Qed.

Hint Resolve max_lt_1 max_lt_2 lt_S_n: arith.

Lemma lt_S_max_l : forall n m k :nat, S (max n m) < S k -> n < k.
Proof.
  intros; cut (max n m < k); eauto 2 with arith. 
Qed.

Lemma lt_S_max_r : forall n m k :nat, S (max n m) < S k -> m < k.
Proof.
  intros; cut (max n m < k); eauto 2 with arith.
Qed.

Hint Resolve lt_S_max_l lt_S_max_r: arith.

Lemma lt_SS_max_l : forall n m k :nat, S (max n (S m)) < S k -> n < k.
Proof.
  intros; eauto 2 with arith.
Qed.

Lemma lt_SS_max_r : forall n m k :nat, S (max n (S m)) < S k -> m < k.
Proof.
  intros; eauto 2 with arith.
Qed.

Hint Resolve lt_SS_max_l lt_SS_max_r : arith.
Hint Resolve lt_n_O : arith.


