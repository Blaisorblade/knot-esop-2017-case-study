Set Implicit Arguments.

Require Import LNameless_Isomorphism.
Require Import LNameless_STLC_Iso.
Require Import LN_Template_One_Sort.
Require Export LN_STLC_basic_Definitions.

(** ** Pure Lambda Calculus *)

(** Reference: Chargueraud's POPLmark contribution using Locally Nameless style
   and cofinite quantification *)

(** Many of the generic properties about substitution, environments are
   already proved in a generic
   *)

Notation "[ z ~> u ] t" := (Tfsubst t z u) (at level 68).

(** ** Regularity of relations *)

(** A typing relation holds only if the environment has no
   duplicated keys and the pre-term is locally-closed. *)

Lemma typing_regular : forall E e T,
  typing E e T -> uniq E /\ TwfT e.
Proof.
  split; induction H; eauto; try gconstructor.
  pick_fresh y; forward~ H0 as Huniq; eauto; inversion* Huniq.
Qed.

(** The value predicate only holds on locally-closed terms. *)

Lemma value_regular : forall e,
  value e -> TwfT e.
Proof.
  induction 1; auto*.
Qed.

(** A reduction relation only holds on pairs of locally-closed terms. *)

Lemma TwfT_abs_inv : forall (T:trm),
  TwfT (trm_abs T) ->
  exists L, forall x, x `notin` L -> TwfT (T ^ x).
Proof.
  intros.
  unfold TwfT in * |-; simpl in * |-.
  dependent destruction H.
  dependent destruction H; inversion H0; subst; dependent destruction H1.
  dependent destruction H; intuition. simpl in * |-.
  exists L; intros. 
  generalize (H1 x H2); intro H3; clear H1.
  dependent destruction H3; auto.
  gunfold; auto.  
Qed.  

Lemma red_regular : forall e e',
  red e e' -> TwfT e /\ TwfT e'.
Proof with eauto using value_regular.
  split; induction H; try gconstructor; eauto...
  clear NotInTac NotInTac0.

  generalize (TwfT_abs_inv H); intro H2; inversion H2.
  pick fresh y for (x `union` Tfv t1);destruct_notin.
  assert (TwfT (trm_fvar a)); [gconstructor | idtac].
  rewrite (Tbfsubst_var_intro t1 (trm_fvar a) NotInTac); simpl.
  apply TwfT_Tfsubst; eauto.

  generalize (value_regular H0); intros.
  generalize (TwfT_abs_inv H); intro H2; inversion H2.
  pick fresh y for (x `union` Tfv t1);destruct_notin.
  rewrite (Tbfsubst_var_intro t1 t2 NotInTac); simpl.
  apply TwfT_Tfsubst; auto.
Qed.

