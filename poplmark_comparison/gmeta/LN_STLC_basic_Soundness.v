Set Implicit Arguments.

Require Import LNameless_Isomorphism.
Require Import LNameless_STLC_Iso.
Require Import LN_Template_One_Sort.
Require Import LN_STLC_basic_Infrastructure.

(** ** Pure Lambda Calculus *)

(** Reference: Chargueraud's POPLmark contribution using Locally Nameless style
   and cofinite quantification *)

(** Many of the generic properties about substitution, environments are
   already proved in a generic
   *)

(** Typing is preserved by weakening. *)

Lemma typing_weaken : forall G E F t T,
  (E ++ G) |= t ~: T ->
    uniq (E ++ F ++ G) ->
    (E ++ F ++ G) |= t ~: T.
Proof.
  intros.
  dependent induction H.

  apply typing_var; auto. 
  apply typing_abs with (L `union` dom (E0 ++ F ++ G));intros.
  destruct_notin.
  rewrite ass_app.
  apply H0;auto.
  rewrite app_ass;auto.
  apply typing_app with S; auto.
Qed.

(** Typing is preserved by substitution. *)

Lemma typing_subst : forall F U E t T z u,
  (E ++ z ~ U ++ F) |= t ~: T ->
    F |= u ~: U ->
      (E ++ F) |= [z ~> u]t ~: T.
Proof.
  intros; dependent induction H; gsimpl. 
  rewrite <- app_nil_1 with (l := E0).
  rewrite app_assoc.
  rewrite (binds_mid_eq _ _ _ _ _ _ H0 H).
  apply typing_weaken; auto.
  simpl. apply uniq_remove_mid with (x ~ U); auto.
  constructor; eauto using binds_remove_mid. 

  apply typing_abs with (L `union` {{ z }}); intros; destruct_notin.
  rewrite ass_app.
  generalize Tbfsubst_permutation_var_wfT; intro; simpl in *.
  rewrite H3; eauto.
  rewrite <- cons_app_assoc.
  apply H0 with (U1 := U0); auto.
  elim typing_regular with F u U0; auto.
  apply typing_app with S.
  eapply IHtyping1 ; eauto.
  apply IHtyping2 with U; auto.
Qed.

(** Preservation (typing is preserved by reduction). *)

Lemma preservation_result : preservation.
Proof.
  unfold preservation.
  intros.
  generalize dependent t'.
  induction H; intros.
  inversion H1.
  inversion H1.

  inversion H1.
  subst t1.
  inversion H.
  pick fresh x for (L `union` (Tfv t0));destruct_notin.
  rewrite Tbfsubst_var_intro with (a:=x);auto using value_regular.
  (* rewrite subst_intro_ with (x:=x);auto using value_regular. *)
  assert (E = nil ++ E).
  simpl;auto.
  rewrite H11.
  apply typing_subst with (U:=S);simpl;simpl_alist;auto.
  apply typing_app with S;auto.
  apply typing_app with S;auto.
Qed.

(** Progress (a well-typed term is either a value or it can 
  take a step of reduction). *)

Lemma progress_result : progress.
Proof.
  unfold progress.
  intros t0 T. gen_eq (empty_env : env typ) as E.
  intros.
  induction H0.
  subst E; inversion H1.
  left; constructor.
  gconstructor with L.
  intros; elim typing_regular with (E:= (a, U) :: E) (e:= t1 ^ a) (T := T);
    auto.
  right.
  destruct IHtyping1 as [Val1 | [t1' Red1]]; destruct IHtyping2 as [Val2 | [t2' Red2]]; auto.
  inversion H0_; subst; inversion Val1.
  exists (t0 ^^ t2).
  apply red_beta; auto.
  exists (trm_app t1 t2'); constructor 3; auto.
  exists (trm_app t1' t2); constructor 2; auto using value_regular.
  exists (trm_app t1' t2); constructor 2; auto.
  elim typing_regular with E t2 S; auto.
Qed.

