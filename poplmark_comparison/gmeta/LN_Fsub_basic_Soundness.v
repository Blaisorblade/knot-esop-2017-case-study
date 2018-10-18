Set Implicit Arguments.

Require Import LibTactics.
Require Import LNameless_Meta.
Require Import LNameless_Isomorphism.
Require Import LNameless_Fsub_Iso.
Require Import LN_Template_Two_Sort.
Require Import LN_Fsub_basic_Infrastructure.


(** ** Fsub Part 1A and 2A *)

(** Reference: Chargueraud's POPL solution using Locally Nameless style
   and cofinite quantification *)

(** * Properties of Subtyping *)

(** "apply_fresh T as x" is used to apply inductive rule which
   use an universal quantification over a cofinite set *)    

Ltac apply_fresh_base_simple lemma gather :=
  let L0 := gather in let L := beautify_fset L0 in
  first [apply (@lemma L) | eapply (@lemma L)].

Ltac apply_fresh_base lemma gather var_name :=
  apply_fresh_base_simple lemma gather;
  try match goal with |- forall _, _ `notin` _ -> _ =>
    let Fr := fresh "Fr" in intros var_name Fr; destruct_notin end.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_atoms x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto*.

(** These tactics help applying a lemma which conclusion mentions
  an environment (E & F) in the particular case when F is empty *)

Ltac get_env :=
  match goal with
  | |- wft ?E _ => E
  | |- sub ?E _ _  => E
  | |- typing ?E _ _ => E
  end.

Tactic Notation "apply_empty_bis" tactic(get_env) constr(lemma) :=
  let E := get_env in rewrite <- (app_nil_1 _ E);
  eapply lemma; try rewrite app_nil_1.

Lemma sub_reflexivity : forall E T,
  okt E -> 
  wft E T -> 
  sub E T T .
Proof.
  introv Ok WI. poses W (type_from_wft WI). gen E.
  induction W; intros; inversions WI; eauto.
  apply_fresh* sub_all as Y.
Qed.

(* ********************************************************************** *)
(** Weakening *)

Lemma sub_weakening : forall E F G S T,
   sub (E ++ G) S T -> 
   okt (E ++ F ++ G) ->
   sub (E ++ F ++ G) S T.
Proof.
  introv Typ. gen_eq (E ++ G) as H. gen E.
  induction Typ; introv EQ Ok; subst; auto.
  (* case: fvar trans *)
  eapply sub_trans_tvar; auto; eapply binds_weaken; auto.
  (* case: all *)
  apply_fresh* sub_all as Y. apply_ih_bind* H0.
Qed.
 
(* ********************************************************************** *)
(** Narrowing and transitivity *)

Section NarrowTrans.

Definition transitivity_on Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Hint Unfold transitivity_on.

Hint Resolve wft_narrow.

Implicit Arguments binds_mid_eq [A x a b E F].

Lemma sub_narrowing_aux : forall Q F E Z P S T,
  transitivity_on Q ->
  sub (E ++ Z ~<: Q ++ F) S T ->
  sub F P Q ->
  sub (E ++ Z ~<: P ++ F) S T.
Proof.
  introv TransQ SsubT PsubQ.
  gen_eq (E ++ Z ~<: Q ++ F) as G. gen E.
  induction SsubT; introv EQ; subst.

  apply sub_top; eauto.

  apply sub_refl_tvar; eauto.

  puts (@okt_narrow E0 F Q).
  elim sub_regular with (E0 ++ Z ~<: Q ++ F) U T; intros; auto.
  case (X == Z); intros EQ; subst.
    assert (bind_sub U = bind_sub Q).
      apply binds_mid_eq with Z F E0; auto.
    inversion H3; subst; clear H3.
    apply (@sub_trans_tvar P).
      apply binds_app_3; auto.
    apply TransQ; auto.
    do_rew <- (app_assoc) (apply_empty* sub_weakening); auto.
  apply* (@sub_trans_tvar U); auto.
  analyze_binds H.
    
  apply sub_arrow; auto.

  apply_fresh* sub_all as Y. apply_ih_bind* H0.
Qed.

Lemma sub_transitivity : forall Q,
  transitivity_on Q.
Proof.
  intro Q. introv SsubQ QsubT. asserts* W (type Q).
  gen E S T. gen_eq Q as Q' eq. gen Q' eq.
  induction W; intros Q' EQ E S SsubQ;
    induction SsubQ; try discriminate; inversions EQ;
      intros T QsubT; inversions QsubT; 
        eauto 4 using sub_trans_tvar.
  (* case: all / top -> only needed to fix well-formedness,
     by building back what has been deconstructed too much *)
  assert (sub E (typ_all S1 S2) (typ_all T1 T2)). 
    apply_fresh* sub_all as y. 
  auto*.
  (* case: all / all *)
  apply_fresh sub_all as Y. auto*. 
  forward~ (H0 Y) as K. apply (K (T2 open_tt_var Y)); auto.
  puts (IHW T1); simpl; apply_empty* (@sub_narrowing_aux T1 E).
Qed.

Lemma sub_narrowing : forall Q E F Z P S T,
  sub F P Q ->
  sub (E ++ Z ~<: Q ++ F) S T ->
  sub (E ++ Z ~<: P ++ F) S T.
Proof.
  intros. 
  apply sub_narrowing_aux with Q; auto.
  apply* sub_transitivity.
Qed.

End NarrowTrans.

(* ********************************************************************** *)
(** Type substitution preserves subtyping *)

Lemma sub_through_subst_tt : forall Q E F Z S T P,
  sub (E ++ Z ~<: Q ++ F) S T ->
  sub F P Q ->
  sub (map (subst_tb Z P) E ++ F) (M_yy.M.Tfsubst S Z P) (M_yy.M.Tfsubst T Z P).
Proof.
  introv SsubT PsubQ.
  gen_eq (E ++ Z ~<: Q ++ F) as G. gen E.
  induction SsubT; introv EQ; subst.
  apply sub_top; eauto.

  apply sub_reflexivity; eauto.

  elim sub_regular with F P Q;
    [intros Hokt Hwft; inversion Hwft as [Hp Hq]; clear Hwft | idtac]; auto.
  elim sub_regular with  (E0 ++ Z ~<: Q ++ F) U T;
    [intros Hokt0 Hwft0; inversion Hwft0 as [Hu Ht]; clear Hwft0 | idtac]; auto.
  gsimpl; simpl_alist in *.
    apply (@sub_transitivity Q).
      apply_empty* sub_weakening.
    pattern Q; rewrite* (@M_yy.M.Tfsubst_no_occur Q X P).
      assert (bind_sub U = bind_sub Q).
        apply binds_mid_eq with X F E0; auto.
      inversion H0; subst; clear H0; auto.
    apply notin_fv_wf with (E:= F); auto.
    apply fresh_mid_tail with (bind_sub Q) E0; auto.
  analyze_binds H.
    apply (@sub_trans_tvar (M_yy.M.Tfsubst U Z P)); auto; simpl.
    replace (bind_sub (M_yy.M.Tfsubst U Z P)) with (subst_tb Z P (bind_sub U)); auto.
  apply sub_trans_tvar with (U:= U); auto.
  pattern U; rewrite* (@M_yy.M.Tfsubst_no_occur U Z P).
  apply notin_fv_wf with (E:= F); auto.
    apply wft_from_env_has_sub with X; auto.
  apply fresh_mid_tail with (bind_sub Q) E0; auto.

  gsimpl; simpl_alist in *; apply sub_arrow.

  gsimpl; simpl_alist in *; apply_fresh* sub_all as X.
   unsimpl (subst_tb Z P (bind_sub T1)).
   do 2 grewrite Ybfsubst_permutation_var_wf; auto.
   apply_ih_map_bind* H0.
Qed.

(* ********************************************************************** *)
(** * Properties of Typing *)

(* ********************************************************************** *)
(** Weakening *)

Lemma typing_weakening : forall E F G e T,
   typing (E ++ G) e T -> 
   okt (E ++ F ++ G) ->
   typing (E ++ F ++ G) e T.
Proof. 
  introv Typ. gen_eq (E ++ G) as H. gen E.
  induction Typ; introv EQ Ok; subst; auto.

  apply_fresh* typing_abs as x. forward~ (H x) as K.
  apply_ih_bind (H0 x); auto.
  apply okt_typ; auto.
  elim typing_regular with (x ~: V ++ E0 ++ G) (e1 open_ee_var x) T1; intros; auto.
  inversion H1; auto.

  apply typing_app with T1; auto.

  apply_fresh* typing_tabs as X. forward~ (H X) as K. 
  apply_ih_bind (H0 X); auto.
  apply okt_sub; auto.
  elim typing_regular with (X ~<: V ++ E0 ++ G) (e1 open_te_var X) (T1 open_tt_var X); intros; auto.
  inversion H1; auto.

  eapply typing_tapp; eauto. eapply sub_weakening; eauto.
  eapply typing_sub; eauto. eapply sub_weakening; eauto.
Qed.

(* ********************************************************************** *)
(** Strengthening *)

Lemma sub_strengthening : forall x U E F S T,
  sub (E ++ x ~: U ++ F) S T ->
  sub (E ++ F) S T.
Proof.
  intros x U E F S T SsubT.
  gen_eq (E ++ x ~: U ++ F) as G. gen E.
  induction SsubT; introv EQ; subst; use wft_strengthen.
  (* case: fvar trans *)
  apply (@sub_trans_tvar U0); auto.
  analyze_binds H.
  (* case: all *)
  apply_fresh* sub_all as X. apply_ih_bind* H0.
Qed.

(************************************************************************ *)
(** Preservation by Type Narrowing *)

Lemma typing_narrowing : forall Q E F X P e T,
  sub F P Q ->
  typing (E ++ X ~<: Q ++ F) e T ->
  typing (E ++ X ~<: P ++ F) e T.
Proof.
  introv PsubQ Typ. gen_eq (E ++ X ~<: Q ++ F) as E'. gen E.
  induction Typ; introv EQ; subst.

  analyze_binds H0; apply typing_var; eauto.

  apply_fresh* typing_abs as y. apply_ih_bind* H0.
  eapply typing_app; eauto.
  apply_fresh* typing_tabs as Y. apply_ih_bind* H0.
  eapply typing_tapp; eauto. eapply (@sub_narrowing Q); eauto.
  eapply typing_sub; eauto. eapply (@sub_narrowing Q); eauto.
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution *)

Lemma typing_through_subst_ee : forall U E F x T e u,
  typing (E ++ x ~: U ++ F) e T ->
  typing F u U ->
  typing (E ++ F) (M_tt.M.Tfsubst e x u) T.
Proof.
  introv TypT TypU. gen_eq (E ++ x ~: U ++ F) as E'. gen E.
  induction TypT; introv EQ; subst; gsimpl; simpl_alist in *.

  assert (bind_typ T = bind_typ U) as Hbind.
    apply binds_mid_eq with x0 F E0; auto.
  inversion Hbind; subst; clear Hbind; auto.
  apply_empty* typing_weakening.

  analyze_binds H0; apply typing_var; eauto.

  apply_fresh* typing_abs as y.
  grewrite Tbfsubst_permutation_var_TTwf; auto.
  apply_ih_bind* H0.

  eapply typing_app; eauto.

  apply_fresh* typing_tabs as Y.
  grewrite noRepr_THbfsubst_permutation_var_1_wf.
  apply_ih_bind* H0.
  elim (term_TTwf (proj32 (typing_regular TypU))); tauto.

  eapply typing_tapp; eauto. eapply sub_strengthening; eauto.

  eapply typing_sub; eauto. eapply sub_strengthening; eauto.
Qed.

(************************************************************************ *)
(** Preservation by Type Substitution *)

Lemma typing_through_subst_te : forall Q E F Z e T P,
  typing (E ++ Z ~<: Q ++ F) e T ->
  sub F P Q ->
  typing (map (subst_tb Z P) E ++ F) (M_yt.M.Tfsubst e Z P) (M_yy.M.Tfsubst T Z P).
Proof.
  introv Typ PsubQ. gen_eq (E ++ Z ~<: Q ++ F) as G. gen E.
  induction Typ; introv EQ; subst; gsimpl; simpl_alist in *.

  analyze_binds H0; apply typing_var; eauto.
    apply binds_app_2.
    replace (bind_typ (M_yy.M.Tfsubst T Z P)) with (subst_tb Z P (bind_typ T)); auto.
  apply binds_app_3.
  rewrite* <- (@M_yy.M.Tfsubst_no_occur T Z P).
  apply notin_fv_wf with (E:= F); auto.
    apply wft_from_env_has_typ with x; auto.
  apply fresh_mid_tail with (bind_sub Q) E0; auto.

  apply_fresh* typing_abs as y.
  unsimpl (subst_tb Z P (bind_typ V)).
  grewrite noRepr_THbfsubst_permutation_var.
  apply_ih_map_bind* H0.

  eapply typing_app; eauto.
  apply IHTyp1; auto.

  apply_fresh* typing_tabs as Y.
    unsimpl (subst_tb Z P (bind_sub V)).
    grewrite THbfsubst_permutation_var_wf; auto.
    grewrite Ybfsubst_permutation_var_wf; auto.
    apply_ih_map_bind* H0. 

  rewrite* <- Ybfsubst_permutation_core_Ywf.
  apply typing_tapp with (M_yy.M.Tfsubst T1 Z P); auto.
  apply sub_through_subst_tt with Q; auto. 

  eapply typing_sub; eauto. eapply sub_through_subst_tt; eauto.
Qed.

(* ********************************************************************** *)
(** * Preservation *)

(* ********************************************************************** *)
(** Inversions for Typing *)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (trm_abs S1 e1) T -> 
  forall U1 U2, sub E T (typ_arrow U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
     typing (x ~: S1 ++ E) (e1 open_ee_var x) S2 /\ sub E S2 U2.
Proof.
  introv Typ. gen_eq (trm_abs S1 e1) as e. gen S1 e1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversions EQ.
  inversions* Sub. use (@sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall E S1 e1 T,
  typing E (trm_tabs S1 e1) T -> 
  forall U1 U2, sub E T (typ_all U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing (X ~<: U1 ++ E) (e1 open_te_var X) (S2 open_tt_var X)
     /\ sub (X ~<: U1 ++ E) (S2 open_tt_var X) (U2 open_tt_var X).
Proof.
  intros E S1 e1 T H. gen_eq (trm_tabs S1 e1) as e. gen S1 e1.
  induction H; intros S1 b EQ U1 U2 Sub; inversion EQ.
  inversions Sub. splits; auto.
   exists T1. let L1 := gather_atoms in exists L1.
   intros Y Fr; destruct_notin. splits; auto. 
   simpl; apply_empty* (@typing_narrowing S1). 
  use (@sub_transitivity T).
Qed. 

(* ********************************************************************** *)
(** Preservation Result *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen e'. induction Typ; introv Red; 
   try solve [ inversion Red ].
  (* case: app *)
  inversions Red; try solve [ eapply typing_app; eauto ].
  destructi (typing_inv_abs Typ1 (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    eapply sub_reflexivity; eauto.
  pick_fresh X; destruct_notin.  
  forward~ (P2 X) as K. destruct K.

  rewrite M_tt.M.Tbfsubst_var_intro with (a:=X); simpl; auto.
  apply_empty (@typing_through_subst_ee V); eauto.  
  eapply (@typing_sub S2); eauto. apply_empty* sub_weakening.
  
  (* case: tapp *)
  inversions Red; try solve [ eapply typing_tapp; eauto ].
  destructi (typing_inv_tabs Typ (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    eapply sub_reflexivity; eauto.
  pick_fresh X; destruct_notin. forward~ (P2 X) as K. destruct K.
  rewrite M_yt.M.Tbfsubst_var_intro with (a:=X); simpl; auto.
  rewrite M_yy.M.Tbfsubst_var_intro with (a:=X); simpl; auto.
  unsimpl (E ++ map (subst_tb X T) empty_env).
  generalize (@typing_through_subst_te T1 nil); simpl; intros; eauto.
  (* case sub *)
  eapply typing_sub; eauto.
Qed.

(* ********************************************************************** *)
(** * Progress *)

(* ********************************************************************** *)
(** Canonical Forms *)

Lemma canonical_form_abs : forall t U1 U2,
  value t -> typing empty_env t (typ_arrow U1 U2) -> 
  exists V, exists e1, t = trm_abs V e1.
Proof.
  introv Val Typ. gen_eq (@empty_env bind) as E.
  gen_eq (typ_arrow U1 U2) as T. gen U1 U2.
  induction Typ; introv EQT EQE; 
   try solve [ inversion Val | inversion EQT | eauto ].
    subst. inversion H. inversion H0. auto*.
Qed.

Lemma canonical_form_tabs : forall t U1 U2,
  value t -> typing empty_env t (typ_all U1 U2) -> 
  exists V, exists e1, t = trm_tabs V e1.
Proof.
  introv Val Typ. gen_eq (@empty_env bind) as E.
  gen_eq (typ_all U1 U2) as T. gen U1 U2.
  induction Typ; introv EQT EQE; 
   try solve [ inversion Val | inversion EQT | eauto ].
    subst. inversion H. inversion H0. auto*.
Qed.

(* ********************************************************************** *)
(** Progress Result *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq (@empty_env bind) as E. poses Typ' Typ.
  induction Typ; intros EQ; subst.
  (* case: var *)
  inversion H0.
  (* case: abs *)
  left*. 
  (* case: app *)
  right. destruct* IHTyp1 as [Val1 | [e1' Rede1']].
    destruct* IHTyp2 as [Val2 | [e2' Rede2']].
      destruct (canonical_form_abs Val1 Typ1) as [S [e3 EQ]].
        subst. exists* (M_tt.M.Tbsubst e3 0 e2). 
  (* case: tabs *)
  left*. 
  (* case: tapp *)
  right. destruct* IHTyp as [Val1 | [e1' Rede1']]. 
    destruct (canonical_form_tabs Val1 Typ) as [S [e3 EQ]]. 
      subst. exists* (M_yt.M.Tbsubst e3 0 T). 
  (* case: sub *)
  auto*.
Qed.



