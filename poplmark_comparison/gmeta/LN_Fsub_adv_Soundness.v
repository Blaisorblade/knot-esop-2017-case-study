Set Implicit Arguments.

Require Import LibTactics.
(* Require Import LibTactics_chargueraud. *)

Require Import LNameless_Meta.
Require Import LNameless_Isomorphism.
Require Import LNameless_Fsub_Iso.
Require Export LN_Template_Two_Sort.
Require Export LN_Fsub_adv_Infrastructure.


(* ************************************************************ *)
(** ** Fsub Part 1A and 2A *)

(** Reference: Chargueraud's POPL solution using Locally Nameless style
   and cofinite quantification *)


(* ********************************************************************** *)
(** * Properties of Subtyping *)

(* ********************************************************************** *)
(** Reflexivity *)

Lemma sub_reflexivity : forall E F T,
  M_yy.Ywf_env E -> 
  M_yy.YTenvT E F T -> 
  sub E F T T .
Proof.
  introv Ok WI. assert_concrete. poses W (M_yy.YenvT_YwfT WI).
  clear WI. assert_concrete. gen E.
  induction H0; intros E Hwf Hwft; auto; inversion Hwft; subst. 
  apply sub_arrow; auto.

  apply sub_all with (L `union` dom E `union` L0); auto; intros;
    destruct_notin; subst.
  apply H1; auto.
  generalize (wft_YTenvT H6); intro.
  unfold M_yy.Ywf_env; simpl. simpl_alist; constructor; auto.
  to_gen; generalize (H7 X NotInTac0); intro.
  generalize (wft_YTenvT H3); intro.
  generalize (wft_YTenvT H6); intro.
  apply M_yy.YTenvT_narrow_left with V; auto.
  constructor; auto using uniq_from_Ywf_env. 
Qed.  

(* ********************************************************************** *)
(** Weakening *)

Lemma sub_weakening : forall E F G F0 S T,
   sub (E ++ G) F0 S T -> 
   M_yy.Ywf_env (E ++ F ++ G) ->
   sub (E ++ F ++ G) F0 S T.
Proof.
  introv Typ. gen_eq (E ++ G) as H. gen E.
  induction Typ; introv EQ Ok; subst.
  (* sub_top *)
  constructor; auto using M_yy.TenvT_weaken, uniq_from_Ywf_env. 
  (* sub_refl_var *)
  constructor 2; auto using M_yy.TenvT_weaken, uniq_from_Ywf_env. 
  (* sub_trans_tvar *)
  apply sub_trans_tvar with U; auto.
  (* sub_arrow *)
  apply sub_arrow; auto.
  (* sub_all *)
  apply sub_all with (L `union` dom (E0 ++ F ++ G)); auto; intros; destruct_notin.
  do_rew <- app_assoc (apply H0); auto.
  apply Ywf_env_cons; auto.
  apply M_yy.TenvT_weaken; auto using uniq_from_Ywf_env.
  change (M_yy.YTenvT (E0 ++ G) F0 T1); auto.
Qed.

(* ********************************************************************** *)
(** Narrowing and transitivity *)

Section NarrowTrans.

  Definition transitivity_on Q := forall E F S T,
    sub E F S Q -> sub E F Q T -> sub E F S T.

  Hint Unfold transitivity_on.

  Hint Resolve M_yy.YTenvT_narrow.

  Lemma sub_narrowing_aux : forall Q F E Z P S T F0,
    transitivity_on Q ->
    sub (E ++ Z ~ Q ++ F) F0 S T ->
    sub F F0 P Q ->
    sub (E ++ Z ~ P ++ F) F0 S T.
  Proof.
    introv TransQ SsubT PsubQ.
    gen_eq (E ++ Z ~ Q ++ F) as G. gen E.
    induction SsubT; introv EQ; subst.
    (* sub_top *)
    apply* sub_top.
      apply Ywf_env_narrow with Q; auto.
    apply M_yy.YTenvT_narrow with Q; eauto using uniq_dom_only, uniq_from_Ywf_env.
    (* sub_refl_tvar *)
    apply* sub_refl_tvar.
      apply Ywf_env_narrow with Q; auto.
    apply M_yy.YTenvT_narrow with Q; eauto using uniq_dom_only, uniq_from_Ywf_env.
    (* sub_trans_var *)
    elim sub_regular with (E0 ++ [(Z, Q)] ++ F) F0 U T; intros; auto.
    inversion H1; clear H1.
    generalize (uniq_from_Ywf_env H0); intro.
    case (X == Z); intros EQ; subst.
      generalize (binds_mid_eq _ _ _ _ _ _ H H1); intro.
      apply* (@sub_trans_tvar P); auto.
      generalize (@sub_weakening nil); simpl; intro.
      apply* TransQ; simpl_alist in *.
        do_rew <- app_assoc (apply H5; auto).
        apply Ywf_env_narrow with Q; auto.
      subst.
      apply IHSsubT; auto.
    (* X <> Z *)
    analyze_binds H.
      apply* sub_trans_tvar; eauto using binds_app_2.
    apply* sub_trans_tvar; eauto using binds_app_3.
    (* sub_arrow *)
    apply sub_arrow; auto.
    (* sub_all *)
    apply sub_all with L; auto; intros; rewrite <- app_assoc; auto.
  Qed.

  Lemma sub_transitivity : forall Q,
    transitivity_on Q.
  Proof.
    intro Q; introv SsubQ QsubT.

    asserts W (type Q).
      to_gen. apply M_yy.YenvT_YwfT with E; auto.      
    gen E F S T. gen_eq Q as Q' eq. gen Q' eq.
    induction W; intros Q' EQ E F S SsubQ;
      induction SsubQ; try discriminate; inversions EQ;
        intros T' QsubT; inversions QsubT; 
          eauto 4 using sub_trans_tvar.

    apply sub_top; auto. clear H2. from_gen.
    apply wft_all with (L `union` L0 `union` dom E) T1; auto.
    intros; destruct_notin.
    generalize (H1 X NotInTac); intro.
    elim sub_regular with ([(X, T1)] ++ E) F (M_yy.M.Tbsubst S2 0%nat (typ_fvar X))
      (M_yy.M.Tbsubst T2 0%nat (typ_fvar X));tauto.

    clear H2 IHSsubQ.
    apply sub_all with (L `union` L0 `union` L1); auto*.
    intros; destruct_notin.
    apply H0 with (X:=X)(Q':=M_yy.M.Tbsubst T2 0 (typ_fvar X)); simpl_alist; auto.
    generalize (@sub_narrowing_aux T1 E nil X); simpl; intro.
    apply H3; simpl_alist; auto.
    unfold transitivity_on; intros; eauto 2 using IHW.
  Qed.

  Lemma sub_narrowing : forall Q E F Z P S T F0,
    sub F F0 P Q ->
    sub (E ++ Z ~ Q ++ F) F0 S T ->
    sub (E ++ Z ~ P ++ F) F0 S T.
  Proof.
    intros. 
    apply sub_narrowing_aux with Q; auto.
    apply* sub_transitivity.
  Qed.

End NarrowTrans.

(* ********************************************************************** *)
(** Type substitution preserves subtyping *)

Lemma sub_through_subst_tt : forall Q E F Z S T P F0,
  sub (E  ++ Z ~ Q ++ F) F0 S T ->
  sub F F0 P Q ->
  sub (map (fun U => M_yy.M.Tfsubst U Z P) E ++ F) (map (fun U => M_yy.M.Tfsubst U Z P) F0)
  (M_yy.M.Tfsubst S Z P) (M_yy.M.Tfsubst T Z P).
Proof.
  introv SsubT PsubQ.
  generalize (sub_regular PsubQ); intro Hsub;
    inversion Hsub as [Hsub1 Hsub2]; inversion Hsub2; clear Hsub Hsub2.
  generalize (sub_regular SsubT); intro Hsub0;
    inversion Hsub0 as [Hsub10 Hsub20]; inversion Hsub20; clear Hsub0 Hsub20.
  generalize (wft_YTenvT H); intro.
  generalize (noRepr_Ywf_env_Yfsubst typ_noRepr E Q Z Hsub10 H3); intro Hokt. 
  assert (uniq (map (fun U => M_yy.M.Tfsubst U Z P) E ++ F)).
  set (f := fun U0 => M_yy.M.Tfsubst U0 Z P).
  apply (map_uniq_5 typ f E F Z Q).
  apply uniq_from_Ywf_env; auto.
  set (f := fun U0 => M_yy.M.Tfsubst U0 Z P).
  gen_eq (E ++ Z ~ Q ++ F) as G. gen E.
  induction SsubT; introv Hok_env Huniq EQ; subst; gsimpl; simpl_alist in *.
  (* subtop *)
  unfold f; apply sub_top; eauto.
  (* sub_refl_tvar *)
  (* Z = X *)
  apply sub_reflexivity; auto.
  (* Z <> X *)
  apply sub_refl_tvar; auto.
  from_gen. 
  clear H2 Hsub10.
  dependent destruction H1.
  analyze_binds H1.
  apply wft_var with (U:=f U); auto using binds_app_2, binds_map_2.
  apply wft_var with (U:=U); auto using binds_app_1.

  (* sub_trans_tvar *)
  (* Z = X *)
  subst X.
  generalize (binds_mid_eq _ _ _ _ _ _ H4 (uniq_from_Ywf_env Hsub10)); intro; subst U.
  apply* (@sub_transitivity Q).
    apply sub_typ_indep with F0; auto.
    generalize (@sub_weakening nil); simpl; intro; auto.
  pattern Q; rewrite (@M_yy.M.Tfsubst_no_occur Q Z P); auto.
  apply YTenvT_Yfv with F F0; auto.
  apply fresh_mid_tail with (a:=Q)(F:= E0).
  apply uniq_from_Ywf_env; auto.
  (* Z <> X *)
  replace (M_yy.M.Tfsubst T Z P) with (f T); auto.
  analyze_binds H4.
    apply sub_trans_tvar with (f U); auto using binds_app_2, binds_map_2.
  apply* (@sub_trans_tvar U); auto using binds_app_3.
  pattern U; rewrite (@M_yy.M.Tfsubst_no_occur U Z P); auto.
  puts (Ywf_env_binds X U Hsub1 BindsTac0).
  apply M_yy.envT_Yfv with F; auto.
  apply fresh_mid_tail with (a:=Q)(F:=E0).
  apply uniq_from_Ywf_env; auto.

  (* sub_all *)
  elim sub_regular with (E0 ++ Z ~ Q ++ F) F0 T1 S1; intros; auto.
  apply sub_all with (L `union` {{Z}} `union` dom (E0 ++ Z ~ Q ++ F)); intros; auto; destruct_notin.
  clear IHSsubT.
  replace (typ_fvar X) with (Iso_typ.To (Var Iso_typ.RR (inl X))); auto. 
  repeat (rewrite Ybfsubst_permutation_var_wfT; auto); simpl.
  simpl_alist; rewrite <- app_assoc.
  puts (H4 X H8); simpl_alist in *.
  elim sub_regular with  ([(X, T1)] ++ E0 ++ [(Z, Q)] ++ F) F0
    (M_yy.M.Tbsubst S2 0%nat (typ_fvar X)) (M_yy.M.Tbsubst T2 0%nat (typ_fvar X));
    intros; auto.
  assert ([(X, M_yy.M.Tfsubst T1 Z P)] ++ map f E0
    = map f (X ~ T1 ++ E0)) as Hmap.
  unfold f; simpl; auto.
  rewrite <- app_assoc.
  Set Printing All.
  unfold elt, Iso_typ.TT in *.  (* Coq bug? *)
  rewrite Hmap.
  Unset Printing All.
  apply H5; auto; try tauto.
  apply noRepr_Ywf_env_Yfsubst with Q; auto.
  apply uniq_map_app_1.
  rewrite app_assoc; simpl.
  apply uniq_cons_3; try solve_uniq.
  simpl_alist in *; solve_notin.
Qed.

(* ********************************************************************** *)
(** * Properties of Typing *)

(* ********************************************************************** *)
(** Weakening *)

(** [typing_weakening_sub] needs to be divided. *)

Lemma typing_weakening_sub : forall E F G e T F0,
  typing (E ++ G) F0 e T -> 
  YTwf_env (E ++ F ++ G) F0 ->
  typing (E ++ F ++ G) F0 e T.
Proof. 
  introv Typ. gen_eq (E ++ G) as H. gen E.
  induction Typ; introv EQ Ok; subst.
  (* typing_var *)
  apply typing_var; auto.
  (* typing_abs *)
  apply typing_abs with (L `union` dom (E0 ++ F ++ G) `union` dom F0); auto.
  intros; destruct_notin; apply H0; auto.
  elim typing_regular with (E0 ++ G) ([(x, V)] ++ F0) (M_tt.M.Tbsubst e1 0%nat (trm_fvar x)) T1; intros; auto.
  constructor 3; auto.
  apply M_yy.YTenvT_weaken; auto.
  apply YTenvT_from_YTwf_env_2_left with x; auto.
  apply uniq_from_YTwf_env_1 with F0; auto.
  (* typing_app *)
  eapply typing_app; eauto.
  (* typing_tabs *)
  apply typing_tabs with (L `union` dom (E0 ++ F ++ G) `union` dom F0); auto.
  intros; destruct_notin.
  rewrite <- app_assoc.
  apply H0; auto.
  rewrite app_assoc.
  constructor 2; auto.
  puts (proj31 (typing_regular (H X H1))).
  apply M_yy.YTenvT_weaken; [idtac | apply uniq_from_YTwf_env_1 with F0; auto].
  apply YTenvT_from_YTwf_env_1_left with X; auto.
  (* typing_tapp *)
  eapply typing_tapp; eauto.
  apply sub_weakening; auto.
  eauto using Ywf_env_from_YTwf_env.
  (* typing_sub *)
  eapply typing_sub; eauto.
  eapply sub_weakening; eauto.
  eauto using Ywf_env_from_YTwf_env.
Qed.

Lemma typing_weakening_typ : forall E F G e T E0,
  typing E0 (E ++ G) e T -> 
  YTwf_env E0 (E ++ F ++ G) ->
  typing E0 (E ++ F ++ G) e T.
Proof. 
  introv Typ. gen_eq (E ++ G) as H. gen E.
  induction Typ; introv EQ Ok; subst.
  (* typing_var *)
  apply* typing_var; auto.
  (* typing_abs *)
  apply typing_abs with (L `union` dom (E0 ++ F ++ G) `union` dom E); auto.
  intros; destruct_notin.
  rewrite <- app_assoc.
  apply H0; auto.
  rewrite app_assoc; constructor 3; auto.
  apply M_yy.YTenvT_typ_var_indep with (E0 ++ G).
  puts (proj31 (typing_regular (H x H1))).
  apply YTenvT_from_YTwf_env_2_left with x; auto.
  (* typing_app *)
  eauto using typing_app.
  (* typing_tabs *)
  apply typing_tabs with (L `union` dom (E0 ++ F ++ G) `union` dom E); auto.
  intros; destruct_notin.
  apply H0; auto.
  apply YTwf_sub; auto.
  apply M_yy.YTenvT_typ_var_indep with (E0 ++ G).
  puts (proj31 (typing_regular (H X H1))).
  apply YTenvT_from_YTwf_env_1_left with X; auto.
  (* typing_tapp *)
  eapply typing_tapp; eauto.
  apply sub_typ_indep with (E0 ++ G); auto.
  (* typing_sub *)
  eapply typing_sub; eauto.
  apply sub_typ_indep with (E0 ++ G); auto.
Qed.

(* ********************************************************************** *)
(** Strengthening *)

Lemma sub_strengthening : forall x U E E0 F S T,
  sub E (E0 ++ x ~ U ++ F) S T ->
  sub E (E0 ++ F) S T.
Proof.
  intros.
  apply sub_typ_indep with (E0 ++ x ~ U ++ F); auto.
Qed.

(************************************************************************ *)
(** Preservation by Type Narrowing (7) *)

Lemma typing_narrowing : forall Q E F F0 X P e T,
  sub F F0 P Q ->
  typing (E ++ X ~ Q ++ F) F0 e T ->
  typing (E ++ X ~ P ++ F) F0 e T.
Proof.
  introv PsubQ Typ. gen_eq (E ++ X ~ Q ++ F) as E'. gen E.
  induction Typ; introv EQ; subst; elim sub_regular with F F0 P Q; intros; auto.
  (* typing_var *)
  apply typing_var; auto.
  apply YTwf_env_narrow with Q; auto; try tauto.
  (* typing_abs *)
  apply typing_abs with (L `union` dom F); intros.
  destruct_notin.
  apply H0; auto.
  apply sub_typ_indep with F0; auto.
  (* typing_app *)
  apply typing_app with T1; auto.
  (* typing_tabs *)
  apply typing_tabs with L.
  intros.
  rewrite <- app_assoc.
  apply H0; auto.
  (* typing_tapp *)
  apply typing_tapp with T1; auto.
  apply sub_narrowing with Q; auto.
  (* typing_sub *)
  eapply typing_sub; eauto. apply (@sub_narrowing Q); auto.
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution *)

Lemma typing_through_subst_ee : forall U E0 E F x T e u,
  typing E (E0 ++ x ~ U ++ F) e T ->
  typing E F u U ->
  typing E (E0 ++ F) (M_tt.M.Tfsubst e x u) T.
Proof.
  introv TypT TypU. gen_eq (E0 ++ x ~ U ++ F) as E'. gen E0.
  induction TypT; introv EQ; subst; gsimpl; simpl_alist in *.
  (* typing_var *)
  (* eq *)
  generalize (binds_mid_eq _ _ _ _ _ _ H0 (uniq_from_YTwf_env_2 H)); intro; subst U.
  generalize (@typing_weakening_typ nil); simpl; intro.
  apply H1; eauto using YTwf_env_strengthening.
  (* x <> x0 *)
  apply typing_var; eauto; analyze_binds H0.
  (* typing_abs *)
  apply typing_abs with (L `union` {{x}}); auto; intros; destruct_notin.
  generalize (@Tbfsubst_permutation_var_wfT); simpl; intro.
  rewrite H2; auto; simpl_alist; eauto.
    rewrite <- app_assoc; auto.
  elim typing_regular with E F u U; intros; auto.
  inversion H4.
  generalize (term_TTwfT H5); intros.
  inversion H7; auto.
  (* typing_app *)
  apply typing_app with T1; auto.
  (* typing_tabs *)
  apply typing_tabs with L; intros.
  generalize (@H0 X H1); intro.  
  generalize noRepr_THbfsubst_permutation_var_1; simpl; intro.
  puts (H X H1); simpl_alist in *.
  elim typing_regular with
    ([(X, V)] ++ E) (E0 ++ [(x, U)] ++ F)
    (M_yt.M.Tbsubst e1 0%nat (typ_fvar X)) (M_yy.M.Tbsubst T1 0%nat (typ_fvar X));
    intros; auto.
  elim typing_regular with E F u U; intros; auto.
  inversion H8. generalize (term_TTwfT H9); intro.
  inversion H11.
  rewrite H3; auto. 
  apply H2; auto.
  generalize (@typing_weakening_sub nil); simpl; intro.
  simpl_alist.
  apply H14; auto.
  eauto using YTwf_env_strengthening_1.
  (* typing_tapp *)
  apply typing_tapp with T1; auto.
  apply sub_strengthening with x U; auto.
  (* typing_sub *)
  eauto using typing_sub, sub_strengthening.
Qed.

(************************************************************************ *)
(** Preservation by Type Substitution *)

Lemma typing_through_subst_te : forall Q E F F0 Z e T P,
  typing (E ++ Z ~ Q ++ F) F0 e T ->
  sub F F0 P Q ->
  typing (map (fun U => M_yy.M.Tfsubst U Z P) E ++ F) (map (fun U => M_yy.M.Tfsubst U Z P) F0)
  (M_yt.M.Tfsubst e Z P) (M_yy.M.Tfsubst T Z P).
Proof.
  introv Typ PsubQ. gen_eq (E ++ Z ~ Q ++ F) as G. gen E.
  induction Typ;
    set (f := fun U => M_yy.M.Tfsubst U Z P); 
      introv EQ; subst; gsimpl; simpl_alist in *. 
  (* typing_var *)
  apply typing_var; auto.
    apply noRepr_YTwf_env_Yfsubst with Q; auto.
  replace (M_yy.M.Tfsubst T Z P) with (f T); auto.
  (* typing_abs *)
  apply typing_abs with L; intros; destruct_notin; simpl in *; simpl_env in *.
  replace (trm_fvar x) with (Iso_trm.To (Var Iso_trm.RR (inl x))); auto.
  rewrite noRepr_THbfsubst_permutation_var; simpl; auto.
  apply H0; auto;  simpl_env in *.
  apply sub_typ_indep with F0; auto.
  (* typing_app *)
  apply typing_app with (M_yy.M.Tfsubst T1 Z P); auto.
  (* typing_tabs *)
  apply typing_tabs with (L `union` {{Z}}); intros; destruct_notin.
  replace (typ_fvar X) with (Iso_typ.To (Var Iso_typ.RR (inl X))); auto.
  rewrite THbfsubst_permutation_var with (E:=F); auto.
  rewrite Ybfsubst_permutation_var with (E:=F); simpl; auto.
  simpl_alist.
  assert (X ~ M_yy.M.Tfsubst V Z P = map f (X ~  V)) as Hmap; [try unfold f; auto | idtac].
  unfold elt, Iso_typ.TT in *.  (* Coq bug? *)
  rewrite Hmap.
  rewrite <- app_assoc; rewrite <- map_app.
  apply H0; auto.
  (* typing_tapp *)
  rewrite <- Ybfsubst_permutation_core; auto.
  apply typing_tapp with (M_yy.M.Tfsubst T1 Z P); auto.
  apply sub_through_subst_tt with Q; auto.
  (* typing_sub *)
  apply typing_sub with (M_yy.M.Tfsubst S Z P); auto.
  apply sub_through_subst_tt with Q; auto.
Qed.  

(* ********************************************************************** *)
(** * Preservation *)

(* ********************************************************************** *)
(** Inversions for Typing *)

Lemma typing_inv_abs : forall E F S1 e1 T,
  typing E F (trm_abs S1 e1) T -> 
  forall U1 U2,
    sub E F T (typ_arrow U1 U2) ->
    (sub E F U1 S1
      /\ exists S2, exists L, forall x,
        x `notin` L -> typing E (x ~ S1 ++ F) (M_tt.M.Tbsubst e1 0 (trm_fvar x)) S2
      /\ sub E F S2 U2).
Proof.
  introv Typ. gen_eq (trm_abs S1 e1) as e. gen S1 e1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversions EQ.
  inversions* Sub.
  use (@sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall E F S1 e1 T,
  typing E F (trm_tabs S1 e1) T -> 
  forall U1 U2,
    sub E F T (typ_all U1 U2) ->
    (sub E F U1 S1
      /\ exists S2, exists L, forall X, X `notin` L ->
        typing (X ~ U1 ++ E) F (M_yt.M.Tbsubst e1 0 (typ_fvar X)) (M_yy.M.Tbsubst S2 0 (typ_fvar X))
        /\ sub (X ~ U1 ++ E) F (M_yy.M.Tbsubst S2 0 (typ_fvar X)) (M_yy.M.Tbsubst U2 0 (typ_fvar X))).
Proof.
  intros E F S1 e1 T H. gen_eq (trm_tabs S1 e1) as e. gen S1 e1.
  induction H; intros S1 b EQ U1 U2 Sub; inversion EQ.
  inversions Sub; splits; auto.
  exists T1; exists (L `union` L0); intros Y Fr; destruct_notin; splits; auto. 
  generalize (@typing_narrowing S1 nil); simpl; intro.
  apply H1; simpl_alist; auto.
  use (@sub_transitivity T).
Qed. 

(* ********************************************************************** *)
(** Preservation Result *)

(** some tactics from Metatheory_Env  *)

Ltac env_fix_core :=
  let go := try env_fix_core in
  match goal with 
  | H: context [(?x,?a)::?E] |- _ =>
     (   (progress (change ((x,a)::E) with (x ~ a ++ E) in H))
      || (progress (unsimpl (x ~ a ++ E) in H))   ); go
  | |- context [(?x,?a)::?E] =>
    (   (progress (change ((x,a)::E) with (x ~ a ++ E)))
      || (progress (unsimpl (x ~ a ++ E)))  ); go
  |  H: context [@nil ((var * ?A)%type)] |- _ =>
      progress (change (@nil ((var * A)%type)) with (@empty A) in H); go
  | |- context [@nil ((var * ?A)%type)] => 
     progress (change (@nil ((var * A)%type)) with (@empty A)); go
  end.

Ltac env_fix := try env_fix_core.

Tactic Notation "apply_empty" constr(lemma) :=
  let H := fresh in poses H (@lemma empty);
  simpl in H; eapply H; env_fix; clear H.

Tactic Notation "apply_empty" "*" constr(lemma) :=
  apply_empty lemma; auto*.


Lemma preservation_result : preservation.
Proof.
  introv Typ. gen e'.
  induction Typ; introv Red; try solve [ inversion Red ].
  (* case: app *)
  inversions Red; try solve [ eapply typing_app; eauto ].
  destructi (typing_inv_abs Typ1 (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    apply sub_reflexivity; auto.
    destructs (typing_regular Typ2).
    eauto using Ywf_env_from_YTwf_env.
  pick fresh X for (L `union` (M_tt.M.Tfv e0)); destruct_notin.
  forward~ (P2 X) as K. destruct K.
  rewrite* (@M_tt.M.Tbfsubst_var_intro e0 e2 X NotInTac); auto.
    generalize (@typing_through_subst_ee V nil); simpl; intro; auto.
    apply H2; simpl_alist; auto.
      apply* (@typing_sub S2); auto.
      apply sub_typ_indep with F; auto.
  apply typing_sub with T1; auto.
  (* case: tapp *)
  inversions Red; try solve [ eapply typing_tapp; eauto ].
  destructs (sub_regular H).
  destructi (typing_inv_tabs Typ (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    apply sub_reflexivity; auto.
  pick fresh X for (L `union` dom E `union` dom F `union` (M_yy.M.Tfv T2) `union` M_yt.M.Tfv e0);
  destruct_notin.
  forward~ (P2 X) as K. destruct K.
  rewrite (@M_yt.M.Tbfsubst_var_intro e0 T X); simpl ; auto.
  rewrite (@M_yy.M.Tbfsubst_var_intro T2 T X); simpl; auto.
  unsimpl (map (fun U => M_yy.M.Tfsubst U X T) nil ++ E).
  assert (map (fun U => M_yy.M.Tfsubst U X T) F = F).
  apply M_yy.M.env_fv_no_occur.
  apply YTwf_env_fv_2 with E; auto.
  apply (proj31 (typing_regular Typ)).
  rewrite <- H7.
  apply (@typing_through_subst_te T1); simpl; simpl_env in *; auto.
  eauto using typing_sub.
  (* case sub *)
  eauto using typing_sub.
Qed.

(* ********************************************************************** *)
(** * Progress *)

(* ********************************************************************** *)
(** Canonical Forms *)

Tactic Notation "gen_eq" constr(c) "as" ident(x) ident(H) "at" integer(n) :=
  set (x := c) at n ; assert (H : x = c) by reflexivity; clearbody x.


Lemma canonical_form_abs : forall T U1 U2,
  value T ->
  typing nil nil T (typ_arrow U1 U2) ->
  exists V, exists e1, T = trm_abs V e1.
Proof.
  introv Val.
  gen_eq (@nil (var * typ)) as E H at 1.
  gen_eq (@nil (var * typ)) as F H0.
  introv Typ.
  gen_eq (typ_arrow U1 U2) as U.
  gen U1 U2.  gen E F. do 5 intro.
  induction Typ; intros; try solve [ inversion Val | inversion EQT | eauto ];
    try discriminate.
  destructi (typing_regular Typ). inversion H4.
  subst. inversion H1; subst.
  inversion H.
  apply IHTyp with S1 S2; auto.
Qed.

Lemma canonical_form_tabs : forall t U1 U2,
  value t ->
  typing nil nil t (typ_all U1 U2) ->
  exists V, exists e1, t = trm_tabs V e1.
Proof.
  introv Val.
  gen_eq (@nil (var * typ)) as E H at 1.
  gen_eq (@nil (var * typ)) as F H0.
  intro Typ.
  gen_eq (typ_all U1 U2) as U.
  gen U1 U2.
  induction Typ; introv EQT;
    try solve [ inversion Val | inversion EQT | eauto ].
  subst. inversion H1. inversion H. auto*.
Qed.  

(* ********************************************************************** *)
(** Progress Result *)

Lemma progress_result : progress.
Proof.
  do 2 intro.
  gen_eq (@empty_env typ) as E H at 1.
  gen_eq (@empty_env typ) as F H0.
  introv Typ.
  poses Typ' Typ.
  induction Typ; subst.
  (* case: var *)
  inversion H2.
  (* case: abs *)
  left*.
  (* case: app *)
  right. destruct* IHTyp1 as [Val1 | [e1' Rede1']].
  destruct* IHTyp2 as [Val2 | [e2' Rede2']].
  destruct (canonical_form_abs Val1 Typ1) as [S [e3 EQ]]. subst.
  exists* (M_tt.M.Tbsubst e3 0 e2). 
  (* case: tabs *)
  left*.
  (* case: tapp *)
  right.
  destruct* IHTyp as [Val1 | [e1' Rede1']]. 
  destruct (canonical_form_tabs Val1 Typ) as [S [e3 EQ]]. 
  subst.
  exists* (M_yt.M.Tbsubst e3 0 T).
  (* case: sub *)
  auto*.
Qed.  

