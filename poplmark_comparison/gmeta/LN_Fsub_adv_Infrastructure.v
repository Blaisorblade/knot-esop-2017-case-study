Set Implicit Arguments.

Require Import LNameless_Meta.
Require Import LNameless_Meta_Env.
Require Import LNameless_Isomorphism.
Require Import LNameless_Fsub_Iso.
Require Import LN_Template_Two_Sort.
Require Export LN_Fsub_adv_Definitions.


(***************************************************************)
(** * Fsub Part 1A and 2A *)
(***************************************************************)

(** Reference: Chargueraud's POPL solution using Locally Nameless style
   and cofinite quantification *)

  (** [gconstructor] helps to use [TwfT], [THwfT], [YwfT], [YTenvT], [YenvT]
     behaves inductively as expected.
     - [apply_wfT], [from_wfT], [apply_envT], [from_envT], [gsimpl_subst]
       are auxiliary tactics. *)

  (** Inversion tactics for well-formedness
     - [wf_inv]: inversion tactics for [TwfT], [THwfT], [YwfT], [YTenvT], [YenvT].

     - The other tactics are auxiliary.

     - [dependent destruction] needs to be redefined
       because of some bugs. *)

(***************************************************************)
(** ** Equivalence proofs *)
(***************************************************************)

(** We start with some proofs showing the equivalence between well-formedness
   in the object language and that in its representation *)

Lemma type_YwfT : forall (T:typ),
  type T -> M_yy.M.TwfT T.
Proof.
  induction 1; gconstructor*.
Qed.  

(** [YwfT_arrow_inv] and [YwfT_all_inv] can be saved thanks to [wf_inv] tactic. *)

Lemma YwfT_arrow_inv : forall T1 T2,
  M_yy.M.TwfT (typ_arrow T1 T2) ->
  M_yy.M.TwfT T1 /\ M_yy.M.TwfT T2.
Proof.
  introv H; wf_inv in H.
Qed.

Lemma YwfT_all_inv : forall T1 T2,
  M_yy.M.TwfT (typ_all T1 T2) -> 
  M_yy.M.TwfT T1 /\  exists L, (forall X, X `notin` L -> M_yy.M.TwfT (M_yy.M.Tbsubst T2 0 (typ_fvar X))).
Proof.
  introv H; split; wf_inv in H.
  exists L; intros.
  puts (H1 X H2); clear H1.
  wf_inv in H3.
Qed.

Lemma YwfT_type : forall (U:typ),
  M_yy.M.TwfT U -> type U.
Proof.
  intro U.
  cut (M_yy.M.TSize U < S (M_yy.M.TSize U));
    [ generalize (S (M_yy.M.TSize U)); intro n; gen U | auto with arith].
  induction n; intros U Hsize Hwf;
    [ elim lt_n_O with (n:= M_yy.M.TSize U); auto
      | destruct U; gsimpl in Hsize; wf_inv in Hwf; 
        [ apply type_arrow; apply IHn; eauto with arith
          | apply type_all with L; intros; apply IHn; eauto 2 with arith;
            [ grewrite <- YSize_Ybsubst; eauto 2 with arith
              | puts (H1 X H2); clear H1; wf_inv in H3 ] ] ].
Qed.   

Hint Resolve type_YwfT YwfT_type.

Lemma wft_YTenvT : forall E F U,
  wft E F U -> M_yy.YTenvT E F U.
Proof.
  induction 1; gconstructor; auto.
  apply env_Bind_REC_homo with (L:=L)(V:=Iso_typ.From V); auto; intros.
  gconstructor.
  change ((k, Iso_typ.From V) :: map Iso_typ.From E) with
    (map Iso_typ.From (k ~ V ++ E)).
  from_envT.
  apply* H1.
Qed.

Lemma YTenvT_wft : forall U E F,
  M_yy.YTenvT E F U ->
  wft E F U.
Proof.
  intro U.
  cut (M_yy.M.TSize U < S (M_yy.M.TSize U));
    [ generalize (S (M_yy.M.TSize U)); gen U; intros U n; gen U; gen n | auto].
  induction n; intros U Hsize E F HenvT;
    [ elim lt_n_O with (n:= M_yy.M.TSize U); auto
      | destruct U; gsimpl in Hsize; wf_inv in HenvT ]. 
  (* typ_fvar *)
  apply wft_var with (U:= Iso_typ.To U).
  pattern U in H0;  rewrite <- Iso_typ.From_To in H0.
  apply binds_map_1 with (f:= Iso_typ.From); auto using Iso_typ.From_inj.
  (* typ_arrow *)
  apply wft_arrow; apply IHn; eauto 2 with arith.
  (* type_all *)
  apply wft_all with L (Iso_typ.To V);
    [ apply IHn; eauto with arith | idtac].
  intros.
  puts (H1 X H2); clear H1.
  wf_inv in H3.
  unfold elt in *.              (* coq bug *)
  replace ((X, V) :: map Iso_typ.From E) with (map Iso_typ.From ((X, Iso_typ.To V) :: E)) in H1;
    [ from_envT; apply IHn; auto 1; grewrite <- YSize_Ybsubst; eauto 2 with arith
      | simpl; auto_rewrite].
Qed.

Hint Resolve wft_YTenvT YTenvT_wft.

Lemma term_TTwfT : forall (T:trm), term T -> TTwfT T.
Proof.
  unfold TTwfT; introv Hterm; split; induction Hterm; try gconstructor*; auto;
    pick fresh x; puts (H1 x Fr);
    [ apply TwfT_THbsubst with 0 x | apply THwfT_Tbsubst with 0 x] ; auto.
Qed.

Lemma TTwfT_term : forall (T:trm),
  TTwfT T ->
  term T.
Proof.
  intro T.
  cut (M_tt.M.TSize T < S (M_tt.M.TSize T));
    [ generalize (S (M_tt.M.TSize T)); gen T; intros T n; gen T; gen n | auto with arith].
  unfold TTwfT; induction n; intros T Hsize HTT; inversion HTT as [HT HTH]; clear HTT;
    [ elim lt_n_O with (n:= M_tt.M.TSize T); auto
      | destruct T as [| | T1 T2 | U T | T U| U T]; gsimpl in Hsize; wf_inv in HT ].

  wf_inv in HTH; apply term_app; apply IHn; eauto with arith.

  wf_inv in HTH; [elim trm_typ; auto | idtac].
  apply term_abs with L; auto; intros.
  puts (H1 x H5); clear H1.
  wf_inv in H6.
  apply IHn; eauto 2 with arith.
  grewrite <- TSize_Tbsubst; eauto 2 with arith.
  split; auto.
  apply* THwfT_Tbsubst_1.

  wf_inv in HTH.
  apply term_tapp; try apply IHn; eauto with arith; tauto.

  wf_inv in HTH.
  apply term_tabs with L; auto.
  intros.
  puts (H6 X H5); clear H6.
  wf_inv in H7.
  apply IHn; eauto 2 with arith.
  grewrite <- TSize_THbsubst; eauto 2 with arith.
  split; auto.
  apply* TwfT_THbsubst_1.
Qed.

Hint Resolve term_TTwfT TTwfT_term.

Lemma YTenvT_all_inv : forall E F T1 T2,
  M_yy.YTenvT E F (typ_all T1 T2) ->
  M_yy.YTenvT E F T1 /\
  exists L, exists U,
    (forall X, X `notin` L -> M_yy.YTenvT (X ~ U ++ E) F (M_yy.M.Tbsubst T2 0 (typ_fvar X))).
Proof.
  split; wf_inv in H.
  exists L; exists (Iso_typ.To V); intros.
  puts (H1 X H2); clear H1.
  wf_inv in H3.
  replace ((X, V) :: map Iso_typ.From E) with
    (map Iso_typ.From ((X, Iso_typ.To V) :: E)) in H1;
    [ from_envT; auto | simpl; auto_rewrite].
Qed.


(***************************************************************)
(** * Main Formalization *)
(***************************************************************)

(** Constructors as hints
   - Note that some lemmas are already saved in the template module. *)

Hint Constructors wfT uniq wf_env value red.

Hint Resolve 
  sub_top sub_refl_tvar sub_arrow
  typing_var typing_app typing_tapp typing_sub.

Hint Resolve YwfT_Yfsubst TTwfT_Tfsubst (@noRepr_TTwfT_THfsubst typ_noRepr trm_typ).

Hint Resolve (@noRepr_YTenvT_Yfsubst typ_noRepr).

(**************************************************************)
(**************************************************************)

Lemma sub_typ_indep : forall E F S T, sub E F S T ->
  forall F0, sub E F0 S T.
Proof.
  induction 1; intros; try constructor; auto.
  apply sub_trans_tvar with U; auto.
  apply sub_all with L; auto.
Qed.  
 

(** Through type reduction *)

Lemma wft_open : forall E F U T1 T2,
  uniq E ->
  M_yy.YTenvT E F (typ_all T1 T2) ->
  M_yy.YTenvT E F U ->
  M_yy.YTenvT E F (M_yy.M.Tbsubst T2 0 U).
Proof.
  intros.
  generalize (YTenvT_all_inv H0); intro Hall; inversion Hall.
  destruct H3 as [L]. destruct H3 as [U0].
  pick fresh X for (L `union` M_yy.M.Tfv T2); destruct_notin.
  generalize (H3 X Fr); intro Hnotin.
  rewrite M_yy.M.Tbfsubst_var_intro with (a:=X); eauto using YenvT_YwfT.
  apply noRepr_YTenvT_Yfsubst_left with U0; auto.
Qed. 
  
Hint Extern 1 (uniq _) => apply uniq_from_YTwf_env_1.
Hint Extern 1 (uniq _) => apply uniq_from_YTwf_env_2.


Hint Resolve M_yy.YTenvT_weaken.
Hint Resolve M_yy.YTenvT_weaken_right.
Hint Resolve M_yy.YTenvT_weaken_left.

Hint Immediate YTwf_env_binds_1 YTwf_env_binds_2.
Hint Resolve (noRepr_YTenvT_Yfsubst typ_noRepr).
Hint Resolve (noRepr_YTenvT_Yfsubst_left typ_noRepr).
Hint Resolve YTenvT_from_YTwf_env_1 YTenvT_from_YTwf_env_1_left.
Hint Resolve YTenvT_from_YTwf_env_2 YTenvT_from_YTwf_env_2_left.


(* ********************************************************************** *)
(** ** Properties of well-formedness of an environment *)

Hint Resolve YTwf_env_narrow (@noRepr_YTwf_env_Yfsubst typ_noRepr).
Hint Immediate YTwf_env_strengthening.


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

Lemma sub_regular : forall E F S T,
  sub E F S T -> Ywf_env E /\ wft E F S /\ wft E F T.
Proof.
  induction 1.
  (* sub_top *)
  auto.
  (* sub_refl_tvar *)
  auto.
  (* sub_trans_tvar *)
  intuition.
  apply wft_var with U; auto.
  (* sub_arrow *)
  intuition.
  (* sub_all *)
  intuition.
  apply wft_all with L T1; auto; intros.
  elim H1 with X; intros; intuition.    
  apply wft_all with L T1; auto; intros.
  elim H1 with X; intros; auto.
  inversion H7; auto.
Qed.

(** The typing relation is restricted to well-formed objects. *)

Tactic Notation "to_gen" :=
  match goal with
    | |- type _    => apply YwfT_type
    | |- wft _ _ _ => apply YTenvT_wft
    | |- term _    => apply TTwfT_term
  end.

Tactic Notation "from_gen" :=
  match goal with
    | |- M_yy.M.TwfT _       => apply type_YwfT
    | |- M_yy.YTenvT _ _ _ => apply wft_YTenvT
    | |- TTwfT _      => apply term_TTwfT
  end.

Tactic Notation "assert_gen" :=
  match goal with
    | H : type _    |- _ => generalize (type_YwfT H); intro
    | H : wft _ _ _ |- _ => generalize (wft_YTenvT H); intro
    | H : term _    |- _ => generalize (term_TTwfT H); intro
  end.

Tactic Notation "assert_concrete" :=
  match goal with
    | H : M_yy.M.TwfT _       |- _ => generalize (YwfT_type H); intro
    | H : M_yy.YTenvT _ _ _ |- _ => generalize (YTenvT_wft H); intro
    | H : TTwfT _      |- _ => generalize (TTwfT_term H); intro
  end.

Lemma typing_regular : forall E F e T,
  typing E F e T -> YTwf_env E F /\ term e /\ wft E F T.
Proof.
  induction 1.
  (* typing_var *)
  split; auto; split; auto.
  eauto using YTwf_env_binds_1.

  (* typing_abs *)
  pick fresh x for L.
  elim H0 with x; auto; intros.
  inversion H2.
  split; auto.
  eauto using YTwf_env_strengthening_left.
  split.
  apply term_abs with L; auto.
  apply M_yy.YenvT_YwfT with E.
  eapply YTenvT_from_YTwf_env_2_left; eauto. 
  intros.
  elim H0 with x0; tauto.
  apply wft_arrow.
  to_gen; eapply YTenvT_from_YTwf_env_2_left; eauto.
  assert_gen; to_gen; auto.

  (* typing_app *)
  inversion IHtyping1 as [IHtyping11 IHtyping12]; inversion IHtyping12.
  inversion IHtyping2 as [IHtyping21 IHtyping22]; inversion IHtyping22.
  split; auto; split.
    apply term_app; auto.
  inversion IHtyping12.
  dependent destruction H6; auto.

  (* typing_tabs *)
  pick fresh X for (L `union` M_yy.M.env_fv F); destruct_notin.
  elim H0 with X; intros; auto.
  inversion H2.
  split.
  generalize (@noRepr_YTwf_env_Yfsubst typ_noRepr nil E F V V X H1); simpl; intro;
    simpl_env in *.
  assert (map (fun U : Iso_typ.TT => M_yy.M.Tfsubst U X V) F = F).
  apply* M_yy.M.env_fv_no_occur.
  rewrite H6 in H5.
  apply H5; eauto using YTenvT_from_YTwf_env_1_left.
  split.
  apply term_tabs with L; auto.
  apply M_yy.YenvT_YwfT with E.
  eapply YTenvT_from_YTwf_env_1_left; eauto.
  intros.
  elim H0 with X0; intros; intuition.
  apply wft_all with L V.
  to_gen; eapply YTenvT_from_YTwf_env_1_left; eauto.
  intros.
  elim H0 with X0; intros; auto; elim H7; auto.

  (* typing_tapp *)
  inversion IHtyping as [IHtyping1 IHtyping2]; inversion IHtyping2.
  assert_gen.
  assert (M_yy.M.TwfT T).
  apply M_yy.YenvT_YwfT with E.
  change (M_yy.YTenvT E F T).
  elim sub_regular with E F T T1; intros; auto; from_gen; tauto.
  dependent destruction H2.
  (* pick fresh X for (L `union` dom E `union` dom F). *)
  pick fresh X for (L `union` M_yy.M.Tfv T2 `union` M_yy.M.env_fv F).
  destruct_notin.
  split; auto; split.
  apply term_tapp; auto.
  generalize (H5 X Fr); intro.
  assert_gen; to_gen.
  rewrite M_yy.M.Tbfsubst_var_intro with (a:=X); auto.
  apply noRepr_YTenvT_Yfsubst_left with V; auto.
  from_gen; elim sub_regular with E F T T1; tauto.
  eapply uniq_from_YTwf_env_1; eauto.

  (* typing_sub *)
  inversion IHtyping as [IHtyping1 IHtyping2]; inversion IHtyping2.
  split; auto; split; auto.
  elim sub_regular with E F S T; firstorder.
Qed.
  
(** The value relation is restricted to well-formed objects. *)

Lemma value_regular : forall t,
  value t -> term t.
Proof.
  induction 1; auto*.
Qed.

(** The reduction relation is restricted to well-formed objects. *)

Lemma red_regular : forall t t',
  red t t' -> term t /\ term t'.
Proof.
  induction 1; split.

  (* red_app_1 *)
  inversion IHred; apply term_app; auto.
  inversion IHred; apply term_app; auto.

  (* red_app_2 *)
  inversion IHred; apply term_app; auto using value_regular.
  inversion IHred; apply term_app; auto using value_regular.

  (* red_tapp *)
  inversion IHred; apply term_tapp; auto. 
  inversion IHred; apply term_tapp; auto.

  (* red_abs *)
  apply term_app; auto using value_regular.
  assert_concrete.
  inversion H1.
  pick fresh X for (L `union` M_tt.M.Tfv e1); destruct_notin.
  generalize (value_regular H0); intro; assert_gen.
  rewrite* (@M_tt.M.Tbfsubst_var_intro e1 v2 X NotInTac); simpl.
  generalize (H5 X Fr); intro; assert_gen; to_gen.
  auto using TTwfT_Tfsubst.

  (* red_tabs *)
  apply term_tapp; auto.
  generalize (TTwfT_term H); intro.
  assert_concrete.
  inversion H1.
  pick fresh X for (L `union` M_yt.M.Tfv e1); destruct_notin.
  rewrite* (@M_yt.M.Tbfsubst_var_intro e1 V2 X NotInTac); simpl.
  generalize (H6 X Fr); intro; to_gen.
  generalize (term_TTwfT H7); intro.
  auto using TTwfT_THfsubst.
Qed.

(** Useful tactics *)

Notation "'proj31' P" := (proj1 P) (at level 69).
Notation "'proj32' P" := (proj1 (proj2 P)) (at level 69).
Notation "'proj33' P" := (proj2 (proj2 P)) (at level 69).

Hint Extern 1 (M_yy.Ywf_env ?E) =>
  match goal with
  | H: sub E _ _     |- _ =>
    eapply (proj31 (sub_regular H))
  | H: typing E ?F _ |- _ =>
    eapply (@Ywf_env_from_YTwf_env E F); eapply (proj31 (typing_regular H))
  end.

Hint Extern 1 (YTwf_env ?E ?F) =>
  match goal with
  | H: typing _ _ _ |- _ => apply (proj31 (typing_regular H))
  end.

Hint Extern 1 (wft ?E ?F ?T) =>
  match goal with
  | H: typing E F _ T |- _ => apply (proj33 (typing_regular H))
  | H: sub E F T _    |- _ => apply (proj32 (sub_regular H))
  | H: sub E F _ T    |- _ => apply (proj33 (sub_regular H))
  end.

Hint Extern 1 (M_yy.YTenvT ?E ?F ?T) =>
  match goal with
  | H: typing E F _ T |- _ => from_gen; apply (proj33 (typing_regular H))
  | H: sub E F T _    |- _ => from_gen; apply (proj32 (sub_regular H))
  | H: sub E F _ T    |- _ => from_gen; apply (proj33 (sub_regular H))
  end.

Hint Extern 1 (M_yy.YenvT ?E ?T) =>
  match goal with
  | H: typing E ?F _ T |- _ =>
    change (M_yy.YTenvT E F T); from_gen; apply (proj33 (typing_regular H))
  | H: sub E ?F T _    |- _ =>
    change (M_yy.YTenvT E F T); from_gen; apply (proj32 (sub_regular H))
  | H: sub E ?F _ T    |- _ =>
    change (M_yy.YTenvT E F T); from_gen; apply (proj33 (sub_regular H))
  end.

Hint Extern 1 (type ?T) =>
  let go E F:= apply (@YTenvT_YwfT E F); auto in
  match goal with
  | H: typing ?E ?F _ T |- _ => to_gen; go E F
  | H: sub ?E ?F T _    |- _ => to_gen; go E F
  | H: sub ?E ?F _ T    |- _ => to_gen; go E F
  end.

Hint Extern 1 (M_yy.M.TwfT ?T) =>
  let go E F := apply (@YTenvT_YwfT E F); auto in
  match goal with
  | H: typing ?E ?F _ T |- _ => go E F
  | H: sub ?E ?F T _    |- _ => go E F
  | H: sub ?E ?F _ T    |- _ => go E F
  end.

Hint Extern 1 (term ?e) =>
  match goal with
  | H: typing _ _ ?e _ |- _ => apply (proj32 (typing_regular H))
  | H: red ?e _        |- _ => apply (proj1 (red_regular H))
  | H: red _ ?e        |- _ => apply (proj2 (red_regular H))
  end.

Hint Extern 1 (TTwfT ?e) =>
  match goal with
  | H: typing _ _ ?e _ |- _ => from_gen; apply (proj32 (typing_regular H))
  | H: red ?e _        |- _ => from_gen; apply (proj1 (red_regular H))
  | H: red _ ?e        |- _ => from_gen; apply (proj2 (red_regular H))
  end.


