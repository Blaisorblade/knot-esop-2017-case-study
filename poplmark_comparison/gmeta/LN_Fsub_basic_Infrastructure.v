Set Implicit Arguments.

Require Import Arith_Max_extra.
Require Import LNameless_Meta.
Require Import LNameless_Meta_Env.
Require Import LNameless_Isomorphism.
Require Import LNameless_Fsub_Iso.
Require Import LN_Template_Two_Sort.
Require Export LN_Fsub_basic_Definitions.

(* ************************************************************ *)
(** ** Fsub Part 1A and 2A *)

(** Reference: Chargueraud's POPL solution using Locally Nameless style
   and cofinite quantification *)

(** Constructors as hints *)

Hint Constructors type term wft uniq okt value red.

Hint Resolve 
  sub_top sub_refl_tvar sub_arrow
  typing_var typing_app typing_tapp typing_sub.

(** * Infrastructure *)

Lemma type_Ywf : forall T,
  type T -> M_yy.M.Twf T.
Proof.
  intros.
  cut (forall (k:nat) (U:MY.TT), T = M_yy.M.Tbsubst T k U);
    [tauto| idtac].

  induction H; gsimpl; f_equal*.
  pick_fresh X; destruct_notin.
  apply M_yy.M.Tbsubst_homo_core with (j:=0) (V:=(typ_fvar X)); [omega | apply H1;auto].
Qed.

Lemma Ywf_basic_type : forall T,
  M_yy.M.Twf_basic T -> type T.
Proof.
  unfold M_yy.M.Twf_basic; simpl; intro T.
  cut (M_yy.M.TSize T < S (M_yy.M.TSize T)); [idtac | auto].
  generalize (S (M_yy.M.TSize T)).
  intro n. gen T.
  induction n; intros;
  [elim lt_n_O with (M_yy.M.TSize T); assumption | idtac].
  
  induction T; gsimpl in H.

  generalize (H0 n0 n0); gsimpl; discriminate.

  apply type_arrow;
    [apply IHT1; intros; eauto with arith; generalize (H0 k a); gsimpl; injection H1; tauto |
      apply IHT2; intros; eauto with arith; generalize (H0 k a); gsimpl; injection H1; tauto].

  apply type_all with (M_yy.M.Tfv T2);
    [apply IHT1; intros; eauto with arith; generalize (H0 k a); gsimpl; injection H1; tauto |
      idtac].

  intros; apply IHn;
    [grewrite <- YSize_Ybsubst; eauto with arith | idtac].

  intros; case_eq (eq_nat_dec k 0); intros;
    [rewrite e; grewrite <- Ybsubst_var_twice | idtac ].

  generalize (H0 (k-1) a); gsimpl.
  injection H3; intros.
  clear H5.
  assert (S (k - 1) = k); [omega |idtac].
  rewrite H5 in H4; clear H5.
  pattern T2 at 1; rewrite H4.
  apply M_yy.M.Tbsubst_homo; assumption.
Qed.

Lemma Ywf_type : forall T,
  M_yy.M.Twf T -> type T.
Proof.
  intros; cut (M_yy.M.Twf_basic T);
    [apply Ywf_basic_type| apply M_yy.M.Twf_basic_from_Twf; auto].
Qed.

Lemma term_TTwf : forall T,
  term T ->
  TTwf T.
Proof.
  split.

  unfold M_tt.M.Twf.
  induction H; intros; gsimpl; f_equal*; (* try rewrite noRepr_YHbsubst; *) auto.
  pick_fresh x; destruct_notin;
  apply M_tt.M.Tbsubst_homo_core with (V:=trm_fvar x)(j:=0); [omega | eauto].
  pick_fresh X; destruct_notin;
  apply THbsubst_hetero_core_2 with (V:=typ_fvar X)(j:=0);auto.

  unfold M_yt.M.Twf.
  induction H; intros; gsimpl; f_equal*; try (apply type_Ywf; auto).
  pick_fresh x; destruct_notin.
  eapply THbsubst_hetero_core_1; eauto.
  pick_fresh X; destruct_notin.
  apply M_yt.M.Tbsubst_homo_core with (V:=typ_fvar X)(j:=0); [omega|eauto].
Qed.

Lemma TTwf_term : forall (T:trm),
  TTwf T -> term T.
Proof.
  introv HTwf.
  cut (TTwf_basic T);
    [idtac | auto using TTwf_basic_from_TTwf].
  clear HTwf.
  unfold TTwf_basic.
  cut (M_tt.M.TSize T < S (M_tt.M.TSize T)); [idtac | auto].
  generalize (S (M_tt.M.TSize T)).
  intro n. gen T.
  induction n; intros;
    [elim lt_n_O with (M_tt.M.TSize T); assumption | idtac].
  inversion H0 as [HT HTH]; clear H0.
  destruct T; gsimpl in H;
    [generalize (HT n0 n0); gsimpl; discriminate | idtac| idtac| idtac| idtac].

  apply term_app; apply IHn; eauto with arith; split; intros k a;
  generalize (HT k a); gsimpl; 
  generalize (HTH k a); gsimpl;
  injection H0; try tauto;
  injection H1; try tauto.

  apply term_abs with {};
    [apply Ywf_basic_type; intros k a; generalize (HTH k a); gsimpl; injection H0; tauto | idtac].
  intros; destruct_notin; apply IHn;
    [grewrite <- TSize_Tbsubst; eauto with arith | idtac ].
  split; intros k a.

  case_eq (eq_nat_dec k 0); intros.
  rewrite e.
  grewrite <- Tbsubst_var_twice.
  generalize (HT (k-1) a); gsimpl.
  injection H1; intros.
  assert (S (k - 1) = k); [omega |idtac].
  rewrite H3 in H2; clear H3.
  pattern T at 1; rewrite H2.
  apply M_tt.M.Tbsubst_homo; assumption.
  
  generalize (HTH k a); gsimpl.
  injection H0; intros.
  clear H2.
  pattern T at 1; rewrite H1.
  apply* THbsubst_hetero.

  apply term_tapp.
  apply IHn; [eauto with arith | split; intros k a].
  generalize (HT k a); gsimpl.
  injection H0; intros; auto.
  generalize (HTH k a); gsimpl.
  injection H0; intros; auto.

  apply Ywf_basic_type.
  intros k a.
  generalize (HTH k a); gsimpl.
  injection H0; intros; auto.

  apply term_tabs with {}.
  apply Ywf_basic_type.
  intros k a.
  generalize (HTH k a); gsimpl.
  injection H0; intros; auto.

  intros; destruct_notin.
  apply IHn;
    [grewrite <- TSize_THbsubst; eauto with arith | split; intros k a].
  generalize (HT k a); gsimpl.
  injection H0; intros.
  pattern T at 1; rewrite H1.
  symmetry; apply* THbsubst_hetero.

  case_eq (eq_nat_dec k 0); intros.
  rewrite e.
  grewrite <- THbsubst_var_twice.
  generalize (HTH (k-1) a); gsimpl.
  injection H1; intros.
  clear H3.
  assert (S (k - 1) = k); [omega |idtac].
  rewrite H3 in H2; clear H3.
  pattern T at 1; rewrite H2.
  apply M_yt.M.Tbsubst_homo; assumption.
Qed.

(** Substitution for free type variables in environment. *)

Definition subst_tb (Z : var) (P : typ) (b : bind) : bind :=
  match b with
  | bind_sub T => bind_sub (M_yy.M.Tfsubst T Z P)
  | bind_typ T => bind_typ (M_yy.M.Tfsubst T Z P)
  end.

Hint Resolve Ywf_type TTwf_term type_Ywf term_TTwf.

Hint Resolve Ywf_Yfsubst TTwf_THfsubst TTwf_Tfsubst.

(** * Properties of well-formedness of a type in an environment *)

(** If a type is well-formed in an environment then it is locally closed. *)

Lemma type_from_wft : forall E T,
  wft E T -> type T.
Proof.
  induction  1; eauto.
Qed.

(** Through weakening *)

 Tactic Notation "apply_ih_bind" constr(H) :=
   do_rew <- app_assoc (eapply H).

 Tactic Notation "apply_ih_bind" "*" constr(H) :=
   do_rew* <- app_assoc (eapply H).              

Lemma wft_weaken : forall E G F T,
  wft (E ++ G) T ->
  uniq (E ++ F ++ G) ->
  wft (E ++ F ++ G) T.
Proof.
  intros. gen_eq (E ++ G) as K. gen E F G.
  induction H; intros; subst; eauto.
  (* case: all *)
  apply wft_all with (L `union` dom (E0 ++ F ++ G)); auto;
    intros; destruct_notin.
 apply_ih_bind* H1. 
Qed.

(** Through narrowing *)

Lemma wft_narrow : forall E F V U T X,
  wft (E ++ X ~<: V ++ F) T ->
  uniq (E ++ X ~<: U ++ F) -> 
  wft (E ++ X ~<: U ++ F) T.
Proof.
  intros. gen_eq (E ++ X ~<: V ++ F) as K. gen E F.
  induction H; intros; subst; eauto.
  analyze_binds H.
    eapply wft_var. apply* binds_app_2.
    inversion BindsTacVal; subst.
    apply (@wft_var U). apply* binds_app_3.
    eapply wft_var. apply* binds_app_3.
  apply wft_all with (L `union` dom (E0 ++ X ~<: U ++ F));
    auto; intros; destruct_notin.
  apply_ih_bind H1; auto.
Qed.

(** Through strengthening *)

Lemma wft_strengthen : forall E F x U T,
 wft (E ++ x ~: U ++ F) T -> wft (E ++ F) T.
Proof.
  intros. gen_eq (E ++ x ~: U ++ F) as G. gen E.
  induction H; intros E0 EQ; subst; auto.
  apply* (@wft_var U0).
  analyze_binds H; try discriminate; auto*.
  apply wft_all with L; auto; intros; destruct_notin.
  apply_ih_bind* H1.
Qed.

(** Through type substitution *)

Tactic Notation "apply_empty" constr(lemma) :=
  let H := fresh in poses H (@lemma empty_env);
    simpl in H; simpl_alist in H; eapply H; simpl_alist in *; clear H.

Tactic Notation "apply_empty" "*" constr(lemma) :=
  apply_empty lemma; auto*.  

Tactic Notation "apply_ih_map_bind" constr(H) :=
  do_rew app_assoc_map_push (eapply H).

Tactic Notation "apply_ih_map_bind" "*" constr(H) :=
  do_rew* app_assoc_map_push (eapply H).

Lemma wft_subst_tb : forall E F Q P Z T,
  wft (E ++ Z ~<: Q ++ F) T ->
  wft F P ->
  uniq (map (subst_tb Z P) E ++ F) ->
  wft (map (subst_tb Z P) E ++ F) (M_yy.M.Tfsubst T Z P).
Proof.
  introv WT WP. gen_eq (E ++ Z ~<: Q ++ F) as G. gen E.
  induction WT; intros E0 EQ Ok; subst; gsimpl; simpl_alist in *. 
  apply_empty* wft_weaken.
  analyze_binds H.
    apply wft_var with (M_yy.M.Tfsubst U Z P).
    apply* binds_app_2.
    replace (bind_sub (M_yy.M.Tfsubst U Z P))
      with ((subst_tb Z P) (bind_sub U)); auto.
  apply wft_var with U.
  apply* binds_app_3.
  apply wft_all with (L `union` {{Z}} `union` dom (map (subst_tb Z P) E0 ++ F));
    auto; intros; destruct_notin.
   unsimpl ((subst_tb Z P) (bind_sub T1)).
   puts type_from_wft.
   puts type_Ywf.
   grewrite Ybfsubst_permutation_var_wf; eauto. 
   apply_ih_map_bind H0; auto.
Qed.

(** Through type reduction *)

Lemma wft_open : forall E U T1 T2,
  uniq E ->
  wft E (typ_all T1 T2) -> 
  wft E U ->
  wft E (M_yy.M.Tbsubst T2 0 U).
Proof.
  introv Ok WA WU. inversions WA.
  pick fresh X for (L `union` M_yy.M.Tfv T2); intros; destruct_notin. 
  puts type_from_wft.
  puts type_Ywf.
  rewrite M_yy.M.Tbfsubst_var_intro with (a:=X); eauto.
  poses K (@wft_subst_tb empty_env); simpls*.
Qed.

(* ********************************************************************** *)
(** * Relations between well-formed environment and types well-formed
  in environments *)

(** If an environment is well-formed, then it does not contain duplicated keys. *)

Lemma ok_from_okt : forall E,
  okt E -> uniq E.
Proof.
  induction 1; unfold empty_env; auto. 
Qed.

Hint Extern 1 (uniq _) => apply ok_from_okt.

(** Extraction from a subtyping assumption in a well-formed environments *)

Lemma wft_from_env_has_sub : forall x U E,
  okt E -> binds x (bind_sub U) E -> wft E U.
Proof.
  unfold binds. induction E as [|(y,a)]; simpl; intros Ok B; simpl_alist in *.
  contradictions*.
  inversions B. 
    inversion H; subst. inversions Ok. apply_empty* wft_weaken.
  apply_empty* wft_weaken. inversions* Ok.
Qed.

(** Extraction from a typing assumption in a well-formed environments *)

Lemma wft_from_env_has_typ : forall x U E,
  okt E -> binds x (bind_typ U) E -> wft E U.
Proof.
  unfold binds. induction E as [|(y,a)]; simpl; intros Ok B; simpl_alist in *.
  contradictions*.
  inversions B.
    inversion H; subst; inversions Ok. apply_empty* wft_weaken.
  apply_empty* wft_weaken. inversions* Ok.
Qed.

(** Extraction from a well-formed environment *)

Lemma wft_from_okt_typ : forall x T E,
  okt (x ~: T ++ E) -> wft E T.
Proof.
  intros. inversions* H.
Qed.

Lemma wft_from_okt_sub : forall x T E,
  okt (x ~<: T ++ E) -> wft E T.
Proof.
  intros. inversions* H.
Qed.

Lemma wft_weaken_right : forall T E F,
  wft F T ->
  uniq (E ++ F) ->
  wft (E ++ F) T.
Proof.
  intros. apply_empty* wft_weaken.
Qed.

Hint Resolve wft_weaken_right.

Hint Immediate wft_from_env_has_sub wft_from_env_has_typ.
Hint Resolve wft_subst_tb.
Hint Resolve wft_from_okt_typ wft_from_okt_sub.


(** ** Properties of well-formedness of an environment *)

(** Through narrowing *)

Lemma okt_narrow : forall E F V U X,
  okt (E ++ X ~<: V ++ F) ->
  wft F U ->
  okt (E ++ X ~<: U ++ F).
Proof.
  induction E as [|(Y,B)]; simpl; introv Ok Wf; simpl_alist in *; inversion Ok; auto; simpl_env in *.
  apply okt_sub; eauto. apply wft_narrow with V; auto.
  apply uniq_dom_only with (bind_sub V); auto.
  repeat rewrite dom_app; simpl_alist in *; solve_notin.
  apply okt_typ; eauto. apply wft_narrow with V; auto. 
  apply uniq_dom_only with (bind_sub V); auto.
  repeat rewrite dom_app; simpl_alist in *; solve_notin.
Qed.

(** Through strengthening *)

Lemma okt_strengthen : forall E F x T,
  okt (E ++ x ~: T ++ F) ->
  okt (E ++ F).
Proof.
  induction E as [|(Y,B)]; simpl; introv Ok; simpl_alist in *;
    inversions Ok; auto; simpl_env in *.
  apply okt_sub; eauto. use wft_strengthen.
  rewrite dom_app; simpl_alist in *; solve_notin.    
  apply okt_typ; eauto. use wft_strengthen. 
  rewrite dom_app; simpl_alist in *; solve_notin.    
Qed.

(** Through type substitution *)

Lemma okt_subst_tb : forall E F Q P Z,
  okt (E ++ Z ~<: Q ++ F) ->
  wft F P ->
  okt (map (subst_tb Z P) E ++ F).
Proof.
  induction E as [|(Y,B)]; simpl; introv Ok WP; 
   simpl_env in *; inversions Ok; simpl subst_tb; simpl_env in *; auto.
  apply okt_sub; eauto; solve_notin.
  apply okt_typ; eauto; solve_notin. 
Qed.

(** Automation *)

Hint Resolve okt_narrow okt_subst_tb wft_weaken.
Hint Immediate okt_strengthen.


(* ********************************************************************** *)
(** ** Environment is unchanged by substitution from a fresh name *)

Lemma notin_fv_wf : forall E X T,
  wft E T -> X # E -> X `notin` M_yy.M.Tfv T.
Proof.
  induction 1; intros Fr; gsimpl.
  apply notin_singleton_2. intro. subst. eauto using binds_dom_contradiction.
  pick_fresh X0; destruct_notin.
  assert (X `notin` M_yy.M.Tfv (T2 open_tt_var X0)); auto.  
  assert (X `notin` M_yy.M.Tfv T2); eauto using M_yy.M.Tfv_pass_binder_1.
Qed.

Lemma map_subst_tb_id : forall G Z P,
  okt G -> Z # G -> G = map (subst_tb Z P) G.
Proof.
  induction 1; simpl; intros Fr; auto; destruct_notin.
  rewrite* <- IHokt. rewrite* <- M_yy.M.Tfsubst_no_occur. apply* notin_fv_wf.
  rewrite* <- IHokt. rewrite* <- M_yy.M.Tfsubst_no_occur. apply* notin_fv_wf.
Qed.


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

Lemma sub_regular : forall E S T,
  sub E S T -> okt E /\ wft E S /\ wft E T.
Proof.
  induction 1; auto*; split; auto*; split;
  apply wft_all with L; try tauto;
  intros; destructi~ (H1 X H2); auto; simpl; apply_empty* wft_narrow. 
Qed.

(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e T,
  typing E e T -> okt E /\ term e /\ wft E T.
Proof.
  induction 1.
  splits*.
  splits.
      pick_fresh y. forward~ (H0 y) as K. destructs K. inversions* H1.
    apply term_abs with L.
      pick_fresh y. forward~ (H0 y) as K. destructs K. 
      inversions H1. apply* type_from_wft.
    intros. forward~ (H0 x) as K. destructs K. auto.
  pick_fresh y. forward~ (H0 y) as K. destructs K. 
  apply* wft_arrow. inversions* H1.  apply_empty* wft_strengthen.
  splits*. destructs IHtyping1. inversion* H4.
  splits.
      pick_fresh y. forward~ (H0 y) as K. destructs K. inversions* H1.
    apply term_tabs with L.
      pick_fresh y. forward~ (H0 y) as K. destructs K. 
      inversions H1. apply* type_from_wft.
    intros. forward~ (H0 X) as K. destructs K. auto.
  apply wft_all with L.
    pick_fresh y. forward~ (H0 y) as K. destructs K. inversions* H1. 
  intros. forward~ (H0 X) as K. destructs K. auto.
  splits*; destructs (sub_regular H0).
    apply* term_tapp. use type_from_wft.
  apply* wft_open.
  splits*. destructs (sub_regular H0). auto.
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
  induction 1; split; use value_regular.
  inversions H. pick fresh y for (L `union` M_tt.M.Tfv e1); destruct_notin.
  rewrite M_tt.M.Tbfsubst_var_intro with (a:=y); simpl; auto.
  inversions H. pick fresh Y for (L `union` M_yt.M.Tfv e1); destruct_notin.
  rewrite M_yt.M.Tbfsubst_var_intro with (a:=Y); simpl; auto.
Qed.

(** Automation *)

Hint Extern 1 (okt ?E) =>
  match goal with
  | H: sub _ _ _ |- _ => apply (proj31 (sub_regular H))
  | H: typing _ _ _ |- _ => apply (proj31 (typing_regular H))
  end.

Hint Extern 1 (wft ?E ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj33 (typing_regular H))
  | H: sub E T _ |- _ => apply (proj32 (sub_regular H))
  | H: sub E _ T |- _ => apply (proj33 (sub_regular H))
  end.

Hint Extern 1 (type ?T) =>
  let go E := apply (@type_from_wft E); auto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
  end.

Hint Extern 1 (term ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj32 (typing_regular H))
  | H: red ?e _ |- _ => apply (proj1 (red_regular H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular H))
  end.
