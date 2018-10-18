Set Implicit Arguments.

Require Import LNameless_Meta.
Require Import LNameless_Meta_Env.
Require Import LNameless_Isomorphism.
Require Import LNameless_Fsub_Iso.
Require Export LN_Template.

Module Export M_tt := FWellformed Iso_trm Iso_trm.
Module Export M_yy := FWellformed Iso_typ Iso_typ.
Module Export M_yt := FWellformed Iso_typ Iso_trm.
Module Export M_ty := FWellformed Iso_trm Iso_typ.

Module MT := Iso_trm.
Module MY := Iso_typ.

  Hint Unfold M_tt.M.Twf M_tt.M.Twf_basic M_tt.M.gTwf M_tt.M.gTwf_basic.
  Hint Unfold M_tt.M.Tfsubst M_tt.M.Tbsubst M_tt.M.Tfv M_tt.M.TwfT M_yt.TenvT M_tt.M.TSize.

  (**************************************************************)
  (** * Tactics I *)
  (**************************************************************)

  Hint Resolve MT.To_From MT.From_To MY.To_From MY.From_To.

  Hint Rewrite MT.From_To MT.To_From : isorew.
  Hint Rewrite MY.From_To MY.To_From : isorew.
  Hint Rewrite <- M_tt.M.From_Tfsubst : isorew.
  Hint Rewrite <- M_tt.M.From_Tbsubst : isorew.
  Hint Rewrite conv_id : isorew.

  Hint Rewrite <- M_tt.M.From_Tfsubst_var : isorew.
  Hint Rewrite <- M_tt.M.From_Tbsubst_var : isorew.

  (** A tactic unfolding everything *)

  Ltac gunfoldo :=
    unfold M_tt.M.Twf, M_tt.M.Twf_basic in *;
    unfold M_tt.M.gTwf, M_tt.M.gTwf_basic, wf_basic in *;
    unfold M_tt.M.Tfsubst, M_tt.M.Tbsubst, M_tt.M.Tfv, M_tt.M.TwfT, M_yt.TenvT, M_tt.M.TSize in *;
    intros;
    repeat rewrite MT.To_From in *;
    repeat rewrite MT.From_To in *;
    repeat rewrite MY.To_From in *;
    repeat rewrite MY.From_To in *;
    simpl in *; 
    simpl_env in *.

  (** [grewrite] is can be used in order to apply generic lemmas
     which envolve variables cases such as

     - Tbfsubst_var_intro, etc. *)
  
  Tactic Notation "grewrite" ident(Y) :=
    let H := fresh in
      poses H Y; simpl in * |-; rewrite H; auto; clear H.

  Tactic Notation "grewrite" "<-" ident(Y) :=
    let H := fresh in
      poses H Y; simpl in * |-; rewrite <- H; auto; clear H.


  (** Domain-specific infrastructure: Lemmas involving multiple binders *)

  Lemma Tfsubst_Lemma : forall (T U V:MT.TT)(a b : nat),
    a <> b ->
    a `notin` (M_tt.M.Tfv V) ->
    M_tt.M.Tfsubst (M_tt.M.Tfsubst T a U) b V =
    M_tt.M.Tfsubst (M_tt.M.Tfsubst T b V) a (M_tt.M.Tfsubst U b V).
  Proof.
    gunfoldo; f_equal; auto using fsubstitution.
  Qed.

  Hint Resolve M_tt.M.gTwf_Twf M_tt.M.Twf_gTwf.

  Hint Resolve M_tt.M.gTwf_from_Twf_basic M_tt.M.Twf_basic_from_gTwf.

  (* Tbsubst_homo_1 => Tbsubst_homo_wf *)
  Lemma Tbsubst_homo_wf : forall (T:MT.TT) k l (U V:MT.TT),
    k <> l ->
    M_tt.M.Twf U ->
    M_tt.M.Twf V ->
    M_tt.M.Tbsubst (M_tt.M.Tbsubst T k U) l V = M_tt.M.Tbsubst (M_tt.M.Tbsubst T l V) k U.
  Proof.
    introv Hneq Hu Hv.
    puts (M_tt.M.Twf_gTwf Hu); clear Hu.
    puts (M_tt.M.Twf_gTwf Hv); clear Hv.
    gunfoldo; f_equal; apply* bsubstitution_homo_wf.
  Qed.

  (* Tbsubst_var_twice_1 => Tbsubst_var_twice_wf *)
  Lemma Tbsubst_var_twice_wf : forall (T:MT.TT) k (U V:MT.TT),
    M_tt.M.Twf V ->
    M_tt.M.Tbsubst T k V = M_tt.M.Tbsubst (M_tt.M.Tbsubst T k V) k U.
  Proof.
    introv Hwf.
    puts (M_tt.M.Twf_gTwf Hwf); clear Hwf.
    gunfoldo; f_equal; apply* bsubstitution_var_twice_wf.
  Qed.

  Lemma Tbfsubst_permutation_core : forall (T U V:MT.TT) (a:nat), 
    M_tt.M.TwfT U ->
    forall (k:nat),
      M_tt.M.Tbsubst (M_tt.M.Tfsubst T a U) k (M_tt.M.Tfsubst V a U)
      = M_tt.M.Tfsubst (M_tt.M.Tbsubst T k V) a U.
  Proof.
    gunfoldo; rewrite bfsubst_permutation_core; auto.
  Qed.

  Lemma Tbfsubst_permutation_core_wf : forall (T U V:MT.TT) (a:nat), 
    M_tt.M.Twf U ->
    forall (k:nat),
      M_tt.M.Tbsubst (M_tt.M.Tfsubst T a U) k (M_tt.M.Tfsubst V a U)
      = M_tt.M.Tfsubst (M_tt.M.Tbsubst T k V) a U.
  Proof.
    introv H.
    cut (M_tt.M.gTwf U); auto 2.
    gunfoldo; rewrite bfsubst_permutation_core_wf; auto.
  Qed.

  Lemma Tbfsubst_permutation_ind : forall (T U V:MT.TT) (a:nat), 
    M_tt.M.TwfT U ->
    a `notin` (M_tt.M.Tfv V) ->
    forall (k:nat),
      M_tt.M.Tbsubst (M_tt.M.Tfsubst T a U) k V = M_tt.M.Tfsubst (M_tt.M.Tbsubst T k V) a U.
  Proof.
    gunfoldo; rewrite bfsubst_permutation_ind; auto.
  Qed.

  Lemma Tbfsubst_permutation_ind_wf : forall (T U V:MT.TT) (a:nat), 
    M_tt.M.Twf U ->
    a `notin` (M_tt.M.Tfv V) ->
    forall (k:nat),
      M_tt.M.Tbsubst (M_tt.M.Tfsubst T a U) k V = M_tt.M.Tfsubst (M_tt.M.Tbsubst T k V) a U.
  Proof.
    introv H.
    cut (M_tt.M.gTwf U); auto 2.
    gunfoldo; rewrite bfsubst_permutation_ind_wf; auto.
  Qed.

  Lemma Tbfsubst_permutation_wfT : forall (T U V:MT.TT) (a:nat),
    M_tt.M.TwfT U -> 
    a `notin` (M_tt.M.Tfv V) ->
    M_tt.M.Tbsubst (M_tt.M.Tfsubst T a U) 0 V = M_tt.M.Tfsubst (M_tt.M.Tbsubst T 0 V) a U.
  Proof.
    gunfoldo; f_equal; auto using bfsubst_permutation_wfT.
  Qed.

  Lemma Tbfsubst_permutation_wf : forall (T U V:MT.TT) (a:nat),
    M_tt.M.Twf U -> 
    a `notin` (M_tt.M.Tfv V) ->
    M_tt.M.Tbsubst (M_tt.M.Tfsubst T a U) 0 V = M_tt.M.Tfsubst (M_tt.M.Tbsubst T 0 V) a U.
  Proof.
    introv H.
    cut (M_tt.M.gTwf U); auto 2.
    gunfoldo; f_equal; auto using bfsubst_permutation_wf.
  Qed.

  Lemma Tbfsubst_permutation_var_wfT : forall (T U:MT.TT) (a b:nat),
    a <> b ->
    M_tt.M.TwfT U -> 
    M_tt.M.Tbsubst (M_tt.M.Tfsubst T a U) 0 (MT.To (Var MT.RR (inl b))) =
    M_tt.M.Tfsubst (M_tt.M.Tbsubst T 0 (MT.To (Var MT.RR (inl b)))) a U.
  Proof.
    gunfoldo; f_equal; auto using bfsubst_permutation_var_wfT.
  Qed.

  Lemma Tbfsubst_permutation_var_wf : forall (T U:MT.TT) (a b:nat),
    a <> b ->
    M_tt.M.Twf U -> 
    M_tt.M.Tbsubst (M_tt.M.Tfsubst T a U) 0 (MT.To (Var MT.RR (inl b))) =
    M_tt.M.Tfsubst (M_tt.M.Tbsubst T 0 (MT.To (Var MT.RR (inl b)))) a U.
  Proof.
    introv H H0.
    cut (M_tt.M.gTwf U); auto 2.
    gunfoldo; f_equal; auto using bfsubst_permutation_var_wf.
  Qed.


  (**************************************************************)
  (** * Preservation of well-formedness *)
  (**************************************************************)

  (** Substitutions preserve well-formedness. *)

  (* wfT_Tfsubst => TwfT_Tfsubst *)
  Lemma TwfT_Tfsubst : forall (T U:MT.TT) (a:nat),
    M_tt.M.TwfT T ->
    M_tt.M.TwfT U ->
    M_tt.M.TwfT (M_tt.M.Tfsubst T a U).
  Proof.
    gunfoldo; auto using wfT_fsubst.
  Qed.

  (* wf_Tfsubst => Twf_Tfsubst *)
  Lemma Twf_Tfsubst : forall (T U:MT.TT) (a:nat),
    M_tt.M.Twf T ->
    M_tt.M.Twf U ->
    M_tt.M.Twf (M_tt.M.Tfsubst T a U).
  Proof.
    introv H H0.
    cut (M_tt.M.gTwf T); auto 2.
    cut (M_tt.M.gTwf U); auto 2; intros.
    cut (M_tt.M.gTwf (M_tt.M.Tfsubst T a U)); auto 2.
    gunfoldo; auto using wf_fsubst.
  Qed.


  (**************************************************************)
  (** * Well-formedness in an environment *)
  (**************************************************************)

  (** Well-formed terms/types in an environment are well-formed. *)

  Lemma TenvT_TwfT : forall (E:env MY.TT)(T:MT.TT), 
    M_yt.TenvT E T ->
    M_tt.M.TwfT T.
  Proof.
    gunfoldo; eauto using envT_wfT.
  Qed.

  Hint Resolve TenvT_TwfT.

  (** Bound variable substitution has no effect on well-formed terms/types. *)

  (* Tbsubst_on_env => TenvT_Twf *)
  Lemma TenvT_Twf : forall (E:env MY.TT)(T:MT.TT), 
    M_yt.TenvT E T -> forall (k:nat) (U:MT.TT), T = M_tt.M.Tbsubst T k U.
  Proof.
    intros; eauto using TenvT_TwfT, M_tt.M.TwfT_Twf.
  Qed.


  (** Environments capture all the parameters in terms/types *)

  Lemma envT_Tfv : forall (E:env MY.TT) (T:MT.TT) (a:atom),
    a # E -> M_yt.TenvT E T -> a `notin` M_tt.M.Tfv T.
  Proof.
    gunfoldo;
    apply envT_fv with (r':= MY.RR)(E:= map MY.From E); auto.
  Qed.

  Lemma TenvT_dom_subset : forall (E:env MY.TT) (T:MT.TT),
    M_yt.TenvT E T -> M_tt.M.Tfv T [<=] dom E.
  Proof.
    gunfoldo; intros a H0; apply dom_map_2 with (f:=MY.From).
    generalize dependent a; apply envT_dom_subset; auto.
  Qed.

  (** Parameter substitution for a fresh parameter *)

  Lemma Tfsubst_fresh : forall (E:env MY.TT)(T U:MT.TT)(a:nat),
    a # E -> M_yt.TenvT E T -> T = M_tt.M.Tfsubst T a U.
  Proof.
    gunfoldo; erewrite <- fsubst_fresh; eauto; auto.  
  Qed.


  (** Permutation of substitutions when [TenvT] holds *)
  
  Lemma Tbfsubst_permutation : forall (E:env MY.TT)(T U V:MT.TT)(a:nat),
    M_yt.TenvT E U -> 
    a `notin` (M_tt.M.Tfv V) ->
    M_tt.M.Tbsubst (M_tt.M.Tfsubst T a U) 0 V = M_tt.M.Tfsubst (M_tt.M.Tbsubst T 0 V) a U.
  Proof.
    gunfoldo; f_equal; eauto using bfsubst_permutation.
  Qed.

  Lemma Tbfsubst_permutation_var : forall (E:env MY.TT)(T U:MT.TT)(a b:nat),
    a <> b ->
    M_yt.TenvT E U -> 
    M_tt.M.Tbsubst (M_tt.M.Tfsubst T a U) 0 (MT.To (Var MT.RR (inl b))) =
    M_tt.M.Tfsubst (M_tt.M.Tbsubst T 0 (MT.To (Var MT.RR (inl b)))) a U.
  Proof.
    gunfoldo; f_equal; eauto using bfsubst_permutation_var.
  Qed.

  (** Well-formed terms are term containing no free occurence of
     any term or type variables. *)

  Definition TTwfT (T:MT.TT) : Prop :=
    M_tt.M.TwfT T /\ M_yt.M.TwfT T.

  Definition TTwf (T:MT.TT) : Prop :=
    M_tt.M.Twf T /\ M_yt.M.Twf T. 

  Definition TTwf_basic (T:MT.TT) : Prop :=
    M_tt.M.Twf_basic T /\ M_yt.M.Twf_basic T.

  Definition gTTwf (T:MT.TT) : Prop :=
    M_tt.M.gTwf T /\ M_yt.M.gTwf T.

  Definition gTTwf_basic (T:MT.TT) : Prop :=
    M_tt.M.gTwf_basic T /\ M_yt.M.gTwf_basic T. 


  Definition TTenvT (E:env MY.TT)(F:env MY.TT)(T:MT.TT) : Prop :=
    M_yt.TenvT E T /\ M_yt.THenvT F T.


  Inductive YTwf_env : env MY.TT -> env MY.TT -> Prop :=
  | YTwf_empty :
    YTwf_env nil nil
  | YTwf_sub : forall E F X T,
    YTwf_env E F -> M_yy.YTenvT E F T -> X # E -> YTwf_env (X ~ T ++ E) F
  | YTwf_typ : forall E F x T,
    YTwf_env E F -> M_yy.YTenvT E F T -> x # F -> YTwf_env E (x ~ T ++ F).

  Hint Constructors YTwf_env.

  Hint Resolve YTwf_empty YTwf_sub YTwf_typ.


  Hint Unfold M_yt.M.Tfsubst M_yt.M.Tbsubst M_yt.M.Tfv M_yt.M.TwfT M_yt.M.Twf M_yt.M.Twf_basic M_yt.M.gTwf M_yt.M.gTwf_basic M_yt.THenvT.
  Hint Unfold TTwfT TTenvT TTwf TTwf_basic.
  Hint Unfold M_yy.M.Tfsubst M_yy.M.Tbsubst M_yy.M.Tfv M_yy.M.TwfT M_yy.M.Twf M_yy.M.Twf_basic M_yy.M.gTwf M_yy.M.gTwf_basic M_yy.YenvT M_yy.TenvT M_yy.Ywf_env M_yy.M.TSize.
  Hint Unfold M_ty.M.Tfsubst M_ty.M.Tbsubst M_ty.M.Tfv M_ty.M.TwfT M_ty.M.Twf M_ty.M.Twf_basic M_ty.M.gTwf M_ty.M.gTwf_basic M_ty.YHenvT.
  Hint Unfold M_yy.YTenvT.


  (**************************************************************)
  (** Tactics I *)
  (**************************************************************)

  Hint Resolve MT.To_From MT.From_To MY.To_From MY.From_To.

  Hint Rewrite <- M_yt.M.From_Tfsubst : isorew.
  Hint Rewrite <- M_yt.M.From_Tbsubst : isorew.
  Hint Rewrite <- M_yy.M.From_Tfsubst  : isorew.
  Hint Rewrite <- M_yy.M.From_Tbsubst  : isorew.
  Hint Rewrite <- M_ty.M.From_Tfsubst : isorew.
  Hint Rewrite <- M_ty.M.From_Tbsubst : isorew.
  Hint Rewrite <- M_yt.M.From_Tfsubst_var : isorew.
  Hint Rewrite <- M_yt.M.From_Tbsubst_var : isorew.
  Hint Rewrite <- M_yy.M.From_Tfsubst_var  : isorew.
  Hint Rewrite <- M_yy.M.From_Tbsubst_var  : isorew.
  Hint Rewrite <- M_ty.M.From_Tfsubst_var : isorew.
  Hint Rewrite <- M_ty.M.From_Tbsubst_var : isorew.

  (** A tactic unfolding everything *)

  Ltac gunfold :=
    unfold TTwf, TTwf_basic, M_tt.M.Twf, M_tt.M.Twf_basic, M_yt.M.Twf, M_yt.M.Twf_basic in *;
    unfold M_yy.M.Twf, M_yy.M.Twf_basic, M_ty.M.Twf, M_ty.M.Twf_basic in *;
    unfold gTTwf, gTTwf_basic, M_tt.M.gTwf, M_tt.M.gTwf_basic, M_yt.M.gTwf, M_yt.M.gTwf_basic in *;
    unfold M_yy.M.gTwf, M_yy.M.gTwf_basic, M_ty.M.gTwf, M_ty.M.gTwf_basic, wf_basic in *;
    unfold TTwfT, TTenvT, M_yy.YTenvT in *; 
    unfold M_tt.M.Tfsubst, M_tt.M.Tbsubst, M_tt.M.Tfv, M_tt.M.TwfT, M_yt.TenvT, M_tt.M.TSize in *;
    unfold M_yt.M.Tfsubst, M_yt.M.Tbsubst, M_yt.M.Tfv, M_yt.M.TwfT, M_yt.THenvT in *;
    unfold M_yy.M.Tfsubst, M_yy.M.Tbsubst, M_yy.M.Tfv, M_yy.M.TwfT, M_yy.YenvT, M_yy.TenvT, M_yy.M.TSize in *;
    unfold M_ty.M.Tfsubst, M_ty.M.Tbsubst, M_ty.M.Tfv, M_ty.M.TwfT, M_ty.YHenvT in *;
    unfold M_yy.Ywf_env in *;
    intros;
    repeat rewrite MT.To_From in *;
    repeat rewrite MT.From_To in *;
    repeat rewrite MY.To_From in *;
    repeat rewrite MY.From_To in *;
    simpl in *; simpl_env in *.


  (** Substitution Lemma *)

  Lemma THfsubst_Lemma : forall (T:MT.TT)(U V:MY.TT)(a b : nat),
    a <> b ->
    a `notin` (M_yy.M.Tfv V) ->
    M_yt.M.Tfsubst (M_yt.M.Tfsubst T a U) b V =
    M_yt.M.Tfsubst (M_yt.M.Tfsubst T b V) a (M_yy.M.Tfsubst U b V).
  Proof.
    gunfold; f_equal; auto using fsubstitution.
  Qed.

  Lemma Yfsubst_Lemma : forall (T U V:MY.TT)(a b : nat),
    a <> b ->
    a `notin` (M_yy.M.Tfv V) ->
    M_yy.M.Tfsubst (M_yy.M.Tfsubst T a U) b V =
    M_yy.M.Tfsubst (M_yy.M.Tfsubst T b V) a (M_yy.M.Tfsubst U b V).
  Proof.
    gunfold; f_equal; auto using fsubstitution.
  Qed.

  Lemma YHfsubst_Lemma : forall (T:MY.TT)(U V:MT.TT)(a b : nat),
    a <> b ->
    a `notin` (M_tt.M.Tfv V) ->
    M_ty.M.Tfsubst (M_ty.M.Tfsubst T a U) b V =
    M_ty.M.Tfsubst (M_ty.M.Tfsubst T b V) a (M_tt.M.Tfsubst U b V).
  Proof.
    gunfold; f_equal; auto using fsubstitution.
  Qed.

  (* wfT_THbsubst_core_1 => THbsubst_hetero_core_1 *)
  Lemma THbsubst_hetero_core_1 : forall (T V: MT.TT)(U: MY.TT) k j,
    MT.RR <> MY.RR ->
    M_tt.M.Tbsubst T j V = M_yt.M.Tbsubst (M_tt.M.Tbsubst T j V) k U ->
    T = M_yt.M.Tbsubst T k U.
  Proof.
    gunfold; rewrite <- bsubst_hetero_core with (V:= MT.From V) (j:=j); auto using MT.To_inj.
  Qed.

  (* wfT_THbsubst_core_2 => THbsubst_hetero_core_2 *)
  Lemma THbsubst_hetero_core_2 : forall (T U: MT.TT)(V: MY.TT) k j,
    MT.RR <> MY.RR ->
    M_yt.M.Tbsubst T j V = M_tt.M.Tbsubst (M_yt.M.Tbsubst T j V) k U ->
    T = M_tt.M.Tbsubst T k U.
  Proof.
    gunfold; rewrite <- bsubst_hetero_core with (V:= MY.From V) (j:=j); auto using MT.To_inj.
  Qed.

  Lemma TTwf_basic_from_TTwf : forall (T:MT.TT), TTwf T -> TTwf_basic T.
  Proof.
    unfold TTwf; split;
      inversion H; [apply M_tt.M.Twf_basic_from_Twf | apply M_yt.M.Twf_basic_from_Twf]; auto.
  Qed.

  Lemma TTwf_from_TTwf_basic : forall (T:MT.TT), TTwf_basic T -> TTwf T.
  Proof.
    unfold TTwf_basic; split; inversion H;
      [apply M_tt.M.Twf_from_Twf_basic | apply M_yt.M.Twf_from_Twf_basic]; auto.
  Qed.

  Lemma TTwf_gTTwf_basic : forall (T:MT.TT), TTwf_basic T -> gTTwf_basic T.
  Proof.
    unfold TTwf_basic; split; inversion H;
      [apply M_tt.M.Twf_gTwf_basic | apply M_yt.M.Twf_gTwf_basic]; auto.
  Qed.

  Lemma gTTwf_TTwf_basic : forall (T:MT.TT), gTTwf_basic T -> TTwf_basic T.
  Proof.
    unfold gTTwf_basic; split; inversion H;
      [apply M_tt.M.gTwf_Twf_basic | apply M_yt.M.gTwf_Twf_basic]; auto.
  Qed.

  Lemma TTwf_gTTwf : forall (T:MT.TT), TTwf T -> gTTwf T.
  Proof.
    unfold TTwf; split; inversion H;
      [apply M_tt.M.Twf_gTwf | apply M_yt.M.Twf_gTwf]; auto.
  Qed.

  Lemma gTTwf_TTwf : forall (T:MT.TT), gTTwf T -> TTwf T.
  Proof.
    unfold gTTwf; split; inversion H;
      [apply M_tt.M.gTwf_Twf | apply M_yt.M.gTwf_Twf]; auto.
  Qed.

  Hint Resolve M_yt.M.gTwf_Twf M_yt.M.Twf_gTwf.
  Hint Resolve gTTwf_TTwf TTwf_gTTwf.
  Hint Resolve M_yy.M.gTwf_Twf M_yy.M.Twf_gTwf.
  Hint Resolve M_ty.M.gTwf_Twf M_ty.M.Twf_gTwf.

  (* TTwfT_Tbsubst_id => TTwfT_Twf *)
  Lemma TTwfT_Twf : forall (T:MT.TT),
    TTwfT T ->
    forall (k:nat) (U:MT.TT), T = M_tt.M.Tbsubst T k U.
  Proof.
    introv HTT; inversion HTT; auto using M_tt.M.TwfT_Twf.
  Qed.

  (* TTwfT_THbsubst_id => TTwfT_THwf *)
  Lemma TTwfT_THwf : forall (T:MT.TT),
    TTwfT T ->
    forall (k:nat) (U:MY.TT), T = M_yt.M.Tbsubst T k U.
  Proof.
    introv HTT; inversion HTT; auto using M_yt.M.TwfT_Twf.
  Qed.

  (* THbsubst_homo_1 => THbsubst_homo_wf *)
  Lemma THbsubst_homo_wf : forall (T:MT.TT) k l (U V:MY.TT),
    k <> l ->
    M_yy.M.Twf U ->
    M_yy.M.Twf V ->
    M_yt.M.Tbsubst (M_yt.M.Tbsubst T k U) l V = M_yt.M.Tbsubst (M_yt.M.Tbsubst T l V) k U.
  Proof.
    introv Hneq Hu Hv.
    puts (M_yy.M.Twf_gTwf Hu); clear Hu.
    puts (M_yy.M.Twf_gTwf Hv); clear Hv.
    gunfold; f_equal; apply* bsubstitution_homo_wf.
  Qed.

  (* Ybsubst_homo_1 => Ybsubst_homo_wf *)
  Lemma Ybsubst_homo_wf : forall (T:MY.TT) (k l:atom) (U V:MY.TT),
    k <> l ->
    M_yy.M.Twf U ->
    M_yy.M.Twf V ->
    M_yy.M.Tbsubst (M_yy.M.Tbsubst T k U) l V = M_yy.M.Tbsubst (M_yy.M.Tbsubst T l V) k U.
  Proof.
    introv Hneq Hu Hv.
    puts (M_yy.M.Twf_gTwf Hu); clear Hu.
    puts (M_yy.M.Twf_gTwf Hv); clear Hv.
    gunfold; f_equal; apply* bsubstitution_homo_wf.
  Qed.

  (* THbsubst_hetero_1 => THbsubst_hetero_wf *)
  Lemma THbsubst_hetero_wf : forall (T:MT.TT) k l (U:MY.TT) (V:MT.TT),
    MY.RR <> MT.RR ->
    noRepr MY.RR ->
    M_yt.M.Twf V ->
    M_tt.M.Tbsubst (M_yt.M.Tbsubst T k U) l V
    = M_yt.M.Tbsubst (M_tt.M.Tbsubst T l V) k U.
  Proof.
    introv Hnew Hno Hv.
    puts (M_yt.M.Twf_gTwf Hv); clear Hv.
    gunfold; f_equal; apply* bsubstitution_hetero_wf.
    apply* noRepr_wf_hetero.
  Qed.

  Lemma THbsubst_hetero : forall (T:MT.TT) k l a b,
    MY.RR <> MT.RR ->
    M_tt.M.Tbsubst (M_yt.M.Tbsubst T k (MY.To (Var MY.RR (inl a)))) l (MT.To (Var MT.RR (inl b)))
    = M_yt.M.Tbsubst (M_tt.M.Tbsubst T l (MT.To (Var MT.RR (inl b)))) k (MY.To (Var MY.RR (inl a))).
  Proof.
    gunfold; f_equal; apply bsubstitution_hetero; auto.
  Qed.

  (** Consecutive substitution of the same (bound) variable has no effect. *)

  (* THbsubst_var_twice_1 => THbsubst_var_twice_wf *)
  Lemma THbsubst_var_twice_wf : forall (T:MT.TT) k (U V:MY.TT),
    M_yy.M.Twf V ->
    M_yt.M.Tbsubst T k V = M_yt.M.Tbsubst (M_yt.M.Tbsubst T k V) k U.
  Proof.
    introv Hwf.
    puts (M_yy.M.Twf_gTwf Hwf); clear Hwf.
    gunfold; f_equal; apply* bsubstitution_var_twice_wf.
  Qed.

  (* Ybsubst_var_twice_1 => Ybsubst_var_twice_wf *) 
  Lemma Ybsubst_var_twice_wf : forall (T:MY.TT) k (U V:MY.TT),
    M_yy.M.Twf V ->
    M_yy.M.Tbsubst T k V = M_yy.M.Tbsubst (M_yy.M.Tbsubst T k V) k U.
  Proof.
    introv Hwf.
    puts (M_yy.M.Twf_gTwf Hwf); clear Hwf.
    gunfold; f_equal; apply* bsubstitution_var_twice_wf.
  Qed.

  Lemma Tbfsubst_permutation_core_TTwfT : forall (T U V:MT.TT) (a:nat), 
    TTwfT U ->
    forall (k:nat),
      M_tt.M.Tbsubst (M_tt.M.Tfsubst T a U) k (M_tt.M.Tfsubst V a U)
      = M_tt.M.Tfsubst (M_tt.M.Tbsubst T k V) a U.
  Proof.
    inversion 1; auto using Tbfsubst_permutation_core.
  Qed.

  Lemma Tbfsubst_permutation_core_TTwf : forall (T U V:MT.TT) (a:nat), 
    TTwf U ->
    forall (k:nat),
      M_tt.M.Tbsubst (M_tt.M.Tfsubst T a U) k (M_tt.M.Tfsubst V a U)
      = M_tt.M.Tfsubst (M_tt.M.Tbsubst T k V) a U.
  Proof.
    inversion 1; auto using Tbfsubst_permutation_core_wf.
  Qed.

  Lemma THbfsubst_permutation_core : forall (T:MT.TT)(U V:MY.TT)(a:nat),
    M_yy.M.TwfT U ->
    forall (k:nat),
      M_yt.M.Tbsubst (M_yt.M.Tfsubst T a U) k (M_yy.M.Tfsubst V a U)
      = M_yt.M.Tfsubst (M_yt.M.Tbsubst T k V) a U.
  Proof.
    gunfold; f_equal; rewrite bfsubst_permutation_core; auto.
  Qed.

  Lemma THbfsubst_permutation_core_Ywf : forall (T:MT.TT)(U V:MY.TT)(a:nat),
    M_yy.M.Twf U ->
    forall (k:nat),
      M_yt.M.Tbsubst (M_yt.M.Tfsubst T a U) k (M_yy.M.Tfsubst V a U)
      = M_yt.M.Tfsubst (M_yt.M.Tbsubst T k V) a U.
  Proof.
    introv H.
    cut (M_yy.M.gTwf U); auto 2.
    gunfold; f_equal; rewrite bfsubst_permutation_core_wf; auto.
  Qed.

  Lemma Ybfsubst_permutation_core : forall (T U V:MY.TT)(a:nat),
    M_yy.M.TwfT U ->
    forall (k:nat),
      M_yy.M.Tbsubst (M_yy.M.Tfsubst T a U) k (M_yy.M.Tfsubst V a U)
      = M_yy.M.Tfsubst (M_yy.M.Tbsubst T k V) a U.
  Proof.
    gunfold; f_equal; rewrite bfsubst_permutation_core; auto.
  Qed.

  Lemma Ybfsubst_permutation_core_Ywf : forall (T U V:MY.TT)(a:nat),
    M_yy.M.Twf U ->
    forall (k:nat),
      M_yy.M.Tbsubst (M_yy.M.Tfsubst T a U) k (M_yy.M.Tfsubst V a U)
      = M_yy.M.Tfsubst (M_yy.M.Tbsubst T k V) a U.
  Proof.
    introv H.
    cut (M_yy.M.gTwf U); auto 2.
    gunfold; f_equal; rewrite bfsubst_permutation_core_wf; auto.
  Qed.

  Lemma THbfsubst_permutation_ind : forall (T:MT.TT)(U V:MY.TT) (a:nat), 
    M_yy.M.TwfT U ->
    a `notin` (M_yy.M.Tfv V) ->
    forall (k:nat),
      M_yt.M.Tbsubst (M_yt.M.Tfsubst T a U) k V = M_yt.M.Tfsubst (M_yt.M.Tbsubst T k V) a U.
  Proof.
    gunfold; rewrite bfsubst_permutation_ind; auto.
  Qed.

  Lemma THbfsubst_permutation_ind_Ywf : forall (T:MT.TT)(U V:MY.TT) (a:nat), 
    M_yy.M.Twf U ->
    a `notin` (M_yy.M.Tfv V) ->
    forall (k:nat),
      M_yt.M.Tbsubst (M_yt.M.Tfsubst T a U) k V = M_yt.M.Tfsubst (M_yt.M.Tbsubst T k V) a U.
  Proof.
    introv H.
    cut (M_yy.M.gTwf U); auto 2.
    gunfold; rewrite bfsubst_permutation_ind_wf; auto.
  Qed.

  Lemma Ybfsubst_permutation_ind : forall (T U V:MY.TT) (a:nat),
    M_yy.M.TwfT U ->
    a `notin` (M_yy.M.Tfv V) ->
    forall (k:nat),
      M_yy.M.Tbsubst (M_yy.M.Tfsubst T a U) k V = M_yy.M.Tfsubst (M_yy.M.Tbsubst T k V) a U.
  Proof.
    gunfold; rewrite bfsubst_permutation_ind; auto.
  Qed.

  Lemma Ybfsubst_permutation_ind_Ywf : forall (T U V:MY.TT) (a:nat),
    M_yy.M.Twf U ->
    a `notin` (M_yy.M.Tfv V) ->
    forall (k:nat),
      M_yy.M.Tbsubst (M_yy.M.Tfsubst T a U) k V = M_yy.M.Tfsubst (M_yy.M.Tbsubst T k V) a U.
  Proof.
    introv H.
    cut (M_yy.M.gTwf U); auto 2.
    gunfold; rewrite bfsubst_permutation_ind_wf; auto.
  Qed.

  Lemma THbfsubst_permutation_wfT : forall (T:MT.TT)(U V:MY.TT)(a:nat),
    M_yy.M.TwfT U -> 
    a `notin` (M_yy.M.Tfv V) ->
    M_yt.M.Tbsubst (M_yt.M.Tfsubst T a U) 0 V = M_yt.M.Tfsubst (M_yt.M.Tbsubst T 0 V) a U.
  Proof.
    gunfold; f_equal; auto using bfsubst_permutation_wfT.
  Qed.

  Lemma THbfsubst_permutation_wf : forall (T:MT.TT)(U V:MY.TT)(a:nat),
    M_yy.M.Twf U -> 
    a `notin` (M_yy.M.Tfv V) ->
    M_yt.M.Tbsubst (M_yt.M.Tfsubst T a U) 0 V = M_yt.M.Tfsubst (M_yt.M.Tbsubst T 0 V) a U.
  Proof.
    introv H.
    cut (M_yy.M.gTwf U); auto 2.
    gunfold; f_equal; auto using bfsubst_permutation_wf.
  Qed.

  Lemma Ybfsubst_permutation_wfT : forall (T U V:MY.TT)(a:nat),
    M_yy.M.TwfT U -> 
    a `notin` (M_yy.M.Tfv V) ->
    M_yy.M.Tbsubst (M_yy.M.Tfsubst T a U) 0 V = M_yy.M.Tfsubst (M_yy.M.Tbsubst T 0 V) a U.
  Proof.
    gunfold; f_equal; auto using bfsubst_permutation_wfT.
  Qed.

  Lemma Ybfsubst_permutation_wf : forall (T U V:MY.TT)(a:nat),
    M_yy.M.Twf U -> 
    a `notin` (M_yy.M.Tfv V) ->
    M_yy.M.Tbsubst (M_yy.M.Tfsubst T a U) 0 V = M_yy.M.Tfsubst (M_yy.M.Tbsubst T 0 V) a U.
  Proof.
    introv H.
    cut (M_yy.M.gTwf U); auto 2.
    gunfold; f_equal; auto using bfsubst_permutation_wf.
  Qed.

  Lemma Tbfsubst_permutation_var_TTwfT : forall (T U:MT.TT) (a b:nat),
    a <> b ->
    TTwfT U -> 
    M_tt.M.Tbsubst (M_tt.M.Tfsubst T a U) 0 (MT.To (Var MT.RR (inl b))) =
    M_tt.M.Tfsubst (M_tt.M.Tbsubst T 0 (MT.To (Var MT.RR (inl b)))) a U.
  Proof.
    inversion 2; auto using Tbfsubst_permutation_var_wfT.
  Qed.

  Lemma Tbfsubst_permutation_var_TTwf : forall (T U:MT.TT) (a b:nat),
    a <> b ->
    TTwf U -> 
    M_tt.M.Tbsubst (M_tt.M.Tfsubst T a U) 0 (MT.To (Var MT.RR (inl b))) =
    M_tt.M.Tfsubst (M_tt.M.Tbsubst T 0 (MT.To (Var MT.RR (inl b)))) a U.
  Proof.
    introv H H0.
    cut (gTTwf U); auto 2.
    inversion 1; auto using Tbfsubst_permutation_var_wf.
  Qed.

  Lemma THbfsubst_permutation_var_wfT : forall (T:MT.TT)(U:MY.TT)(a b:nat),
    a <> b ->
    M_yy.M.TwfT U -> 
    M_yt.M.Tbsubst (M_yt.M.Tfsubst T a U) 0 (MY.To (Var MY.RR (inl b))) =
    M_yt.M.Tfsubst (M_yt.M.Tbsubst T 0 (MY.To (Var MY.RR (inl b)))) a U.
  Proof.
    gunfold; f_equal; auto using bfsubst_permutation_var_wfT.
  Qed.

  Lemma THbfsubst_permutation_var_wf : forall (T:MT.TT)(U:MY.TT)(a b:nat),
    a <> b ->
    M_yy.M.Twf U -> 
    M_yt.M.Tbsubst (M_yt.M.Tfsubst T a U) 0 (MY.To (Var MY.RR (inl b))) =
    M_yt.M.Tfsubst (M_yt.M.Tbsubst T 0 (MY.To (Var MY.RR (inl b)))) a U.
  Proof.
    introv H H0.
    cut (M_yy.M.gTwf U); auto 2.
    gunfold; f_equal; auto using bfsubst_permutation_var_wf.
  Qed.

  Lemma Ybfsubst_permutation_var_wfT : forall (T U:MY.TT)(a b:nat),
    a <> b ->
    M_yy.M.TwfT U -> 
    M_yy.M.Tbsubst (M_yy.M.Tfsubst T a U) 0 (MY.To (Var MY.RR (inl b))) =
    M_yy.M.Tfsubst (M_yy.M.Tbsubst T 0 (MY.To (Var MY.RR (inl b)))) a U.
  Proof.
    gunfold; f_equal; auto using bfsubst_permutation_var_wfT.
  Qed.

  Lemma Ybfsubst_permutation_var_wf : forall (T U:MY.TT)(a b:nat),
    a <> b ->
    M_yy.M.Twf U -> 
    M_yy.M.Tbsubst (M_yy.M.Tfsubst T a U) 0 (MY.To (Var MY.RR (inl b))) =
    M_yy.M.Tfsubst (M_yy.M.Tbsubst T 0 (MY.To (Var MY.RR (inl b)))) a U.
  Proof.
    introv H H0.
    cut (M_yy.M.gTwf U); auto 2.
    gunfold; f_equal; auto using bfsubst_permutation_var_wf.
  Qed.


  (**************************************************************)
  (** * Preservation of well-formedness *)
  (**************************************************************)

  (** Substitutions preserve well-formedness. *)

  (* wfT_Tfsubst_1 => THwfT_Tfsubst *)
  Lemma THwfT_Tfsubst : forall (T:MT.TT)(U:MT.TT)(a:nat),
    M_yt.M.TwfT T ->
    M_yt.M.TwfT U ->
    M_yt.M.TwfT (M_tt.M.Tfsubst T a U).
  Proof.
    gunfold; auto using wfT_fsubst.
  Qed.

  (* wf_Tfsubst_1 => THwf_Tfsubst *)
  Lemma THwf_Tfsubst : forall (T:MT.TT)(U:MT.TT)(a:nat),
    M_yt.M.Twf T ->
    M_yt.M.Twf U ->
    M_yt.M.Twf (M_tt.M.Tfsubst T a U).
  Proof.
    introv H H0.
    cut (M_yt.M.gTwf T); auto 2.
    cut (M_yt.M.gTwf U); auto 2; intros.
    cut (M_yt.M.gTwf (M_tt.M.Tfsubst T a U)); auto 2.
    gunfold; auto using wf_fsubst.
  Qed.

  Lemma TTwfT_Tfsubst : forall (T:MT.TT)(U:MT.TT)(a:nat),
    TTwfT T ->
    TTwfT U ->
    TTwfT (M_tt.M.Tfsubst T a U).
  Proof.
    introv HT HU; inversion HT; inversion HU;
      split; auto using TwfT_Tfsubst, THwfT_Tfsubst.
  Qed.  

  Lemma TTwf_Tfsubst : forall (T:MT.TT)(U:MT.TT)(a:nat),
    TTwf T ->
    TTwf U ->
    TTwf (M_tt.M.Tfsubst T a U).
  Proof.
    introv HT HU; inversion HT; inversion HU;
      split; auto using Twf_Tfsubst, THwf_Tfsubst.
  Qed.  

  (* wfT_THfsubst => THwfT_THfsubst *)
  Lemma THwfT_THfsubst : forall (T:MT.TT)(U:MY.TT)(a:nat),
    M_yt.M.TwfT T ->
    M_yy.M.TwfT U ->
    M_yt.M.TwfT (M_yt.M.Tfsubst T a U).
  Proof.
    gunfold; auto using wfT_fsubst.
  Qed.

  (* wf_THfsubst => THwf_THfsubst *)
  Lemma THwf_THfsubst : forall (T:MT.TT)(U:MY.TT)(a:nat),
    M_yt.M.Twf T ->
    M_yy.M.Twf U ->
    M_yt.M.Twf (M_yt.M.Tfsubst T a U).
  Proof.
    introv H H0.
    cut (M_yt.M.gTwf T); auto 2.
    cut (M_yy.M.gTwf U); auto 2; intros.
    cut (M_yt.M.gTwf (M_yt.M.Tfsubst T a U)); auto 2.
    gunfold; auto using wf_fsubst.
  Qed.

  (* wfT_THfsubst_1 => TwfT_THfsubst *)
  Lemma TwfT_THfsubst : forall (T:MT.TT)(U:MY.TT)(a:nat),
    M_tt.M.TwfT T ->
    M_ty.M.TwfT U ->
    M_tt.M.TwfT (M_yt.M.Tfsubst T a U).
  Proof.
    gunfold; auto using wfT_fsubst.
  Qed.

  (* wf_THfsubst_1 => Twf_THfsubst *)
  Lemma Twf_THfsubst : forall (T:MT.TT)(U:MY.TT)(a:nat),
    M_tt.M.Twf T ->
    M_ty.M.Twf U ->
    M_tt.M.Twf (M_yt.M.Tfsubst T a U).
  Proof.
    introv H H0.
    cut (M_tt.M.gTwf T); auto 2.
    cut (M_ty.M.gTwf U); auto 2; intros.
    cut (M_tt.M.gTwf (M_yt.M.Tfsubst T a U)); auto 2.
    gunfold; auto using wf_fsubst.
  Qed.

  Lemma TTwfT_THfsubst : forall (T:MT.TT)(U:MY.TT)(a:nat),
    TTwfT T ->
    M_yy.M.TwfT U ->
    M_ty.M.TwfT U ->
    TTwfT (M_yt.M.Tfsubst T a U).
  Proof.
    inversion 1; split; auto using THwfT_THfsubst, TwfT_THfsubst.
  Qed.

  Lemma TTwf_THfsubst : forall (T:MT.TT)(U:MY.TT)(a:nat),
    TTwf T ->
    M_yy.M.Twf U ->
    M_ty.M.Twf U ->
    TTwf (M_yt.M.Tfsubst T a U).
  Proof.
    inversion 1; split; auto using THwf_THfsubst, Twf_THfsubst.
  Qed.

  (* wfT_Yfsubst => YwfT_Yfsubst *)
  Lemma YwfT_Yfsubst : forall (T U:MY.TT)(a:nat),
    M_yy.M.TwfT T ->
    M_yy.M.TwfT U ->
    M_yy.M.TwfT (M_yy.M.Tfsubst T a U).
  Proof.
    gunfold; auto using wfT_fsubst.
  Qed.

  (* wf_Yfsubst => Ywf_Yfsubst *)
  Lemma Ywf_Yfsubst : forall (T U:MY.TT)(a:nat),
    M_yy.M.Twf T ->
    M_yy.M.Twf U ->
    M_yy.M.Twf (M_yy.M.Tfsubst T a U).
  Proof.
    introv H H0.
    cut (M_yy.M.gTwf T); auto 2.
    cut (M_yy.M.gTwf U); auto 2; intros.
    cut (M_yy.M.gTwf (M_yy.M.Tfsubst T a U)); auto 2.
    gunfold; auto using wf_fsubst.
  Qed.


  (**************************************************************)
  (** * Heterogeneous substitution and well-formedness *)
  (**************************************************************)

  Lemma TwfT_THbsubst : forall (T: MT.TT) (k a : nat),
    MT.RR <> MY.RR -> 
    M_tt.M.TwfT (M_yt.M.Tbsubst T k (MY.To (Var _ (inl a)))) ->  M_tt.M.TwfT T.
  Proof.
    gunfold.
    apply wfT_bsubst_hetero with (r1:=MY.RR) (k:=k)(a:=a); auto.
  Qed.

  Lemma THwfT_Tbsubst : forall (T: MT.TT) (k a : nat),
    MT.RR <> MY.RR -> 
    M_yt.M.TwfT (M_tt.M.Tbsubst T k (MT.To (Var _ (inl a)))) ->  M_yt.M.TwfT T.
  Proof.
    gunfold.
    apply wfT_bsubst_hetero with (r1:=MT.RR) (k:=k)(a:=a); auto.
  Qed.

  Lemma TwfT_THbsubst_1 : forall (T: MT.TT) (k a : nat),
    MT.RR <> MY.RR -> 
    M_tt.M.TwfT T -> M_tt.M.TwfT (M_yt.M.Tbsubst T k (MY.To (Var _ (inl a)))).
  Proof.
    gunfold.
    apply wfT_bsubst_hetero_1 with (r1:=MY.RR) (k:=k)(a:=a); auto.
  Qed.

  Lemma THwfT_Tbsubst_1 : forall (T: MT.TT) (k a : nat),
    MT.RR <> MY.RR -> 
    M_yt.M.TwfT T -> M_yt.M.TwfT (M_tt.M.Tbsubst T k (MT.To (Var _ (inl a)))).
  Proof.
    gunfold.
    apply wfT_bsubst_hetero_1 with (r1:=MT.RR) (k:=k)(a:=a); auto.
  Qed.

  Lemma YTenvT_YwfT : forall (E F:env MY.TT)(T:MY.TT), 
    M_yy.YTenvT E F T ->
    M_yy.M.TwfT T.
  Proof.
    gunfold; eauto using envT_wfT.
  Qed.

  Hint Resolve TenvT_TwfT M_yt.THenvT_THwfT YenvT_YwfT.

  Lemma TTenvT_Tfv : forall (E F:env MY.TT) (T:MT.TT) (a:atom),
    a # E -> TTenvT E F T -> a `notin` M_tt.M.Tfv T.
  Proof.
    introv Hnotin Htt.
    inversion Htt; eauto using envT_Tfv.
  Qed.

  Lemma TTenvT_THfv : forall (E F:env MY.TT) (T:MT.TT) (a:atom),
    a # F -> TTenvT E F T -> a `notin` M_yt.M.Tfv T.
  Proof.
    introv Hnotin Htt.
    inversion Htt; eauto using M_yt.envT_THfv.
  Qed.

  Lemma TTenvT_fv : forall (E F:env MY.TT) (T:MT.TT) (a:atom),
    a # E -> a # F -> TTenvT E F T -> a `notin` M_tt.M.Tfv T /\ a `notin` M_yt.M.Tfv T.
  Proof.
    intros until 2; intro Htt.
    inversion Htt; eauto using TTenvT_Tfv, TTenvT_THfv.
  Qed.

  Lemma YTenvT_Yfv : forall (E F:env MY.TT) (T:MY.TT) (a:atom),
    a # E -> M_yy.YTenvT E F T -> a `notin` M_yy.M.Tfv T.
  Proof.
    intros; apply M_yy.envT_Yfv with E; auto.
  Qed.

  Lemma THenvT_dom_subset : forall (E:env MY.TT) (T:MT.TT),
    M_yt.THenvT E T -> M_yt.M.Tfv T [<=] dom E.
  Proof.
    gunfold; intros a H0; apply dom_map_2 with (f:=MY.From).
    generalize dependent a; apply envT_dom_subset; auto.
  Qed.

  Lemma YenvT_dom_subset : forall (E:env MY.TT) (T:MY.TT),
    M_yy.YenvT E T -> M_yy.M.Tfv T [<=] dom E.
  Proof.
    gunfold; intros a H0; apply dom_map_2 with (f:=MY.From).
    generalize dependent a; apply envT_dom_subset; auto.
  Qed.

  (** Parameter substitution for a fresh parameter
     - [Tfsubst_fresh]  is already included *)

  Lemma THfsubst_fresh : forall (E:env MY.TT)(T:MT.TT)(U:MY.TT)(a:nat),
    a # E -> M_yt.THenvT E T -> T = M_yt.M.Tfsubst T a U.
  Proof.
    gunfold; erewrite <- fsubst_fresh; eauto; auto. 
  Qed.

  Lemma Yfsubst_fresh : forall (E:env MY.TT)(T U:MY.TT)(a:nat),
    a # E -> M_yy.YenvT E T -> T = M_yy.M.Tfsubst T a U.
  Proof.
    gunfold; erewrite <- fsubst_fresh; eauto;  auto.
  Qed.
 
  (** Permutation of substitutions when [YenvT] holds
     - [Tbfsubst_permutation]  is already included

     - [Tbfsubst_permutation_var] already exists *)

  Lemma THbfsubst_permutation : forall (E:env MY.TT)(T:MT.TT)(U V:MY.TT)(a:nat),
    M_yy.YenvT E U -> 
    a `notin` (M_yy.M.Tfv V) ->
    M_yt.M.Tbsubst (M_yt.M.Tfsubst T a U) 0 V = M_yt.M.Tfsubst (M_yt.M.Tbsubst T 0 V) a U.
  Proof.
    gunfold; f_equal; eauto using bfsubst_permutation.
  Qed.

  Lemma THbfsubst_permutation_var : forall (E:env MY.TT)(T:MT.TT)(U:MY.TT)(a b:nat),
    a <> b ->
    M_yy.YenvT E U -> 
    M_yt.M.Tbsubst (M_yt.M.Tfsubst T a U) 0 (MY.To (Var MY.RR (inl b))) =
    M_yt.M.Tfsubst (M_yt.M.Tbsubst T 0 (MY.To (Var MY.RR (inl b)))) a U.
  Proof.
    gunfold; f_equal; eauto using bfsubst_permutation_var.
  Qed.

  Lemma Ybfsubst_permutation : forall (E:env MY.TT)(T U V:MY.TT)(a:nat),
    M_yy.YenvT E U -> 
    a `notin` (M_yy.M.Tfv V) ->
    M_yy.M.Tbsubst (M_yy.M.Tfsubst T a U) 0 V = M_yy.M.Tfsubst (M_yy.M.Tbsubst T 0 V) a U.
  Proof.
    gunfold; f_equal; eauto using bfsubst_permutation.
  Qed.

  Lemma Ybfsubst_permutation_var : forall (E:env MY.TT)(T U:MY.TT)(a b:nat),
    a <> b ->
    M_yy.YenvT E U -> 
    M_yy.M.Tbsubst (M_yy.M.Tfsubst T a U) 0 (MY.To (Var MY.RR (inl b))) =
    M_yy.M.Tfsubst (M_yy.M.Tbsubst T 0 (MY.To (Var MY.RR (inl b)))) a U.
  Proof.
    gunfold; f_equal; eauto using bfsubst_permutation_var.
  Qed.

  Lemma TTenvT_weaken : forall (E F G D:env MY.TT)(T:MT.TT),
    TTenvT (E ++ G) D T ->
    uniq (E ++ F ++ G) ->
    TTenvT (E ++ F ++ G) D T.
  Proof.
    gunfold; split; try apply envT_weaken; intuition solve_uniq.
  Qed.

  Lemma TTenvT_weaken_left : forall (E F D:env MY.TT)(T:MT.TT),
    TTenvT F D T ->
    uniq (E ++ F) ->
    TTenvT (E ++ F) D T.
  Proof.
    gunfold; split; try apply envT_weaken_left; intuition solve_uniq.
  Qed.

  Lemma TTenvT_weaken_right : forall (E F D:env MY.TT)(T:MT.TT),
    TTenvT E D T ->
    uniq (E ++ F) ->
    TTenvT (E ++ F) D T.
  Proof.
    gunfold; split; try apply envT_weaken_right; intuition solve_uniq.
  Qed.

  Lemma TTenvT_narrow : forall (E F D:env MY.TT)(U V:MY.TT)(T:MT.TT)(a:nat),
    TTenvT (E ++ a ~ V ++ F) D T ->
    uniq (E ++ a ~ U ++ F) -> 
    TTenvT (E ++ a ~ U ++ F) D T.
  Proof.
    introv H; inversion H; gunfold; split; try eapply envT_narrow; eauto.
  Qed.

  Lemma TTenvT_narrow_left : forall (F D:env MY.TT)(U V:MY.TT)(T:MT.TT)(a:nat),
    TTenvT (a ~ V ++ F) D T ->
    uniq (a ~ U ++ F) -> 
    TTenvT (a ~ U ++ F) D T.
  Proof.
    introv H; inversion H; gunfold; split;
      try eapply envT_narrow_left; eauto; solve_uniq.
  Qed.

  Lemma TTenvT_narrow_right : forall (E D:env MY.TT)(U V:MY.TT)(T:MT.TT)(a:nat),
    TTenvT (E ++ a ~ V) D T ->
    uniq (E ++ a ~ U) -> 
    TTenvT (E ++ a ~ U) D T.
  Proof.
    introv H; inversion H; gunfold; split;
      try eapply envT_narrow_right; eauto; solve_uniq.
  Qed.


  (********************************************************************)
  (** * Well-formed environments *)
  (********************************************************************)

  (** Well-formed environments and fresh variables *)

  Lemma YTwf_env_fv_1 : forall E F (x:atom),
    YTwf_env E F ->
    x # E ->
    x # F ->
    x `notin` M_yy.M.env_fv E.
  Proof.
    induction 1; simpl; intros; destruct_notin; auto.
    assert (x `notin` (M_yy.M.Tfv T)).
    apply (YTenvT_Yfv NotInTac0 H0); auto. 
    solve_notin.
  Qed.

  Lemma YTwf_env_fv_2 : forall E F (x:atom),
    YTwf_env E F ->
    x # E ->
    x # F ->
    x `notin` M_yy.M.env_fv F.
  Proof.
    induction 1; simpl; intros; destruct_notin; auto.
    assert (x `notin` (M_yy.M.Tfv T)).
    apply (YTenvT_Yfv H2 H0); auto.
    solve_notin.
  Qed.

  (** Well-formed environments and substitution for fresh variables *)
  
  Lemma YTwf_env_map_subst_id_1 : forall (E F:env MY.TT) (a:nat)(P:MY.TT),
    YTwf_env E F ->
    a # E ->
    E = map (fun U => M_yy.M.Tfsubst U a P) E.
  Proof.
    induction 1; simpl; intros; auto; destruct_notin.
    simpl_env; repeat f_equal.
    apply Yfsubst_fresh with E; auto.
    apply IHYTwf_env; auto.
  Qed.
    
  Lemma YTwf_env_map_subst_id_2 : forall (E F:env MY.TT) (a:nat)(P:MY.TT),
    YTwf_env E F ->
    a # E ->
    F = map (fun U => M_yy.M.Tfsubst U a P) F.
  Proof.
    induction 1; simpl; intros; auto; destruct_notin.
    apply IHYTwf_env; auto.
    simpl_env; repeat f_equal.
    apply Yfsubst_fresh with E; auto.
    apply IHYTwf_env; auto.
  Qed.
    
  Lemma YTwf_env_map_subst_id_3 : forall (E F:env MY.TT) (a:nat)(P:MY.TT),
    YTwf_env E F ->
    a # E ->
    E = map (fun U => M_yy.M.Tfsubst U a P) E /\ F = map (fun U => M_yy.M.Tfsubst U a P) F.
  Proof.
    split; eauto using YTwf_env_map_subst_id_1, YTwf_env_map_subst_id_2.
  Qed.

  (** If an environment is well-formed,
     then it does not contain duplicated keys. *)

  Lemma Ywf_env_from_YTwf_env: forall (E F:env MY.TT),
    YTwf_env E F -> M_yy.Ywf_env E.
  Proof.
    induction 1; gunfold; try constructor; auto.
  Qed.  


  Lemma Ywf_env_cons : forall E X T,
    M_yy.Ywf_env E ->
    M_yy.YenvT E T ->
    X # E ->
    M_yy.Ywf_env (X ~ T ++ E).
  Proof.
    gunfold; constructor; auto.
  Qed.

  Lemma uniq_from_YTwf_env_1 : forall (E F:env MY.TT),
    YTwf_env E F -> uniq E.
  Proof.
    induction 1; solve_uniq.
  Qed.

  Lemma uniq_from_YTwf_env_2 : forall (E F:env MY.TT),
    YTwf_env E F -> uniq F.
  Proof.
    induction 1; solve_uniq.
  Qed.

  (** Every type in a well-formed environment is well-formed. *)

  Lemma Ywf_env_binds : forall (E:env MY.TT)(a:nat)(T:MY.TT), 
    M_yy.Ywf_env E -> binds a T E -> M_yy.YenvT E T.
  Proof.
    gunfold; eauto using wf_env_binds.
  Qed.

  Lemma YTwf_env_binds_1 : forall (E F:env MY.TT)(a:nat)(T:MY.TT), 
    YTwf_env E F -> binds a T E -> M_yy.YTenvT E F T.
  Proof.
    intros; apply Ywf_env_binds with a; eauto using Ywf_env_from_YTwf_env.
  Qed.

  Lemma YTwf_env_binds_2 : forall (E F:env MY.TT)(a:nat)(T:MY.TT), 
    YTwf_env E F -> binds a T F -> M_yy.YTenvT E F T.
  Proof.
    induction 1; intros.
    inversion H.
    apply M_yy.YTenvT_weaken_left; auto.
    constructor; eauto using uniq_from_YTwf_env_1.
    analyze_binds H2.
  Qed.

  (** Extraction from a well-formed environment *)

  Lemma YenvT_from_Ywf_env : forall (E E0:env MY.TT)(a:nat)(T:MY.TT),
    M_yy.Ywf_env (E ++ a ~ T ++ E0) -> M_yy.YenvT E0 T.
  Proof.
    gunfold; eapply envT_from_wf_env with (a:=a); eauto.
  Qed.

  Lemma YenvT_from_Ywf_env_left : forall (E:env MY.TT)(a:nat)(T:MY.TT),
    M_yy.Ywf_env (a ~ T ++ E) -> M_yy.YenvT E T.
  Proof.
    gunfold;eapply envT_from_wf_env_left with (a:=a); eauto.
  Qed.

  Lemma YTenvT_from_YTwf_env_1 : forall (E E0 D:env MY.TT)(a:nat)(T:MY.TT),
    YTwf_env (E ++ a ~ T ++ E0) D -> M_yy.YTenvT E0 D T.
  Proof.
    intros.
    apply YenvT_from_Ywf_env with E a; eauto using Ywf_env_from_YTwf_env.
  Qed.

  Lemma YTenvT_from_YTwf_env_1_left : forall (E D:env MY.TT)(a:nat)(T:MY.TT),
    YTwf_env (a ~ T ++ E) D -> M_yy.YTenvT E D T.
  Proof.
    intros.
    apply YenvT_from_Ywf_env_left with a; eauto using Ywf_env_from_YTwf_env.
  Qed.

  Lemma YTenvT_from_YTwf_env_2 : forall (E D D0:env MY.TT)(a:nat)(T:MY.TT),
    YTwf_env E (D ++ a ~ T ++ D0) -> M_yy.YTenvT E D0 T.
  Proof.
    intros.
    apply YTwf_env_binds_2 with (a:=a)(F:=D ++ a ~ T ++ D0); auto.
  Qed.

  Lemma YTenvT_from_YTwf_env_2_left : forall (E D:env MY.TT)(a:nat)(T:MY.TT),
    YTwf_env E (a ~ T ++ D) -> M_yy.YTenvT E D T.
  Proof.
    intros.
    apply YTwf_env_binds_2 with (a:=a)(F:=a ~ T ++ D); auto.
  Qed.
    

  (** [uniq] depends only on the variables, not on types. *)

  Lemma Ywf_env_narrow : forall (E F: env MY.TT)(U V:MY.TT)(a:nat),
    M_yy.Ywf_env (E ++ a ~ U ++ F) ->
    M_yy.YenvT F V ->
    M_yy.Ywf_env (E ++ a ~ V ++ F).
  Proof.
    gunfold; eapply wf_env_narrow; eauto.
  Qed.

  Lemma Ywf_env_narrow_left : forall (F: env MY.TT)(U V:MY.TT)(a:nat),
    M_yy.Ywf_env (a ~ U ++ F) ->
    M_yy.YenvT F V ->
    M_yy.Ywf_env (a ~ V ++ F).
  Proof.
    gunfold; eapply wf_env_narrow_left; eauto.
  Qed.


  Lemma YTwf_env_narrow : forall (E F D: env MY.TT)(U V:MY.TT)(a:nat),
    YTwf_env (E ++ a ~ U ++ F) D ->
    M_yy.YTenvT F D V ->
    YTwf_env (E ++ a ~ V ++ F) D.
  Proof.
    intros E F D; generalize dependent E.
    induction D as [|(a1, U1)]; intros.
    (* D = nil *)
    induction E as [|(a0,U0)]; simpl in *; simpl_env in *; 
      inversion H; simpl_env in *; destruct_notin; subst.
    constructor 2; auto.

    constructor 2; auto.
    apply M_yy.YTenvT_narrow with U; auto.
    eauto using uniq_from_YTwf_env_1.
    auto using notin_app_3.
    
    (* D = a1 ~ U1 ++ D *)
    induction E as [|(a0, U0)]; simpl; intros; simpl_env in *;
      inversion H; auto; simpl_env in *; destruct_notin.
    
    constructor 3; auto.
    generalize (IHD nil U V a); simpl; intro IHD1; simpl_env in *;
      apply IHD1; auto.
    apply M_yy.YTenvT_narrow_left with U; auto.
    eauto using uniq_from_YTwf_env_1.

    constructor 2; auto.
    apply M_yy.YTenvT_narrow with U; auto.
    apply uniq_dom_only with U.
    apply uniq_from_YTwf_env_1 with (a1 ~ U1 ++ D); auto.
    auto using notin_app_3.

    constructor 3; auto.
    rewrite <- app_assoc.
    apply IHD with U; auto.
    rewrite <- app_assoc.
    apply M_yy.YTenvT_narrow with U; auto.
    apply uniq_dom_only with U.
    rewrite app_assoc.
    apply uniq_from_YTwf_env_1 with D; auto.
  Qed.

  Lemma YTwf_env_strengthening_left : forall (E F: env MY.TT)(U:MY.TT)(a:nat),
    YTwf_env E (a ~ U ++ F) ->
    YTwf_env E F.
  Proof.
    induction E as [|(a0, U0)]; intros.
    inversion H; auto.
    simpl_env in *.
    inversion H; auto; subst.
    constructor 2; auto.
    apply IHE with U a; auto.
  Qed.

  Lemma YTwf_env_strengthening : forall (E F G: env MY.TT)(U:MY.TT)(a:nat),
    YTwf_env E (F ++ a ~ U ++ G) ->
    YTwf_env E (F ++ G).
  Proof.
    induction E as [|(a0, U0)]; intros; simpl in *; simpl_env in *.
    (* E = nil *)
    induction F as [|(a1, U1)]; intros; simpl in *; simpl_env in *.
    (* F = nil *)
    apply YTwf_env_strengthening_left with U a; auto.
    (* F cons *)
    inversion H; auto; simpl_env in *; destruct_notin.
    constructor 3; auto.
    (* E cons *)
    induction F as [|(a1, U1)]; intros; simpl in *; simpl_env in *.
    (* F nil *)
    apply YTwf_env_strengthening_left with U a; auto.
    (* F cons *)
    inversion H; auto; simpl_env in *; destruct_notin; subst.
    constructor 3; auto.
    constructor 2; auto.
    apply IHE with U a; simpl_env in *.
    apply YTwf_env_strengthening_left with U1 a1; auto.
    apply YTenvT_from_YTwf_env_2_left with a1; auto.
    apply YTwf_sub; auto.
    forward~ (IHE (a1 ~ U1 ++ F) G U a) as K; auto.
    apply uniq_cons_2 with U1; simpl_alist; auto.
    generalize (uniq_from_YTwf_env_2 H3); intro.
    rewrite <- app_assoc. rewrite <- app_assoc in H0.
    apply uniq_remove_mid with (a ~ U); auto.
    constructor 3;auto.
  Qed.
    
  Lemma YTwf_env_strengthening_1 : forall (E F G: env MY.TT)(U:MY.TT)(a:nat),
    YTwf_env E (F ++ a ~ U ++ G) ->
    YTwf_env E G.
  Proof.
    induction F as [|(b,T)]; simpl; intros; simpl_env in *.
    apply YTwf_env_strengthening_left with U a; auto.
    generalize (@YTwf_env_strengthening_left E (F ++ [(a, U)] ++ G) T b H); intro.
    apply IHF with U a; auto.
  Qed.    


  Hint Rewrite M_ty.M.noRepr_Tfsubst  : isorew.
  Hint Rewrite M_ty.M.noRepr_Tbsubst  : isorew.
  
  (* TTwfT_THfsubst_1 => noRepr_TTwfT_THfsubst *)
  Lemma noRepr_TTwfT_THfsubst :
    noRepr MY.RR ->
    MT.RR <> MY.RR ->
    forall (T:MT.TT)(U:MY.TT)(a:nat),
      TTwfT T ->
      M_yy.M.TwfT U ->
      TTwfT (M_yt.M.Tfsubst T a U).
  Proof.
    intros; apply TTwfT_THfsubst; auto using M_ty.M.noRepr_TwfT.
  Qed.

  (* TTwf_THfsubst_1 => noRepr_TTwf_THfsubst *)
  Lemma noRepr_TTwf_THfsubst :
    noRepr MY.RR ->
    MT.RR <> MY.RR ->
    forall (T:MT.TT)(U:MY.TT)(a:nat),
      TTwf T ->
      M_yy.M.Twf U ->
      TTwf (M_yt.M.Tfsubst T a U).
  Proof.
    intros.
    apply TTwf_THfsubst; auto using M_ty.M.noRepr_Twf.
  Qed.


  Hint Resolve M_ty.M.noRepr_Tfv M_ty.M.noRepr_TwfT M_ty.M.noRepr_Twf M_ty.noRepr_YHenvT.

  Lemma noRepr_THbfsubst_permutation_var : 
    noRepr MY.RR ->
    MT.RR <> MY.RR ->
    forall (T:MT.TT)(U:MY.TT)(a b:nat)(k:nat),
      M_tt.M.Tbsubst (M_yt.M.Tfsubst T a U) k (MT.To (Var MT.RR (inl b)))
      = M_yt.M.Tfsubst (M_tt.M.Tbsubst T k (MT.To (Var MT.RR (inl b)))) a U.
  Proof.
    gunfold; func_equal.
    set (V := Var MT.RR (inl b)).
    assert (V = fsubst V a (MY.From U)) as Hid.
      unfold V; simpl.
      reflexivity.
      (* case_rep; intuition. *)
    pattern V at 1; rewrite Hid.
    rewrite bfsubst_permutation_core; auto using noRepr_wfT_hetero.    
  Qed.
  
  Lemma noRepr_THbfsubst_permutation_var_1 :
    noRepr MY.RR ->
    MT.RR <> MY.RR ->
    forall (T:MT.TT)(U:MT.TT)(a b:nat),
      M_yt.M.TwfT U ->
      forall (k:nat),
        M_yt.M.Tbsubst (M_tt.M.Tfsubst T a U) k (MY.To (Var MY.RR (inl b)))
        = M_tt.M.Tfsubst (M_yt.M.Tbsubst T k (MY.To (Var MY.RR (inl b)))) a U.
  Proof.
    gunfold; func_equal.
    set (V := Var MY.RR (inl b)).
    assert (V = fsubst V a (MT.From U)) as Hid.
      unfold V; simpl.
      reflexivity.
      (* case_rep; intuition congruence. *)
    pattern V at 1; rewrite Hid.
    rewrite bfsubst_permutation_core; auto using noRepr_wfT_hetero.    
  Qed.

  Lemma noRepr_THbfsubst_permutation_var_1_wf :
    noRepr MY.RR ->
    MT.RR <> MY.RR ->
    forall (T:MT.TT)(U:MT.TT)(a b:nat),
      M_yt.M.Twf U ->
      forall (k:nat),
        M_yt.M.Tbsubst (M_tt.M.Tfsubst T a U) k (MY.To (Var MY.RR (inl b)))
        = M_tt.M.Tfsubst (M_yt.M.Tbsubst T k (MY.To (Var MY.RR (inl b)))) a U.
  Proof.
    introv H H0. intros T U a b H1.
    cut (M_yt.M.gTwf U); auto 2.
    gunfold; func_equal.
    set (V := Var MY.RR (inl b)).
    assert (V = fsubst V a (MT.From U)) as Hid.
      unfold V; simpl.
      reflexivity.
      (* case_rep; intuition congruence. *)
    pattern V at 1; rewrite Hid.
    rewrite bfsubst_permutation_core_wf; auto using noRepr_wf_hetero.    
  Qed.


  Lemma noRepr_YenvT_Yfsubst :
    noRepr MY.RR ->
    forall (E F:env MY.TT) (T P Q:MY.TT)(a:nat),
      M_yy.YenvT (E ++ a ~ P ++ F) T ->
      M_yy.YenvT F Q ->
      uniq (map (fun U => M_yy.M.Tfsubst U a Q) E ++ F) ->
      M_yy.YenvT (map (fun U => M_yy.M.Tfsubst U a Q) E ++ F) (M_yy.M.Tfsubst T a Q).
  Proof.
    gunfold; rewrite M_yy.M.iso_env_map.
    destruct_uniq.
    apply noRepr_envT_fsubst with (P:=MY.From P); auto.
    rewrite <- M_yy.M.iso_env_map; rewrite <- map_app; solve_uniq.
  Qed.

  Lemma noRepr_YTenvT_Yfsubst :
    noRepr MY.RR ->
    forall (E F D:env MY.TT) (T P Q:MY.TT)(a:nat),
      M_yy.YTenvT (E ++ a ~ P ++ F) D T ->
      M_yy.YTenvT F D Q ->
      uniq (map (fun U => M_yy.M.Tfsubst U a Q) E ++ F) ->
      M_yy.YTenvT (map (fun U => M_yy.M.Tfsubst U a Q) E ++ F) D (M_yy.M.Tfsubst T a Q).
  Proof.
    intros; eauto using noRepr_YenvT_Yfsubst.
    apply noRepr_YenvT_Yfsubst with (P:=P); auto.
  Qed.

  Lemma noRepr_YTenvT_Yfsubst_left :
    noRepr MY.RR ->
    forall (F D:env MY.TT) (T P Q:MY.TT)(a:nat),
      M_yy.YTenvT (a ~ P ++ F) D T ->
      M_yy.YTenvT F D Q ->
      uniq F ->
      M_yy.YTenvT F D (M_yy.M.Tfsubst T a Q).
  Proof.
    intro HnoRepr; intros;
      generalize (@noRepr_YTenvT_Yfsubst HnoRepr nil F D T P Q a);
        simpl; intro; simpl_alist in *; tauto.
  Qed.

  Lemma noRepr_Ywf_env_Yfsubst : 
    noRepr MY.RR ->
    forall (E F:env MY.TT) (P Q:MY.TT)(a:nat),
      M_yy.Ywf_env (E ++ a ~ P ++ F) ->
      M_yy.YenvT F Q ->
      M_yy.Ywf_env (map (fun U => M_yy.M.Tfsubst U a Q) E ++ F).
  Proof.
    gunfold; rewrite M_yy.M.iso_env_map.    
    apply noRepr_wf_env_fsubst with (MY.From P); auto.
  Qed.

  Lemma noRepr_YTwf_env_Yfsubst : 
    noRepr MY.RR ->
    forall (E F D:env MY.TT) (P Q:MY.TT)(a:nat),
      YTwf_env (E ++ a ~ P ++ F) D ->
      M_yy.YTenvT F D Q ->
      YTwf_env (map (fun U => M_yy.M.Tfsubst U a Q) E ++ F) (map (fun U => M_yy.M.Tfsubst U a Q) D).
  Proof.
    intros Hno E F D; generalize dependent E.
    induction D as [|(b,V)]; simpl; intros; simpl_env in *.
    (* D : nil *)
    induction E as [|(a0, U0)]; intros; simpl in *; simpl_env in *;
      inversion H; auto; subst; simpl_env in *; destruct_notin.
    (* E : cons *)
    constructor 2; auto.
    apply noRepr_YTenvT_Yfsubst with P; auto.
    apply uniq_map_app_1.
    apply uniq_remove_mid with (a ~ P); eauto using uniq_from_YTwf_env_1.
    (* D : cons *)
    induction E as [|(a0, U0)]; intros; simpl in *; simpl_env in *.
    (* E : nil *)
    generalize (IHD nil P Q a); intro IHD1; simpl_env in *.
    constructor 3; auto.
    apply IHD1; auto.
    apply YTwf_env_strengthening_left with V b; auto.
    apply noRepr_YTenvT_Yfsubst_left with P; auto.
    apply M_yy.YTenvT_typ_var_indep with D; auto.
    apply YTenvT_from_YTwf_env_2_left with b; auto.
    generalize (uniq_from_YTwf_env_1 H); intros; solve_uniq.
    generalize (uniq_from_YTwf_env_2 H); intros; solve_uniq.
    (* E : cons *)
    set (f:= fun U : MY.TT => M_yy.M.Tfsubst U a Q).
    inversion H; auto; subst; simpl_env in *; destruct_notin.
    constructor 2; auto.
    replace (M_yy.M.Tfsubst V a Q) with (f V); auto.
    rewrite <- map_cons.
    replace ((b,V) :: D) with (b ~ V ++ D); auto.
    apply noRepr_YTenvT_Yfsubst with P; auto.
    apply uniq_map_app_1.
    generalize (uniq_from_YTwf_env_1 H4); intros; solve_uniq.
    replace (M_yy.M.Tfsubst U0 a Q) with (f U0); auto.
    rewrite <- app_assoc.
    rewrite <- map_cons.
    constructor 3;auto.
    replace ((a0,U0) :: E) with (a0 ~ U0 ++ E); auto.
    apply IHD with P; auto.
    apply noRepr_YTenvT_Yfsubst with P; auto.
    apply uniq_map_app_1; simpl_alist; rewrite <- app_assoc.
    generalize (uniq_from_YTwf_env_1 H5); intro Huniq1;
      rewrite <- app_assoc in Huniq1.
    apply uniq_remove_mid with (a ~ P); auto.
  Qed.

  Lemma noRepr_YTwf_env_Yfsubst_left : 
    noRepr MY.RR ->
    forall (F D:env MY.TT) (P Q:MY.TT)(a:nat),
      YTwf_env (a ~ P ++ F) D ->
      M_yy.YTenvT F D Q ->
      YTwf_env F (map (fun U => M_yy.M.Tfsubst U a Q) D).
  Proof.
    intros.
    generalize (noRepr_YTwf_env_Yfsubst H nil); simpl; intros.
    apply H2 with P; simpl_alist; auto.
  Qed.

  (* HTL part end *)



  (********************************************************************)
  (** * Tactics II *)
  (********************************************************************)

  (** The following tactics can be used in concrete formalizations.
     They help the end user of the DGP libraries in the way that
     the end user don't need to look into the generic library.
     - [auto_rewrite] rewrites all the basic equalities
       from the [isorew] autorewrite library.

     - [gsimpl] makes [Tfsubst], [Tbsubst], [Tsize], etc. in
       each patters behaves as if they are resursively defined
       in the object languages.

     - [gsimpl in H] simplifies the assumptions as expectied.

     - [gconstructor] helps to use [TwfT], [THwfT], [YwfT], [YTenvT], [YenvT]
       behaves inductively as expected.

     - [gconstructor] is useful e.g. when proving the equivalence
       of the generic and concrete version of well-formedness.

     - [wf_inv]: inversion tactics for [TwfT], [THwfT], [YwfT], [YTenvT], [YenvT].

     - The other tactics are auxiliary.

     - [dependent destruction] needs to be redefined
       because of some bugs. *)

  (** Customization of [gather_atoms] which originally defined
     in [MetatheoryAtom.v]
     - [gather_atoms] collects all parameter which have occurrs
       during proof.  *)

  Ltac gather_atoms :=
    let A := gather_atoms_with (fun x : atoms => x) in
    let B := gather_atoms_with (fun x : atom => {{ x }}) in
    let C := gather_atoms_with (fun x : MT.TT => M_yt.M.Tfv x) in
    let D := gather_atoms_with (fun x : MT.TT => M_tt.M.Tfv x) in
    let E := gather_atoms_with (fun x : MY.TT => M_yy.M.Tfv x) in
    let F := gather_atoms_with (fun A : Type => fun x : env A => dom x) in
      constr:(A `union` B `union` C `union` D `union` E `union` F).

  Tactic Notation "pick" "fresh" ident(Y) :=
    let L := gather_atoms in
      pick fresh Y for L.

  Ltac pick_fresh y :=
    pick fresh y.

  (** [auto_rewrite]  *)

  Ltac auto_rewrite :=
    try case_var; intros;
      autorewrite with isorew in *;
        simpl in *; auto 1.

  (** [gsimpl]
     - Unfolding [bsubst] first is better for computation  *)

  Ltac gsimpl_bsubst :=
    unfold M_tt.M.Tbsubst; 
    unfold M_yt.M.Tbsubst;
    unfold M_yy.M.Tbsubst; 
    unfold M_ty.M.Tbsubst;
    simpl bsubst.

  Ltac gsimpl_fsubst :=
    unfold M_tt.M.Tfsubst; 
    unfold M_yt.M.Tfsubst;
    unfold M_yy.M.Tfsubst; 
    unfold M_ty.M.Tfsubst;
    simpl fsubst.

  Ltac from_freevars :=
    match goal with
      | _ : context [ freevars MT.RR (MT.From ?T) ] |- _ =>
        replace (freevars MT.RR (MT.From T)) with
          (M_tt.M.Tfv T) in *; [idtac | auto]
      | |- context [ freevars MT.RR (MT.From ?T) ] =>
        replace (freevars MT.RR (MT.From T)) with
          (M_tt.M.Tfv T) in *; [idtac | auto]
      | _ : context [ freevars MY.RR (MT.From ?T) ] |- _ =>
        replace (freevars MY.RR (MT.From T)) with
          (M_yt.M.Tfv T) in *; [idtac | auto]
      | |- context [ freevars MY.RR (MT.From ?T) ] =>
        replace (freevars MY.RR (MT.From T)) with
          (M_yt.M.Tfv T) in *; [idtac | auto]
      | _ : context [ freevars MY.RR (MY.From ?T) ] |- _ =>
        replace (freevars MY.RR (MY.From T)) with
          (M_yy.M.Tfv T) in *; [idtac | auto]
      | |- context [ freevars MY.RR (MY.From ?T) ] =>
        replace (freevars MY.RR (MY.From T)) with
          (M_yy.M.Tfv T) in *; [idtac | auto]
      | _ : context [ freevars MT.RR (MY.From ?T) ] |- _ =>
        replace (freevars MT.RR (MY.From T)) with
          (M_ty.M.Tfv T) in *; [idtac | auto]
      | |- context [ freevars MT.RR (MY.From ?T) ] =>
        replace (freevars MT.RR (MY.From T)) with
          (M_ty.M.Tfv T) in *; [idtac | auto]
    end.

  Ltac gsimpl_fv :=
    unfold M_tt.M.Tfv; simpl;
    unfold M_yt.M.Tfv; simpl;
    unfold M_yy.M.Tfv; simpl;
    unfold M_ty.M.Tfv; simpl;
    repeat from_freevars;
    destruct_notin;
    try solve_notin.

  Ltac gsimpl_size :=
    unfold M_tt.M.TSize;
    unfold M_yy.M.TSize;
    simpl.
  
  Ltac from_subst :=
    match goal with
      | _ : context [MT.To (fsubst (MT.From ?T) ?k (MT.From ?U))] |- _ =>
        replace (MT.To (fsubst (MT.From T) k (MT.From U))) with
          (M_tt.M.Tfsubst T k U) in * |-; [idtac | unfold M_tt.M.Tfsubst; reflexivity]
      | _ : context [MT.To (bsubst (MT.From ?T) ?k (MY.From ?U))] |- _ =>
        replace (MT.To (fsubst (MT.From T) k (MY.From U))) with
          (M_yt.M.Tfsubst T k U) in * |-; [idtac | unfold M_yt.M.Tfsubst; reflexivity]
      | _ : context [MY.To (fsubst (MY.From ?T) ?k (MY.From ?U))] |- _ =>
        replace (MY.To (fsubst (MY.From T) k (MY.From U))) with
          (M_yy.M.Tfsubst T k U) in * |-; [idtac | unfold M_yy.M.Tfsubst; reflexivity]
      | _ : context [MY.To (fsubst (MY.From ?T) ?k (MT.From ?U))] |- _ =>
        replace (MY.To (fsubst (MY.From T) k (MT.From U))) with
          (M_ty.M.Tfsubst T k U) in * |-; [idtac | unfold M_ty.M.Tfsubst; reflexivity]
      | _ : context [MT.To (bsubst (MT.From ?T) ?k (MT.From ?U))] |- _ =>
        replace (MT.To (bsubst (MT.From T) k (MT.From U))) with
          (M_tt.M.Tbsubst T k U) in * |-; [idtac | unfold M_tt.M.Tbsubst; reflexivity]
      | _ : context [MT.To (bsubst (MT.From ?T) ?k (MY.From ?U))] |- _ =>
        replace (MT.To (bsubst (MT.From T) k (MY.From U))) with
          (M_yt.M.Tbsubst T k U) in * |-; [idtac | unfold M_yt.M.Tbsubst; reflexivity]
      | _ : context [MY.To (bsubst (MY.From ?T) ?k (MY.From ?U))] |- _ =>
        replace (MY.To (bsubst (MY.From T) k (MY.From U))) with
          (M_yy.M.Tbsubst T k U) in * |-; [idtac | unfold M_yy.M.Tbsubst; reflexivity]
      | _ : context [MY.To (bsubst (MY.From ?T) ?k (MT.From ?U))] |- _ =>
        replace (MY.To (bsubst (MY.From T) k (MT.From U))) with
          (M_ty.M.Tbsubst T k U) in * |-; [idtac | unfold M_ty.M.Tbsubst; reflexivity]
      | _ : context [MY.To (bsubst (MY.From ?T) ?k (Var MY.RR (inl ?l)))] |- _ =>
        replace (MY.To (bsubst (MY.From T) k (Var MY.RR (inl l)))) with
          (M_yy.M.Tbsubst T k (MY.To (Var MY.RR (inl l)))) in * |-;
            [idtac; simpl in *
              | unfold M_yy.M.Tbsubst; autorewrite with isorew; simpl; reflexivity]
    end.

  Ltac from_size :=
    match goal with
      | _ : context [ size (MT.From ?T) ] |- _ =>
        replace (size (MT.From T)) with
          (M_tt.M.TSize T) in *; [idtac | unfold M_tt.M.TSize in *; reflexivity]
      | _ : context [ size (MY.From ?T) ] |- _ =>
        replace (size (MY.From T)) with
          (M_yy.M.TSize T) in *; [idtac | unfold M_yy.M.TSize in *; reflexivity]
    end.

  Ltac gsimpl := repeat (
    gsimpl_bsubst;
    gsimpl_fsubst;
    auto_rewrite;
    try gsimpl_fv;
    simpl_alist in *;
    try gsimpl_size;
    repeat from_subst;
    repeat from_freevars;
    destruct_notin; try solve_notin;
    repeat from_size;
    auto_rewrite);
    simpl_alist in *.

  (** [gsimpl in]  *)

  Tactic Notation "gsimpl_bsubst" "in" constr(H) :=
    unfold M_tt.M.Tbsubst in H;
    unfold M_yt.M.Tbsubst in H;
    unfold M_yy.M.Tbsubst in H;
    unfold M_ty.M.Tbsubst in H;
    simpl bsubst in H.

  Tactic Notation "gsimpl_fsubst" "in" constr(H) :=
    unfold M_tt.M.Tfsubst in H;
    unfold M_yt.M.Tfsubst in H;
    unfold M_yy.M.Tfsubst in H;
    unfold M_ty.M.Tfsubst in H;
    simpl fsubst in H.

  Tactic Notation "gsimpl_fv" "in" constr(H) :=
    unfold M_tt.M.Tfv in H;
    unfold M_yt.M.Tfv in H;
    unfold M_yy.M.Tfv in H;
    unfold M_ty.M.Tfv in H;
    simpl freevars in H.

  Tactic Notation "gsimpl_size" "in" constr(H) :=
    unfold M_tt.M.TSize in H;
    unfold M_yy.M.TSize in H;
    simpl size in H.

  Tactic Notation "gsimpl" "in" constr(H) := repeat (
    gsimpl_bsubst in H;
    gsimpl_fsubst in H;
    auto_rewrite;
    try gsimpl_fv in H;
    simpl_alist in *;
    try gsimpl_size in H;
    repeat from_subst;
    repeat from_freevars;
    destruct_notin; try solve_notin;
    from_size).

  (** [gconstructor] *)

  Ltac apply_wfT :=
    match goal with
      | |- wfTRep _ (Unit) => apply wf_Unit
      | |- wfTRep _ (Const _ _) => apply wf_Const
      | |- wfTRep _ (Repr _ _) => apply wf_Repr
      | |- wfTRep _ (InL _ _) => apply wf_InL
      | |- wfTRep _ (InR _ _) => apply wf_InR
      | |- wfTRep _ (Pair _ _) => apply wf_Pair
      | |- wfTRep MT.RR (Bind REC _ (Rec (MT.From _))) =>
        let L := fresh "L" in
          let L := gather_atoms in
            apply wf_Bind_REC_homo with L; auto; simpl; intros; destruct_notin
      | |- wfTRep MY.RR (Bind REC _ (Rec (MT.From _))) =>
        apply wf_Bind_REC_hetero; auto
      | |- wfTRep MY.RR (Bind REC _ (Rec (MY.From _))) =>
        let L := fresh "L" in
          let L := gather_atoms in
            apply wf_Bind_REC_homo with L; auto; simpl; intros; destruct_notin
      | |- wfTRep MT.RR (Bind REC _ (Rec (MY.From _))) =>
        apply wf_Bind_REC_hetero; auto

      | |- wfTRep MT.RR (Bind MY.RR _ (Rec (MT.From _))) =>
        apply wf_Bind_hetero; auto
      | |- wfTRep MY.RR (Bind MY.RR _ (Rec (MT.From _))) =>
        let L := fresh "L" in
          let L := gather_atoms in
            apply wf_Bind_homo with L; auto; simpl; intros; destruct_notin
      | |- wfTRep MT.RR (Bind MY.RR _ (Rec (MY.From _))) =>
        apply wf_Bind_hetero; auto
      | |- wfTRep MY.RR (Bind MY.RR _ (Rec (MY.From _))) =>
        let L := fresh "L" in
          let L := gather_atoms in
            apply wf_Bind_homo with L; auto; simpl; intros; destruct_notin
      | |- wfTRep _ (Rec _) => apply wf_Rec
      | |- wfT MT.RR (Var MT.RR (inl _)) => apply wf_fvar
      | |- wfT MY.RR (Var MT.RR _) => apply wf_Var
      | |- wfT MY.RR (Var MY.RR (inl _)) => apply wf_fvar
      | |- wfT _ (Term _) => apply wf_Term
    end.

  Ltac from_wfT :=
    match goal with
      | |- wfT MT.RR (MT.From ?T) =>
        change (wfT MT.RR (MT.From T)) with (M_tt.M.TwfT T)
      | |- wfT MY.RR (MT.From ?T) =>
        change (wfT MY.RR (MT.From T)) with (M_yt.M.TwfT T)
      | |- wfT MY.RR (MY.From ?T) =>
        change (wfT MY.RR (MY.From T)) with (M_yy.M.TwfT T)
      | |- wfT MT.RR (MY.From ?T) =>
        change (wfT MT.RR (MY.From T)) with (M_ty.M.TwfT T)
      | |- wf MT.RR (MT.From ?T) =>
        change (wf MT.RR (MT.From T)) with (M_tt.M.Twf T)
      | |- wf MY.RR (MY.From ?T) =>
        change (wf MY.RR (MY.From T)) with (M_yy.M.Twf T)

      | H : wfT MT.RR (MT.From ?T) |- _ =>
        change (wfT MT.RR (MT.From T)) with (M_tt.M.TwfT T) in H
      | H : wfT MY.RR (MT.From ?T) |- _ =>
        change (wfT MY.RR (MT.From T)) with (M_yt.M.TwfT T) in H
      | H : wfT MY.RR (MY.From ?T) |- _ =>
        change (wfT MY.RR (MY.From T)) with (M_yy.M.TwfT T) in H
      | H : wfT MT.RR (MY.From ?T) |- _ =>
        change (wfT MT.RR (MY.From T)) with (M_ty.M.TwfT T) in H
      | H : wf MT.RR (MT.From ?T) |- _ =>
        change (wf MT.RR (MT.From T)) with (M_tt.M.Twf T) in H
      | H : wf MY.RR (MY.From ?T) |- _ =>
        change (wf MY.RR (MY.From T)) with (M_yy.M.Twf T) in H
    end.

  Ltac apply_envT :=
    match goal with
      | |- envTRep _ _ (Unit)       => apply env_Unit
      | |- envTRep _ _ (Const _ _)  => apply env_Const
      | |- envTRep _ _ (Repr _ _)   => apply env_Repr
      | |- envTRep _ _ (InL _ _)    => apply env_InL
      | |- envTRep _ _ (InR _ _)    => apply env_InR
      | |- envTRep _ _ (Pair _ _)   => apply env_Pair
      | |- envTRep _ _ (Bind _ _ _) =>
        let L := fresh "L" in
          let L := gather_atoms in
            apply env_Bind_REC_homo with L; auto; simpl; intros; destruct_notin
      | |- envTRep _ _ (Rec _)      => apply env_Rec
      | |- envT _ (map MY.From ?E) (Var _ (inl ?v)) =>
        match goal with
          | H : binds v ?U E |- _ =>
            apply env_fvar with (MY.From U)
        end
      | |- envT _ _ (Term _)        => apply env_Term
    end.

  Ltac from_envT :=
    match goal with
      | |- envT MY.RR (map MY.From ?E) (MY.From ?T) =>
        change (envT MY.RR (map MY.From E) (MY.From T)) with
          (M_yy.YenvT E T)
      | H : envT MY.RR (map MY.From ?E) (MY.From ?T) |- _ =>
        change (envT MY.RR (map MY.From E) (MY.From T)) with
          (M_yy.YenvT E T) in H
    end.

  Ltac gsimpl_subst :=
    gsimpl_bsubst;
    gsimpl_fsubst;
    autorewrite with isorew in *;
    simpl;
    auto*.

  Tactic Notation "gconstructor" :=
    intros; 
    unfold M_tt.M.TwfT, M_yy.M.TwfT, M_yt.M.TwfT;
    unfold M_yy.YTenvT, M_yy.YenvT, M_yy.TenvT;
    simpl;
    repeat apply_wfT;
    repeat apply_envT;
    gsimpl_subst;
    repeat from_wfT;
    repeat from_envT.
  
  Tactic Notation "gconstructor" "*" := gconstructor; auto*.

  Tactic Notation "apply_wfT" "with" constr(L) :=
    match goal with
      | |- wfTRep _ (Unit) => apply wf_Unit
      | |- wfTRep _ (Const _ _) => apply wf_Const
      | |- wfTRep _ (Repr _ _) => apply wf_Repr
      | |- wfTRep _ (InL _ _) => apply wf_InL
      | |- wfTRep _ (InR _ _) => apply wf_InR
      | |- wfTRep _ (Pair _ _) => apply wf_Pair
      | |- wfTRep MT.RR (Bind REC _ (Rec (MT.From _))) =>
        apply wf_Bind_REC_homo with L; auto; simpl; intros; destruct_notin
      | |- wfTRep MY.RR (Bind REC _ (Rec (MT.From _))) =>
        apply wf_Bind_REC_hetero; auto
      | |- wfTRep MY.RR (Bind REC _ (Rec (MY.From _))) =>
        apply wf_Bind_REC_homo with L; auto; simpl; intros; destruct_notin
      | |- wfTRep MT.RR (Bind REC _ (Rec (MY.From _))) =>
        apply wf_Bind_REC_hetero; auto
      | |- wfTRep MT.RR (Bind MY.RR _ (Rec (MT.From _))) =>
        apply wf_Bind_hetero; auto
      | |- wfTRep MY.RR (Bind MY.RR _ (Rec (MT.From _))) =>
        apply wf_Bind_homo with L; auto; simpl; intros; destruct_notin
      | |- wfTRep MT.RR (Bind MY.RR _ (Rec (MY.From _))) =>
        apply wf_Bind_hetero; auto
      | |- wfTRep MY.RR (Bind MY.RR _ (Rec (MY.From _))) =>
        apply wf_Bind_homo with L; auto; simpl; intros; destruct_notin
      | |- wfTRep _ (Rec _) => apply wf_Rec
      | |- wfT MT.RR (Var MT.RR (inl _)) => apply wf_fvar
      | |- wfT MY.RR (Var MT.RR _) => apply wf_Var
      | |- wfT MY.RR (Var MY.RR (inl _)) => apply wf_fvar
      | |- wfT _ (Term _) => apply wf_Term
    end.

  Tactic Notation "apply_envT" "with" constr(L) :=
    match goal with
      | |- envTRep _ _ (Unit)       => apply env_Unit
      | |- envTRep _ _ (Const _ _)  => apply env_Const
      | |- envTRep _ _ (Repr _ _)   => apply env_Repr
      | |- envTRep _ _ (InL _ _)    => apply env_InL
      | |- envTRep _ _ (InR _ _)    => apply env_InR
      | |- envTRep _ _ (Pair _ _)   => apply env_Pair
      | |- envTRep _ _ (Bind _ _ _) =>
        apply env_Bind_REC_homo with L; auto; simpl; intros; destruct_notin
      | |- envTRep _ _ (Rec _)      => apply env_Rec
      | |- envT _ (map MY.From ?E) (Var _ (inl ?v)) =>
        match goal with
          | H : binds v ?U E |- _ =>
            apply env_fvar with (MY.From U)
        end
      | |- envT _ _ (Term _)        => apply env_Term
    end.

  Tactic Notation "gconstructor" "with" constr(L) :=
    intros; 
    unfold M_tt.M.TwfT, M_yy.M.TwfT, M_yt.M.TwfT;
    unfold M_yy.YTenvT, M_yy.YenvT, M_yy.TenvT;
    simpl;
    repeat (apply_wfT with L);
    repeat (apply_envT with L);
    gsimpl_subst;
    repeat from_wfT;
    repeat from_envT.

  Tactic Notation "apply_envT" "with" constr(L) constr(V) :=
    match goal with
      | |- envTRep _ _ (Unit)       => apply env_Unit
      | |- envTRep _ _ (Const _ _)  => apply env_Const
      | |- envTRep _ _ (Repr _ _)   => apply env_Repr
      | |- envTRep _ _ (InL _ _)    => apply env_InL
      | |- envTRep _ _ (InR _ _)    => apply env_InR
      | |- envTRep _ _ (Pair _ _)   => apply env_Pair
      | |- envTRep _ _ (Bind _ _ _) =>
        apply env_Bind_REC_homo with L V; [reflexivity | intros ]
      | |- envTRep _ _ (Rec _)      => apply env_Rec
      | |- envT _ (map MY.From ?E) (Var _ (inl ?v)) =>
        match goal with
          | H : binds v ?U E |- _ =>
            apply env_fvar with (MY.From U)
        end
      | |- envT _ _ (Term _)        => apply env_Term
    end.

  Tactic Notation "gconstructor" "with" constr(L) constr(V) :=
    intros; 
    unfold M_tt.M.TwfT, M_yy.M.TwfT, M_yt.M.TwfT;
    unfold M_yy.YTenvT, M_yy.YenvT, M_yy.TenvT;
    simpl;
    repeat (apply_wfT with L);
    repeat (
      apply_envT with L V);
    gsimpl_subst;
    try (match goal with
           | |- context [((?k, MY.From ?T) :: map MY.From ?E)]
             => let Heq := fresh "Heq" in
               assert
                 ((k, MY.From T) :: map MY.From E = map MY.From ((k, T) :: E))
                 as Heq;
                   [simpl* | unfold elt in *; rewrite Heq]
           | |- context [([(?k, MY.From ?T)] ++ map MY.From ?E)]
             => let Heq := fresh "Heq" in
               assert
                 ([(k, MY.From T)] ++ map MY.From E = map MY.From ([(k, T)] ++ E))
                 as Heq;
                   [simpl* | unfold elt in *; rewrite Heq]
         end; autorewrite with isorew) ;
    repeat apply_envT;
    repeat from_wfT;
    repeat from_envT;
    simpl;
    simpl_alist in *.

  (** [wf_inv] *)

  Ltac do_depelim' tac H :=
    (try intros until H);
    dep_elimify;
    generalize_eqs H;
    tac H;
    simplify_dep_elim;
    un_dep_elimify.

  Tactic Notation "dependent" "destruction" hyp(H) :=
    do_depelim' ltac:(fun hyp => do_case hyp) H.

  Ltac wfT_inv :=
    match goal with
      | [ H : wfTRep _ Unit |- _ ]         => dependent destruction H
      | [ H : wfTRep _ (Const _ _) |- _ ]  => dependent destruction H
      | [ H : wfTRep _ (Repr _ _) |- _ ]   => dependent destruction H
      | [ H : wfTRep _ (InL _ _) |- _ ]    => dependent destruction H
      | [ H : wfTRep _ (InR _ _) |- _ ]    => dependent destruction H
      | [ H : wfTRep _ (Pair _ _) |- _ ]   => dependent destruction H
      | [ H : wfTRep _ (Bind _ _ _) |- _ ] => dependent destruction H
      | [ H : wfTRep _ (Rec _) |- _ ]      => dependent destruction H
      | [ H : wfT _ (Var _ _) |- _ ]       => dependent destruction H
      | [ H : wfT _ (Term _) |- _ ]        => dependent destruction H
    end.

  Ltac envT_inv :=
    match goal with
      | [ H : envTRep _ _ Unit |- _ ]         => dependent destruction H
      | [ H : envTRep _ _ (Const _ _) |- _ ]  => dependent destruction H
      | [ H : envTRep _ _ (Repr _ _) |- _ ]   => dependent destruction H
      | [ H : envTRep _ _ (InL _ _) |- _ ]    => dependent destruction H
      | [ H : envTRep _ _ (InR _ _) |- _ ]    => dependent destruction H
      | [ H : envTRep _ _ (Pair _ _) |- _ ]   => dependent destruction H
      | [ H : envTRep _ _ (Bind _ _ _) |- _ ] => dependent destruction H
      | [ H : envTRep _ _ (Rec _) |- _ ]      => dependent destruction H
      | [ H : envT _ _ (Var _ _) |- _ ]       => dependent destruction H
      | [ H : envT _ _ (Term _) |- _ ]        => dependent destruction H
    end.

  Tactic Notation "wf_inv" "in" constr(H) :=
    intros;
    unfold M_tt.M.TwfT, M_yt.M.TwfT, M_yy.M.TwfT in H;
    unfold M_yy.YTenvT, M_yy.YenvT, M_yy.TenvT in H;
    simpl in H;
    repeat (
      try wfT_inv;
      try envT_inv;
      try congruence;
      try (
        match goal with
          | H : PLUS _ _ = _ |- _ => inversion H; subst; clear H
        end;
        match goal with
          | H : JMeq _ _ |- _ => dependent destruction H
        end);
      auto_rewrite;
      try from_wfT;
      try from_envT );
      try tauto.

  Tactic Notation "wf_inv" "*" "in" constr(H) := wf_inv in H; auto*.

(** Naming variations of TSize_Tbsubst *)

  Definition YSize_Ybsubst := M_yy.M.TSize_Tbsubst.
  Definition TSize_Tbsubst := M_tt.M.TSize_Tbsubst.
  Definition TSize_THbsubst := M_yt.M.TSize_Tbsubst.

  Definition Ybsubst_var_twice := M_yy.M.Tbsubst_var_twice.
  Definition Tbsubst_var_twice := M_tt.M.Tbsubst_var_twice.
  Definition THbsubst_var_twice := M_yt.M.Tbsubst_var_twice.


