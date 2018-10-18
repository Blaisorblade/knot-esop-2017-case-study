Set Implicit Arguments.

Require Import LNameless_Meta.
Require Import LNameless_Meta_Env.
Require Import LNameless_Isomorphism.
Require Import LNameless_STLC_Iso.
Require Export LN_Template.

(* Module Export M_tt := LNTemplate Iso_trm Iso_trm. *)

Module Export M_tt := FWellformed Iso_trm Iso_trm.
Module Export M_yt := PWellformed Iso_typ Iso_trm.

Module MT := Iso_trm.
Module MY := Iso_typ.


  (**************************************************************)
  (** * Tactics I *)
  (**************************************************************)

  (** A tactic unfolding everything *)

  Ltac gunfold :=
    unfold Twf, Twf_basic in *;
    unfold gTwf, gTwf_basic, wf_basic in *;
    unfold Tfsubst, Tbsubst, Tfv, TwfT, TenvT, TSize in *;
    intros;
    repeat rewrite MT.To_From in *;
    repeat rewrite MT.From_To in *;
    repeat rewrite MY.To_From in *;
    simpl in *; 
    simpl_env in *.


  (** Substitution Lemma *)

  Lemma Tfsubst_Lemma : forall (T U V:MT.TT)(a b : nat),
    a <> b ->
    a `notin` (Tfv V) ->
    Tfsubst (Tfsubst T a U) b V =
    Tfsubst (Tfsubst T b V) a (Tfsubst U b V).
  Proof.
    gunfold; f_equal; auto using fsubstitution.
  Qed.


  (**************************************************************)
  (** * Permutation of substitutions *)
  (**************************************************************)

  (** Swapping of substitutions for (bound) variables. *)

  (* Tbsubst_homo_1 => Tbsubst_homo_wf *)
  Lemma Tbsubst_homo_wf : forall (T:MT.TT) k l (U V:MT.TT),
    k <> l ->
    Twf U ->
    Twf V ->
    Tbsubst (Tbsubst T k U) l V = Tbsubst (Tbsubst T l V) k U.
  Proof.
    introv Hneq Hu Hv.
    puts (Twf_gTwf Hu); clear Hu.
    puts (Twf_gTwf Hv); clear Hv.
    gunfold; f_equal; apply* bsubstitution_homo_wf.
  Qed.


  (* Tbsubst_var_twice_1 => Tbsubst_var_twice_wf *)
  Lemma Tbsubst_var_twice_wf : forall (T:MT.TT) k (U V:MT.TT),
    Twf V ->
    Tbsubst T k V = Tbsubst (Tbsubst T k V) k U.
  Proof.
    introv Hwf.
    puts (Twf_gTwf Hwf); clear Hwf.
    gunfold; f_equal; apply* bsubstitution_var_twice_wf.
  Qed.


  Lemma Tbfsubst_permutation_core : forall (T U V:MT.TT) (a:nat), 
    TwfT U ->
    forall (k:nat),
      Tbsubst (Tfsubst T a U) k (Tfsubst V a U)
      = Tfsubst (Tbsubst T k V) a U.
  Proof.
    gunfold; rewrite bfsubst_permutation_core; auto.
  Qed.

  Lemma Tbfsubst_permutation_core_wf : forall (T U V:MT.TT) (a:nat), 
    Twf U ->
    forall (k:nat),
      Tbsubst (Tfsubst T a U) k (Tfsubst V a U)
      = Tfsubst (Tbsubst T k V) a U.
  Proof.
    introv H.
    cut (gTwf U); auto 2.
    gunfold; rewrite bfsubst_permutation_core_wf; auto.
  Qed.

  Lemma Tbfsubst_permutation_ind : forall (T U V:MT.TT) (a:nat), 
    TwfT U ->
    a `notin` (Tfv V) ->
    forall (k:nat),
      Tbsubst (Tfsubst T a U) k V = Tfsubst (Tbsubst T k V) a U.
  Proof.
    gunfold; rewrite bfsubst_permutation_ind; auto.
  Qed.

  Lemma Tbfsubst_permutation_ind_wf : forall (T U V:MT.TT) (a:nat), 
    Twf U ->
    a `notin` (Tfv V) ->
    forall (k:nat),
      Tbsubst (Tfsubst T a U) k V = Tfsubst (Tbsubst T k V) a U.
  Proof.
    introv H.
    cut (gTwf U); auto 2.
    gunfold; rewrite bfsubst_permutation_ind_wf; auto.
  Qed.

  Lemma Tbfsubst_permutation_wfT : forall (T U V:MT.TT) (a:nat),
    TwfT U -> 
    a `notin` (Tfv V) ->
    Tbsubst (Tfsubst T a U) 0 V = Tfsubst (Tbsubst T 0 V) a U.
  Proof.
    gunfold; f_equal; auto using bfsubst_permutation_wfT.
  Qed.

  Lemma Tbfsubst_permutation_wf : forall (T U V:MT.TT) (a:nat),
    Twf U -> 
    a `notin` (Tfv V) ->
    Tbsubst (Tfsubst T a U) 0 V = Tfsubst (Tbsubst T 0 V) a U.
  Proof.
    introv H.
    cut (gTwf U); auto 2.
    gunfold; f_equal; auto using bfsubst_permutation_wf.
  Qed.

  Lemma Tbfsubst_permutation_var_wfT : forall (T U:MT.TT) (a b:nat),
    a <> b ->
    TwfT U -> 
    Tbsubst (Tfsubst T a U) 0 (MT.To (Var MT.RR (inl b))) =
    Tfsubst (Tbsubst T 0 (MT.To (Var MT.RR (inl b)))) a U.
  Proof.
    gunfold; f_equal; auto using bfsubst_permutation_var_wfT.
  Qed.

  Lemma Tbfsubst_permutation_var_wf : forall (T U:MT.TT) (a b:nat),
    a <> b ->
    Twf U -> 
    Tbsubst (Tfsubst T a U) 0 (MT.To (Var MT.RR (inl b))) =
    Tfsubst (Tbsubst T 0 (MT.To (Var MT.RR (inl b)))) a U.
  Proof.
    introv H H0.
    cut (gTwf U); auto 2.
    gunfold; f_equal; auto using bfsubst_permutation_var_wf.
  Qed.


  (**************************************************************)
  (** * Preservation of well-formedness *)
  (**************************************************************)

  (** Substitutions preserve well-formedness. *)

  (* wfT_Tfsubst => TwfT_Tfsubst *)
  Lemma TwfT_Tfsubst : forall (T U:MT.TT) (a:nat),
    TwfT T ->
    TwfT U ->
    TwfT (Tfsubst T a U).
  Proof.
    gunfold; auto using wfT_fsubst.
  Qed.

  (* wf_Tfsubst => Twf_Tfsubst *)
  Lemma Twf_Tfsubst : forall (T U:MT.TT) (a:nat),
    Twf T ->
    Twf U ->
    Twf (Tfsubst T a U).
  Proof.
    introv H H0.
    cut (gTwf T); auto 2.
    cut (gTwf U); auto 2; intros.
    cut (gTwf (Tfsubst T a U)); auto 2.
    gunfold; auto using wf_fsubst.
  Qed.


  (**************************************************************)
  (** * Well-formedness in an environment *)
  (**************************************************************)

  (** Well-formed terms/types in an environment are well-formed. *)

  Lemma TenvT_TwfT : forall (E:env MY.TT)(T:MT.TT), 
    TenvT E T ->
    TwfT T.
  Proof.
    gunfold; eauto using envT_wfT.
  Qed.

  Hint Resolve TenvT_TwfT.

  (* Tbsubst_on_env => TenvT_Twf *)
  Lemma TenvT_Twf : forall (E:env MY.TT)(T:MT.TT),
    TenvT E T -> forall (k:nat) (U:MT.TT), T = Tbsubst T k U.
  Proof.
    intros; eauto using TenvT_TwfT, M.TwfT_Twf.
  Qed.

  (** Environments capture all the parameters in terms/types *)
  Lemma envT_Tfv : forall (E:env MY.TT) (T:MT.TT) (a:atom),
    a # E -> TenvT E T -> a `notin` Tfv T.
  Proof.
    gunfold;
    apply envT_fv with (r':= MY.RR)(E:= map MY.From E); auto.
  Qed.

  Lemma TenvT_dom_subset : forall (E:env MY.TT) (T:MT.TT),
    TenvT E T -> Tfv T [<=] dom E.
  Proof.
    gunfold; intros a H0; apply dom_map_2 with (f:=MY.From).
    generalize dependent a; apply envT_dom_subset; auto.
  Qed.

  (** Parameter substitution for a fresh parameter *)

  Lemma Tfsubst_fresh : forall (E:env MY.TT)(T U:MT.TT)(a:nat),
    a # E -> TenvT E T -> T = Tfsubst T a U.
  Proof.
    gunfold; erewrite <- fsubst_fresh; eauto; auto.  
  Qed.

  (** Permutation of substitutions when [TenvT] holds *)
  
  Lemma Tbfsubst_permutation : forall (E:env MY.TT)(T U V:MT.TT)(a:nat),
    TenvT E U -> 
    a `notin` (Tfv V) ->
    Tbsubst (Tfsubst T a U) 0 V = Tfsubst (Tbsubst T 0 V) a U.
  Proof.
    gunfold; f_equal; eauto using bfsubst_permutation.
  Qed.

  Lemma Tbfsubst_permutation_var : forall (E:env MY.TT)(T U:MT.TT)(a b:nat),
    a <> b ->
    TenvT E U -> 
    Tbsubst (Tfsubst T a U) 0 (MT.To (Var MT.RR (inl b))) =
    Tfsubst (Tbsubst T 0 (MT.To (Var MT.RR (inl b)))) a U.
  Proof.
    gunfold; f_equal; eauto using bfsubst_permutation_var.
  Qed.


  (**************************************************************)
  (** * Tactics II *)
  (**************************************************************)

  (** The following tactics can be used in concrete formalizations.
     They help the end user of the DGP libraries in the way that
     the end user don't need to look into the generic library.
     - [auto_rewrite] rewrites all the basic equalities
       from the [isorew] autorewrite library.

     - [gsimpl] makes [Tfsubst], [Tbsubst], [Tsize], etc. in
       each patters behaves as if they are resursively defined
       in the object languages.

     - [gsimpl in H] simplifies the assumptions as expectied.

     - [gconstructor] is useful e.g. when proving the equivalence
       of the generic and concrete version of well-formedness.

     - The other tactics are auxiliary. *)

  (** [auto_rewrite]  *)

  Ltac auto_rewrite :=
    try case_var;
    intros;
    autorewrite with isorew in *;
    simpl in *;
    auto 1.

  (** [gsimpl] *)

  Ltac gsimpl_bsubst :=
    unfold Tbsubst; 
    simpl bsubst.

  Ltac gsimpl_fsubst :=
    unfold Tfsubst; 
    simpl fsubst.

  Ltac from_freevars :=
    match goal with
      | _ : context [ freevars MT.RR (MT.From ?T) ] |- _ =>
        replace (freevars MT.RR (MT.From T)) with
          (Tfv T) in *; [idtac | auto]
      | |- context [ freevars MT.RR (MT.From ?T) ] =>
        replace (freevars MT.RR (MT.From T)) with
          (Tfv T) in *; [idtac | auto]
    end.

  Ltac gsimpl_fv :=
    unfold Tfv in *; simpl in *;
      repeat from_freevars;
        destruct_notin; try solve_notin.
  
  Ltac gsimpl_size :=
    unfold TSize;
    simpl.

  Ltac from_subst :=
    match goal with
      | _ : context [MT.To (fsubst (MT.From ?T) ?k (MT.From ?U))] |- _ =>
        replace (MT.To (fsubst (MT.From T) k (MT.From U))) with
          (Tfsubst T k U) in * |-; [idtac | unfold Tfsubst; reflexivity]
      | _ : context [MT.To (bsubst (MT.From ?T) ?k (MT.From ?U))] |- _ =>
        replace (MT.To (bsubst (MT.From T) k (MT.From U))) with
          (Tbsubst T k U) in * |-; [idtac | unfold Tbsubst; reflexivity]
    end.

  Ltac from_size :=
    match goal with
      | _ : context [ size (MT.From ?T) ] |- _ =>
        replace (size (MT.From T)) with
          (TSize T) in *; [idtac | unfold TSize in *; reflexivity]
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
    unfold Tbsubst in H;
    simpl bsubst in H.

  Tactic Notation "gsimpl_fsubst" "in" constr(H) :=
    unfold Tfsubst in H;
    simpl fsubst in H.

  Tactic Notation "gsimpl_fv" "in" constr(H) :=
    unfold Tfv in H;
    simpl freevars in H.

  Tactic Notation "gsimpl_size" "in" constr(H) :=
    unfold TSize in H;
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
      | |- wfTRep _ (InL _ _) => apply wf_InL
      | |- wfTRep _ (InR _ _) => apply wf_InR
      | |- wfTRep _ (Pair _ _) => apply wf_Pair
      | |- wfTRep _ (Bind _ _ _) =>
        let L := fresh "L" in
          let L := gather_atoms in
            apply wf_Bind_REC_homo with L; auto; simpl; intros; destruct_notin
      | |- wfTRep _ (Rec _) => apply wf_Rec
      | |- wfT _ (Var _ _) => apply wf_fvar; auto
      | |- wfT _ (Term _) => apply wf_Term
    end.

  Ltac gsimpl_subst :=
    unfold Tbsubst; simpl;
    unfold Tfsubst; simpl;
    try case_var; intros;
    autorewrite with isorew;
    simpl in *; auto*.

  Ltac from_wfT :=
    match goal with
      | |- wfT MT.RR (MT.From ?T) =>
        change (wfT MT.RR (MT.From T)) with (TwfT T); auto
      | |- wf MT.RR (MT.From ?T) =>
        change (wf MT.RR (MT.From T)) with (Twf T); auto
    end.

  Ltac gconstructor :=
    intros;
    unfold TwfT;
    simpl;
    repeat apply_wfT;
    gsimpl_subst;
    from_wfT. 

  (** [gconstructor with]   *)

  Tactic Notation "apply_wfT" "with" constr(L) :=
    match goal with
      | |- wfTRep _ (Unit) => apply wf_Unit
      | |- wfTRep _ (Const _ _) => apply wf_Const
      | |- wfTRep _ (InL _ _) => apply wf_InL
      | |- wfTRep _ (InR _ _) => apply wf_InR
      | |- wfTRep _ (Pair _ _) => apply wf_Pair
      | |- wfTRep _ (Bind _ _ _) =>
        apply wf_Bind_REC_homo with L; auto; simpl; intros; destruct_notin
      | |- wfTRep _ (Rec _) => apply wf_Rec
      | |- wfT _ (Var _ _) => apply wf_fvar; auto
      | |- wfT _ (Term _) => apply wf_Term
    end.

  Tactic Notation "gconstructor" "with" constr(L) :=
    intros;
    unfold TwfT;
    simpl;
    repeat (apply_wfT with L);
    gsimpl_subst; from_wfT. 


  (** Customization of [gather_atoms] which originally defined
     in [MetatheoryAtom.v]
     - [gather_atoms] collects all parameter which have occurrs
       during proof.  *)
  
  Ltac gather_atoms :=
    let A := gather_atoms_with (fun x : atoms => x) in
    let B := gather_atoms_with (fun x : atom => {{ x }}) in
    let C := gather_atoms_with (fun x : MT.TT => Tfv x) in
    let D := gather_atoms_with (fun A : Type => fun x : env A => dom x) in
      constr:(A `union` B `union` C `union` D).

  Tactic Notation "pick" "fresh" ident(Y) :=
    let L := gather_atoms in
      pick fresh Y for L.

  Ltac pick_fresh y :=
    pick fresh y.
