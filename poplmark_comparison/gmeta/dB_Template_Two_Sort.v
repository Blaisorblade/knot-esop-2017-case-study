Set Implicit Arguments.

Require Import Variable_Sets.
Require Import deBruijn_Isomorphism.
Require Import deBruijn_Fsub_Iso.
Require Export dB_Template.


Module Export M_tt := dBTemplate Iso_trm Iso_trm.
Module Export M_yy := dBTemplate Iso_typ Iso_typ.
Module Export M_yt := dBTemplate Iso_typ Iso_trm.
Module Export M_ty := dBTemplate Iso_trm Iso_typ.

Module MT := Iso_trm.
Module MY := Iso_typ.


Notation "[[[ e ]]]" := (M_yt.Tlth e).


  (**************************************************************)
  (** * A tactic unfolding everything *)
  (**************************************************************)

  Ltac gunfold :=
    unfold M_tt.Tshift, M_yt.Tshift, M_yy.Tshift, M_ty.Tshift,
           M_tt.Tsubst, M_yt.Tsubst, M_yy.Tsubst, M_ty.Tsubst in *;
    unfold M_yy.Ysize in *;
    intros;
    repeat rewrite MT.To_From in *; 
    repeat rewrite MT.From_To in *;
    repeat rewrite MY.From_To in *;
    repeat rewrite MY.From_To in *;
    simpl in *.



  (**************************************************************)
  (** * Generic lemmas about term shifting and substitution *)
  (**************************************************************)

  Lemma noRepr_Ysubst_Yshift : forall (n : nat) (T T' : MY.TT), 
    noRepr MY.RR ->
    T = M_yy.Tsubst (M_yy.Tshift n T) n T'.
  Proof.
    gunfold; rewrite* <- noRepr_subst_shift.
  Qed.

  Lemma noRepr_Yshift_Yshift : forall (n n' : nat) (T : MY.TT),
    noRepr MY.RR ->
    M_yy.Tshift n (M_yy.Tshift (n + n')%nat T) 
    = M_yy.Tshift (S (n + n')%nat) (M_yy.Tshift n T).
  Proof.
    gunfold; rewrite* noRepr_shift_shift.
  Qed.

  Lemma noRepr_Yshift_Ysubst_1 : forall (n n' : nat) (T T' : MY.TT),
    noRepr MY.RR ->
    M_yy.Tshift n (M_yy.Tsubst T (n + n')%nat T') =
    M_yy.Tsubst (M_yy.Tshift n T) (1 + n + n')%nat (M_yy.Tshift n T').
  Proof.
    gunfold; rewrite* noRepr_shift_subst_1.
  Qed.

  Lemma noRepr_Yshift_Ysubst_2 : forall (n n' : nat) (T T' : MY.TT),
    noRepr MY.RR ->
    (M_yy.Tshift (n + n')%nat (M_yy.Tsubst T n T')) =
    (M_yy.Tsubst (M_yy.Tshift (1 + n + n')%nat T) n (M_yy.Tshift (n + n')%nat T')).
  Proof.
    gunfold; rewrite* noRepr_shift_subst_2.
  Qed.

  Lemma noRepr_Ysubst_Ysubst : forall (n n' : nat) (T U V : MY.TT),
    noRepr MY.RR ->
    (M_yy.Tsubst (M_yy.Tsubst T n U) (n + n')%nat V) =
    (M_yy.Tsubst (M_yy.Tsubst T (1 + n + n')%nat 
      (M_yy.Tshift n V)) n (M_yy.Tsubst U (n + n')%nat V)).
  Proof.
    gunfold; rewrite* noRepr_subst_subst.
  Qed.

  Lemma noRepr_Yshift_preserves_Ysize : forall (T : MY.TT) (X : nat), 
    noRepr MY.RR ->
    M_yy.Ysize (M_yy.Tshift X T) = M_yy.Ysize T.
  Proof.
    gunfold; rewrite* noRepr_shift_preserves_size.
  Qed.


  Fixpoint Tget_left (e: M_yt.TEnv) (X:atom) {struct e} : option MY.TT :=
    match e with
      | nil   => None
      | (inr T) :: e' => Tget_left e' X
      | (inl T) :: e' =>
        opt_map (M_yy.Tshift 0)
        (match X with
           | O    => Some T
           | S X' => Tget_left e' X'
         end)
    end.

  Fixpoint Tget_right (e: M_yt.TEnv) (x:atom) {struct e} : option MY.TT :=
  match e with
    nil       => None
  | ((inl _)::e') => opt_map (M_yy.Tshift 0) (Tget_right e' x)
  | ((inr T)::e') =>
      match x with
      | O    => Some T
      | S x' => Tget_right e' x'
      end
  end.


  Lemma Tget_left_gTget_left : forall (e: M_yt.TEnv) (X:atom),
    Tget_left e X = M_yt.gTget_left e X.
  Proof.
    unfold M_yt.gTget_left.
    intro e.
    induction e; simpl; auto.
    destruct a; auto.
    destruct X; simpl; f_equal.
    rewrite (IHe X); simpl.
    destruct (get_left (M_yt.From_TEnv e) X); simpl; f_equal.
    unfold M_yy.Tshift. rewrite MY.From_To; auto.
  Qed.
    
  Lemma Tget_right_gTget_right : forall (e: M_yt.TEnv) (X:atom),
    Tget_right e X = M_yt.gTget_right e X.
  Proof.
    induction e; unfold M_yt.gTget_right; simpl; intros; auto.
    destruct a;
      [ rewrite IHe; unfold M_yt.gTget_right; simpl;
        destruct (get_right (M_yt.From_TEnv e) X); simpl; auto;
        unfold M_yy.Tshift; autorewrite with isorew; auto
      | destruct X; simpl;
        [ rewrite MY.To_From; auto
        | rewrite IHe; unfold M_yt.gTget_right; auto
        ]
      ].
  Qed.

  Lemma Tlth_preserving : forall (e e' : M_yt.TEnv),
    (forall (X : nat), Tget_left e' X = None -> Tget_left e X = None) ->
    [[[e]]] <= [[[e']]].
  Proof.
    intros.
    assert (forall X : nat, M_yt.gTget_left e' X = None -> M_yt.gTget_left e X = None).
    intros; rewrite <- Tget_left_gTget_left;
      apply H; rewrite Tget_left_gTget_left; auto.
    unfold M_yt.gTget_left, M_yt.Tlth in *; intros.    
    auto with opt.
  Qed.

  Hint Resolve Tlth_preserving.

  Lemma Twf_typ_env_weaken : forall (T : MY.TT) (e e' : M_yt.TEnv),
    (forall (X : nat), Tget_left e' X = None -> Tget_left e X = None) ->
    M_yt.Twf_typ e T -> M_yt.Twf_typ e' T.
  Proof.
    intros.
    assert (forall X : nat, M_yt.gTget_left e' X = None -> M_yt.gTget_left e X = None).
    intros; rewrite <- Tget_left_gTget_left;
      apply H; rewrite Tget_left_gTget_left; auto.
    unfold M_yt.Twf_typ, M_yt.gTget_left in *.
    eauto using HO_wf_weaken_lth with opt.
  Qed.

  Lemma Twf_typ_extensionality : forall (T : MY.TT) (e e' : M_yt.TEnv),
    (forall (X : nat), Tget_left e X = Tget_left e' X) ->
    M_yt.Twf_typ e T -> M_yt.Twf_typ e' T.
  Proof.
    intros.
    assert (forall X : nat, M_yt.gTget_left e X = M_yt.gTget_left e' X).
    intros; do 2 rewrite <- Tget_left_gTget_left; apply H.
    unfold M_yt.Twf_typ, M_yt.gTget_left in *.
    eauto using HO_wf_extensionality with opt.
  Qed.

  Lemma Tget_right_remove_right_lt : forall (e : M_yt.TEnv) (x x' : nat),
    x < x' -> Tget_right (M_yt.Tremove_right e x') x = Tget_right e x.
  Proof.
    intros.
    rewrite M_yt.Tremove_right_gTremove_right.
    do 2 rewrite Tget_right_gTget_right.
    unfold M_yt.gTremove_right, M_yt.gTget_right; intros.
    autorewrite with isorew.
    auto using get_right_remove_right_lt with opt.
  Qed.

  Lemma Tget_right_remove_right_ge : forall (e : M_yt.TEnv) (x x' : nat),
    x >= x' -> Tget_right (M_yt.Tremove_right e x') x = Tget_right e (S x).
  Proof.
    intros.
    rewrite M_yt.Tremove_right_gTremove_right.
    do 2 rewrite Tget_right_gTget_right.
    unfold M_yt.gTremove_right, M_yt.gTget_right; intros.
    autorewrite with isorew.
    auto using get_right_remove_right_ge with opt.
  Qed.

  Lemma Tget_left_remove_right : forall (e : M_yt.TEnv) (X x': nat), 
    Tget_left e X = Tget_left (M_yt.Tremove_right e x') X.
  Proof.
    intros.
    rewrite M_yt.Tremove_right_gTremove_right.
    do 2 rewrite Tget_left_gTget_left.
    unfold M_yt.gTremove_right, M_yt.gTget_left; intros.
    autorewrite with isorew.
    auto using get_left_remove_right with opt.
  Qed.


  (** Tinsert_left inserts an element to environment.
     It is defined by Inductive not by Fixpoint 
     because there are some conditions for adding elements to environment. *)

  Inductive Tinsert_left : nat -> M_yt.TEnv -> M_yt.TEnv -> Prop :=
    Til_here :
      forall (T : MY.TT) (e : M_yt.TEnv), M_yt.Twf_typ e T -> Tinsert_left 0 e ((inl T)::e)
  | Til_right :
      forall (X : nat) (T : MY.TT) (e e' : M_yt.TEnv),
      Tinsert_left X e e' ->
      Tinsert_left X ((inr T)::e) ((inr (M_yy.Tshift X T))::e')
  | Til_left :
      forall (X : nat) (T : MY.TT) (e e' : M_yt.TEnv),
      Tinsert_left X e e' ->
      Tinsert_left (S X) ((inl T)::e) ((inl (M_yy.Tshift X T))::e').


  Lemma Tinsert_left_gTinsert_left : forall n (e e':M_yt.TEnv) ,
    Tinsert_left n e e' -> M_yt.gTinsert_left n e e'.
  Proof.
    unfold M_yt.gTinsert_left; induction 1;
    [ simpl; apply il_here;
      unfold M_yt.Twf_typ in H; auto
    | simpl; unfold M_yy.Tshift; rewrite MY.From_To; apply il_right;
      apply IHTinsert_left
    | simpl; unfold M_yy.Tshift; rewrite MY.From_To; apply il_left;
      apply IHTinsert_left
    ].
  Qed.

  Lemma gTinsert_left_Tinsert_left : forall n (e e':M_yt.TEnv) ,
    M_yt.gTinsert_left n e e' -> Tinsert_left n e e'.
  Proof.
    unfold M_yt.gTinsert_left.
    intros n e e'.
    pattern e at 2; rewrite <- (M_yt.To_From_TEnv e).
    pattern e' at 2; rewrite <- (M_yt.To_From_TEnv e').
    generalize (M_yt.From_TEnv e).
    generalize (M_yt.From_TEnv e').
    induction 1;
    [ simpl; apply Til_here;
      unfold M_yt.Twf_typ; autorewrite with isorew; auto; simpl
    | assert (MY.To (shift X MY.RR T) = M_yy.Tshift X (MY.To T));
      [unfold M_yy.Tshift; simpl; rewrite MY.From_To; auto 
        |simpl; rewrite H0; apply Til_right; auto]
    | simpl; assert (MY.To (shift X MY.RR T) = M_yy.Tshift X (MY.To T));
      [unfold M_yy.Tshift; simpl; rewrite MY.From_To; auto|
        simpl; rewrite H0; apply Til_left; auto]
    ].
  Qed.

  Lemma Tinsert_T_ind : forall (e:M_yt.TEnv) (T: MY.TT)(H:HO_wf 0 (MY.From T)),
    Tinsert_left 0 e (M_yt.Tinsert 0 e T H).
  Proof.
    intros.
    apply gTinsert_left_Tinsert_left.
    unfold M_yt.Tinsert, M_yt.gTinsert_left; intros.
    autorewrite with isorew.
    auto using insert_T_ind.
  Qed.

  Lemma Tinsert_T : forall (e: M_yt.TEnv) n (T:MY.TT)(H:M_yt.Twf_typ nil T),
    [[[e]]] > 0 ->
    [[[e]]] >= n ->
    Tinsert_left n e (M_yt.Tinsert n e T H).
  Proof.
    intros.
    apply gTinsert_left_Tinsert_left.
    unfold M_yt.Tinsert, M_yt.gTinsert_left; intros.
    autorewrite with isorew.
    auto using insert_T.
  Qed.

  Lemma Tget_left_insert_left_ge : forall (X X' : nat) (e e' : M_yt.TEnv),
    noRepr MY.RR ->
    Tinsert_left X' e e' ->
    X' <= X ->
    Tget_left e' (S X) = opt_map (M_yy.Tshift  X') (Tget_left e X).
  Proof.
    intros.
    do 2 rewrite Tget_left_gTget_left.
    apply Tinsert_left_gTinsert_left in H0.
    unfold M_yy.gTinsert_left, M_yt.gTget_left; intros.
    rewrite get_left_insert_left_ge with (X':=X') (e:=M_yt.From_TEnv e); 
      auto.
    induction (get_left(M_yt.From_TEnv e) X);
      unfold M_yy.Tshift; simpl; [rewrite MY.From_To | idtac]; auto.
  Qed.

  Lemma Tget_left_insert_left_lt : forall (X X' : nat) (e e' : M_yt.TEnv),
    noRepr MY.RR ->
    Tinsert_left X' e e' ->
    X < X' ->
    Tget_left e' X = opt_map (M_yy.Tshift X') (Tget_left e X).
  Proof.
    intros.
    do 2 rewrite Tget_left_gTget_left.
    apply Tinsert_left_gTinsert_left in H0.
    unfold M_yy.gTinsert_left, M_yt.gTget_left; intros.
    rewrite get_left_insert_left_lt with (X':=X') (e:=M_yt.From_TEnv e);
      auto.
    induction (get_left(M_yt.From_TEnv e) X);
      unfold M_yy.Tshift; simpl; [rewrite MY.From_To | idtac]; auto.
  Qed.

  Lemma Tget_right_insert_left : forall (x X' : nat) (e e' : M_yt.TEnv),
    noRepr MY.RR ->
    Tinsert_left X' e e' ->
    Tget_right e' x = opt_map (M_yy.Tshift X') (Tget_right e x).
  Proof.
    intros.
    do 2 rewrite Tget_right_gTget_right.
    apply Tinsert_left_gTinsert_left in H0.
    unfold M_yy.gTinsert_left, M_yt.gTget_right; intros.
    rewrite get_right_insert_left with (X':=X') (e:=M_yt.From_TEnv e);
      auto.
    induction (get_right(M_yt.From_TEnv e) x);
      unfold M_yy.Tshift; simpl; [rewrite MY.From_To | idtac]; auto.
  Qed.

  Lemma Tinsert_left_length : forall X (e e':M_yt.TEnv),
    Tinsert_left X e e' -> [[[e']]] >= S X.
  Proof.
    intros.
    apply Tinsert_left_gTinsert_left in H.
    unfold M_yy.gTinsert_left, M_yt.Tlth.
    eauto using insert_left_lth.
  Qed.

  Lemma Tinsert_left_length_1 : forall X (e e':M_yt.TEnv),
    Tinsert_left X e e' -> [[[e']]] = S [[[e]]].
  Proof.
    intros.
    apply Tinsert_left_gTinsert_left in H.
    unfold M_yy.gTinsert_left, M_yt.Tlth.
    eauto using insert_left_lth_1.
  Qed.

  Lemma Tinsert_left_wf_typ : forall (T : MY.TT) (X : nat) (e e' : M_yt.TEnv) (U:MY.TT),
    M_yt.Twf_typ nil U ->
    Tinsert_left X e e' ->
    M_yt.Twf_typ e T ->
    M_yt.Twf_typ e' (M_yy.Tshift X T).
  Proof.
    intros.
    apply Tinsert_left_gTinsert_left in H0.
    unfold M_yt.Twf_typ, M_yy.gTinsert_left, M_yy.Tshift; intros.
    rewrite MY.From_To.
    eauto using insert_left_HO_wf.
  Qed.

  Lemma Tinsert_left_wf_env : forall (X : nat) (e e' : M_yt.TEnv) (U: MY.TT),
    M_yt.Twf_typ nil U ->
    Tinsert_left X e e' ->
    M_yt.Twf_env e ->
    M_yt.Twf_env e'.
  Proof.
    intros.
    apply Tinsert_left_gTinsert_left in H0.
    apply M_yt.Twf_env_gTwf_env in H1.
    apply M_yt.gTwf_env_Twf_env.
    unfold M_yt.Twf_typ, M_yy.gTinsert_left, M_yt.gTwf_env.
    eauto using insert_left_wf_env.
  Qed.

  Lemma Twf_typ_weakening_left : forall (e : M_yt.TEnv) (T U U' : MY.TT),
    M_yt.Twf_typ nil U' ->
    M_yt.Twf_typ e T -> 
    M_yt.Twf_typ e U -> 
    M_yt.Twf_typ ((inl U) :: e) (M_yy.Tshift 0 T).
  Proof.
    unfold M_yt.Twf_typ, M_yy.Tshift; simpl; intros.
    rewrite MY.From_To.
    apply HO_wf_weakening_left with (U:= MY.From U)(U':= MY.From U'); auto.
  Qed.

  Lemma Tget_right_wf : forall (e : M_yt.TEnv) (n : nat) (T U: MY.TT),
    M_yt.Twf_typ nil U ->
    M_yt.Twf_env e ->
    Tget_right e n = Some T ->
    M_yt.Twf_typ e T.
  Proof.
    intros.
    rewrite Tget_right_gTget_right in H1.
    apply M_yt.Twf_env_gTwf_env in H0.
    unfold M_yt.Twf_typ, gTwf_env, M_yt.gTget_right in *; simpl; intros.
    apply get_right_wf with (n:=n) (U:=MY.From U);auto.
    induction (get_right (M_yt.From_TEnv e) n);
      [ inversion H1; rewrite MY.From_To; auto
      | discriminate].
  Qed.

  Lemma Tget_left_some_gt : forall (e: M_yt.TEnv) (X:atom) (U U':MY.TT),
    noRepr MY.RR ->
    M_yt.Twf_typ nil U' ->
    Tget_left e X = Some U ->
    [[[e]]] > X.
  Proof.
    intros.
    rewrite Tget_left_gTget_left in H1.
    unfold M_yt.Twf_typ, M_yt.gTget_left, M_yt.Tlth in *; intros.
    apply get_left_gt with (U:=MY.From U) (U':=MY.From U'); auto.
    destruct (get_left (M_yt.From_TEnv e) X); try discriminate.
    inversion H1; rewrite MY.From_To; auto.
  Qed.


  (**************************************************************)
  (** * Simplification tactics for generic contepts *)
  (**************************************************************)
  
  Ltac gfold :=
    match goal with
      | |- context [HO_wf [[M_yt.From_TEnv ?e]] (MY.From ?T)] =>
        assert (Tem: HO_wf [[M_yt.From_TEnv e]] (MY.From T) = M_yt.Twf_typ e T);
          [ unfold M_yt.Twf_typ; auto |
            rewrite Tem; clear Tem]
      | |- context [M_yt.Ysize (MY.From ?T)] =>
        assert (Tem: M_yt.Ysize (MY.From T) = size T);
          [ unfold size; auto |
            rewrite Tem; clear Tem]
      | |- context [ [[M_yt.From_TEnv ?e]] ] =>
        assert (Tem: [[M_yt.From_TEnv e]] = [[[e]]]);
          [ unfold M_yt.Tlth; auto |
            rewrite Tem; clear Tem]
    end.

  Ltac gsimpl :=
    unfold M_tt.Tsubst, M_yy.Tsubst, M_ty.Tsubst, M_yt.Tsubst, 
      M_tt.Tshift, M_ty.Tshift, M_yy.Tshift, M_yt.Tshift, 
      M_yt.Twf_typ, M_yt.Ysize, M_yt.Tlth;
      simpl;
      repeat rewrite conv_id;
      repeat rewrite <- M_tt.From_Tshift;
      repeat rewrite <- M_yy.From_Tshift;
      repeat rewrite <- M_ty.From_Tshift;
      repeat rewrite <- M_yt.From_Tshift;
      repeat rewrite <- M_tt.From_Tsubst;
      repeat rewrite <- M_yy.From_Tsubst;
      repeat rewrite <- M_ty.From_Tsubst;
      repeat rewrite <- M_yt.From_Tsubst;
      repeat rewrite MY.From_To;
      repeat rewrite MY.To_From;
      repeat rewrite MT.From_To;
      repeat rewrite MT.To_From;
      repeat gfold.

  Ltac gcase :=
    match goal with
      | |- context [le_gt_dec ?n ?n'] => 
        destruct (le_gt_dec n n');auto
      | |- context [lt_eq_lt_dec ?n ?n'] =>
        destruct (lt_eq_lt_dec n n') as [| s ]; destruct s; auto
    end.

