Require Export BoilerplateFunctions.
Set Implicit Arguments.

(******************************************************************************)
(* Lemmas.                                                                    *)
(******************************************************************************)

Create HintDb interaction.
Ltac isimpl := simpl; autorewrite with interaction in *; simpl.

Ltac specialize_suc :=
  progress
    match goal with
      | [ H : forall _ : nat, _, k : nat |- _ ] => apply (H (S k))
    end.
Ltac var_case :=
  match goal with
    | [ |- forall v i, _ ] =>
      induction v; simpl; intros; destruct i; auto; isimpl;
      try apply (f_equal (tshiftTy 0)) with (y := tvar _);
      try congruence; auto
  end.
Ltac ty_case T v :=
  induction T; simpl; intros;
  try solve [ try apply f_equal with (f := tvar); apply v
            | apply f_equal2 with (f := tarr); trivial
            | apply f_equal with (f := tall); specialize_suc; trivial
            | apply f_equal with (f := texist); specialize_suc; trivial
            ].

Lemma shiftIndex_comm_ind :
  forall v i c,
    shiftIndex (v + S c) (shiftIndex (v + O) i) =
    shiftIndex (v + O  ) (shiftIndex (v + c) i).
Proof.
  var_case.
Qed.

Lemma tshiftTy_comm_ind (T : Ty) :
  forall v c,
    tshiftTy (v + S c) (tshiftTy (v + O) T) =
    tshiftTy (v + O  ) (tshiftTy (v + c) T).
Proof.
  ty_case T shiftIndex_comm_ind.
Qed.

Lemma tshiftTy_comm (c : nat) (T : Ty) :
    tshiftTy (S c) (tshiftTy O T)
  = tshiftTy O     (tshiftTy c T).
Proof.
  apply (tshiftTy_comm_ind _ 0).
Qed.
Hint Rewrite tshiftTy_comm : interaction.

Lemma tsubstIndex_shiftIndex_reflection_ind :
  forall (k X : nat) (T : Ty),
    tsubstIndex (k + 0) T (shiftIndex (k + O) X) = tvar X.
Proof.
  var_case.
Qed.

Lemma tsubstTy_tshiftTy_reflection_ind (T : Ty) :
  forall k T',
    tsubstTy (k + 0) T' (tshiftTy (k + O) T) = T.
Proof.
  ty_case T tsubstIndex_shiftIndex_reflection_ind.
Qed.

Lemma tsubstTy_tshiftTy_reflection (T' T : Ty) :
  tsubstTy 0 T' (tshiftTy O T) = T.
Proof.
  apply (tsubstTy_tshiftTy_reflection_ind _ 0).
Qed.
Hint Rewrite tsubstTy_tshiftTy_reflection : interaction.

Lemma tshiftTy_tsubstIndex_comm_ind :
  forall (k X c : nat) (T : Ty),
    tshiftTy (k + c) (tsubstIndex (k + 0) T X) =
    tsubstIndex (k + 0) (tshiftTy c T) (shiftIndex (k + S c) X).
Proof.
  var_case.
Qed.

Lemma tshiftTy_tsubstTy_comm_ind (T : Ty):
  forall (k c : nat) (T' : Ty),
    tshiftTy (k + c) (tsubstTy (k + 0) T' T) =
    tsubstTy (k + 0) (tshiftTy c T') (tshiftTy (k + S c) T).
Proof.
  ty_case T tshiftTy_tsubstIndex_comm_ind.
Qed.

Lemma tshiftTy_tsubstTy_comm c (T T2 : Ty) :
    tshiftTy c (tsubstTy O T T2)
  = tsubstTy O (tshiftTy c T) (tshiftTy (S c) T2).
Proof.
  apply (tshiftTy_tsubstTy_comm_ind _ 0).
Qed.
Hint Rewrite tshiftTy_tsubstTy_comm : interaction.

Lemma tsubstIndex_shiftIndex_comm_ind :
  forall k Y X T',
    tsubstIndex (k + S X) T' (shiftIndex (k + 0) Y) =
    tshiftTy (k + 0) (tsubstIndex (k + X) T' Y).
Proof.
  var_case.
Qed.

Lemma tsubstTy_tshiftTy_comm_ind (T : Ty) :
  forall k X T',
    tsubstTy (k + S X) T' (tshiftTy (k + 0) T) =
    tshiftTy (k + 0) (tsubstTy (k + X) T' T).
Proof.
  ty_case T tsubstIndex_shiftIndex_comm_ind.
Qed.

Lemma tsubstTy_tshiftTy_comm :
  forall X T' T,
    tsubstTy (S X) T' (tshiftTy 0 T) =
    tshiftTy 0 (tsubstTy X T' T).
Proof.
  intros; apply (tsubstTy_tshiftTy_comm_ind _ 0).
Qed.
Hint Rewrite tsubstTy_tshiftTy_comm : interaction.

Lemma tsubstTy_tsubstIndex_comm_ind :
  forall k Y T1 T2 X,
    tsubstTy (k + X) T1 (tsubstIndex (k + 0) T2 Y) =
    tsubstTy (k + 0) (tsubstTy X T1 T2) (tsubstIndex (k + S X) T1 Y).
Proof.
  var_case.
Qed.

Lemma tsubstTy_tsubstTy_comm_ind (T : Ty) :
  forall k X T1 T2,
    tsubstTy (k + X) T1 (tsubstTy (k + 0) T2 T) =
    tsubstTy (k + 0) (tsubstTy X T1 T2) (tsubstTy (k + (S X)) T1 T).
Proof.
  ty_case T tsubstTy_tsubstIndex_comm_ind.
Qed.

Lemma tsubstTy_tsubstTy_comm :
  forall X T1 T2 T,
    tsubstTy X T1 (tsubstTy 0 T2 T) =
    tsubstTy 0 (tsubstTy X T1 T2) (tsubstTy (S X) T1 T).
Proof.
  intros; apply (tsubstTy_tsubstTy_comm_ind _ 0).
Qed.
Hint Rewrite tsubstTy_tsubstTy_comm : interaction.

Fixpoint hplus (h1 h2: hnat) : hnat :=
  match h2 with
    | hn0 => h1
    | hsm h2' => hsm (hplus h1 h2')
    | hsy h2' => hsy (hplus h1 h2')
  end.

Fixpoint hplusNatTy (n: nat) (h: hnat) : nat :=
  match h with
    | hn0 => n
    | hsm h' => hplusNatTy n h'
    | hsy h' => S (hplusNatTy n h')
  end.

Fixpoint hplusNatTm (n: nat) (h: hnat) : nat :=
  match h with
    | hn0 => n
    | hsm h' => S (hplusNatTm n h')
    | hsy h' => hplusNatTm n h'
  end.

Lemma tsubstTm_shiftTm0_comm_ind (t : Tm) :
  forall (k : hnat) (X : nat) (S0 : Ty),
    tsubstTm (hplusNatTy X k) S0 (shiftTm (hplusNatTm 0 k) t) =
    shiftTm (hplusNatTm 0 k) (tsubstTm (hplusNatTy X k) S0 t).
Proof.
  induction t; simpl; intros; f_equal; auto.
  - apply (IHt (hsm k)).
  - apply (IHt (hsy k)).
  - apply (IHt2 (hsm (hsy k))).
Qed.

Definition tsubstTm_shiftTm0_comm (t : Tm) (X : nat) (S0 : Ty) :
  tsubstTm X S0 (shiftTm 0 t) =
  shiftTm 0 (tsubstTm X S0 t) := tsubstTm_shiftTm0_comm_ind t hn0 X S0.

(* Lemma tshiftTm_tsubstTm_comm_ind (t : Tm): *)
(*   forall (k c : nat) (T' : Ty), *)
(*     tshiftTm (k + c) (tsubstTm (k + 0) T' t) = *)
(*     tsubstTm (k + 0) (tshiftTy c T') (tshiftTm (k + S c) t). *)
(* Proof. *)
(*   induction t; simpl; intros; f_equal; try rewrite tshiftTy_tsubstTy_comm_ind; auto. *)
(*   - apply (IHt (S k)). *)
(*   - apply (IHt2 (S k)). *)
(* Qed. *)

(* Definition tshiftTm_tsubstTm_comm c (T' : Ty) (t : Tm) : *)
(*   tshiftTm c (tsubstTm O T' t) = *)
(*   tsubstTm O (tshiftTy c T') (tshiftTm (S c) t) := *)
(*   tshiftTm_tsubstTm_comm_ind t 0 c T'. *)


Lemma tsubstTm_tshiftTm0_comm_ind (t : Tm) :
  forall (k X : nat) (T' : Ty),
    tsubstTm (k + S X) T' (tshiftTm (k + 0) t) =
    tshiftTm (k + 0) (tsubstTm (k + X) T' t).
Proof.
  induction t; simpl; intros; f_equal;
    try rewrite tsubstTy_tshiftTy_comm_ind; auto.
  - apply (IHt (S k)).
  - apply (IHt2 (S k)).
Qed.

Definition tsubstTm_tshiftTm0_comm (t : Tm) (X : nat) (T' : Ty) :
  tsubstTm (S X) T' (tshiftTm 0 t) =
  tshiftTm 0 (tsubstTm X T' t) :=
  tsubstTm_tshiftTm0_comm_ind t 0 X T'.

Lemma tsubstTm_substTm0_comm_ind (t : Tm) :
  forall (k : hnat) (X : nat) (T' : Ty) (t' : Tm),
    tsubstTm (hplusNatTy X k) T' (substTm k t' t) =
    substTm k (tsubstTm X T' t') (tsubstTm (hplusNatTy X k) T' t).
Proof.
  induction t; simpl; intros; try (f_equal; eauto; fail).
  - revert x X; induction k; simpl; intros.
    + destruct x; simpl; eauto.
    + destruct x; simpl; eauto.
      rewrite tsubstTm_shiftTm0_comm.
      f_equal; auto.
    + rewrite tsubstTm_tshiftTm0_comm.
      f_equal; auto.
  - f_equal.
    apply (IHt (hsm k)).
  - f_equal; auto.
    apply (IHt (hsy k)).
  - f_equal; auto.
    apply (IHt2 (hsm (hsy k))).
Qed.

Definition tsubstTm_substTm0_comm (t : Tm) (X : nat) (T' : Ty) (t' : Tm) :
  tsubstTm X T' (substTm hn0 t' t) =
  substTm hn0 (tsubstTm X T' t') (tsubstTm X T' t) :=
  tsubstTm_substTm0_comm_ind t hn0 X T' t'.

Lemma tsubstTm_tshiftTm_reflection_ind (t : Tm) :
  forall k T',
    tsubstTm (k + 0) T' (tshiftTm (k + O) t) = t.
Proof.
  induction t; simpl; intros; f_equal;
    try rewrite tsubstTy_tshiftTy_reflection_ind; auto.
  - apply (IHt (S k)).
  - apply (IHt2 (S k)).
Qed.

Definition tsubstTm_tshiftTm_reflection (t : Tm) (T' : Ty) :
  tsubstTm 0 T' (tshiftTm 0 t) = t :=
  tsubstTm_tshiftTm_reflection_ind t 0 T'.

(******************************************************************************)
(* Context insertions.                                                        *)
(******************************************************************************)

Inductive shift_etvar : nat → Env → Env → Prop :=
  | shift_etvar_here {Γ} :
      shift_etvar 0 Γ (etvar Γ)
  | shift_etvar_there_evar {Γ1 Γ2 c T} :
      shift_etvar c Γ1 Γ2 →
      shift_etvar c (evar Γ1 T) (evar Γ2 (tshiftTy c T))
  | shift_etvar_there_etvar {Γ1 Γ2 c} :
      shift_etvar c Γ1 Γ2 →
      shift_etvar (S c) (etvar Γ1) (etvar Γ2).
Hint Constructors shift_etvar.

Inductive shift_evar : nat → Env → Env → Prop :=
  | shift_evar_here {Γ T} :
      shift_evar 0 Γ (evar Γ T)
  | shift_evar_there_evar {Γ1 Γ2 c T} :
      shift_evar c Γ1 Γ2 →
      shift_evar (S c) (evar Γ1 T) (evar Γ2 T)
  | shift_evar_there_etvar {Γ1 Γ2 c} :
      shift_evar c Γ1 Γ2 →
      shift_evar c (etvar Γ1) (etvar Γ2).
Hint Constructors shift_evar.

(******************************************************************************)
(* Lemmas about shifting and context lookups.                                 *)
(******************************************************************************)

Lemma shift_etvar_lookup_etvar {Γ1 Γ2 c} (ib : shift_etvar c Γ1 Γ2) :
  ∀ X, lookup_etvar Γ1 X →
       lookup_etvar Γ2 (shiftIndex c X).
Proof.
  induction ib; inversion 1; isimpl; eauto.
Qed.
Hint Resolve shift_etvar_lookup_etvar.

Lemma shift_etvar_lookup_evar {Γ1 Γ2 c} (ib : shift_etvar c Γ1 Γ2) :
  ∀ x T, lookup_evar Γ1 x T →
         lookup_evar Γ2 x (tshiftTy c T).
Proof.
  induction ib; inversion 1; isimpl; eauto.
Qed.
Hint Resolve shift_etvar_lookup_evar.

Lemma shift_evar_lookup_etvar {Γ1 Γ2 c} (iv : shift_evar c Γ1 Γ2) :
  ∀ X, lookup_etvar Γ1 X → lookup_etvar Γ2 X.
Proof.
  induction iv; inversion 1; simpl; eauto.
Qed.
Hint Resolve shift_evar_lookup_etvar.

Lemma shift_evar_lookup_evar {Γ1 Γ2 c} (iv : shift_evar c Γ1 Γ2) :
  ∀ x T, lookup_evar Γ1 x T → lookup_evar Γ2 (shiftIndex c x) T.
Proof.
  induction iv; inversion 1; simpl; eauto.
Qed.
Hint Resolve shift_evar_lookup_evar.

(******************************************************************************)
(* Weakening lemmas for well-formedness                                       *)
(******************************************************************************)

Lemma shift_etvar_wftyp {Γ1 T} (wfT: wfTy Γ1 T) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → wfTy Γ2 (tshiftTy c T).
Proof.
  induction wfT; simpl; econstructor; eauto.
Qed.
Hint Resolve shift_etvar_wftyp.

Lemma shift_evar_wftyp {Γ1 T} (wfT: wfTy Γ1 T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → wfTy Γ2 T.
Proof.
  induction wfT; simpl; econstructor; eauto.
Qed.
Hint Resolve shift_evar_wftyp.
