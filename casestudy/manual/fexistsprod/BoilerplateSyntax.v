Require Export BoilerplateFunctions.
Set Implicit Arguments.

(******************************************************************************)
(* Lemmas.                                                                    *)
(******************************************************************************)

Lemma hplus_assoc (h0 h1 h2 : hnat) :
  h0 + (h1 + h2) = (h0 + h1) + h2.
Proof.
  induction h2; simpl; f_equal; auto.
Qed.

Create HintDb interaction.
Ltac isimpl := simpl; autorewrite with interaction in *; simpl.

Ltac specialize_sucy :=
  progress match goal with
             | [ H : forall _ : hnat, _, k : hnat |- _ ] => apply (H (HSy k))
           end.
Ltac specialize_sucm :=
  progress match goal with
             | [ H : forall _ : hnat, _, k : hnat |- _ ] => apply (H (HSm k))
           end.
Ltac specialize_sucmy :=
  progress match goal with
             | [ H : forall _ : hnat, _, k : hnat |- _ ] => apply (H (HSm (HSy k)))
           end.

Ltac var_case :=
  match goal with
    | [ |- forall v i, _ ] =>
      induction v; simpl; intros; destruct i; auto; isimpl;
      try apply (f_equal (tshiftTy HO)) with (y := tvar _);
      try congruence; auto
  end.
Ltac ty_case T v :=
  induction T; simpl; intros;
    [ try apply f_equal with (f := tvar); apply v
    | apply f_equal2 with (f := tarr); trivial
    | apply f_equal with (f := tall); specialize_sucy; trivial
    | apply f_equal with (f := texist); specialize_sucy; trivial
    | apply f_equal2 with (f := tprod); trivial
    ].
Ltac tm_case t :=
  induction t; simpl; intros;
    [ try apply f_equal with (f := var); auto
    | apply f_equal2 with (f := abs); auto; specialize_sucm
    | apply f_equal2 with (f := app); auto
    | apply f_equal with (f := tabs); specialize_sucy
    | apply f_equal2 with (f := tapp); auto
    | apply f_equal3 with (f := pack); auto
    | apply f_equal2 with (f := unpack); auto; specialize_sucmy
    | apply f_equal2 with (f := prod); auto
    | apply f_equal3 with (f := case); rewrite <- ?hplus_assoc; auto
    ].

Lemma shiftIndex_comm_ind :
  forall v i c,
    shiftIndex (HSm c + v) (shiftIndex (HO + v) i) =
    shiftIndex (HO    + v) (shiftIndex (c  + v) i).
Proof.
  var_case.
Qed.

Lemma tshiftIndex_comm_ind :
  forall v i c,
    tshiftIndex (HSy c + v) (tshiftIndex (HO + v) i) =
    tshiftIndex (HO    + v) (tshiftIndex (c  + v) i).
Proof.
  var_case.
Qed.

Lemma tshiftTy_comm_ind (T : Ty) :
  forall v c,
    tshiftTy (HSy c + v) (tshiftTy (HO + v) T) =
    tshiftTy (HO    + v) (tshiftTy (c  + v) T).
Proof.
  ty_case T tshiftIndex_comm_ind.
Qed.

Lemma tshiftTy_comm (c : hnat) (T : Ty) :
    tshiftTy (HSy c) (tshiftTy HO T)
  = tshiftTy HO      (tshiftTy  c T).
Proof.
  apply (tshiftTy_comm_ind _ HO).
Qed.
Hint Rewrite tshiftTy_comm : interaction.

Lemma tsubstIndex_shiftIndex_reflection_ind :
  forall (k : hnat) (X : nat) (T : Ty),
    tsubstIndex (HO + k) T (tshiftIndex (HO + k) X) = tvar X.
Proof.
  var_case.
Qed.

Lemma tsubstTy_tshiftTy_reflection_ind (T : Ty) :
  forall k T',
    tsubstTy (HO + k) T' (tshiftTy (HO + k) T) = T.
Proof.
  ty_case T tsubstIndex_shiftIndex_reflection_ind.
Qed.
Hint Resolve tsubstTy_tshiftTy_reflection_ind.

Lemma tsubstTy_tshiftTy_reflection (T' T : Ty) :
  tsubstTy HO T' (tshiftTy HO T) = T.
Proof.
  apply (tsubstTy_tshiftTy_reflection_ind _ HO).
Qed.
Hint Rewrite tsubstTy_tshiftTy_reflection : interaction.

Lemma tshiftIndex_subord_ind :
  ∀ k X c, tshiftIndex (HSm c + k) X = tshiftIndex (c + k) X.
Proof.
  var_case.
Qed.

Lemma tshiftTy_subord_ind T :
  ∀ k c, tshiftTy (HSm c + k) T = tshiftTy (c + k) T.
Proof.
  ty_case T tshiftIndex_subord_ind.
Qed.

Lemma tshiftTy_subord T :
  ∀ c, tshiftTy (HSm c) T = tshiftTy c T.
Proof.
  apply (tshiftTy_subord_ind _ HO).
Qed.
Hint Rewrite tshiftTy_subord : interaction.

Lemma tshiftTy_tsubstIndex_comm_ind :
  forall (k : hnat) (X : nat) c (T : Ty),
    tshiftTy    (c  + k) (tsubstIndex (HO + k) T X) =
    tsubstIndex (HO + k) (tshiftTy c T) (tshiftIndex (HSy c + k) X).
Proof.
  var_case.
Qed.

Lemma tshiftTy_tsubstTy_comm_ind (T : Ty):
  forall (k c : hnat) (T' : Ty),
    tshiftTy (c  + k) (tsubstTy (HO + k) T' T) =
    tsubstTy (HO + k) (tshiftTy c T') (tshiftTy (HSy c + k) T).
Proof.
  ty_case T tshiftTy_tsubstIndex_comm_ind.
Qed.

Lemma tshiftTy_tsubstTy_comm c (T T2 : Ty) :
    tshiftTy c  (tsubstTy HO T T2)
  = tsubstTy HO (tshiftTy c T) (tshiftTy (HSy c) T2).
Proof.
  apply (tshiftTy_tsubstTy_comm_ind _ HO).
Qed.
Hint Rewrite tshiftTy_tsubstTy_comm : interaction.

Lemma tsubstIndex_shiftIndex_comm_ind :
  forall k Y X T',
    tsubstIndex (HSy X + k) T' (tshiftIndex (HO + k) Y) =
    tshiftTy (HO + k)          (tsubstIndex (X + k) T' Y).
Proof.
  var_case.
Qed.

Lemma tsubstTy_tshiftTy_comm_ind (T : Ty) :
  forall k X T',
    tsubstTy (HSy X + k) T' (tshiftTy (HO + k) T) =
    tshiftTy (HO    + k) (tsubstTy (X + k) T' T).
Proof.
  ty_case T tsubstIndex_shiftIndex_comm_ind.
Qed.
Hint Resolve tsubstTy_tshiftTy_comm_ind.

Lemma tsubstTy_tshiftTy_comm :
  forall X T' T,
    tsubstTy (HSy X) T' (tshiftTy HO T) =
    tshiftTy HO (tsubstTy X T' T).
Proof.
  intros; apply (tsubstTy_tshiftTy_comm_ind _ HO).
Qed.
Hint Rewrite tsubstTy_tshiftTy_comm : interaction.

Lemma tsubstIndex_subord_ind T' :
  ∀ k Y X, tsubstIndex (HSm X + k) T' Y = tsubstIndex (X + k) T' Y.
Proof.
  var_case.
Qed.

Lemma tsubstTy_subord_ind T' T:
  ∀ k X, tsubstTy (HSm X + k) T' T = tsubstTy (X + k) T' T.
Proof.
  ty_case T tsubstIndex_subord_ind.
Qed.
Hint Resolve tsubstTy_subord_ind.

Lemma tsubstTy_subord T' T :
  ∀ X, tsubstTy (HSm X) T' T = tsubstTy X T' T.
Proof.
  apply (tsubstTy_subord_ind _ _ HO).
Qed.
Hint Rewrite tsubstTy_subord : interaction.

Lemma tsubstTm_subord_ind T' t:
  ∀ k X, tsubstTm (HSm X + k) T' t = tsubstTm (X + k) T' t.
Proof.
  tm_case t.
Qed.

Lemma tsubstTm_subord T' T :
  ∀ X, tsubstTm (HSm X) T' T = tsubstTm X T' T.
Proof.
  apply (tsubstTm_subord_ind _ _ HO).
Qed.
Hint Rewrite tsubstTm_subord : interaction.

Lemma tsubstTy_tsubstIndex_comm_ind :
  forall k Y T1 T2 X,
    tsubstTy (X  + k) T1 (tsubstIndex (HO + k) T2 Y) =
    tsubstTy (HO + k) (tsubstTy X T1 T2) (tsubstIndex (HSy X + k) T1 Y).
Proof.
  var_case.
Qed.

Lemma tsubstTy_tsubstTy_comm_ind (T : Ty) :
  forall k X T1 T2,
    tsubstTy (X  + k) T1 (tsubstTy (HO + k) T2 T) =
    tsubstTy (HO + k) (tsubstTy X T1 T2) (tsubstTy (HSy X + k) T1 T).
Proof.
  ty_case T tsubstTy_tsubstIndex_comm_ind.
Qed.

Lemma tsubstTy_tsubstTy_comm :
  forall X T1 T2 T,
    tsubstTy X T1 (tsubstTy HO T2 T) =
    tsubstTy HO (tsubstTy X T1 T2) (tsubstTy (HSy X) T1 T).
Proof.
  intros; apply (tsubstTy_tsubstTy_comm_ind _ HO).
Qed.
Hint Rewrite tsubstTy_tsubstTy_comm : interaction.

Lemma tsubstTm_shiftTm0_comm_ind (t : Tm) :
  forall (k X  : hnat) (S0 : Ty),
    tsubstTm (X + k) S0 (shiftTm (HO + k) t) =
    shiftTm (HO + k) (tsubstTm (X + k) S0 t).
Proof.
  tm_case t.
Qed.

Definition tsubstTm_shiftTm0_comm (t : Tm) (X : hnat) (S0 : Ty) :
  tsubstTm X S0 (shiftTm HO t) = shiftTm HO (tsubstTm X S0 t) :=
  tsubstTm_shiftTm0_comm_ind t HO X S0.

Lemma tsubstTm_tshiftTm0_comm_ind (t : Tm) :
  forall (k X : hnat) (T' : Ty),
    tsubstTm (HSy X + k) T' (tshiftTm (HO + k) t) =
    tshiftTm (HO    + k) (tsubstTm (X + k) T' t).
Proof.
  tm_case t.
Qed.

Definition tsubstTm_tshiftTm0_comm (t : Tm) (X : hnat) (T' : Ty) :
  tsubstTm (HSy X) T' (tshiftTm HO t) =
  tshiftTm HO (tsubstTm X T' t) :=
  tsubstTm_tshiftTm0_comm_ind t HO X T'.

Lemma tsubstTm_substTm0_comm_ind (t : Tm) :
  forall (k X : hnat) (T' : Ty) (t' : Tm),
    tsubstTm (X + k) T' (substTm k t' t) =
    substTm k (tsubstTm X T' t') (tsubstTm (X + k) T' t).
Proof.
  tm_case t.
  - revert x X; induction k; simpl; intros.
    + destruct x; simpl; eauto.
    + destruct x; simpl; eauto.
      rewrite tsubstTm_shiftTm0_comm.
      rewrite tsubstTm_subord.
      f_equal; auto.
    + rewrite tsubstTm_tshiftTm0_comm.
      f_equal; auto.
Qed.

Definition tsubstTm_substTm0_comm (t : Tm) (X : hnat) (T' : Ty) (t' : Tm) :
  tsubstTm X T' (substTm HO t' t) =
  substTm HO (tsubstTm X T' t') (tsubstTm X T' t) :=
  tsubstTm_substTm0_comm_ind t HO X T' t'.

Lemma tsubstTm_tshiftTm_reflection_ind (t : Tm) :
  forall k T',
    tsubstTm (HO + k) T' (tshiftTm (HO + k) t) = t.
Proof.
  tm_case t.
Qed.

Definition tsubstTm_tshiftTm_reflection (t : Tm) (T' : Ty) :
  tsubstTm HO T' (tshiftTm HO t) = t :=
  tsubstTm_tshiftTm_reflection_ind t HO T'.
Hint Rewrite tsubstTm_tshiftTm_reflection : interaction.

Lemma dom_tshiftEnv (c : hnat) (Δ : Env) :
  dom (tshiftEnv c Δ) = dom Δ.
Proof.
  induction Δ; simpl; f_equal; auto.
Qed.
Hint Rewrite dom_tshiftEnv : interaction.

Lemma dom_tsubstEnv (X : hnat) (T' : Ty) (Δ : Env) :
  dom (tsubstEnv X T' Δ) = dom Δ.
Proof.
  induction Δ; simpl; f_equal; auto.
Qed.
Hint Rewrite dom_tsubstEnv : interaction.


Lemma append_assoc (Γ : Env) (Δ1 Δ2 : Env) :
  append Γ (append Δ1 Δ2) = append (append Γ Δ1) Δ2.
Proof.
  induction Δ2; simpl; f_equal; auto.
Qed.

Lemma dom_append (Δ1 Δ2 : Env) :
  dom (append Δ1 Δ2) = dom Δ1 + dom Δ2.
Proof.
  induction Δ2; simpl; f_equal; auto.
Qed.

Lemma tshiftEnv_append (c : hnat) (Δ1 Δ2 : Env) :
  tshiftEnv c (append Δ1 Δ2) =
  append (tshiftEnv c Δ1) (tshiftEnv (c + dom Δ1) Δ2).
Proof.
  induction Δ2; simpl; f_equal; auto.
  rewrite dom_append, hplus_assoc; auto.
Qed.
Hint Rewrite tshiftEnv_append : interaction.

Lemma tsubstEnv_append (X : hnat) (S : Ty) (Δ1 Δ2 : Env) :
  tsubstEnv X S (append Δ1 Δ2) =
  append (tsubstEnv X S Δ1) (tsubstEnv (X + dom Δ1) S Δ2).
Proof.
  induction Δ2; simpl; f_equal; auto.
  rewrite dom_append, hplus_assoc; auto.
Qed.
Hint Rewrite tsubstEnv_append : interaction.

(******************************************************************************)
(* Context insertions.                                                        *)
(******************************************************************************)

Inductive shift_etvar : hnat → Env → Env → Prop :=
  | shift_etvar_here {Γ} :
      shift_etvar HO Γ (etvar Γ)
  | shift_etvar_there_evar {Γ1 Γ2 c T} :
      shift_etvar c Γ1 Γ2 →
      shift_etvar (HSm c) (evar Γ1 T) (evar Γ2 (tshiftTy c T))
  | shift_etvar_there_etvar {Γ1 Γ2 c} :
      shift_etvar c Γ1 Γ2 →
      shift_etvar (HSy c) (etvar Γ1) (etvar Γ2).
Hint Constructors shift_etvar.

Inductive shift_evar : hnat → Env → Env → Prop :=
  | shift_evar_here {Γ T} :
      shift_evar HO Γ (evar Γ T)
  | shift_evar_there_evar {Γ1 Γ2 c T} :
      shift_evar c Γ1 Γ2 →
      shift_evar (HSm c) (evar Γ1 T) (evar Γ2 T)
  | shift_evar_there_etvar {Γ1 Γ2 c} :
      shift_evar c Γ1 Γ2 →
      shift_evar (HSy c) (etvar Γ1) (etvar Γ2).
Hint Constructors shift_evar.

Lemma weaken_shift_etvar {Γ1 Γ2: Env} (Δ : Env) {c} :
  shift_etvar c Γ1 Γ2 →
  shift_etvar (c + dom Δ) (append Γ1 Δ) (append Γ2 (tshiftEnv c Δ)).
Proof.
  revert c Γ2; induction Δ; simpl; intros; try constructor; auto.
Qed.
Hint Resolve weaken_shift_etvar.

Lemma weaken_shift_evar {Γ1 Γ2 : Env} (Δ : Env) {c} :
  shift_evar c Γ1 Γ2 →
  shift_evar (c + dom Δ) (append Γ1 Δ) (append Γ2 Δ).
Proof.
  revert c Γ2; induction Δ; simpl; intros; try constructor; auto.
Qed.
Hint Resolve weaken_shift_evar.

(******************************************************************************)
(* Lemmas about shifting and context lookups.                                 *)
(******************************************************************************)

Lemma shift_etvar_lookup_etvar {Γ1 Γ2 c} (ib : shift_etvar c Γ1 Γ2) :
  ∀ X, lookup_etvar Γ1 X →
       lookup_etvar Γ2 (tshiftIndex c X).
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
