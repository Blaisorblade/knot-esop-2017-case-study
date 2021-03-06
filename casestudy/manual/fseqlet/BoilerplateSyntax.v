Require Export BoilerplateFunctions.
Set Implicit Arguments.

(******************************************************************************)
(* Lemmas.                                                                    *)
(******************************************************************************)

Create HintDb interaction.
Ltac isimpl := simpl; autorewrite with interaction; simpl.

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
            ].

Lemma lengthExt_tshiftExt (c : nat) (Δ : Ext) :
  lengthExt (tshiftExt c Δ) = lengthExt Δ.
Proof.
  induction Δ; simpl; f_equal; auto.
Qed.
Hint Rewrite lengthExt_tshiftExt : interaction.

Lemma lengthExt_tsubstExt (X : nat) (T' : Ty) (Δ : Ext) :
  lengthExt (tsubstExt X T' Δ) = lengthExt Δ.
Proof.
  induction Δ; simpl; f_equal; auto.
Qed.
Hint Rewrite lengthExt_tsubstExt : interaction.

Lemma bind_tshiftDecls (c : nat) (ds : Decls) :
  bind (tshiftDecls c ds) = bind ds.
Proof.
  induction ds; simpl; f_equal; auto.
Qed.
Hint Rewrite bind_tshiftDecls : interaction.

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

(******************************************************************************)
(* Interaction between term substitutions and typevar shifting.               *)
(******************************************************************************)

Lemma shiftTm_tshiftTm_comm :
  (∀ (t : Tm) ca cb,
    shiftTm  cb (tshiftTm ca t) =
    tshiftTm ca (shiftTm  cb t)) ∧
  (∀ (ds : Decls) ca cb,
    shiftDecls  cb (tshiftDecls ca ds) =
    tshiftDecls ca (shiftDecls  cb ds)).
Proof.
  apply tm_decls_induction; intros; isimpl; congruence.
Qed.

(******************************************************************************)
(* Context insertions.                                                        *)
(******************************************************************************)

Inductive shift_etvar : nat → Env → Env → Prop :=
  | ib_here {Γ : Env} :
      shift_etvar O Γ (etvar Γ)
  | ib_var {Γ1 : Env} {Γ2 : Env} {c T} :
      shift_etvar c Γ1 Γ2 →
      shift_etvar c (evar Γ1 T) (evar Γ2 (tshiftTy c T))
  | ib_etvar {Γ1 : Env} {Γ2 : Env} {c} :
      shift_etvar c Γ1 Γ2 →
      shift_etvar (S c) (etvar Γ1) (etvar Γ2).
Hint Constructors shift_etvar.

Inductive shift_evar : nat → Env → Env → Prop :=
  | iv_here {Γ : Env} {T} :
      shift_evar O Γ (evar Γ T)
  | iv_var {Γ1 : Env} {Γ2 : Env} {c T} :
      shift_evar c Γ1 Γ2 →
      shift_evar (S c) (evar Γ1 T) (evar Γ2 T)
  | iv_etvar {Γ1 : Env} {Γ2 : Env} {c} :
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
  induction ib; intros; dependent destruction H; simpl;
    try rewrite tshiftTy_comm; repeat constructor; auto.
Qed.

Lemma shift_etvar_lookup_evar {Γ1 Γ2 c} (ib : shift_etvar c Γ1 Γ2) :
  ∀ x T, lookup_evar Γ1 x T →
         lookup_evar Γ2 x (tshiftTy c T).
Proof.
  induction ib; intros; dependent destruction H; simpl;
    try rewrite tshiftTy_comm; repeat constructor; auto.
Qed.

Lemma shift_evar_lookup_etvar {Γ1 Γ2 c} (iv : shift_evar c Γ1 Γ2) :
  ∀ X, lookup_etvar Γ1 X → lookup_etvar Γ2 X.
Proof.
  induction iv; intros; dependent destruction H; simpl;
    repeat constructor; auto.
Qed.

Lemma shift_evar_lookup_evar {Γ1 Γ2 c} (iv : shift_evar c Γ1 Γ2) :
  ∀ x T, lookup_evar Γ1 x T → lookup_evar Γ2 (shiftIndex c x) T.
Proof.
  induction iv; intros; dependent destruction H; simpl;
    repeat constructor; auto.
Qed.

Lemma shift_etvar_wftyp {Γ1 T} (wT: wfTy Γ1 T) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → wfTy Γ2 (tshiftTy c T).
Proof.
  induction wT; simpl; econstructor; eauto using shift_etvar_lookup_etvar.
Qed.

Lemma weakening_etvar_wftyp {Γ T} (wT: wfTy Γ T) :
  wfTy (etvar Γ) (tshiftTy O T).
Proof.
  eauto using shift_etvar_wftyp.
Qed.

Lemma shift_evar_wftyp {Γ1 T} (wT: wfTy Γ1 T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → wfTy Γ2 T.
Proof.
  induction wT; simpl; econstructor; eauto using shift_evar_lookup_etvar.
Qed.

Lemma weakening_var_wftyp {Γ : Env} {S T} :
  wfTy Γ T → wfTy (evar Γ S) T.
Proof.
  eauto using shift_evar_wftyp.
Qed.

(******************************************************************************)
(* Context extensions.                                                        *)
(******************************************************************************)

Lemma extend_append (Γ : Env) (Δ1 Δ2 : Ext) :
  extend Γ (append Δ1 Δ2) = extend (extend Γ Δ1) Δ2.
Proof.
  induction Δ2; simpl; f_equal; auto.
Qed.

Lemma lengthExt_append (Δ1 Δ2 : Ext) :
  lengthExt (append Δ1 Δ2) = lengthExt Δ2 + lengthExt Δ1.
Proof.
  induction Δ2; simpl; try rewrite IHΔ2; induction Δ1; auto.
Qed.

Lemma tshiftExt_append (c : nat) (Δ1 Δ2 : Ext) :
  tshiftExt c (append Δ1 Δ2) = append (tshiftExt c Δ1) (tshiftExt c Δ2).
Proof.
  induction Δ2; simpl; f_equal; auto.
Qed.

Lemma tsubstExt_append (X : nat) (T' : Ty) (Δ1 Δ2 : Ext) :
  tsubstExt X T' (append Δ1 Δ2) = append (tsubstExt X T' Δ1) (tsubstExt X T' Δ2).
Proof.
  induction Δ2; simpl; f_equal; auto.
Qed.

Lemma weakenshift_etvar {Γ1 : Env} {Γ2 : Env} {Δ : Ext} {c} :
  shift_etvar c Γ1 Γ2 →
  shift_etvar c (extend Γ1 Δ) (extend Γ2 (tshiftExt c Δ)).
Proof.
  revert c Γ2; induction Δ; simpl; intros; try constructor; auto.
Qed.

Lemma weakenshift_evar {Γ1 : Env} {Γ2 : Env} (Δ : Ext) {c} :
  shift_evar c Γ1 Γ2 → shift_evar (lengthExt Δ + c) (extend Γ1 Δ) (extend Γ2 Δ).
Proof.
  revert c Γ2; induction Δ; simpl; intros; try constructor; auto.
Qed.
