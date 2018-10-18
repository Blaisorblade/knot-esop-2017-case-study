Require Export BoilerplateSyntax.
Require Export SpecSemantics.
Set Implicit Arguments.

Lemma PTyping_bindPat_dom {Γ p T Δ} (wp: PTyping Γ p T Δ) :
  bindPat p = dom Δ.
Proof.
  induction wp; isimpl; try rewrite dom_append; congruence.
Qed.

Lemma weakenTy_hplus T k1 k2 :
  weakenTy T (k1 + k2) = weakenTy (weakenTy T k1) k2.
Proof.
  revert T k1. induction k2; simpl; congruence.
Qed.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma weakenTy_tshiftTy c T Δ :
  tshiftTy (c + dom Δ) (weakenTy T (dom Δ)) =
  weakenTy (tshiftTy c T) (dom Δ).
Proof.
  induction Δ; isimpl; now f_equal.
Qed.
Hint Rewrite weakenTy_tshiftTy : interaction.

Lemma weakenTy_tsubstTy X S T Δ :
  tsubstTy (X + dom Δ) S (weakenTy T (dom Δ)) =
  weakenTy (tsubstTy X S T) (dom Δ).
Proof.
  induction Δ; isimpl; now f_equal.
Qed.
Hint Rewrite weakenTy_tsubstTy : interaction.

Lemma shift_etvar_ptyping {Γ1 p T Δ} (wp: PTyping Γ1 p T Δ) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → PTyping Γ2 p (tshiftTy c T) (tshiftEnv c Δ).
Proof.
  induction wp; intros; isimpl; econstructor; isimpl; eauto.
  specialize (IHwp2 (c + dom Δ1)); isimpl; eauto.
Qed.
Hint Resolve shift_etvar_ptyping.

Lemma shift_etvar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Typing Γ2 (tshiftTm c t) (tshiftTy c T).
Proof.
  induction wt; intros; try (isimpl; econstructor; eauto; fail); simpl.
  - specialize (IHwt (HSm c) (evar Γ2 (tshiftTy c T1))).
    isimpl; constructor; eauto.
  - specialize (IHwt c Γ2 H1).
    isimpl; constructor; eauto.
  - specialize (IHwt2 (HSm (HSy c)) (evar (etvar Γ2) (tshiftTy (HSy c) T12))).
    isimpl; econstructor; eauto.
  - rewrite (PTyping_bindPat_dom H).
    specialize (IHwt2 (c + dom Δ) (append Γ2 (tshiftEnv c Δ))
                  (weaken_shift_etvar Δ H0)).
    econstructor; repeat (isimpl; eauto).
Qed.

Lemma shift_evar_ptyping {Γ1 p T Δ} (wp: PTyping Γ1 p T Δ) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → PTyping Γ2 p T Δ.
Proof.
  induction wp; intros; isimpl; econstructor; isimpl; eauto.
Qed.
Hint Resolve shift_evar_ptyping.

Lemma shift_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Typing Γ2 (shiftTm c t) T.
Proof.
  induction wt; intros; try (isimpl; econstructor; eauto; fail).
  - simpl; rewrite (PTyping_bindPat_dom H).
    econstructor; eauto using shift_evar_ptyping.
Qed.

Lemma weaken_typing {Γ} Δ :
  ∀ {t T}, Typing Γ t T →
           Typing (append Γ Δ) (weakenTm t (dom Δ)) (weakenTy T (dom Δ)).
Proof.
  induction Δ; intros; simpl; eauto using shift_evar_typing, shift_etvar_typing.
Qed.

(******************************************************************************)
(* Substitution lemmas                                                        *)
(******************************************************************************)

Inductive subst_etvar : hnat → Ty → Env → Env → Prop :=
  | tse_here {Γ T} :
      wfTy Γ T → subst_etvar HO T (etvar Γ) Γ
  | tse_var {Γ1 Γ2 T' T X} :
      subst_etvar X T' Γ1 Γ2 →
      subst_etvar (HSm X) T' (evar Γ1 T) (evar Γ2 (tsubstTy X T' T))
  | tse_bound {Γ1 Γ2 X T'} :
      subst_etvar X T' Γ1 Γ2 →
      subst_etvar (HSy X) T' (etvar Γ1) (etvar Γ2).
Hint Constructors subst_etvar.

Lemma weaken_subst_etvar {T} (Δ : Env) :
  ∀ {x Γ1 Γ2},
    subst_etvar x T Γ1 Γ2 →
    subst_etvar (x + dom Δ) T (append Γ1 Δ) (append Γ2 (tsubstEnv x T Δ)).
Proof.
  induction Δ; simpl; intros; try constructor; auto.
Qed.
Hint Resolve weaken_subst_etvar.

Lemma subst_etvar_lookup_etvar {X T' Γ1 Γ2} (esub: subst_etvar X T' Γ1 Γ2) :
  ∀ {Y}, lookup_etvar Γ1 Y → wfTy Γ2 (tsubstIndex X T' Y).
Proof.
  induction esub; inversion 1; simpl; eauto.
Qed.

Lemma subst_etvar_wfty {Γ1 T' T} (wT: wfTy Γ1 T) :
  ∀ {X Γ2}, subst_etvar X T' Γ1 Γ2 → wfTy Γ2 (tsubstTy X T' T).
Proof.
  induction wT; simpl; eauto using subst_etvar_lookup_etvar.
Qed.
Hint Resolve subst_etvar_wfty.

Lemma subst_etvar_lookup_evar  {X T' Γ1 Γ2} (esub: subst_etvar X T' Γ1 Γ2) :
  ∀ {x T}, lookup_evar Γ1 x T → lookup_evar Γ2 x (tsubstTy X T' T).
Proof.
  induction esub; inversion 1; isimpl; eauto.
Qed.
Hint Resolve subst_etvar_lookup_evar.

Inductive subst_evar : hnat → Tm → Env → Env → Prop :=
  | se_here {Γ s S} :
      Typing Γ s S → subst_evar HO s (evar Γ S) Γ
  | se_var {Γ1 Γ2 T s x} :
      subst_evar x s Γ1 Γ2 →
      subst_evar (HSm x) s (evar Γ1 T) (evar Γ2 T)
  | se_bound {Γ1 Γ2 x s} :
      subst_evar x s Γ1 Γ2 →
      subst_evar (HSy x) s (etvar Γ1) (etvar Γ2).
Hint Constructors subst_evar.

Lemma weaken_subst_evar {t} (Δ : Env) :
  ∀ {x Γ1 Γ2},
    subst_evar x t Γ1 Γ2 →
    subst_evar (x + dom Δ) t (append Γ1 Δ) (append Γ2 Δ).
Proof.
  induction Δ; simpl; intros; try constructor; auto.
Qed.
Hint Resolve weaken_subst_evar.

Lemma subst_evar_lookup_etvar {x s Γ1 Γ2} (esub: subst_evar x s Γ1 Γ2) :
  ∀ {Y}, lookup_etvar Γ1 Y → lookup_etvar Γ2 Y.
Proof.
  induction esub; inversion 1; simpl; eauto.
Qed.

Lemma subst_evar_wftyp {Γ1 T} (wT: wfTy Γ1 T) :
  ∀ {x s Γ2}, subst_evar x s Γ1 Γ2 → wfTy Γ2 T.
Proof.
  induction wT; simpl; eauto using subst_evar_lookup_etvar.
Qed.
Hint Resolve subst_evar_wftyp.

Lemma subst_etvar_ptyping {S Γ1 p T Δ} (wp: PTyping Γ1 p T Δ) :
  ∀ {X Γ2}, subst_etvar X S Γ1 Γ2 →
    PTyping Γ2 p (tsubstTy X S T) (tsubstEnv X S Δ).
Proof.
  induction wp; intros; isimpl; econstructor; isimpl; eauto.
  specialize (IHwp2 (X + dom Δ1)); isimpl; eauto.
Qed.

Lemma subst_etvar_typing {T' Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {X Γ2}, subst_etvar X T' Γ1 Γ2 →
    Typing Γ2 (tsubstTm X T' t) (tsubstTy X T' T).
Proof.
  induction wt; intros; try (isimpl; econstructor; eauto; fail); simpl.
  - specialize (IHwt (HSm X) (evar Γ2 (tsubstTy X T' T1))).
    isimpl; constructor; eauto.
  - specialize (IHwt X Γ2 H1).
    isimpl; constructor; eauto.
  - specialize (IHwt2 (HSm (HSy X))).
    isimpl; econstructor; eauto.
  - rewrite (PTyping_bindPat_dom H).
    specialize (IHwt2 (X + dom Δ)).
    econstructor; repeat (isimpl; eauto using subst_etvar_ptyping).
Qed.

Lemma subst_evar_lookup_evar {x t Γ1 Γ2} (esub: subst_evar x t Γ1 Γ2) :
  ∀ {y U}, lookup_evar Γ1 y U → Typing Γ2 (substIndex x t y) U.
Proof.
  induction esub; inversion 1; subst; simpl;
    eauto using T_Var, shift_etvar_typing, shift_evar_typing.
Qed.

Lemma subst_evar_ptyping {s Γ1 p T Δ} (wp: PTyping Γ1 p T Δ) :
  ∀ {X Γ2}, subst_evar X s Γ1 Γ2 →
    PTyping Γ2 p T Δ.
Proof.
  induction wp; intros; isimpl; econstructor; isimpl; eauto.
Qed.

Lemma subst_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {x t' Γ2}, subst_evar x t' Γ1 Γ2 → Typing Γ2 (substTm x t' t) T.
Proof.
  induction wt; simpl; eauto using subst_evar_lookup_evar; econstructor;
    try rewrite (PTyping_bindPat_dom H); eauto using subst_evar_ptyping.
Qed.
