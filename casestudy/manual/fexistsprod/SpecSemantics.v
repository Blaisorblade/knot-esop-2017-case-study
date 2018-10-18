Require Export BoilerplateFunctions.
Set Implicit Arguments.

(*************************************************************************)
(* Reduction relation                                                    *)
(*************************************************************************)

Fixpoint Value (t : Tm) : Prop :=
  match t with
    | abs _ _    => True
    | tabs _     => True
    | pack _ t _ => Value t
    | prod x y => Value x ∧ Value y
    | _          => False
  end.

Inductive Match : Pat → Tm → Tm → Tm → Prop :=
  | M_Var {v t} :
      Match pvar v t (substTm HO v t)
  | M_Prod {p1 p2 v1 v2 t t' t''} :
      Match p2 (weakenTm v2 (bindPat p1)) t t' →
      Match p1 v1 t' t'' →
      Match (pprod p1 p2) (prod v1 v2) t t''.

Inductive red : Tm → Tm → Prop :=
  | appabs {T11 t12 t2} :
      Value t2 → red (app (abs T11 t12) t2) (substTm HO t2 t12)
  | tapptabs {T2 t11} :
      red (tapp (tabs t11) T2) (tsubstTm HO T2 t11)
  | unpackpack {T11 v12 T1 t2} :
      Value v12 →
      red (unpack (pack T11 v12 (texist T1)) t2)
          (tsubstTm HO T11 (substTm HO (tshiftTm HO v12) t2))
  | appfun {t1 t1' t2} :
      red t1 t1' → red (app t1 t2) (app t1' t2)
  | apparg {t1 t2 t2'} :
      Value t1 → red t2 t2' → red (app t1 t2) (app t1 t2')
  | typefun {t1 t1' T2} :
      red t1 t1' → red (tapp t1 T2) (tapp t1' T2)
  | E_pack {T11 t12 t12' T1} :
      red t12 t12' → red (pack T11 t12 T1) (pack T11 t12' T1)
  | E_unpack {t1 t1' t2} :
      red t1 t1' → red (unpack t1 t2) (unpack t1' t2)
  | prodl {t1 t1' t2} :
      red t1 t1' → red (prod t1 t2) (prod t1' t2)
  | prodr {t1 t2 t2'} :
      Value t1 → red t2 t2' → red (prod t1 t2) (prod t1 t2')
  | casep {p t1 t1' t2} :
      red t1 t1' → red (case t1 p t2) (case t1' p t2)
  | casev {p t1 t3 t2} :
      Value t1 → Match p t1 t2 t3 → red (case t1 p t2) t3.


(******************************************************************************)
(* Typing relation.                                                           *)
(******************************************************************************)

Inductive PTyping (Γ: Env) : Pat → Ty → Env → Prop :=
  | P_Var {T} (wT: wfTy Γ T) :
      PTyping Γ pvar T (evar empty T)
  | P_Prod {p1 p2 T1 T2 Δ1 Δ2} :
      PTyping Γ p1 T1 Δ1 →
      PTyping (append Γ Δ1) p2 (weakenTy T2 (dom Δ1)) Δ2 →
      PTyping Γ (pprod p1 p2) (tprod T1 T2) (append Δ1 Δ2).

Inductive Typing (Γ: Env) : Tm → Ty → Prop :=
  | T_Var {y T} :
      lookup_evar Γ y T → Typing Γ (var y) T
  | T_Abs {t T1 T2} (wf_T1: wfTy Γ T1) :
      Typing (evar Γ T1) t T2 →
      Typing Γ (abs T1 t) (tarr T1 T2)
  | T_App {t1 t2 T11 T12} :
      Typing Γ t1 (tarr T11 T12) → Typing Γ t2 T11 →
      Typing Γ (app t1 t2) T12
  | T_Tabs {t T} :
      Typing (etvar Γ) t T →  Typing Γ (tabs t) (tall T)
  | T_Tapp {t1 T12 T2} :
      Typing Γ t1 (tall T12) → wfTy Γ T2 →
      Typing Γ (tapp t1 T2) (tsubstTy HO T2 T12)
  | T_Pack {t2 U T2} :
      Typing Γ t2 (tsubstTy HO U T2) →
      wfTy (etvar Γ) T2 → wfTy Γ U →
      Typing Γ (pack U t2 (texist T2)) (texist T2)
  | T_Unpack {t1 T12 t2 T2} :
      Typing Γ t1 (texist T12) →
      Typing (evar (etvar Γ) T12) t2 (tshiftTy HO T2) →
      wfTy Γ T2 →
      Typing Γ (unpack t1 t2) T2
  | T_Prod {t1 T1 t2 T2} :
      Typing Γ t1 T1 → Typing Γ t2 T2 →
      Typing Γ (prod t1 t2) (tprod T1 T2)
  | T_Case {p t1 t2 T1 T2 Δ} :
      Typing Γ t1 T1 → PTyping Γ p T1 Δ →
      Typing (append Γ Δ) t2 (weakenTy T2 (dom Δ)) →
      Typing Γ (case t1 p t2) T2.
