Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export Needle.

Local Set Asymmetric Patterns.

Section Namespace.
  Inductive Namespace : Type :=
    | ty .
  Lemma eq_namespace_dec (a : Namespace) (b : Namespace) :
    (sumbool (a = b) (not (a = b))).
  Proof.
    decide equality .
  Defined.
End Namespace.

Section HVarlist.
  Inductive Hvl : Type :=
    | H0 
    | HS (a : Namespace) (k : Hvl).
  
  Fixpoint appendHvl (k : Hvl) (k0 : Hvl) {struct k0} :
  Hvl :=
    match k0 with
      | (H0) => k
      | (HS a k0) => (HS a (appendHvl k k0))
    end.
  
  Lemma appendHvl_assoc  :
    (forall (k : Hvl) (k0 : Hvl) (k1 : Hvl) ,
      ((appendHvl (appendHvl k k0) k1) = (appendHvl k (appendHvl k0 k1)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End HVarlist.

Section Index.
  Inductive Index (a : Namespace) : Type :=
    | I0 
    | IS : (Index a) -> (Index a).
  
  Global Arguments I0 [a] .
  Global Arguments IS [a] _ .
  
  Lemma eq_index_dec {a : Namespace} (i : (Index a)) (j : (Index a)) :
    (sumbool (i = j) (not (i = j))).
  Proof.
    decide equality .
  Qed.
  
  Fixpoint weakenIndexty (X5 : (Index ty)) (k : Hvl) {struct k} :
  (Index ty) :=
    match k with
      | (H0) => X5
      | (HS a k) => match a with
        | (ty) => (IS (weakenIndexty X5 k))
      end
    end.
  Lemma weakenIndexty_append  :
    (forall (X5 : (Index ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexty (weakenIndexty X5 k) k0) = (weakenIndexty X5 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Ty : Set :=
    | tvar (X : (Index ty))
    | tarrow (T1 : Ty) (T2 : Ty)
    | tall (T : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
End Terms.

Section Functions.
  
End Functions.

Section Shift.
  Inductive Cutoff (a : Namespace) : Type :=
    | C0 
    | CS : (Cutoff a) -> (Cutoff a).
  
  Global Arguments C0 {a} .
  Global Arguments CS {a} _ .
  Fixpoint weakenCutoffty (c : (Cutoff ty)) (k : Hvl) {struct k} :
  (Cutoff ty) :=
    match k with
      | (H0) => c
      | (HS a k) => match a with
        | (ty) => (CS (weakenCutoffty c k))
      end
    end.
  
  Lemma weakenCutoffty_append  :
    (forall (c : (Cutoff ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffty (weakenCutoffty c k) k0) = (weakenCutoffty c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint shiftIndex (c : (Cutoff ty)) (X5 : (Index ty)) {struct c} :
  (Index ty) :=
    match c with
      | (C0) => (IS X5)
      | (CS c) => match X5 with
        | (I0) => I0
        | (IS X5) => (IS (shiftIndex c X5))
      end
    end.
  Fixpoint shiftTy (c : (Cutoff ty)) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (tvar X5) => (tvar (shiftIndex c X5))
      | (tarrow T4 T5) => (tarrow (shiftTy c T4) (shiftTy c T5))
      | (tall T6) => (tall (shiftTy (CS c) T6))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S0
      | (HS ty k) => (shiftTy C0 (weakenTy S0 k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T4 : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x
      | (HS b k) => (XS b (weakenTrace x k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x k) k0) = (weakenTrace x (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint substIndex (d : (Trace ty)) (S0 : Ty) (X5 : (Index ty)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X5 with
        | (I0) => S0
        | (IS X5) => (tvar X5)
      end
      | (XS ty d) => match X5 with
        | (I0) => (tvar I0)
        | (IS X5) => (shiftTy C0 (substIndex d S0 X5))
      end
    end.
  Fixpoint substTy (d : (Trace ty)) (S0 : Ty) (S1 : Ty) {struct S1} :
  Ty :=
    match S1 with
      | (tvar X5) => (substIndex d S0 X5)
      | (tarrow T4 T5) => (tarrow (substTy d S0 T4) (substTy d S0 T5))
      | (tall T6) => (tall (substTy (weakenTrace d (HS ty H0)) S0 T6))
    end.
End Subst.

Global Hint Resolve (f_equal (shiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutoffty_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (S0 : Ty) :
    (forall (k : Hvl) (X5 : (Index ty)) ,
      ((substIndex (weakenTrace X0 k) S0 (shiftIndex (weakenCutoffty C0 k) X5)) = (tvar X5))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst0_shift0_Ty_reflection_ind (S1 : Ty) (k : Hvl) (S0 : Ty) {struct S1} :
  ((substTy (weakenTrace X0 k) S0 (shiftTy (weakenCutoffty C0 k) S1)) = S1) :=
    match S1 return ((substTy (weakenTrace X0 k) S0 (shiftTy (weakenCutoffty C0 k) S1)) = S1) with
      | (tvar X5) => (substIndex0_shiftIndex0_reflection_ind S0 k X5)
      | (tarrow T5 T6) => (f_equal2 tarrow (subst0_shift0_Ty_reflection_ind T5 k S0) (subst0_shift0_Ty_reflection_ind T6 k S0))
      | (tall T4) => (f_equal tall (eq_trans (f_equal3 substTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (subst0_shift0_Ty_reflection_ind T4 (HS ty k) S0)))
    end.
  Definition substTy0_shiftTy0_reflection (S1 : Ty) : (forall (S0 : Ty) ,
    ((substTy X0 S0 (shiftTy C0 S1)) = S1)) := (subst0_shift0_Ty_reflection_ind S1 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff ty)) (X5 : (Index ty)) ,
        ((shiftIndex (weakenCutoffty (CS c) k) (shiftIndex (weakenCutoffty C0 k) X5)) = (shiftIndex (weakenCutoffty C0 k) (shiftIndex (weakenCutoffty c k) X5)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint shift_shift0_Ty_comm_ind (S0 : Ty) (k : Hvl) (c : (Cutoff ty)) {struct S0} :
    ((shiftTy (weakenCutoffty (CS c) k) (shiftTy (weakenCutoffty C0 k) S0)) = (shiftTy (weakenCutoffty C0 k) (shiftTy (weakenCutoffty c k) S0))) :=
      match S0 return ((shiftTy (weakenCutoffty (CS c) k) (shiftTy (weakenCutoffty C0 k) S0)) = (shiftTy (weakenCutoffty C0 k) (shiftTy (weakenCutoffty c k) S0))) with
        | (tvar X5) => (f_equal tvar (shiftIndex_shiftIndex0_comm_ind k c X5))
        | (tarrow T5 T6) => (f_equal2 tarrow (shift_shift0_Ty_comm_ind T5 k c) (shift_shift0_Ty_comm_ind T6 k c))
        | (tall T4) => (f_equal tall (shift_shift0_Ty_comm_ind T4 (HS ty k) c))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition shift_shift0_Ty_comm (S0 : Ty) : (forall (c : (Cutoff ty)) ,
      ((shiftTy (CS c) (shiftTy C0 S0)) = (shiftTy C0 (shiftTy c S0)))) := (shift_shift0_Ty_comm_ind S0 H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_shift0_Ty_comm : interaction.
 Hint Rewrite shift_shift0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTy_shiftTy  :
    (forall (k : Hvl) (c : (Cutoff ty)) (S0 : Ty) ,
      ((weakenTy (shiftTy c S0) k) = (shiftTy (weakenCutoffty c k) (weakenTy S0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTy_substIndex0_comm_ind (c : (Cutoff ty)) (S0 : Ty) :
      (forall (k : Hvl) (X5 : (Index ty)) ,
        ((shiftTy (weakenCutoffty c k) (substIndex (weakenTrace X0 k) S0 X5)) = (substIndex (weakenTrace X0 k) (shiftTy c S0) (shiftIndex (weakenCutoffty (CS c) k) X5)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint shift_subst0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c : (Cutoff ty)) (S0 : Ty) {struct S1} :
    ((shiftTy (weakenCutoffty c k) (substTy (weakenTrace X0 k) S0 S1)) = (substTy (weakenTrace X0 k) (shiftTy c S0) (shiftTy (weakenCutoffty (CS c) k) S1))) :=
      match S1 return ((shiftTy (weakenCutoffty c k) (substTy (weakenTrace X0 k) S0 S1)) = (substTy (weakenTrace X0 k) (shiftTy c S0) (shiftTy (weakenCutoffty (CS c) k) S1))) with
        | (tvar X5) => (shiftTy_substIndex0_comm_ind c S0 k X5)
        | (tarrow T5 T6) => (f_equal2 tarrow (shift_subst0_Ty_comm_ind T5 k c S0) (shift_subst0_Ty_comm_ind T6 k c S0))
        | (tall T4) => (f_equal tall (eq_trans (f_equal2 shiftTy eq_refl (f_equal3 substTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Ty_comm_ind T4 (HS ty k) c S0) (f_equal3 substTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shiftTy_substTy0_comm (S1 : Ty) : (forall (c : (Cutoff ty)) (S0 : Ty) ,
      ((shiftTy c (substTy X0 S0 S1)) = (substTy X0 (shiftTy c S0) (shiftTy (CS c) S1)))) := (shift_subst0_Ty_comm_ind S1 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTy0_comm_ind (d : (Trace ty)) (S0 : Ty) :
      (forall (k : Hvl) (X5 : (Index ty)) ,
        ((substIndex (weakenTrace (XS ty d) k) S0 (shiftIndex (weakenCutoffty C0 k) X5)) = (shiftTy (weakenCutoffty C0 k) (substIndex (weakenTrace d k) S0 X5)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_shift0_Ty_comm_ind (S1 : Ty) (k : Hvl) (d : (Trace ty)) (S0 : Ty) {struct S1} :
    ((substTy (weakenTrace (XS ty d) k) S0 (shiftTy (weakenCutoffty C0 k) S1)) = (shiftTy (weakenCutoffty C0 k) (substTy (weakenTrace d k) S0 S1))) :=
      match S1 return ((substTy (weakenTrace (XS ty d) k) S0 (shiftTy (weakenCutoffty C0 k) S1)) = (shiftTy (weakenCutoffty C0 k) (substTy (weakenTrace d k) S0 S1))) with
        | (tvar X5) => (substIndex_shiftTy0_comm_ind d S0 k X5)
        | (tarrow T5 T6) => (f_equal2 tarrow (subst_shift0_Ty_comm_ind T5 k d S0) (subst_shift0_Ty_comm_ind T6 k d S0))
        | (tall T4) => (f_equal tall (eq_trans (f_equal3 substTy (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Ty_comm_ind T4 (HS ty k) d S0) (f_equal2 shiftTy eq_refl (f_equal3 substTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition substTy_shiftTy0_comm (S1 : Ty) : (forall (d : (Trace ty)) (S0 : Ty) ,
      ((substTy (XS ty d) S0 (shiftTy C0 S1)) = (shiftTy C0 (substTy d S0 S1)))) := (subst_shift0_Ty_comm_ind S1 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    
  End SubstSubordInd.
  Section SubstSubord.
    
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite substTy0_shiftTy0_reflection : interaction.
 Hint Rewrite substTy0_shiftTy0_reflection : reflection.
 Hint Rewrite substTy_shiftTy0_comm : interaction.
 Hint Rewrite substTy_shiftTy0_comm : subst_shift0.
 Hint Rewrite shiftTy_substTy0_comm : interaction.
 Hint Rewrite shiftTy_substTy0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTy_substIndex0_commright_ind (d : (Trace ty)) (S0 : Ty) (S1 : Ty) :
      (forall (k : Hvl) (X5 : (Index ty)) ,
        ((substTy (weakenTrace d k) S0 (substIndex (weakenTrace X0 k) S1 X5)) = (substTy (weakenTrace X0 k) (substTy d S0 S1) (substIndex (weakenTrace (XS ty d) k) S0 X5)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_subst0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d : (Trace ty)) (S0 : Ty) (S1 : Ty) {struct S2} :
    ((substTy (weakenTrace d k) S0 (substTy (weakenTrace X0 k) S1 S2)) = (substTy (weakenTrace X0 k) (substTy d S0 S1) (substTy (weakenTrace (XS ty d) k) S0 S2))) :=
      match S2 return ((substTy (weakenTrace d k) S0 (substTy (weakenTrace X0 k) S1 S2)) = (substTy (weakenTrace X0 k) (substTy d S0 S1) (substTy (weakenTrace (XS ty d) k) S0 S2))) with
        | (tvar X5) => (substTy_substIndex0_commright_ind d S0 S1 k X5)
        | (tarrow T5 T6) => (f_equal2 tarrow (subst_subst0_Ty_comm_ind T5 k d S0 S1) (subst_subst0_Ty_comm_ind T6 k d S0 S1))
        | (tall T4) => (f_equal tall (eq_trans (f_equal3 substTy (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 substTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Ty_comm_ind T4 (HS ty k) d S0 S1) (f_equal3 substTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 substTy (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition substTy_substTy0_comm (S2 : Ty) : (forall (d : (Trace ty)) (S0 : Ty) (S1 : Ty) ,
      ((substTy d S0 (substTy X0 S1 S2)) = (substTy X0 (substTy d S0 S1) (substTy (XS ty d) S0 S2)))) := (subst_subst0_Ty_comm_ind S2 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_substTy  :
      (forall (k : Hvl) (d : (Trace ty)) (S0 : Ty) (S1 : Ty) ,
        ((weakenTy (substTy d S0 S1) k) = (substTy (weakenTrace d k) S0 (weakenTy S1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite substTy_substTy0_comm : interaction.
 Hint Rewrite substTy_substTy0_comm : subst_subst0.
 Hint Rewrite weakenTy_shiftTy : weaken_shift.
 Hint Rewrite weakenTy_substTy : weaken_subst.
Section WellFormed.
  Fixpoint wfindex {a : Namespace} (k : Hvl) (i : (Index a)) {struct k} :
  Prop :=
    match k with
      | (H0) => False
      | (HS b k) => match (eq_namespace_dec a b) with
        | (left e) => match i with
          | (I0) => True
          | (IS i) => (wfindex k i)
        end
        | (right n) => (wfindex k i)
      end
    end.
  Inductive wfTy (k : Hvl) : Ty -> Prop :=
    | wfTy_tvar (X5 : (Index ty))
        (wfi : (wfindex k X5)) :
        (wfTy k (tvar X5))
    | wfTy_tarrow {T4 : Ty}
        (wf : (wfTy k T4)) {T5 : Ty}
        (wf0 : (wfTy k T5)) :
        (wfTy k (tarrow T4 T5))
    | wfTy_tall {T6 : Ty}
        (wf : (wfTy (HS ty k) T6)) :
        (wfTy k (tall T6)).
  Definition inversion_wfTy_tvar_1 (k : Hvl) (X : (Index ty)) (H7 : (wfTy k (tvar X))) : (wfindex k X) := match H7 in (wfTy _ S0) return match S0 return Prop with
    | (tvar X) => (wfindex k X)
    | _ => True
  end with
    | (wfTy_tvar X H1) => H1
    | _ => I
  end.
  Definition inversion_wfTy_tarrow_0 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H8 : (wfTy k0 (tarrow T1 T2))) : (wfTy k0 T1) := match H8 in (wfTy _ S1) return match S1 return Prop with
    | (tarrow T1 T2) => (wfTy k0 T1)
    | _ => True
  end with
    | (wfTy_tarrow T1 H2 T2 H3) => H2
    | _ => I
  end.
  Definition inversion_wfTy_tarrow_1 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H8 : (wfTy k0 (tarrow T1 T2))) : (wfTy k0 T2) := match H8 in (wfTy _ S1) return match S1 return Prop with
    | (tarrow T1 T2) => (wfTy k0 T2)
    | _ => True
  end with
    | (wfTy_tarrow T1 H2 T2 H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_tall_1 (k1 : Hvl) (T : Ty) (H9 : (wfTy k1 (tall T))) : (wfTy (HS ty k1) T) := match H9 in (wfTy _ S2) return match S2 return Prop with
    | (tall T) => (wfTy (HS ty k1) T)
    | _ => True
  end with
    | (wfTy_tall T H4) => H4
    | _ => I
  end.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_ty : (forall (c : (Cutoff ty)) (k2 : Hvl) (k3 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k2 : Hvl)
        : (shifthvl_ty C0 k2 (HS ty k2))
    | shifthvl_ty_there_ty
        (c : (Cutoff ty)) (k2 : Hvl)
        (k3 : Hvl) :
        (shifthvl_ty c k2 k3) -> (shifthvl_ty (CS c) (HS ty k2) (HS ty k3)).
  Lemma weaken_shifthvl_ty  :
    (forall (k2 : Hvl) {c : (Cutoff ty)} {k3 : Hvl} {k4 : Hvl} ,
      (shifthvl_ty c k3 k4) -> (shifthvl_ty (weakenCutoffty c k2) (appendHvl k3 k2) (appendHvl k4 k2))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c : (Cutoff ty)) (k2 : Hvl) (k3 : Hvl) (ins : (shifthvl_ty c k2 k3)) (X5 : (Index ty)) ,
      (wfindex k2 X5) -> (wfindex k3 (shiftIndex c X5))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k2 : Hvl) ,
    (forall (S3 : Ty) (wf : (wfTy k2 S3)) ,
      (forall (c : (Cutoff ty)) (k3 : Hvl) ,
        (shifthvl_ty c k2 k3) -> (wfTy k3 (shiftTy c S3))))) := (ind_wfTy (fun (k2 : Hvl) (S3 : Ty) (wf : (wfTy k2 S3)) =>
    (forall (c : (Cutoff ty)) (k3 : Hvl) ,
      (shifthvl_ty c k2 k3) -> (wfTy k3 (shiftTy c S3)))) (fun (k2 : Hvl) (X5 : (Index ty)) (wfi : (wfindex k2 X5)) (c : (Cutoff ty)) (k3 : Hvl) (ins : (shifthvl_ty c k2 k3)) =>
    (wfTy_tvar k3 _ (shift_wfindex_ty c k2 k3 ins X5 wfi))) (fun (k2 : Hvl) (T1 : Ty) (wf : (wfTy k2 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k2 T2)) IHT2 (c : (Cutoff ty)) (k3 : Hvl) (ins : (shifthvl_ty c k2 k3)) =>
    (wfTy_tarrow k3 (IHT1 c k3 (weaken_shifthvl_ty H0 ins)) (IHT2 c k3 (weaken_shifthvl_ty H0 ins)))) (fun (k2 : Hvl) (T : Ty) (wf : (wfTy (HS ty k2) T)) IHT (c : (Cutoff ty)) (k3 : Hvl) (ins : (shifthvl_ty c k2 k3)) =>
    (wfTy_tall k3 (IHT (CS c) (HS ty k3) (weaken_shifthvl_ty (HS ty H0) ins))))).
  Fixpoint weaken_wfTy (k2 : Hvl) {struct k2} :
  (forall (k3 : Hvl) (S3 : Ty) (wf : (wfTy k3 S3)) ,
    (wfTy (appendHvl k3 k2) (weakenTy S3 k2))) :=
    match k2 return (forall (k3 : Hvl) (S3 : Ty) (wf : (wfTy k3 S3)) ,
      (wfTy (appendHvl k3 k2) (weakenTy S3 k2))) with
      | (H0) => (fun (k3 : Hvl) (S3 : Ty) (wf : (wfTy k3 S3)) =>
        wf)
      | (HS ty k2) => (fun (k3 : Hvl) (S3 : Ty) (wf : (wfTy k3 S3)) =>
        (shift_wfTy (appendHvl k3 k2) (weakenTy S3 k2) (weaken_wfTy k2 k3 S3 wf) C0 (HS ty (appendHvl k3 k2)) (shifthvl_ty_here (appendHvl k3 k2))))
    end.
End ShiftWellFormed.
Lemma wfTy_cast  :
  (forall (k2 : Hvl) (S3 : Ty) (k3 : Hvl) (S4 : Ty) ,
    (k2 = k3) -> (S3 = S4) -> (wfTy k2 S3) -> (wfTy k3 S4)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_wfindex_ty : infra.
 Hint Resolve shift_wfindex_ty : shift.
 Hint Resolve shift_wfindex_ty : shift_wf.
 Hint Resolve shift_wfindex_ty : wf.
 Hint Resolve shift_wfTy : infra.
 Hint Resolve shift_wfTy : shift.
 Hint Resolve shift_wfTy : shift_wf.
 Hint Resolve shift_wfTy : wf.
 Hint Constructors shifthvl_ty : infra.
 Hint Constructors shifthvl_ty : shift.
 Hint Constructors shifthvl_ty : shift_wf.
 Hint Constructors shifthvl_ty : wf.
 Hint Resolve weaken_shifthvl_ty : infra.
 Hint Resolve weaken_shifthvl_ty : shift.
 Hint Resolve weaken_shifthvl_ty : shift_wf.
 Hint Resolve weaken_shifthvl_ty : weaken.
 Hint Resolve weaken_shifthvl_ty : wf.
Section SubstWellFormed.
  Inductive substhvl_ty (k2 : Hvl) : (forall (d : (Trace ty)) (k3 : Hvl) (k4 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k2 X0 (HS ty k2) k2)
    | substhvl_ty_there_ty
        {d : (Trace ty)} {k3 : Hvl}
        {k4 : Hvl} :
        (substhvl_ty k2 d k3 k4) -> (substhvl_ty k2 (XS ty d) (HS ty k3) (HS ty k4)).
  Lemma weaken_substhvl_ty  :
    (forall {k3 : Hvl} (k2 : Hvl) {d : (Trace ty)} {k4 : Hvl} {k5 : Hvl} ,
      (substhvl_ty k3 d k4 k5) -> (substhvl_ty k3 (weakenTrace d k2) (appendHvl k4 k2) (appendHvl k5 k2))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k2 : Hvl} {S3 : Ty} (wft : (wfTy k2 S3)) :
    (forall {d : (Trace ty)} {k3 : Hvl} {k4 : Hvl} ,
      (substhvl_ty k2 d k3 k4) -> (forall {X5 : (Index ty)} ,
        (wfindex k3 X5) -> (wfTy k4 (substIndex d S3 X5)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Definition substhvl_ty_wfTy {k2 : Hvl} {S3 : Ty} (wf : (wfTy k2 S3)) : (forall (k3 : Hvl) ,
    (forall (S4 : Ty) (wf0 : (wfTy k3 S4)) ,
      (forall {d : (Trace ty)} {k4 : Hvl} ,
        (substhvl_ty k2 d k3 k4) -> (wfTy k4 (substTy d S3 S4))))) := (ind_wfTy (fun (k3 : Hvl) (S4 : Ty) (wf0 : (wfTy k3 S4)) =>
    (forall {d : (Trace ty)} {k4 : Hvl} ,
      (substhvl_ty k2 d k3 k4) -> (wfTy k4 (substTy d S3 S4)))) (fun (k3 : Hvl) {X5 : (Index ty)} (wfi : (wfindex k3 X5)) {d : (Trace ty)} {k4 : Hvl} (del : (substhvl_ty k2 d k3 k4)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k3 : Hvl) (T1 : Ty) (wf0 : (wfTy k3 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k3 T2)) IHT2 {d : (Trace ty)} {k4 : Hvl} (del : (substhvl_ty k2 d k3 k4)) =>
    (wfTy_tarrow k4 (IHT1 (weakenTrace d H0) k4 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d H0) k4 (weaken_substhvl_ty H0 del)))) (fun (k3 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k3) T)) IHT {d : (Trace ty)} {k4 : Hvl} (del : (substhvl_ty k2 d k3 k4)) =>
    (wfTy_tall k4 (IHT (weakenTrace d (HS ty H0)) (HS ty k4) (weaken_substhvl_ty (HS ty H0) del))))).
End SubstWellFormed.
 Hint Resolve substhvl_ty_wfindex_ty : infra.
 Hint Resolve substhvl_ty_wfindex_ty : subst.
 Hint Resolve substhvl_ty_wfindex_ty : subst_wf.
 Hint Resolve substhvl_ty_wfindex_ty : wf.
 Hint Resolve substhvl_ty_wfTy : infra.
 Hint Resolve substhvl_ty_wfTy : subst.
 Hint Resolve substhvl_ty_wfTy : subst_wf.
 Hint Resolve substhvl_ty_wfTy : wf.
 Hint Constructors substhvl_ty : infra.
 Hint Constructors substhvl_ty : subst.
 Hint Constructors substhvl_ty : subst_wf.
 Hint Constructors substhvl_ty : wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | etvar (G : Env) (T1 : Ty)
        (T2 : Ty).
  Fixpoint appendEnv (G : Env) (G0 : Env) :
  Env :=
    match G0 with
      | (empty) => G
      | (etvar G1 T1 T2) => (etvar (appendEnv G G1) T1 T2)
    end.
  Fixpoint domainEnv (G : Env) :
  Hvl :=
    match G with
      | (empty) => H0
      | (etvar G0 T1 T2) => (HS ty (domainEnv G0))
    end.
  Lemma appendEnv_assoc  :
    (forall (G : Env) (G0 : Env) (G1 : Env) ,
      ((appendEnv G (appendEnv G0 G1)) = (appendEnv (appendEnv G G0) G1))).
  Proof.
    needleGenericAppendEnvAssoc .
  Qed.
  Lemma domainEnv_appendEnv  :
    (forall (G : Env) (G0 : Env) ,
      ((domainEnv (appendEnv G G0)) = (appendHvl (domainEnv G) (domainEnv G0)))).
  Proof.
    needleGenericDomainEnvAppendEnv .
  Qed.
  Fixpoint shiftEnv (c : (Cutoff ty)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (etvar G0 T1 T2) => (etvar (shiftEnv c G0) (shiftTy (weakenCutoffty c (domainEnv G0)) T1) (shiftTy (weakenCutoffty c (domainEnv G0)) T2))
    end.
  Fixpoint weakenEnv (G : Env) (k2 : Hvl) {struct k2} :
  Env :=
    match k2 with
      | (H0) => G
      | (HS ty k2) => (shiftEnv C0 (weakenEnv G k2))
    end.
  Fixpoint substEnv (d : (Trace ty)) (S3 : Ty) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (etvar G0 T1 T2) => (etvar (substEnv d S3 G0) (substTy (weakenTrace d (domainEnv G0)) S3 T1) (substTy (weakenTrace d (domainEnv G0)) S3 T2))
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c : (Cutoff ty)) (G : Env) ,
      ((domainEnv (shiftEnv c G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d : (Trace ty)) (S3 : Ty) (G : Env) ,
      ((domainEnv (substEnv d S3 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shiftEnv_appendEnv  :
      (forall (c : (Cutoff ty)) (G : Env) (G0 : Env) ,
        ((shiftEnv c (appendEnv G G0)) = (appendEnv (shiftEnv c G) (shiftEnv (weakenCutoffty c (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d : (Trace ty)) (S3 : Ty) (G : Env) (G0 : Env) ,
        ((substEnv d S3 (appendEnv G G0)) = (appendEnv (substEnv d S3 G) (substEnv (weakenTrace d (domainEnv G)) S3 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S3 : Ty) (k2 : Hvl) (k3 : Hvl) ,
      ((weakenTy (weakenTy S3 k2) k3) = (weakenTy S3 (appendHvl k2 k3)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_etvar : Env -> (Index ty) -> Ty -> Ty -> Prop :=
      | lookup_etvar_here {G : Env}
          (T4 : Ty) (T5 : Ty) :
          (wfTy (domainEnv G) T4) -> (wfTy (domainEnv G) T5) -> (lookup_etvar (etvar G T4 T5) I0 (shiftTy C0 T4) (shiftTy C0 T5))
      | lookup_etvar_there_etvar
          {G : Env} {X5 : (Index ty)}
          (T6 : Ty) (T7 : Ty) (T8 : Ty)
          (T9 : Ty) :
          (lookup_etvar G X5 T6 T7) -> (lookup_etvar (etvar G T8 T9) (IS X5) (shiftTy C0 T6) (shiftTy C0 T7)).
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Env) (T6 : Ty) (T7 : Ty) (T8 : Ty) (T9 : Ty) ,
        (lookup_etvar (etvar G T6 T7) I0 T8 T9) -> ((shiftTy C0 T6) = T8) /\
        ((shiftTy C0 T7) = T9)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G : Env} {X5 : (Index ty)} ,
        (forall (T6 : Ty) (T7 : Ty) ,
          (lookup_etvar G X5 T6 T7) -> (forall (T8 : Ty) (T9 : Ty) ,
            (lookup_etvar G X5 T8 T9) -> (T6 = T8) /\
            (T7 = T9)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G : Env} {X5 : (Index ty)} (T6 : Ty) (T7 : Ty) ,
        (lookup_etvar G X5 T6 T7) -> (wfTy (domainEnv G) T6) /\
        (wfTy (domainEnv G) T7)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X5 : (Index ty)} (T6 : Ty) (T7 : Ty) ,
        (lookup_etvar G X5 T6 T7) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X5 (domainEnv G0)) (weakenTy T6 (domainEnv G0)) (weakenTy T7 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X5 : (Index ty)} (T10 : Ty) (T11 : Ty) ,
        (lookup_etvar G X5 T10 T11) -> (wfindex (domainEnv G) X5)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G : Env}
        {T6 : Ty} {T7 : Ty} :
        (shift_etvar C0 G (etvar G T6 T7))
    | shiftetvar_there_etvar
        {c : (Cutoff ty)} {G : Env}
        {G0 : Env} {T1 : Ty} {T2 : Ty} :
        (shift_etvar c G G0) -> (shift_etvar (CS c) (etvar G T1 T2) (etvar G0 (shiftTy c T1) (shiftTy c T2))).
  Lemma weaken_shift_etvar  :
    (forall (G : Env) {c : (Cutoff ty)} {G0 : Env} {G1 : Env} ,
      (shift_etvar c G0 G1) -> (shift_etvar (weakenCutoffty c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 (shiftEnv c G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_etvar_shifthvl_ty  :
    (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} ,
      (shift_etvar c G G0) -> (shifthvl_ty c (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_etvar (G : Env) (T6 : Ty) (T7 : Ty) (S3 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G T6 T7 S3 X0 (etvar G T6 T7) G)
    | subst_etvar_there_etvar
        {d : (Trace ty)} {G0 : Env}
        {G1 : Env} (T8 : Ty) (T9 : Ty) :
        (subst_etvar G T6 T7 S3 d G0 G1) -> (subst_etvar G T6 T7 S3 (XS ty d) (etvar G0 T8 T9) (etvar G1 (substTy d S3 T8) (substTy d S3 T9))).
  Lemma weaken_subst_etvar {G : Env} (T6 : Ty) (T7 : Ty) {S3 : Ty} :
    (forall (G0 : Env) {d : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G T6 T7 S3 d G1 G2) -> (subst_etvar G T6 T7 S3 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (substEnv d S3 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S3 : Ty} (T6 : Ty) (T7 : Ty) :
    (forall {d : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G T6 T7 S3 d G0 G1) -> (substhvl_ty (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
End ContextStuff.
 Hint Rewrite domainEnv_shiftEnv : interaction.
 Hint Rewrite domainEnv_shiftEnv : env_domain_shift.
 Hint Rewrite domainEnv_substEnv : interaction.
 Hint Rewrite domainEnv_substEnv : env_domain_subst.
 Hint Rewrite shiftEnv_appendEnv : interaction.
 Hint Rewrite shiftEnv_appendEnv : env_shift_append.
 Hint Rewrite substEnv_appendEnv : interaction.
 Hint Rewrite substEnv_appendEnv : env_shift_append.
 Hint Constructors lookup_etvar : infra.
 Hint Constructors lookup_etvar : lookup.
 Hint Constructors lookup_etvar : shift.
 Hint Constructors lookup_etvar : subst.
 Hint Resolve weaken_lookup_etvar : infra.
 Hint Resolve weaken_lookup_etvar : lookup.
 Hint Resolve weaken_lookup_etvar : shift.
 Hint Resolve weaken_lookup_etvar : weaken.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) {T6 : Ty} (wf : (wfTy (domainEnv G) T6)) {T7 : Ty} (wf0 : (wfTy (domainEnv G) T7)) ,
    (lookup_etvar (appendEnv (etvar G T6 T7) G0) (weakenIndexty I0 (domainEnv G0)) (weakenTy (shiftTy C0 T6) (domainEnv G0)) (weakenTy (shiftTy C0 T7) (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfTy : infra.
 Hint Constructors wfTy : wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H16 : (wfTy _ (tvar _)) |- _ => inversion H16; subst; clear H16
  | H16 : (wfTy _ (tarrow _ _)) |- _ => inversion H16; subst; clear H16
  | H16 : (wfTy _ (tall _)) |- _ => inversion H16; subst; clear H16
end : infra wf.
 Hint Resolve lookup_etvar_wf : infra.
 Hint Resolve lookup_etvar_wf : wf.
 Hint Resolve lookup_etvar_wfindex : infra.
 Hint Resolve lookup_etvar_wfindex : lookup.
 Hint Resolve lookup_etvar_wfindex : wf.
 Hint Constructors shift_etvar : infra.
 Hint Constructors shift_etvar : shift.
 Hint Constructors shift_etvar : subst.
 Hint Resolve weaken_shift_etvar : infra.
 Hint Resolve weaken_shift_etvar : shift.
 Hint Resolve shift_etvar_shifthvl_ty : infra.
 Hint Resolve shift_etvar_shifthvl_ty : shift.
 Hint Resolve shift_etvar_shifthvl_ty : shift_wf.
 Hint Resolve shift_etvar_shifthvl_ty : wf.
 Hint Constructors subst_etvar : infra.
 Hint Constructors subst_etvar : subst.
 Hint Resolve weaken_subst_etvar : infra.
 Hint Resolve weaken_subst_etvar : subst.
 Hint Resolve subst_etvar_substhvl_ty : infra.
 Hint Resolve subst_etvar_substhvl_ty : subst.
 Hint Resolve subst_etvar_substhvl_ty : subst_wf.
 Hint Resolve subst_etvar_substhvl_ty : wf.
 Hint Resolve subst_etvar_substhvl_ty : substenv_substhvl.
Lemma shift_etvar_lookup_etvar  :
  (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {X5 : (Index ty)} {T6 : Ty} {T7 : Ty} ,
    (lookup_etvar G X5 T6 T7) -> (lookup_etvar G0 (shiftIndex c X5) (shiftTy c T6) (shiftTy c T7))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_etvar_lookup_etvar : shift.
Fixpoint size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (tvar X5) => 1
    | (tarrow T4 T5) => (plus 1 (plus (size_Ty T4) (size_Ty T5)))
    | (tall T6) => (plus 1 (size_Ty T6))
  end.
Fixpoint shift_size_Ty (S0 : Ty) (c : (Cutoff ty)) {struct S0} :
((size_Ty (shiftTy c S0)) = (size_Ty S0)) :=
  match S0 return ((size_Ty (shiftTy c S0)) = (size_Ty S0)) with
    | (tvar _) => eq_refl
    | (tarrow T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Ty T1 c) (shift_size_Ty T2 c)))
    | (tall T) => (f_equal2 plus eq_refl (shift_size_Ty T (CS c)))
  end.
 Hint Rewrite shift_size_Ty : interaction.
 Hint Rewrite shift_size_Ty : shift_size.
Lemma weaken_size_Ty  :
  (forall (k : Hvl) (S0 : Ty) ,
    ((size_Ty (weakenTy S0 k)) = (size_Ty S0))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Ty : weaken_size.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutoffty_append weakenTrace_append weakenTy_append appendHvl_assoc : interaction.