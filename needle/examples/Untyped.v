Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export Needle.

Local Set Asymmetric Patterns.

Section Namespace.
  Inductive Namespace : Type :=
    | tm .
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
  
  Fixpoint weakenIndextm (x3 : (Index tm)) (k : Hvl) {struct k} :
  (Index tm) :=
    match k with
      | (H0) => x3
      | (HS a k) => match a with
        | (tm) => (IS (weakenIndextm x3 k))
      end
    end.
  Lemma weakenIndextm_append  :
    (forall (x3 : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x3 k) k0) = (weakenIndextm x3 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (t : Tm)
    | app (t1 : Tm) (t2 : Tm).
  Scheme ind_Tm := Induction for Tm Sort Prop.
End Terms.

Section Functions.
  
End Functions.

Section Shift.
  Inductive Cutoff (a : Namespace) : Type :=
    | C0 
    | CS : (Cutoff a) -> (Cutoff a).
  
  Global Arguments C0 {a} .
  Global Arguments CS {a} _ .
  Fixpoint weakenCutofftm (c : (Cutoff tm)) (k : Hvl) {struct k} :
  (Cutoff tm) :=
    match k with
      | (H0) => c
      | (HS a k) => match a with
        | (tm) => (CS (weakenCutofftm c k))
      end
    end.
  
  Lemma weakenCutofftm_append  :
    (forall (c : (Cutoff tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutofftm (weakenCutofftm c k) k0) = (weakenCutofftm c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint shiftIndex (c : (Cutoff tm)) (x3 : (Index tm)) {struct c} :
  (Index tm) :=
    match c with
      | (C0) => (IS x3)
      | (CS c) => match x3 with
        | (I0) => I0
        | (IS x3) => (IS (shiftIndex c x3))
      end
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x3) => (var (shiftIndex c x3))
      | (abs t0) => (abs (shiftTm (CS c) t0))
      | (app t3 t4) => (app (shiftTm c t3) (shiftTm c t4))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} :
  Tm :=
    match k with
      | (H0) => s
      | (HS tm k) => (shiftTm C0 (weakenTm s k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x3 : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x3
      | (HS b k) => (XS b (weakenTrace x3 k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x3 : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x3 k) k0) = (weakenTrace x3 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint substIndex (d : (Trace tm)) (s : Tm) (x3 : (Index tm)) {struct d} :
  Tm :=
    match d with
      | (X0) => match x3 with
        | (I0) => s
        | (IS x3) => (var x3)
      end
      | (XS tm d) => match x3 with
        | (I0) => (var I0)
        | (IS x3) => (shiftTm C0 (substIndex d s x3))
      end
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x3) => (substIndex d s x3)
      | (abs t0) => (abs (substTm (weakenTrace d (HS tm H0)) s t0))
      | (app t3 t4) => (app (substTm d s t3) (substTm d s t4))
    end.
End Subst.

Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x3 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k) s (shiftIndex (weakenCutofftm C0 k) x3)) = (var x3))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) with
      | (var x3) => (substIndex0_shiftIndex0_reflection_ind s k x3)
      | (abs t0) => (f_equal abs (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t0 (HS tm k) s)))
      | (app t3 t4) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t3 k s) (subst0_shift0_Tm_reflection_ind t4 k s))
    end.
  Definition substTm0_shiftTm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((substTm X0 s (shiftTm C0 s0)) = s0)) := (subst0_shift0_Tm_reflection_ind s0 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff tm)) (x3 : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c) k) (shiftIndex (weakenCutofftm C0 k) x3)) = (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c k) x3)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x3) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c x3))
        | (abs t0) => (f_equal abs (shift_shift0_Tm_comm_ind t0 (HS tm k) c))
        | (app t3 t4) => (f_equal2 app (shift_shift0_Tm_comm_ind t3 k c) (shift_shift0_Tm_comm_ind t4 k c))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition shift_shift0_Tm_comm (s : Tm) : (forall (c : (Cutoff tm)) ,
      ((shiftTm (CS c) (shiftTm C0 s)) = (shiftTm C0 (shiftTm c s)))) := (shift_shift0_Tm_comm_ind s H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_shift0_Tm_comm : interaction.
 Hint Rewrite shift_shift0_Tm_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTm_shiftTm  :
    (forall (k : Hvl) (c : (Cutoff tm)) (s : Tm) ,
      ((weakenTm (shiftTm c s) k) = (shiftTm (weakenCutofftm c k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTm_substIndex0_comm_ind (c : (Cutoff tm)) (s : Tm) :
      (forall (k : Hvl) (x3 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c k) (substIndex (weakenTrace X0 k) s x3)) = (substIndex (weakenTrace X0 k) (shiftTm c s) (shiftIndex (weakenCutofftm (CS c) k) x3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff tm)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) with
        | (var x3) => (shiftTm_substIndex0_comm_ind c s k x3)
        | (abs t0) => (f_equal abs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t0 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t3 t4) => (f_equal2 app (shift_subst0_Tm_comm_ind t3 k c s) (shift_subst0_Tm_comm_ind t4 k c s))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shiftTm_substTm0_comm (s0 : Tm) : (forall (c : (Cutoff tm)) (s : Tm) ,
      ((shiftTm c (substTm X0 s s0)) = (substTm X0 (shiftTm c s) (shiftTm (CS c) s0)))) := (shift_subst0_Tm_comm_ind s0 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x3 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d) k) s (shiftIndex (weakenCutofftm C0 k) x3)) = (shiftTm (weakenCutofftm C0 k) (substIndex (weakenTrace d k) s x3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x3) => (substIndex_shiftTm0_comm_ind d s k x3)
        | (abs t0) => (f_equal abs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t0 (HS tm k) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t3 t4) => (f_equal2 app (subst_shift0_Tm_comm_ind t3 k d s) (subst_shift0_Tm_comm_ind t4 k d s))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition substTm_shiftTm0_comm (s0 : Tm) : (forall (d : (Trace tm)) (s : Tm) ,
      ((substTm (XS tm d) s (shiftTm C0 s0)) = (shiftTm C0 (substTm d s s0)))) := (subst_shift0_Tm_comm_ind s0 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    
  End SubstSubordInd.
  Section SubstSubord.
    
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite substTm0_shiftTm0_reflection : interaction.
 Hint Rewrite substTm0_shiftTm0_reflection : reflection.
 Hint Rewrite substTm_shiftTm0_comm : interaction.
 Hint Rewrite substTm_shiftTm0_comm : subst_shift0.
 Hint Rewrite shiftTm_substTm0_comm : interaction.
 Hint Rewrite shiftTm_substTm0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d : (Trace tm)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (x3 : (Index tm)) ,
        ((substTm (weakenTrace d k) s (substIndex (weakenTrace X0 k) s0 x3)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substIndex (weakenTrace (XS tm d) k) s x3)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) with
        | (var x3) => (substTm_substIndex0_commright_ind d s s0 k x3)
        | (abs t0) => (f_equal abs (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t0 (HS tm k) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t3 t4) => (f_equal2 app (subst_subst0_Tm_comm_ind t3 k d s s0) (subst_subst0_Tm_comm_ind t4 k d s s0))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition substTm_substTm0_comm (s1 : Tm) : (forall (d : (Trace tm)) (s : Tm) (s0 : Tm) ,
      ((substTm d s (substTm X0 s0 s1)) = (substTm X0 (substTm d s s0) (substTm (XS tm d) s s1)))) := (subst_subst0_Tm_comm_ind s1 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTm_substTm  :
      (forall (k : Hvl) (d : (Trace tm)) (s : Tm) (s0 : Tm) ,
        ((weakenTm (substTm d s s0) k) = (substTm (weakenTrace d k) s (weakenTm s0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite substTm_substTm0_comm : interaction.
 Hint Rewrite substTm_substTm0_comm : subst_subst0.
 Hint Rewrite weakenTm_shiftTm : weaken_shift.
 Hint Rewrite weakenTm_substTm : weaken_subst.
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
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var (x3 : (Index tm))
        (wfi : (wfindex k x3)) :
        (wfTm k (var x3))
    | wfTm_abs {t0 : Tm}
        (wf : (wfTm (HS tm k) t0)) :
        (wfTm k (abs t0))
    | wfTm_app {t3 : Tm}
        (wf : (wfTm k t3)) {t4 : Tm}
        (wf0 : (wfTm k t4)) :
        (wfTm k (app t3 t4)).
  Definition inversion_wfTm_var_1 (k : Hvl) (x : (Index tm)) (H5 : (wfTm k (var x))) : (wfindex k x) := match H5 in (wfTm _ s) return match s return Prop with
    | (var x) => (wfindex k x)
    | _ => True
  end with
    | (wfTm_var x H1) => H1
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k0 : Hvl) (t : Tm) (H6 : (wfTm k0 (abs t))) : (wfTm (HS tm k0) t) := match H6 in (wfTm _ s0) return match s0 return Prop with
    | (abs t) => (wfTm (HS tm k0) t)
    | _ => True
  end with
    | (wfTm_abs t H2) => H2
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k1 : Hvl) (t1 : Tm) (t2 : Tm) (H7 : (wfTm k1 (app t1 t2))) : (wfTm k1 t1) := match H7 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k1 t1)
    | _ => True
  end with
    | (wfTm_app t1 H3 t2 H4) => H3
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k1 : Hvl) (t1 : Tm) (t2 : Tm) (H7 : (wfTm k1 (app t1 t2))) : (wfTm k1 t2) := match H7 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k1 t2)
    | _ => True
  end with
    | (wfTm_app t1 H3 t2 H4) => H4
    | _ => I
  end.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c : (Cutoff tm)) (k2 : Hvl) (k3 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k2 : Hvl)
        : (shifthvl_tm C0 k2 (HS tm k2))
    | shifthvl_tm_there_tm
        (c : (Cutoff tm)) (k2 : Hvl)
        (k3 : Hvl) :
        (shifthvl_tm c k2 k3) -> (shifthvl_tm (CS c) (HS tm k2) (HS tm k3)).
  Lemma weaken_shifthvl_tm  :
    (forall (k2 : Hvl) {c : (Cutoff tm)} {k3 : Hvl} {k4 : Hvl} ,
      (shifthvl_tm c k3 k4) -> (shifthvl_tm (weakenCutofftm c k2) (appendHvl k3 k2) (appendHvl k4 k2))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c : (Cutoff tm)) (k2 : Hvl) (k3 : Hvl) (ins : (shifthvl_tm c k2 k3)) (x3 : (Index tm)) ,
      (wfindex k2 x3) -> (wfindex k3 (shiftIndex c x3))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTm : (forall (k2 : Hvl) ,
    (forall (s2 : Tm) (wf : (wfTm k2 s2)) ,
      (forall (c : (Cutoff tm)) (k3 : Hvl) ,
        (shifthvl_tm c k2 k3) -> (wfTm k3 (shiftTm c s2))))) := (ind_wfTm (fun (k2 : Hvl) (s2 : Tm) (wf : (wfTm k2 s2)) =>
    (forall (c : (Cutoff tm)) (k3 : Hvl) ,
      (shifthvl_tm c k2 k3) -> (wfTm k3 (shiftTm c s2)))) (fun (k2 : Hvl) (x3 : (Index tm)) (wfi : (wfindex k2 x3)) (c : (Cutoff tm)) (k3 : Hvl) (ins : (shifthvl_tm c k2 k3)) =>
    (wfTm_var k3 _ (shift_wfindex_tm c k2 k3 ins x3 wfi))) (fun (k2 : Hvl) (t : Tm) (wf : (wfTm (HS tm k2) t)) IHt (c : (Cutoff tm)) (k3 : Hvl) (ins : (shifthvl_tm c k2 k3)) =>
    (wfTm_abs k3 (IHt (CS c) (HS tm k3) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k2 : Hvl) (t1 : Tm) (wf : (wfTm k2 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k2 t2)) IHt2 (c : (Cutoff tm)) (k3 : Hvl) (ins : (shifthvl_tm c k2 k3)) =>
    (wfTm_app k3 (IHt1 c k3 (weaken_shifthvl_tm H0 ins)) (IHt2 c k3 (weaken_shifthvl_tm H0 ins))))).
  Fixpoint weaken_wfTm (k2 : Hvl) {struct k2} :
  (forall (k3 : Hvl) (s2 : Tm) (wf : (wfTm k3 s2)) ,
    (wfTm (appendHvl k3 k2) (weakenTm s2 k2))) :=
    match k2 return (forall (k3 : Hvl) (s2 : Tm) (wf : (wfTm k3 s2)) ,
      (wfTm (appendHvl k3 k2) (weakenTm s2 k2))) with
      | (H0) => (fun (k3 : Hvl) (s2 : Tm) (wf : (wfTm k3 s2)) =>
        wf)
      | (HS tm k2) => (fun (k3 : Hvl) (s2 : Tm) (wf : (wfTm k3 s2)) =>
        (shift_wfTm (appendHvl k3 k2) (weakenTm s2 k2) (weaken_wfTm k2 k3 s2 wf) C0 (HS tm (appendHvl k3 k2)) (shifthvl_tm_here (appendHvl k3 k2))))
    end.
End ShiftWellFormed.
Lemma wfTm_cast  :
  (forall (k2 : Hvl) (s2 : Tm) (k3 : Hvl) (s3 : Tm) ,
    (k2 = k3) -> (s2 = s3) -> (wfTm k2 s2) -> (wfTm k3 s3)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_wfindex_tm : infra.
 Hint Resolve shift_wfindex_tm : shift.
 Hint Resolve shift_wfindex_tm : shift_wf.
 Hint Resolve shift_wfindex_tm : wf.
 Hint Resolve shift_wfTm : infra.
 Hint Resolve shift_wfTm : shift.
 Hint Resolve shift_wfTm : shift_wf.
 Hint Resolve shift_wfTm : wf.
 Hint Constructors shifthvl_tm : infra.
 Hint Constructors shifthvl_tm : shift.
 Hint Constructors shifthvl_tm : shift_wf.
 Hint Constructors shifthvl_tm : wf.
 Hint Resolve weaken_shifthvl_tm : infra.
 Hint Resolve weaken_shifthvl_tm : shift.
 Hint Resolve weaken_shifthvl_tm : shift_wf.
 Hint Resolve weaken_shifthvl_tm : weaken.
 Hint Resolve weaken_shifthvl_tm : wf.
Section SubstWellFormed.
  Inductive substhvl_tm (k2 : Hvl) : (forall (d : (Trace tm)) (k3 : Hvl) (k4 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k2 X0 (HS tm k2) k2)
    | substhvl_tm_there_tm
        {d : (Trace tm)} {k3 : Hvl}
        {k4 : Hvl} :
        (substhvl_tm k2 d k3 k4) -> (substhvl_tm k2 (XS tm d) (HS tm k3) (HS tm k4)).
  Lemma weaken_substhvl_tm  :
    (forall {k3 : Hvl} (k2 : Hvl) {d : (Trace tm)} {k4 : Hvl} {k5 : Hvl} ,
      (substhvl_tm k3 d k4 k5) -> (substhvl_tm k3 (weakenTrace d k2) (appendHvl k4 k2) (appendHvl k5 k2))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k2 : Hvl} {s2 : Tm} (wft : (wfTm k2 s2)) :
    (forall {d : (Trace tm)} {k3 : Hvl} {k4 : Hvl} ,
      (substhvl_tm k2 d k3 k4) -> (forall {x3 : (Index tm)} ,
        (wfindex k3 x3) -> (wfTm k4 (substIndex d s2 x3)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Definition substhvl_tm_wfTm {k2 : Hvl} {s2 : Tm} (wf : (wfTm k2 s2)) : (forall (k3 : Hvl) ,
    (forall (s3 : Tm) (wf0 : (wfTm k3 s3)) ,
      (forall {d : (Trace tm)} {k4 : Hvl} ,
        (substhvl_tm k2 d k3 k4) -> (wfTm k4 (substTm d s2 s3))))) := (ind_wfTm (fun (k3 : Hvl) (s3 : Tm) (wf0 : (wfTm k3 s3)) =>
    (forall {d : (Trace tm)} {k4 : Hvl} ,
      (substhvl_tm k2 d k3 k4) -> (wfTm k4 (substTm d s2 s3)))) (fun (k3 : Hvl) {x3 : (Index tm)} (wfi : (wfindex k3 x3)) {d : (Trace tm)} {k4 : Hvl} (del : (substhvl_tm k2 d k3 k4)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k3 : Hvl) (t : Tm) (wf0 : (wfTm (HS tm k3) t)) IHt {d : (Trace tm)} {k4 : Hvl} (del : (substhvl_tm k2 d k3 k4)) =>
    (wfTm_abs k4 (IHt (weakenTrace d (HS tm H0)) (HS tm k4) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k3 : Hvl) (t1 : Tm) (wf0 : (wfTm k3 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k3 t2)) IHt2 {d : (Trace tm)} {k4 : Hvl} (del : (substhvl_tm k2 d k3 k4)) =>
    (wfTm_app k4 (IHt1 (weakenTrace d H0) k4 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d H0) k4 (weaken_substhvl_tm H0 del))))).
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm : infra.
 Hint Resolve substhvl_tm_wfindex_tm : subst.
 Hint Resolve substhvl_tm_wfindex_tm : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm : wf.
 Hint Resolve substhvl_tm_wfTm : infra.
 Hint Resolve substhvl_tm_wfTm : subst.
 Hint Resolve substhvl_tm_wfTm : subst_wf.
 Hint Resolve substhvl_tm_wfTm : wf.
 Hint Constructors substhvl_tm : infra.
 Hint Constructors substhvl_tm : subst.
 Hint Constructors substhvl_tm : subst_wf.
 Hint Constructors substhvl_tm : wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | evar (G : Env).
  Fixpoint appendEnv (G : Env) (G0 : Env) :
  Env :=
    match G0 with
      | (empty) => G
      | (evar G1) => (evar (appendEnv G G1))
    end.
  Fixpoint domainEnv (G : Env) :
  Hvl :=
    match G with
      | (empty) => H0
      | (evar G0) => (HS tm (domainEnv G0))
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
  Fixpoint shiftEnv (c : (Cutoff tm)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0) => (evar (shiftEnv c G0))
    end.
  Fixpoint weakenEnv (G : Env) (k2 : Hvl) {struct k2} :
  Env :=
    match k2 with
      | (H0) => G
      | (HS tm k2) => (weakenEnv G k2)
    end.
  Fixpoint substEnv (d : (Trace tm)) (s2 : Tm) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0) => (evar (substEnv d s2 G0))
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c : (Cutoff tm)) (G : Env) ,
      ((domainEnv (shiftEnv c G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d : (Trace tm)) (s2 : Tm) (G : Env) ,
      ((domainEnv (substEnv d s2 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shiftEnv_appendEnv  :
      (forall (c : (Cutoff tm)) (G : Env) (G0 : Env) ,
        ((shiftEnv c (appendEnv G G0)) = (appendEnv (shiftEnv c G) (shiftEnv (weakenCutofftm c (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d : (Trace tm)) (s2 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d s2 (appendEnv G G0)) = (appendEnv (substEnv d s2 G) (substEnv (weakenTrace d (domainEnv G)) s2 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTm_append  :
    (forall (s2 : Tm) (k2 : Hvl) (k3 : Hvl) ,
      ((weakenTm (weakenTm s2 k2) k3) = (weakenTm s2 (appendHvl k2 k3)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Prop :=
      | lookup_evar_here {G : Env} :
          (lookup_evar (evar G) I0)
      | lookup_evar_there_evar
          {G : Env} {x3 : (Index tm)} :
          (lookup_evar G x3) -> (lookup_evar (evar G) (IS x3)).
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x3 : (Index tm)} ,
        (lookup_evar G x3) -> (lookup_evar (appendEnv G G0) (weakenIndextm x3 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x3 : (Index tm)} ,
        (lookup_evar G x3) -> (wfindex (domainEnv G) x3)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env} :
        (shift_evar C0 G (evar G))
    | shiftevar_there_evar
        {c : (Cutoff tm)} {G : Env}
        {G0 : Env} :
        (shift_evar c G G0) -> (shift_evar (CS c) (evar G) (evar G0)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c G0 G1) -> (shift_evar (weakenCutofftm c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_tm  :
    (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} ,
      (shift_evar c G G0) -> (shifthvl_tm c (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Env) (s2 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G s2 X0 (evar G) G)
    | subst_evar_there_evar
        {d : (Trace tm)} {G0 : Env}
        {G1 : Env} :
        (subst_evar G s2 d G0 G1) -> (subst_evar G s2 (XS tm d) (evar G0) (evar G1)).
  Lemma weaken_subst_evar {G : Env} {s2 : Tm} :
    (forall (G0 : Env) {d : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G s2 d G1 G2) -> (subst_evar G s2 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s2 : Tm} :
    (forall {d : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G s2 d G0 G1) -> (substhvl_tm (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
End ContextStuff.
 Hint Constructors lookup_evar : infra.
 Hint Constructors lookup_evar : lookup.
 Hint Constructors lookup_evar : shift.
 Hint Constructors lookup_evar : subst.
 Hint Resolve weaken_lookup_evar : infra.
 Hint Resolve weaken_lookup_evar : lookup.
 Hint Resolve weaken_lookup_evar : shift.
 Hint Resolve weaken_lookup_evar : weaken.
Lemma weaken_lookup_evar_here  :
  (forall {G : Env} (G0 : Env) ,
    (lookup_evar (appendEnv (evar G) G0) (weakenIndextm I0 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfTm : infra.
 Hint Constructors wfTm : wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H8 : (wfTm _ (var _)) |- _ => inversion H8; subst; clear H8
  | H8 : (wfTm _ (abs _)) |- _ => inversion H8; subst; clear H8
  | H8 : (wfTm _ (app _ _)) |- _ => inversion H8; subst; clear H8
end : infra wf.
 Hint Resolve lookup_evar_wfindex : infra.
 Hint Resolve lookup_evar_wfindex : lookup.
 Hint Resolve lookup_evar_wfindex : wf.
 Hint Constructors shift_evar : infra.
 Hint Constructors shift_evar : shift.
 Hint Constructors shift_evar : subst.
 Hint Resolve weaken_shift_evar : infra.
 Hint Resolve weaken_shift_evar : shift.
 Hint Resolve shift_evar_shifthvl_tm : infra.
 Hint Resolve shift_evar_shifthvl_tm : shift.
 Hint Resolve shift_evar_shifthvl_tm : shift_wf.
 Hint Resolve shift_evar_shifthvl_tm : wf.
 Hint Constructors subst_evar : infra.
 Hint Constructors subst_evar : subst.
 Hint Resolve weaken_subst_evar : infra.
 Hint Resolve weaken_subst_evar : subst.
 Hint Resolve subst_evar_substhvl_tm : infra.
 Hint Resolve subst_evar_substhvl_tm : subst.
 Hint Resolve subst_evar_substhvl_tm : subst_wf.
 Hint Resolve subst_evar_substhvl_tm : wf.
 Hint Resolve subst_evar_substhvl_tm : substenv_substhvl.
Lemma shift_evar_lookup_evar  :
  (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {x3 : (Index tm)} ,
    (lookup_evar G x3) -> (lookup_evar G0 (shiftIndex c x3))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar : infra.
 Hint Resolve shift_evar_lookup_evar : lookup.
 Hint Resolve shift_evar_lookup_evar : shift.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x3) => 1
    | (abs t0) => (plus 1 (size_Tm t0))
    | (app t3 t4) => (plus 1 (plus (size_Tm t3) (size_Tm t4)))
  end.
Fixpoint shift_size_Tm (s : Tm) (c : (Cutoff tm)) {struct s} :
((size_Tm (shiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs t) => (f_equal2 plus eq_refl (shift_size_Tm t (CS c)))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 c)))
  end.
 Hint Rewrite shift_size_Tm : interaction.
 Hint Rewrite shift_size_Tm : shift_size.
Lemma weaken_size_Tm  :
  (forall (k : Hvl) (s : Tm) ,
    ((size_Tm (weakenTm s k)) = (size_Tm s))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Tm : interaction.
 Hint Rewrite weaken_size_Tm : weaken_size.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutofftm_append weakenTrace_append weakenTm_append appendHvl_assoc : interaction.