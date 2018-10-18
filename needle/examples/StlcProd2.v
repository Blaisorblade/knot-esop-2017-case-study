Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export Needle.

Local Set Asymmetric Patterns.

Section Namespace.
  Inductive Namespace : Type :=
    | TmVar .
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
  
  Fixpoint weakenIndexTmVar (x6 : (Index TmVar)) (k : Hvl) {struct k} :
  (Index TmVar) :=
    match k with
      | (H0) => x6
      | (HS a k) => match a with
        | (TmVar) => (IS (weakenIndexTmVar x6 k))
      end
    end.
  Lemma weakenIndexTmVar_append  :
    (forall (x6 : (Index TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTmVar (weakenIndexTmVar x6 k) k0) = (weakenIndexTmVar x6 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Ty : Set :=
    | TArr (T1 : Ty) (T2 : Ty)
    | TUnit 
    | TProd (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Pat : Set :=
    | PVar (T : Ty)
    | PProd (p1 : Pat) (p2 : Pat).
  Scheme ind_Pat := Induction for Pat Sort Prop.
  
  Inductive Tm : Set :=
    | Var (x : (Index TmVar))
    | Abs (T : Ty) (t : Tm)
    | App (t1 : Tm) (t2 : Tm)
    | Unit 
    | Prod (t1 : Tm) (t2 : Tm)
    | Case (t1 : Tm) (p : Pat)
        (t2 : Tm).
  Scheme ind_Tm := Induction for Tm Sort Prop.
End Terms.

Section Functions.
  Fixpoint bind (p8 : Pat) {struct p8} :
  Hvl :=
    match p8 with
      | (PVar T) => (HS TmVar H0)
      | (PProd p1 p2) => (appendHvl (appendHvl H0 (bind p1)) (bind p2))
    end.
  Scheme ind_bind_Pat := Induction for Pat Sort Prop.
End Functions.

Section Shift.
  Inductive Cutoff (a : Namespace) : Type :=
    | C0 
    | CS : (Cutoff a) -> (Cutoff a).
  
  Global Arguments C0 {a} .
  Global Arguments CS {a} _ .
  Fixpoint weakenCutoffTmVar (c : (Cutoff TmVar)) (k : Hvl) {struct k} :
  (Cutoff TmVar) :=
    match k with
      | (H0) => c
      | (HS a k) => match a with
        | (TmVar) => (CS (weakenCutoffTmVar c k))
      end
    end.
  
  Lemma weakenCutoffTmVar_append  :
    (forall (c : (Cutoff TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffTmVar (weakenCutoffTmVar c k) k0) = (weakenCutoffTmVar c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint shift_TmVar_Index (c : (Cutoff TmVar)) (x6 : (Index TmVar)) {struct c} :
  (Index TmVar) :=
    match c with
      | (C0) => (IS x6)
      | (CS c) => match x6 with
        | (I0) => I0
        | (IS x6) => (IS (shift_TmVar_Index c x6))
      end
    end.
  Fixpoint shift_TmVar_Tm (c : (Cutoff TmVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x6) => (Var (shift_TmVar_Index c x6))
      | (Abs T7 t6) => (Abs T7 (shift_TmVar_Tm (CS c) t6))
      | (App t7 t8) => (App (shift_TmVar_Tm c t7) (shift_TmVar_Tm c t8))
      | (Unit) => (Unit)
      | (Prod t9 t10) => (Prod (shift_TmVar_Tm c t9) (shift_TmVar_Tm c t10))
      | (Case t11 p9 t12) => (Case (shift_TmVar_Tm c t11) p9 (shift_TmVar_Tm (weakenCutoffTmVar c (appendHvl H0 (bind p9))) t12))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S0
      | (HS TmVar k) => (weakenTy S0 k)
    end.
  Fixpoint weakenPat (p9 : Pat) (k : Hvl) {struct k} :
  Pat :=
    match k with
      | (H0) => p9
      | (HS TmVar k) => (weakenPat p9 k)
    end.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} :
  Tm :=
    match k with
      | (H0) => s
      | (HS TmVar k) => (shift_TmVar_Tm C0 (weakenTm s k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T7 : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x6 : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x6
      | (HS b k) => (XS b (weakenTrace x6 k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x6 : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x6 k) k0) = (weakenTrace x6 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint subst_TmVar_Index (d : (Trace TmVar)) (s : Tm) (x6 : (Index TmVar)) {struct d} :
  Tm :=
    match d with
      | (X0) => match x6 with
        | (I0) => s
        | (IS x6) => (Var x6)
      end
      | (XS TmVar d) => match x6 with
        | (I0) => (Var I0)
        | (IS x6) => (shift_TmVar_Tm C0 (subst_TmVar_Index d s x6))
      end
    end.
  Fixpoint subst_TmVar_Tm (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (Var x6) => (subst_TmVar_Index d s x6)
      | (Abs T7 t6) => (Abs T7 (subst_TmVar_Tm (weakenTrace d (HS TmVar H0)) s t6))
      | (App t7 t8) => (App (subst_TmVar_Tm d s t7) (subst_TmVar_Tm d s t8))
      | (Unit) => (Unit)
      | (Prod t9 t10) => (Prod (subst_TmVar_Tm d s t9) (subst_TmVar_Tm d s t10))
      | (Case t11 p9 t12) => (Case (subst_TmVar_Tm d s t11) p9 (subst_TmVar_Tm (weakenTrace d (appendHvl H0 (bind p9))) s t12))
    end.
End Subst.

Global Hint Resolve (f_equal (shift_TmVar_Tm C0)) : cong_shift0.
 Hint Rewrite weakenCutoffTmVar_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_weaken_bind  :
  (forall (k : Hvl) (p9 : Pat) ,
    ((bind (weakenPat p9 k)) = (bind p9))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bind : interaction.
 Hint Rewrite stability_weaken_bind : stability_weaken.
Section SubstShiftReflection.
  Lemma subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x6 : (Index TmVar)) ,
      ((subst_TmVar_Index (weakenTrace X0 k) s (shift_TmVar_Index (weakenCutoffTmVar C0 k) x6)) = (Var x6))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((subst_TmVar_Tm (weakenTrace X0 k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = s0) :=
    match s0 return ((subst_TmVar_Tm (weakenTrace X0 k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = s0) with
      | (Var x6) => (subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind s k x6)
      | (Abs T7 t6) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t6 (HS TmVar k) s)))
      | (App t7 t8) => (f_equal2 App (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t7 k s) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t8 k s))
      | (Unit) => eq_refl
      | (Prod t7 t8) => (f_equal2 Prod (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t7 k s) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t8 k s))
      | (Case t7 p9 t8) => (f_equal3 Case (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t7 k s) eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p9))) eq_refl (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p9))) eq_refl)) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t8 (appendHvl k (appendHvl H0 (bind p9))) s)))
    end.
  Definition subst_TmVar_Tm0_shift_TmVar_Tm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((subst_TmVar_Tm X0 s (shift_TmVar_Tm C0 s0)) = s0)) := (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind s0 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shift_TmVar_Index_shift_TmVar_Index0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff TmVar)) (x6 : (Index TmVar)) ,
        ((shift_TmVar_Index (weakenCutoffTmVar (CS c) k) (shift_TmVar_Index (weakenCutoffTmVar C0 k) x6)) = (shift_TmVar_Index (weakenCutoffTmVar C0 k) (shift_TmVar_Index (weakenCutoffTmVar c k) x6)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint shift_TmVar__shift_TmVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TmVar)) {struct s} :
    ((shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) :=
      match s return ((shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) with
        | (Var x6) => (f_equal Var (shift_TmVar_Index_shift_TmVar_Index0_comm_ind k c x6))
        | (Abs T7 t6) => (f_equal2 Abs eq_refl (shift_TmVar__shift_TmVar_0_Tm_comm_ind t6 (HS TmVar k) c))
        | (App t7 t8) => (f_equal2 App (shift_TmVar__shift_TmVar_0_Tm_comm_ind t7 k c) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t8 k c))
        | (Unit) => eq_refl
        | (Prod t7 t8) => (f_equal2 Prod (shift_TmVar__shift_TmVar_0_Tm_comm_ind t7 k c) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t8 k c))
        | (Case t7 p9 t8) => (f_equal3 Case (shift_TmVar__shift_TmVar_0_Tm_comm_ind t7 k c) eq_refl (eq_trans (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append (CS c) k (appendHvl H0 (bind p9))) (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p9))) eq_refl)) (eq_trans (shift_TmVar__shift_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind p9))) c) (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p9)))) (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append c k (appendHvl H0 (bind p9)))) eq_refl)))))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition shift_TmVar__shift_TmVar_0_Tm_comm (s : Tm) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Tm (CS c) (shift_TmVar_Tm C0 s)) = (shift_TmVar_Tm C0 (shift_TmVar_Tm c s)))) := (shift_TmVar__shift_TmVar_0_Tm_comm_ind s H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_TmVar__shift_TmVar_0_Tm_comm : interaction.
 Hint Rewrite shift_TmVar__shift_TmVar_0_Tm_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTm_shift_TmVar_Tm  :
    (forall (k : Hvl) (c : (Cutoff TmVar)) (s : Tm) ,
      ((weakenTm (shift_TmVar_Tm c s) k) = (shift_TmVar_Tm (weakenCutoffTmVar c k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shift_TmVar_Tm_subst_TmVar_Index0_comm_ind (c : (Cutoff TmVar)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Index (weakenTrace X0 k) s x6)) = (subst_TmVar_Index (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Index (weakenCutoffTmVar (CS c) k) x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint shift_TmVar__subst_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff TmVar)) (s : Tm) {struct s0} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) s0))) :=
      match s0 return ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) s0))) with
        | (Var x6) => (shift_TmVar_Tm_subst_TmVar_Index0_comm_ind c s k x6)
        | (Abs T7 t6) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind t6 (HS TmVar k) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t7 t8) => (f_equal2 App (shift_TmVar__subst_TmVar_0_Tm_comm_ind t7 k c s) (shift_TmVar__subst_TmVar_0_Tm_comm_ind t8 k c s))
        | (Unit) => eq_refl
        | (Prod t7 t8) => (f_equal2 Prod (shift_TmVar__subst_TmVar_0_Tm_comm_ind t7 k c s) (shift_TmVar__subst_TmVar_0_Tm_comm_ind t8 k c s))
        | (Case t7 p9 t8) => (f_equal3 Case (shift_TmVar__subst_TmVar_0_Tm_comm_ind t7 k c s) eq_refl (eq_trans (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append c k (appendHvl H0 (bind p9))) (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p9))) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind p9))) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p9)))) eq_refl (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append (CS c) k (appendHvl H0 (bind p9)))) eq_refl)))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shift_TmVar_Tm_subst_TmVar_Tm0_comm (s0 : Tm) : (forall (c : (Cutoff TmVar)) (s : Tm) ,
      ((shift_TmVar_Tm c (subst_TmVar_Tm X0 s s0)) = (subst_TmVar_Tm X0 (shift_TmVar_Tm c s) (shift_TmVar_Tm (CS c) s0)))) := (shift_TmVar__subst_TmVar_0_Tm_comm_ind s0 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma subst_TmVar_Index_shift_TmVar_Tm0_comm_ind (d : (Trace TmVar)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TmVar d) k) s (shift_TmVar_Index (weakenCutoffTmVar C0 k) x6)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Index (weakenTrace d k) s x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_TmVar__shift_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) {struct s0} :
    ((subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) :=
      match s0 return ((subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) with
        | (Var x6) => (subst_TmVar_Index_shift_TmVar_Tm0_comm_ind d s k x6)
        | (Abs T7 t6) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind t6 (HS TmVar k) d s) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t7 t8) => (f_equal2 App (subst_TmVar__shift_TmVar_0_Tm_comm_ind t7 k d s) (subst_TmVar__shift_TmVar_0_Tm_comm_ind t8 k d s))
        | (Unit) => eq_refl
        | (Prod t7 t8) => (f_equal2 Prod (subst_TmVar__shift_TmVar_0_Tm_comm_ind t7 k d s) (subst_TmVar__shift_TmVar_0_Tm_comm_ind t8 k d s))
        | (Case t7 p9 t8) => (f_equal3 Case (subst_TmVar__shift_TmVar_0_Tm_comm_ind t7 k d s) eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TmVar d) k (appendHvl H0 (bind p9))) eq_refl (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p9))) eq_refl)) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind p9))) d s) (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p9)))) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (appendHvl H0 (bind p9)))) eq_refl eq_refl)))))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition subst_TmVar_Tm_shift_TmVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) ,
      ((subst_TmVar_Tm (XS TmVar d) s (shift_TmVar_Tm C0 s0)) = (shift_TmVar_Tm C0 (subst_TmVar_Tm d s s0)))) := (subst_TmVar__shift_TmVar_0_Tm_comm_ind s0 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    
  End SubstSubordInd.
  Section SubstSubord.
    
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite subst_TmVar_Tm0_shift_TmVar_Tm0_reflection : interaction.
 Hint Rewrite subst_TmVar_Tm0_shift_TmVar_Tm0_reflection : reflection.
 Hint Rewrite subst_TmVar_Tm_shift_TmVar_Tm0_comm : interaction.
 Hint Rewrite subst_TmVar_Tm_shift_TmVar_Tm0_comm : subst_shift0.
 Hint Rewrite shift_TmVar_Tm_subst_TmVar_Tm0_comm : interaction.
 Hint Rewrite shift_TmVar_Tm_subst_TmVar_Tm0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma subst_TmVar_Tm_subst_TmVar_Index0_commright_ind (d : (Trace TmVar)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Index (weakenTrace X0 k) s0 x6)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Index (weakenTrace (XS TmVar d) k) s x6)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_TmVar__subst_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s1} :
    ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s s1))) :=
      match s1 return ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s s1))) with
        | (Var x6) => (subst_TmVar_Tm_subst_TmVar_Index0_commright_ind d s s0 k x6)
        | (Abs T7 t6) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t6 (HS TmVar k) d s s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t7 t8) => (f_equal2 App (subst_TmVar__subst_TmVar_0_Tm_comm_ind t7 k d s s0) (subst_TmVar__subst_TmVar_0_Tm_comm_ind t8 k d s s0))
        | (Unit) => eq_refl
        | (Prod t7 t8) => (f_equal2 Prod (subst_TmVar__subst_TmVar_0_Tm_comm_ind t7 k d s s0) (subst_TmVar__subst_TmVar_0_Tm_comm_ind t8 k d s s0))
        | (Case t7 p9 t8) => (f_equal3 Case (subst_TmVar__subst_TmVar_0_Tm_comm_ind t7 k d s s0) eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (appendHvl H0 (bind p9))) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p9))) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind p9))) d s s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p9)))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (appendHvl H0 (bind p9)))) eq_refl eq_refl)))))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition subst_TmVar_Tm_subst_TmVar_Tm0_comm (s1 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) (s0 : Tm) ,
      ((subst_TmVar_Tm d s (subst_TmVar_Tm X0 s0 s1)) = (subst_TmVar_Tm X0 (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (XS TmVar d) s s1)))) := (subst_TmVar__subst_TmVar_0_Tm_comm_ind s1 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTm_subst_TmVar_Tm  :
      (forall (k : Hvl) (d : (Trace TmVar)) (s : Tm) (s0 : Tm) ,
        ((weakenTm (subst_TmVar_Tm d s s0) k) = (subst_TmVar_Tm (weakenTrace d k) s (weakenTm s0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite subst_TmVar_Tm_subst_TmVar_Tm0_comm : interaction.
 Hint Rewrite subst_TmVar_Tm_subst_TmVar_Tm0_comm : subst_subst0.
 Hint Rewrite weakenTm_shift_TmVar_Tm : weaken_shift.
 Hint Rewrite weakenTm_subst_TmVar_Tm : weaken_subst.
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
    | wfTy_TArr {T7 : Ty}
        (wf : (wfTy k T7)) {T8 : Ty}
        (wf0 : (wfTy k T8)) :
        (wfTy k (TArr T7 T8))
    | wfTy_TUnit : (wfTy k (TUnit))
    | wfTy_TProd {T9 : Ty}
        (wf : (wfTy k T9)) {T10 : Ty}
        (wf0 : (wfTy k T10)) :
        (wfTy k (TProd T9 T10)).
  Inductive wfPat (k : Hvl) : Pat -> Prop :=
    | wfPat_PVar {T7 : Ty}
        (wf : (wfTy k T7)) :
        (wfPat k (PVar T7))
    | wfPat_PProd {p9 : Pat}
        (wf : (wfPat k p9)) {p10 : Pat}
        (wf0 : (wfPat (appendHvl k (appendHvl H0 (bind p9))) p10))
        : (wfPat k (PProd p9 p10)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_Var
        (x6 : (Index TmVar))
        (wfi : (wfindex k x6)) :
        (wfTm k (Var x6))
    | wfTm_Abs {T7 : Ty}
        (wf : (wfTy k T7)) {t6 : Tm}
        (wf0 : (wfTm (HS TmVar k) t6)) :
        (wfTm k (Abs T7 t6))
    | wfTm_App {t7 : Tm}
        (wf : (wfTm k t7)) {t8 : Tm}
        (wf0 : (wfTm k t8)) :
        (wfTm k (App t7 t8))
    | wfTm_Unit : (wfTm k (Unit))
    | wfTm_Prod {t9 : Tm}
        (wf : (wfTm k t9)) {t10 : Tm}
        (wf0 : (wfTm k t10)) :
        (wfTm k (Prod t9 t10))
    | wfTm_Case {t11 : Tm}
        (wf : (wfTm k t11)) {p9 : Pat}
        (wf0 : (wfPat k p9)) {t12 : Tm}
        (wf1 : (wfTm (appendHvl k (appendHvl H0 (bind p9))) t12))
        : (wfTm k (Case t11 p9 t12)).
  Definition inversion_wfTy_TArr_0 (k : Hvl) (T1 : Ty) (T2 : Ty) (H19 : (wfTy k (TArr T1 T2))) : (wfTy k T1) := match H19 in (wfTy _ S0) return match S0 return Prop with
    | (TArr T1 T2) => (wfTy k T1)
    | _ => True
  end with
    | (wfTy_TArr T1 H1 T2 H2) => H1
    | _ => I
  end.
  Definition inversion_wfTy_TArr_1 (k : Hvl) (T1 : Ty) (T2 : Ty) (H19 : (wfTy k (TArr T1 T2))) : (wfTy k T2) := match H19 in (wfTy _ S0) return match S0 return Prop with
    | (TArr T1 T2) => (wfTy k T2)
    | _ => True
  end with
    | (wfTy_TArr T1 H1 T2 H2) => H2
    | _ => I
  end.
  Definition inversion_wfTy_TProd_0 (k1 : Hvl) (T1 : Ty) (T2 : Ty) (H21 : (wfTy k1 (TProd T1 T2))) : (wfTy k1 T1) := match H21 in (wfTy _ S2) return match S2 return Prop with
    | (TProd T1 T2) => (wfTy k1 T1)
    | _ => True
  end with
    | (wfTy_TProd T1 H3 T2 H4) => H3
    | _ => I
  end.
  Definition inversion_wfTy_TProd_1 (k1 : Hvl) (T1 : Ty) (T2 : Ty) (H21 : (wfTy k1 (TProd T1 T2))) : (wfTy k1 T2) := match H21 in (wfTy _ S2) return match S2 return Prop with
    | (TProd T1 T2) => (wfTy k1 T2)
    | _ => True
  end with
    | (wfTy_TProd T1 H3 T2 H4) => H4
    | _ => I
  end.
  Definition inversion_wfPat_PVar_1 (k2 : Hvl) (T : Ty) (H22 : (wfPat k2 (PVar T))) : (wfTy k2 T) := match H22 in (wfPat _ p9) return match p9 return Prop with
    | (PVar T) => (wfTy k2 T)
    | _ => True
  end with
    | (wfPat_PVar T H5) => H5
    | _ => I
  end.
  Definition inversion_wfPat_PProd_0 (k3 : Hvl) (p1 : Pat) (p2 : Pat) (H23 : (wfPat k3 (PProd p1 p2))) : (wfPat k3 p1) := match H23 in (wfPat _ p10) return match p10 return Prop with
    | (PProd p1 p2) => (wfPat k3 p1)
    | _ => True
  end with
    | (wfPat_PProd p1 H6 p2 H7) => H6
    | _ => I
  end.
  Definition inversion_wfPat_PProd_1 (k3 : Hvl) (p1 : Pat) (p2 : Pat) (H23 : (wfPat k3 (PProd p1 p2))) : (wfPat (appendHvl k3 (appendHvl H0 (bind p1))) p2) := match H23 in (wfPat _ p10) return match p10 return Prop with
    | (PProd p1 p2) => (wfPat (appendHvl k3 (appendHvl H0 (bind p1))) p2)
    | _ => True
  end with
    | (wfPat_PProd p1 H6 p2 H7) => H7
    | _ => I
  end.
  Definition inversion_wfTm_Var_1 (k4 : Hvl) (x : (Index TmVar)) (H24 : (wfTm k4 (Var x))) : (wfindex k4 x) := match H24 in (wfTm _ s) return match s return Prop with
    | (Var x) => (wfindex k4 x)
    | _ => True
  end with
    | (wfTm_Var x H8) => H8
    | _ => I
  end.
  Definition inversion_wfTm_Abs_1 (k5 : Hvl) (T : Ty) (t : Tm) (H25 : (wfTm k5 (Abs T t))) : (wfTy k5 T) := match H25 in (wfTm _ s0) return match s0 return Prop with
    | (Abs T t) => (wfTy k5 T)
    | _ => True
  end with
    | (wfTm_Abs T H9 t H10) => H9
    | _ => I
  end.
  Definition inversion_wfTm_Abs_2 (k5 : Hvl) (T : Ty) (t : Tm) (H25 : (wfTm k5 (Abs T t))) : (wfTm (HS TmVar k5) t) := match H25 in (wfTm _ s0) return match s0 return Prop with
    | (Abs T t) => (wfTm (HS TmVar k5) t)
    | _ => True
  end with
    | (wfTm_Abs T H9 t H10) => H10
    | _ => I
  end.
  Definition inversion_wfTm_App_0 (k6 : Hvl) (t1 : Tm) (t2 : Tm) (H26 : (wfTm k6 (App t1 t2))) : (wfTm k6 t1) := match H26 in (wfTm _ s1) return match s1 return Prop with
    | (App t1 t2) => (wfTm k6 t1)
    | _ => True
  end with
    | (wfTm_App t1 H11 t2 H12) => H11
    | _ => I
  end.
  Definition inversion_wfTm_App_1 (k6 : Hvl) (t1 : Tm) (t2 : Tm) (H26 : (wfTm k6 (App t1 t2))) : (wfTm k6 t2) := match H26 in (wfTm _ s1) return match s1 return Prop with
    | (App t1 t2) => (wfTm k6 t2)
    | _ => True
  end with
    | (wfTm_App t1 H11 t2 H12) => H12
    | _ => I
  end.
  Definition inversion_wfTm_Prod_0 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H28 : (wfTm k8 (Prod t1 t2))) : (wfTm k8 t1) := match H28 in (wfTm _ s3) return match s3 return Prop with
    | (Prod t1 t2) => (wfTm k8 t1)
    | _ => True
  end with
    | (wfTm_Prod t1 H13 t2 H14) => H13
    | _ => I
  end.
  Definition inversion_wfTm_Prod_1 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H28 : (wfTm k8 (Prod t1 t2))) : (wfTm k8 t2) := match H28 in (wfTm _ s3) return match s3 return Prop with
    | (Prod t1 t2) => (wfTm k8 t2)
    | _ => True
  end with
    | (wfTm_Prod t1 H13 t2 H14) => H14
    | _ => I
  end.
  Definition inversion_wfTm_Case_0 (k9 : Hvl) (t1 : Tm) (p : Pat) (t2 : Tm) (H29 : (wfTm k9 (Case t1 p t2))) : (wfTm k9 t1) := match H29 in (wfTm _ s4) return match s4 return Prop with
    | (Case t1 p t2) => (wfTm k9 t1)
    | _ => True
  end with
    | (wfTm_Case t1 H15 p H16 t2 H17) => H15
    | _ => I
  end.
  Definition inversion_wfTm_Case_1 (k9 : Hvl) (t1 : Tm) (p : Pat) (t2 : Tm) (H29 : (wfTm k9 (Case t1 p t2))) : (wfPat k9 p) := match H29 in (wfTm _ s4) return match s4 return Prop with
    | (Case t1 p t2) => (wfPat k9 p)
    | _ => True
  end with
    | (wfTm_Case t1 H15 p H16 t2 H17) => H16
    | _ => I
  end.
  Definition inversion_wfTm_Case_2 (k9 : Hvl) (t1 : Tm) (p : Pat) (t2 : Tm) (H29 : (wfTm k9 (Case t1 p t2))) : (wfTm (appendHvl k9 (appendHvl H0 (bind p))) t2) := match H29 in (wfTm _ s4) return match s4 return Prop with
    | (Case t1 p t2) => (wfTm (appendHvl k9 (appendHvl H0 (bind p))) t2)
    | _ => True
  end with
    | (wfTm_Case t1 H15 p H16 t2 H17) => H17
    | _ => I
  end.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfPat := Induction for wfPat Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_TmVar : (forall (c : (Cutoff TmVar)) (k10 : Hvl) (k11 : Hvl) ,
    Prop) :=
    | shifthvl_TmVar_here
        (k10 : Hvl) :
        (shifthvl_TmVar C0 k10 (HS TmVar k10))
    | shifthvl_TmVar_there_TmVar
        (c : (Cutoff TmVar)) (k10 : Hvl)
        (k11 : Hvl) :
        (shifthvl_TmVar c k10 k11) -> (shifthvl_TmVar (CS c) (HS TmVar k10) (HS TmVar k11)).
  Lemma weaken_shifthvl_TmVar  :
    (forall (k10 : Hvl) {c : (Cutoff TmVar)} {k11 : Hvl} {k12 : Hvl} ,
      (shifthvl_TmVar c k11 k12) -> (shifthvl_TmVar (weakenCutoffTmVar c k10) (appendHvl k11 k10) (appendHvl k12 k10))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_TmVar__wfindex_TmVar  :
    (forall (c : (Cutoff TmVar)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) (x6 : (Index TmVar)) ,
      (wfindex k10 x6) -> (wfindex k11 (shift_TmVar_Index c x6))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_TmVar__wfTy : (forall (k10 : Hvl) ,
    (forall (S3 : Ty) (wf : (wfTy k10 S3)) ,
      (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
        (shifthvl_TmVar c k10 k11) -> (wfTy k11 S3)))) := (fun (k10 : Hvl) =>
    (ind_wfTy k10 (fun (S3 : Ty) (wf : (wfTy k10 S3)) =>
      (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
        (shifthvl_TmVar c k10 k11) -> (wfTy k11 S3))) (fun (T1 : Ty) (wf : (wfTy k10 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k10 T2)) IHT2 (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
      (wfTy_TArr k11 (IHT1 c k11 (weaken_shifthvl_TmVar H0 ins)) (IHT2 c k11 (weaken_shifthvl_TmVar H0 ins)))) (fun (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
      (wfTy_TUnit k11)) (fun (T1 : Ty) (wf : (wfTy k10 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k10 T2)) IHT2 (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
      (wfTy_TProd k11 (IHT1 c k11 (weaken_shifthvl_TmVar H0 ins)) (IHT2 c k11 (weaken_shifthvl_TmVar H0 ins)))))).
  Definition shift_TmVar__wfPat : (forall (k10 : Hvl) ,
    (forall (p11 : Pat) (wf : (wfPat k10 p11)) ,
      (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
        (shifthvl_TmVar c k10 k11) -> (wfPat k11 p11)))) := (ind_wfPat (fun (k10 : Hvl) (p11 : Pat) (wf : (wfPat k10 p11)) =>
    (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
      (shifthvl_TmVar c k10 k11) -> (wfPat k11 p11))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfPat_PVar k11 (shift_TmVar__wfTy k10 T wf c k11 (weaken_shifthvl_TmVar H0 ins)))) (fun (k10 : Hvl) (p1 : Pat) (wf : (wfPat k10 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k10 (appendHvl H0 (bind p1))) p2)) IHp2 (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfPat_PProd k11 (IHp1 c k11 (weaken_shifthvl_TmVar H0 ins)) (IHp2 (weakenCutoffTmVar c (appendHvl H0 (bind p1))) (appendHvl k11 (appendHvl H0 (bind p1))) (weaken_shifthvl_TmVar (appendHvl H0 (bind p1)) ins))))).
  Definition shift_TmVar__wfTm : (forall (k10 : Hvl) ,
    (forall (s5 : Tm) (wf : (wfTm k10 s5)) ,
      (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
        (shifthvl_TmVar c k10 k11) -> (wfTm k11 (shift_TmVar_Tm c s5))))) := (ind_wfTm (fun (k10 : Hvl) (s5 : Tm) (wf : (wfTm k10 s5)) =>
    (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
      (shifthvl_TmVar c k10 k11) -> (wfTm k11 (shift_TmVar_Tm c s5)))) (fun (k10 : Hvl) (x6 : (Index TmVar)) (wfi : (wfindex k10 x6)) (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTm_Var k11 _ (shift_TmVar__wfindex_TmVar c k10 k11 ins x6 wfi))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) (t : Tm) (wf0 : (wfTm (HS TmVar k10) t)) IHt (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTm_Abs k11 (shift_TmVar__wfTy k10 T wf c k11 (weaken_shifthvl_TmVar H0 ins)) (IHt (CS c) (HS TmVar k11) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k10 t2)) IHt2 (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTm_App k11 (IHt1 c k11 (weaken_shifthvl_TmVar H0 ins)) (IHt2 c k11 (weaken_shifthvl_TmVar H0 ins)))) (fun (k10 : Hvl) (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTm_Unit k11)) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k10 t2)) IHt2 (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTm_Prod k11 (IHt1 c k11 (weaken_shifthvl_TmVar H0 ins)) (IHt2 c k11 (weaken_shifthvl_TmVar H0 ins)))) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (p : Pat) (wf0 : (wfPat k10 p)) (t2 : Tm) (wf1 : (wfTm (appendHvl k10 (appendHvl H0 (bind p))) t2)) IHt2 (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTm_Case k11 (IHt1 c k11 (weaken_shifthvl_TmVar H0 ins)) (shift_TmVar__wfPat k10 p wf0 c k11 (weaken_shifthvl_TmVar H0 ins)) (IHt2 (weakenCutoffTmVar c (appendHvl H0 (bind p))) (appendHvl k11 (appendHvl H0 (bind p))) (weaken_shifthvl_TmVar (appendHvl H0 (bind p)) ins))))).
  Fixpoint weaken_wfTy (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (S3 : Ty) (wf : (wfTy k11 S3)) ,
    (wfTy (appendHvl k11 k10) (weakenTy S3 k10))) :=
    match k10 return (forall (k11 : Hvl) (S3 : Ty) (wf : (wfTy k11 S3)) ,
      (wfTy (appendHvl k11 k10) (weakenTy S3 k10))) with
      | (H0) => (fun (k11 : Hvl) (S3 : Ty) (wf : (wfTy k11 S3)) =>
        wf)
      | (HS TmVar k10) => (fun (k11 : Hvl) (S3 : Ty) (wf : (wfTy k11 S3)) =>
        (shift_TmVar__wfTy (appendHvl k11 k10) (weakenTy S3 k10) (weaken_wfTy k10 k11 S3 wf) C0 (HS TmVar (appendHvl k11 k10)) (shifthvl_TmVar_here (appendHvl k11 k10))))
    end.
  Fixpoint weaken_wfPat (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (p11 : Pat) (wf : (wfPat k11 p11)) ,
    (wfPat (appendHvl k11 k10) (weakenPat p11 k10))) :=
    match k10 return (forall (k11 : Hvl) (p11 : Pat) (wf : (wfPat k11 p11)) ,
      (wfPat (appendHvl k11 k10) (weakenPat p11 k10))) with
      | (H0) => (fun (k11 : Hvl) (p11 : Pat) (wf : (wfPat k11 p11)) =>
        wf)
      | (HS TmVar k10) => (fun (k11 : Hvl) (p11 : Pat) (wf : (wfPat k11 p11)) =>
        (shift_TmVar__wfPat (appendHvl k11 k10) (weakenPat p11 k10) (weaken_wfPat k10 k11 p11 wf) C0 (HS TmVar (appendHvl k11 k10)) (shifthvl_TmVar_here (appendHvl k11 k10))))
    end.
  Fixpoint weaken_wfTm (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (s5 : Tm) (wf : (wfTm k11 s5)) ,
    (wfTm (appendHvl k11 k10) (weakenTm s5 k10))) :=
    match k10 return (forall (k11 : Hvl) (s5 : Tm) (wf : (wfTm k11 s5)) ,
      (wfTm (appendHvl k11 k10) (weakenTm s5 k10))) with
      | (H0) => (fun (k11 : Hvl) (s5 : Tm) (wf : (wfTm k11 s5)) =>
        wf)
      | (HS TmVar k10) => (fun (k11 : Hvl) (s5 : Tm) (wf : (wfTm k11 s5)) =>
        (shift_TmVar__wfTm (appendHvl k11 k10) (weakenTm s5 k10) (weaken_wfTm k10 k11 s5 wf) C0 (HS TmVar (appendHvl k11 k10)) (shifthvl_TmVar_here (appendHvl k11 k10))))
    end.
End ShiftWellFormed.
Lemma wfTy_cast  :
  (forall (k14 : Hvl) (S4 : Ty) (k15 : Hvl) (S5 : Ty) ,
    (k14 = k15) -> (S4 = S5) -> (wfTy k14 S4) -> (wfTy k15 S5)).
Proof.
  congruence .
Qed.
Lemma wfPat_cast  :
  (forall (k14 : Hvl) (p12 : Pat) (k15 : Hvl) (p13 : Pat) ,
    (k14 = k15) -> (p12 = p13) -> (wfPat k14 p12) -> (wfPat k15 p13)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k14 : Hvl) (s5 : Tm) (k15 : Hvl) (s6 : Tm) ,
    (k14 = k15) -> (s5 = s6) -> (wfTm k14 s5) -> (wfTm k15 s6)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_TmVar__wfindex_TmVar : infra.
 Hint Resolve shift_TmVar__wfindex_TmVar : shift.
 Hint Resolve shift_TmVar__wfindex_TmVar : shift_wf.
 Hint Resolve shift_TmVar__wfindex_TmVar : wf.
 Hint Resolve shift_TmVar__wfPat shift_TmVar__wfTm shift_TmVar__wfTy : infra.
 Hint Resolve shift_TmVar__wfPat shift_TmVar__wfTm shift_TmVar__wfTy : shift.
 Hint Resolve shift_TmVar__wfPat shift_TmVar__wfTm shift_TmVar__wfTy : shift_wf.
 Hint Resolve shift_TmVar__wfPat shift_TmVar__wfTm shift_TmVar__wfTy : wf.
 Hint Constructors shifthvl_TmVar : infra.
 Hint Constructors shifthvl_TmVar : shift.
 Hint Constructors shifthvl_TmVar : shift_wf.
 Hint Constructors shifthvl_TmVar : wf.
 Hint Resolve weaken_shifthvl_TmVar : infra.
 Hint Resolve weaken_shifthvl_TmVar : shift.
 Hint Resolve weaken_shifthvl_TmVar : shift_wf.
 Hint Resolve weaken_shifthvl_TmVar : weaken.
 Hint Resolve weaken_shifthvl_TmVar : wf.
Section SubstWellFormed.
  Inductive substhvl_TmVar (k10 : Hvl) : (forall (d : (Trace TmVar)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | substhvl_TmVar_here :
        (substhvl_TmVar k10 X0 (HS TmVar k10) k10)
    | substhvl_TmVar_there_TmVar
        {d : (Trace TmVar)} {k11 : Hvl}
        {k12 : Hvl} :
        (substhvl_TmVar k10 d k11 k12) -> (substhvl_TmVar k10 (XS TmVar d) (HS TmVar k11) (HS TmVar k12)).
  Lemma weaken_substhvl_TmVar  :
    (forall {k11 : Hvl} (k10 : Hvl) {d : (Trace TmVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TmVar k11 d k12 k13) -> (substhvl_TmVar k11 (weakenTrace d k10) (appendHvl k12 k10) (appendHvl k13 k10))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_TmVar_wfindex_TmVar {k14 : Hvl} {s5 : Tm} (wft : (wfTm k14 s5)) :
    (forall {d : (Trace TmVar)} {k15 : Hvl} {k16 : Hvl} ,
      (substhvl_TmVar k14 d k15 k16) -> (forall {x6 : (Index TmVar)} ,
        (wfindex k15 x6) -> (wfTm k16 (subst_TmVar_Index d s5 x6)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Definition substhvl_TmVar_wfTy {k14 : Hvl} : (forall (k15 : Hvl) ,
    (forall (S4 : Ty) (wf0 : (wfTy k15 S4)) ,
      (forall {d : (Trace TmVar)} {k16 : Hvl} ,
        (substhvl_TmVar k14 d k15 k16) -> (wfTy k16 S4)))) := (fun (k15 : Hvl) =>
    (ind_wfTy k15 (fun (S4 : Ty) (wf0 : (wfTy k15 S4)) =>
      (forall {d : (Trace TmVar)} {k16 : Hvl} ,
        (substhvl_TmVar k14 d k15 k16) -> (wfTy k16 S4))) (fun (T1 : Ty) (wf0 : (wfTy k15 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k15 T2)) IHT2 {d : (Trace TmVar)} {k16 : Hvl} (del : (substhvl_TmVar k14 d k15 k16)) =>
      (wfTy_TArr k16 (IHT1 (weakenTrace d H0) k16 (weaken_substhvl_TmVar H0 del)) (IHT2 (weakenTrace d H0) k16 (weaken_substhvl_TmVar H0 del)))) (fun {d : (Trace TmVar)} {k16 : Hvl} (del : (substhvl_TmVar k14 d k15 k16)) =>
      (wfTy_TUnit k16)) (fun (T1 : Ty) (wf0 : (wfTy k15 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k15 T2)) IHT2 {d : (Trace TmVar)} {k16 : Hvl} (del : (substhvl_TmVar k14 d k15 k16)) =>
      (wfTy_TProd k16 (IHT1 (weakenTrace d H0) k16 (weaken_substhvl_TmVar H0 del)) (IHT2 (weakenTrace d H0) k16 (weaken_substhvl_TmVar H0 del)))))).
  Definition substhvl_TmVar_wfPat {k14 : Hvl} : (forall (k15 : Hvl) ,
    (forall (p12 : Pat) (wf0 : (wfPat k15 p12)) ,
      (forall {d : (Trace TmVar)} {k16 : Hvl} ,
        (substhvl_TmVar k14 d k15 k16) -> (wfPat k16 p12)))) := (ind_wfPat (fun (k15 : Hvl) (p12 : Pat) (wf0 : (wfPat k15 p12)) =>
    (forall {d : (Trace TmVar)} {k16 : Hvl} ,
      (substhvl_TmVar k14 d k15 k16) -> (wfPat k16 p12))) (fun (k15 : Hvl) (T : Ty) (wf0 : (wfTy k15 T)) {d : (Trace TmVar)} {k16 : Hvl} (del : (substhvl_TmVar k14 d k15 k16)) =>
    (wfPat_PVar k16 (substhvl_TmVar_wfTy k15 T wf0 (weaken_substhvl_TmVar H0 del)))) (fun (k15 : Hvl) (p1 : Pat) (wf0 : (wfPat k15 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k15 (appendHvl H0 (bind p1))) p2)) IHp2 {d : (Trace TmVar)} {k16 : Hvl} (del : (substhvl_TmVar k14 d k15 k16)) =>
    (wfPat_PProd k16 (IHp1 (weakenTrace d H0) k16 (weaken_substhvl_TmVar H0 del)) (IHp2 (weakenTrace d (appendHvl H0 (bind p1))) (appendHvl k16 (appendHvl H0 (bind p1))) (weaken_substhvl_TmVar (appendHvl H0 (bind p1)) del))))).
  Definition substhvl_TmVar_wfTm {k14 : Hvl} {s5 : Tm} (wf : (wfTm k14 s5)) : (forall (k15 : Hvl) ,
    (forall (s6 : Tm) (wf0 : (wfTm k15 s6)) ,
      (forall {d : (Trace TmVar)} {k16 : Hvl} ,
        (substhvl_TmVar k14 d k15 k16) -> (wfTm k16 (subst_TmVar_Tm d s5 s6))))) := (ind_wfTm (fun (k15 : Hvl) (s6 : Tm) (wf0 : (wfTm k15 s6)) =>
    (forall {d : (Trace TmVar)} {k16 : Hvl} ,
      (substhvl_TmVar k14 d k15 k16) -> (wfTm k16 (subst_TmVar_Tm d s5 s6)))) (fun (k15 : Hvl) {x6 : (Index TmVar)} (wfi : (wfindex k15 x6)) {d : (Trace TmVar)} {k16 : Hvl} (del : (substhvl_TmVar k14 d k15 k16)) =>
    (substhvl_TmVar_wfindex_TmVar wf del wfi)) (fun (k15 : Hvl) (T : Ty) (wf0 : (wfTy k15 T)) (t : Tm) (wf1 : (wfTm (HS TmVar k15) t)) IHt {d : (Trace TmVar)} {k16 : Hvl} (del : (substhvl_TmVar k14 d k15 k16)) =>
    (wfTm_Abs k16 (substhvl_TmVar_wfTy k15 T wf0 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d (HS TmVar H0)) (HS TmVar k16) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k15 : Hvl) (t1 : Tm) (wf0 : (wfTm k15 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k15 t2)) IHt2 {d : (Trace TmVar)} {k16 : Hvl} (del : (substhvl_TmVar k14 d k15 k16)) =>
    (wfTm_App k16 (IHt1 (weakenTrace d H0) k16 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d H0) k16 (weaken_substhvl_TmVar H0 del)))) (fun (k15 : Hvl) {d : (Trace TmVar)} {k16 : Hvl} (del : (substhvl_TmVar k14 d k15 k16)) =>
    (wfTm_Unit k16)) (fun (k15 : Hvl) (t1 : Tm) (wf0 : (wfTm k15 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k15 t2)) IHt2 {d : (Trace TmVar)} {k16 : Hvl} (del : (substhvl_TmVar k14 d k15 k16)) =>
    (wfTm_Prod k16 (IHt1 (weakenTrace d H0) k16 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d H0) k16 (weaken_substhvl_TmVar H0 del)))) (fun (k15 : Hvl) (t1 : Tm) (wf0 : (wfTm k15 t1)) IHt1 (p : Pat) (wf1 : (wfPat k15 p)) (t2 : Tm) (wf2 : (wfTm (appendHvl k15 (appendHvl H0 (bind p))) t2)) IHt2 {d : (Trace TmVar)} {k16 : Hvl} (del : (substhvl_TmVar k14 d k15 k16)) =>
    (wfTm_Case k16 (IHt1 (weakenTrace d H0) k16 (weaken_substhvl_TmVar H0 del)) (substhvl_TmVar_wfPat k15 p wf1 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d (appendHvl H0 (bind p))) (appendHvl k16 (appendHvl H0 (bind p))) (weaken_substhvl_TmVar (appendHvl H0 (bind p)) del))))).
End SubstWellFormed.
 Hint Resolve substhvl_TmVar_wfindex_TmVar : infra.
 Hint Resolve substhvl_TmVar_wfindex_TmVar : subst.
 Hint Resolve substhvl_TmVar_wfindex_TmVar : subst_wf.
 Hint Resolve substhvl_TmVar_wfindex_TmVar : wf.
 Hint Resolve substhvl_TmVar_wfPat substhvl_TmVar_wfTm substhvl_TmVar_wfTy : infra.
 Hint Resolve substhvl_TmVar_wfPat substhvl_TmVar_wfTm substhvl_TmVar_wfTy : subst.
 Hint Resolve substhvl_TmVar_wfPat substhvl_TmVar_wfTm substhvl_TmVar_wfTy : subst_wf.
 Hint Resolve substhvl_TmVar_wfPat substhvl_TmVar_wfTm substhvl_TmVar_wfTy : wf.
 Hint Constructors substhvl_TmVar : infra.
 Hint Constructors substhvl_TmVar : subst.
 Hint Constructors substhvl_TmVar : subst_wf.
 Hint Constructors substhvl_TmVar : wf.
Fixpoint subhvl_TmVar (k14 : Hvl) {struct k14} :
Prop :=
  match k14 with
    | (H0) => True
    | (HS a k14) => match a with
      | (TmVar) => (subhvl_TmVar k14)
    end
  end.
Lemma subhvl_TmVar_append  :
  (forall (k14 : Hvl) (k15 : Hvl) ,
    (subhvl_TmVar k14) -> (subhvl_TmVar k15) -> (subhvl_TmVar (appendHvl k14 k15))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_TmVar_append : infra.
 Hint Resolve subhvl_TmVar_append : wf.
Lemma wfPat_strengthen_subhvl_TmVar  :
  (forall (k11 : Hvl) (k10 : Hvl) (p11 : Pat) ,
    (subhvl_TmVar k11) -> (wfPat (appendHvl k10 k11) (weakenPat p11 k11)) -> (wfPat k10 p11)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfTy_strengthen_subhvl_TmVar  :
  (forall (k13 : Hvl) (k12 : Hvl) (S3 : Ty) ,
    (subhvl_TmVar k13) -> (wfTy (appendHvl k12 k13) (weakenTy S3 k13)) -> (wfTy k12 S3)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H33 : (wfPat (appendHvl _ _) (weakenPat _ _)) |- _ => apply (wfPat_strengthen_subhvl_TmVar) in H33
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H34 : (wfTy (appendHvl _ _) (weakenTy _ _)) |- _ => apply (wfTy_strengthen_subhvl_TmVar) in H34
end : infra wf.
Section Context.
  Inductive Ctx : Type :=
    | empty 
    | evar (G : Ctx) (T : Ty).
  Fixpoint appendCtx (G : Ctx) (G0 : Ctx) :
  Ctx :=
    match G0 with
      | (empty) => G
      | (evar G1 T) => (evar (appendCtx G G1) T)
    end.
  Fixpoint domainCtx (G : Ctx) :
  Hvl :=
    match G with
      | (empty) => H0
      | (evar G0 T) => (HS TmVar (domainCtx G0))
    end.
  Lemma appendCtx_assoc  :
    (forall (G : Ctx) (G0 : Ctx) (G1 : Ctx) ,
      ((appendCtx G (appendCtx G0 G1)) = (appendCtx (appendCtx G G0) G1))).
  Proof.
    needleGenericAppendEnvAssoc .
  Qed.
  Lemma domainCtx_appendCtx  :
    (forall (G : Ctx) (G0 : Ctx) ,
      ((domainCtx (appendCtx G G0)) = (appendHvl (domainCtx G) (domainCtx G0)))).
  Proof.
    needleGenericDomainEnvAppendEnv .
  Qed.
  Fixpoint shift_TmVar_Ctx (c : (Cutoff TmVar)) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shift_TmVar_Ctx c G0) T)
    end.
  Fixpoint weakenCtx (G : Ctx) (k14 : Hvl) {struct k14} :
  Ctx :=
    match k14 with
      | (H0) => G
      | (HS TmVar k14) => (weakenCtx G k14)
    end.
  Fixpoint subst_TmVar_Ctx (d : (Trace TmVar)) (s5 : Tm) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (subst_TmVar_Ctx d s5 G0) T)
    end.
  Lemma domainCtx_shift_TmVar_Ctx  :
    (forall (c : (Cutoff TmVar)) (G : Ctx) ,
      ((domainCtx (shift_TmVar_Ctx c G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainCtx_subst_TmVar_Ctx  :
    (forall (d : (Trace TmVar)) (s5 : Tm) (G : Ctx) ,
      ((domainCtx (subst_TmVar_Ctx d s5 G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainCtx_appendCtx : interaction.
 Hint Rewrite domainCtx_appendCtx : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shift_TmVar_Ctx_appendCtx  :
      (forall (c : (Cutoff TmVar)) (G : Ctx) (G0 : Ctx) ,
        ((shift_TmVar_Ctx c (appendCtx G G0)) = (appendCtx (shift_TmVar_Ctx c G) (shift_TmVar_Ctx (weakenCutoffTmVar c (domainCtx G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma subst_TmVar_Ctx_appendCtx  :
      (forall (d : (Trace TmVar)) (s5 : Tm) (G : Ctx) (G0 : Ctx) ,
        ((subst_TmVar_Ctx d s5 (appendCtx G G0)) = (appendCtx (subst_TmVar_Ctx d s5 G) (subst_TmVar_Ctx (weakenTrace d (domainCtx G)) s5 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S4 : Ty) (k14 : Hvl) (k15 : Hvl) ,
      ((weakenTy (weakenTy S4 k14) k15) = (weakenTy S4 (appendHvl k14 k15)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenPat_append  :
    (forall (p12 : Pat) (k14 : Hvl) (k15 : Hvl) ,
      ((weakenPat (weakenPat p12 k14) k15) = (weakenPat p12 (appendHvl k14 k15)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s5 : Tm) (k14 : Hvl) (k15 : Hvl) ,
      ((weakenTm (weakenTm s5 k14) k15) = (weakenTm s5 (appendHvl k14 k15)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Ctx -> (Index TmVar) -> Ty -> Prop :=
      | lookup_evar_here {G : Ctx}
          (T7 : Ty) :
          (wfTy (domainCtx G) T7) -> (lookup_evar (evar G T7) I0 T7)
      | lookup_evar_there_evar
          {G : Ctx} {x6 : (Index TmVar)}
          (T8 : Ty) (T9 : Ty) :
          (lookup_evar G x6 T8) -> (lookup_evar (evar G T9) (IS x6) T8).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Ctx) (T8 : Ty) (T9 : Ty) ,
        (lookup_evar (evar G T8) I0 T9) -> (T8 = T9)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Ctx} {x6 : (Index TmVar)} ,
        (forall (T8 : Ty) ,
          (lookup_evar G x6 T8) -> (forall (T9 : Ty) ,
            (lookup_evar G x6 T9) -> (T8 = T9)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Ctx} {x6 : (Index TmVar)} (T8 : Ty) ,
        (lookup_evar G x6 T8) -> (wfTy (domainCtx G) T8)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Ctx} (G0 : Ctx) {x6 : (Index TmVar)} (T8 : Ty) ,
        (lookup_evar G x6 T8) -> (lookup_evar (appendCtx G G0) (weakenIndexTmVar x6 (domainCtx G0)) (weakenTy T8 (domainCtx G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Ctx} {x6 : (Index TmVar)} (T10 : Ty) ,
        (lookup_evar G x6 T10) -> (wfindex (domainCtx G) x6)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff TmVar) -> Ctx -> Ctx -> Prop :=
    | shift_evar_here {G : Ctx}
        {T8 : Ty} :
        (shift_evar C0 G (evar G T8))
    | shiftevar_there_evar
        {c : (Cutoff TmVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_evar c G G0) -> (shift_evar (CS c) (evar G T) (evar G0 T)).
  Lemma weaken_shift_evar  :
    (forall (G : Ctx) {c : (Cutoff TmVar)} {G0 : Ctx} {G1 : Ctx} ,
      (shift_evar c G0 G1) -> (shift_evar (weakenCutoffTmVar c (domainCtx G)) (appendCtx G0 G) (appendCtx G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_TmVar  :
    (forall {c : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} ,
      (shift_evar c G G0) -> (shifthvl_TmVar c (domainCtx G) (domainCtx G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Ctx) (T8 : Ty) (s5 : Tm) : (Trace TmVar) -> Ctx -> Ctx -> Prop :=
    | subst_evar_here :
        (subst_evar G T8 s5 X0 (evar G T8) G)
    | subst_evar_there_evar
        {d : (Trace TmVar)} {G0 : Ctx}
        {G1 : Ctx} (T9 : Ty) :
        (subst_evar G T8 s5 d G0 G1) -> (subst_evar G T8 s5 (XS TmVar d) (evar G0 T9) (evar G1 T9)).
  Lemma weaken_subst_evar {G : Ctx} (T8 : Ty) {s5 : Tm} :
    (forall (G0 : Ctx) {d : (Trace TmVar)} {G1 : Ctx} {G2 : Ctx} ,
      (subst_evar G T8 s5 d G1 G2) -> (subst_evar G T8 s5 (weakenTrace d (domainCtx G0)) (appendCtx G1 G0) (appendCtx G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_TmVar {G : Ctx} {s5 : Tm} (T8 : Ty) :
    (forall {d : (Trace TmVar)} {G0 : Ctx} {G1 : Ctx} ,
      (subst_evar G T8 s5 d G0 G1) -> (substhvl_TmVar (domainCtx G) d (domainCtx G0) (domainCtx G1))).
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
  (forall {G : Ctx} (G0 : Ctx) {T8 : Ty} (wf : (wfTy (domainCtx G) T8)) ,
    (lookup_evar (appendCtx (evar G T8) G0) (weakenIndexTmVar I0 (domainCtx G0)) (weakenTy T8 (domainCtx G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfPat wfTm wfTy : infra.
 Hint Constructors wfPat wfTm wfTy : wf.
 Hint Extern 10 ((wfPat _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H33 : (wfTy _ (TArr _ _)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfTy _ (TUnit)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfTy _ (TProd _ _)) |- _ => inversion H33; subst; clear H33
end : infra wf.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H33 : (wfPat _ (PVar _)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfPat _ (PProd _ _)) |- _ => inversion H33; subst; clear H33
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H33 : (wfTm _ (Var _)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfTm _ (Abs _ _)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfTm _ (App _ _)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfTm _ (Unit)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfTm _ (Prod _ _)) |- _ => inversion H33; subst; clear H33
  | H33 : (wfTm _ (Case _ _ _)) |- _ => inversion H33; subst; clear H33
end : infra wf.
 Hint Resolve lookup_evar_wf : infra.
 Hint Resolve lookup_evar_wf : wf.
 Hint Resolve lookup_evar_wfindex : infra.
 Hint Resolve lookup_evar_wfindex : lookup.
 Hint Resolve lookup_evar_wfindex : wf.
 Hint Constructors shift_evar : infra.
 Hint Constructors shift_evar : shift.
 Hint Constructors shift_evar : subst.
 Hint Resolve weaken_shift_evar : infra.
 Hint Resolve weaken_shift_evar : shift.
 Hint Resolve shift_evar_shifthvl_TmVar : infra.
 Hint Resolve shift_evar_shifthvl_TmVar : shift.
 Hint Resolve shift_evar_shifthvl_TmVar : shift_wf.
 Hint Resolve shift_evar_shifthvl_TmVar : wf.
 Hint Constructors subst_evar : infra.
 Hint Constructors subst_evar : subst.
 Hint Resolve weaken_subst_evar : infra.
 Hint Resolve weaken_subst_evar : subst.
 Hint Resolve subst_evar_substhvl_TmVar : infra.
 Hint Resolve subst_evar_substhvl_TmVar : subst.
 Hint Resolve subst_evar_substhvl_TmVar : subst_wf.
 Hint Resolve subst_evar_substhvl_TmVar : wf.
 Hint Resolve subst_evar_substhvl_TmVar : substenv_substhvl.
Lemma shift_evar_lookup_evar  :
  (forall {c : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evar c G G0)) {x6 : (Index TmVar)} {T8 : Ty} ,
    (lookup_evar G x6 T8) -> (lookup_evar G0 (shift_TmVar_Index c x6) T8)).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar : infra.
 Hint Resolve shift_evar_lookup_evar : lookup.
 Hint Resolve shift_evar_lookup_evar : shift.
Fixpoint size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (TArr T7 T8) => (plus 1 (plus (size_Ty T7) (size_Ty T8)))
    | (TUnit) => 1
    | (TProd T9 T10) => (plus 1 (plus (size_Ty T9) (size_Ty T10)))
  end.
Fixpoint size_Pat (p9 : Pat) {struct p9} :
nat :=
  match p9 with
    | (PVar T7) => (plus 1 (size_Ty T7))
    | (PProd p10 p11) => (plus 1 (plus (size_Pat p10) (size_Pat p11)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (Var x6) => 1
    | (Abs T7 t6) => (plus 1 (plus (size_Ty T7) (size_Tm t6)))
    | (App t7 t8) => (plus 1 (plus (size_Tm t7) (size_Tm t8)))
    | (Unit) => 1
    | (Prod t9 t10) => (plus 1 (plus (size_Tm t9) (size_Tm t10)))
    | (Case t11 p9 t12) => (plus 1 (plus (size_Tm t11) (plus (size_Pat p9) (size_Tm t12))))
  end.
Fixpoint shift_TmVar__size_Tm (s : Tm) (c : (Cutoff TmVar)) {struct s} :
((size_Tm (shift_TmVar_Tm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shift_TmVar_Tm c s)) = (size_Tm s)) with
    | (Var _) => eq_refl
    | (Abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_TmVar__size_Tm t (CS c))))
    | (App t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t1 c) (shift_TmVar__size_Tm t2 c)))
    | (Unit) => eq_refl
    | (Prod t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t1 c) (shift_TmVar__size_Tm t2 c)))
    | (Case t1 p t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t1 c) (f_equal2 plus eq_refl (shift_TmVar__size_Tm t2 (weakenCutoffTmVar c (appendHvl H0 (bind p)))))))
  end.
 Hint Rewrite shift_TmVar__size_Tm : interaction.
 Hint Rewrite shift_TmVar__size_Tm : shift_size.
Lemma weaken_size_Pat  :
  (forall (k : Hvl) (p9 : Pat) ,
    ((size_Pat (weakenPat p9 k)) = (size_Pat p9))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Tm  :
  (forall (k : Hvl) (s : Tm) ,
    ((size_Tm (weakenTm s k)) = (size_Tm s))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k : Hvl) (S0 : Ty) ,
    ((size_Ty (weakenTy S0 k)) = (size_Ty S0))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : weaken_size.
 Hint Rewrite appendCtx_assoc : interaction.
 Hint Rewrite <- weakenCutoffTmVar_append weakenTrace_append weakenPat_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.