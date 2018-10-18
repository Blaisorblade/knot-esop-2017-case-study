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
  
  Fixpoint weakenIndexTmVar (x13 : (Index TmVar)) (k : Hvl) {struct k} :
  (Index TmVar) :=
    match k with
      | (H0) => x13
      | (HS a k) => match a with
        | (TmVar) => (IS (weakenIndexTmVar x13 k))
      end
    end.
  Lemma weakenIndexTmVar_append  :
    (forall (x13 : (Index TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTmVar (weakenIndexTmVar x13 k) k0) = (weakenIndexTmVar x13 (appendHvl k k0)))).
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
  Fixpoint bind (p17 : Pat) {struct p17} :
  Hvl :=
    match p17 with
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
  Fixpoint shift_TmVar_Index (c : (Cutoff TmVar)) (x13 : (Index TmVar)) {struct c} :
  (Index TmVar) :=
    match c with
      | (C0) => (IS x13)
      | (CS c) => match x13 with
        | (I0) => I0
        | (IS x13) => (IS (shift_TmVar_Index c x13))
      end
    end.
  Fixpoint shift_TmVar_Tm (c : (Cutoff TmVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x13) => (Var (shift_TmVar_Index c x13))
      | (Abs T35 t21) => (Abs T35 (shift_TmVar_Tm (CS c) t21))
      | (App t22 t23) => (App (shift_TmVar_Tm c t22) (shift_TmVar_Tm c t23))
      | (Unit) => (Unit)
      | (Prod t24 t25) => (Prod (shift_TmVar_Tm c t24) (shift_TmVar_Tm c t25))
      | (Case t26 p18 t27) => (Case (shift_TmVar_Tm c t26) p18 (shift_TmVar_Tm (weakenCutoffTmVar c (appendHvl H0 (bind p18))) t27))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S0
      | (HS TmVar k) => (weakenTy S0 k)
    end.
  Fixpoint weakenPat (p18 : Pat) (k : Hvl) {struct k} :
  Pat :=
    match k with
      | (H0) => p18
      | (HS TmVar k) => (weakenPat p18 k)
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
        (T35 : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x13 : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x13
      | (HS b k) => (XS b (weakenTrace x13 k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x13 : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x13 k) k0) = (weakenTrace x13 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint subst_TmVar_Index (d : (Trace TmVar)) (s : Tm) (x13 : (Index TmVar)) {struct d} :
  Tm :=
    match d with
      | (X0) => match x13 with
        | (I0) => s
        | (IS x13) => (Var x13)
      end
      | (XS TmVar d) => match x13 with
        | (I0) => (Var I0)
        | (IS x13) => (shift_TmVar_Tm C0 (subst_TmVar_Index d s x13))
      end
    end.
  Fixpoint subst_TmVar_Tm (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (Var x13) => (subst_TmVar_Index d s x13)
      | (Abs T35 t21) => (Abs T35 (subst_TmVar_Tm (weakenTrace d (HS TmVar H0)) s t21))
      | (App t22 t23) => (App (subst_TmVar_Tm d s t22) (subst_TmVar_Tm d s t23))
      | (Unit) => (Unit)
      | (Prod t24 t25) => (Prod (subst_TmVar_Tm d s t24) (subst_TmVar_Tm d s t25))
      | (Case t26 p18 t27) => (Case (subst_TmVar_Tm d s t26) p18 (subst_TmVar_Tm (weakenTrace d (appendHvl H0 (bind p18))) s t27))
    end.
End Subst.

Global Hint Resolve (f_equal (shift_TmVar_Tm C0)) : cong_shift0.
 Hint Rewrite weakenCutoffTmVar_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_weaken_bind  :
  (forall (k : Hvl) (p18 : Pat) ,
    ((bind (weakenPat p18 k)) = (bind p18))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bind : interaction.
 Hint Rewrite stability_weaken_bind : stability_weaken.
Section SubstShiftReflection.
  Lemma subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x13 : (Index TmVar)) ,
      ((subst_TmVar_Index (weakenTrace X0 k) s (shift_TmVar_Index (weakenCutoffTmVar C0 k) x13)) = (Var x13))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((subst_TmVar_Tm (weakenTrace X0 k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = s0) :=
    match s0 return ((subst_TmVar_Tm (weakenTrace X0 k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = s0) with
      | (Var x13) => (subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind s k x13)
      | (Abs T35 t21) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t21 (HS TmVar k) s)))
      | (App t22 t23) => (f_equal2 App (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t22 k s) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t23 k s))
      | (Unit) => eq_refl
      | (Prod t22 t23) => (f_equal2 Prod (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t22 k s) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t23 k s))
      | (Case t22 p18 t23) => (f_equal3 Case (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t22 k s) eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p18))) eq_refl (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p18))) eq_refl)) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t23 (appendHvl k (appendHvl H0 (bind p18))) s)))
    end.
  Definition subst_TmVar_Tm0_shift_TmVar_Tm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((subst_TmVar_Tm X0 s (shift_TmVar_Tm C0 s0)) = s0)) := (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind s0 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shift_TmVar_Index_shift_TmVar_Index0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff TmVar)) (x13 : (Index TmVar)) ,
        ((shift_TmVar_Index (weakenCutoffTmVar (CS c) k) (shift_TmVar_Index (weakenCutoffTmVar C0 k) x13)) = (shift_TmVar_Index (weakenCutoffTmVar C0 k) (shift_TmVar_Index (weakenCutoffTmVar c k) x13)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint shift_TmVar__shift_TmVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TmVar)) {struct s} :
    ((shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) :=
      match s return ((shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) with
        | (Var x13) => (f_equal Var (shift_TmVar_Index_shift_TmVar_Index0_comm_ind k c x13))
        | (Abs T35 t21) => (f_equal2 Abs eq_refl (shift_TmVar__shift_TmVar_0_Tm_comm_ind t21 (HS TmVar k) c))
        | (App t22 t23) => (f_equal2 App (shift_TmVar__shift_TmVar_0_Tm_comm_ind t22 k c) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t23 k c))
        | (Unit) => eq_refl
        | (Prod t22 t23) => (f_equal2 Prod (shift_TmVar__shift_TmVar_0_Tm_comm_ind t22 k c) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t23 k c))
        | (Case t22 p18 t23) => (f_equal3 Case (shift_TmVar__shift_TmVar_0_Tm_comm_ind t22 k c) eq_refl (eq_trans (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append (CS c) k (appendHvl H0 (bind p18))) (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p18))) eq_refl)) (eq_trans (shift_TmVar__shift_TmVar_0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind p18))) c) (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p18)))) (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append c k (appendHvl H0 (bind p18)))) eq_refl)))))
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
      (forall (k : Hvl) (x13 : (Index TmVar)) ,
        ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Index (weakenTrace X0 k) s x13)) = (subst_TmVar_Index (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Index (weakenCutoffTmVar (CS c) k) x13)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint shift_TmVar__subst_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff TmVar)) (s : Tm) {struct s0} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) s0))) :=
      match s0 return ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) s0))) with
        | (Var x13) => (shift_TmVar_Tm_subst_TmVar_Index0_comm_ind c s k x13)
        | (Abs T35 t21) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind t21 (HS TmVar k) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t22 t23) => (f_equal2 App (shift_TmVar__subst_TmVar_0_Tm_comm_ind t22 k c s) (shift_TmVar__subst_TmVar_0_Tm_comm_ind t23 k c s))
        | (Unit) => eq_refl
        | (Prod t22 t23) => (f_equal2 Prod (shift_TmVar__subst_TmVar_0_Tm_comm_ind t22 k c s) (shift_TmVar__subst_TmVar_0_Tm_comm_ind t23 k c s))
        | (Case t22 p18 t23) => (f_equal3 Case (shift_TmVar__subst_TmVar_0_Tm_comm_ind t22 k c s) eq_refl (eq_trans (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append c k (appendHvl H0 (bind p18))) (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p18))) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind p18))) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p18)))) eq_refl (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append (CS c) k (appendHvl H0 (bind p18)))) eq_refl)))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shift_TmVar_Tm_subst_TmVar_Tm0_comm (s0 : Tm) : (forall (c : (Cutoff TmVar)) (s : Tm) ,
      ((shift_TmVar_Tm c (subst_TmVar_Tm X0 s s0)) = (subst_TmVar_Tm X0 (shift_TmVar_Tm c s) (shift_TmVar_Tm (CS c) s0)))) := (shift_TmVar__subst_TmVar_0_Tm_comm_ind s0 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma subst_TmVar_Index_shift_TmVar_Tm0_comm_ind (d : (Trace TmVar)) (s : Tm) :
      (forall (k : Hvl) (x13 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TmVar d) k) s (shift_TmVar_Index (weakenCutoffTmVar C0 k) x13)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Index (weakenTrace d k) s x13)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_TmVar__shift_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) {struct s0} :
    ((subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) :=
      match s0 return ((subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) with
        | (Var x13) => (subst_TmVar_Index_shift_TmVar_Tm0_comm_ind d s k x13)
        | (Abs T35 t21) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind t21 (HS TmVar k) d s) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t22 t23) => (f_equal2 App (subst_TmVar__shift_TmVar_0_Tm_comm_ind t22 k d s) (subst_TmVar__shift_TmVar_0_Tm_comm_ind t23 k d s))
        | (Unit) => eq_refl
        | (Prod t22 t23) => (f_equal2 Prod (subst_TmVar__shift_TmVar_0_Tm_comm_ind t22 k d s) (subst_TmVar__shift_TmVar_0_Tm_comm_ind t23 k d s))
        | (Case t22 p18 t23) => (f_equal3 Case (subst_TmVar__shift_TmVar_0_Tm_comm_ind t22 k d s) eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TmVar d) k (appendHvl H0 (bind p18))) eq_refl (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p18))) eq_refl)) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind p18))) d s) (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p18)))) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (appendHvl H0 (bind p18)))) eq_refl eq_refl)))))
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
      (forall (k : Hvl) (x13 : (Index TmVar)) ,
        ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Index (weakenTrace X0 k) s0 x13)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Index (weakenTrace (XS TmVar d) k) s x13)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_TmVar__subst_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s1} :
    ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s s1))) :=
      match s1 return ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s s1))) with
        | (Var x13) => (subst_TmVar_Tm_subst_TmVar_Index0_commright_ind d s s0 k x13)
        | (Abs T35 t21) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t21 (HS TmVar k) d s s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t22 t23) => (f_equal2 App (subst_TmVar__subst_TmVar_0_Tm_comm_ind t22 k d s s0) (subst_TmVar__subst_TmVar_0_Tm_comm_ind t23 k d s s0))
        | (Unit) => eq_refl
        | (Prod t22 t23) => (f_equal2 Prod (subst_TmVar__subst_TmVar_0_Tm_comm_ind t22 k d s s0) (subst_TmVar__subst_TmVar_0_Tm_comm_ind t23 k d s s0))
        | (Case t22 p18 t23) => (f_equal3 Case (subst_TmVar__subst_TmVar_0_Tm_comm_ind t22 k d s s0) eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (appendHvl H0 (bind p18))) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p18))) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t23 (appendHvl k (appendHvl H0 (bind p18))) d s s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p18)))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (appendHvl H0 (bind p18)))) eq_refl eq_refl)))))
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
    | wfTy_TArr {T35 : Ty}
        (wf : (wfTy k T35)) {T36 : Ty}
        (wf0 : (wfTy k T36)) :
        (wfTy k (TArr T35 T36))
    | wfTy_TUnit : (wfTy k (TUnit))
    | wfTy_TProd {T37 : Ty}
        (wf : (wfTy k T37)) {T38 : Ty}
        (wf0 : (wfTy k T38)) :
        (wfTy k (TProd T37 T38)).
  Inductive wfPat (k : Hvl) : Pat -> Prop :=
    | wfPat_PVar {T35 : Ty}
        (wf : (wfTy k T35)) :
        (wfPat k (PVar T35))
    | wfPat_PProd {p18 : Pat}
        (wf : (wfPat k p18)) {p19 : Pat}
        (wf0 : (wfPat (appendHvl k (appendHvl H0 (bind p18))) p19))
        : (wfPat k (PProd p18 p19)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_Var
        (x13 : (Index TmVar))
        (wfi : (wfindex k x13)) :
        (wfTm k (Var x13))
    | wfTm_Abs {T35 : Ty}
        (wf : (wfTy k T35)) {t21 : Tm}
        (wf0 : (wfTm (HS TmVar k) t21))
        : (wfTm k (Abs T35 t21))
    | wfTm_App {t22 : Tm}
        (wf : (wfTm k t22)) {t23 : Tm}
        (wf0 : (wfTm k t23)) :
        (wfTm k (App t22 t23))
    | wfTm_Unit : (wfTm k (Unit))
    | wfTm_Prod {t24 : Tm}
        (wf : (wfTm k t24)) {t25 : Tm}
        (wf0 : (wfTm k t25)) :
        (wfTm k (Prod t24 t25))
    | wfTm_Case {t26 : Tm}
        (wf : (wfTm k t26)) {p18 : Pat}
        (wf0 : (wfPat k p18)) {t27 : Tm}
        (wf1 : (wfTm (appendHvl k (appendHvl H0 (bind p18))) t27))
        : (wfTm k (Case t26 p18 t27)).
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
  Definition inversion_wfPat_PVar_1 (k2 : Hvl) (T : Ty) (H22 : (wfPat k2 (PVar T))) : (wfTy k2 T) := match H22 in (wfPat _ p18) return match p18 return Prop with
    | (PVar T) => (wfTy k2 T)
    | _ => True
  end with
    | (wfPat_PVar T H5) => H5
    | _ => I
  end.
  Definition inversion_wfPat_PProd_0 (k3 : Hvl) (p1 : Pat) (p2 : Pat) (H23 : (wfPat k3 (PProd p1 p2))) : (wfPat k3 p1) := match H23 in (wfPat _ p19) return match p19 return Prop with
    | (PProd p1 p2) => (wfPat k3 p1)
    | _ => True
  end with
    | (wfPat_PProd p1 H6 p2 H7) => H6
    | _ => I
  end.
  Definition inversion_wfPat_PProd_1 (k3 : Hvl) (p1 : Pat) (p2 : Pat) (H23 : (wfPat k3 (PProd p1 p2))) : (wfPat (appendHvl k3 (appendHvl H0 (bind p1))) p2) := match H23 in (wfPat _ p19) return match p19 return Prop with
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
    (forall (c : (Cutoff TmVar)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) (x13 : (Index TmVar)) ,
      (wfindex k10 x13) -> (wfindex k11 (shift_TmVar_Index c x13))).
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
    (forall (p20 : Pat) (wf : (wfPat k10 p20)) ,
      (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
        (shifthvl_TmVar c k10 k11) -> (wfPat k11 p20)))) := (ind_wfPat (fun (k10 : Hvl) (p20 : Pat) (wf : (wfPat k10 p20)) =>
    (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
      (shifthvl_TmVar c k10 k11) -> (wfPat k11 p20))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfPat_PVar k11 (shift_TmVar__wfTy k10 T wf c k11 (weaken_shifthvl_TmVar H0 ins)))) (fun (k10 : Hvl) (p1 : Pat) (wf : (wfPat k10 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k10 (appendHvl H0 (bind p1))) p2)) IHp2 (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfPat_PProd k11 (IHp1 c k11 (weaken_shifthvl_TmVar H0 ins)) (IHp2 (weakenCutoffTmVar c (appendHvl H0 (bind p1))) (appendHvl k11 (appendHvl H0 (bind p1))) (weaken_shifthvl_TmVar (appendHvl H0 (bind p1)) ins))))).
  Definition shift_TmVar__wfTm : (forall (k10 : Hvl) ,
    (forall (s5 : Tm) (wf : (wfTm k10 s5)) ,
      (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
        (shifthvl_TmVar c k10 k11) -> (wfTm k11 (shift_TmVar_Tm c s5))))) := (ind_wfTm (fun (k10 : Hvl) (s5 : Tm) (wf : (wfTm k10 s5)) =>
    (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
      (shifthvl_TmVar c k10 k11) -> (wfTm k11 (shift_TmVar_Tm c s5)))) (fun (k10 : Hvl) (x13 : (Index TmVar)) (wfi : (wfindex k10 x13)) (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTm_Var k11 _ (shift_TmVar__wfindex_TmVar c k10 k11 ins x13 wfi))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) (t : Tm) (wf0 : (wfTm (HS TmVar k10) t)) IHt (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
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
  (forall (k11 : Hvl) (p20 : Pat) (wf : (wfPat k11 p20)) ,
    (wfPat (appendHvl k11 k10) (weakenPat p20 k10))) :=
    match k10 return (forall (k11 : Hvl) (p20 : Pat) (wf : (wfPat k11 p20)) ,
      (wfPat (appendHvl k11 k10) (weakenPat p20 k10))) with
      | (H0) => (fun (k11 : Hvl) (p20 : Pat) (wf : (wfPat k11 p20)) =>
        wf)
      | (HS TmVar k10) => (fun (k11 : Hvl) (p20 : Pat) (wf : (wfPat k11 p20)) =>
        (shift_TmVar__wfPat (appendHvl k11 k10) (weakenPat p20 k10) (weaken_wfPat k10 k11 p20 wf) C0 (HS TmVar (appendHvl k11 k10)) (shifthvl_TmVar_here (appendHvl k11 k10))))
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
  (forall (k14 : Hvl) (p21 : Pat) (k15 : Hvl) (p22 : Pat) ,
    (k14 = k15) -> (p21 = p22) -> (wfPat k14 p21) -> (wfPat k15 p22)).
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
      (substhvl_TmVar k14 d k15 k16) -> (forall {x13 : (Index TmVar)} ,
        (wfindex k15 x13) -> (wfTm k16 (subst_TmVar_Index d s5 x13)))).
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
    (forall (p21 : Pat) (wf0 : (wfPat k15 p21)) ,
      (forall {d : (Trace TmVar)} {k16 : Hvl} ,
        (substhvl_TmVar k14 d k15 k16) -> (wfPat k16 p21)))) := (ind_wfPat (fun (k15 : Hvl) (p21 : Pat) (wf0 : (wfPat k15 p21)) =>
    (forall {d : (Trace TmVar)} {k16 : Hvl} ,
      (substhvl_TmVar k14 d k15 k16) -> (wfPat k16 p21))) (fun (k15 : Hvl) (T : Ty) (wf0 : (wfTy k15 T)) {d : (Trace TmVar)} {k16 : Hvl} (del : (substhvl_TmVar k14 d k15 k16)) =>
    (wfPat_PVar k16 (substhvl_TmVar_wfTy k15 T wf0 (weaken_substhvl_TmVar H0 del)))) (fun (k15 : Hvl) (p1 : Pat) (wf0 : (wfPat k15 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k15 (appendHvl H0 (bind p1))) p2)) IHp2 {d : (Trace TmVar)} {k16 : Hvl} (del : (substhvl_TmVar k14 d k15 k16)) =>
    (wfPat_PProd k16 (IHp1 (weakenTrace d H0) k16 (weaken_substhvl_TmVar H0 del)) (IHp2 (weakenTrace d (appendHvl H0 (bind p1))) (appendHvl k16 (appendHvl H0 (bind p1))) (weaken_substhvl_TmVar (appendHvl H0 (bind p1)) del))))).
  Definition substhvl_TmVar_wfTm {k14 : Hvl} {s5 : Tm} (wf : (wfTm k14 s5)) : (forall (k15 : Hvl) ,
    (forall (s6 : Tm) (wf0 : (wfTm k15 s6)) ,
      (forall {d : (Trace TmVar)} {k16 : Hvl} ,
        (substhvl_TmVar k14 d k15 k16) -> (wfTm k16 (subst_TmVar_Tm d s5 s6))))) := (ind_wfTm (fun (k15 : Hvl) (s6 : Tm) (wf0 : (wfTm k15 s6)) =>
    (forall {d : (Trace TmVar)} {k16 : Hvl} ,
      (substhvl_TmVar k14 d k15 k16) -> (wfTm k16 (subst_TmVar_Tm d s5 s6)))) (fun (k15 : Hvl) {x13 : (Index TmVar)} (wfi : (wfindex k15 x13)) {d : (Trace TmVar)} {k16 : Hvl} (del : (substhvl_TmVar k14 d k15 k16)) =>
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
  (forall (k11 : Hvl) (k10 : Hvl) (p20 : Pat) ,
    (subhvl_TmVar k11) -> (wfPat (appendHvl k10 k11) (weakenPat p20 k11)) -> (wfPat k10 p20)).
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
  Inductive Env : Type :=
    | empty 
    | evar (G2 : Env) (T : Ty).
  Fixpoint appendEnv (G2 : Env) (G3 : Env) :
  Env :=
    match G3 with
      | (empty) => G2
      | (evar G4 T) => (evar (appendEnv G2 G4) T)
    end.
  Fixpoint domainEnv (G2 : Env) :
  Hvl :=
    match G2 with
      | (empty) => H0
      | (evar G3 T) => (HS TmVar (domainEnv G3))
    end.
  Lemma appendEnv_assoc  :
    (forall (G2 : Env) (G3 : Env) (G4 : Env) ,
      ((appendEnv G2 (appendEnv G3 G4)) = (appendEnv (appendEnv G2 G3) G4))).
  Proof.
    needleGenericAppendEnvAssoc .
  Qed.
  Lemma domainEnv_appendEnv  :
    (forall (G2 : Env) (G3 : Env) ,
      ((domainEnv (appendEnv G2 G3)) = (appendHvl (domainEnv G2) (domainEnv G3)))).
  Proof.
    needleGenericDomainEnvAppendEnv .
  Qed.
  Fixpoint shift_TmVar_Env (c : (Cutoff TmVar)) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (shift_TmVar_Env c G3) T)
    end.
  Fixpoint weakenEnv (G2 : Env) (k14 : Hvl) {struct k14} :
  Env :=
    match k14 with
      | (H0) => G2
      | (HS TmVar k14) => (weakenEnv G2 k14)
    end.
  Fixpoint subst_TmVar_Env (d : (Trace TmVar)) (s5 : Tm) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (subst_TmVar_Env d s5 G3) T)
    end.
  Lemma domainEnv_shift_TmVar_Env  :
    (forall (c : (Cutoff TmVar)) (G2 : Env) ,
      ((domainEnv (shift_TmVar_Env c G2)) = (domainEnv G2))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_subst_TmVar_Env  :
    (forall (d : (Trace TmVar)) (s5 : Tm) (G2 : Env) ,
      ((domainEnv (subst_TmVar_Env d s5 G2)) = (domainEnv G2))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shift_TmVar_Env_appendEnv  :
      (forall (c : (Cutoff TmVar)) (G2 : Env) (G3 : Env) ,
        ((shift_TmVar_Env c (appendEnv G2 G3)) = (appendEnv (shift_TmVar_Env c G2) (shift_TmVar_Env (weakenCutoffTmVar c (domainEnv G2)) G3)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma subst_TmVar_Env_appendEnv  :
      (forall (d : (Trace TmVar)) (s5 : Tm) (G2 : Env) (G3 : Env) ,
        ((subst_TmVar_Env d s5 (appendEnv G2 G3)) = (appendEnv (subst_TmVar_Env d s5 G2) (subst_TmVar_Env (weakenTrace d (domainEnv G2)) s5 G3)))).
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
    (forall (p21 : Pat) (k14 : Hvl) (k15 : Hvl) ,
      ((weakenPat (weakenPat p21 k14) k15) = (weakenPat p21 (appendHvl k14 k15)))).
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
    Inductive lookup_evar : Env -> (Index TmVar) -> Ty -> Prop :=
      | lookup_evar_here {G2 : Env}
          (T35 : Ty) :
          (wfTy (domainEnv G2) T35) -> (lookup_evar (evar G2 T35) I0 T35)
      | lookup_evar_there_evar
          {G2 : Env} {x13 : (Index TmVar)}
          (T36 : Ty) (T37 : Ty) :
          (lookup_evar G2 x13 T36) -> (lookup_evar (evar G2 T37) (IS x13) T36).
    Lemma lookup_evar_inversion_here  :
      (forall (G2 : Env) (T36 : Ty) (T37 : Ty) ,
        (lookup_evar (evar G2 T36) I0 T37) -> (T36 = T37)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G2 : Env} {x13 : (Index TmVar)} ,
        (forall (T36 : Ty) ,
          (lookup_evar G2 x13 T36) -> (forall (T37 : Ty) ,
            (lookup_evar G2 x13 T37) -> (T36 = T37)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G2 : Env} {x13 : (Index TmVar)} (T36 : Ty) ,
        (lookup_evar G2 x13 T36) -> (wfTy (domainEnv G2) T36)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G2 : Env} (G3 : Env) {x13 : (Index TmVar)} (T36 : Ty) ,
        (lookup_evar G2 x13 T36) -> (lookup_evar (appendEnv G2 G3) (weakenIndexTmVar x13 (domainEnv G3)) (weakenTy T36 (domainEnv G3)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G2 : Env} {x13 : (Index TmVar)} (T38 : Ty) ,
        (lookup_evar G2 x13 T38) -> (wfindex (domainEnv G2) x13)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff TmVar) -> Env -> Env -> Prop :=
    | shift_evar_here {G2 : Env}
        {T36 : Ty} :
        (shift_evar C0 G2 (evar G2 T36))
    | shiftevar_there_evar
        {c : (Cutoff TmVar)} {G2 : Env}
        {G3 : Env} {T : Ty} :
        (shift_evar c G2 G3) -> (shift_evar (CS c) (evar G2 T) (evar G3 T)).
  Lemma weaken_shift_evar  :
    (forall (G2 : Env) {c : (Cutoff TmVar)} {G3 : Env} {G4 : Env} ,
      (shift_evar c G3 G4) -> (shift_evar (weakenCutoffTmVar c (domainEnv G2)) (appendEnv G3 G2) (appendEnv G4 G2))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_TmVar  :
    (forall {c : (Cutoff TmVar)} {G2 : Env} {G3 : Env} ,
      (shift_evar c G2 G3) -> (shifthvl_TmVar c (domainEnv G2) (domainEnv G3))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G2 : Env) (T36 : Ty) (s5 : Tm) : (Trace TmVar) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G2 T36 s5 X0 (evar G2 T36) G2)
    | subst_evar_there_evar
        {d : (Trace TmVar)} {G3 : Env}
        {G4 : Env} (T37 : Ty) :
        (subst_evar G2 T36 s5 d G3 G4) -> (subst_evar G2 T36 s5 (XS TmVar d) (evar G3 T37) (evar G4 T37)).
  Lemma weaken_subst_evar {G2 : Env} (T36 : Ty) {s5 : Tm} :
    (forall (G3 : Env) {d : (Trace TmVar)} {G4 : Env} {G5 : Env} ,
      (subst_evar G2 T36 s5 d G4 G5) -> (subst_evar G2 T36 s5 (weakenTrace d (domainEnv G3)) (appendEnv G4 G3) (appendEnv G5 G3))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_TmVar {G2 : Env} {s5 : Tm} (T36 : Ty) :
    (forall {d : (Trace TmVar)} {G3 : Env} {G4 : Env} ,
      (subst_evar G2 T36 s5 d G3 G4) -> (substhvl_TmVar (domainEnv G2) d (domainEnv G3) (domainEnv G4))).
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
  (forall {G2 : Env} (G3 : Env) {T36 : Ty} (wf : (wfTy (domainEnv G2) T36)) ,
    (lookup_evar (appendEnv (evar G2 T36) G3) (weakenIndexTmVar I0 (domainEnv G3)) (weakenTy T36 (domainEnv G3)))).
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
  (forall {c : (Cutoff TmVar)} {G2 : Env} {G3 : Env} (ins : (shift_evar c G2 G3)) {x13 : (Index TmVar)} {T36 : Ty} ,
    (lookup_evar G2 x13 T36) -> (lookup_evar G3 (shift_TmVar_Index c x13) T36)).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar : infra.
 Hint Resolve shift_evar_lookup_evar : lookup.
 Hint Resolve shift_evar_lookup_evar : shift.
Fixpoint size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (TArr T35 T36) => (plus 1 (plus (size_Ty T35) (size_Ty T36)))
    | (TUnit) => 1
    | (TProd T37 T38) => (plus 1 (plus (size_Ty T37) (size_Ty T38)))
  end.
Fixpoint size_Pat (p18 : Pat) {struct p18} :
nat :=
  match p18 with
    | (PVar T35) => (plus 1 (size_Ty T35))
    | (PProd p19 p20) => (plus 1 (plus (size_Pat p19) (size_Pat p20)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (Var x13) => 1
    | (Abs T35 t21) => (plus 1 (plus (size_Ty T35) (size_Tm t21)))
    | (App t22 t23) => (plus 1 (plus (size_Tm t22) (size_Tm t23)))
    | (Unit) => 1
    | (Prod t24 t25) => (plus 1 (plus (size_Tm t24) (size_Tm t25)))
    | (Case t26 p18 t27) => (plus 1 (plus (size_Tm t26) (plus (size_Pat p18) (size_Tm t27))))
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
  (forall (k : Hvl) (p18 : Pat) ,
    ((size_Pat (weakenPat p18 k)) = (size_Pat p18))).
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
Inductive PTyping (G2 : Env) : Pat -> Ty -> Env -> Prop :=
  | P_Var (T : Ty)
      (H21 : (wfTy (domainEnv G2) T))
      :
      (PTyping G2 (PVar T) T (evar empty T))
  | P_Prod (T1 : Ty) (T2 : Ty)
      (p1 : Pat) (p2 : Pat) (G : Env)
      (G0 : Env)
      (wtp1 : (PTyping G2 p1 T1 G))
      (wtp2 : (PTyping (appendEnv G2 (appendEnv empty G)) p2 (weakenTy T2 (appendHvl H0 (bind p1))) G0))
      (H23 : (wfTy (domainEnv G2) T2))
      :
      (PTyping G2 (PProd p1 p2) (TProd T1 T2) (appendEnv (appendEnv empty G) G0)).
Inductive Typing (G2 : Env) : Tm -> Ty -> Prop :=
  | T_Var (T : Ty)
      (x : (Index TmVar))
      (lk : (lookup_evar G2 x T))
      (H21 : (wfTy (domainEnv G2) T))
      (H22 : (wfindex (domainEnv G2) x))
      : (Typing G2 (Var x) T)
  | T_Unit :
      (Typing G2 (Unit) (TUnit))
  | T_Abs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm : (Typing (evar G2 T1) t (weakenTy T2 (HS TmVar H0))))
      (H23 : (wfTy (domainEnv G2) T1))
      (H24 : (wfTy (domainEnv G2) T2))
      :
      (Typing G2 (Abs T1 t) (TArr T1 T2))
  | T_App (T11 : Ty) (T12 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm0 : (Typing G2 t1 (TArr T11 T12)))
      (jm1 : (Typing G2 t2 T11)) :
      (Typing G2 (App t1 t2) T12)
  | T_Prod (T1 : Ty) (T2 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm2 : (Typing G2 t1 T1))
      (jm3 : (Typing G2 t2 T2)) :
      (Typing G2 (Prod t1 t2) (TProd T1 T2))
  | T_Let (T1 : Ty) (T2 : Ty)
      (p : Pat) (t1 : Tm) (t2 : Tm)
      (G1 : Env)
      (jm4 : (Typing G2 t1 T1))
      (wtp : (PTyping G2 p T1 G1))
      (jm5 : (Typing (appendEnv G2 (appendEnv empty G1)) t2 (weakenTy T2 (appendHvl H0 (bind p)))))
      (H35 : (wfTy (domainEnv G2) T2))
      : (Typing G2 (Case t1 p t2) T2).
Fixpoint domain_PTyping_bind (G4 : Env) (p23 : Pat) (T41 : Ty) (G5 : Env) (wtp8 : (PTyping G4 p23 T41 G5)) :
((domainEnv G5) = (bind p23)) :=
  match wtp8 in (PTyping _ p23 T41 G5) return ((domainEnv G5) = (bind p23)) with
    | (P_Var T38 H35) => (eq_refl (HS TmVar H0))
    | (P_Prod T39 T40 p21 p22 G2 G3 wtp6 wtp7 H37) => (eq_trans (domainEnv_appendEnv (appendEnv empty G2) G3) (f_equal2 appendHvl (eq_trans (domainEnv_appendEnv empty G2) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bind G4 p21 T39 G2 wtp6))) (domain_PTyping_bind (appendEnv G4 (appendEnv empty G2)) p22 (weakenTy T40 (appendHvl H0 (bind p21))) G3 wtp7)))
  end.
Lemma PTyping_cast  :
  (forall (G2 : Env) (p21 : Pat) (T38 : Ty) (G4 : Env) (G3 : Env) (p22 : Pat) (T39 : Ty) (G5 : Env) ,
    (G2 = G3) -> (p21 = p22) -> (T38 = T39) -> (G4 = G5) -> (PTyping G2 p21 T38 G4) -> (PTyping G3 p22 T39 G5)).
Proof.
  congruence .
Qed.
Lemma Typing_cast  :
  (forall (G2 : Env) (t21 : Tm) (T38 : Ty) (G3 : Env) (t22 : Tm) (T39 : Ty) ,
    (G2 = G3) -> (t21 = t22) -> (T38 = T39) -> (Typing G2 t21 T38) -> (Typing G3 t22 T39)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_PTyping (G9 : Env) (p24 : Pat) (T45 : Ty) (G10 : Env) (wtp9 : (PTyping G9 p24 T45 G10)) :
(forall (c : (Cutoff TmVar)) (G11 : Env) (H48 : (shift_evar c G9 G11)) ,
  (PTyping G11 p24 T45 G10)) :=
  match wtp9 in (PTyping _ p24 T45 G10) return (forall (c : (Cutoff TmVar)) (G11 : Env) (H48 : (shift_evar c G9 G11)) ,
    (PTyping G11 p24 T45 G10)) with
    | (P_Var T42 H41) => (fun (c : (Cutoff TmVar)) (G11 : Env) (H48 : (shift_evar c G9 G11)) =>
      (P_Var G11 T42 (shift_TmVar__wfTy _ _ H41 _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H48)))))
    | (P_Prod T43 T44 p22 p23 G7 G8 wtp7 wtp8 H43) => (fun (c : (Cutoff TmVar)) (G11 : Env) (H48 : (shift_evar c G9 G11)) =>
      (PTyping_cast G11 _ _ _ G11 (PProd p22 p23) (TProd T43 T44) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym eq_refl) eq_refl) (eq_sym eq_refl)) (P_Prod G11 T43 T44 p22 p23 G7 G8 (shift_evar_PTyping G9 p22 T43 G7 wtp7 c G11 (weaken_shift_evar empty H48)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) eq_refl (eq_trans eq_refl (eq_sym eq_refl)) eq_refl (shift_evar_PTyping (appendEnv G9 (appendEnv empty G7)) p23 (weakenTy T44 (appendHvl H0 (bind p22))) G8 wtp8 (weakenCutoffTmVar c (domainEnv (appendEnv empty G7))) (appendEnv G11 (appendEnv empty G7)) (weaken_shift_evar (appendEnv empty G7) H48))) (shift_TmVar__wfTy _ _ H43 _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H48))))))
  end.
Fixpoint shift_evar_Typing (G8 : Env) (t25 : Tm) (T47 : Ty) (jm14 : (Typing G8 t25 T47)) :
(forall (c : (Cutoff TmVar)) (G9 : Env) (H61 : (shift_evar c G8 G9)) ,
  (Typing G9 (shift_TmVar_Tm c t25) T47)) :=
  match jm14 in (Typing _ t25 T47) return (forall (c : (Cutoff TmVar)) (G9 : Env) (H61 : (shift_evar c G8 G9)) ,
    (Typing G9 (shift_TmVar_Tm c t25) T47)) with
    | (T_Var T42 x15 lk0 H41 H42) => (fun (c : (Cutoff TmVar)) (G9 : Env) (H61 : (shift_evar c G8 G9)) =>
      (T_Var G9 T42 (shift_TmVar_Index c x15) (shift_evar_lookup_evar H61 lk0) (shift_TmVar__wfTy _ _ H41 _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H61))) (shift_TmVar__wfindex_TmVar _ _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H61)) _ H42)))
    | (T_Unit) => (fun (c : (Cutoff TmVar)) (G9 : Env) (H61 : (shift_evar c G8 G9)) =>
      (T_Unit G9))
    | (T_Abs T43 T46 t22 jm7 H43 H44) => (fun (c : (Cutoff TmVar)) (G9 : Env) (H61 : (shift_evar c G8 G9)) =>
      (T_Abs G9 T43 T46 (shift_TmVar_Tm (CS c) t22) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar G8 T43) t22 (weakenTy T46 (HS TmVar H0)) jm7 (CS c) (evar G9 T43) (weaken_shift_evar (evar empty T43) H61))) (shift_TmVar__wfTy _ _ H43 _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H61))) (shift_TmVar__wfTy _ _ H44 _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H61)))))
    | (T_App T44 T45 t23 t24 jm8 jm9) => (fun (c : (Cutoff TmVar)) (G9 : Env) (H61 : (shift_evar c G8 G9)) =>
      (T_App G9 T44 T45 (shift_TmVar_Tm c t23) (shift_TmVar_Tm c t24) (shift_evar_Typing G8 t23 (TArr T44 T45) jm8 c G9 (weaken_shift_evar empty H61)) (shift_evar_Typing G8 t24 T44 jm9 c G9 (weaken_shift_evar empty H61))))
    | (T_Prod T43 T46 t23 t24 jm10 jm11) => (fun (c : (Cutoff TmVar)) (G9 : Env) (H61 : (shift_evar c G8 G9)) =>
      (T_Prod G9 T43 T46 (shift_TmVar_Tm c t23) (shift_TmVar_Tm c t24) (shift_evar_Typing G8 t23 T43 jm10 c G9 (weaken_shift_evar empty H61)) (shift_evar_Typing G8 t24 T46 jm11 c G9 (weaken_shift_evar empty H61))))
    | (T_Let T43 T46 p22 t23 t24 G7 jm12 wtp7 jm13 H55) => (fun (c : (Cutoff TmVar)) (G9 : Env) (H61 : (shift_evar c G8 G9)) =>
      (T_Let G9 T43 T46 p22 (shift_TmVar_Tm c t23) (shift_TmVar_Tm (weakenCutoffTmVar c (appendHvl H0 (bind p22))) t24) G7 (shift_evar_Typing G8 t23 T43 jm12 c G9 (weaken_shift_evar empty H61)) (shift_evar_PTyping G8 p22 T43 G7 wtp7 c G9 (weaken_shift_evar empty H61)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) (f_equal2 shift_TmVar_Tm (f_equal2 weakenCutoffTmVar eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bind G8 p22 T43 G7 wtp7)))) eq_refl) (eq_trans eq_refl (eq_sym eq_refl)) (shift_evar_Typing (appendEnv G8 (appendEnv empty G7)) t24 (weakenTy T46 (appendHvl H0 (bind p22))) jm13 (weakenCutoffTmVar c (domainEnv (appendEnv empty G7))) (appendEnv G9 (appendEnv empty G7)) (weaken_shift_evar (appendEnv empty G7) H61))) (shift_TmVar__wfTy _ _ H55 _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H61)))))
  end.
 Hint Resolve shift_evar_PTyping shift_evar_Typing : infra.
 Hint Resolve shift_evar_PTyping shift_evar_Typing : shift.
Fixpoint weaken_PTyping (G2 : Env) :
(forall (G3 : Env) (p21 : Pat) (T38 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p21 T38 G4)) ,
  (PTyping (appendEnv G3 G2) (weakenPat p21 (domainEnv G2)) (weakenTy T38 (domainEnv G2)) (weakenEnv G4 (domainEnv G2)))) :=
  match G2 return (forall (G3 : Env) (p21 : Pat) (T38 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p21 T38 G4)) ,
    (PTyping (appendEnv G3 G2) (weakenPat p21 (domainEnv G2)) (weakenTy T38 (domainEnv G2)) (weakenEnv G4 (domainEnv G2)))) with
    | (empty) => (fun (G3 : Env) (p21 : Pat) (T38 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p21 T38 G4)) =>
      wtp6)
    | (evar G2 T39) => (fun (G3 : Env) (p21 : Pat) (T38 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p21 T38 G4)) =>
      (shift_evar_PTyping (appendEnv G3 G2) (weakenPat p21 (domainEnv G2)) (weakenTy T38 (domainEnv G2)) (weakenEnv G4 (domainEnv G2)) (weaken_PTyping G2 G3 p21 T38 G4 wtp6) C0 (evar (appendEnv G3 G2) T39) shift_evar_here))
  end.
Fixpoint weaken_Typing (G5 : Env) :
(forall (G6 : Env) (t21 : Tm) (T40 : Ty) (jm6 : (Typing G6 t21 T40)) ,
  (Typing (appendEnv G6 G5) (weakenTm t21 (domainEnv G5)) (weakenTy T40 (domainEnv G5)))) :=
  match G5 return (forall (G6 : Env) (t21 : Tm) (T40 : Ty) (jm6 : (Typing G6 t21 T40)) ,
    (Typing (appendEnv G6 G5) (weakenTm t21 (domainEnv G5)) (weakenTy T40 (domainEnv G5)))) with
    | (empty) => (fun (G6 : Env) (t21 : Tm) (T40 : Ty) (jm6 : (Typing G6 t21 T40)) =>
      jm6)
    | (evar G5 T41) => (fun (G6 : Env) (t21 : Tm) (T40 : Ty) (jm6 : (Typing G6 t21 T40)) =>
      (shift_evar_Typing (appendEnv G6 G5) (weakenTm t21 (domainEnv G5)) (weakenTy T40 (domainEnv G5)) (weaken_Typing G5 G6 t21 T40 jm6) C0 (evar (appendEnv G6 G5) T41) shift_evar_here))
  end.
Fixpoint PTyping_wf_0 (G2 : Env) (p22 : Pat) (T42 : Ty) (G7 : Env) (wtp7 : (PTyping G2 p22 T42 G7)) {struct wtp7} :
(wfPat (domainEnv G2) p22) :=
  match wtp7 in (PTyping _ p22 T42 G7) return (wfPat (domainEnv G2) p22) with
    | (P_Var T H21) => (wfPat_PVar (domainEnv G2) H21)
    | (P_Prod T1 T2 p1 p2 G G0 wtp1 wtp2 H23) => (wfPat_PProd (domainEnv G2) (PTyping_wf_0 G2 p1 T1 G wtp1) (wfPat_cast _ _ _ _ (eq_trans (domainEnv_appendEnv G2 (appendEnv empty G)) (f_equal2 appendHvl (eq_refl (domainEnv G2)) (eq_trans (domainEnv_appendEnv empty G) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bind G2 p1 T1 G wtp1))))) eq_refl (PTyping_wf_0 (appendEnv G2 (appendEnv empty G)) p2 (weakenTy T2 (appendHvl H0 (bind p1))) G0 wtp2)))
  end
with PTyping_wf_1 (G2 : Env) (p22 : Pat) (T42 : Ty) (G8 : Env) (wtp8 : (PTyping G2 p22 T42 G8)) {struct wtp8} :
(wfTy (domainEnv G2) T42) :=
  match wtp8 in (PTyping _ p22 T42 G8) return (wfTy (domainEnv G2) T42) with
    | (P_Var T H21) => H21
    | (P_Prod T1 T2 p1 p2 G G0 wtp1 wtp2 H23) => (wfTy_TProd (domainEnv G2) (PTyping_wf_1 G2 p1 T1 G wtp1) H23)
  end.
Fixpoint Typing_wf_0 (G2 : Env) (t22 : Tm) (T43 : Ty) (jm7 : (Typing G2 t22 T43)) {struct jm7} :
(wfTm (domainEnv G2) t22) :=
  match jm7 in (Typing _ t22 T43) return (wfTm (domainEnv G2) t22) with
    | (T_Var T x lk0 H21 H22) => (wfTm_Var (domainEnv G2) _ H22)
    | (T_Unit) => (wfTm_Unit (domainEnv G2))
    | (T_Abs T1 T2 t jm H23 H24) => (wfTm_Abs (domainEnv G2) H23 (Typing_wf_0 (evar G2 T1) t (weakenTy T2 (HS TmVar H0)) jm))
    | (T_App T11 T12 t1 t2 jm0 jm1) => (wfTm_App (domainEnv G2) (Typing_wf_0 G2 t1 (TArr T11 T12) jm0) (Typing_wf_0 G2 t2 T11 jm1))
    | (T_Prod T1 T2 t1 t2 jm2 jm3) => (wfTm_Prod (domainEnv G2) (Typing_wf_0 G2 t1 T1 jm2) (Typing_wf_0 G2 t2 T2 jm3))
    | (T_Let T1 T2 p t1 t2 G1 jm4 wtp jm5 H35) => (wfTm_Case (domainEnv G2) (Typing_wf_0 G2 t1 T1 jm4) (PTyping_wf_0 G2 p T1 G1 wtp) (wfTm_cast _ _ _ _ (eq_trans (domainEnv_appendEnv G2 (appendEnv empty G1)) (f_equal2 appendHvl (eq_refl (domainEnv G2)) (eq_trans (domainEnv_appendEnv empty G1) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bind G2 p T1 G1 wtp))))) eq_refl (Typing_wf_0 (appendEnv G2 (appendEnv empty G1)) t2 (weakenTy T2 (appendHvl H0 (bind p))) jm5)))
  end
with Typing_wf_1 (G2 : Env) (t22 : Tm) (T43 : Ty) (jm8 : (Typing G2 t22 T43)) {struct jm8} :
(wfTy (domainEnv G2) T43) :=
  match jm8 in (Typing _ t22 T43) return (wfTy (domainEnv G2) T43) with
    | (T_Var T x lk1 H21 H22) => H21
    | (T_Unit) => (wfTy_TUnit (domainEnv G2))
    | (T_Abs T1 T2 t jm H23 H24) => (wfTy_TArr (domainEnv G2) H23 H24)
    | (T_App T11 T12 t1 t2 jm0 jm1) => (inversion_wfTy_TArr_1 (domainEnv G2) T11 T12 (Typing_wf_1 G2 t1 (TArr T11 T12) jm0))
    | (T_Prod T1 T2 t1 t2 jm2 jm3) => (wfTy_TProd (domainEnv G2) (Typing_wf_1 G2 t1 T1 jm2) (Typing_wf_1 G2 t2 T2 jm3))
    | (T_Let T1 T2 p t1 t2 G1 jm4 wtp jm5 H35) => H35
  end.
 Hint Extern 8 => match goal with
  | H45 : (PTyping _ _ _ _) |- _ => pose proof ((PTyping_wf_0 _ _ _ _ H45)); pose proof ((PTyping_wf_1 _ _ _ _ H45)); clear H45
end : wf.
 Hint Extern 8 => match goal with
  | H46 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H46)); pose proof ((Typing_wf_1 _ _ _ H46)); clear H46
end : wf.
Lemma subst_evar_lookup_evar (G9 : Env) (s5 : Tm) (T44 : Ty) (jm9 : (Typing G9 s5 T44)) :
  (forall (d : (Trace TmVar)) (G10 : Env) (G12 : Env) (sub : (subst_evar G9 T44 s5 d G10 G12)) (x15 : (Index TmVar)) (T45 : Ty) ,
    (lookup_evar G10 x15 T45) -> (Typing G12 (subst_TmVar_Index d s5 x15) T45)).
Proof.
  needleGenericSubstEnvLookupHom (T_Var).
Qed.
Fixpoint subst_evar_PTyping (G12 : Env) (s5 : Tm) (T44 : Ty) (jm9 : (Typing G12 s5 T44)) (G11 : Env) (p : Pat) (T : Ty) (G13 : Env) (wtp11 : (PTyping G11 p T G13)) :
(forall (G14 : Env) (d : (Trace TmVar)) (H53 : (subst_evar G12 T44 s5 d G11 G14)) ,
  (PTyping G14 p T G13)) :=
  match wtp11 in (PTyping _ p T G13) return (forall (G14 : Env) (d : (Trace TmVar)) (H53 : (subst_evar G12 T44 s5 d G11 G14)) ,
    (PTyping G14 p T G13)) with
    | (P_Var T45 H48) => (fun (G14 : Env) (d : (Trace TmVar)) (H53 : (subst_evar G12 T44 s5 d G11 G14)) =>
      (P_Var G14 T45 (substhvl_TmVar_wfTy _ _ H48 (weaken_substhvl_TmVar H0 (subst_evar_substhvl_TmVar _ H53)))))
    | (P_Prod T46 T47 p23 p24 G9 G10 wtp9 wtp10 H50) => (fun (G14 : Env) (d : (Trace TmVar)) (H53 : (subst_evar G12 T44 s5 d G11 G14)) =>
      (PTyping_cast G14 _ _ _ G14 (PProd p23 p24) (TProd T46 T47) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym eq_refl) eq_refl) (eq_sym eq_refl)) (P_Prod G14 T46 T47 p23 p24 G9 G10 (subst_evar_PTyping G12 s5 T44 jm9 G11 p23 T46 G9 wtp9 G14 d (weaken_subst_evar _ empty H53)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) eq_refl (eq_trans eq_refl (eq_sym eq_refl)) eq_refl (subst_evar_PTyping G12 s5 T44 jm9 (appendEnv G11 (appendEnv empty G9)) p24 (weakenTy T47 (appendHvl H0 (bind p23))) G10 wtp10 (appendEnv G14 (appendEnv empty G9)) (weakenTrace d (domainEnv (appendEnv empty G9))) (weaken_subst_evar _ (appendEnv empty G9) H53))) (substhvl_TmVar_wfTy _ _ H50 (weaken_substhvl_TmVar H0 (subst_evar_substhvl_TmVar _ H53))))))
  end.
Fixpoint subst_evar_Typing (G11 : Env) (s5 : Tm) (T45 : Ty) (jm16 : (Typing G11 s5 T45)) (G10 : Env) (t : Tm) (T : Ty) (jm17 : (Typing G10 t T)) :
(forall (G12 : Env) (d : (Trace TmVar)) (H67 : (subst_evar G11 T45 s5 d G10 G12)) ,
  (Typing G12 (subst_TmVar_Tm d s5 t) T)) :=
  match jm17 in (Typing _ t T) return (forall (G12 : Env) (d : (Trace TmVar)) (H67 : (subst_evar G11 T45 s5 d G10 G12)) ,
    (Typing G12 (subst_TmVar_Tm d s5 t) T)) with
    | (T_Var T46 x15 lk2 H49 H50) => (fun (G12 : Env) (d : (Trace TmVar)) (H67 : (subst_evar G11 T45 s5 d G10 G12)) =>
      (subst_evar_lookup_evar G11 s5 T45 jm16 d G10 G12 H67 x15 T46 lk2))
    | (T_Unit) => (fun (G12 : Env) (d : (Trace TmVar)) (H67 : (subst_evar G11 T45 s5 d G10 G12)) =>
      (T_Unit G12))
    | (T_Abs T47 T50 t23 jm9 H51 H52) => (fun (G12 : Env) (d : (Trace TmVar)) (H67 : (subst_evar G11 T45 s5 d G10 G12)) =>
      (T_Abs G12 T47 T50 (subst_TmVar_Tm (weakenTrace d (HS TmVar H0)) s5 t23) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G11 s5 T45 jm16 (evar G10 T47) t23 (weakenTy T50 (HS TmVar H0)) jm9 (appendEnv G12 (evar empty T47)) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty T47) H67))) (substhvl_TmVar_wfTy _ _ H51 (weaken_substhvl_TmVar H0 (subst_evar_substhvl_TmVar _ H67))) (substhvl_TmVar_wfTy _ _ H52 (weaken_substhvl_TmVar H0 (subst_evar_substhvl_TmVar _ H67)))))
    | (T_App T48 T49 t24 t25 jm10 jm11) => (fun (G12 : Env) (d : (Trace TmVar)) (H67 : (subst_evar G11 T45 s5 d G10 G12)) =>
      (T_App G12 T48 T49 (subst_TmVar_Tm (weakenTrace d H0) s5 t24) (subst_TmVar_Tm (weakenTrace d H0) s5 t25) (subst_evar_Typing G11 s5 T45 jm16 G10 t24 (TArr T48 T49) jm10 G12 d (weaken_subst_evar _ empty H67)) (subst_evar_Typing G11 s5 T45 jm16 G10 t25 T48 jm11 G12 d (weaken_subst_evar _ empty H67))))
    | (T_Prod T47 T50 t24 t25 jm12 jm13) => (fun (G12 : Env) (d : (Trace TmVar)) (H67 : (subst_evar G11 T45 s5 d G10 G12)) =>
      (T_Prod G12 T47 T50 (subst_TmVar_Tm (weakenTrace d H0) s5 t24) (subst_TmVar_Tm (weakenTrace d H0) s5 t25) (subst_evar_Typing G11 s5 T45 jm16 G10 t24 T47 jm12 G12 d (weaken_subst_evar _ empty H67)) (subst_evar_Typing G11 s5 T45 jm16 G10 t25 T50 jm13 G12 d (weaken_subst_evar _ empty H67))))
    | (T_Let T47 T50 p23 t24 t25 G9 jm14 wtp9 jm15 H63) => (fun (G12 : Env) (d : (Trace TmVar)) (H67 : (subst_evar G11 T45 s5 d G10 G12)) =>
      (T_Let G12 T47 T50 p23 (subst_TmVar_Tm (weakenTrace d H0) s5 t24) (subst_TmVar_Tm (weakenTrace d (appendHvl H0 (bind p23))) s5 t25) G9 (subst_evar_Typing G11 s5 T45 jm16 G10 t24 T47 jm14 G12 d (weaken_subst_evar _ empty H67)) (subst_evar_PTyping G11 s5 T45 jm16 G10 p23 T47 G9 wtp9 G12 d (weaken_subst_evar _ empty H67)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) (f_equal3 subst_TmVar_Tm (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bind G10 p23 T47 G9 wtp9)))) eq_refl eq_refl) (eq_trans eq_refl (eq_sym eq_refl)) (subst_evar_Typing G11 s5 T45 jm16 (appendEnv G10 (appendEnv empty G9)) t25 (weakenTy T50 (appendHvl H0 (bind p23))) jm15 (appendEnv G12 (appendEnv empty G9)) (weakenTrace d (domainEnv (appendEnv empty G9))) (weaken_subst_evar _ (appendEnv empty G9) H67))) (substhvl_TmVar_wfTy _ _ H63 (weaken_substhvl_TmVar H0 (subst_evar_substhvl_TmVar _ H67)))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutoffTmVar_append weakenTrace_append weakenPat_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.