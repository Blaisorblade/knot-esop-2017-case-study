Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export Needle.

Local Set Asymmetric Patterns.

Section Namespace.
  Inductive Namespace : Type :=
    | TmVar 
    | TyVar .
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
        | _ => (weakenIndexTmVar x6 k)
      end
    end.
  Fixpoint weakenIndexTyVar (y1 : (Index TyVar)) (k : Hvl) {struct k} :
  (Index TyVar) :=
    match k with
      | (H0) => y1
      | (HS a k) => match a with
        | (TyVar) => (IS (weakenIndexTyVar y1 k))
        | _ => (weakenIndexTyVar y1 k)
      end
    end.
  Lemma weakenIndexTmVar_append  :
    (forall (x6 : (Index TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTmVar (weakenIndexTmVar x6 k) k0) = (weakenIndexTmVar x6 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexTyVar_append  :
    (forall (y1 : (Index TyVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTyVar (weakenIndexTyVar y1 k) k0) = (weakenIndexTyVar y1 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Ty : Set :=
    | TVar (y : (Index TyVar))
    | TArr (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Pat : Set :=
    | PVar 
    | PProp (p1 : Pat) (p2 : Pat).
  Scheme ind_Pat := Induction for Pat Sort Prop.
  
  Inductive Tm : Set :=
    | Var (x : (Index TmVar))
    | App (t1 : Tm) (t2 : Tm)
    | Lam (T : Ty) (t : Tm)
    | Let (p : Pat) (t1 : Tm)
        (t2 : Tm).
  Scheme ind_Tm := Induction for Tm Sort Prop.
End Terms.

Section Functions.
  Fixpoint bind (p8 : Pat) {struct p8} :
  Hvl :=
    match p8 with
      | (PVar) => (HS TmVar H0)
      | (PProp p1 p2) => (appendHvl (appendHvl H0 (bind p1)) (bind p2))
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
        | _ => (weakenCutoffTmVar c k)
      end
    end.
  Fixpoint weakenCutoffTyVar (c : (Cutoff TyVar)) (k : Hvl) {struct k} :
  (Cutoff TyVar) :=
    match k with
      | (H0) => c
      | (HS a k) => match a with
        | (TyVar) => (CS (weakenCutoffTyVar c k))
        | _ => (weakenCutoffTyVar c k)
      end
    end.
  
  Lemma weakenCutoffTmVar_append  :
    (forall (c : (Cutoff TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffTmVar (weakenCutoffTmVar c k) k0) = (weakenCutoffTmVar c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenCutoffTyVar_append  :
    (forall (c : (Cutoff TyVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffTyVar (weakenCutoffTyVar c k) k0) = (weakenCutoffTyVar c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint shiftIndex (c : (Cutoff TmVar)) (x6 : (Index TmVar)) {struct c} :
  (Index TmVar) :=
    match c with
      | (C0) => (IS x6)
      | (CS c) => match x6 with
        | (I0) => I0
        | (IS x6) => (IS (shiftIndex c x6))
      end
    end.
  Fixpoint tshiftIndex (c : (Cutoff TyVar)) (y1 : (Index TyVar)) {struct c} :
  (Index TyVar) :=
    match c with
      | (C0) => (IS y1)
      | (CS c) => match y1 with
        | (I0) => I0
        | (IS y1) => (IS (tshiftIndex c y1))
      end
    end.
  Fixpoint tshiftTy (c : (Cutoff TyVar)) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (TVar y1) => (TVar (tshiftIndex c y1))
      | (TArr T3 T4) => (TArr (tshiftTy c T3) (tshiftTy c T4))
    end.
  Fixpoint shiftTm (c : (Cutoff TmVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x6) => (Var (shiftIndex c x6))
      | (App t4 t5) => (App (shiftTm c t4) (shiftTm c t5))
      | (Lam T3 t6) => (Lam T3 (shiftTm (CS c) t6))
      | (Let p9 t7 t8) => (Let p9 (shiftTm c t7) (shiftTm (weakenCutoffTmVar c (appendHvl H0 (bind p9))) t8))
    end.
  Fixpoint tshiftTm (c : (Cutoff TyVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x6) => (Var x6)
      | (App t4 t5) => (App (tshiftTm c t4) (tshiftTm c t5))
      | (Lam T3 t6) => (Lam (tshiftTy c T3) (tshiftTm c t6))
      | (Let p9 t7 t8) => (Let p9 (tshiftTm c t7) (tshiftTm (weakenCutoffTyVar c (appendHvl H0 (bind p9))) t8))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S0
      | (HS TmVar k) => (weakenTy S0 k)
      | (HS TyVar k) => (tshiftTy C0 (weakenTy S0 k))
    end.
  Fixpoint weakenPat (p9 : Pat) (k : Hvl) {struct k} :
  Pat :=
    match k with
      | (H0) => p9
      | (HS TmVar k) => (weakenPat p9 k)
      | (HS TyVar k) => (weakenPat p9 k)
    end.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} :
  Tm :=
    match k with
      | (H0) => s
      | (HS TmVar k) => (shiftTm C0 (weakenTm s k))
      | (HS TyVar k) => (tshiftTm C0 (weakenTm s k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T3 : (Trace a)).
  
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
        | (IS x6) => (shiftTm C0 (subst_TmVar_Index d s x6))
      end
      | (XS TyVar d) => (tshiftTm C0 (subst_TmVar_Index d s x6))
    end.
  Fixpoint subst_TyVar_Index (d : (Trace TyVar)) (S0 : Ty) (y1 : (Index TyVar)) {struct d} :
  Ty :=
    match d with
      | (X0) => match y1 with
        | (I0) => S0
        | (IS y1) => (TVar y1)
      end
      | (XS TmVar d) => (subst_TyVar_Index d S0 y1)
      | (XS TyVar d) => match y1 with
        | (I0) => (TVar I0)
        | (IS y1) => (tshiftTy C0 (subst_TyVar_Index d S0 y1))
      end
    end.
  Fixpoint subst_TyVar_Ty (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) {struct S1} :
  Ty :=
    match S1 with
      | (TVar y1) => (subst_TyVar_Index d S0 y1)
      | (TArr T3 T4) => (TArr (subst_TyVar_Ty d S0 T3) (subst_TyVar_Ty d S0 T4))
    end.
  Fixpoint subst_TmVar_Tm (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (Var x6) => (subst_TmVar_Index d s x6)
      | (App t4 t5) => (App (subst_TmVar_Tm d s t4) (subst_TmVar_Tm d s t5))
      | (Lam T3 t6) => (Lam T3 (subst_TmVar_Tm (weakenTrace d (HS TmVar H0)) s t6))
      | (Let p9 t7 t8) => (Let p9 (subst_TmVar_Tm d s t7) (subst_TmVar_Tm (weakenTrace d (appendHvl H0 (bind p9))) s t8))
    end.
  Fixpoint subst_TyVar_Tm (d : (Trace TyVar)) (S0 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x6) => (Var x6)
      | (App t4 t5) => (App (subst_TyVar_Tm d S0 t4) (subst_TyVar_Tm d S0 t5))
      | (Lam T3 t6) => (Lam (subst_TyVar_Ty d S0 T3) (subst_TyVar_Tm (weakenTrace d (HS TmVar H0)) S0 t6))
      | (Let p9 t7 t8) => (Let p9 (subst_TyVar_Tm d S0 t7) (subst_TyVar_Tm (weakenTrace d (appendHvl H0 (bind p9))) S0 t8))
    end.
End Subst.

Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutoffTmVar_append weakenCutoffTyVar_append : weakencutoff_append.
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
  Lemma subst_TmVar_Index0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x6 : (Index TmVar)) ,
      ((subst_TmVar_Index (weakenTrace X0 k) s (shiftIndex (weakenCutoffTmVar C0 k) x6)) = (Var x6))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma subst_TyVar_Index0_tshiftIndex0_reflection_ind (S0 : Ty) :
    (forall (k : Hvl) (y1 : (Index TyVar)) ,
      ((subst_TyVar_Index (weakenTrace X0 k) S0 (tshiftIndex (weakenCutoffTyVar C0 k) y1)) = (TVar y1))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst_TyVar_0_tshift0_Ty_reflection_ind (S1 : Ty) (k : Hvl) (S0 : Ty) {struct S1} :
  ((subst_TyVar_Ty (weakenTrace X0 k) S0 (tshiftTy (weakenCutoffTyVar C0 k) S1)) = S1) :=
    match S1 return ((subst_TyVar_Ty (weakenTrace X0 k) S0 (tshiftTy (weakenCutoffTyVar C0 k) S1)) = S1) with
      | (TVar y1) => (subst_TyVar_Index0_tshiftIndex0_reflection_ind S0 k y1)
      | (TArr T3 T4) => (f_equal2 TArr (subst_TyVar_0_tshift0_Ty_reflection_ind T3 k S0) (subst_TyVar_0_tshift0_Ty_reflection_ind T4 k S0))
    end.
  Fixpoint subst_TmVar_0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((subst_TmVar_Tm (weakenTrace X0 k) s (shiftTm (weakenCutoffTmVar C0 k) s0)) = s0) :=
    match s0 return ((subst_TmVar_Tm (weakenTrace X0 k) s (shiftTm (weakenCutoffTmVar C0 k) s0)) = s0) with
      | (Var x6) => (subst_TmVar_Index0_shiftIndex0_reflection_ind s k x6)
      | (App t5 t6) => (f_equal2 App (subst_TmVar_0_shift0_Tm_reflection_ind t5 k s) (subst_TmVar_0_shift0_Tm_reflection_ind t6 k s))
      | (Lam T3 t4) => (f_equal2 Lam eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift0_Tm_reflection_ind t4 (HS TmVar k) s)))
      | (Let p9 t5 t6) => (f_equal3 Let eq_refl (subst_TmVar_0_shift0_Tm_reflection_ind t5 k s) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p9))) eq_refl (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p9))) eq_refl)) (subst_TmVar_0_shift0_Tm_reflection_ind t6 (appendHvl k (appendHvl H0 (bind p9))) s)))
    end.
  Fixpoint subst_TyVar_0_tshift0_Tm_reflection_ind (s : Tm) (k : Hvl) (S0 : Ty) {struct s} :
  ((subst_TyVar_Tm (weakenTrace X0 k) S0 (tshiftTm (weakenCutoffTyVar C0 k) s)) = s) :=
    match s return ((subst_TyVar_Tm (weakenTrace X0 k) S0 (tshiftTm (weakenCutoffTyVar C0 k) s)) = s) with
      | (Var x6) => eq_refl
      | (App t5 t6) => (f_equal2 App (subst_TyVar_0_tshift0_Tm_reflection_ind t5 k S0) (subst_TyVar_0_tshift0_Tm_reflection_ind t6 k S0))
      | (Lam T3 t4) => (f_equal2 Lam (subst_TyVar_0_tshift0_Ty_reflection_ind T3 k S0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_tshift0_Tm_reflection_ind t4 (HS TmVar k) S0)))
      | (Let p9 t5 t6) => (f_equal3 Let eq_refl (subst_TyVar_0_tshift0_Tm_reflection_ind t5 k S0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p9))) eq_refl (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p9))) eq_refl)) (subst_TyVar_0_tshift0_Tm_reflection_ind t6 (appendHvl k (appendHvl H0 (bind p9))) S0)))
    end.
  Definition subst_TyVar_Ty0_tshiftTy0_reflection (S1 : Ty) : (forall (S0 : Ty) ,
    ((subst_TyVar_Ty X0 S0 (tshiftTy C0 S1)) = S1)) := (subst_TyVar_0_tshift0_Ty_reflection_ind S1 H0).
  Definition subst_TmVar_Tm0_shiftTm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((subst_TmVar_Tm X0 s (shiftTm C0 s0)) = s0)) := (subst_TmVar_0_shift0_Tm_reflection_ind s0 H0).
  Definition subst_TyVar_Tm0_tshiftTm0_reflection (s : Tm) : (forall (S0 : Ty) ,
    ((subst_TyVar_Tm X0 S0 (tshiftTm C0 s)) = s)) := (subst_TyVar_0_tshift0_Tm_reflection_ind s H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff TmVar)) (x6 : (Index TmVar)) ,
        ((shiftIndex (weakenCutoffTmVar (CS c) k) (shiftIndex (weakenCutoffTmVar C0 k) x6)) = (shiftIndex (weakenCutoffTmVar C0 k) (shiftIndex (weakenCutoffTmVar c k) x6)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff TyVar)) (y1 : (Index TyVar)) ,
        ((tshiftIndex (weakenCutoffTyVar (CS c) k) (tshiftIndex (weakenCutoffTyVar C0 k) y1)) = (tshiftIndex (weakenCutoffTyVar C0 k) (tshiftIndex (weakenCutoffTyVar c k) y1)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint tshift_tshift0_Ty_comm_ind (S0 : Ty) (k : Hvl) (c : (Cutoff TyVar)) {struct S0} :
    ((tshiftTy (weakenCutoffTyVar (CS c) k) (tshiftTy (weakenCutoffTyVar C0 k) S0)) = (tshiftTy (weakenCutoffTyVar C0 k) (tshiftTy (weakenCutoffTyVar c k) S0))) :=
      match S0 return ((tshiftTy (weakenCutoffTyVar (CS c) k) (tshiftTy (weakenCutoffTyVar C0 k) S0)) = (tshiftTy (weakenCutoffTyVar C0 k) (tshiftTy (weakenCutoffTyVar c k) S0))) with
        | (TVar y1) => (f_equal TVar (tshiftIndex_tshiftIndex0_comm_ind k c y1))
        | (TArr T3 T4) => (f_equal2 TArr (tshift_tshift0_Ty_comm_ind T3 k c) (tshift_tshift0_Ty_comm_ind T4 k c))
      end.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TmVar)) {struct s} :
    ((shiftTm (weakenCutoffTmVar (CS c) k) (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (shiftTm (weakenCutoffTmVar c k) s))) :=
      match s return ((shiftTm (weakenCutoffTmVar (CS c) k) (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (shiftTm (weakenCutoffTmVar c k) s))) with
        | (Var x6) => (f_equal Var (shiftIndex_shiftIndex0_comm_ind k c x6))
        | (App t5 t6) => (f_equal2 App (shift_shift0_Tm_comm_ind t5 k c) (shift_shift0_Tm_comm_ind t6 k c))
        | (Lam T3 t4) => (f_equal2 Lam eq_refl (shift_shift0_Tm_comm_ind t4 (HS TmVar k) c))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (shift_shift0_Tm_comm_ind t5 k c) (eq_trans (f_equal2 shiftTm (weakenCutoffTmVar_append (CS c) k (appendHvl H0 (bind p9))) (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p9))) eq_refl)) (eq_trans (shift_shift0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) c) (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p9)))) (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append c k (appendHvl H0 (bind p9)))) eq_refl)))))
      end.
    Fixpoint shift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TmVar)) {struct s} :
    ((shiftTm (weakenCutoffTmVar c k) (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (shiftTm (weakenCutoffTmVar c k) s))) :=
      match s return ((shiftTm (weakenCutoffTmVar c k) (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (shiftTm (weakenCutoffTmVar c k) s))) with
        | (Var x6) => eq_refl
        | (App t5 t6) => (f_equal2 App (shift_tshift0_Tm_comm_ind t5 k c) (shift_tshift0_Tm_comm_ind t6 k c))
        | (Lam T3 t4) => (f_equal2 Lam eq_refl (shift_tshift0_Tm_comm_ind t4 (HS TmVar k) c))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (shift_tshift0_Tm_comm_ind t5 k c) (eq_trans (f_equal2 shiftTm (weakenCutoffTmVar_append c k (appendHvl H0 (bind p9))) (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p9))) eq_refl)) (eq_trans (shift_tshift0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) c) (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p9)))) (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append c k (appendHvl H0 (bind p9)))) eq_refl)))))
      end.
    Fixpoint tshift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TyVar)) {struct s} :
    ((tshiftTm (weakenCutoffTyVar c k) (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (tshiftTm (weakenCutoffTyVar c k) s))) :=
      match s return ((tshiftTm (weakenCutoffTyVar c k) (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (tshiftTm (weakenCutoffTyVar c k) s))) with
        | (Var x6) => eq_refl
        | (App t5 t6) => (f_equal2 App (tshift_shift0_Tm_comm_ind t5 k c) (tshift_shift0_Tm_comm_ind t6 k c))
        | (Lam T3 t4) => (f_equal2 Lam eq_refl (tshift_shift0_Tm_comm_ind t4 (HS TmVar k) c))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (tshift_shift0_Tm_comm_ind t5 k c) (eq_trans (f_equal2 tshiftTm (weakenCutoffTyVar_append c k (appendHvl H0 (bind p9))) (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p9))) eq_refl)) (eq_trans (tshift_shift0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) c) (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p9)))) (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append c k (appendHvl H0 (bind p9)))) eq_refl)))))
      end.
    Fixpoint tshift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TyVar)) {struct s} :
    ((tshiftTm (weakenCutoffTyVar (CS c) k) (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (tshiftTm (weakenCutoffTyVar c k) s))) :=
      match s return ((tshiftTm (weakenCutoffTyVar (CS c) k) (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (tshiftTm (weakenCutoffTyVar c k) s))) with
        | (Var x6) => eq_refl
        | (App t5 t6) => (f_equal2 App (tshift_tshift0_Tm_comm_ind t5 k c) (tshift_tshift0_Tm_comm_ind t6 k c))
        | (Lam T3 t4) => (f_equal2 Lam (tshift_tshift0_Ty_comm_ind T3 k c) (tshift_tshift0_Tm_comm_ind t4 (HS TmVar k) c))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (tshift_tshift0_Tm_comm_ind t5 k c) (eq_trans (f_equal2 tshiftTm (weakenCutoffTyVar_append (CS c) k (appendHvl H0 (bind p9))) (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p9))) eq_refl)) (eq_trans (tshift_tshift0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) c) (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p9)))) (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append c k (appendHvl H0 (bind p9)))) eq_refl)))))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_Ty_comm (S0 : Ty) : (forall (c : (Cutoff TyVar)) ,
      ((tshiftTy (CS c) (tshiftTy C0 S0)) = (tshiftTy C0 (tshiftTy c S0)))) := (tshift_tshift0_Ty_comm_ind S0 H0).
    Definition shift_shift0_Tm_comm (s : Tm) : (forall (c : (Cutoff TmVar)) ,
      ((shiftTm (CS c) (shiftTm C0 s)) = (shiftTm C0 (shiftTm c s)))) := (shift_shift0_Tm_comm_ind s H0).
    Definition shift_tshift0_Tm_comm (s : Tm) : (forall (c : (Cutoff TmVar)) ,
      ((shiftTm c (tshiftTm C0 s)) = (tshiftTm C0 (shiftTm c s)))) := (shift_tshift0_Tm_comm_ind s H0).
    Definition tshift_shift0_Tm_comm (s : Tm) : (forall (c : (Cutoff TyVar)) ,
      ((tshiftTm c (shiftTm C0 s)) = (shiftTm C0 (tshiftTm c s)))) := (tshift_shift0_Tm_comm_ind s H0).
    Definition tshift_tshift0_Tm_comm (s : Tm) : (forall (c : (Cutoff TyVar)) ,
      ((tshiftTm (CS c) (tshiftTm C0 s)) = (tshiftTm C0 (tshiftTm c s)))) := (tshift_tshift0_Tm_comm_ind s H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : interaction.
 Hint Rewrite shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTy_tshiftTy  :
    (forall (k : Hvl) (c : (Cutoff TyVar)) (S0 : Ty) ,
      ((weakenTy (tshiftTy c S0) k) = (tshiftTy (weakenCutoffTyVar c k) (weakenTy S0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k : Hvl) (c : (Cutoff TmVar)) (s : Tm) ,
      ((weakenTm (shiftTm c s) k) = (shiftTm (weakenCutoffTmVar c k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k : Hvl) (c : (Cutoff TyVar)) (s : Tm) ,
      ((weakenTm (tshiftTm c s) k) = (tshiftTm (weakenCutoffTyVar c k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTm_subst_TmVar_Index0_comm_ind (c : (Cutoff TmVar)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((shiftTm (weakenCutoffTmVar c k) (subst_TmVar_Index (weakenTrace X0 k) s x6)) = (subst_TmVar_Index (weakenTrace X0 k) (shiftTm c s) (shiftIndex (weakenCutoffTmVar (CS c) k) x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_subst_TmVar_Index0_comm_ind (c : (Cutoff TyVar)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((tshiftTm (weakenCutoffTyVar c k) (subst_TmVar_Index (weakenTrace X0 k) s x6)) = (subst_TmVar_Index (weakenTrace X0 k) (tshiftTm c s) x6))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTy_subst_TyVar_Index0_comm_ind (c : (Cutoff TyVar)) (S0 : Ty) :
      (forall (k : Hvl) (y1 : (Index TyVar)) ,
        ((tshiftTy (weakenCutoffTyVar c k) (subst_TyVar_Index (weakenTrace X0 k) S0 y1)) = (subst_TyVar_Index (weakenTrace X0 k) (tshiftTy c S0) (tshiftIndex (weakenCutoffTyVar (CS c) k) y1)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint tshift_subst_TyVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c : (Cutoff TyVar)) (S0 : Ty) {struct S1} :
    ((tshiftTy (weakenCutoffTyVar c k) (subst_TyVar_Ty (weakenTrace X0 k) S0 S1)) = (subst_TyVar_Ty (weakenTrace X0 k) (tshiftTy c S0) (tshiftTy (weakenCutoffTyVar (CS c) k) S1))) :=
      match S1 return ((tshiftTy (weakenCutoffTyVar c k) (subst_TyVar_Ty (weakenTrace X0 k) S0 S1)) = (subst_TyVar_Ty (weakenTrace X0 k) (tshiftTy c S0) (tshiftTy (weakenCutoffTyVar (CS c) k) S1))) with
        | (TVar y1) => (tshiftTy_subst_TyVar_Index0_comm_ind c S0 k y1)
        | (TArr T3 T4) => (f_equal2 TArr (tshift_subst_TyVar_0_Ty_comm_ind T3 k c S0) (tshift_subst_TyVar_0_Ty_comm_ind T4 k c S0))
      end.
    Fixpoint shift_subst_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff TmVar)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutoffTmVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutoffTmVar (CS c) k) s0))) :=
      match s0 return ((shiftTm (weakenCutoffTmVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutoffTmVar (CS c) k) s0))) with
        | (Var x6) => (shiftTm_subst_TmVar_Index0_comm_ind c s k x6)
        | (App t5 t6) => (f_equal2 App (shift_subst_TmVar_0_Tm_comm_ind t5 k c s) (shift_subst_TmVar_0_Tm_comm_ind t6 k c s))
        | (Lam T3 t4) => (f_equal2 Lam eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_subst_TmVar_0_Tm_comm_ind t4 (HS TmVar k) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (shift_subst_TmVar_0_Tm_comm_ind t5 k c s) (eq_trans (f_equal2 shiftTm (weakenCutoffTmVar_append c k (appendHvl H0 (bind p9))) (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p9))) eq_refl eq_refl)) (eq_trans (shift_subst_TmVar_0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p9)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append (CS c) k (appendHvl H0 (bind p9)))) eq_refl)))))
      end.
    Fixpoint shift_subst_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TmVar)) (S0 : Ty) {struct s} :
    ((shiftTm (weakenCutoffTmVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S0 s)) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (shiftTm (weakenCutoffTmVar c k) s))) :=
      match s return ((shiftTm (weakenCutoffTmVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S0 s)) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (shiftTm (weakenCutoffTmVar c k) s))) with
        | (Var x6) => eq_refl
        | (App t5 t6) => (f_equal2 App (shift_subst_TyVar_0_Tm_comm_ind t5 k c S0) (shift_subst_TyVar_0_Tm_comm_ind t6 k c S0))
        | (Lam T3 t4) => (f_equal2 Lam eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_subst_TyVar_0_Tm_comm_ind t4 (HS TmVar k) c S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (shift_subst_TyVar_0_Tm_comm_ind t5 k c S0) (eq_trans (f_equal2 shiftTm (weakenCutoffTmVar_append c k (appendHvl H0 (bind p9))) (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p9))) eq_refl eq_refl)) (eq_trans (shift_subst_TyVar_0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) c S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p9)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append c k (appendHvl H0 (bind p9)))) eq_refl)))))
      end.
    Fixpoint tshift_subst_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff TyVar)) (s : Tm) {struct s0} :
    ((tshiftTm (weakenCutoffTyVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (tshiftTm c s) (tshiftTm (weakenCutoffTyVar c k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffTyVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (tshiftTm c s) (tshiftTm (weakenCutoffTyVar c k) s0))) with
        | (Var x6) => (tshiftTm_subst_TmVar_Index0_comm_ind c s k x6)
        | (App t5 t6) => (f_equal2 App (tshift_subst_TmVar_0_Tm_comm_ind t5 k c s) (tshift_subst_TmVar_0_Tm_comm_ind t6 k c s))
        | (Lam T3 t4) => (f_equal2 Lam eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tshift_subst_TmVar_0_Tm_comm_ind t4 (HS TmVar k) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (tshift_subst_TmVar_0_Tm_comm_ind t5 k c s) (eq_trans (f_equal2 tshiftTm (weakenCutoffTyVar_append c k (appendHvl H0 (bind p9))) (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p9))) eq_refl eq_refl)) (eq_trans (tshift_subst_TmVar_0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p9)))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append c k (appendHvl H0 (bind p9)))) eq_refl)))))
      end.
    Fixpoint tshift_subst_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TyVar)) (S0 : Ty) {struct s} :
    ((tshiftTm (weakenCutoffTyVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S0 s)) = (subst_TyVar_Tm (weakenTrace X0 k) (tshiftTy c S0) (tshiftTm (weakenCutoffTyVar (CS c) k) s))) :=
      match s return ((tshiftTm (weakenCutoffTyVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S0 s)) = (subst_TyVar_Tm (weakenTrace X0 k) (tshiftTy c S0) (tshiftTm (weakenCutoffTyVar (CS c) k) s))) with
        | (Var x6) => eq_refl
        | (App t5 t6) => (f_equal2 App (tshift_subst_TyVar_0_Tm_comm_ind t5 k c S0) (tshift_subst_TyVar_0_Tm_comm_ind t6 k c S0))
        | (Lam T3 t4) => (f_equal2 Lam (tshift_subst_TyVar_0_Ty_comm_ind T3 k c S0) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tshift_subst_TyVar_0_Tm_comm_ind t4 (HS TmVar k) c S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (tshift_subst_TyVar_0_Tm_comm_ind t5 k c S0) (eq_trans (f_equal2 tshiftTm (weakenCutoffTyVar_append c k (appendHvl H0 (bind p9))) (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p9))) eq_refl eq_refl)) (eq_trans (tshift_subst_TyVar_0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) c S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p9)))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append (CS c) k (appendHvl H0 (bind p9)))) eq_refl)))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTy_subst_TyVar_Ty0_comm (S1 : Ty) : (forall (c : (Cutoff TyVar)) (S0 : Ty) ,
      ((tshiftTy c (subst_TyVar_Ty X0 S0 S1)) = (subst_TyVar_Ty X0 (tshiftTy c S0) (tshiftTy (CS c) S1)))) := (tshift_subst_TyVar_0_Ty_comm_ind S1 H0).
    Definition shiftTm_subst_TmVar_Tm0_comm (s0 : Tm) : (forall (c : (Cutoff TmVar)) (s : Tm) ,
      ((shiftTm c (subst_TmVar_Tm X0 s s0)) = (subst_TmVar_Tm X0 (shiftTm c s) (shiftTm (CS c) s0)))) := (shift_subst_TmVar_0_Tm_comm_ind s0 H0).
    Definition shiftTm_subst_TyVar_Tm0_comm (s : Tm) : (forall (c : (Cutoff TmVar)) (S0 : Ty) ,
      ((shiftTm c (subst_TyVar_Tm X0 S0 s)) = (subst_TyVar_Tm X0 S0 (shiftTm c s)))) := (shift_subst_TyVar_0_Tm_comm_ind s H0).
    Definition tshiftTm_subst_TmVar_Tm0_comm (s0 : Tm) : (forall (c : (Cutoff TyVar)) (s : Tm) ,
      ((tshiftTm c (subst_TmVar_Tm X0 s s0)) = (subst_TmVar_Tm X0 (tshiftTm c s) (tshiftTm c s0)))) := (tshift_subst_TmVar_0_Tm_comm_ind s0 H0).
    Definition tshiftTm_subst_TyVar_Tm0_comm (s : Tm) : (forall (c : (Cutoff TyVar)) (S0 : Ty) ,
      ((tshiftTm c (subst_TyVar_Tm X0 S0 s)) = (subst_TyVar_Tm X0 (tshiftTy c S0) (tshiftTm (CS c) s)))) := (tshift_subst_TyVar_0_Tm_comm_ind s H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma subst_TmVar_Index_shiftTm0_comm_ind (d : (Trace TmVar)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TmVar d) k) s (shiftIndex (weakenCutoffTmVar C0 k) x6)) = (shiftTm (weakenCutoffTmVar C0 k) (subst_TmVar_Index (weakenTrace d k) s x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Index_tshiftTm0_comm_ind (d : (Trace TmVar)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TyVar d) k) s x6) = (tshiftTm (weakenCutoffTyVar C0 k) (subst_TmVar_Index (weakenTrace d k) s x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Index_shiftTy0_comm_ind (d : (Trace TyVar)) (S0 : Ty) :
      (forall (k : Hvl) (y1 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace (XS TmVar d) k) S0 y1) = (subst_TyVar_Index (weakenTrace d k) S0 y1))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Index_tshiftTy0_comm_ind (d : (Trace TyVar)) (S0 : Ty) :
      (forall (k : Hvl) (y1 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace (XS TyVar d) k) S0 (tshiftIndex (weakenCutoffTyVar C0 k) y1)) = (tshiftTy (weakenCutoffTyVar C0 k) (subst_TyVar_Index (weakenTrace d k) S0 y1)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_TyVar__tshift0_Ty_comm_ind (S1 : Ty) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct S1} :
    ((subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S0 (tshiftTy (weakenCutoffTyVar C0 k) S1)) = (tshiftTy (weakenCutoffTyVar C0 k) (subst_TyVar_Ty (weakenTrace d k) S0 S1))) :=
      match S1 return ((subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S0 (tshiftTy (weakenCutoffTyVar C0 k) S1)) = (tshiftTy (weakenCutoffTyVar C0 k) (subst_TyVar_Ty (weakenTrace d k) S0 S1))) with
        | (TVar y1) => (subst_TyVar_Index_tshiftTy0_comm_ind d S0 k y1)
        | (TArr T3 T4) => (f_equal2 TArr (subst_TyVar__tshift0_Ty_comm_ind T3 k d S0) (subst_TyVar__tshift0_Ty_comm_ind T4 k d S0))
      end.
    Fixpoint subst_TmVar__shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) {struct s0} :
    ((subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s (shiftTm (weakenCutoffTmVar C0 k) s0)) = (shiftTm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) :=
      match s0 return ((subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s (shiftTm (weakenCutoffTmVar C0 k) s0)) = (shiftTm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) with
        | (Var x6) => (subst_TmVar_Index_shiftTm0_comm_ind d s k x6)
        | (App t5 t6) => (f_equal2 App (subst_TmVar__shift0_Tm_comm_ind t5 k d s) (subst_TmVar__shift0_Tm_comm_ind t6 k d s))
        | (Lam T3 t4) => (f_equal2 Lam eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift0_Tm_comm_ind t4 (HS TmVar k) d s) (f_equal2 shiftTm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (subst_TmVar__shift0_Tm_comm_ind t5 k d s) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TmVar d) k (appendHvl H0 (bind p9))) eq_refl (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p9))) eq_refl)) (eq_trans (subst_TmVar__shift0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) d s) (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p9)))) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (appendHvl H0 (bind p9)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) {struct s0} :
    ((subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s (tshiftTm (weakenCutoffTyVar C0 k) s0)) = (tshiftTm (weakenCutoffTyVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) :=
      match s0 return ((subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s (tshiftTm (weakenCutoffTyVar C0 k) s0)) = (tshiftTm (weakenCutoffTyVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) with
        | (Var x6) => (subst_TmVar_Index_tshiftTm0_comm_ind d s k x6)
        | (App t5 t6) => (f_equal2 App (subst_TmVar__tshift0_Tm_comm_ind t5 k d s) (subst_TmVar__tshift0_Tm_comm_ind t6 k d s))
        | (Lam T3 t4) => (f_equal2 Lam eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__tshift0_Tm_comm_ind t4 (HS TmVar k) d s) (f_equal2 tshiftTm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (subst_TmVar__tshift0_Tm_comm_ind t5 k d s) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TyVar d) k (appendHvl H0 (bind p9))) eq_refl (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p9))) eq_refl)) (eq_trans (subst_TmVar__tshift0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) d s) (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p9)))) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (appendHvl H0 (bind p9)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__shift0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct s} :
    ((subst_TyVar_Tm (weakenTrace d k) S0 (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S0 s))) :=
      match s return ((subst_TyVar_Tm (weakenTrace d k) S0 (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S0 s))) with
        | (Var x6) => eq_refl
        | (App t5 t6) => (f_equal2 App (subst_TyVar__shift0_Tm_comm_ind t5 k d S0) (subst_TyVar__shift0_Tm_comm_ind t6 k d S0))
        | (Lam T3 t4) => (f_equal2 Lam eq_refl (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift0_Tm_comm_ind t4 (HS TmVar k) d S0) (f_equal2 shiftTm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (subst_TyVar__shift0_Tm_comm_ind t5 k d S0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (appendHvl H0 (bind p9))) eq_refl (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p9))) eq_refl)) (eq_trans (subst_TyVar__shift0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) d S0) (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p9)))) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (appendHvl H0 (bind p9)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct s} :
    ((subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S0 (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S0 s))) :=
      match s return ((subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S0 (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S0 s))) with
        | (Var x6) => eq_refl
        | (App t5 t6) => (f_equal2 App (subst_TyVar__tshift0_Tm_comm_ind t5 k d S0) (subst_TyVar__tshift0_Tm_comm_ind t6 k d S0))
        | (Lam T3 t4) => (f_equal2 Lam (subst_TyVar__tshift0_Ty_comm_ind T3 k d S0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__tshift0_Tm_comm_ind t4 (HS TmVar k) d S0) (f_equal2 tshiftTm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (subst_TyVar__tshift0_Tm_comm_ind t5 k d S0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TyVar d) k (appendHvl H0 (bind p9))) eq_refl (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p9))) eq_refl)) (eq_trans (subst_TyVar__tshift0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) d S0) (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p9)))) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (appendHvl H0 (bind p9)))) eq_refl eq_refl)))))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition subst_TyVar_Ty_tshiftTy0_comm (S1 : Ty) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Ty (XS TyVar d) S0 (tshiftTy C0 S1)) = (tshiftTy C0 (subst_TyVar_Ty d S0 S1)))) := (subst_TyVar__tshift0_Ty_comm_ind S1 H0).
    Definition subst_TmVar_Tm_shiftTm0_comm (s0 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) ,
      ((subst_TmVar_Tm (XS TmVar d) s (shiftTm C0 s0)) = (shiftTm C0 (subst_TmVar_Tm d s s0)))) := (subst_TmVar__shift0_Tm_comm_ind s0 H0).
    Definition subst_TmVar_Tm_tshiftTm0_comm (s0 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) ,
      ((subst_TmVar_Tm (XS TyVar d) s (tshiftTm C0 s0)) = (tshiftTm C0 (subst_TmVar_Tm d s s0)))) := (subst_TmVar__tshift0_Tm_comm_ind s0 H0).
    Definition subst_TyVar_Tm_shiftTm0_comm (s : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Tm d S0 (shiftTm C0 s)) = (shiftTm C0 (subst_TyVar_Tm d S0 s)))) := (subst_TyVar__shift0_Tm_comm_ind s H0).
    Definition subst_TyVar_Tm_tshiftTm0_comm (s : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Tm (XS TyVar d) S0 (tshiftTm C0 s)) = (tshiftTm C0 (subst_TyVar_Tm d S0 s)))) := (subst_TyVar__tshift0_Tm_comm_ind s H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Fixpoint subst_TyVar__TmVar_Ty_ind (S1 : Ty) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct S1} :
    ((subst_TyVar_Ty (weakenTrace (XS TmVar d) k) S0 S1) = (subst_TyVar_Ty (weakenTrace d k) S0 S1)) :=
      match S1 return ((subst_TyVar_Ty (weakenTrace (XS TmVar d) k) S0 S1) = (subst_TyVar_Ty (weakenTrace d k) S0 S1)) with
        | (TVar y1) => (subst_TyVar_Index_shiftTy0_comm_ind d S0 k y1)
        | (TArr T3 T4) => (f_equal2 TArr (subst_TyVar__TmVar_Ty_ind T3 k d S0) (subst_TyVar__TmVar_Ty_ind T4 k d S0))
      end.
    Fixpoint subst_TyVar__TmVar_Tm_ind (s : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct s} :
    ((subst_TyVar_Tm (weakenTrace (XS TmVar d) k) S0 s) = (subst_TyVar_Tm (weakenTrace d k) S0 s)) :=
      match s return ((subst_TyVar_Tm (weakenTrace (XS TmVar d) k) S0 s) = (subst_TyVar_Tm (weakenTrace d k) S0 s)) with
        | (Var x6) => eq_refl
        | (App t5 t6) => (f_equal2 App (subst_TyVar__TmVar_Tm_ind t5 k d S0) (subst_TyVar__TmVar_Tm_ind t6 k d S0))
        | (Lam T3 t4) => (f_equal2 Lam (subst_TyVar__TmVar_Ty_ind T3 k d S0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__TmVar_Tm_ind t4 (HS TmVar k) d S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl))))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (subst_TyVar__TmVar_Tm_ind t5 k d S0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TmVar d) k (appendHvl H0 (bind p9))) eq_refl eq_refl) (eq_trans (subst_TyVar__TmVar_Tm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) d S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (appendHvl H0 (bind p9)))) eq_refl eq_refl))))
      end.
  End SubstSubordInd.
  Section SubstSubord.
    Definition subst_TyVar_Ty_TmVar (S1 : Ty) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Ty (XS TmVar d) S0 S1) = (subst_TyVar_Ty d S0 S1))) := (subst_TyVar__TmVar_Ty_ind S1 H0).
    Definition subst_TyVar_Tm_TmVar (s : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Tm (XS TmVar d) S0 s) = (subst_TyVar_Tm d S0 s))) := (subst_TyVar__TmVar_Tm_ind s H0).
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite subst_TmVar_Tm0_shiftTm0_reflection subst_TyVar_Tm0_tshiftTm0_reflection subst_TyVar_Ty0_tshiftTy0_reflection : interaction.
 Hint Rewrite subst_TmVar_Tm0_shiftTm0_reflection subst_TyVar_Tm0_tshiftTm0_reflection subst_TyVar_Ty0_tshiftTy0_reflection : reflection.
 Hint Rewrite subst_TmVar_Tm_shiftTm0_comm subst_TmVar_Tm_tshiftTm0_comm subst_TyVar_Tm_shiftTm0_comm subst_TyVar_Tm_tshiftTm0_comm subst_TyVar_Ty_tshiftTy0_comm : interaction.
 Hint Rewrite subst_TmVar_Tm_shiftTm0_comm subst_TmVar_Tm_tshiftTm0_comm subst_TyVar_Tm_shiftTm0_comm subst_TyVar_Tm_tshiftTm0_comm subst_TyVar_Ty_tshiftTy0_comm : subst_shift0.
 Hint Rewrite subst_TyVar_Tm_TmVar subst_TyVar_Ty_TmVar : interaction.
 Hint Rewrite subst_TyVar_Tm_TmVar subst_TyVar_Ty_TmVar : subst_shift0.
 Hint Rewrite shiftTm_subst_TmVar_Tm0_comm shiftTm_subst_TyVar_Tm0_comm tshiftTm_subst_TmVar_Tm0_comm tshiftTm_subst_TyVar_Tm0_comm tshiftTy_subst_TyVar_Ty0_comm : interaction.
 Hint Rewrite shiftTm_subst_TmVar_Tm0_comm shiftTm_subst_TyVar_Tm0_comm tshiftTm_subst_TmVar_Tm0_comm tshiftTm_subst_TyVar_Tm0_comm tshiftTy_subst_TyVar_Ty0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma subst_TmVar_Tm_subst_TmVar_Index0_commright_ind (d : (Trace TmVar)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Index (weakenTrace X0 k) s0 x6)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Index (weakenTrace (XS TmVar d) k) s x6)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Tm_subst_TmVar_Index0_commright_ind (d : (Trace TyVar)) (S0 : Ty) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TmVar_Index (weakenTrace X0 k) s x6)) = (subst_TmVar_Index (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) x6))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Ty_subst_TyVar_Index0_commright_ind (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) :
      (forall (k : Hvl) (y1 : (Index TyVar)) ,
        ((subst_TyVar_Ty (weakenTrace d k) S0 (subst_TyVar_Index (weakenTrace X0 k) S1 y1)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Index (weakenTrace (XS TyVar d) k) S0 y1)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Ty_subst_TyVar_Index0_commleft_ind (d : (Trace TmVar)) (s : Tm) (S0 : Ty) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace d k) s x6) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (subst_TmVar_Index (weakenTrace (XS TyVar d) k) s x6)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_TyVar__subst_TyVar_0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) {struct S2} :
    ((subst_TyVar_Ty (weakenTrace d k) S0 (subst_TyVar_Ty (weakenTrace X0 k) S1 S2)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S0 S2))) :=
      match S2 return ((subst_TyVar_Ty (weakenTrace d k) S0 (subst_TyVar_Ty (weakenTrace X0 k) S1 S2)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S0 S2))) with
        | (TVar y1) => (subst_TyVar_Ty_subst_TyVar_Index0_commright_ind d S0 S1 k y1)
        | (TArr T3 T4) => (f_equal2 TArr (subst_TyVar__subst_TyVar_0_Ty_comm_ind T3 k d S0 S1) (subst_TyVar__subst_TyVar_0_Ty_comm_ind T4 k d S0 S1))
      end.
    Fixpoint subst_TmVar__subst_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s1} :
    ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s s1))) :=
      match s1 return ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s s1))) with
        | (Var x6) => (subst_TmVar_Tm_subst_TmVar_Index0_commright_ind d s s0 k x6)
        | (App t5 t6) => (f_equal2 App (subst_TmVar__subst_TmVar_0_Tm_comm_ind t5 k d s s0) (subst_TmVar__subst_TmVar_0_Tm_comm_ind t6 k d s s0))
        | (Lam T3 t4) => (f_equal2 Lam eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t4 (HS TmVar k) d s s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (subst_TmVar__subst_TmVar_0_Tm_comm_ind t5 k d s s0) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (appendHvl H0 (bind p9))) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p9))) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) d s s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p9)))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (appendHvl H0 (bind p9)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__subst_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) (S0 : Ty) {struct s0} :
    ((subst_TmVar_Tm (weakenTrace d k) s (subst_TyVar_Tm (weakenTrace X0 k) S0 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s s0))) :=
      match s0 return ((subst_TmVar_Tm (weakenTrace d k) s (subst_TyVar_Tm (weakenTrace X0 k) S0 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s s0))) with
        | (Var x6) => (subst_TmVar_Ty_subst_TyVar_Index0_commleft_ind d s S0 k x6)
        | (App t5 t6) => (f_equal2 App (subst_TmVar__subst_TyVar_0_Tm_comm_ind t5 k d s S0) (subst_TmVar__subst_TyVar_0_Tm_comm_ind t6 k d s S0))
        | (Lam T3 t4) => (f_equal2 Lam eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Tm_comm_ind t4 (HS TmVar k) d s S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (subst_TmVar__subst_TyVar_0_Tm_comm_ind t5 k d s S0) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (appendHvl H0 (bind p9))) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p9))) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) d s S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p9)))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (appendHvl H0 (bind p9)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__subst_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (s : Tm) {struct s0} :
    ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) (subst_TyVar_Tm (weakenTrace d k) S0 s0))) :=
      match s0 return ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) (subst_TyVar_Tm (weakenTrace d k) S0 s0))) with
        | (Var x6) => (subst_TyVar_Tm_subst_TmVar_Index0_commright_ind d S0 s k x6)
        | (App t5 t6) => (f_equal2 App (subst_TyVar__subst_TmVar_0_Tm_comm_ind t5 k d S0 s) (subst_TyVar__subst_TmVar_0_Tm_comm_ind t6 k d S0 s))
        | (Lam T3 t4) => (f_equal2 Lam eq_refl (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Tm_comm_ind t4 (HS TmVar k) d S0 s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (subst_TyVar__subst_TmVar_0_Tm_comm_ind t5 k d S0 s) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (appendHvl H0 (bind p9))) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p9))) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) d S0 s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p9)))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (appendHvl H0 (bind p9)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__subst_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) {struct s} :
    ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TyVar_Tm (weakenTrace X0 k) S1 s)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S0 s))) :=
      match s return ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TyVar_Tm (weakenTrace X0 k) S1 s)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S0 s))) with
        | (Var x6) => eq_refl
        | (App t5 t6) => (f_equal2 App (subst_TyVar__subst_TyVar_0_Tm_comm_ind t5 k d S0 S1) (subst_TyVar__subst_TyVar_0_Tm_comm_ind t6 k d S0 S1))
        | (Lam T3 t4) => (f_equal2 Lam (subst_TyVar__subst_TyVar_0_Ty_comm_ind T3 k d S0 S1) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Tm_comm_ind t4 (HS TmVar k) d S0 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (Let p9 t5 t6) => (f_equal3 Let eq_refl (subst_TyVar__subst_TyVar_0_Tm_comm_ind t5 k d S0 S1) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (appendHvl H0 (bind p9))) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p9))) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Tm_comm_ind t6 (appendHvl k (appendHvl H0 (bind p9))) d S0 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p9)))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (appendHvl H0 (bind p9)))) eq_refl eq_refl)))))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition subst_TyVar_Ty_subst_TyVar_Ty0_comm (S2 : Ty) : (forall (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) ,
      ((subst_TyVar_Ty d S0 (subst_TyVar_Ty X0 S1 S2)) = (subst_TyVar_Ty X0 (subst_TyVar_Ty d S0 S1) (subst_TyVar_Ty (XS TyVar d) S0 S2)))) := (subst_TyVar__subst_TyVar_0_Ty_comm_ind S2 H0).
    Definition subst_TmVar_Tm_subst_TmVar_Tm0_comm (s1 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) (s0 : Tm) ,
      ((subst_TmVar_Tm d s (subst_TmVar_Tm X0 s0 s1)) = (subst_TmVar_Tm X0 (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (XS TmVar d) s s1)))) := (subst_TmVar__subst_TmVar_0_Tm_comm_ind s1 H0).
    Definition subst_TmVar_Tm_subst_TyVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) (S0 : Ty) ,
      ((subst_TmVar_Tm d s (subst_TyVar_Tm X0 S0 s0)) = (subst_TyVar_Tm X0 S0 (subst_TmVar_Tm (XS TyVar d) s s0)))) := (subst_TmVar__subst_TyVar_0_Tm_comm_ind s0 H0).
    Definition subst_TyVar_Tm_subst_TmVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) (s : Tm) ,
      ((subst_TyVar_Tm d S0 (subst_TmVar_Tm X0 s s0)) = (subst_TmVar_Tm X0 (subst_TyVar_Tm d S0 s) (subst_TyVar_Tm d S0 s0)))) := (subst_TyVar__subst_TmVar_0_Tm_comm_ind s0 H0).
    Definition subst_TyVar_Tm_subst_TyVar_Tm0_comm (s : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) ,
      ((subst_TyVar_Tm d S0 (subst_TyVar_Tm X0 S1 s)) = (subst_TyVar_Tm X0 (subst_TyVar_Ty d S0 S1) (subst_TyVar_Tm (XS TyVar d) S0 s)))) := (subst_TyVar__subst_TyVar_0_Tm_comm_ind s H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_subst_TyVar_Ty  :
      (forall (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) ,
        ((weakenTy (subst_TyVar_Ty d S0 S1) k) = (subst_TyVar_Ty (weakenTrace d k) S0 (weakenTy S1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_subst_TmVar_Tm  :
      (forall (k : Hvl) (d : (Trace TmVar)) (s : Tm) (s0 : Tm) ,
        ((weakenTm (subst_TmVar_Tm d s s0) k) = (subst_TmVar_Tm (weakenTrace d k) s (weakenTm s0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_subst_TyVar_Tm  :
      (forall (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (s : Tm) ,
        ((weakenTm (subst_TyVar_Tm d S0 s) k) = (subst_TyVar_Tm (weakenTrace d k) S0 (weakenTm s k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite subst_TmVar_Tm_subst_TmVar_Tm0_comm subst_TyVar_Tm_subst_TyVar_Tm0_comm subst_TyVar_Ty_subst_TyVar_Ty0_comm : interaction.
 Hint Rewrite subst_TmVar_Tm_subst_TmVar_Tm0_comm subst_TyVar_Tm_subst_TyVar_Tm0_comm subst_TyVar_Ty_subst_TyVar_Ty0_comm : subst_subst0.
 Hint Rewrite weakenTm_shiftTm weakenTm_tshiftTm weakenTy_tshiftTy : weaken_shift.
 Hint Rewrite weakenTm_subst_TmVar_Tm weakenTm_subst_TyVar_Tm weakenTy_subst_TyVar_Ty : weaken_subst.
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
    | wfTy_TVar
        (y1 : (Index TyVar))
        (wfi : (wfindex k y1)) :
        (wfTy k (TVar y1))
    | wfTy_TArr {T3 : Ty}
        (wf : (wfTy k T3)) {T4 : Ty}
        (wf0 : (wfTy k T4)) :
        (wfTy k (TArr T3 T4)).
  Inductive wfPat (k : Hvl) : Pat -> Prop :=
    | wfPat_PVar :
        (wfPat k (PVar))
    | wfPat_PProp {p9 : Pat}
        (wf : (wfPat k p9)) {p10 : Pat}
        (wf0 : (wfPat (appendHvl k (appendHvl H0 (bind p9))) p10))
        : (wfPat k (PProp p9 p10)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_Var
        (x6 : (Index TmVar))
        (wfi : (wfindex k x6)) :
        (wfTm k (Var x6))
    | wfTm_App {t4 : Tm}
        (wf : (wfTm k t4)) {t5 : Tm}
        (wf0 : (wfTm k t5)) :
        (wfTm k (App t4 t5))
    | wfTm_Lam {T3 : Ty}
        (wf : (wfTy k T3)) {t6 : Tm}
        (wf0 : (wfTm (HS TmVar k) t6)) :
        (wfTm k (Lam T3 t6))
    | wfTm_Let {p9 : Pat}
        (wf : (wfPat k p9)) {t7 : Tm}
        (wf0 : (wfTm k t7)) {t8 : Tm}
        (wf1 : (wfTm (appendHvl k (appendHvl H0 (bind p9))) t8))
        : (wfTm k (Let p9 t7 t8)).
  Definition inversion_wfTy_TVar_1 (k : Hvl) (y : (Index TyVar)) (H15 : (wfTy k (TVar y))) : (wfindex k y) := match H15 in (wfTy _ S0) return match S0 return Prop with
    | (TVar y) => (wfindex k y)
    | _ => True
  end with
    | (wfTy_TVar y H1) => H1
    | _ => I
  end.
  Definition inversion_wfTy_TArr_0 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H16 : (wfTy k0 (TArr T1 T2))) : (wfTy k0 T1) := match H16 in (wfTy _ S1) return match S1 return Prop with
    | (TArr T1 T2) => (wfTy k0 T1)
    | _ => True
  end with
    | (wfTy_TArr T1 H2 T2 H3) => H2
    | _ => I
  end.
  Definition inversion_wfTy_TArr_1 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H16 : (wfTy k0 (TArr T1 T2))) : (wfTy k0 T2) := match H16 in (wfTy _ S1) return match S1 return Prop with
    | (TArr T1 T2) => (wfTy k0 T2)
    | _ => True
  end with
    | (wfTy_TArr T1 H2 T2 H3) => H3
    | _ => I
  end.
  Definition inversion_wfPat_PProp_0 (k2 : Hvl) (p1 : Pat) (p2 : Pat) (H18 : (wfPat k2 (PProp p1 p2))) : (wfPat k2 p1) := match H18 in (wfPat _ p10) return match p10 return Prop with
    | (PProp p1 p2) => (wfPat k2 p1)
    | _ => True
  end with
    | (wfPat_PProp p1 H4 p2 H5) => H4
    | _ => I
  end.
  Definition inversion_wfPat_PProp_1 (k2 : Hvl) (p1 : Pat) (p2 : Pat) (H18 : (wfPat k2 (PProp p1 p2))) : (wfPat (appendHvl k2 (appendHvl H0 (bind p1))) p2) := match H18 in (wfPat _ p10) return match p10 return Prop with
    | (PProp p1 p2) => (wfPat (appendHvl k2 (appendHvl H0 (bind p1))) p2)
    | _ => True
  end with
    | (wfPat_PProp p1 H4 p2 H5) => H5
    | _ => I
  end.
  Definition inversion_wfTm_Var_1 (k3 : Hvl) (x : (Index TmVar)) (H19 : (wfTm k3 (Var x))) : (wfindex k3 x) := match H19 in (wfTm _ s) return match s return Prop with
    | (Var x) => (wfindex k3 x)
    | _ => True
  end with
    | (wfTm_Var x H6) => H6
    | _ => I
  end.
  Definition inversion_wfTm_App_0 (k4 : Hvl) (t1 : Tm) (t2 : Tm) (H20 : (wfTm k4 (App t1 t2))) : (wfTm k4 t1) := match H20 in (wfTm _ s0) return match s0 return Prop with
    | (App t1 t2) => (wfTm k4 t1)
    | _ => True
  end with
    | (wfTm_App t1 H7 t2 H8) => H7
    | _ => I
  end.
  Definition inversion_wfTm_App_1 (k4 : Hvl) (t1 : Tm) (t2 : Tm) (H20 : (wfTm k4 (App t1 t2))) : (wfTm k4 t2) := match H20 in (wfTm _ s0) return match s0 return Prop with
    | (App t1 t2) => (wfTm k4 t2)
    | _ => True
  end with
    | (wfTm_App t1 H7 t2 H8) => H8
    | _ => I
  end.
  Definition inversion_wfTm_Lam_1 (k5 : Hvl) (T : Ty) (t : Tm) (H21 : (wfTm k5 (Lam T t))) : (wfTy k5 T) := match H21 in (wfTm _ s1) return match s1 return Prop with
    | (Lam T t) => (wfTy k5 T)
    | _ => True
  end with
    | (wfTm_Lam T H9 t H10) => H9
    | _ => I
  end.
  Definition inversion_wfTm_Lam_2 (k5 : Hvl) (T : Ty) (t : Tm) (H21 : (wfTm k5 (Lam T t))) : (wfTm (HS TmVar k5) t) := match H21 in (wfTm _ s1) return match s1 return Prop with
    | (Lam T t) => (wfTm (HS TmVar k5) t)
    | _ => True
  end with
    | (wfTm_Lam T H9 t H10) => H10
    | _ => I
  end.
  Definition inversion_wfTm_Let_0 (k6 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H22 : (wfTm k6 (Let p t1 t2))) : (wfPat k6 p) := match H22 in (wfTm _ s2) return match s2 return Prop with
    | (Let p t1 t2) => (wfPat k6 p)
    | _ => True
  end with
    | (wfTm_Let p H11 t1 H12 t2 H13) => H11
    | _ => I
  end.
  Definition inversion_wfTm_Let_1 (k6 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H22 : (wfTm k6 (Let p t1 t2))) : (wfTm k6 t1) := match H22 in (wfTm _ s2) return match s2 return Prop with
    | (Let p t1 t2) => (wfTm k6 t1)
    | _ => True
  end with
    | (wfTm_Let p H11 t1 H12 t2 H13) => H12
    | _ => I
  end.
  Definition inversion_wfTm_Let_2 (k6 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H22 : (wfTm k6 (Let p t1 t2))) : (wfTm (appendHvl k6 (appendHvl H0 (bind p))) t2) := match H22 in (wfTm _ s2) return match s2 return Prop with
    | (Let p t1 t2) => (wfTm (appendHvl k6 (appendHvl H0 (bind p))) t2)
    | _ => True
  end with
    | (wfTm_Let p H11 t1 H12 t2 H13) => H13
    | _ => I
  end.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfPat := Induction for wfPat Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_TmVar : (forall (c : (Cutoff TmVar)) (k7 : Hvl) (k8 : Hvl) ,
    Prop) :=
    | shifthvl_TmVar_here
        (k7 : Hvl) :
        (shifthvl_TmVar C0 k7 (HS TmVar k7))
    | shifthvl_TmVar_there_TmVar
        (c : (Cutoff TmVar)) (k7 : Hvl)
        (k8 : Hvl) :
        (shifthvl_TmVar c k7 k8) -> (shifthvl_TmVar (CS c) (HS TmVar k7) (HS TmVar k8))
    | shifthvl_TmVar_there_TyVar
        (c : (Cutoff TmVar)) (k7 : Hvl)
        (k8 : Hvl) :
        (shifthvl_TmVar c k7 k8) -> (shifthvl_TmVar c (HS TyVar k7) (HS TyVar k8)).
  Inductive shifthvl_TyVar : (forall (c : (Cutoff TyVar)) (k7 : Hvl) (k8 : Hvl) ,
    Prop) :=
    | shifthvl_TyVar_here
        (k7 : Hvl) :
        (shifthvl_TyVar C0 k7 (HS TyVar k7))
    | shifthvl_TyVar_there_TmVar
        (c : (Cutoff TyVar)) (k7 : Hvl)
        (k8 : Hvl) :
        (shifthvl_TyVar c k7 k8) -> (shifthvl_TyVar c (HS TmVar k7) (HS TmVar k8))
    | shifthvl_TyVar_there_TyVar
        (c : (Cutoff TyVar)) (k7 : Hvl)
        (k8 : Hvl) :
        (shifthvl_TyVar c k7 k8) -> (shifthvl_TyVar (CS c) (HS TyVar k7) (HS TyVar k8)).
  Lemma weaken_shifthvl_TmVar  :
    (forall (k7 : Hvl) {c : (Cutoff TmVar)} {k8 : Hvl} {k9 : Hvl} ,
      (shifthvl_TmVar c k8 k9) -> (shifthvl_TmVar (weakenCutoffTmVar c k7) (appendHvl k8 k7) (appendHvl k9 k7))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_TyVar  :
    (forall (k7 : Hvl) {c : (Cutoff TyVar)} {k8 : Hvl} {k9 : Hvl} ,
      (shifthvl_TyVar c k8 k9) -> (shifthvl_TyVar (weakenCutoffTyVar c k7) (appendHvl k8 k7) (appendHvl k9 k7))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_TmVar  :
    (forall (c : (Cutoff TmVar)) (k7 : Hvl) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) (x6 : (Index TmVar)) ,
      (wfindex k7 x6) -> (wfindex k8 (shiftIndex c x6))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_TyVar  :
    (forall (c : (Cutoff TmVar)) (k7 : Hvl) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) (y1 : (Index TyVar)) ,
      (wfindex k7 y1) -> (wfindex k8 y1)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_TmVar  :
    (forall (c : (Cutoff TyVar)) (k7 : Hvl) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) (x6 : (Index TmVar)) ,
      (wfindex k7 x6) -> (wfindex k8 x6)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_TyVar  :
    (forall (c : (Cutoff TyVar)) (k7 : Hvl) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) (y1 : (Index TyVar)) ,
      (wfindex k7 y1) -> (wfindex k8 (tshiftIndex c y1))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k7 : Hvl) ,
    (forall (S2 : Ty) (wf : (wfTy k7 S2)) ,
      (forall (c : (Cutoff TmVar)) (k8 : Hvl) ,
        (shifthvl_TmVar c k7 k8) -> (wfTy k8 S2)))) := (fun (k7 : Hvl) =>
    (ind_wfTy k7 (fun (S2 : Ty) (wf : (wfTy k7 S2)) =>
      (forall (c : (Cutoff TmVar)) (k8 : Hvl) ,
        (shifthvl_TmVar c k7 k8) -> (wfTy k8 S2))) (fun (y1 : (Index TyVar)) (wfi : (wfindex k7 y1)) (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
      (wfTy_TVar k8 _ (shift_wfindex_TyVar c k7 k8 ins y1 wfi))) (fun (T1 : Ty) (wf : (wfTy k7 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k7 T2)) IHT2 (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
      (wfTy_TArr k8 (IHT1 c k8 (weaken_shifthvl_TmVar H0 ins)) (IHT2 c k8 (weaken_shifthvl_TmVar H0 ins)))))).
  Definition tshift_wfTy : (forall (k7 : Hvl) ,
    (forall (S2 : Ty) (wf : (wfTy k7 S2)) ,
      (forall (c : (Cutoff TyVar)) (k8 : Hvl) ,
        (shifthvl_TyVar c k7 k8) -> (wfTy k8 (tshiftTy c S2))))) := (fun (k7 : Hvl) =>
    (ind_wfTy k7 (fun (S2 : Ty) (wf : (wfTy k7 S2)) =>
      (forall (c : (Cutoff TyVar)) (k8 : Hvl) ,
        (shifthvl_TyVar c k7 k8) -> (wfTy k8 (tshiftTy c S2)))) (fun (y1 : (Index TyVar)) (wfi : (wfindex k7 y1)) (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
      (wfTy_TVar k8 _ (tshift_wfindex_TyVar c k7 k8 ins y1 wfi))) (fun (T1 : Ty) (wf : (wfTy k7 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k7 T2)) IHT2 (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
      (wfTy_TArr k8 (IHT1 c k8 (weaken_shifthvl_TyVar H0 ins)) (IHT2 c k8 (weaken_shifthvl_TyVar H0 ins)))))).
  Definition shift_wfPat : (forall (k7 : Hvl) ,
    (forall (p11 : Pat) (wf : (wfPat k7 p11)) ,
      (forall (c : (Cutoff TmVar)) (k8 : Hvl) ,
        (shifthvl_TmVar c k7 k8) -> (wfPat k8 p11)))) := (ind_wfPat (fun (k7 : Hvl) (p11 : Pat) (wf : (wfPat k7 p11)) =>
    (forall (c : (Cutoff TmVar)) (k8 : Hvl) ,
      (shifthvl_TmVar c k7 k8) -> (wfPat k8 p11))) (fun (k7 : Hvl) (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
    (wfPat_PVar k8)) (fun (k7 : Hvl) (p1 : Pat) (wf : (wfPat k7 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k7 (appendHvl H0 (bind p1))) p2)) IHp2 (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
    (wfPat_PProp k8 (IHp1 c k8 (weaken_shifthvl_TmVar H0 ins)) (IHp2 (weakenCutoffTmVar c (appendHvl H0 (bind p1))) (appendHvl k8 (appendHvl H0 (bind p1))) (weaken_shifthvl_TmVar (appendHvl H0 (bind p1)) ins))))).
  Definition tshift_wfPat : (forall (k7 : Hvl) ,
    (forall (p11 : Pat) (wf : (wfPat k7 p11)) ,
      (forall (c : (Cutoff TyVar)) (k8 : Hvl) ,
        (shifthvl_TyVar c k7 k8) -> (wfPat k8 p11)))) := (ind_wfPat (fun (k7 : Hvl) (p11 : Pat) (wf : (wfPat k7 p11)) =>
    (forall (c : (Cutoff TyVar)) (k8 : Hvl) ,
      (shifthvl_TyVar c k7 k8) -> (wfPat k8 p11))) (fun (k7 : Hvl) (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
    (wfPat_PVar k8)) (fun (k7 : Hvl) (p1 : Pat) (wf : (wfPat k7 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k7 (appendHvl H0 (bind p1))) p2)) IHp2 (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
    (wfPat_PProp k8 (IHp1 c k8 (weaken_shifthvl_TyVar H0 ins)) (IHp2 (weakenCutoffTyVar c (appendHvl H0 (bind p1))) (appendHvl k8 (appendHvl H0 (bind p1))) (weaken_shifthvl_TyVar (appendHvl H0 (bind p1)) ins))))).
  Definition shift_wfTm : (forall (k7 : Hvl) ,
    (forall (s3 : Tm) (wf : (wfTm k7 s3)) ,
      (forall (c : (Cutoff TmVar)) (k8 : Hvl) ,
        (shifthvl_TmVar c k7 k8) -> (wfTm k8 (shiftTm c s3))))) := (ind_wfTm (fun (k7 : Hvl) (s3 : Tm) (wf : (wfTm k7 s3)) =>
    (forall (c : (Cutoff TmVar)) (k8 : Hvl) ,
      (shifthvl_TmVar c k7 k8) -> (wfTm k8 (shiftTm c s3)))) (fun (k7 : Hvl) (x6 : (Index TmVar)) (wfi : (wfindex k7 x6)) (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
    (wfTm_Var k8 _ (shift_wfindex_TmVar c k7 k8 ins x6 wfi))) (fun (k7 : Hvl) (t1 : Tm) (wf : (wfTm k7 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k7 t2)) IHt2 (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
    (wfTm_App k8 (IHt1 c k8 (weaken_shifthvl_TmVar H0 ins)) (IHt2 c k8 (weaken_shifthvl_TmVar H0 ins)))) (fun (k7 : Hvl) (T : Ty) (wf : (wfTy k7 T)) (t : Tm) (wf0 : (wfTm (HS TmVar k7) t)) IHt (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
    (wfTm_Lam k8 (shift_wfTy k7 T wf c k8 (weaken_shifthvl_TmVar H0 ins)) (IHt (CS c) (HS TmVar k8) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k7 : Hvl) (p : Pat) (wf : (wfPat k7 p)) (t1 : Tm) (wf0 : (wfTm k7 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (appendHvl k7 (appendHvl H0 (bind p))) t2)) IHt2 (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
    (wfTm_Let k8 (shift_wfPat k7 p wf c k8 (weaken_shifthvl_TmVar H0 ins)) (IHt1 c k8 (weaken_shifthvl_TmVar H0 ins)) (IHt2 (weakenCutoffTmVar c (appendHvl H0 (bind p))) (appendHvl k8 (appendHvl H0 (bind p))) (weaken_shifthvl_TmVar (appendHvl H0 (bind p)) ins))))).
  Definition tshift_wfTm : (forall (k7 : Hvl) ,
    (forall (s3 : Tm) (wf : (wfTm k7 s3)) ,
      (forall (c : (Cutoff TyVar)) (k8 : Hvl) ,
        (shifthvl_TyVar c k7 k8) -> (wfTm k8 (tshiftTm c s3))))) := (ind_wfTm (fun (k7 : Hvl) (s3 : Tm) (wf : (wfTm k7 s3)) =>
    (forall (c : (Cutoff TyVar)) (k8 : Hvl) ,
      (shifthvl_TyVar c k7 k8) -> (wfTm k8 (tshiftTm c s3)))) (fun (k7 : Hvl) (x6 : (Index TmVar)) (wfi : (wfindex k7 x6)) (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
    (wfTm_Var k8 _ (tshift_wfindex_TmVar c k7 k8 ins x6 wfi))) (fun (k7 : Hvl) (t1 : Tm) (wf : (wfTm k7 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k7 t2)) IHt2 (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
    (wfTm_App k8 (IHt1 c k8 (weaken_shifthvl_TyVar H0 ins)) (IHt2 c k8 (weaken_shifthvl_TyVar H0 ins)))) (fun (k7 : Hvl) (T : Ty) (wf : (wfTy k7 T)) (t : Tm) (wf0 : (wfTm (HS TmVar k7) t)) IHt (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
    (wfTm_Lam k8 (tshift_wfTy k7 T wf c k8 (weaken_shifthvl_TyVar H0 ins)) (IHt c (HS TmVar k8) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k7 : Hvl) (p : Pat) (wf : (wfPat k7 p)) (t1 : Tm) (wf0 : (wfTm k7 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (appendHvl k7 (appendHvl H0 (bind p))) t2)) IHt2 (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
    (wfTm_Let k8 (tshift_wfPat k7 p wf c k8 (weaken_shifthvl_TyVar H0 ins)) (IHt1 c k8 (weaken_shifthvl_TyVar H0 ins)) (IHt2 (weakenCutoffTyVar c (appendHvl H0 (bind p))) (appendHvl k8 (appendHvl H0 (bind p))) (weaken_shifthvl_TyVar (appendHvl H0 (bind p)) ins))))).
  Fixpoint weaken_wfTy (k7 : Hvl) {struct k7} :
  (forall (k8 : Hvl) (S2 : Ty) (wf : (wfTy k8 S2)) ,
    (wfTy (appendHvl k8 k7) (weakenTy S2 k7))) :=
    match k7 return (forall (k8 : Hvl) (S2 : Ty) (wf : (wfTy k8 S2)) ,
      (wfTy (appendHvl k8 k7) (weakenTy S2 k7))) with
      | (H0) => (fun (k8 : Hvl) (S2 : Ty) (wf : (wfTy k8 S2)) =>
        wf)
      | (HS TmVar k7) => (fun (k8 : Hvl) (S2 : Ty) (wf : (wfTy k8 S2)) =>
        (shift_wfTy (appendHvl k8 k7) (weakenTy S2 k7) (weaken_wfTy k7 k8 S2 wf) C0 (HS TmVar (appendHvl k8 k7)) (shifthvl_TmVar_here (appendHvl k8 k7))))
      | (HS TyVar k7) => (fun (k8 : Hvl) (S2 : Ty) (wf : (wfTy k8 S2)) =>
        (tshift_wfTy (appendHvl k8 k7) (weakenTy S2 k7) (weaken_wfTy k7 k8 S2 wf) C0 (HS TyVar (appendHvl k8 k7)) (shifthvl_TyVar_here (appendHvl k8 k7))))
    end.
  Fixpoint weaken_wfPat (k7 : Hvl) {struct k7} :
  (forall (k8 : Hvl) (p11 : Pat) (wf : (wfPat k8 p11)) ,
    (wfPat (appendHvl k8 k7) (weakenPat p11 k7))) :=
    match k7 return (forall (k8 : Hvl) (p11 : Pat) (wf : (wfPat k8 p11)) ,
      (wfPat (appendHvl k8 k7) (weakenPat p11 k7))) with
      | (H0) => (fun (k8 : Hvl) (p11 : Pat) (wf : (wfPat k8 p11)) =>
        wf)
      | (HS TmVar k7) => (fun (k8 : Hvl) (p11 : Pat) (wf : (wfPat k8 p11)) =>
        (shift_wfPat (appendHvl k8 k7) (weakenPat p11 k7) (weaken_wfPat k7 k8 p11 wf) C0 (HS TmVar (appendHvl k8 k7)) (shifthvl_TmVar_here (appendHvl k8 k7))))
      | (HS TyVar k7) => (fun (k8 : Hvl) (p11 : Pat) (wf : (wfPat k8 p11)) =>
        (tshift_wfPat (appendHvl k8 k7) (weakenPat p11 k7) (weaken_wfPat k7 k8 p11 wf) C0 (HS TyVar (appendHvl k8 k7)) (shifthvl_TyVar_here (appendHvl k8 k7))))
    end.
  Fixpoint weaken_wfTm (k7 : Hvl) {struct k7} :
  (forall (k8 : Hvl) (s3 : Tm) (wf : (wfTm k8 s3)) ,
    (wfTm (appendHvl k8 k7) (weakenTm s3 k7))) :=
    match k7 return (forall (k8 : Hvl) (s3 : Tm) (wf : (wfTm k8 s3)) ,
      (wfTm (appendHvl k8 k7) (weakenTm s3 k7))) with
      | (H0) => (fun (k8 : Hvl) (s3 : Tm) (wf : (wfTm k8 s3)) =>
        wf)
      | (HS TmVar k7) => (fun (k8 : Hvl) (s3 : Tm) (wf : (wfTm k8 s3)) =>
        (shift_wfTm (appendHvl k8 k7) (weakenTm s3 k7) (weaken_wfTm k7 k8 s3 wf) C0 (HS TmVar (appendHvl k8 k7)) (shifthvl_TmVar_here (appendHvl k8 k7))))
      | (HS TyVar k7) => (fun (k8 : Hvl) (s3 : Tm) (wf : (wfTm k8 s3)) =>
        (tshift_wfTm (appendHvl k8 k7) (weakenTm s3 k7) (weaken_wfTm k7 k8 s3 wf) C0 (HS TyVar (appendHvl k8 k7)) (shifthvl_TyVar_here (appendHvl k8 k7))))
    end.
End ShiftWellFormed.
Lemma wfTy_cast  :
  (forall (k11 : Hvl) (S3 : Ty) (k12 : Hvl) (S4 : Ty) ,
    (k11 = k12) -> (S3 = S4) -> (wfTy k11 S3) -> (wfTy k12 S4)).
Proof.
  congruence .
Qed.
Lemma wfPat_cast  :
  (forall (k11 : Hvl) (p12 : Pat) (k12 : Hvl) (p13 : Pat) ,
    (k11 = k12) -> (p12 = p13) -> (wfPat k11 p12) -> (wfPat k12 p13)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k11 : Hvl) (s3 : Tm) (k12 : Hvl) (s4 : Tm) ,
    (k11 = k12) -> (s3 = s4) -> (wfTm k11 s3) -> (wfTm k12 s4)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_wfindex_TmVar shift_wfindex_TyVar tshift_wfindex_TmVar tshift_wfindex_TyVar : infra.
 Hint Resolve shift_wfindex_TmVar shift_wfindex_TyVar tshift_wfindex_TmVar tshift_wfindex_TyVar : shift.
 Hint Resolve shift_wfindex_TmVar shift_wfindex_TyVar tshift_wfindex_TmVar tshift_wfindex_TyVar : shift_wf.
 Hint Resolve shift_wfindex_TmVar shift_wfindex_TyVar tshift_wfindex_TmVar tshift_wfindex_TyVar : wf.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : infra.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : shift.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : shift_wf.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : wf.
 Hint Constructors shifthvl_TmVar shifthvl_TyVar : infra.
 Hint Constructors shifthvl_TmVar shifthvl_TyVar : shift.
 Hint Constructors shifthvl_TmVar shifthvl_TyVar : shift_wf.
 Hint Constructors shifthvl_TmVar shifthvl_TyVar : wf.
 Hint Resolve weaken_shifthvl_TmVar weaken_shifthvl_TyVar : infra.
 Hint Resolve weaken_shifthvl_TmVar weaken_shifthvl_TyVar : shift.
 Hint Resolve weaken_shifthvl_TmVar weaken_shifthvl_TyVar : shift_wf.
 Hint Resolve weaken_shifthvl_TmVar weaken_shifthvl_TyVar : weaken.
 Hint Resolve weaken_shifthvl_TmVar weaken_shifthvl_TyVar : wf.
Section SubstWellFormed.
  Inductive substhvl_TmVar (k7 : Hvl) : (forall (d : (Trace TmVar)) (k8 : Hvl) (k9 : Hvl) ,
    Prop) :=
    | substhvl_TmVar_here :
        (substhvl_TmVar k7 X0 (HS TmVar k7) k7)
    | substhvl_TmVar_there_TmVar
        {d : (Trace TmVar)} {k8 : Hvl}
        {k9 : Hvl} :
        (substhvl_TmVar k7 d k8 k9) -> (substhvl_TmVar k7 (XS TmVar d) (HS TmVar k8) (HS TmVar k9))
    | substhvl_TmVar_there_TyVar
        {d : (Trace TmVar)} {k8 : Hvl}
        {k9 : Hvl} :
        (substhvl_TmVar k7 d k8 k9) -> (substhvl_TmVar k7 (XS TyVar d) (HS TyVar k8) (HS TyVar k9)).
  Inductive substhvl_TyVar (k7 : Hvl) : (forall (d : (Trace TyVar)) (k8 : Hvl) (k9 : Hvl) ,
    Prop) :=
    | substhvl_TyVar_here :
        (substhvl_TyVar k7 X0 (HS TyVar k7) k7)
    | substhvl_TyVar_there_TmVar
        {d : (Trace TyVar)} {k8 : Hvl}
        {k9 : Hvl} :
        (substhvl_TyVar k7 d k8 k9) -> (substhvl_TyVar k7 (XS TmVar d) (HS TmVar k8) (HS TmVar k9))
    | substhvl_TyVar_there_TyVar
        {d : (Trace TyVar)} {k8 : Hvl}
        {k9 : Hvl} :
        (substhvl_TyVar k7 d k8 k9) -> (substhvl_TyVar k7 (XS TyVar d) (HS TyVar k8) (HS TyVar k9)).
  Lemma weaken_substhvl_TmVar  :
    (forall {k8 : Hvl} (k7 : Hvl) {d : (Trace TmVar)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_TmVar k8 d k9 k10) -> (substhvl_TmVar k8 (weakenTrace d k7) (appendHvl k9 k7) (appendHvl k10 k7))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_TyVar  :
    (forall {k8 : Hvl} (k7 : Hvl) {d : (Trace TyVar)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_TyVar k8 d k9 k10) -> (substhvl_TyVar k8 (weakenTrace d k7) (appendHvl k9 k7) (appendHvl k10 k7))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_TmVar_wfindex_TmVar {k11 : Hvl} {s3 : Tm} (wft : (wfTm k11 s3)) :
    (forall {d : (Trace TmVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TmVar k11 d k12 k13) -> (forall {x6 : (Index TmVar)} ,
        (wfindex k12 x6) -> (wfTm k13 (subst_TmVar_Index d s3 x6)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TyVar_wfindex_TyVar {k11 : Hvl} {S3 : Ty} (wft : (wfTy k11 S3)) :
    (forall {d : (Trace TyVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TyVar k11 d k12 k13) -> (forall {y1 : (Index TyVar)} ,
        (wfindex k12 y1) -> (wfTy k13 (subst_TyVar_Index d S3 y1)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TmVar_wfindex_TyVar {k11 : Hvl} :
    (forall {d : (Trace TmVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TmVar k11 d k12 k13) -> (forall {y1 : (Index TyVar)} ,
        (wfindex k12 y1) -> (wfindex k13 y1))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_TyVar_wfindex_TmVar {k11 : Hvl} :
    (forall {d : (Trace TyVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TyVar k11 d k12 k13) -> (forall {x6 : (Index TmVar)} ,
        (wfindex k12 x6) -> (wfindex k13 x6))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_TmVar_wfTy {k11 : Hvl} : (forall (k12 : Hvl) ,
    (forall (S3 : Ty) (wf0 : (wfTy k12 S3)) ,
      (forall {d : (Trace TmVar)} {k13 : Hvl} ,
        (substhvl_TmVar k11 d k12 k13) -> (wfTy k13 S3)))) := (fun (k12 : Hvl) =>
    (ind_wfTy k12 (fun (S3 : Ty) (wf0 : (wfTy k12 S3)) =>
      (forall {d : (Trace TmVar)} {k13 : Hvl} ,
        (substhvl_TmVar k11 d k12 k13) -> (wfTy k13 S3))) (fun {y1 : (Index TyVar)} (wfi : (wfindex k12 y1)) {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
      (wfTy_TVar k13 _ (substhvl_TmVar_wfindex_TyVar del wfi))) (fun (T1 : Ty) (wf0 : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k12 T2)) IHT2 {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
      (wfTy_TArr k13 (IHT1 (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)) (IHT2 (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)))))).
  Definition substhvl_TyVar_wfTy {k11 : Hvl} {S3 : Ty} (wf : (wfTy k11 S3)) : (forall (k12 : Hvl) ,
    (forall (S4 : Ty) (wf0 : (wfTy k12 S4)) ,
      (forall {d : (Trace TyVar)} {k13 : Hvl} ,
        (substhvl_TyVar k11 d k12 k13) -> (wfTy k13 (subst_TyVar_Ty d S3 S4))))) := (fun (k12 : Hvl) =>
    (ind_wfTy k12 (fun (S4 : Ty) (wf0 : (wfTy k12 S4)) =>
      (forall {d : (Trace TyVar)} {k13 : Hvl} ,
        (substhvl_TyVar k11 d k12 k13) -> (wfTy k13 (subst_TyVar_Ty d S3 S4)))) (fun {y1 : (Index TyVar)} (wfi : (wfindex k12 y1)) {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
      (substhvl_TyVar_wfindex_TyVar wf del wfi)) (fun (T1 : Ty) (wf0 : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k12 T2)) IHT2 {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
      (wfTy_TArr k13 (IHT1 (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)) (IHT2 (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)))))).
  Definition substhvl_TmVar_wfPat {k11 : Hvl} : (forall (k12 : Hvl) ,
    (forall (p12 : Pat) (wf0 : (wfPat k12 p12)) ,
      (forall {d : (Trace TmVar)} {k13 : Hvl} ,
        (substhvl_TmVar k11 d k12 k13) -> (wfPat k13 p12)))) := (ind_wfPat (fun (k12 : Hvl) (p12 : Pat) (wf0 : (wfPat k12 p12)) =>
    (forall {d : (Trace TmVar)} {k13 : Hvl} ,
      (substhvl_TmVar k11 d k12 k13) -> (wfPat k13 p12))) (fun (k12 : Hvl) {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfPat_PVar k13)) (fun (k12 : Hvl) (p1 : Pat) (wf0 : (wfPat k12 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k12 (appendHvl H0 (bind p1))) p2)) IHp2 {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfPat_PProp k13 (IHp1 (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)) (IHp2 (weakenTrace d (appendHvl H0 (bind p1))) (appendHvl k13 (appendHvl H0 (bind p1))) (weaken_substhvl_TmVar (appendHvl H0 (bind p1)) del))))).
  Definition substhvl_TyVar_wfPat {k11 : Hvl} : (forall (k12 : Hvl) ,
    (forall (p12 : Pat) (wf0 : (wfPat k12 p12)) ,
      (forall {d : (Trace TyVar)} {k13 : Hvl} ,
        (substhvl_TyVar k11 d k12 k13) -> (wfPat k13 p12)))) := (ind_wfPat (fun (k12 : Hvl) (p12 : Pat) (wf0 : (wfPat k12 p12)) =>
    (forall {d : (Trace TyVar)} {k13 : Hvl} ,
      (substhvl_TyVar k11 d k12 k13) -> (wfPat k13 p12))) (fun (k12 : Hvl) {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfPat_PVar k13)) (fun (k12 : Hvl) (p1 : Pat) (wf0 : (wfPat k12 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k12 (appendHvl H0 (bind p1))) p2)) IHp2 {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfPat_PProp k13 (IHp1 (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)) (IHp2 (weakenTrace d (appendHvl H0 (bind p1))) (appendHvl k13 (appendHvl H0 (bind p1))) (weaken_substhvl_TyVar (appendHvl H0 (bind p1)) del))))).
  Definition substhvl_TmVar_wfTm {k11 : Hvl} {s3 : Tm} (wf : (wfTm k11 s3)) : (forall (k12 : Hvl) ,
    (forall (s4 : Tm) (wf0 : (wfTm k12 s4)) ,
      (forall {d : (Trace TmVar)} {k13 : Hvl} ,
        (substhvl_TmVar k11 d k12 k13) -> (wfTm k13 (subst_TmVar_Tm d s3 s4))))) := (ind_wfTm (fun (k12 : Hvl) (s4 : Tm) (wf0 : (wfTm k12 s4)) =>
    (forall {d : (Trace TmVar)} {k13 : Hvl} ,
      (substhvl_TmVar k11 d k12 k13) -> (wfTm k13 (subst_TmVar_Tm d s3 s4)))) (fun (k12 : Hvl) {x6 : (Index TmVar)} (wfi : (wfindex k12 x6)) {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (substhvl_TmVar_wfindex_TmVar wf del wfi)) (fun (k12 : Hvl) (t1 : Tm) (wf0 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k12 t2)) IHt2 {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfTm_App k13 (IHt1 (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)))) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) (t : Tm) (wf1 : (wfTm (HS TmVar k12) t)) IHt {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfTm_Lam k13 (substhvl_TmVar_wfTy k12 T wf0 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k12 : Hvl) (p : Pat) (wf0 : (wfPat k12 p)) (t1 : Tm) (wf1 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf2 : (wfTm (appendHvl k12 (appendHvl H0 (bind p))) t2)) IHt2 {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfTm_Let k13 (substhvl_TmVar_wfPat k12 p wf0 (weaken_substhvl_TmVar H0 del)) (IHt1 (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d (appendHvl H0 (bind p))) (appendHvl k13 (appendHvl H0 (bind p))) (weaken_substhvl_TmVar (appendHvl H0 (bind p)) del))))).
  Definition substhvl_TyVar_wfTm {k11 : Hvl} {S3 : Ty} (wf : (wfTy k11 S3)) : (forall (k12 : Hvl) ,
    (forall (s3 : Tm) (wf0 : (wfTm k12 s3)) ,
      (forall {d : (Trace TyVar)} {k13 : Hvl} ,
        (substhvl_TyVar k11 d k12 k13) -> (wfTm k13 (subst_TyVar_Tm d S3 s3))))) := (ind_wfTm (fun (k12 : Hvl) (s3 : Tm) (wf0 : (wfTm k12 s3)) =>
    (forall {d : (Trace TyVar)} {k13 : Hvl} ,
      (substhvl_TyVar k11 d k12 k13) -> (wfTm k13 (subst_TyVar_Tm d S3 s3)))) (fun (k12 : Hvl) {x6 : (Index TmVar)} (wfi : (wfindex k12 x6)) {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfTm_Var k13 _ (substhvl_TyVar_wfindex_TmVar del wfi))) (fun (k12 : Hvl) (t1 : Tm) (wf0 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k12 t2)) IHt2 {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfTm_App k13 (IHt1 (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)) (IHt2 (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)))) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) (t : Tm) (wf1 : (wfTm (HS TmVar k12) t)) IHt {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfTm_Lam k13 (substhvl_TyVar_wfTy wf k12 T wf0 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k12 : Hvl) (p : Pat) (wf0 : (wfPat k12 p)) (t1 : Tm) (wf1 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf2 : (wfTm (appendHvl k12 (appendHvl H0 (bind p))) t2)) IHt2 {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfTm_Let k13 (substhvl_TyVar_wfPat k12 p wf0 (weaken_substhvl_TyVar H0 del)) (IHt1 (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)) (IHt2 (weakenTrace d (appendHvl H0 (bind p))) (appendHvl k13 (appendHvl H0 (bind p))) (weaken_substhvl_TyVar (appendHvl H0 (bind p)) del))))).
End SubstWellFormed.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : infra.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : subst.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : subst_wf.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : wf.
 Hint Resolve substhvl_TmVar_wfPat substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfPat substhvl_TyVar_wfTm substhvl_TyVar_wfTy : infra.
 Hint Resolve substhvl_TmVar_wfPat substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfPat substhvl_TyVar_wfTm substhvl_TyVar_wfTy : subst.
 Hint Resolve substhvl_TmVar_wfPat substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfPat substhvl_TyVar_wfTm substhvl_TyVar_wfTy : subst_wf.
 Hint Resolve substhvl_TmVar_wfPat substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfPat substhvl_TyVar_wfTm substhvl_TyVar_wfTy : wf.
 Hint Constructors substhvl_TmVar substhvl_TyVar : infra.
 Hint Constructors substhvl_TmVar substhvl_TyVar : subst.
 Hint Constructors substhvl_TmVar substhvl_TyVar : subst_wf.
 Hint Constructors substhvl_TmVar substhvl_TyVar : wf.
Fixpoint subhvl_TmVar (k11 : Hvl) {struct k11} :
Prop :=
  match k11 with
    | (H0) => True
    | (HS a k11) => match a with
      | (TmVar) => (subhvl_TmVar k11)
      | _ => False
    end
  end.
Lemma subhvl_TmVar_append  :
  (forall (k11 : Hvl) (k12 : Hvl) ,
    (subhvl_TmVar k11) -> (subhvl_TmVar k12) -> (subhvl_TmVar (appendHvl k11 k12))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_TmVar_append : infra.
 Hint Resolve subhvl_TmVar_append : wf.
Lemma wfPat_strengthen_subhvl_TmVar  :
  (forall (k8 : Hvl) (k7 : Hvl) (p11 : Pat) ,
    (subhvl_TmVar k8) -> (wfPat (appendHvl k7 k8) (weakenPat p11 k8)) -> (wfPat k7 p11)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfTy_strengthen_subhvl_TmVar  :
  (forall (k10 : Hvl) (k9 : Hvl) (S2 : Ty) ,
    (subhvl_TmVar k10) -> (wfTy (appendHvl k9 k10) (weakenTy S2 k10)) -> (wfTy k9 S2)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H26 : (wfPat (appendHvl _ _) (weakenPat _ _)) |- _ => apply (wfPat_strengthen_subhvl_TmVar) in H26
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H27 : (wfTy (appendHvl _ _) (weakenTy _ _)) |- _ => apply (wfTy_strengthen_subhvl_TmVar) in H27
end : infra wf.
Section Context.
  Inductive Ctx : Type :=
    | empty 
    | evar (G : Ctx) (T : Ty)
    | etvar (G : Ctx).
  Fixpoint appendCtx (G : Ctx) (G0 : Ctx) :
  Ctx :=
    match G0 with
      | (empty) => G
      | (evar G1 T) => (evar (appendCtx G G1) T)
      | (etvar G1) => (etvar (appendCtx G G1))
    end.
  Fixpoint domainCtx (G : Ctx) :
  Hvl :=
    match G with
      | (empty) => H0
      | (evar G0 T) => (HS TmVar (domainCtx G0))
      | (etvar G0) => (HS TyVar (domainCtx G0))
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
  Fixpoint shiftCtx (c : (Cutoff TmVar)) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shiftCtx c G0) T)
      | (etvar G0) => (etvar (shiftCtx c G0))
    end.
  Fixpoint tshiftCtx (c : (Cutoff TyVar)) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tshiftCtx c G0) (tshiftTy (weakenCutoffTyVar c (domainCtx G0)) T))
      | (etvar G0) => (etvar (tshiftCtx c G0))
    end.
  Fixpoint weakenCtx (G : Ctx) (k11 : Hvl) {struct k11} :
  Ctx :=
    match k11 with
      | (H0) => G
      | (HS TmVar k11) => (weakenCtx G k11)
      | (HS TyVar k11) => (tshiftCtx C0 (weakenCtx G k11))
    end.
  Fixpoint subst_TmVar_Ctx (d : (Trace TmVar)) (s3 : Tm) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (subst_TmVar_Ctx d s3 G0) T)
      | (etvar G0) => (etvar (subst_TmVar_Ctx d s3 G0))
    end.
  Fixpoint subst_TyVar_Ctx (d : (Trace TyVar)) (S3 : Ty) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (subst_TyVar_Ctx d S3 G0) (subst_TyVar_Ty (weakenTrace d (domainCtx G0)) S3 T))
      | (etvar G0) => (etvar (subst_TyVar_Ctx d S3 G0))
    end.
  Lemma domainCtx_shiftCtx  :
    (forall (c : (Cutoff TmVar)) (G : Ctx) ,
      ((domainCtx (shiftCtx c G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainCtx_tshiftCtx  :
    (forall (c : (Cutoff TyVar)) (G : Ctx) ,
      ((domainCtx (tshiftCtx c G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainCtx_subst_TmVar_Ctx  :
    (forall (d : (Trace TmVar)) (s3 : Tm) (G : Ctx) ,
      ((domainCtx (subst_TmVar_Ctx d s3 G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainCtx_subst_TyVar_Ctx  :
    (forall (d : (Trace TyVar)) (S3 : Ty) (G : Ctx) ,
      ((domainCtx (subst_TyVar_Ctx d S3 G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainCtx_appendCtx : interaction.
 Hint Rewrite domainCtx_appendCtx : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shiftCtx_appendCtx  :
      (forall (c : (Cutoff TmVar)) (G : Ctx) (G0 : Ctx) ,
        ((shiftCtx c (appendCtx G G0)) = (appendCtx (shiftCtx c G) (shiftCtx (weakenCutoffTmVar c (domainCtx G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma tshiftCtx_appendCtx  :
      (forall (c : (Cutoff TyVar)) (G : Ctx) (G0 : Ctx) ,
        ((tshiftCtx c (appendCtx G G0)) = (appendCtx (tshiftCtx c G) (tshiftCtx (weakenCutoffTyVar c (domainCtx G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma subst_TmVar_Ctx_appendCtx  :
      (forall (d : (Trace TmVar)) (s3 : Tm) (G : Ctx) (G0 : Ctx) ,
        ((subst_TmVar_Ctx d s3 (appendCtx G G0)) = (appendCtx (subst_TmVar_Ctx d s3 G) (subst_TmVar_Ctx (weakenTrace d (domainCtx G)) s3 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma subst_TyVar_Ctx_appendCtx  :
      (forall (d : (Trace TyVar)) (S3 : Ty) (G : Ctx) (G0 : Ctx) ,
        ((subst_TyVar_Ctx d S3 (appendCtx G G0)) = (appendCtx (subst_TyVar_Ctx d S3 G) (subst_TyVar_Ctx (weakenTrace d (domainCtx G)) S3 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S3 : Ty) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenTy (weakenTy S3 k11) k12) = (weakenTy S3 (appendHvl k11 k12)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenPat_append  :
    (forall (p12 : Pat) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenPat (weakenPat p12 k11) k12) = (weakenPat p12 (appendHvl k11 k12)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s3 : Tm) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenTm (weakenTm s3 k11) k12) = (weakenTm s3 (appendHvl k11 k12)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Ctx -> (Index TmVar) -> Ty -> Prop :=
      | lookup_evar_here {G : Ctx}
          (T3 : Ty) :
          (wfTy (domainCtx G) T3) -> (lookup_evar (evar G T3) I0 T3)
      | lookup_evar_there_evar
          {G : Ctx} {x6 : (Index TmVar)}
          (T4 : Ty) (T5 : Ty) :
          (lookup_evar G x6 T4) -> (lookup_evar (evar G T5) (IS x6) T4)
      | lookup_evar_there_etvar
          {G : Ctx} {x6 : (Index TmVar)}
          (T4 : Ty) :
          (lookup_evar G x6 T4) -> (lookup_evar (etvar G) x6 (tshiftTy C0 T4)).
    Inductive lookup_etvar : Ctx -> (Index TyVar) -> Prop :=
      | lookup_etvar_here {G : Ctx}
          : (lookup_etvar (etvar G) I0)
      | lookup_etvar_there_evar
          {G : Ctx} {y1 : (Index TyVar)}
          (T4 : Ty) :
          (lookup_etvar G y1) -> (lookup_etvar (evar G T4) y1)
      | lookup_etvar_there_etvar
          {G : Ctx} {y1 : (Index TyVar)} :
          (lookup_etvar G y1) -> (lookup_etvar (etvar G) (IS y1)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Ctx) (T4 : Ty) (T5 : Ty) ,
        (lookup_evar (evar G T4) I0 T5) -> (T4 = T5)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Ctx} {x6 : (Index TmVar)} ,
        (forall (T4 : Ty) ,
          (lookup_evar G x6 T4) -> (forall (T5 : Ty) ,
            (lookup_evar G x6 T5) -> (T4 = T5)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Ctx} {x6 : (Index TmVar)} (T4 : Ty) ,
        (lookup_evar G x6 T4) -> (wfTy (domainCtx G) T4)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Ctx} (G0 : Ctx) {x6 : (Index TmVar)} (T4 : Ty) ,
        (lookup_evar G x6 T4) -> (lookup_evar (appendCtx G G0) (weakenIndexTmVar x6 (domainCtx G0)) (weakenTy T4 (domainCtx G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Ctx} (G0 : Ctx) {y1 : (Index TyVar)} ,
        (lookup_etvar G y1) -> (lookup_etvar (appendCtx G G0) (weakenIndexTyVar y1 (domainCtx G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Ctx} {x6 : (Index TmVar)} (T6 : Ty) ,
        (lookup_evar G x6 T6) -> (wfindex (domainCtx G) x6)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Ctx} {y1 : (Index TyVar)} ,
        (lookup_etvar G y1) -> (wfindex (domainCtx G) y1)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff TmVar) -> Ctx -> Ctx -> Prop :=
    | shift_evar_here {G : Ctx}
        {T4 : Ty} :
        (shift_evar C0 G (evar G T4))
    | shiftevar_there_evar
        {c : (Cutoff TmVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_evar c G G0) -> (shift_evar (CS c) (evar G T) (evar G0 T))
    | shiftevar_there_etvar
        {c : (Cutoff TmVar)} {G : Ctx}
        {G0 : Ctx} :
        (shift_evar c G G0) -> (shift_evar c (etvar G) (etvar G0)).
  Lemma weaken_shift_evar  :
    (forall (G : Ctx) {c : (Cutoff TmVar)} {G0 : Ctx} {G1 : Ctx} ,
      (shift_evar c G0 G1) -> (shift_evar (weakenCutoffTmVar c (domainCtx G)) (appendCtx G0 G) (appendCtx G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff TyVar) -> Ctx -> Ctx -> Prop :=
    | shift_etvar_here {G : Ctx} :
        (shift_etvar C0 G (etvar G))
    | shiftetvar_there_evar
        {c : (Cutoff TyVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_etvar c G G0) -> (shift_etvar c (evar G T) (evar G0 (tshiftTy c T)))
    | shiftetvar_there_etvar
        {c : (Cutoff TyVar)} {G : Ctx}
        {G0 : Ctx} :
        (shift_etvar c G G0) -> (shift_etvar (CS c) (etvar G) (etvar G0)).
  Lemma weaken_shift_etvar  :
    (forall (G : Ctx) {c : (Cutoff TyVar)} {G0 : Ctx} {G1 : Ctx} ,
      (shift_etvar c G0 G1) -> (shift_etvar (weakenCutoffTyVar c (domainCtx G)) (appendCtx G0 G) (appendCtx G1 (tshiftCtx c G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_TmVar  :
    (forall {c : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} ,
      (shift_evar c G G0) -> (shifthvl_TmVar c (domainCtx G) (domainCtx G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_etvar_shifthvl_TyVar  :
    (forall {c : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} ,
      (shift_etvar c G G0) -> (shifthvl_TyVar c (domainCtx G) (domainCtx G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Ctx) (T4 : Ty) (s3 : Tm) : (Trace TmVar) -> Ctx -> Ctx -> Prop :=
    | subst_evar_here :
        (subst_evar G T4 s3 X0 (evar G T4) G)
    | subst_evar_there_evar
        {d : (Trace TmVar)} {G0 : Ctx}
        {G1 : Ctx} (T5 : Ty) :
        (subst_evar G T4 s3 d G0 G1) -> (subst_evar G T4 s3 (XS TmVar d) (evar G0 T5) (evar G1 T5))
    | subst_evar_there_etvar
        {d : (Trace TmVar)} {G0 : Ctx}
        {G1 : Ctx} :
        (subst_evar G T4 s3 d G0 G1) -> (subst_evar G T4 s3 (XS TyVar d) (etvar G0) (etvar G1)).
  Lemma weaken_subst_evar {G : Ctx} (T4 : Ty) {s3 : Tm} :
    (forall (G0 : Ctx) {d : (Trace TmVar)} {G1 : Ctx} {G2 : Ctx} ,
      (subst_evar G T4 s3 d G1 G2) -> (subst_evar G T4 s3 (weakenTrace d (domainCtx G0)) (appendCtx G1 G0) (appendCtx G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Ctx) (S3 : Ty) : (Trace TyVar) -> Ctx -> Ctx -> Prop :=
    | subst_etvar_here :
        (subst_etvar G S3 X0 (etvar G) G)
    | subst_etvar_there_evar
        {d : (Trace TyVar)} {G0 : Ctx}
        {G1 : Ctx} (T4 : Ty) :
        (subst_etvar G S3 d G0 G1) -> (subst_etvar G S3 (XS TmVar d) (evar G0 T4) (evar G1 (subst_TyVar_Ty d S3 T4)))
    | subst_etvar_there_etvar
        {d : (Trace TyVar)} {G0 : Ctx}
        {G1 : Ctx} :
        (subst_etvar G S3 d G0 G1) -> (subst_etvar G S3 (XS TyVar d) (etvar G0) (etvar G1)).
  Lemma weaken_subst_etvar {G : Ctx} {S3 : Ty} :
    (forall (G0 : Ctx) {d : (Trace TyVar)} {G1 : Ctx} {G2 : Ctx} ,
      (subst_etvar G S3 d G1 G2) -> (subst_etvar G S3 (weakenTrace d (domainCtx G0)) (appendCtx G1 G0) (appendCtx G2 (subst_TyVar_Ctx d S3 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_TmVar {G : Ctx} {s3 : Tm} (T4 : Ty) :
    (forall {d : (Trace TmVar)} {G0 : Ctx} {G1 : Ctx} ,
      (subst_evar G T4 s3 d G0 G1) -> (substhvl_TmVar (domainCtx G) d (domainCtx G0) (domainCtx G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_TyVar {G : Ctx} {S3 : Ty} :
    (forall {d : (Trace TyVar)} {G0 : Ctx} {G1 : Ctx} ,
      (subst_etvar G S3 d G0 G1) -> (substhvl_TyVar (domainCtx G) d (domainCtx G0) (domainCtx G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
End ContextStuff.
 Hint Rewrite domainCtx_tshiftCtx : interaction.
 Hint Rewrite domainCtx_tshiftCtx : env_domain_shift.
 Hint Rewrite domainCtx_subst_TyVar_Ctx : interaction.
 Hint Rewrite domainCtx_subst_TyVar_Ctx : env_domain_subst.
 Hint Rewrite tshiftCtx_appendCtx : interaction.
 Hint Rewrite tshiftCtx_appendCtx : env_shift_append.
 Hint Rewrite subst_TyVar_Ctx_appendCtx : interaction.
 Hint Rewrite subst_TyVar_Ctx_appendCtx : env_shift_append.
 Hint Constructors lookup_evar lookup_etvar : infra.
 Hint Constructors lookup_evar lookup_etvar : lookup.
 Hint Constructors lookup_evar lookup_etvar : shift.
 Hint Constructors lookup_evar lookup_etvar : subst.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : infra.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : lookup.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : shift.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : weaken.
Lemma weaken_lookup_evar_here  :
  (forall {G : Ctx} (G0 : Ctx) {T4 : Ty} (wf : (wfTy (domainCtx G) T4)) ,
    (lookup_evar (appendCtx (evar G T4) G0) (weakenIndexTmVar I0 (domainCtx G0)) (weakenTy T4 (domainCtx G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Ctx} (G0 : Ctx) ,
    (lookup_etvar (appendCtx (etvar G) G0) (weakenIndexTyVar I0 (domainCtx G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfPat wfTm wfTy : infra.
 Hint Constructors wfPat wfTm wfTy : wf.
 Hint Extern 10 ((wfPat _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H26 : (wfTy _ (TVar _)) |- _ => inversion H26; subst; clear H26
  | H26 : (wfTy _ (TArr _ _)) |- _ => inversion H26; subst; clear H26
end : infra wf.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H26 : (wfPat _ (PVar)) |- _ => inversion H26; subst; clear H26
  | H26 : (wfPat _ (PProp _ _)) |- _ => inversion H26; subst; clear H26
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H26 : (wfTm _ (Var _)) |- _ => inversion H26; subst; clear H26
  | H26 : (wfTm _ (App _ _)) |- _ => inversion H26; subst; clear H26
  | H26 : (wfTm _ (Lam _ _)) |- _ => inversion H26; subst; clear H26
  | H26 : (wfTm _ (Let _ _ _)) |- _ => inversion H26; subst; clear H26
end : infra wf.
 Hint Resolve lookup_evar_wf : infra.
 Hint Resolve lookup_evar_wf : wf.
 Hint Resolve lookup_evar_wfindex lookup_etvar_wfindex : infra.
 Hint Resolve lookup_evar_wfindex lookup_etvar_wfindex : lookup.
 Hint Resolve lookup_evar_wfindex lookup_etvar_wfindex : wf.
 Hint Constructors shift_evar shift_etvar : infra.
 Hint Constructors shift_evar shift_etvar : shift.
 Hint Constructors shift_evar shift_etvar : subst.
 Hint Resolve weaken_shift_evar weaken_shift_etvar : infra.
 Hint Resolve weaken_shift_evar weaken_shift_etvar : shift.
 Hint Resolve shift_evar_shifthvl_TmVar shift_etvar_shifthvl_TyVar : infra.
 Hint Resolve shift_evar_shifthvl_TmVar shift_etvar_shifthvl_TyVar : shift.
 Hint Resolve shift_evar_shifthvl_TmVar shift_etvar_shifthvl_TyVar : shift_wf.
 Hint Resolve shift_evar_shifthvl_TmVar shift_etvar_shifthvl_TyVar : wf.
 Hint Constructors subst_evar subst_etvar : infra.
 Hint Constructors subst_evar subst_etvar : subst.
 Hint Resolve weaken_subst_evar weaken_subst_etvar : infra.
 Hint Resolve weaken_subst_evar weaken_subst_etvar : subst.
 Hint Resolve subst_evar_substhvl_TmVar subst_etvar_substhvl_TyVar : infra.
 Hint Resolve subst_evar_substhvl_TmVar subst_etvar_substhvl_TyVar : subst.
 Hint Resolve subst_evar_substhvl_TmVar subst_etvar_substhvl_TyVar : subst_wf.
 Hint Resolve subst_evar_substhvl_TmVar subst_etvar_substhvl_TyVar : wf.
 Hint Resolve subst_evar_substhvl_TmVar subst_etvar_substhvl_TyVar : substenv_substhvl.
Lemma shift_evar_lookup_evar  :
  (forall {c : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evar c G G0)) {x6 : (Index TmVar)} {T4 : Ty} ,
    (lookup_evar G x6 T4) -> (lookup_evar G0 (shiftIndex c x6) T4)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evar c G G0)) {y1 : (Index TyVar)} ,
    (lookup_etvar G y1) -> (lookup_etvar G0 y1)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_etvar c G G0)) {x6 : (Index TmVar)} {T4 : Ty} ,
    (lookup_evar G x6 T4) -> (lookup_evar G0 x6 (tshiftTy c T4))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_etvar c G G0)) {y1 : (Index TyVar)} ,
    (lookup_etvar G y1) -> (lookup_etvar G0 (tshiftIndex c y1))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Ctx} (T5 : Ty) {s3 : Tm} :
  (forall {d : (Trace TmVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_evar G T5 s3 d G0 G1)) {y1 : (Index TyVar)} ,
    (lookup_etvar G0 y1) -> (lookup_etvar G1 y1)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Ctx} {S3 : Ty} (wf : (wfTy (domainCtx G) S3)) :
  (forall {d : (Trace TyVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_etvar G S3 d G0 G1)) {x6 : (Index TmVar)} (T5 : Ty) ,
    (lookup_evar G0 x6 T5) -> (lookup_evar G1 x6 (subst_TyVar_Ty d S3 T5))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (TVar y1) => 1
    | (TArr T3 T4) => (plus 1 (plus (size_Ty T3) (size_Ty T4)))
  end.
Fixpoint size_Pat (p9 : Pat) {struct p9} :
nat :=
  match p9 with
    | (PVar) => 1
    | (PProp p10 p11) => (plus 1 (plus (size_Pat p10) (size_Pat p11)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (Var x6) => 1
    | (App t4 t5) => (plus 1 (plus (size_Tm t4) (size_Tm t5)))
    | (Lam T3 t6) => (plus 1 (plus (size_Ty T3) (size_Tm t6)))
    | (Let p9 t7 t8) => (plus 1 (plus (size_Pat p9) (plus (size_Tm t7) (size_Tm t8))))
  end.
Fixpoint tshift_size_Ty (S0 : Ty) (c : (Cutoff TyVar)) {struct S0} :
((size_Ty (tshiftTy c S0)) = (size_Ty S0)) :=
  match S0 return ((size_Ty (tshiftTy c S0)) = (size_Ty S0)) with
    | (TVar _) => eq_refl
    | (TArr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c) (tshift_size_Ty T2 c)))
  end.
Fixpoint shift_size_Tm (s : Tm) (c : (Cutoff TmVar)) {struct s} :
((size_Tm (shiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c s)) = (size_Tm s)) with
    | (Var _) => eq_refl
    | (App t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 c)))
    | (Lam T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c))))
    | (Let p t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 (weakenCutoffTmVar c (appendHvl H0 (bind p)))))))
  end.
Fixpoint tshift_size_Tm (s : Tm) (c : (Cutoff TyVar)) {struct s} :
((size_Tm (tshiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (tshiftTm c s)) = (size_Tm s)) with
    | (Var _) => eq_refl
    | (App t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c) (tshift_size_Tm t2 c)))
    | (Lam T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c) (tshift_size_Tm t c)))
    | (Let p t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c) (tshift_size_Tm t2 (weakenCutoffTyVar c (appendHvl H0 (bind p)))))))
  end.
 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
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
 Hint Rewrite <- weakenCutoffTmVar_append weakenCutoffTyVar_append weakenTrace_append weakenPat_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.