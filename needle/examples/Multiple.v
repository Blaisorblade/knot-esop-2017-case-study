Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export Needle.

Local Set Asymmetric Patterns.

Section Namespace.
  Inductive Namespace : Type :=
    | TmVar 
    | TxVar 
    | TyVar .
  Lemma eq_namespace_dec (a1 : Namespace) (b : Namespace) :
    (sumbool (a1 = b) (not (a1 = b))).
  Proof.
    decide equality .
  Defined.
End Namespace.

Section HVarlist.
  Inductive Hvl : Type :=
    | H0 
    | HS (a1 : Namespace) (k : Hvl).
  
  Fixpoint appendHvl (k : Hvl) (k0 : Hvl) {struct k0} :
  Hvl :=
    match k0 with
      | (H0) => k
      | (HS a1 k0) => (HS a1 (appendHvl k k0))
    end.
  
  Lemma appendHvl_assoc  :
    (forall (k : Hvl) (k0 : Hvl) (k1 : Hvl) ,
      ((appendHvl (appendHvl k k0) k1) = (appendHvl k (appendHvl k0 k1)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End HVarlist.

Section Index.
  Inductive Index (a1 : Namespace) : Type :=
    | I0 
    | IS : (Index a1) -> (Index a1).
  
  Global Arguments I0 [a1] .
  Global Arguments IS [a1] _ .
  
  Lemma eq_index_dec {a1 : Namespace} (i : (Index a1)) (j : (Index a1)) :
    (sumbool (i = j) (not (i = j))).
  Proof.
    decide equality .
  Qed.
  
  Fixpoint weakenIndexTmVar (x3 : (Index TmVar)) (k : Hvl) {struct k} :
  (Index TmVar) :=
    match k with
      | (H0) => x3
      | (HS a1 k) => match a1 with
        | (TmVar) => (IS (weakenIndexTmVar x3 k))
        | _ => (weakenIndexTmVar x3 k)
      end
    end.
  Fixpoint weakenIndexTxVar (a2 : (Index TxVar)) (k : Hvl) {struct k} :
  (Index TxVar) :=
    match k with
      | (H0) => a2
      | (HS a1 k) => match a1 with
        | (TxVar) => (IS (weakenIndexTxVar a2 k))
        | _ => (weakenIndexTxVar a2 k)
      end
    end.
  Fixpoint weakenIndexTyVar (X7 : (Index TyVar)) (k : Hvl) {struct k} :
  (Index TyVar) :=
    match k with
      | (H0) => X7
      | (HS a1 k) => match a1 with
        | (TyVar) => (IS (weakenIndexTyVar X7 k))
        | _ => (weakenIndexTyVar X7 k)
      end
    end.
  Lemma weakenIndexTmVar_append  :
    (forall (x3 : (Index TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTmVar (weakenIndexTmVar x3 k) k0) = (weakenIndexTmVar x3 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexTxVar_append  :
    (forall (a1 : (Index TxVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTxVar (weakenIndexTxVar a1 k) k0) = (weakenIndexTxVar a1 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexTyVar_append  :
    (forall (X7 : (Index TyVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTyVar (weakenIndexTyVar X7 k) k0) = (weakenIndexTyVar X7 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Ty : Set :=
    | TVar (X : (Index TyVar))
    | TArr (T1 : Ty) (T2 : Ty)
    | TAll (T : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Tm : Set :=
    | Var (x : (Index TmVar))
    | XVar (a : (Index TxVar))
    | Abs (T : Ty) (t : Tm)
    | App (t1 : Tm) (t2 : Tm)
    | TAbs (t : Tm)
    | TApp (t : Tm) (T : Ty).
  Scheme ind_Tm := Induction for Tm Sort Prop.
End Terms.

Section Functions.
  
End Functions.

Section Shift.
  Inductive Cutoff (a1 : Namespace) : Type :=
    | C0 
    | CS :
        (Cutoff a1) -> (Cutoff a1).
  
  Global Arguments C0 {a1} .
  Global Arguments CS {a1} _ .
  Fixpoint weakenCutoffTmVar (c : (Cutoff TmVar)) (k : Hvl) {struct k} :
  (Cutoff TmVar) :=
    match k with
      | (H0) => c
      | (HS a1 k) => match a1 with
        | (TmVar) => (CS (weakenCutoffTmVar c k))
        | _ => (weakenCutoffTmVar c k)
      end
    end.
  Fixpoint weakenCutoffTxVar (c : (Cutoff TxVar)) (k : Hvl) {struct k} :
  (Cutoff TxVar) :=
    match k with
      | (H0) => c
      | (HS a1 k) => match a1 with
        | (TxVar) => (CS (weakenCutoffTxVar c k))
        | _ => (weakenCutoffTxVar c k)
      end
    end.
  Fixpoint weakenCutoffTyVar (c : (Cutoff TyVar)) (k : Hvl) {struct k} :
  (Cutoff TyVar) :=
    match k with
      | (H0) => c
      | (HS a1 k) => match a1 with
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
  Lemma weakenCutoffTxVar_append  :
    (forall (c : (Cutoff TxVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffTxVar (weakenCutoffTxVar c k) k0) = (weakenCutoffTxVar c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenCutoffTyVar_append  :
    (forall (c : (Cutoff TyVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffTyVar (weakenCutoffTyVar c k) k0) = (weakenCutoffTyVar c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint shift_TmVar_Index (c : (Cutoff TmVar)) (x3 : (Index TmVar)) {struct c} :
  (Index TmVar) :=
    match c with
      | (C0) => (IS x3)
      | (CS c) => match x3 with
        | (I0) => I0
        | (IS x3) => (IS (shift_TmVar_Index c x3))
      end
    end.
  Fixpoint shift_TxVar_Index (c : (Cutoff TxVar)) (a1 : (Index TxVar)) {struct c} :
  (Index TxVar) :=
    match c with
      | (C0) => (IS a1)
      | (CS c) => match a1 with
        | (I0) => I0
        | (IS a1) => (IS (shift_TxVar_Index c a1))
      end
    end.
  Fixpoint shift_TyVar_Index (c : (Cutoff TyVar)) (X7 : (Index TyVar)) {struct c} :
  (Index TyVar) :=
    match c with
      | (C0) => (IS X7)
      | (CS c) => match X7 with
        | (I0) => I0
        | (IS X7) => (IS (shift_TyVar_Index c X7))
      end
    end.
  Fixpoint shift_TyVar_Ty (c : (Cutoff TyVar)) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (TVar X7) => (TVar (shift_TyVar_Index c X7))
      | (TArr T6 T7) => (TArr (shift_TyVar_Ty c T6) (shift_TyVar_Ty c T7))
      | (TAll T8) => (TAll (shift_TyVar_Ty (CS c) T8))
    end.
  Fixpoint shift_TmVar_Tm (c : (Cutoff TmVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x3) => (Var (shift_TmVar_Index c x3))
      | (XVar a1) => (XVar a1)
      | (Abs T6 t4) => (Abs T6 (shift_TmVar_Tm (CS c) t4))
      | (App t5 t6) => (App (shift_TmVar_Tm c t5) (shift_TmVar_Tm c t6))
      | (TAbs t7) => (TAbs (shift_TmVar_Tm c t7))
      | (TApp t8 T7) => (TApp (shift_TmVar_Tm c t8) T7)
    end.
  Fixpoint shift_TxVar_Tm (c : (Cutoff TxVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x3) => (Var x3)
      | (XVar a1) => (XVar (shift_TxVar_Index c a1))
      | (Abs T6 t4) => (Abs T6 (shift_TxVar_Tm c t4))
      | (App t5 t6) => (App (shift_TxVar_Tm c t5) (shift_TxVar_Tm c t6))
      | (TAbs t7) => (TAbs (shift_TxVar_Tm c t7))
      | (TApp t8 T7) => (TApp (shift_TxVar_Tm c t8) T7)
    end.
  Fixpoint shift_TyVar_Tm (c : (Cutoff TyVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x3) => (Var x3)
      | (XVar a1) => (XVar a1)
      | (Abs T6 t4) => (Abs (shift_TyVar_Ty c T6) (shift_TyVar_Tm c t4))
      | (App t5 t6) => (App (shift_TyVar_Tm c t5) (shift_TyVar_Tm c t6))
      | (TAbs t7) => (TAbs (shift_TyVar_Tm (CS c) t7))
      | (TApp t8 T7) => (TApp (shift_TyVar_Tm c t8) (shift_TyVar_Ty c T7))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S0
      | (HS TmVar k) => (weakenTy S0 k)
      | (HS TxVar k) => (weakenTy S0 k)
      | (HS TyVar k) => (shift_TyVar_Ty C0 (weakenTy S0 k))
    end.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} :
  Tm :=
    match k with
      | (H0) => s
      | (HS TmVar k) => (shift_TmVar_Tm C0 (weakenTm s k))
      | (HS TxVar k) => (shift_TxVar_Tm C0 (weakenTm s k))
      | (HS TyVar k) => (shift_TyVar_Tm C0 (weakenTm s k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a1 : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T6 : (Trace a1)).
  
  Global Arguments X0 [a1] .
  Global Arguments XS [a1] b _ .
  Fixpoint weakenTrace {a1 : Namespace} (x3 : (Trace a1)) (k : Hvl) {struct k} :
  (Trace a1) :=
    match k with
      | (H0) => x3
      | (HS b k) => (XS b (weakenTrace x3 k))
    end.
  Lemma weakenTrace_append (a1 : Namespace) :
    (forall (x3 : (Trace a1)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x3 k) k0) = (weakenTrace x3 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint subst_TmVar_Index (d : (Trace TmVar)) (s : Tm) (x3 : (Index TmVar)) {struct d} :
  Tm :=
    match d with
      | (X0) => match x3 with
        | (I0) => s
        | (IS x3) => (Var x3)
      end
      | (XS TmVar d) => match x3 with
        | (I0) => (Var I0)
        | (IS x3) => (shift_TmVar_Tm C0 (subst_TmVar_Index d s x3))
      end
      | (XS TxVar d) => (shift_TxVar_Tm C0 (subst_TmVar_Index d s x3))
      | (XS TyVar d) => (shift_TyVar_Tm C0 (subst_TmVar_Index d s x3))
    end.
  Fixpoint subst_TxVar_Index (d : (Trace TxVar)) (s : Tm) (a1 : (Index TxVar)) {struct d} :
  Tm :=
    match d with
      | (X0) => match a1 with
        | (I0) => s
        | (IS a1) => (XVar a1)
      end
      | (XS TmVar d) => (shift_TmVar_Tm C0 (subst_TxVar_Index d s a1))
      | (XS TxVar d) => match a1 with
        | (I0) => (XVar I0)
        | (IS a1) => (shift_TxVar_Tm C0 (subst_TxVar_Index d s a1))
      end
      | (XS TyVar d) => (shift_TyVar_Tm C0 (subst_TxVar_Index d s a1))
    end.
  Fixpoint subst_TyVar_Index (d : (Trace TyVar)) (S0 : Ty) (X7 : (Index TyVar)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X7 with
        | (I0) => S0
        | (IS X7) => (TVar X7)
      end
      | (XS TmVar d) => (subst_TyVar_Index d S0 X7)
      | (XS TxVar d) => (subst_TyVar_Index d S0 X7)
      | (XS TyVar d) => match X7 with
        | (I0) => (TVar I0)
        | (IS X7) => (shift_TyVar_Ty C0 (subst_TyVar_Index d S0 X7))
      end
    end.
  Fixpoint subst_TyVar_Ty (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) {struct S1} :
  Ty :=
    match S1 with
      | (TVar X7) => (subst_TyVar_Index d S0 X7)
      | (TArr T6 T7) => (TArr (subst_TyVar_Ty d S0 T6) (subst_TyVar_Ty d S0 T7))
      | (TAll T8) => (TAll (subst_TyVar_Ty (weakenTrace d (HS TyVar H0)) S0 T8))
    end.
  Fixpoint subst_TmVar_Tm (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (Var x3) => (subst_TmVar_Index d s x3)
      | (XVar a1) => (XVar a1)
      | (Abs T6 t4) => (Abs T6 (subst_TmVar_Tm (weakenTrace d (HS TmVar H0)) s t4))
      | (App t5 t6) => (App (subst_TmVar_Tm d s t5) (subst_TmVar_Tm d s t6))
      | (TAbs t7) => (TAbs (subst_TmVar_Tm (weakenTrace d (HS TyVar H0)) s t7))
      | (TApp t8 T7) => (TApp (subst_TmVar_Tm d s t8) T7)
    end.
  Fixpoint subst_TxVar_Tm (d : (Trace TxVar)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (Var x3) => (Var x3)
      | (XVar a1) => (subst_TxVar_Index d s a1)
      | (Abs T6 t4) => (Abs T6 (subst_TxVar_Tm (weakenTrace d (HS TmVar H0)) s t4))
      | (App t5 t6) => (App (subst_TxVar_Tm d s t5) (subst_TxVar_Tm d s t6))
      | (TAbs t7) => (TAbs (subst_TxVar_Tm (weakenTrace d (HS TyVar H0)) s t7))
      | (TApp t8 T7) => (TApp (subst_TxVar_Tm d s t8) T7)
    end.
  Fixpoint subst_TyVar_Tm (d : (Trace TyVar)) (S0 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x3) => (Var x3)
      | (XVar a1) => (XVar a1)
      | (Abs T6 t4) => (Abs (subst_TyVar_Ty d S0 T6) (subst_TyVar_Tm (weakenTrace d (HS TmVar H0)) S0 t4))
      | (App t5 t6) => (App (subst_TyVar_Tm d S0 t5) (subst_TyVar_Tm d S0 t6))
      | (TAbs t7) => (TAbs (subst_TyVar_Tm (weakenTrace d (HS TyVar H0)) S0 t7))
      | (TApp t8 T7) => (TApp (subst_TyVar_Tm d S0 t8) (subst_TyVar_Ty d S0 T7))
    end.
End Subst.

Global Hint Resolve (f_equal (shift_TmVar_Tm C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TxVar_Tm C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TyVar_Tm C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TyVar_Ty C0)) : cong_shift0.
 Hint Rewrite weakenCutoffTmVar_append weakenCutoffTxVar_append weakenCutoffTyVar_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Section SubstShiftReflection.
  Lemma subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x3 : (Index TmVar)) ,
      ((subst_TmVar_Index (weakenTrace X0 k) s (shift_TmVar_Index (weakenCutoffTmVar C0 k) x3)) = (Var x3))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma subst_TxVar_Index0_shift_TxVar_Index0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (a1 : (Index TxVar)) ,
      ((subst_TxVar_Index (weakenTrace X0 k) s (shift_TxVar_Index (weakenCutoffTxVar C0 k) a1)) = (XVar a1))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma subst_TyVar_Index0_shift_TyVar_Index0_reflection_ind (S0 : Ty) :
    (forall (k : Hvl) (X7 : (Index TyVar)) ,
      ((subst_TyVar_Index (weakenTrace X0 k) S0 (shift_TyVar_Index (weakenCutoffTyVar C0 k) X7)) = (TVar X7))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind (S1 : Ty) (k : Hvl) (S0 : Ty) {struct S1} :
  ((subst_TyVar_Ty (weakenTrace X0 k) S0 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = S1) :=
    match S1 return ((subst_TyVar_Ty (weakenTrace X0 k) S0 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = S1) with
      | (TVar X7) => (subst_TyVar_Index0_shift_TyVar_Index0_reflection_ind S0 k X7)
      | (TArr T7 T8) => (f_equal2 TArr (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T7 k S0) (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T8 k S0))
      | (TAll T6) => (f_equal TAll (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T6 (HS TyVar k) S0)))
    end.
  Fixpoint subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((subst_TmVar_Tm (weakenTrace X0 k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = s0) :=
    match s0 return ((subst_TmVar_Tm (weakenTrace X0 k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = s0) with
      | (Var x3) => (subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind s k x3)
      | (XVar a1) => eq_refl
      | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t4 (HS TmVar k) s)))
      | (App t5 t6) => (f_equal2 App (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t5 k s) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t6 k s))
      | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t4 (HS TyVar k) s)))
      | (TApp t4 T6) => (f_equal2 TApp (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t4 k s) eq_refl)
    end.
  Fixpoint subst_TxVar_0_shift_TxVar_0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((subst_TxVar_Tm (weakenTrace X0 k) s (shift_TxVar_Tm (weakenCutoffTxVar C0 k) s0)) = s0) :=
    match s0 return ((subst_TxVar_Tm (weakenTrace X0 k) s (shift_TxVar_Tm (weakenCutoffTxVar C0 k) s0)) = s0) with
      | (Var x3) => eq_refl
      | (XVar a1) => (subst_TxVar_Index0_shift_TxVar_Index0_reflection_ind s k a1)
      | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TxVar_0_shift_TxVar_0_Tm_reflection_ind t4 (HS TmVar k) s)))
      | (App t5 t6) => (f_equal2 App (subst_TxVar_0_shift_TxVar_0_Tm_reflection_ind t5 k s) (subst_TxVar_0_shift_TxVar_0_Tm_reflection_ind t6 k s))
      | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar X0 k (HS TyVar H0)) eq_refl eq_refl) (subst_TxVar_0_shift_TxVar_0_Tm_reflection_ind t4 (HS TyVar k) s)))
      | (TApp t4 T6) => (f_equal2 TApp (subst_TxVar_0_shift_TxVar_0_Tm_reflection_ind t4 k s) eq_refl)
    end.
  Fixpoint subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind (s : Tm) (k : Hvl) (S0 : Ty) {struct s} :
  ((subst_TyVar_Tm (weakenTrace X0 k) S0 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = s) :=
    match s return ((subst_TyVar_Tm (weakenTrace X0 k) S0 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = s) with
      | (Var x3) => eq_refl
      | (XVar a1) => eq_refl
      | (Abs T6 t4) => (f_equal2 Abs (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T6 k S0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t4 (HS TmVar k) S0)))
      | (App t5 t6) => (f_equal2 App (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t5 k S0) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t6 k S0))
      | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t4 (HS TyVar k) S0)))
      | (TApp t4 T6) => (f_equal2 TApp (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t4 k S0) (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T6 k S0))
    end.
  Definition subst_TyVar_Ty0_shift_TyVar_Ty0_reflection (S1 : Ty) : (forall (S0 : Ty) ,
    ((subst_TyVar_Ty X0 S0 (shift_TyVar_Ty C0 S1)) = S1)) := (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind S1 H0).
  Definition subst_TmVar_Tm0_shift_TmVar_Tm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((subst_TmVar_Tm X0 s (shift_TmVar_Tm C0 s0)) = s0)) := (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind s0 H0).
  Definition subst_TxVar_Tm0_shift_TxVar_Tm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((subst_TxVar_Tm X0 s (shift_TxVar_Tm C0 s0)) = s0)) := (subst_TxVar_0_shift_TxVar_0_Tm_reflection_ind s0 H0).
  Definition subst_TyVar_Tm0_shift_TyVar_Tm0_reflection (s : Tm) : (forall (S0 : Ty) ,
    ((subst_TyVar_Tm X0 S0 (shift_TyVar_Tm C0 s)) = s)) := (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind s H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shift_TmVar_Index_shift_TmVar_Index0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff TmVar)) (x3 : (Index TmVar)) ,
        ((shift_TmVar_Index (weakenCutoffTmVar (CS c) k) (shift_TmVar_Index (weakenCutoffTmVar C0 k) x3)) = (shift_TmVar_Index (weakenCutoffTmVar C0 k) (shift_TmVar_Index (weakenCutoffTmVar c k) x3)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma shift_TxVar_Index_shift_TxVar_Index0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff TxVar)) (a1 : (Index TxVar)) ,
        ((shift_TxVar_Index (weakenCutoffTxVar (CS c) k) (shift_TxVar_Index (weakenCutoffTxVar C0 k) a1)) = (shift_TxVar_Index (weakenCutoffTxVar C0 k) (shift_TxVar_Index (weakenCutoffTxVar c k) a1)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma shift_TyVar_Index_shift_TyVar_Index0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff TyVar)) (X7 : (Index TyVar)) ,
        ((shift_TyVar_Index (weakenCutoffTyVar (CS c) k) (shift_TyVar_Index (weakenCutoffTyVar C0 k) X7)) = (shift_TyVar_Index (weakenCutoffTyVar C0 k) (shift_TyVar_Index (weakenCutoffTyVar c k) X7)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint shift_TyVar__shift_TyVar_0_Ty_comm_ind (S0 : Ty) (k : Hvl) (c : (Cutoff TyVar)) {struct S0} :
    ((shift_TyVar_Ty (weakenCutoffTyVar (CS c) k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S0)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c k) S0))) :=
      match S0 return ((shift_TyVar_Ty (weakenCutoffTyVar (CS c) k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S0)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c k) S0))) with
        | (TVar X7) => (f_equal TVar (shift_TyVar_Index_shift_TyVar_Index0_comm_ind k c X7))
        | (TArr T7 T8) => (f_equal2 TArr (shift_TyVar__shift_TyVar_0_Ty_comm_ind T7 k c) (shift_TyVar__shift_TyVar_0_Ty_comm_ind T8 k c))
        | (TAll T6) => (f_equal TAll (shift_TyVar__shift_TyVar_0_Ty_comm_ind T6 (HS TyVar k) c))
      end.
    Fixpoint shift_TmVar__shift_TmVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TmVar)) {struct s} :
    ((shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) :=
      match s return ((shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) with
        | (Var x3) => (f_equal Var (shift_TmVar_Index_shift_TmVar_Index0_comm_ind k c x3))
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (shift_TmVar__shift_TmVar_0_Tm_comm_ind t4 (HS TmVar k) c))
        | (App t5 t6) => (f_equal2 App (shift_TmVar__shift_TmVar_0_Tm_comm_ind t5 k c) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t6 k c))
        | (TAbs t4) => (f_equal TAbs (shift_TmVar__shift_TmVar_0_Tm_comm_ind t4 (HS TyVar k) c))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TmVar__shift_TmVar_0_Tm_comm_ind t4 k c) eq_refl)
      end.
    Fixpoint shift_TmVar__shift_TxVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TmVar)) {struct s} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c k) (shift_TxVar_Tm (weakenCutoffTxVar C0 k) s)) = (shift_TxVar_Tm (weakenCutoffTxVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) :=
      match s return ((shift_TmVar_Tm (weakenCutoffTmVar c k) (shift_TxVar_Tm (weakenCutoffTxVar C0 k) s)) = (shift_TxVar_Tm (weakenCutoffTxVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (shift_TmVar__shift_TxVar_0_Tm_comm_ind t4 (HS TmVar k) c))
        | (App t5 t6) => (f_equal2 App (shift_TmVar__shift_TxVar_0_Tm_comm_ind t5 k c) (shift_TmVar__shift_TxVar_0_Tm_comm_ind t6 k c))
        | (TAbs t4) => (f_equal TAbs (shift_TmVar__shift_TxVar_0_Tm_comm_ind t4 (HS TyVar k) c))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TmVar__shift_TxVar_0_Tm_comm_ind t4 k c) eq_refl)
      end.
    Fixpoint shift_TmVar__shift_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TmVar)) {struct s} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) :=
      match s return ((shift_TmVar_Tm (weakenCutoffTmVar c k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (shift_TmVar__shift_TyVar_0_Tm_comm_ind t4 (HS TmVar k) c))
        | (App t5 t6) => (f_equal2 App (shift_TmVar__shift_TyVar_0_Tm_comm_ind t5 k c) (shift_TmVar__shift_TyVar_0_Tm_comm_ind t6 k c))
        | (TAbs t4) => (f_equal TAbs (shift_TmVar__shift_TyVar_0_Tm_comm_ind t4 (HS TyVar k) c))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TmVar__shift_TyVar_0_Tm_comm_ind t4 k c) eq_refl)
      end.
    Fixpoint shift_TxVar__shift_TmVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TxVar)) {struct s} :
    ((shift_TxVar_Tm (weakenCutoffTxVar c k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TxVar_Tm (weakenCutoffTxVar c k) s))) :=
      match s return ((shift_TxVar_Tm (weakenCutoffTxVar c k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TxVar_Tm (weakenCutoffTxVar c k) s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (shift_TxVar__shift_TmVar_0_Tm_comm_ind t4 (HS TmVar k) c))
        | (App t5 t6) => (f_equal2 App (shift_TxVar__shift_TmVar_0_Tm_comm_ind t5 k c) (shift_TxVar__shift_TmVar_0_Tm_comm_ind t6 k c))
        | (TAbs t4) => (f_equal TAbs (shift_TxVar__shift_TmVar_0_Tm_comm_ind t4 (HS TyVar k) c))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TxVar__shift_TmVar_0_Tm_comm_ind t4 k c) eq_refl)
      end.
    Fixpoint shift_TxVar__shift_TxVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TxVar)) {struct s} :
    ((shift_TxVar_Tm (weakenCutoffTxVar (CS c) k) (shift_TxVar_Tm (weakenCutoffTxVar C0 k) s)) = (shift_TxVar_Tm (weakenCutoffTxVar C0 k) (shift_TxVar_Tm (weakenCutoffTxVar c k) s))) :=
      match s return ((shift_TxVar_Tm (weakenCutoffTxVar (CS c) k) (shift_TxVar_Tm (weakenCutoffTxVar C0 k) s)) = (shift_TxVar_Tm (weakenCutoffTxVar C0 k) (shift_TxVar_Tm (weakenCutoffTxVar c k) s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => (f_equal XVar (shift_TxVar_Index_shift_TxVar_Index0_comm_ind k c a1))
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (shift_TxVar__shift_TxVar_0_Tm_comm_ind t4 (HS TmVar k) c))
        | (App t5 t6) => (f_equal2 App (shift_TxVar__shift_TxVar_0_Tm_comm_ind t5 k c) (shift_TxVar__shift_TxVar_0_Tm_comm_ind t6 k c))
        | (TAbs t4) => (f_equal TAbs (shift_TxVar__shift_TxVar_0_Tm_comm_ind t4 (HS TyVar k) c))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TxVar__shift_TxVar_0_Tm_comm_ind t4 k c) eq_refl)
      end.
    Fixpoint shift_TxVar__shift_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TxVar)) {struct s} :
    ((shift_TxVar_Tm (weakenCutoffTxVar c k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TxVar_Tm (weakenCutoffTxVar c k) s))) :=
      match s return ((shift_TxVar_Tm (weakenCutoffTxVar c k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TxVar_Tm (weakenCutoffTxVar c k) s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (shift_TxVar__shift_TyVar_0_Tm_comm_ind t4 (HS TmVar k) c))
        | (App t5 t6) => (f_equal2 App (shift_TxVar__shift_TyVar_0_Tm_comm_ind t5 k c) (shift_TxVar__shift_TyVar_0_Tm_comm_ind t6 k c))
        | (TAbs t4) => (f_equal TAbs (shift_TxVar__shift_TyVar_0_Tm_comm_ind t4 (HS TyVar k) c))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TxVar__shift_TyVar_0_Tm_comm_ind t4 k c) eq_refl)
      end.
    Fixpoint shift_TyVar__shift_TmVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TyVar)) {struct s} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c k) s))) :=
      match s return ((shift_TyVar_Tm (weakenCutoffTyVar c k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c k) s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (shift_TyVar__shift_TmVar_0_Tm_comm_ind t4 (HS TmVar k) c))
        | (App t5 t6) => (f_equal2 App (shift_TyVar__shift_TmVar_0_Tm_comm_ind t5 k c) (shift_TyVar__shift_TmVar_0_Tm_comm_ind t6 k c))
        | (TAbs t4) => (f_equal TAbs (shift_TyVar__shift_TmVar_0_Tm_comm_ind t4 (HS TyVar k) c))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TyVar__shift_TmVar_0_Tm_comm_ind t4 k c) eq_refl)
      end.
    Fixpoint shift_TyVar__shift_TxVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TyVar)) {struct s} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c k) (shift_TxVar_Tm (weakenCutoffTxVar C0 k) s)) = (shift_TxVar_Tm (weakenCutoffTxVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c k) s))) :=
      match s return ((shift_TyVar_Tm (weakenCutoffTyVar c k) (shift_TxVar_Tm (weakenCutoffTxVar C0 k) s)) = (shift_TxVar_Tm (weakenCutoffTxVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c k) s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (shift_TyVar__shift_TxVar_0_Tm_comm_ind t4 (HS TmVar k) c))
        | (App t5 t6) => (f_equal2 App (shift_TyVar__shift_TxVar_0_Tm_comm_ind t5 k c) (shift_TyVar__shift_TxVar_0_Tm_comm_ind t6 k c))
        | (TAbs t4) => (f_equal TAbs (shift_TyVar__shift_TxVar_0_Tm_comm_ind t4 (HS TyVar k) c))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TyVar__shift_TxVar_0_Tm_comm_ind t4 k c) eq_refl)
      end.
    Fixpoint shift_TyVar__shift_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TyVar)) {struct s} :
    ((shift_TyVar_Tm (weakenCutoffTyVar (CS c) k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c k) s))) :=
      match s return ((shift_TyVar_Tm (weakenCutoffTyVar (CS c) k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c k) s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs (shift_TyVar__shift_TyVar_0_Ty_comm_ind T6 k c) (shift_TyVar__shift_TyVar_0_Tm_comm_ind t4 (HS TmVar k) c))
        | (App t5 t6) => (f_equal2 App (shift_TyVar__shift_TyVar_0_Tm_comm_ind t5 k c) (shift_TyVar__shift_TyVar_0_Tm_comm_ind t6 k c))
        | (TAbs t4) => (f_equal TAbs (shift_TyVar__shift_TyVar_0_Tm_comm_ind t4 (HS TyVar k) c))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TyVar__shift_TyVar_0_Tm_comm_ind t4 k c) (shift_TyVar__shift_TyVar_0_Ty_comm_ind T6 k c))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition shift_TyVar__shift_TyVar_0_Ty_comm (S0 : Ty) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Ty (CS c) (shift_TyVar_Ty C0 S0)) = (shift_TyVar_Ty C0 (shift_TyVar_Ty c S0)))) := (shift_TyVar__shift_TyVar_0_Ty_comm_ind S0 H0).
    Definition shift_TmVar__shift_TmVar_0_Tm_comm (s : Tm) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Tm (CS c) (shift_TmVar_Tm C0 s)) = (shift_TmVar_Tm C0 (shift_TmVar_Tm c s)))) := (shift_TmVar__shift_TmVar_0_Tm_comm_ind s H0).
    Definition shift_TmVar__shift_TxVar_0_Tm_comm (s : Tm) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Tm c (shift_TxVar_Tm C0 s)) = (shift_TxVar_Tm C0 (shift_TmVar_Tm c s)))) := (shift_TmVar__shift_TxVar_0_Tm_comm_ind s H0).
    Definition shift_TmVar__shift_TyVar_0_Tm_comm (s : Tm) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Tm c (shift_TyVar_Tm C0 s)) = (shift_TyVar_Tm C0 (shift_TmVar_Tm c s)))) := (shift_TmVar__shift_TyVar_0_Tm_comm_ind s H0).
    Definition shift_TxVar__shift_TmVar_0_Tm_comm (s : Tm) : (forall (c : (Cutoff TxVar)) ,
      ((shift_TxVar_Tm c (shift_TmVar_Tm C0 s)) = (shift_TmVar_Tm C0 (shift_TxVar_Tm c s)))) := (shift_TxVar__shift_TmVar_0_Tm_comm_ind s H0).
    Definition shift_TxVar__shift_TxVar_0_Tm_comm (s : Tm) : (forall (c : (Cutoff TxVar)) ,
      ((shift_TxVar_Tm (CS c) (shift_TxVar_Tm C0 s)) = (shift_TxVar_Tm C0 (shift_TxVar_Tm c s)))) := (shift_TxVar__shift_TxVar_0_Tm_comm_ind s H0).
    Definition shift_TxVar__shift_TyVar_0_Tm_comm (s : Tm) : (forall (c : (Cutoff TxVar)) ,
      ((shift_TxVar_Tm c (shift_TyVar_Tm C0 s)) = (shift_TyVar_Tm C0 (shift_TxVar_Tm c s)))) := (shift_TxVar__shift_TyVar_0_Tm_comm_ind s H0).
    Definition shift_TyVar__shift_TmVar_0_Tm_comm (s : Tm) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Tm c (shift_TmVar_Tm C0 s)) = (shift_TmVar_Tm C0 (shift_TyVar_Tm c s)))) := (shift_TyVar__shift_TmVar_0_Tm_comm_ind s H0).
    Definition shift_TyVar__shift_TxVar_0_Tm_comm (s : Tm) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Tm c (shift_TxVar_Tm C0 s)) = (shift_TxVar_Tm C0 (shift_TyVar_Tm c s)))) := (shift_TyVar__shift_TxVar_0_Tm_comm_ind s H0).
    Definition shift_TyVar__shift_TyVar_0_Tm_comm (s : Tm) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Tm (CS c) (shift_TyVar_Tm C0 s)) = (shift_TyVar_Tm C0 (shift_TyVar_Tm c s)))) := (shift_TyVar__shift_TyVar_0_Tm_comm_ind s H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_TmVar__shift_TmVar_0_Tm_comm shift_TmVar__shift_TxVar_0_Tm_comm shift_TmVar__shift_TyVar_0_Tm_comm shift_TxVar__shift_TmVar_0_Tm_comm shift_TxVar__shift_TxVar_0_Tm_comm shift_TxVar__shift_TyVar_0_Tm_comm shift_TyVar__shift_TmVar_0_Tm_comm shift_TyVar__shift_TxVar_0_Tm_comm shift_TyVar__shift_TyVar_0_Tm_comm shift_TyVar__shift_TyVar_0_Ty_comm : interaction.
 Hint Rewrite shift_TmVar__shift_TmVar_0_Tm_comm shift_TmVar__shift_TxVar_0_Tm_comm shift_TmVar__shift_TyVar_0_Tm_comm shift_TxVar__shift_TmVar_0_Tm_comm shift_TxVar__shift_TxVar_0_Tm_comm shift_TxVar__shift_TyVar_0_Tm_comm shift_TyVar__shift_TmVar_0_Tm_comm shift_TyVar__shift_TxVar_0_Tm_comm shift_TyVar__shift_TyVar_0_Tm_comm shift_TyVar__shift_TyVar_0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTy_shift_TyVar_Ty  :
    (forall (k : Hvl) (c : (Cutoff TyVar)) (S0 : Ty) ,
      ((weakenTy (shift_TyVar_Ty c S0) k) = (shift_TyVar_Ty (weakenCutoffTyVar c k) (weakenTy S0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shift_TmVar_Tm  :
    (forall (k : Hvl) (c : (Cutoff TmVar)) (s : Tm) ,
      ((weakenTm (shift_TmVar_Tm c s) k) = (shift_TmVar_Tm (weakenCutoffTmVar c k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shift_TxVar_Tm  :
    (forall (k : Hvl) (c : (Cutoff TxVar)) (s : Tm) ,
      ((weakenTm (shift_TxVar_Tm c s) k) = (shift_TxVar_Tm (weakenCutoffTxVar c k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shift_TyVar_Tm  :
    (forall (k : Hvl) (c : (Cutoff TyVar)) (s : Tm) ,
      ((weakenTm (shift_TyVar_Tm c s) k) = (shift_TyVar_Tm (weakenCutoffTyVar c k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shift_TmVar_Tm_subst_TmVar_Index0_comm_ind (c : (Cutoff TmVar)) (s : Tm) :
      (forall (k : Hvl) (x3 : (Index TmVar)) ,
        ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Index (weakenTrace X0 k) s x3)) = (subst_TmVar_Index (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Index (weakenCutoffTmVar (CS c) k) x3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TxVar_Tm_subst_TmVar_Index0_comm_ind (c : (Cutoff TxVar)) (s : Tm) :
      (forall (k : Hvl) (x3 : (Index TmVar)) ,
        ((shift_TxVar_Tm (weakenCutoffTxVar c k) (subst_TmVar_Index (weakenTrace X0 k) s x3)) = (subst_TmVar_Index (weakenTrace X0 k) (shift_TxVar_Tm c s) x3))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TyVar_Tm_subst_TmVar_Index0_comm_ind (c : (Cutoff TyVar)) (s : Tm) :
      (forall (k : Hvl) (x3 : (Index TmVar)) ,
        ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TmVar_Index (weakenTrace X0 k) s x3)) = (subst_TmVar_Index (weakenTrace X0 k) (shift_TyVar_Tm c s) x3))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TmVar_Tm_subst_TxVar_Index0_comm_ind (c : (Cutoff TmVar)) (s : Tm) :
      (forall (k : Hvl) (a1 : (Index TxVar)) ,
        ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TxVar_Index (weakenTrace X0 k) s a1)) = (subst_TxVar_Index (weakenTrace X0 k) (shift_TmVar_Tm c s) a1))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TxVar_Tm_subst_TxVar_Index0_comm_ind (c : (Cutoff TxVar)) (s : Tm) :
      (forall (k : Hvl) (a1 : (Index TxVar)) ,
        ((shift_TxVar_Tm (weakenCutoffTxVar c k) (subst_TxVar_Index (weakenTrace X0 k) s a1)) = (subst_TxVar_Index (weakenTrace X0 k) (shift_TxVar_Tm c s) (shift_TxVar_Index (weakenCutoffTxVar (CS c) k) a1)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TyVar_Tm_subst_TxVar_Index0_comm_ind (c : (Cutoff TyVar)) (s : Tm) :
      (forall (k : Hvl) (a1 : (Index TxVar)) ,
        ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TxVar_Index (weakenTrace X0 k) s a1)) = (subst_TxVar_Index (weakenTrace X0 k) (shift_TyVar_Tm c s) a1))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TyVar_Ty_subst_TyVar_Index0_comm_ind (c : (Cutoff TyVar)) (S0 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((shift_TyVar_Ty (weakenCutoffTyVar c k) (subst_TyVar_Index (weakenTrace X0 k) S0 X7)) = (subst_TyVar_Index (weakenTrace X0 k) (shift_TyVar_Ty c S0) (shift_TyVar_Index (weakenCutoffTyVar (CS c) k) X7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint shift_TyVar__subst_TyVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c : (Cutoff TyVar)) (S0 : Ty) {struct S1} :
    ((shift_TyVar_Ty (weakenCutoffTyVar c k) (subst_TyVar_Ty (weakenTrace X0 k) S0 S1)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TyVar_Ty c S0) (shift_TyVar_Ty (weakenCutoffTyVar (CS c) k) S1))) :=
      match S1 return ((shift_TyVar_Ty (weakenCutoffTyVar c k) (subst_TyVar_Ty (weakenTrace X0 k) S0 S1)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TyVar_Ty c S0) (shift_TyVar_Ty (weakenCutoffTyVar (CS c) k) S1))) with
        | (TVar X7) => (shift_TyVar_Ty_subst_TyVar_Index0_comm_ind c S0 k X7)
        | (TArr T7 T8) => (f_equal2 TArr (shift_TyVar__subst_TyVar_0_Ty_comm_ind T7 k c S0) (shift_TyVar__subst_TyVar_0_Ty_comm_ind T8 k c S0))
        | (TAll T6) => (f_equal TAll (eq_trans (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Ty_comm_ind T6 (HS TyVar k) c S0) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_TmVar__subst_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff TmVar)) (s : Tm) {struct s0} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) s0))) :=
      match s0 return ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) s0))) with
        | (Var x3) => (shift_TmVar_Tm_subst_TmVar_Index0_comm_ind c s k x3)
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind t4 (HS TmVar k) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t5 t6) => (f_equal2 App (shift_TmVar__subst_TmVar_0_Tm_comm_ind t5 k c s) (shift_TmVar__subst_TmVar_0_Tm_comm_ind t6 k c s))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind t4 (HS TyVar k) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TmVar__subst_TmVar_0_Tm_comm_ind t4 k c s) eq_refl)
      end.
    Fixpoint shift_TmVar__subst_TxVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff TmVar)) (s : Tm) {struct s0} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TxVar_Tm (weakenTrace X0 k) s s0)) = (subst_TxVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Tm (weakenCutoffTmVar c k) s0))) :=
      match s0 return ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TxVar_Tm (weakenTrace X0 k) s s0)) = (subst_TxVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Tm (weakenCutoffTmVar c k) s0))) with
        | (Var x3) => eq_refl
        | (XVar a1) => (shift_TmVar_Tm_subst_TxVar_Index0_comm_ind c s k a1)
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TxVar_0_Tm_comm_ind t4 (HS TmVar k) c s) (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t5 t6) => (f_equal2 App (shift_TmVar__subst_TxVar_0_Tm_comm_ind t5 k c s) (shift_TmVar__subst_TxVar_0_Tm_comm_ind t6 k c s))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TxVar_0_Tm_comm_ind t4 (HS TyVar k) c s) (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TmVar__subst_TxVar_0_Tm_comm_ind t4 k c s) eq_refl)
      end.
    Fixpoint shift_TmVar__subst_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TmVar)) (S0 : Ty) {struct s} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S0 s)) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) :=
      match s return ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S0 s)) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Tm_comm_ind t4 (HS TmVar k) c S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t5 t6) => (f_equal2 App (shift_TmVar__subst_TyVar_0_Tm_comm_ind t5 k c S0) (shift_TmVar__subst_TyVar_0_Tm_comm_ind t6 k c S0))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Tm_comm_ind t4 (HS TyVar k) c S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TmVar__subst_TyVar_0_Tm_comm_ind t4 k c S0) eq_refl)
      end.
    Fixpoint shift_TxVar__subst_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff TxVar)) (s : Tm) {struct s0} :
    ((shift_TxVar_Tm (weakenCutoffTxVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TxVar_Tm c s) (shift_TxVar_Tm (weakenCutoffTxVar c k) s0))) :=
      match s0 return ((shift_TxVar_Tm (weakenCutoffTxVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TxVar_Tm c s) (shift_TxVar_Tm (weakenCutoffTxVar c k) s0))) with
        | (Var x3) => (shift_TxVar_Tm_subst_TmVar_Index0_comm_ind c s k x3)
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shift_TxVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TxVar__subst_TmVar_0_Tm_comm_ind t4 (HS TmVar k) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t5 t6) => (f_equal2 App (shift_TxVar__subst_TmVar_0_Tm_comm_ind t5 k c s) (shift_TxVar__subst_TmVar_0_Tm_comm_ind t6 k c s))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal2 shift_TxVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TxVar__subst_TmVar_0_Tm_comm_ind t4 (HS TyVar k) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TxVar__subst_TmVar_0_Tm_comm_ind t4 k c s) eq_refl)
      end.
    Fixpoint shift_TxVar__subst_TxVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff TxVar)) (s : Tm) {struct s0} :
    ((shift_TxVar_Tm (weakenCutoffTxVar c k) (subst_TxVar_Tm (weakenTrace X0 k) s s0)) = (subst_TxVar_Tm (weakenTrace X0 k) (shift_TxVar_Tm c s) (shift_TxVar_Tm (weakenCutoffTxVar (CS c) k) s0))) :=
      match s0 return ((shift_TxVar_Tm (weakenCutoffTxVar c k) (subst_TxVar_Tm (weakenTrace X0 k) s s0)) = (subst_TxVar_Tm (weakenTrace X0 k) (shift_TxVar_Tm c s) (shift_TxVar_Tm (weakenCutoffTxVar (CS c) k) s0))) with
        | (Var x3) => eq_refl
        | (XVar a1) => (shift_TxVar_Tm_subst_TxVar_Index0_comm_ind c s k a1)
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shift_TxVar_Tm eq_refl (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TxVar__subst_TxVar_0_Tm_comm_ind t4 (HS TmVar k) c s) (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t5 t6) => (f_equal2 App (shift_TxVar__subst_TxVar_0_Tm_comm_ind t5 k c s) (shift_TxVar__subst_TxVar_0_Tm_comm_ind t6 k c s))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal2 shift_TxVar_Tm eq_refl (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TxVar__subst_TxVar_0_Tm_comm_ind t4 (HS TyVar k) c s) (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TxVar__subst_TxVar_0_Tm_comm_ind t4 k c s) eq_refl)
      end.
    Fixpoint shift_TxVar__subst_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TxVar)) (S0 : Ty) {struct s} :
    ((shift_TxVar_Tm (weakenCutoffTxVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S0 s)) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (shift_TxVar_Tm (weakenCutoffTxVar c k) s))) :=
      match s return ((shift_TxVar_Tm (weakenCutoffTxVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S0 s)) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (shift_TxVar_Tm (weakenCutoffTxVar c k) s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shift_TxVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TxVar__subst_TyVar_0_Tm_comm_ind t4 (HS TmVar k) c S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t5 t6) => (f_equal2 App (shift_TxVar__subst_TyVar_0_Tm_comm_ind t5 k c S0) (shift_TxVar__subst_TyVar_0_Tm_comm_ind t6 k c S0))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal2 shift_TxVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TxVar__subst_TyVar_0_Tm_comm_ind t4 (HS TyVar k) c S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TxVar__subst_TyVar_0_Tm_comm_ind t4 k c S0) eq_refl)
      end.
    Fixpoint shift_TyVar__subst_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff TyVar)) (s : Tm) {struct s0} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TyVar_Tm c s) (shift_TyVar_Tm (weakenCutoffTyVar c k) s0))) :=
      match s0 return ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TyVar_Tm c s) (shift_TyVar_Tm (weakenCutoffTyVar c k) s0))) with
        | (Var x3) => (shift_TyVar_Tm_subst_TmVar_Index0_comm_ind c s k x3)
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Tm_comm_ind t4 (HS TmVar k) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t5 t6) => (f_equal2 App (shift_TyVar__subst_TmVar_0_Tm_comm_ind t5 k c s) (shift_TyVar__subst_TmVar_0_Tm_comm_ind t6 k c s))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Tm_comm_ind t4 (HS TyVar k) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TyVar__subst_TmVar_0_Tm_comm_ind t4 k c s) eq_refl)
      end.
    Fixpoint shift_TyVar__subst_TxVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff TyVar)) (s : Tm) {struct s0} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TxVar_Tm (weakenTrace X0 k) s s0)) = (subst_TxVar_Tm (weakenTrace X0 k) (shift_TyVar_Tm c s) (shift_TyVar_Tm (weakenCutoffTyVar c k) s0))) :=
      match s0 return ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TxVar_Tm (weakenTrace X0 k) s s0)) = (subst_TxVar_Tm (weakenTrace X0 k) (shift_TyVar_Tm c s) (shift_TyVar_Tm (weakenCutoffTyVar c k) s0))) with
        | (Var x3) => eq_refl
        | (XVar a1) => (shift_TyVar_Tm_subst_TxVar_Index0_comm_ind c s k a1)
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TxVar_0_Tm_comm_ind t4 (HS TmVar k) c s) (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t5 t6) => (f_equal2 App (shift_TyVar__subst_TxVar_0_Tm_comm_ind t5 k c s) (shift_TyVar__subst_TxVar_0_Tm_comm_ind t6 k c s))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TxVar_0_Tm_comm_ind t4 (HS TyVar k) c s) (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TyVar__subst_TxVar_0_Tm_comm_ind t4 k c s) eq_refl)
      end.
    Fixpoint shift_TyVar__subst_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TyVar)) (S0 : Ty) {struct s} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S0 s)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TyVar_Ty c S0) (shift_TyVar_Tm (weakenCutoffTyVar (CS c) k) s))) :=
      match s return ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S0 s)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TyVar_Ty c S0) (shift_TyVar_Tm (weakenCutoffTyVar (CS c) k) s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs (shift_TyVar__subst_TyVar_0_Ty_comm_ind T6 k c S0) (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Tm_comm_ind t4 (HS TmVar k) c S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t5 t6) => (f_equal2 App (shift_TyVar__subst_TyVar_0_Tm_comm_ind t5 k c S0) (shift_TyVar__subst_TyVar_0_Tm_comm_ind t6 k c S0))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Tm_comm_ind t4 (HS TyVar k) c S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t4 T6) => (f_equal2 TApp (shift_TyVar__subst_TyVar_0_Tm_comm_ind t4 k c S0) (shift_TyVar__subst_TyVar_0_Ty_comm_ind T6 k c S0))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shift_TyVar_Ty_subst_TyVar_Ty0_comm (S1 : Ty) : (forall (c : (Cutoff TyVar)) (S0 : Ty) ,
      ((shift_TyVar_Ty c (subst_TyVar_Ty X0 S0 S1)) = (subst_TyVar_Ty X0 (shift_TyVar_Ty c S0) (shift_TyVar_Ty (CS c) S1)))) := (shift_TyVar__subst_TyVar_0_Ty_comm_ind S1 H0).
    Definition shift_TmVar_Tm_subst_TmVar_Tm0_comm (s0 : Tm) : (forall (c : (Cutoff TmVar)) (s : Tm) ,
      ((shift_TmVar_Tm c (subst_TmVar_Tm X0 s s0)) = (subst_TmVar_Tm X0 (shift_TmVar_Tm c s) (shift_TmVar_Tm (CS c) s0)))) := (shift_TmVar__subst_TmVar_0_Tm_comm_ind s0 H0).
    Definition shift_TmVar_Tm_subst_TxVar_Tm0_comm (s0 : Tm) : (forall (c : (Cutoff TmVar)) (s : Tm) ,
      ((shift_TmVar_Tm c (subst_TxVar_Tm X0 s s0)) = (subst_TxVar_Tm X0 (shift_TmVar_Tm c s) (shift_TmVar_Tm c s0)))) := (shift_TmVar__subst_TxVar_0_Tm_comm_ind s0 H0).
    Definition shift_TmVar_Tm_subst_TyVar_Tm0_comm (s : Tm) : (forall (c : (Cutoff TmVar)) (S0 : Ty) ,
      ((shift_TmVar_Tm c (subst_TyVar_Tm X0 S0 s)) = (subst_TyVar_Tm X0 S0 (shift_TmVar_Tm c s)))) := (shift_TmVar__subst_TyVar_0_Tm_comm_ind s H0).
    Definition shift_TxVar_Tm_subst_TmVar_Tm0_comm (s0 : Tm) : (forall (c : (Cutoff TxVar)) (s : Tm) ,
      ((shift_TxVar_Tm c (subst_TmVar_Tm X0 s s0)) = (subst_TmVar_Tm X0 (shift_TxVar_Tm c s) (shift_TxVar_Tm c s0)))) := (shift_TxVar__subst_TmVar_0_Tm_comm_ind s0 H0).
    Definition shift_TxVar_Tm_subst_TxVar_Tm0_comm (s0 : Tm) : (forall (c : (Cutoff TxVar)) (s : Tm) ,
      ((shift_TxVar_Tm c (subst_TxVar_Tm X0 s s0)) = (subst_TxVar_Tm X0 (shift_TxVar_Tm c s) (shift_TxVar_Tm (CS c) s0)))) := (shift_TxVar__subst_TxVar_0_Tm_comm_ind s0 H0).
    Definition shift_TxVar_Tm_subst_TyVar_Tm0_comm (s : Tm) : (forall (c : (Cutoff TxVar)) (S0 : Ty) ,
      ((shift_TxVar_Tm c (subst_TyVar_Tm X0 S0 s)) = (subst_TyVar_Tm X0 S0 (shift_TxVar_Tm c s)))) := (shift_TxVar__subst_TyVar_0_Tm_comm_ind s H0).
    Definition shift_TyVar_Tm_subst_TmVar_Tm0_comm (s0 : Tm) : (forall (c : (Cutoff TyVar)) (s : Tm) ,
      ((shift_TyVar_Tm c (subst_TmVar_Tm X0 s s0)) = (subst_TmVar_Tm X0 (shift_TyVar_Tm c s) (shift_TyVar_Tm c s0)))) := (shift_TyVar__subst_TmVar_0_Tm_comm_ind s0 H0).
    Definition shift_TyVar_Tm_subst_TxVar_Tm0_comm (s0 : Tm) : (forall (c : (Cutoff TyVar)) (s : Tm) ,
      ((shift_TyVar_Tm c (subst_TxVar_Tm X0 s s0)) = (subst_TxVar_Tm X0 (shift_TyVar_Tm c s) (shift_TyVar_Tm c s0)))) := (shift_TyVar__subst_TxVar_0_Tm_comm_ind s0 H0).
    Definition shift_TyVar_Tm_subst_TyVar_Tm0_comm (s : Tm) : (forall (c : (Cutoff TyVar)) (S0 : Ty) ,
      ((shift_TyVar_Tm c (subst_TyVar_Tm X0 S0 s)) = (subst_TyVar_Tm X0 (shift_TyVar_Ty c S0) (shift_TyVar_Tm (CS c) s)))) := (shift_TyVar__subst_TyVar_0_Tm_comm_ind s H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma subst_TmVar_Index_shift_TmVar_Tm0_comm_ind (d : (Trace TmVar)) (s : Tm) :
      (forall (k : Hvl) (x3 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TmVar d) k) s (shift_TmVar_Index (weakenCutoffTmVar C0 k) x3)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Index (weakenTrace d k) s x3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Index_shift_TxVar_Tm0_comm_ind (d : (Trace TmVar)) (s : Tm) :
      (forall (k : Hvl) (x3 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TxVar d) k) s x3) = (shift_TxVar_Tm (weakenCutoffTxVar C0 k) (subst_TmVar_Index (weakenTrace d k) s x3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Index_shift_TyVar_Tm0_comm_ind (d : (Trace TmVar)) (s : Tm) :
      (forall (k : Hvl) (x3 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TyVar d) k) s x3) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Index (weakenTrace d k) s x3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TxVar_Index_shift_TmVar_Tm0_comm_ind (d : (Trace TxVar)) (s : Tm) :
      (forall (k : Hvl) (a1 : (Index TxVar)) ,
        ((subst_TxVar_Index (weakenTrace (XS TmVar d) k) s a1) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TxVar_Index (weakenTrace d k) s a1)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TxVar_Index_shift_TxVar_Tm0_comm_ind (d : (Trace TxVar)) (s : Tm) :
      (forall (k : Hvl) (a1 : (Index TxVar)) ,
        ((subst_TxVar_Index (weakenTrace (XS TxVar d) k) s (shift_TxVar_Index (weakenCutoffTxVar C0 k) a1)) = (shift_TxVar_Tm (weakenCutoffTxVar C0 k) (subst_TxVar_Index (weakenTrace d k) s a1)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TxVar_Index_shift_TyVar_Tm0_comm_ind (d : (Trace TxVar)) (s : Tm) :
      (forall (k : Hvl) (a1 : (Index TxVar)) ,
        ((subst_TxVar_Index (weakenTrace (XS TyVar d) k) s a1) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TxVar_Index (weakenTrace d k) s a1)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Index_shift_TmVar_Ty0_comm_ind (d : (Trace TyVar)) (S0 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace (XS TmVar d) k) S0 X7) = (subst_TyVar_Index (weakenTrace d k) S0 X7))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Index_shift_TxVar_Ty0_comm_ind (d : (Trace TyVar)) (S0 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace (XS TxVar d) k) S0 X7) = (subst_TyVar_Index (weakenTrace d k) S0 X7))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Index_shift_TyVar_Ty0_comm_ind (d : (Trace TyVar)) (S0 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace (XS TyVar d) k) S0 (shift_TyVar_Index (weakenCutoffTyVar C0 k) X7)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Index (weakenTrace d k) S0 X7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_TyVar__shift_TyVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct S1} :
    ((subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S0 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Ty (weakenTrace d k) S0 S1))) :=
      match S1 return ((subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S0 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Ty (weakenTrace d k) S0 S1))) with
        | (TVar X7) => (subst_TyVar_Index_shift_TyVar_Ty0_comm_ind d S0 k X7)
        | (TArr T7 T8) => (f_equal2 TArr (subst_TyVar__shift_TyVar_0_Ty_comm_ind T7 k d S0) (subst_TyVar__shift_TyVar_0_Ty_comm_ind T8 k d S0))
        | (TAll T6) => (f_equal TAll (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TyVar d) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Ty_comm_ind T6 (HS TyVar k) d S0) (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d k (HS TyVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__shift_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) {struct s0} :
    ((subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) :=
      match s0 return ((subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) with
        | (Var x3) => (subst_TmVar_Index_shift_TmVar_Tm0_comm_ind d s k x3)
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind t4 (HS TmVar k) d s) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TmVar__shift_TmVar_0_Tm_comm_ind t5 k d s) (subst_TmVar__shift_TmVar_0_Tm_comm_ind t6 k d s))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TmVar d) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind t4 (HS TyVar k) d s) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TmVar__shift_TmVar_0_Tm_comm_ind t4 k d s) eq_refl)
      end.
    Fixpoint subst_TmVar__shift_TxVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) {struct s0} :
    ((subst_TmVar_Tm (weakenTrace (XS TxVar d) k) s (shift_TxVar_Tm (weakenCutoffTxVar C0 k) s0)) = (shift_TxVar_Tm (weakenCutoffTxVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) :=
      match s0 return ((subst_TmVar_Tm (weakenTrace (XS TxVar d) k) s (shift_TxVar_Tm (weakenCutoffTxVar C0 k) s0)) = (shift_TxVar_Tm (weakenCutoffTxVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) with
        | (Var x3) => (subst_TmVar_Index_shift_TxVar_Tm0_comm_ind d s k x3)
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TxVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TxVar_0_Tm_comm_ind t4 (HS TmVar k) d s) (f_equal2 shift_TxVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TmVar__shift_TxVar_0_Tm_comm_ind t5 k d s) (subst_TmVar__shift_TxVar_0_Tm_comm_ind t6 k d s))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TxVar d) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TxVar_0_Tm_comm_ind t4 (HS TyVar k) d s) (f_equal2 shift_TxVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TmVar__shift_TxVar_0_Tm_comm_ind t4 k d s) eq_refl)
      end.
    Fixpoint subst_TmVar__shift_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) {struct s0} :
    ((subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) :=
      match s0 return ((subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) with
        | (Var x3) => (subst_TmVar_Index_shift_TyVar_Tm0_comm_ind d s k x3)
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Tm_comm_ind t4 (HS TmVar k) d s) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TmVar__shift_TyVar_0_Tm_comm_ind t5 k d s) (subst_TmVar__shift_TyVar_0_Tm_comm_ind t6 k d s))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TyVar d) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Tm_comm_ind t4 (HS TyVar k) d s) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TmVar__shift_TyVar_0_Tm_comm_ind t4 k d s) eq_refl)
      end.
    Fixpoint subst_TxVar__shift_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TxVar)) (s : Tm) {struct s0} :
    ((subst_TxVar_Tm (weakenTrace (XS TmVar d) k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TxVar_Tm (weakenTrace d k) s s0))) :=
      match s0 return ((subst_TxVar_Tm (weakenTrace (XS TmVar d) k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TxVar_Tm (weakenTrace d k) s s0))) with
        | (Var x3) => eq_refl
        | (XVar a1) => (subst_TxVar_Index_shift_TmVar_Tm0_comm_ind d s k a1)
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TxVar__shift_TmVar_0_Tm_comm_ind t4 (HS TmVar k) d s) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TxVar__shift_TmVar_0_Tm_comm_ind t5 k d s) (subst_TxVar__shift_TmVar_0_Tm_comm_ind t6 k d s))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar (XS TmVar d) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TxVar__shift_TmVar_0_Tm_comm_ind t4 (HS TyVar k) d s) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar d k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TxVar__shift_TmVar_0_Tm_comm_ind t4 k d s) eq_refl)
      end.
    Fixpoint subst_TxVar__shift_TxVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TxVar)) (s : Tm) {struct s0} :
    ((subst_TxVar_Tm (weakenTrace (XS TxVar d) k) s (shift_TxVar_Tm (weakenCutoffTxVar C0 k) s0)) = (shift_TxVar_Tm (weakenCutoffTxVar C0 k) (subst_TxVar_Tm (weakenTrace d k) s s0))) :=
      match s0 return ((subst_TxVar_Tm (weakenTrace (XS TxVar d) k) s (shift_TxVar_Tm (weakenCutoffTxVar C0 k) s0)) = (shift_TxVar_Tm (weakenCutoffTxVar C0 k) (subst_TxVar_Tm (weakenTrace d k) s s0))) with
        | (Var x3) => eq_refl
        | (XVar a1) => (subst_TxVar_Index_shift_TxVar_Tm0_comm_ind d s k a1)
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar (XS TxVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TxVar__shift_TxVar_0_Tm_comm_ind t4 (HS TmVar k) d s) (f_equal2 shift_TxVar_Tm eq_refl (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TxVar__shift_TxVar_0_Tm_comm_ind t5 k d s) (subst_TxVar__shift_TxVar_0_Tm_comm_ind t6 k d s))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar (XS TxVar d) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TxVar__shift_TxVar_0_Tm_comm_ind t4 (HS TyVar k) d s) (f_equal2 shift_TxVar_Tm eq_refl (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar d k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TxVar__shift_TxVar_0_Tm_comm_ind t4 k d s) eq_refl)
      end.
    Fixpoint subst_TxVar__shift_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TxVar)) (s : Tm) {struct s0} :
    ((subst_TxVar_Tm (weakenTrace (XS TyVar d) k) s (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TxVar_Tm (weakenTrace d k) s s0))) :=
      match s0 return ((subst_TxVar_Tm (weakenTrace (XS TyVar d) k) s (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TxVar_Tm (weakenTrace d k) s s0))) with
        | (Var x3) => eq_refl
        | (XVar a1) => (subst_TxVar_Index_shift_TyVar_Tm0_comm_ind d s k a1)
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TxVar__shift_TyVar_0_Tm_comm_ind t4 (HS TmVar k) d s) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TxVar__shift_TyVar_0_Tm_comm_ind t5 k d s) (subst_TxVar__shift_TyVar_0_Tm_comm_ind t6 k d s))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar (XS TyVar d) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TxVar__shift_TyVar_0_Tm_comm_ind t4 (HS TyVar k) d s) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar d k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TxVar__shift_TyVar_0_Tm_comm_ind t4 k d s) eq_refl)
      end.
    Fixpoint subst_TyVar__shift_TmVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct s} :
    ((subst_TyVar_Tm (weakenTrace d k) S0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S0 s))) :=
      match s return ((subst_TyVar_Tm (weakenTrace d k) S0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S0 s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Tm_comm_ind t4 (HS TmVar k) d S0) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TyVar__shift_TmVar_0_Tm_comm_ind t5 k d S0) (subst_TyVar__shift_TmVar_0_Tm_comm_ind t6 k d S0))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Tm_comm_ind t4 (HS TyVar k) d S0) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TyVar__shift_TmVar_0_Tm_comm_ind t4 k d S0) eq_refl)
      end.
    Fixpoint subst_TyVar__shift_TxVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct s} :
    ((subst_TyVar_Tm (weakenTrace d k) S0 (shift_TxVar_Tm (weakenCutoffTxVar C0 k) s)) = (shift_TxVar_Tm (weakenCutoffTxVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S0 s))) :=
      match s return ((subst_TyVar_Tm (weakenTrace d k) S0 (shift_TxVar_Tm (weakenCutoffTxVar C0 k) s)) = (shift_TxVar_Tm (weakenCutoffTxVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S0 s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TxVar_0_Tm_comm_ind t4 (HS TmVar k) d S0) (f_equal2 shift_TxVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TyVar__shift_TxVar_0_Tm_comm_ind t5 k d S0) (subst_TyVar__shift_TxVar_0_Tm_comm_ind t6 k d S0))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TxVar_0_Tm_comm_ind t4 (HS TyVar k) d S0) (f_equal2 shift_TxVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TyVar__shift_TxVar_0_Tm_comm_ind t4 k d S0) eq_refl)
      end.
    Fixpoint subst_TyVar__shift_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct s} :
    ((subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S0 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S0 s))) :=
      match s return ((subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S0 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S0 s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs (subst_TyVar__shift_TyVar_0_Ty_comm_ind T6 k d S0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Tm_comm_ind t4 (HS TmVar k) d S0) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TyVar__shift_TyVar_0_Tm_comm_ind t5 k d S0) (subst_TyVar__shift_TyVar_0_Tm_comm_ind t6 k d S0))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TyVar d) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Tm_comm_ind t4 (HS TyVar k) d S0) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TyVar__shift_TyVar_0_Tm_comm_ind t4 k d S0) (subst_TyVar__shift_TyVar_0_Ty_comm_ind T6 k d S0))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition subst_TyVar_Ty_shift_TyVar_Ty0_comm (S1 : Ty) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Ty (XS TyVar d) S0 (shift_TyVar_Ty C0 S1)) = (shift_TyVar_Ty C0 (subst_TyVar_Ty d S0 S1)))) := (subst_TyVar__shift_TyVar_0_Ty_comm_ind S1 H0).
    Definition subst_TmVar_Tm_shift_TmVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) ,
      ((subst_TmVar_Tm (XS TmVar d) s (shift_TmVar_Tm C0 s0)) = (shift_TmVar_Tm C0 (subst_TmVar_Tm d s s0)))) := (subst_TmVar__shift_TmVar_0_Tm_comm_ind s0 H0).
    Definition subst_TmVar_Tm_shift_TxVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) ,
      ((subst_TmVar_Tm (XS TxVar d) s (shift_TxVar_Tm C0 s0)) = (shift_TxVar_Tm C0 (subst_TmVar_Tm d s s0)))) := (subst_TmVar__shift_TxVar_0_Tm_comm_ind s0 H0).
    Definition subst_TmVar_Tm_shift_TyVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) ,
      ((subst_TmVar_Tm (XS TyVar d) s (shift_TyVar_Tm C0 s0)) = (shift_TyVar_Tm C0 (subst_TmVar_Tm d s s0)))) := (subst_TmVar__shift_TyVar_0_Tm_comm_ind s0 H0).
    Definition subst_TxVar_Tm_shift_TmVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TxVar)) (s : Tm) ,
      ((subst_TxVar_Tm (XS TmVar d) s (shift_TmVar_Tm C0 s0)) = (shift_TmVar_Tm C0 (subst_TxVar_Tm d s s0)))) := (subst_TxVar__shift_TmVar_0_Tm_comm_ind s0 H0).
    Definition subst_TxVar_Tm_shift_TxVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TxVar)) (s : Tm) ,
      ((subst_TxVar_Tm (XS TxVar d) s (shift_TxVar_Tm C0 s0)) = (shift_TxVar_Tm C0 (subst_TxVar_Tm d s s0)))) := (subst_TxVar__shift_TxVar_0_Tm_comm_ind s0 H0).
    Definition subst_TxVar_Tm_shift_TyVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TxVar)) (s : Tm) ,
      ((subst_TxVar_Tm (XS TyVar d) s (shift_TyVar_Tm C0 s0)) = (shift_TyVar_Tm C0 (subst_TxVar_Tm d s s0)))) := (subst_TxVar__shift_TyVar_0_Tm_comm_ind s0 H0).
    Definition subst_TyVar_Tm_shift_TmVar_Tm0_comm (s : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Tm d S0 (shift_TmVar_Tm C0 s)) = (shift_TmVar_Tm C0 (subst_TyVar_Tm d S0 s)))) := (subst_TyVar__shift_TmVar_0_Tm_comm_ind s H0).
    Definition subst_TyVar_Tm_shift_TxVar_Tm0_comm (s : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Tm d S0 (shift_TxVar_Tm C0 s)) = (shift_TxVar_Tm C0 (subst_TyVar_Tm d S0 s)))) := (subst_TyVar__shift_TxVar_0_Tm_comm_ind s H0).
    Definition subst_TyVar_Tm_shift_TyVar_Tm0_comm (s : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Tm (XS TyVar d) S0 (shift_TyVar_Tm C0 s)) = (shift_TyVar_Tm C0 (subst_TyVar_Tm d S0 s)))) := (subst_TyVar__shift_TyVar_0_Tm_comm_ind s H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Fixpoint subst_TyVar__TmVar_Ty_ind (S1 : Ty) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct S1} :
    ((subst_TyVar_Ty (weakenTrace (XS TmVar d) k) S0 S1) = (subst_TyVar_Ty (weakenTrace d k) S0 S1)) :=
      match S1 return ((subst_TyVar_Ty (weakenTrace (XS TmVar d) k) S0 S1) = (subst_TyVar_Ty (weakenTrace d k) S0 S1)) with
        | (TVar X7) => (subst_TyVar_Index_shift_TmVar_Ty0_comm_ind d S0 k X7)
        | (TArr T7 T8) => (f_equal2 TArr (subst_TyVar__TmVar_Ty_ind T7 k d S0) (subst_TyVar__TmVar_Ty_ind T8 k d S0))
        | (TAll T6) => (f_equal TAll (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TmVar d) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__TmVar_Ty_ind T6 (HS TyVar k) d S0) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d k (HS TyVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint subst_TyVar__TxVar_Ty_ind (S1 : Ty) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct S1} :
    ((subst_TyVar_Ty (weakenTrace (XS TxVar d) k) S0 S1) = (subst_TyVar_Ty (weakenTrace d k) S0 S1)) :=
      match S1 return ((subst_TyVar_Ty (weakenTrace (XS TxVar d) k) S0 S1) = (subst_TyVar_Ty (weakenTrace d k) S0 S1)) with
        | (TVar X7) => (subst_TyVar_Index_shift_TxVar_Ty0_comm_ind d S0 k X7)
        | (TArr T7 T8) => (f_equal2 TArr (subst_TyVar__TxVar_Ty_ind T7 k d S0) (subst_TyVar__TxVar_Ty_ind T8 k d S0))
        | (TAll T6) => (f_equal TAll (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TxVar d) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__TxVar_Ty_ind T6 (HS TyVar k) d S0) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d k (HS TyVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint subst_TyVar__TmVar_Tm_ind (s : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct s} :
    ((subst_TyVar_Tm (weakenTrace (XS TmVar d) k) S0 s) = (subst_TyVar_Tm (weakenTrace d k) S0 s)) :=
      match s return ((subst_TyVar_Tm (weakenTrace (XS TmVar d) k) S0 s) = (subst_TyVar_Tm (weakenTrace d k) S0 s)) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs (subst_TyVar__TmVar_Ty_ind T6 k d S0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__TmVar_Tm_ind t4 (HS TmVar k) d S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t5 t6) => (f_equal2 App (subst_TyVar__TmVar_Tm_ind t5 k d S0) (subst_TyVar__TmVar_Tm_ind t6 k d S0))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TmVar d) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__TmVar_Tm_ind t4 (HS TyVar k) d S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TyVar__TmVar_Tm_ind t4 k d S0) (subst_TyVar__TmVar_Ty_ind T6 k d S0))
      end.
    Fixpoint subst_TyVar__TxVar_Tm_ind (s : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct s} :
    ((subst_TyVar_Tm (weakenTrace (XS TxVar d) k) S0 s) = (subst_TyVar_Tm (weakenTrace d k) S0 s)) :=
      match s return ((subst_TyVar_Tm (weakenTrace (XS TxVar d) k) S0 s) = (subst_TyVar_Tm (weakenTrace d k) S0 s)) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs (subst_TyVar__TxVar_Ty_ind T6 k d S0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TxVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__TxVar_Tm_ind t4 (HS TmVar k) d S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t5 t6) => (f_equal2 App (subst_TyVar__TxVar_Tm_ind t5 k d S0) (subst_TyVar__TxVar_Tm_ind t6 k d S0))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TxVar d) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__TxVar_Tm_ind t4 (HS TyVar k) d S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TyVar__TxVar_Tm_ind t4 k d S0) (subst_TyVar__TxVar_Ty_ind T6 k d S0))
      end.
  End SubstSubordInd.
  Section SubstSubord.
    Definition subst_TyVar_Ty_TmVar (S1 : Ty) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Ty (XS TmVar d) S0 S1) = (subst_TyVar_Ty d S0 S1))) := (subst_TyVar__TmVar_Ty_ind S1 H0).
    Definition subst_TyVar_Ty_TxVar (S1 : Ty) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Ty (XS TxVar d) S0 S1) = (subst_TyVar_Ty d S0 S1))) := (subst_TyVar__TxVar_Ty_ind S1 H0).
    Definition subst_TyVar_Tm_TmVar (s : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Tm (XS TmVar d) S0 s) = (subst_TyVar_Tm d S0 s))) := (subst_TyVar__TmVar_Tm_ind s H0).
    Definition subst_TyVar_Tm_TxVar (s : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Tm (XS TxVar d) S0 s) = (subst_TyVar_Tm d S0 s))) := (subst_TyVar__TxVar_Tm_ind s H0).
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite subst_TmVar_Tm0_shift_TmVar_Tm0_reflection subst_TxVar_Tm0_shift_TxVar_Tm0_reflection subst_TyVar_Tm0_shift_TyVar_Tm0_reflection subst_TyVar_Ty0_shift_TyVar_Ty0_reflection : interaction.
 Hint Rewrite subst_TmVar_Tm0_shift_TmVar_Tm0_reflection subst_TxVar_Tm0_shift_TxVar_Tm0_reflection subst_TyVar_Tm0_shift_TyVar_Tm0_reflection subst_TyVar_Ty0_shift_TyVar_Ty0_reflection : reflection.
 Hint Rewrite subst_TmVar_Tm_shift_TmVar_Tm0_comm subst_TmVar_Tm_shift_TxVar_Tm0_comm subst_TmVar_Tm_shift_TyVar_Tm0_comm subst_TxVar_Tm_shift_TmVar_Tm0_comm subst_TxVar_Tm_shift_TxVar_Tm0_comm subst_TxVar_Tm_shift_TyVar_Tm0_comm subst_TyVar_Tm_shift_TmVar_Tm0_comm subst_TyVar_Tm_shift_TxVar_Tm0_comm subst_TyVar_Tm_shift_TyVar_Tm0_comm subst_TyVar_Ty_shift_TyVar_Ty0_comm : interaction.
 Hint Rewrite subst_TmVar_Tm_shift_TmVar_Tm0_comm subst_TmVar_Tm_shift_TxVar_Tm0_comm subst_TmVar_Tm_shift_TyVar_Tm0_comm subst_TxVar_Tm_shift_TmVar_Tm0_comm subst_TxVar_Tm_shift_TxVar_Tm0_comm subst_TxVar_Tm_shift_TyVar_Tm0_comm subst_TyVar_Tm_shift_TmVar_Tm0_comm subst_TyVar_Tm_shift_TxVar_Tm0_comm subst_TyVar_Tm_shift_TyVar_Tm0_comm subst_TyVar_Ty_shift_TyVar_Ty0_comm : subst_shift0.
 Hint Rewrite subst_TyVar_Tm_TmVar subst_TyVar_Tm_TxVar subst_TyVar_Ty_TmVar subst_TyVar_Ty_TxVar : interaction.
 Hint Rewrite subst_TyVar_Tm_TmVar subst_TyVar_Tm_TxVar subst_TyVar_Ty_TmVar subst_TyVar_Ty_TxVar : subst_shift0.
 Hint Rewrite shift_TmVar_Tm_subst_TmVar_Tm0_comm shift_TmVar_Tm_subst_TxVar_Tm0_comm shift_TmVar_Tm_subst_TyVar_Tm0_comm shift_TxVar_Tm_subst_TmVar_Tm0_comm shift_TxVar_Tm_subst_TxVar_Tm0_comm shift_TxVar_Tm_subst_TyVar_Tm0_comm shift_TyVar_Tm_subst_TmVar_Tm0_comm shift_TyVar_Tm_subst_TxVar_Tm0_comm shift_TyVar_Tm_subst_TyVar_Tm0_comm shift_TyVar_Ty_subst_TyVar_Ty0_comm : interaction.
 Hint Rewrite shift_TmVar_Tm_subst_TmVar_Tm0_comm shift_TmVar_Tm_subst_TxVar_Tm0_comm shift_TmVar_Tm_subst_TyVar_Tm0_comm shift_TxVar_Tm_subst_TmVar_Tm0_comm shift_TxVar_Tm_subst_TxVar_Tm0_comm shift_TxVar_Tm_subst_TyVar_Tm0_comm shift_TyVar_Tm_subst_TmVar_Tm0_comm shift_TyVar_Tm_subst_TxVar_Tm0_comm shift_TyVar_Tm_subst_TyVar_Tm0_comm shift_TyVar_Ty_subst_TyVar_Ty0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma subst_TmVar_Tm_subst_TmVar_Index0_commright_ind (d : (Trace TmVar)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (x3 : (Index TmVar)) ,
        ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Index (weakenTrace X0 k) s0 x3)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Index (weakenTrace (XS TmVar d) k) s x3)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TxVar_Tm_subst_TmVar_Index0_commright_ind (d : (Trace TxVar)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (x3 : (Index TmVar)) ,
        ((subst_TxVar_Tm (weakenTrace d k) s (subst_TmVar_Index (weakenTrace X0 k) s0 x3)) = (subst_TmVar_Index (weakenTrace X0 k) (subst_TxVar_Tm d s s0) x3))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Tm_subst_TmVar_Index0_commright_ind (d : (Trace TyVar)) (S0 : Ty) (s : Tm) :
      (forall (k : Hvl) (x3 : (Index TmVar)) ,
        ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TmVar_Index (weakenTrace X0 k) s x3)) = (subst_TmVar_Index (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) x3))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Tm_subst_TxVar_Index0_commright_ind (d : (Trace TmVar)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (a1 : (Index TxVar)) ,
        ((subst_TmVar_Tm (weakenTrace d k) s (subst_TxVar_Index (weakenTrace X0 k) s0 a1)) = (subst_TxVar_Index (weakenTrace X0 k) (subst_TmVar_Tm d s s0) a1))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TxVar_Tm_subst_TxVar_Index0_commright_ind (d : (Trace TxVar)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (a1 : (Index TxVar)) ,
        ((subst_TxVar_Tm (weakenTrace d k) s (subst_TxVar_Index (weakenTrace X0 k) s0 a1)) = (subst_TxVar_Tm (weakenTrace X0 k) (subst_TxVar_Tm d s s0) (subst_TxVar_Index (weakenTrace (XS TxVar d) k) s a1)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Tm_subst_TxVar_Index0_commright_ind (d : (Trace TyVar)) (S0 : Ty) (s : Tm) :
      (forall (k : Hvl) (a1 : (Index TxVar)) ,
        ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TxVar_Index (weakenTrace X0 k) s a1)) = (subst_TxVar_Index (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) a1))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Ty_subst_TyVar_Index0_commright_ind (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((subst_TyVar_Ty (weakenTrace d k) S0 (subst_TyVar_Index (weakenTrace X0 k) S1 X7)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Index (weakenTrace (XS TyVar d) k) S0 X7)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Tm_subst_TxVar_Index0_commleft_ind (d : (Trace TmVar)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (x3 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace d k) s x3) = (subst_TxVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Index (weakenTrace (XS TxVar d) k) s x3)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Ty_subst_TyVar_Index0_commleft_ind (d : (Trace TmVar)) (s : Tm) (S0 : Ty) :
      (forall (k : Hvl) (x3 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace d k) s x3) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (subst_TmVar_Index (weakenTrace (XS TyVar d) k) s x3)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TxVar_Tm_subst_TmVar_Index0_commleft_ind (d : (Trace TxVar)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (a1 : (Index TxVar)) ,
        ((subst_TxVar_Index (weakenTrace d k) s a1) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TxVar_Tm d s s0) (subst_TxVar_Index (weakenTrace (XS TmVar d) k) s a1)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TxVar_Ty_subst_TyVar_Index0_commleft_ind (d : (Trace TxVar)) (s : Tm) (S0 : Ty) :
      (forall (k : Hvl) (a1 : (Index TxVar)) ,
        ((subst_TxVar_Index (weakenTrace d k) s a1) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (subst_TxVar_Index (weakenTrace (XS TyVar d) k) s a1)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_TyVar__subst_TyVar_0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) {struct S2} :
    ((subst_TyVar_Ty (weakenTrace d k) S0 (subst_TyVar_Ty (weakenTrace X0 k) S1 S2)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S0 S2))) :=
      match S2 return ((subst_TyVar_Ty (weakenTrace d k) S0 (subst_TyVar_Ty (weakenTrace X0 k) S1 S2)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S0 S2))) with
        | (TVar X7) => (subst_TyVar_Ty_subst_TyVar_Index0_commright_ind d S0 S1 k X7)
        | (TArr T7 T8) => (f_equal2 TArr (subst_TyVar__subst_TyVar_0_Ty_comm_ind T7 k d S0 S1) (subst_TyVar__subst_TyVar_0_Ty_comm_ind T8 k d S0 S1))
        | (TAll T6) => (f_equal TAll (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar d k (HS TyVar H0)) eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Ty_comm_ind T6 (HS TyVar k) d S0 S1) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TyVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__subst_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s1} :
    ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s s1))) :=
      match s1 return ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s s1))) with
        | (Var x3) => (subst_TmVar_Tm_subst_TmVar_Index0_commright_ind d s s0 k x3)
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t4 (HS TmVar k) d s s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TmVar__subst_TmVar_0_Tm_comm_ind t5 k d s s0) (subst_TmVar__subst_TmVar_0_Tm_comm_ind t6 k d s s0))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (HS TyVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t4 (HS TyVar k) d s s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TmVar__subst_TmVar_0_Tm_comm_ind t4 k d s s0) eq_refl)
      end.
    Fixpoint subst_TmVar__subst_TxVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s1} :
    ((subst_TmVar_Tm (weakenTrace d k) s (subst_TxVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TxVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (weakenTrace (XS TxVar d) k) s s1))) :=
      match s1 return ((subst_TmVar_Tm (weakenTrace d k) s (subst_TxVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TxVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (weakenTrace (XS TxVar d) k) s s1))) with
        | (Var x3) => (subst_TmVar_Tm_subst_TxVar_Index0_commleft_ind d s s0 k x3)
        | (XVar a1) => (subst_TmVar_Tm_subst_TxVar_Index0_commright_ind d s s0 k a1)
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TxVar_0_Tm_comm_ind t4 (HS TmVar k) d s s0) (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TxVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TmVar__subst_TxVar_0_Tm_comm_ind t5 k d s s0) (subst_TmVar__subst_TxVar_0_Tm_comm_ind t6 k d s s0))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (HS TyVar H0)) eq_refl (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TxVar_0_Tm_comm_ind t4 (HS TyVar k) d s s0) (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TxVar d) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TmVar__subst_TxVar_0_Tm_comm_ind t4 k d s s0) eq_refl)
      end.
    Fixpoint subst_TmVar__subst_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) (S0 : Ty) {struct s0} :
    ((subst_TmVar_Tm (weakenTrace d k) s (subst_TyVar_Tm (weakenTrace X0 k) S0 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s s0))) :=
      match s0 return ((subst_TmVar_Tm (weakenTrace d k) s (subst_TyVar_Tm (weakenTrace X0 k) S0 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s s0))) with
        | (Var x3) => (subst_TmVar_Ty_subst_TyVar_Index0_commleft_ind d s S0 k x3)
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Tm_comm_ind t4 (HS TmVar k) d s S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TmVar__subst_TyVar_0_Tm_comm_ind t5 k d s S0) (subst_TmVar__subst_TyVar_0_Tm_comm_ind t6 k d s S0))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (HS TyVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Tm_comm_ind t4 (HS TyVar k) d s S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TmVar__subst_TyVar_0_Tm_comm_ind t4 k d s S0) eq_refl)
      end.
    Fixpoint subst_TxVar__subst_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace TxVar)) (s : Tm) (s0 : Tm) {struct s1} :
    ((subst_TxVar_Tm (weakenTrace d k) s (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TxVar_Tm d s s0) (subst_TxVar_Tm (weakenTrace (XS TmVar d) k) s s1))) :=
      match s1 return ((subst_TxVar_Tm (weakenTrace d k) s (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TxVar_Tm d s s0) (subst_TxVar_Tm (weakenTrace (XS TmVar d) k) s s1))) with
        | (Var x3) => (subst_TxVar_Tm_subst_TmVar_Index0_commright_ind d s s0 k x3)
        | (XVar a1) => (subst_TxVar_Tm_subst_TmVar_Index0_commleft_ind d s s0 k a1)
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TxVar__subst_TmVar_0_Tm_comm_ind t4 (HS TmVar k) d s s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TxVar__subst_TmVar_0_Tm_comm_ind t5 k d s s0) (subst_TxVar__subst_TmVar_0_Tm_comm_ind t6 k d s s0))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar d k (HS TyVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TxVar__subst_TmVar_0_Tm_comm_ind t4 (HS TyVar k) d s s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar (XS TmVar d) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TxVar__subst_TmVar_0_Tm_comm_ind t4 k d s s0) eq_refl)
      end.
    Fixpoint subst_TxVar__subst_TxVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace TxVar)) (s : Tm) (s0 : Tm) {struct s1} :
    ((subst_TxVar_Tm (weakenTrace d k) s (subst_TxVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TxVar_Tm (weakenTrace X0 k) (subst_TxVar_Tm d s s0) (subst_TxVar_Tm (weakenTrace (XS TxVar d) k) s s1))) :=
      match s1 return ((subst_TxVar_Tm (weakenTrace d k) s (subst_TxVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TxVar_Tm (weakenTrace X0 k) (subst_TxVar_Tm d s s0) (subst_TxVar_Tm (weakenTrace (XS TxVar d) k) s s1))) with
        | (Var x3) => eq_refl
        | (XVar a1) => (subst_TxVar_Tm_subst_TxVar_Index0_commright_ind d s s0 k a1)
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TxVar__subst_TxVar_0_Tm_comm_ind t4 (HS TmVar k) d s s0) (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar (XS TxVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TxVar__subst_TxVar_0_Tm_comm_ind t5 k d s s0) (subst_TxVar__subst_TxVar_0_Tm_comm_ind t6 k d s s0))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar d k (HS TyVar H0)) eq_refl (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TxVar__subst_TxVar_0_Tm_comm_ind t4 (HS TyVar k) d s s0) (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar (XS TxVar d) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TxVar__subst_TxVar_0_Tm_comm_ind t4 k d s s0) eq_refl)
      end.
    Fixpoint subst_TxVar__subst_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TxVar)) (s : Tm) (S0 : Ty) {struct s0} :
    ((subst_TxVar_Tm (weakenTrace d k) s (subst_TyVar_Tm (weakenTrace X0 k) S0 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (subst_TxVar_Tm (weakenTrace (XS TyVar d) k) s s0))) :=
      match s0 return ((subst_TxVar_Tm (weakenTrace d k) s (subst_TyVar_Tm (weakenTrace X0 k) S0 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) S0 (subst_TxVar_Tm (weakenTrace (XS TyVar d) k) s s0))) with
        | (Var x3) => eq_refl
        | (XVar a1) => (subst_TxVar_Ty_subst_TyVar_Index0_commleft_ind d s S0 k a1)
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TxVar__subst_TyVar_0_Tm_comm_ind t4 (HS TmVar k) d s S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TxVar__subst_TyVar_0_Tm_comm_ind t5 k d s S0) (subst_TxVar__subst_TyVar_0_Tm_comm_ind t6 k d s S0))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar d k (HS TyVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TxVar__subst_TyVar_0_Tm_comm_ind t4 (HS TyVar k) d s S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar (XS TyVar d) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TxVar__subst_TyVar_0_Tm_comm_ind t4 k d s S0) eq_refl)
      end.
    Fixpoint subst_TyVar__subst_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (s : Tm) {struct s0} :
    ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) (subst_TyVar_Tm (weakenTrace d k) S0 s0))) :=
      match s0 return ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) (subst_TyVar_Tm (weakenTrace d k) S0 s0))) with
        | (Var x3) => (subst_TyVar_Tm_subst_TmVar_Index0_commright_ind d S0 s k x3)
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Tm_comm_ind t4 (HS TmVar k) d S0 s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TyVar__subst_TmVar_0_Tm_comm_ind t5 k d S0 s) (subst_TyVar__subst_TmVar_0_Tm_comm_ind t6 k d S0 s))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TyVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Tm_comm_ind t4 (HS TyVar k) d S0 s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TyVar__subst_TmVar_0_Tm_comm_ind t4 k d S0 s) eq_refl)
      end.
    Fixpoint subst_TyVar__subst_TxVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (s : Tm) {struct s0} :
    ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TxVar_Tm (weakenTrace X0 k) s s0)) = (subst_TxVar_Tm (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) (subst_TyVar_Tm (weakenTrace d k) S0 s0))) :=
      match s0 return ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TxVar_Tm (weakenTrace X0 k) s s0)) = (subst_TxVar_Tm (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) (subst_TyVar_Tm (weakenTrace d k) S0 s0))) with
        | (Var x3) => eq_refl
        | (XVar a1) => (subst_TyVar_Tm_subst_TxVar_Index0_commright_ind d S0 s k a1)
        | (Abs T6 t4) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TxVar_0_Tm_comm_ind t4 (HS TmVar k) d S0 s) (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TyVar__subst_TxVar_0_Tm_comm_ind t5 k d S0 s) (subst_TyVar__subst_TxVar_0_Tm_comm_ind t6 k d S0 s))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TyVar H0)) eq_refl (f_equal3 subst_TxVar_Tm (weakenTrace_append TxVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TxVar_0_Tm_comm_ind t4 (HS TyVar k) d S0 s) (f_equal3 subst_TxVar_Tm (eq_sym (weakenTrace_append TxVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TyVar__subst_TxVar_0_Tm_comm_ind t4 k d S0 s) eq_refl)
      end.
    Fixpoint subst_TyVar__subst_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) {struct s} :
    ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TyVar_Tm (weakenTrace X0 k) S1 s)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S0 s))) :=
      match s return ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TyVar_Tm (weakenTrace X0 k) S1 s)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S0 s))) with
        | (Var x3) => eq_refl
        | (XVar a1) => eq_refl
        | (Abs T6 t4) => (f_equal2 Abs (subst_TyVar__subst_TyVar_0_Ty_comm_ind T6 k d S0 S1) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Tm_comm_ind t4 (HS TmVar k) d S0 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t5 t6) => (f_equal2 App (subst_TyVar__subst_TyVar_0_Tm_comm_ind t5 k d S0 S1) (subst_TyVar__subst_TyVar_0_Tm_comm_ind t6 k d S0 S1))
        | (TAbs t4) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TyVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Tm_comm_ind t4 (HS TyVar k) d S0 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t4 T6) => (f_equal2 TApp (subst_TyVar__subst_TyVar_0_Tm_comm_ind t4 k d S0 S1) (subst_TyVar__subst_TyVar_0_Ty_comm_ind T6 k d S0 S1))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition subst_TyVar_Ty_subst_TyVar_Ty0_comm (S2 : Ty) : (forall (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) ,
      ((subst_TyVar_Ty d S0 (subst_TyVar_Ty X0 S1 S2)) = (subst_TyVar_Ty X0 (subst_TyVar_Ty d S0 S1) (subst_TyVar_Ty (XS TyVar d) S0 S2)))) := (subst_TyVar__subst_TyVar_0_Ty_comm_ind S2 H0).
    Definition subst_TmVar_Tm_subst_TmVar_Tm0_comm (s1 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) (s0 : Tm) ,
      ((subst_TmVar_Tm d s (subst_TmVar_Tm X0 s0 s1)) = (subst_TmVar_Tm X0 (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (XS TmVar d) s s1)))) := (subst_TmVar__subst_TmVar_0_Tm_comm_ind s1 H0).
    Definition subst_TmVar_Tm_subst_TxVar_Tm0_comm (s1 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) (s0 : Tm) ,
      ((subst_TmVar_Tm d s (subst_TxVar_Tm X0 s0 s1)) = (subst_TxVar_Tm X0 (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (XS TxVar d) s s1)))) := (subst_TmVar__subst_TxVar_0_Tm_comm_ind s1 H0).
    Definition subst_TmVar_Tm_subst_TyVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) (S0 : Ty) ,
      ((subst_TmVar_Tm d s (subst_TyVar_Tm X0 S0 s0)) = (subst_TyVar_Tm X0 S0 (subst_TmVar_Tm (XS TyVar d) s s0)))) := (subst_TmVar__subst_TyVar_0_Tm_comm_ind s0 H0).
    Definition subst_TxVar_Tm_subst_TmVar_Tm0_comm (s1 : Tm) : (forall (d : (Trace TxVar)) (s : Tm) (s0 : Tm) ,
      ((subst_TxVar_Tm d s (subst_TmVar_Tm X0 s0 s1)) = (subst_TmVar_Tm X0 (subst_TxVar_Tm d s s0) (subst_TxVar_Tm (XS TmVar d) s s1)))) := (subst_TxVar__subst_TmVar_0_Tm_comm_ind s1 H0).
    Definition subst_TxVar_Tm_subst_TxVar_Tm0_comm (s1 : Tm) : (forall (d : (Trace TxVar)) (s : Tm) (s0 : Tm) ,
      ((subst_TxVar_Tm d s (subst_TxVar_Tm X0 s0 s1)) = (subst_TxVar_Tm X0 (subst_TxVar_Tm d s s0) (subst_TxVar_Tm (XS TxVar d) s s1)))) := (subst_TxVar__subst_TxVar_0_Tm_comm_ind s1 H0).
    Definition subst_TxVar_Tm_subst_TyVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TxVar)) (s : Tm) (S0 : Ty) ,
      ((subst_TxVar_Tm d s (subst_TyVar_Tm X0 S0 s0)) = (subst_TyVar_Tm X0 S0 (subst_TxVar_Tm (XS TyVar d) s s0)))) := (subst_TxVar__subst_TyVar_0_Tm_comm_ind s0 H0).
    Definition subst_TyVar_Tm_subst_TmVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) (s : Tm) ,
      ((subst_TyVar_Tm d S0 (subst_TmVar_Tm X0 s s0)) = (subst_TmVar_Tm X0 (subst_TyVar_Tm d S0 s) (subst_TyVar_Tm d S0 s0)))) := (subst_TyVar__subst_TmVar_0_Tm_comm_ind s0 H0).
    Definition subst_TyVar_Tm_subst_TxVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) (s : Tm) ,
      ((subst_TyVar_Tm d S0 (subst_TxVar_Tm X0 s s0)) = (subst_TxVar_Tm X0 (subst_TyVar_Tm d S0 s) (subst_TyVar_Tm d S0 s0)))) := (subst_TyVar__subst_TxVar_0_Tm_comm_ind s0 H0).
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
    Lemma weakenTm_subst_TxVar_Tm  :
      (forall (k : Hvl) (d : (Trace TxVar)) (s : Tm) (s0 : Tm) ,
        ((weakenTm (subst_TxVar_Tm d s s0) k) = (subst_TxVar_Tm (weakenTrace d k) s (weakenTm s0 k)))).
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
 Hint Rewrite subst_TmVar_Tm_subst_TmVar_Tm0_comm subst_TxVar_Tm_subst_TxVar_Tm0_comm subst_TyVar_Tm_subst_TyVar_Tm0_comm subst_TyVar_Ty_subst_TyVar_Ty0_comm : interaction.
 Hint Rewrite subst_TmVar_Tm_subst_TmVar_Tm0_comm subst_TxVar_Tm_subst_TxVar_Tm0_comm subst_TyVar_Tm_subst_TyVar_Tm0_comm subst_TyVar_Ty_subst_TyVar_Ty0_comm : subst_subst0.
 Hint Rewrite weakenTm_shift_TmVar_Tm weakenTm_shift_TxVar_Tm weakenTm_shift_TyVar_Tm weakenTy_shift_TyVar_Ty : weaken_shift.
 Hint Rewrite weakenTm_subst_TmVar_Tm weakenTm_subst_TxVar_Tm weakenTm_subst_TyVar_Tm weakenTy_subst_TyVar_Ty : weaken_subst.
Section WellFormed.
  Fixpoint wfindex {a1 : Namespace} (k : Hvl) (i : (Index a1)) {struct k} :
  Prop :=
    match k with
      | (H0) => False
      | (HS b k) => match (eq_namespace_dec a1 b) with
        | (left e) => match i with
          | (I0) => True
          | (IS i) => (wfindex k i)
        end
        | (right n) => (wfindex k i)
      end
    end.
  Inductive wfTy (k : Hvl) : Ty -> Prop :=
    | wfTy_TVar
        (X7 : (Index TyVar))
        (wfi : (wfindex k X7)) :
        (wfTy k (TVar X7))
    | wfTy_TArr {T6 : Ty}
        (wf : (wfTy k T6)) {T7 : Ty}
        (wf0 : (wfTy k T7)) :
        (wfTy k (TArr T6 T7))
    | wfTy_TAll {T8 : Ty}
        (wf : (wfTy (HS TyVar k) T8)) :
        (wfTy k (TAll T8)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_Var
        (x3 : (Index TmVar))
        (wfi : (wfindex k x3)) :
        (wfTm k (Var x3))
    | wfTm_XVar (a1 : (Index TxVar))
        (wfi : (wfindex k a1)) :
        (wfTm k (XVar a1))
    | wfTm_Abs {T6 : Ty}
        (wf : (wfTy k T6)) {t4 : Tm}
        (wf0 : (wfTm (HS TmVar k) t4)) :
        (wfTm k (Abs T6 t4))
    | wfTm_App {t5 : Tm}
        (wf : (wfTm k t5)) {t6 : Tm}
        (wf0 : (wfTm k t6)) :
        (wfTm k (App t5 t6))
    | wfTm_TAbs {t7 : Tm}
        (wf : (wfTm (HS TyVar k) t7)) :
        (wfTm k (TAbs t7))
    | wfTm_TApp {t8 : Tm}
        (wf : (wfTm k t8)) {T7 : Ty}
        (wf0 : (wfTy k T7)) :
        (wfTm k (TApp t8 T7)).
  Definition inversion_wfTy_TVar_1 (k : Hvl) (X : (Index TyVar)) (H16 : (wfTy k (TVar X))) : (wfindex k X) := match H16 in (wfTy _ S0) return match S0 return Prop with
    | (TVar X) => (wfindex k X)
    | _ => True
  end with
    | (wfTy_TVar X H1) => H1
    | _ => I
  end.
  Definition inversion_wfTy_TArr_0 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H17 : (wfTy k0 (TArr T1 T2))) : (wfTy k0 T1) := match H17 in (wfTy _ S1) return match S1 return Prop with
    | (TArr T1 T2) => (wfTy k0 T1)
    | _ => True
  end with
    | (wfTy_TArr T1 H2 T2 H3) => H2
    | _ => I
  end.
  Definition inversion_wfTy_TArr_1 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H17 : (wfTy k0 (TArr T1 T2))) : (wfTy k0 T2) := match H17 in (wfTy _ S1) return match S1 return Prop with
    | (TArr T1 T2) => (wfTy k0 T2)
    | _ => True
  end with
    | (wfTy_TArr T1 H2 T2 H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_TAll_1 (k1 : Hvl) (T : Ty) (H18 : (wfTy k1 (TAll T))) : (wfTy (HS TyVar k1) T) := match H18 in (wfTy _ S2) return match S2 return Prop with
    | (TAll T) => (wfTy (HS TyVar k1) T)
    | _ => True
  end with
    | (wfTy_TAll T H4) => H4
    | _ => I
  end.
  Definition inversion_wfTm_Var_1 (k2 : Hvl) (x : (Index TmVar)) (H19 : (wfTm k2 (Var x))) : (wfindex k2 x) := match H19 in (wfTm _ s) return match s return Prop with
    | (Var x) => (wfindex k2 x)
    | _ => True
  end with
    | (wfTm_Var x H5) => H5
    | _ => I
  end.
  Definition inversion_wfTm_XVar_1 (k3 : Hvl) (a : (Index TxVar)) (H20 : (wfTm k3 (XVar a))) : (wfindex k3 a) := match H20 in (wfTm _ s0) return match s0 return Prop with
    | (XVar a) => (wfindex k3 a)
    | _ => True
  end with
    | (wfTm_XVar a H6) => H6
    | _ => I
  end.
  Definition inversion_wfTm_Abs_1 (k4 : Hvl) (T : Ty) (t : Tm) (H21 : (wfTm k4 (Abs T t))) : (wfTy k4 T) := match H21 in (wfTm _ s1) return match s1 return Prop with
    | (Abs T t) => (wfTy k4 T)
    | _ => True
  end with
    | (wfTm_Abs T H7 t H8) => H7
    | _ => I
  end.
  Definition inversion_wfTm_Abs_2 (k4 : Hvl) (T : Ty) (t : Tm) (H21 : (wfTm k4 (Abs T t))) : (wfTm (HS TmVar k4) t) := match H21 in (wfTm _ s1) return match s1 return Prop with
    | (Abs T t) => (wfTm (HS TmVar k4) t)
    | _ => True
  end with
    | (wfTm_Abs T H7 t H8) => H8
    | _ => I
  end.
  Definition inversion_wfTm_App_0 (k5 : Hvl) (t1 : Tm) (t2 : Tm) (H22 : (wfTm k5 (App t1 t2))) : (wfTm k5 t1) := match H22 in (wfTm _ s2) return match s2 return Prop with
    | (App t1 t2) => (wfTm k5 t1)
    | _ => True
  end with
    | (wfTm_App t1 H9 t2 H10) => H9
    | _ => I
  end.
  Definition inversion_wfTm_App_1 (k5 : Hvl) (t1 : Tm) (t2 : Tm) (H22 : (wfTm k5 (App t1 t2))) : (wfTm k5 t2) := match H22 in (wfTm _ s2) return match s2 return Prop with
    | (App t1 t2) => (wfTm k5 t2)
    | _ => True
  end with
    | (wfTm_App t1 H9 t2 H10) => H10
    | _ => I
  end.
  Definition inversion_wfTm_TAbs_1 (k6 : Hvl) (t : Tm) (H23 : (wfTm k6 (TAbs t))) : (wfTm (HS TyVar k6) t) := match H23 in (wfTm _ s3) return match s3 return Prop with
    | (TAbs t) => (wfTm (HS TyVar k6) t)
    | _ => True
  end with
    | (wfTm_TAbs t H11) => H11
    | _ => I
  end.
  Definition inversion_wfTm_TApp_0 (k7 : Hvl) (t : Tm) (T : Ty) (H24 : (wfTm k7 (TApp t T))) : (wfTm k7 t) := match H24 in (wfTm _ s4) return match s4 return Prop with
    | (TApp t T) => (wfTm k7 t)
    | _ => True
  end with
    | (wfTm_TApp t H12 T H13) => H12
    | _ => I
  end.
  Definition inversion_wfTm_TApp_1 (k7 : Hvl) (t : Tm) (T : Ty) (H24 : (wfTm k7 (TApp t T))) : (wfTy k7 T) := match H24 in (wfTm _ s4) return match s4 return Prop with
    | (TApp t T) => (wfTy k7 T)
    | _ => True
  end with
    | (wfTm_TApp t H12 T H13) => H13
    | _ => I
  end.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_TmVar : (forall (c : (Cutoff TmVar)) (k8 : Hvl) (k9 : Hvl) ,
    Prop) :=
    | shifthvl_TmVar_here
        (k8 : Hvl) :
        (shifthvl_TmVar C0 k8 (HS TmVar k8))
    | shifthvl_TmVar_there_TmVar
        (c : (Cutoff TmVar)) (k8 : Hvl)
        (k9 : Hvl) :
        (shifthvl_TmVar c k8 k9) -> (shifthvl_TmVar (CS c) (HS TmVar k8) (HS TmVar k9))
    | shifthvl_TmVar_there_TxVar
        (c : (Cutoff TmVar)) (k8 : Hvl)
        (k9 : Hvl) :
        (shifthvl_TmVar c k8 k9) -> (shifthvl_TmVar c (HS TxVar k8) (HS TxVar k9))
    | shifthvl_TmVar_there_TyVar
        (c : (Cutoff TmVar)) (k8 : Hvl)
        (k9 : Hvl) :
        (shifthvl_TmVar c k8 k9) -> (shifthvl_TmVar c (HS TyVar k8) (HS TyVar k9)).
  Inductive shifthvl_TxVar : (forall (c : (Cutoff TxVar)) (k8 : Hvl) (k9 : Hvl) ,
    Prop) :=
    | shifthvl_TxVar_here
        (k8 : Hvl) :
        (shifthvl_TxVar C0 k8 (HS TxVar k8))
    | shifthvl_TxVar_there_TmVar
        (c : (Cutoff TxVar)) (k8 : Hvl)
        (k9 : Hvl) :
        (shifthvl_TxVar c k8 k9) -> (shifthvl_TxVar c (HS TmVar k8) (HS TmVar k9))
    | shifthvl_TxVar_there_TxVar
        (c : (Cutoff TxVar)) (k8 : Hvl)
        (k9 : Hvl) :
        (shifthvl_TxVar c k8 k9) -> (shifthvl_TxVar (CS c) (HS TxVar k8) (HS TxVar k9))
    | shifthvl_TxVar_there_TyVar
        (c : (Cutoff TxVar)) (k8 : Hvl)
        (k9 : Hvl) :
        (shifthvl_TxVar c k8 k9) -> (shifthvl_TxVar c (HS TyVar k8) (HS TyVar k9)).
  Inductive shifthvl_TyVar : (forall (c : (Cutoff TyVar)) (k8 : Hvl) (k9 : Hvl) ,
    Prop) :=
    | shifthvl_TyVar_here
        (k8 : Hvl) :
        (shifthvl_TyVar C0 k8 (HS TyVar k8))
    | shifthvl_TyVar_there_TmVar
        (c : (Cutoff TyVar)) (k8 : Hvl)
        (k9 : Hvl) :
        (shifthvl_TyVar c k8 k9) -> (shifthvl_TyVar c (HS TmVar k8) (HS TmVar k9))
    | shifthvl_TyVar_there_TxVar
        (c : (Cutoff TyVar)) (k8 : Hvl)
        (k9 : Hvl) :
        (shifthvl_TyVar c k8 k9) -> (shifthvl_TyVar c (HS TxVar k8) (HS TxVar k9))
    | shifthvl_TyVar_there_TyVar
        (c : (Cutoff TyVar)) (k8 : Hvl)
        (k9 : Hvl) :
        (shifthvl_TyVar c k8 k9) -> (shifthvl_TyVar (CS c) (HS TyVar k8) (HS TyVar k9)).
  Lemma weaken_shifthvl_TmVar  :
    (forall (k8 : Hvl) {c : (Cutoff TmVar)} {k9 : Hvl} {k10 : Hvl} ,
      (shifthvl_TmVar c k9 k10) -> (shifthvl_TmVar (weakenCutoffTmVar c k8) (appendHvl k9 k8) (appendHvl k10 k8))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_TxVar  :
    (forall (k8 : Hvl) {c : (Cutoff TxVar)} {k9 : Hvl} {k10 : Hvl} ,
      (shifthvl_TxVar c k9 k10) -> (shifthvl_TxVar (weakenCutoffTxVar c k8) (appendHvl k9 k8) (appendHvl k10 k8))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_TyVar  :
    (forall (k8 : Hvl) {c : (Cutoff TyVar)} {k9 : Hvl} {k10 : Hvl} ,
      (shifthvl_TyVar c k9 k10) -> (shifthvl_TyVar (weakenCutoffTyVar c k8) (appendHvl k9 k8) (appendHvl k10 k8))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_TmVar__wfindex_TmVar  :
    (forall (c : (Cutoff TmVar)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_TmVar c k8 k9)) (x3 : (Index TmVar)) ,
      (wfindex k8 x3) -> (wfindex k9 (shift_TmVar_Index c x3))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TmVar__wfindex_TxVar  :
    (forall (c : (Cutoff TmVar)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_TmVar c k8 k9)) (a1 : (Index TxVar)) ,
      (wfindex k8 a1) -> (wfindex k9 a1)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TmVar__wfindex_TyVar  :
    (forall (c : (Cutoff TmVar)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_TmVar c k8 k9)) (X7 : (Index TyVar)) ,
      (wfindex k8 X7) -> (wfindex k9 X7)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TxVar__wfindex_TmVar  :
    (forall (c : (Cutoff TxVar)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_TxVar c k8 k9)) (x3 : (Index TmVar)) ,
      (wfindex k8 x3) -> (wfindex k9 x3)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TxVar__wfindex_TxVar  :
    (forall (c : (Cutoff TxVar)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_TxVar c k8 k9)) (a1 : (Index TxVar)) ,
      (wfindex k8 a1) -> (wfindex k9 (shift_TxVar_Index c a1))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TxVar__wfindex_TyVar  :
    (forall (c : (Cutoff TxVar)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_TxVar c k8 k9)) (X7 : (Index TyVar)) ,
      (wfindex k8 X7) -> (wfindex k9 X7)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TyVar__wfindex_TmVar  :
    (forall (c : (Cutoff TyVar)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_TyVar c k8 k9)) (x3 : (Index TmVar)) ,
      (wfindex k8 x3) -> (wfindex k9 x3)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TyVar__wfindex_TxVar  :
    (forall (c : (Cutoff TyVar)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_TyVar c k8 k9)) (a1 : (Index TxVar)) ,
      (wfindex k8 a1) -> (wfindex k9 a1)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TyVar__wfindex_TyVar  :
    (forall (c : (Cutoff TyVar)) (k8 : Hvl) (k9 : Hvl) (ins : (shifthvl_TyVar c k8 k9)) (X7 : (Index TyVar)) ,
      (wfindex k8 X7) -> (wfindex k9 (shift_TyVar_Index c X7))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_TmVar__wfTy : (forall (k8 : Hvl) ,
    (forall (S3 : Ty) (wf : (wfTy k8 S3)) ,
      (forall (c : (Cutoff TmVar)) (k9 : Hvl) ,
        (shifthvl_TmVar c k8 k9) -> (wfTy k9 S3)))) := (ind_wfTy (fun (k8 : Hvl) (S3 : Ty) (wf : (wfTy k8 S3)) =>
    (forall (c : (Cutoff TmVar)) (k9 : Hvl) ,
      (shifthvl_TmVar c k8 k9) -> (wfTy k9 S3))) (fun (k8 : Hvl) (X7 : (Index TyVar)) (wfi : (wfindex k8 X7)) (c : (Cutoff TmVar)) (k9 : Hvl) (ins : (shifthvl_TmVar c k8 k9)) =>
    (wfTy_TVar k9 _ (shift_TmVar__wfindex_TyVar c k8 k9 ins X7 wfi))) (fun (k8 : Hvl) (T1 : Ty) (wf : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k8 T2)) IHT2 (c : (Cutoff TmVar)) (k9 : Hvl) (ins : (shifthvl_TmVar c k8 k9)) =>
    (wfTy_TArr k9 (IHT1 c k9 (weaken_shifthvl_TmVar H0 ins)) (IHT2 c k9 (weaken_shifthvl_TmVar H0 ins)))) (fun (k8 : Hvl) (T : Ty) (wf : (wfTy (HS TyVar k8) T)) IHT (c : (Cutoff TmVar)) (k9 : Hvl) (ins : (shifthvl_TmVar c k8 k9)) =>
    (wfTy_TAll k9 (IHT c (HS TyVar k9) (weaken_shifthvl_TmVar (HS TyVar H0) ins))))).
  Definition shift_TxVar__wfTy : (forall (k8 : Hvl) ,
    (forall (S3 : Ty) (wf : (wfTy k8 S3)) ,
      (forall (c : (Cutoff TxVar)) (k9 : Hvl) ,
        (shifthvl_TxVar c k8 k9) -> (wfTy k9 S3)))) := (ind_wfTy (fun (k8 : Hvl) (S3 : Ty) (wf : (wfTy k8 S3)) =>
    (forall (c : (Cutoff TxVar)) (k9 : Hvl) ,
      (shifthvl_TxVar c k8 k9) -> (wfTy k9 S3))) (fun (k8 : Hvl) (X7 : (Index TyVar)) (wfi : (wfindex k8 X7)) (c : (Cutoff TxVar)) (k9 : Hvl) (ins : (shifthvl_TxVar c k8 k9)) =>
    (wfTy_TVar k9 _ (shift_TxVar__wfindex_TyVar c k8 k9 ins X7 wfi))) (fun (k8 : Hvl) (T1 : Ty) (wf : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k8 T2)) IHT2 (c : (Cutoff TxVar)) (k9 : Hvl) (ins : (shifthvl_TxVar c k8 k9)) =>
    (wfTy_TArr k9 (IHT1 c k9 (weaken_shifthvl_TxVar H0 ins)) (IHT2 c k9 (weaken_shifthvl_TxVar H0 ins)))) (fun (k8 : Hvl) (T : Ty) (wf : (wfTy (HS TyVar k8) T)) IHT (c : (Cutoff TxVar)) (k9 : Hvl) (ins : (shifthvl_TxVar c k8 k9)) =>
    (wfTy_TAll k9 (IHT c (HS TyVar k9) (weaken_shifthvl_TxVar (HS TyVar H0) ins))))).
  Definition shift_TyVar__wfTy : (forall (k8 : Hvl) ,
    (forall (S3 : Ty) (wf : (wfTy k8 S3)) ,
      (forall (c : (Cutoff TyVar)) (k9 : Hvl) ,
        (shifthvl_TyVar c k8 k9) -> (wfTy k9 (shift_TyVar_Ty c S3))))) := (ind_wfTy (fun (k8 : Hvl) (S3 : Ty) (wf : (wfTy k8 S3)) =>
    (forall (c : (Cutoff TyVar)) (k9 : Hvl) ,
      (shifthvl_TyVar c k8 k9) -> (wfTy k9 (shift_TyVar_Ty c S3)))) (fun (k8 : Hvl) (X7 : (Index TyVar)) (wfi : (wfindex k8 X7)) (c : (Cutoff TyVar)) (k9 : Hvl) (ins : (shifthvl_TyVar c k8 k9)) =>
    (wfTy_TVar k9 _ (shift_TyVar__wfindex_TyVar c k8 k9 ins X7 wfi))) (fun (k8 : Hvl) (T1 : Ty) (wf : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k8 T2)) IHT2 (c : (Cutoff TyVar)) (k9 : Hvl) (ins : (shifthvl_TyVar c k8 k9)) =>
    (wfTy_TArr k9 (IHT1 c k9 (weaken_shifthvl_TyVar H0 ins)) (IHT2 c k9 (weaken_shifthvl_TyVar H0 ins)))) (fun (k8 : Hvl) (T : Ty) (wf : (wfTy (HS TyVar k8) T)) IHT (c : (Cutoff TyVar)) (k9 : Hvl) (ins : (shifthvl_TyVar c k8 k9)) =>
    (wfTy_TAll k9 (IHT (CS c) (HS TyVar k9) (weaken_shifthvl_TyVar (HS TyVar H0) ins))))).
  Definition shift_TmVar__wfTm : (forall (k8 : Hvl) ,
    (forall (s5 : Tm) (wf : (wfTm k8 s5)) ,
      (forall (c : (Cutoff TmVar)) (k9 : Hvl) ,
        (shifthvl_TmVar c k8 k9) -> (wfTm k9 (shift_TmVar_Tm c s5))))) := (ind_wfTm (fun (k8 : Hvl) (s5 : Tm) (wf : (wfTm k8 s5)) =>
    (forall (c : (Cutoff TmVar)) (k9 : Hvl) ,
      (shifthvl_TmVar c k8 k9) -> (wfTm k9 (shift_TmVar_Tm c s5)))) (fun (k8 : Hvl) (x3 : (Index TmVar)) (wfi : (wfindex k8 x3)) (c : (Cutoff TmVar)) (k9 : Hvl) (ins : (shifthvl_TmVar c k8 k9)) =>
    (wfTm_Var k9 _ (shift_TmVar__wfindex_TmVar c k8 k9 ins x3 wfi))) (fun (k8 : Hvl) (a1 : (Index TxVar)) (wfi : (wfindex k8 a1)) (c : (Cutoff TmVar)) (k9 : Hvl) (ins : (shifthvl_TmVar c k8 k9)) =>
    (wfTm_XVar k9 _ (shift_TmVar__wfindex_TxVar c k8 k9 ins a1 wfi))) (fun (k8 : Hvl) (T : Ty) (wf : (wfTy k8 T)) (t : Tm) (wf0 : (wfTm (HS TmVar k8) t)) IHt (c : (Cutoff TmVar)) (k9 : Hvl) (ins : (shifthvl_TmVar c k8 k9)) =>
    (wfTm_Abs k9 (shift_TmVar__wfTy k8 T wf c k9 (weaken_shifthvl_TmVar H0 ins)) (IHt (CS c) (HS TmVar k9) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k8 : Hvl) (t1 : Tm) (wf : (wfTm k8 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k8 t2)) IHt2 (c : (Cutoff TmVar)) (k9 : Hvl) (ins : (shifthvl_TmVar c k8 k9)) =>
    (wfTm_App k9 (IHt1 c k9 (weaken_shifthvl_TmVar H0 ins)) (IHt2 c k9 (weaken_shifthvl_TmVar H0 ins)))) (fun (k8 : Hvl) (t : Tm) (wf : (wfTm (HS TyVar k8) t)) IHt (c : (Cutoff TmVar)) (k9 : Hvl) (ins : (shifthvl_TmVar c k8 k9)) =>
    (wfTm_TAbs k9 (IHt c (HS TyVar k9) (weaken_shifthvl_TmVar (HS TyVar H0) ins)))) (fun (k8 : Hvl) (t : Tm) (wf : (wfTm k8 t)) IHt (T : Ty) (wf0 : (wfTy k8 T)) (c : (Cutoff TmVar)) (k9 : Hvl) (ins : (shifthvl_TmVar c k8 k9)) =>
    (wfTm_TApp k9 (IHt c k9 (weaken_shifthvl_TmVar H0 ins)) (shift_TmVar__wfTy k8 T wf0 c k9 (weaken_shifthvl_TmVar H0 ins))))).
  Definition shift_TxVar__wfTm : (forall (k8 : Hvl) ,
    (forall (s5 : Tm) (wf : (wfTm k8 s5)) ,
      (forall (c : (Cutoff TxVar)) (k9 : Hvl) ,
        (shifthvl_TxVar c k8 k9) -> (wfTm k9 (shift_TxVar_Tm c s5))))) := (ind_wfTm (fun (k8 : Hvl) (s5 : Tm) (wf : (wfTm k8 s5)) =>
    (forall (c : (Cutoff TxVar)) (k9 : Hvl) ,
      (shifthvl_TxVar c k8 k9) -> (wfTm k9 (shift_TxVar_Tm c s5)))) (fun (k8 : Hvl) (x3 : (Index TmVar)) (wfi : (wfindex k8 x3)) (c : (Cutoff TxVar)) (k9 : Hvl) (ins : (shifthvl_TxVar c k8 k9)) =>
    (wfTm_Var k9 _ (shift_TxVar__wfindex_TmVar c k8 k9 ins x3 wfi))) (fun (k8 : Hvl) (a1 : (Index TxVar)) (wfi : (wfindex k8 a1)) (c : (Cutoff TxVar)) (k9 : Hvl) (ins : (shifthvl_TxVar c k8 k9)) =>
    (wfTm_XVar k9 _ (shift_TxVar__wfindex_TxVar c k8 k9 ins a1 wfi))) (fun (k8 : Hvl) (T : Ty) (wf : (wfTy k8 T)) (t : Tm) (wf0 : (wfTm (HS TmVar k8) t)) IHt (c : (Cutoff TxVar)) (k9 : Hvl) (ins : (shifthvl_TxVar c k8 k9)) =>
    (wfTm_Abs k9 (shift_TxVar__wfTy k8 T wf c k9 (weaken_shifthvl_TxVar H0 ins)) (IHt c (HS TmVar k9) (weaken_shifthvl_TxVar (HS TmVar H0) ins)))) (fun (k8 : Hvl) (t1 : Tm) (wf : (wfTm k8 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k8 t2)) IHt2 (c : (Cutoff TxVar)) (k9 : Hvl) (ins : (shifthvl_TxVar c k8 k9)) =>
    (wfTm_App k9 (IHt1 c k9 (weaken_shifthvl_TxVar H0 ins)) (IHt2 c k9 (weaken_shifthvl_TxVar H0 ins)))) (fun (k8 : Hvl) (t : Tm) (wf : (wfTm (HS TyVar k8) t)) IHt (c : (Cutoff TxVar)) (k9 : Hvl) (ins : (shifthvl_TxVar c k8 k9)) =>
    (wfTm_TAbs k9 (IHt c (HS TyVar k9) (weaken_shifthvl_TxVar (HS TyVar H0) ins)))) (fun (k8 : Hvl) (t : Tm) (wf : (wfTm k8 t)) IHt (T : Ty) (wf0 : (wfTy k8 T)) (c : (Cutoff TxVar)) (k9 : Hvl) (ins : (shifthvl_TxVar c k8 k9)) =>
    (wfTm_TApp k9 (IHt c k9 (weaken_shifthvl_TxVar H0 ins)) (shift_TxVar__wfTy k8 T wf0 c k9 (weaken_shifthvl_TxVar H0 ins))))).
  Definition shift_TyVar__wfTm : (forall (k8 : Hvl) ,
    (forall (s5 : Tm) (wf : (wfTm k8 s5)) ,
      (forall (c : (Cutoff TyVar)) (k9 : Hvl) ,
        (shifthvl_TyVar c k8 k9) -> (wfTm k9 (shift_TyVar_Tm c s5))))) := (ind_wfTm (fun (k8 : Hvl) (s5 : Tm) (wf : (wfTm k8 s5)) =>
    (forall (c : (Cutoff TyVar)) (k9 : Hvl) ,
      (shifthvl_TyVar c k8 k9) -> (wfTm k9 (shift_TyVar_Tm c s5)))) (fun (k8 : Hvl) (x3 : (Index TmVar)) (wfi : (wfindex k8 x3)) (c : (Cutoff TyVar)) (k9 : Hvl) (ins : (shifthvl_TyVar c k8 k9)) =>
    (wfTm_Var k9 _ (shift_TyVar__wfindex_TmVar c k8 k9 ins x3 wfi))) (fun (k8 : Hvl) (a1 : (Index TxVar)) (wfi : (wfindex k8 a1)) (c : (Cutoff TyVar)) (k9 : Hvl) (ins : (shifthvl_TyVar c k8 k9)) =>
    (wfTm_XVar k9 _ (shift_TyVar__wfindex_TxVar c k8 k9 ins a1 wfi))) (fun (k8 : Hvl) (T : Ty) (wf : (wfTy k8 T)) (t : Tm) (wf0 : (wfTm (HS TmVar k8) t)) IHt (c : (Cutoff TyVar)) (k9 : Hvl) (ins : (shifthvl_TyVar c k8 k9)) =>
    (wfTm_Abs k9 (shift_TyVar__wfTy k8 T wf c k9 (weaken_shifthvl_TyVar H0 ins)) (IHt c (HS TmVar k9) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k8 : Hvl) (t1 : Tm) (wf : (wfTm k8 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k8 t2)) IHt2 (c : (Cutoff TyVar)) (k9 : Hvl) (ins : (shifthvl_TyVar c k8 k9)) =>
    (wfTm_App k9 (IHt1 c k9 (weaken_shifthvl_TyVar H0 ins)) (IHt2 c k9 (weaken_shifthvl_TyVar H0 ins)))) (fun (k8 : Hvl) (t : Tm) (wf : (wfTm (HS TyVar k8) t)) IHt (c : (Cutoff TyVar)) (k9 : Hvl) (ins : (shifthvl_TyVar c k8 k9)) =>
    (wfTm_TAbs k9 (IHt (CS c) (HS TyVar k9) (weaken_shifthvl_TyVar (HS TyVar H0) ins)))) (fun (k8 : Hvl) (t : Tm) (wf : (wfTm k8 t)) IHt (T : Ty) (wf0 : (wfTy k8 T)) (c : (Cutoff TyVar)) (k9 : Hvl) (ins : (shifthvl_TyVar c k8 k9)) =>
    (wfTm_TApp k9 (IHt c k9 (weaken_shifthvl_TyVar H0 ins)) (shift_TyVar__wfTy k8 T wf0 c k9 (weaken_shifthvl_TyVar H0 ins))))).
  Fixpoint weaken_wfTy (k8 : Hvl) {struct k8} :
  (forall (k9 : Hvl) (S3 : Ty) (wf : (wfTy k9 S3)) ,
    (wfTy (appendHvl k9 k8) (weakenTy S3 k8))) :=
    match k8 return (forall (k9 : Hvl) (S3 : Ty) (wf : (wfTy k9 S3)) ,
      (wfTy (appendHvl k9 k8) (weakenTy S3 k8))) with
      | (H0) => (fun (k9 : Hvl) (S3 : Ty) (wf : (wfTy k9 S3)) =>
        wf)
      | (HS TmVar k8) => (fun (k9 : Hvl) (S3 : Ty) (wf : (wfTy k9 S3)) =>
        (shift_TmVar__wfTy (appendHvl k9 k8) (weakenTy S3 k8) (weaken_wfTy k8 k9 S3 wf) C0 (HS TmVar (appendHvl k9 k8)) (shifthvl_TmVar_here (appendHvl k9 k8))))
      | (HS TxVar k8) => (fun (k9 : Hvl) (S3 : Ty) (wf : (wfTy k9 S3)) =>
        (shift_TxVar__wfTy (appendHvl k9 k8) (weakenTy S3 k8) (weaken_wfTy k8 k9 S3 wf) C0 (HS TxVar (appendHvl k9 k8)) (shifthvl_TxVar_here (appendHvl k9 k8))))
      | (HS TyVar k8) => (fun (k9 : Hvl) (S3 : Ty) (wf : (wfTy k9 S3)) =>
        (shift_TyVar__wfTy (appendHvl k9 k8) (weakenTy S3 k8) (weaken_wfTy k8 k9 S3 wf) C0 (HS TyVar (appendHvl k9 k8)) (shifthvl_TyVar_here (appendHvl k9 k8))))
    end.
  Fixpoint weaken_wfTm (k8 : Hvl) {struct k8} :
  (forall (k9 : Hvl) (s5 : Tm) (wf : (wfTm k9 s5)) ,
    (wfTm (appendHvl k9 k8) (weakenTm s5 k8))) :=
    match k8 return (forall (k9 : Hvl) (s5 : Tm) (wf : (wfTm k9 s5)) ,
      (wfTm (appendHvl k9 k8) (weakenTm s5 k8))) with
      | (H0) => (fun (k9 : Hvl) (s5 : Tm) (wf : (wfTm k9 s5)) =>
        wf)
      | (HS TmVar k8) => (fun (k9 : Hvl) (s5 : Tm) (wf : (wfTm k9 s5)) =>
        (shift_TmVar__wfTm (appendHvl k9 k8) (weakenTm s5 k8) (weaken_wfTm k8 k9 s5 wf) C0 (HS TmVar (appendHvl k9 k8)) (shifthvl_TmVar_here (appendHvl k9 k8))))
      | (HS TxVar k8) => (fun (k9 : Hvl) (s5 : Tm) (wf : (wfTm k9 s5)) =>
        (shift_TxVar__wfTm (appendHvl k9 k8) (weakenTm s5 k8) (weaken_wfTm k8 k9 s5 wf) C0 (HS TxVar (appendHvl k9 k8)) (shifthvl_TxVar_here (appendHvl k9 k8))))
      | (HS TyVar k8) => (fun (k9 : Hvl) (s5 : Tm) (wf : (wfTm k9 s5)) =>
        (shift_TyVar__wfTm (appendHvl k9 k8) (weakenTm s5 k8) (weaken_wfTm k8 k9 s5 wf) C0 (HS TyVar (appendHvl k9 k8)) (shifthvl_TyVar_here (appendHvl k9 k8))))
    end.
End ShiftWellFormed.
Lemma wfTy_cast  :
  (forall (k8 : Hvl) (S3 : Ty) (k9 : Hvl) (S4 : Ty) ,
    (k8 = k9) -> (S3 = S4) -> (wfTy k8 S3) -> (wfTy k9 S4)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k8 : Hvl) (s5 : Tm) (k9 : Hvl) (s6 : Tm) ,
    (k8 = k9) -> (s5 = s6) -> (wfTm k8 s5) -> (wfTm k9 s6)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TxVar shift_TmVar__wfindex_TyVar shift_TxVar__wfindex_TmVar shift_TxVar__wfindex_TxVar shift_TxVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TxVar shift_TyVar__wfindex_TyVar : infra.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TxVar shift_TmVar__wfindex_TyVar shift_TxVar__wfindex_TmVar shift_TxVar__wfindex_TxVar shift_TxVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TxVar shift_TyVar__wfindex_TyVar : shift.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TxVar shift_TmVar__wfindex_TyVar shift_TxVar__wfindex_TmVar shift_TxVar__wfindex_TxVar shift_TxVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TxVar shift_TyVar__wfindex_TyVar : shift_wf.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TxVar shift_TmVar__wfindex_TyVar shift_TxVar__wfindex_TmVar shift_TxVar__wfindex_TxVar shift_TxVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TxVar shift_TyVar__wfindex_TyVar : wf.
 Hint Resolve shift_TmVar__wfTm shift_TmVar__wfTy shift_TxVar__wfTm shift_TxVar__wfTy shift_TyVar__wfTm shift_TyVar__wfTy : infra.
 Hint Resolve shift_TmVar__wfTm shift_TmVar__wfTy shift_TxVar__wfTm shift_TxVar__wfTy shift_TyVar__wfTm shift_TyVar__wfTy : shift.
 Hint Resolve shift_TmVar__wfTm shift_TmVar__wfTy shift_TxVar__wfTm shift_TxVar__wfTy shift_TyVar__wfTm shift_TyVar__wfTy : shift_wf.
 Hint Resolve shift_TmVar__wfTm shift_TmVar__wfTy shift_TxVar__wfTm shift_TxVar__wfTy shift_TyVar__wfTm shift_TyVar__wfTy : wf.
 Hint Constructors shifthvl_TmVar shifthvl_TxVar shifthvl_TyVar : infra.
 Hint Constructors shifthvl_TmVar shifthvl_TxVar shifthvl_TyVar : shift.
 Hint Constructors shifthvl_TmVar shifthvl_TxVar shifthvl_TyVar : shift_wf.
 Hint Constructors shifthvl_TmVar shifthvl_TxVar shifthvl_TyVar : wf.
 Hint Resolve weaken_shifthvl_TmVar weaken_shifthvl_TxVar weaken_shifthvl_TyVar : infra.
 Hint Resolve weaken_shifthvl_TmVar weaken_shifthvl_TxVar weaken_shifthvl_TyVar : shift.
 Hint Resolve weaken_shifthvl_TmVar weaken_shifthvl_TxVar weaken_shifthvl_TyVar : shift_wf.
 Hint Resolve weaken_shifthvl_TmVar weaken_shifthvl_TxVar weaken_shifthvl_TyVar : weaken.
 Hint Resolve weaken_shifthvl_TmVar weaken_shifthvl_TxVar weaken_shifthvl_TyVar : wf.
Section SubstWellFormed.
  Inductive substhvl_TmVar (k8 : Hvl) : (forall (d : (Trace TmVar)) (k9 : Hvl) (k10 : Hvl) ,
    Prop) :=
    | substhvl_TmVar_here :
        (substhvl_TmVar k8 X0 (HS TmVar k8) k8)
    | substhvl_TmVar_there_TmVar
        {d : (Trace TmVar)} {k9 : Hvl}
        {k10 : Hvl} :
        (substhvl_TmVar k8 d k9 k10) -> (substhvl_TmVar k8 (XS TmVar d) (HS TmVar k9) (HS TmVar k10))
    | substhvl_TmVar_there_TxVar
        {d : (Trace TmVar)} {k9 : Hvl}
        {k10 : Hvl} :
        (substhvl_TmVar k8 d k9 k10) -> (substhvl_TmVar k8 (XS TxVar d) (HS TxVar k9) (HS TxVar k10))
    | substhvl_TmVar_there_TyVar
        {d : (Trace TmVar)} {k9 : Hvl}
        {k10 : Hvl} :
        (substhvl_TmVar k8 d k9 k10) -> (substhvl_TmVar k8 (XS TyVar d) (HS TyVar k9) (HS TyVar k10)).
  Inductive substhvl_TxVar (k8 : Hvl) : (forall (d : (Trace TxVar)) (k9 : Hvl) (k10 : Hvl) ,
    Prop) :=
    | substhvl_TxVar_here :
        (substhvl_TxVar k8 X0 (HS TxVar k8) k8)
    | substhvl_TxVar_there_TmVar
        {d : (Trace TxVar)} {k9 : Hvl}
        {k10 : Hvl} :
        (substhvl_TxVar k8 d k9 k10) -> (substhvl_TxVar k8 (XS TmVar d) (HS TmVar k9) (HS TmVar k10))
    | substhvl_TxVar_there_TxVar
        {d : (Trace TxVar)} {k9 : Hvl}
        {k10 : Hvl} :
        (substhvl_TxVar k8 d k9 k10) -> (substhvl_TxVar k8 (XS TxVar d) (HS TxVar k9) (HS TxVar k10))
    | substhvl_TxVar_there_TyVar
        {d : (Trace TxVar)} {k9 : Hvl}
        {k10 : Hvl} :
        (substhvl_TxVar k8 d k9 k10) -> (substhvl_TxVar k8 (XS TyVar d) (HS TyVar k9) (HS TyVar k10)).
  Inductive substhvl_TyVar (k8 : Hvl) : (forall (d : (Trace TyVar)) (k9 : Hvl) (k10 : Hvl) ,
    Prop) :=
    | substhvl_TyVar_here :
        (substhvl_TyVar k8 X0 (HS TyVar k8) k8)
    | substhvl_TyVar_there_TmVar
        {d : (Trace TyVar)} {k9 : Hvl}
        {k10 : Hvl} :
        (substhvl_TyVar k8 d k9 k10) -> (substhvl_TyVar k8 (XS TmVar d) (HS TmVar k9) (HS TmVar k10))
    | substhvl_TyVar_there_TxVar
        {d : (Trace TyVar)} {k9 : Hvl}
        {k10 : Hvl} :
        (substhvl_TyVar k8 d k9 k10) -> (substhvl_TyVar k8 (XS TxVar d) (HS TxVar k9) (HS TxVar k10))
    | substhvl_TyVar_there_TyVar
        {d : (Trace TyVar)} {k9 : Hvl}
        {k10 : Hvl} :
        (substhvl_TyVar k8 d k9 k10) -> (substhvl_TyVar k8 (XS TyVar d) (HS TyVar k9) (HS TyVar k10)).
  Lemma weaken_substhvl_TmVar  :
    (forall {k9 : Hvl} (k8 : Hvl) {d : (Trace TmVar)} {k10 : Hvl} {k11 : Hvl} ,
      (substhvl_TmVar k9 d k10 k11) -> (substhvl_TmVar k9 (weakenTrace d k8) (appendHvl k10 k8) (appendHvl k11 k8))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_TxVar  :
    (forall {k9 : Hvl} (k8 : Hvl) {d : (Trace TxVar)} {k10 : Hvl} {k11 : Hvl} ,
      (substhvl_TxVar k9 d k10 k11) -> (substhvl_TxVar k9 (weakenTrace d k8) (appendHvl k10 k8) (appendHvl k11 k8))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_TyVar  :
    (forall {k9 : Hvl} (k8 : Hvl) {d : (Trace TyVar)} {k10 : Hvl} {k11 : Hvl} ,
      (substhvl_TyVar k9 d k10 k11) -> (substhvl_TyVar k9 (weakenTrace d k8) (appendHvl k10 k8) (appendHvl k11 k8))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_TmVar_wfindex_TmVar {k8 : Hvl} {s5 : Tm} (wft : (wfTm k8 s5)) :
    (forall {d : (Trace TmVar)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_TmVar k8 d k9 k10) -> (forall {x3 : (Index TmVar)} ,
        (wfindex k9 x3) -> (wfTm k10 (subst_TmVar_Index d s5 x3)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TxVar_wfindex_TxVar {k8 : Hvl} {s5 : Tm} (wft : (wfTm k8 s5)) :
    (forall {d : (Trace TxVar)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_TxVar k8 d k9 k10) -> (forall {a1 : (Index TxVar)} ,
        (wfindex k9 a1) -> (wfTm k10 (subst_TxVar_Index d s5 a1)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TyVar_wfindex_TyVar {k8 : Hvl} {S3 : Ty} (wft : (wfTy k8 S3)) :
    (forall {d : (Trace TyVar)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_TyVar k8 d k9 k10) -> (forall {X7 : (Index TyVar)} ,
        (wfindex k9 X7) -> (wfTy k10 (subst_TyVar_Index d S3 X7)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TmVar_wfindex_TxVar {k8 : Hvl} :
    (forall {d : (Trace TmVar)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_TmVar k8 d k9 k10) -> (forall {a1 : (Index TxVar)} ,
        (wfindex k9 a1) -> (wfindex k10 a1))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_TmVar_wfindex_TyVar {k8 : Hvl} :
    (forall {d : (Trace TmVar)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_TmVar k8 d k9 k10) -> (forall {X7 : (Index TyVar)} ,
        (wfindex k9 X7) -> (wfindex k10 X7))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_TxVar_wfindex_TmVar {k8 : Hvl} :
    (forall {d : (Trace TxVar)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_TxVar k8 d k9 k10) -> (forall {x3 : (Index TmVar)} ,
        (wfindex k9 x3) -> (wfindex k10 x3))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_TxVar_wfindex_TyVar {k8 : Hvl} :
    (forall {d : (Trace TxVar)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_TxVar k8 d k9 k10) -> (forall {X7 : (Index TyVar)} ,
        (wfindex k9 X7) -> (wfindex k10 X7))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_TyVar_wfindex_TmVar {k8 : Hvl} :
    (forall {d : (Trace TyVar)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_TyVar k8 d k9 k10) -> (forall {x3 : (Index TmVar)} ,
        (wfindex k9 x3) -> (wfindex k10 x3))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_TyVar_wfindex_TxVar {k8 : Hvl} :
    (forall {d : (Trace TyVar)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_TyVar k8 d k9 k10) -> (forall {a1 : (Index TxVar)} ,
        (wfindex k9 a1) -> (wfindex k10 a1))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_TmVar_wfTy {k8 : Hvl} : (forall (k9 : Hvl) ,
    (forall (S3 : Ty) (wf0 : (wfTy k9 S3)) ,
      (forall {d : (Trace TmVar)} {k10 : Hvl} ,
        (substhvl_TmVar k8 d k9 k10) -> (wfTy k10 S3)))) := (ind_wfTy (fun (k9 : Hvl) (S3 : Ty) (wf0 : (wfTy k9 S3)) =>
    (forall {d : (Trace TmVar)} {k10 : Hvl} ,
      (substhvl_TmVar k8 d k9 k10) -> (wfTy k10 S3))) (fun (k9 : Hvl) {X7 : (Index TyVar)} (wfi : (wfindex k9 X7)) {d : (Trace TmVar)} {k10 : Hvl} (del : (substhvl_TmVar k8 d k9 k10)) =>
    (wfTy_TVar k10 _ (substhvl_TmVar_wfindex_TyVar del wfi))) (fun (k9 : Hvl) (T1 : Ty) (wf0 : (wfTy k9 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k9 T2)) IHT2 {d : (Trace TmVar)} {k10 : Hvl} (del : (substhvl_TmVar k8 d k9 k10)) =>
    (wfTy_TArr k10 (IHT1 (weakenTrace d H0) k10 (weaken_substhvl_TmVar H0 del)) (IHT2 (weakenTrace d H0) k10 (weaken_substhvl_TmVar H0 del)))) (fun (k9 : Hvl) (T : Ty) (wf0 : (wfTy (HS TyVar k9) T)) IHT {d : (Trace TmVar)} {k10 : Hvl} (del : (substhvl_TmVar k8 d k9 k10)) =>
    (wfTy_TAll k10 (IHT (weakenTrace d (HS TyVar H0)) (HS TyVar k10) (weaken_substhvl_TmVar (HS TyVar H0) del))))).
  Definition substhvl_TxVar_wfTy {k8 : Hvl} : (forall (k9 : Hvl) ,
    (forall (S3 : Ty) (wf0 : (wfTy k9 S3)) ,
      (forall {d : (Trace TxVar)} {k10 : Hvl} ,
        (substhvl_TxVar k8 d k9 k10) -> (wfTy k10 S3)))) := (ind_wfTy (fun (k9 : Hvl) (S3 : Ty) (wf0 : (wfTy k9 S3)) =>
    (forall {d : (Trace TxVar)} {k10 : Hvl} ,
      (substhvl_TxVar k8 d k9 k10) -> (wfTy k10 S3))) (fun (k9 : Hvl) {X7 : (Index TyVar)} (wfi : (wfindex k9 X7)) {d : (Trace TxVar)} {k10 : Hvl} (del : (substhvl_TxVar k8 d k9 k10)) =>
    (wfTy_TVar k10 _ (substhvl_TxVar_wfindex_TyVar del wfi))) (fun (k9 : Hvl) (T1 : Ty) (wf0 : (wfTy k9 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k9 T2)) IHT2 {d : (Trace TxVar)} {k10 : Hvl} (del : (substhvl_TxVar k8 d k9 k10)) =>
    (wfTy_TArr k10 (IHT1 (weakenTrace d H0) k10 (weaken_substhvl_TxVar H0 del)) (IHT2 (weakenTrace d H0) k10 (weaken_substhvl_TxVar H0 del)))) (fun (k9 : Hvl) (T : Ty) (wf0 : (wfTy (HS TyVar k9) T)) IHT {d : (Trace TxVar)} {k10 : Hvl} (del : (substhvl_TxVar k8 d k9 k10)) =>
    (wfTy_TAll k10 (IHT (weakenTrace d (HS TyVar H0)) (HS TyVar k10) (weaken_substhvl_TxVar (HS TyVar H0) del))))).
  Definition substhvl_TyVar_wfTy {k8 : Hvl} {S3 : Ty} (wf : (wfTy k8 S3)) : (forall (k9 : Hvl) ,
    (forall (S4 : Ty) (wf0 : (wfTy k9 S4)) ,
      (forall {d : (Trace TyVar)} {k10 : Hvl} ,
        (substhvl_TyVar k8 d k9 k10) -> (wfTy k10 (subst_TyVar_Ty d S3 S4))))) := (ind_wfTy (fun (k9 : Hvl) (S4 : Ty) (wf0 : (wfTy k9 S4)) =>
    (forall {d : (Trace TyVar)} {k10 : Hvl} ,
      (substhvl_TyVar k8 d k9 k10) -> (wfTy k10 (subst_TyVar_Ty d S3 S4)))) (fun (k9 : Hvl) {X7 : (Index TyVar)} (wfi : (wfindex k9 X7)) {d : (Trace TyVar)} {k10 : Hvl} (del : (substhvl_TyVar k8 d k9 k10)) =>
    (substhvl_TyVar_wfindex_TyVar wf del wfi)) (fun (k9 : Hvl) (T1 : Ty) (wf0 : (wfTy k9 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k9 T2)) IHT2 {d : (Trace TyVar)} {k10 : Hvl} (del : (substhvl_TyVar k8 d k9 k10)) =>
    (wfTy_TArr k10 (IHT1 (weakenTrace d H0) k10 (weaken_substhvl_TyVar H0 del)) (IHT2 (weakenTrace d H0) k10 (weaken_substhvl_TyVar H0 del)))) (fun (k9 : Hvl) (T : Ty) (wf0 : (wfTy (HS TyVar k9) T)) IHT {d : (Trace TyVar)} {k10 : Hvl} (del : (substhvl_TyVar k8 d k9 k10)) =>
    (wfTy_TAll k10 (IHT (weakenTrace d (HS TyVar H0)) (HS TyVar k10) (weaken_substhvl_TyVar (HS TyVar H0) del))))).
  Definition substhvl_TmVar_wfTm {k8 : Hvl} {s5 : Tm} (wf : (wfTm k8 s5)) : (forall (k9 : Hvl) ,
    (forall (s6 : Tm) (wf0 : (wfTm k9 s6)) ,
      (forall {d : (Trace TmVar)} {k10 : Hvl} ,
        (substhvl_TmVar k8 d k9 k10) -> (wfTm k10 (subst_TmVar_Tm d s5 s6))))) := (ind_wfTm (fun (k9 : Hvl) (s6 : Tm) (wf0 : (wfTm k9 s6)) =>
    (forall {d : (Trace TmVar)} {k10 : Hvl} ,
      (substhvl_TmVar k8 d k9 k10) -> (wfTm k10 (subst_TmVar_Tm d s5 s6)))) (fun (k9 : Hvl) {x3 : (Index TmVar)} (wfi : (wfindex k9 x3)) {d : (Trace TmVar)} {k10 : Hvl} (del : (substhvl_TmVar k8 d k9 k10)) =>
    (substhvl_TmVar_wfindex_TmVar wf del wfi)) (fun (k9 : Hvl) {a1 : (Index TxVar)} (wfi : (wfindex k9 a1)) {d : (Trace TmVar)} {k10 : Hvl} (del : (substhvl_TmVar k8 d k9 k10)) =>
    (wfTm_XVar k10 _ (substhvl_TmVar_wfindex_TxVar del wfi))) (fun (k9 : Hvl) (T : Ty) (wf0 : (wfTy k9 T)) (t : Tm) (wf1 : (wfTm (HS TmVar k9) t)) IHt {d : (Trace TmVar)} {k10 : Hvl} (del : (substhvl_TmVar k8 d k9 k10)) =>
    (wfTm_Abs k10 (substhvl_TmVar_wfTy k9 T wf0 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d (HS TmVar H0)) (HS TmVar k10) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k9 : Hvl) (t1 : Tm) (wf0 : (wfTm k9 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k9 t2)) IHt2 {d : (Trace TmVar)} {k10 : Hvl} (del : (substhvl_TmVar k8 d k9 k10)) =>
    (wfTm_App k10 (IHt1 (weakenTrace d H0) k10 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d H0) k10 (weaken_substhvl_TmVar H0 del)))) (fun (k9 : Hvl) (t : Tm) (wf0 : (wfTm (HS TyVar k9) t)) IHt {d : (Trace TmVar)} {k10 : Hvl} (del : (substhvl_TmVar k8 d k9 k10)) =>
    (wfTm_TAbs k10 (IHt (weakenTrace d (HS TyVar H0)) (HS TyVar k10) (weaken_substhvl_TmVar (HS TyVar H0) del)))) (fun (k9 : Hvl) (t : Tm) (wf0 : (wfTm k9 t)) IHt (T : Ty) (wf1 : (wfTy k9 T)) {d : (Trace TmVar)} {k10 : Hvl} (del : (substhvl_TmVar k8 d k9 k10)) =>
    (wfTm_TApp k10 (IHt (weakenTrace d H0) k10 (weaken_substhvl_TmVar H0 del)) (substhvl_TmVar_wfTy k9 T wf1 (weaken_substhvl_TmVar H0 del))))).
  Definition substhvl_TxVar_wfTm {k8 : Hvl} {s5 : Tm} (wf : (wfTm k8 s5)) : (forall (k9 : Hvl) ,
    (forall (s6 : Tm) (wf0 : (wfTm k9 s6)) ,
      (forall {d : (Trace TxVar)} {k10 : Hvl} ,
        (substhvl_TxVar k8 d k9 k10) -> (wfTm k10 (subst_TxVar_Tm d s5 s6))))) := (ind_wfTm (fun (k9 : Hvl) (s6 : Tm) (wf0 : (wfTm k9 s6)) =>
    (forall {d : (Trace TxVar)} {k10 : Hvl} ,
      (substhvl_TxVar k8 d k9 k10) -> (wfTm k10 (subst_TxVar_Tm d s5 s6)))) (fun (k9 : Hvl) {x3 : (Index TmVar)} (wfi : (wfindex k9 x3)) {d : (Trace TxVar)} {k10 : Hvl} (del : (substhvl_TxVar k8 d k9 k10)) =>
    (wfTm_Var k10 _ (substhvl_TxVar_wfindex_TmVar del wfi))) (fun (k9 : Hvl) {a1 : (Index TxVar)} (wfi : (wfindex k9 a1)) {d : (Trace TxVar)} {k10 : Hvl} (del : (substhvl_TxVar k8 d k9 k10)) =>
    (substhvl_TxVar_wfindex_TxVar wf del wfi)) (fun (k9 : Hvl) (T : Ty) (wf0 : (wfTy k9 T)) (t : Tm) (wf1 : (wfTm (HS TmVar k9) t)) IHt {d : (Trace TxVar)} {k10 : Hvl} (del : (substhvl_TxVar k8 d k9 k10)) =>
    (wfTm_Abs k10 (substhvl_TxVar_wfTy k9 T wf0 (weaken_substhvl_TxVar H0 del)) (IHt (weakenTrace d (HS TmVar H0)) (HS TmVar k10) (weaken_substhvl_TxVar (HS TmVar H0) del)))) (fun (k9 : Hvl) (t1 : Tm) (wf0 : (wfTm k9 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k9 t2)) IHt2 {d : (Trace TxVar)} {k10 : Hvl} (del : (substhvl_TxVar k8 d k9 k10)) =>
    (wfTm_App k10 (IHt1 (weakenTrace d H0) k10 (weaken_substhvl_TxVar H0 del)) (IHt2 (weakenTrace d H0) k10 (weaken_substhvl_TxVar H0 del)))) (fun (k9 : Hvl) (t : Tm) (wf0 : (wfTm (HS TyVar k9) t)) IHt {d : (Trace TxVar)} {k10 : Hvl} (del : (substhvl_TxVar k8 d k9 k10)) =>
    (wfTm_TAbs k10 (IHt (weakenTrace d (HS TyVar H0)) (HS TyVar k10) (weaken_substhvl_TxVar (HS TyVar H0) del)))) (fun (k9 : Hvl) (t : Tm) (wf0 : (wfTm k9 t)) IHt (T : Ty) (wf1 : (wfTy k9 T)) {d : (Trace TxVar)} {k10 : Hvl} (del : (substhvl_TxVar k8 d k9 k10)) =>
    (wfTm_TApp k10 (IHt (weakenTrace d H0) k10 (weaken_substhvl_TxVar H0 del)) (substhvl_TxVar_wfTy k9 T wf1 (weaken_substhvl_TxVar H0 del))))).
  Definition substhvl_TyVar_wfTm {k8 : Hvl} {S3 : Ty} (wf : (wfTy k8 S3)) : (forall (k9 : Hvl) ,
    (forall (s5 : Tm) (wf0 : (wfTm k9 s5)) ,
      (forall {d : (Trace TyVar)} {k10 : Hvl} ,
        (substhvl_TyVar k8 d k9 k10) -> (wfTm k10 (subst_TyVar_Tm d S3 s5))))) := (ind_wfTm (fun (k9 : Hvl) (s5 : Tm) (wf0 : (wfTm k9 s5)) =>
    (forall {d : (Trace TyVar)} {k10 : Hvl} ,
      (substhvl_TyVar k8 d k9 k10) -> (wfTm k10 (subst_TyVar_Tm d S3 s5)))) (fun (k9 : Hvl) {x3 : (Index TmVar)} (wfi : (wfindex k9 x3)) {d : (Trace TyVar)} {k10 : Hvl} (del : (substhvl_TyVar k8 d k9 k10)) =>
    (wfTm_Var k10 _ (substhvl_TyVar_wfindex_TmVar del wfi))) (fun (k9 : Hvl) {a1 : (Index TxVar)} (wfi : (wfindex k9 a1)) {d : (Trace TyVar)} {k10 : Hvl} (del : (substhvl_TyVar k8 d k9 k10)) =>
    (wfTm_XVar k10 _ (substhvl_TyVar_wfindex_TxVar del wfi))) (fun (k9 : Hvl) (T : Ty) (wf0 : (wfTy k9 T)) (t : Tm) (wf1 : (wfTm (HS TmVar k9) t)) IHt {d : (Trace TyVar)} {k10 : Hvl} (del : (substhvl_TyVar k8 d k9 k10)) =>
    (wfTm_Abs k10 (substhvl_TyVar_wfTy wf k9 T wf0 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d (HS TmVar H0)) (HS TmVar k10) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k9 : Hvl) (t1 : Tm) (wf0 : (wfTm k9 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k9 t2)) IHt2 {d : (Trace TyVar)} {k10 : Hvl} (del : (substhvl_TyVar k8 d k9 k10)) =>
    (wfTm_App k10 (IHt1 (weakenTrace d H0) k10 (weaken_substhvl_TyVar H0 del)) (IHt2 (weakenTrace d H0) k10 (weaken_substhvl_TyVar H0 del)))) (fun (k9 : Hvl) (t : Tm) (wf0 : (wfTm (HS TyVar k9) t)) IHt {d : (Trace TyVar)} {k10 : Hvl} (del : (substhvl_TyVar k8 d k9 k10)) =>
    (wfTm_TAbs k10 (IHt (weakenTrace d (HS TyVar H0)) (HS TyVar k10) (weaken_substhvl_TyVar (HS TyVar H0) del)))) (fun (k9 : Hvl) (t : Tm) (wf0 : (wfTm k9 t)) IHt (T : Ty) (wf1 : (wfTy k9 T)) {d : (Trace TyVar)} {k10 : Hvl} (del : (substhvl_TyVar k8 d k9 k10)) =>
    (wfTm_TApp k10 (IHt (weakenTrace d H0) k10 (weaken_substhvl_TyVar H0 del)) (substhvl_TyVar_wfTy wf k9 T wf1 (weaken_substhvl_TyVar H0 del))))).
End SubstWellFormed.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TxVar substhvl_TmVar_wfindex_TyVar substhvl_TxVar_wfindex_TmVar substhvl_TxVar_wfindex_TxVar substhvl_TxVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TxVar substhvl_TyVar_wfindex_TyVar : infra.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TxVar substhvl_TmVar_wfindex_TyVar substhvl_TxVar_wfindex_TmVar substhvl_TxVar_wfindex_TxVar substhvl_TxVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TxVar substhvl_TyVar_wfindex_TyVar : subst.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TxVar substhvl_TmVar_wfindex_TyVar substhvl_TxVar_wfindex_TmVar substhvl_TxVar_wfindex_TxVar substhvl_TxVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TxVar substhvl_TyVar_wfindex_TyVar : subst_wf.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TxVar substhvl_TmVar_wfindex_TyVar substhvl_TxVar_wfindex_TmVar substhvl_TxVar_wfindex_TxVar substhvl_TxVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TxVar substhvl_TyVar_wfindex_TyVar : wf.
 Hint Resolve substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TxVar_wfTm substhvl_TxVar_wfTy substhvl_TyVar_wfTm substhvl_TyVar_wfTy : infra.
 Hint Resolve substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TxVar_wfTm substhvl_TxVar_wfTy substhvl_TyVar_wfTm substhvl_TyVar_wfTy : subst.
 Hint Resolve substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TxVar_wfTm substhvl_TxVar_wfTy substhvl_TyVar_wfTm substhvl_TyVar_wfTy : subst_wf.
 Hint Resolve substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TxVar_wfTm substhvl_TxVar_wfTy substhvl_TyVar_wfTm substhvl_TyVar_wfTy : wf.
 Hint Constructors substhvl_TmVar substhvl_TxVar substhvl_TyVar : infra.
 Hint Constructors substhvl_TmVar substhvl_TxVar substhvl_TyVar : subst.
 Hint Constructors substhvl_TmVar substhvl_TxVar substhvl_TyVar : subst_wf.
 Hint Constructors substhvl_TmVar substhvl_TxVar substhvl_TyVar : wf.
Section Context.
  Inductive Ctx : Type :=
    | empty 
    | evar (G : Ctx) (T : Ty)
    | evarx (G : Ctx) (T : Ty)
    | etvar (G : Ctx).
  Fixpoint appendCtx (G : Ctx) (G0 : Ctx) :
  Ctx :=
    match G0 with
      | (empty) => G
      | (evar G1 T) => (evar (appendCtx G G1) T)
      | (evarx G1 T) => (evarx (appendCtx G G1) T)
      | (etvar G1) => (etvar (appendCtx G G1))
    end.
  Fixpoint domainCtx (G : Ctx) :
  Hvl :=
    match G with
      | (empty) => H0
      | (evar G0 T) => (HS TmVar (domainCtx G0))
      | (evarx G0 T) => (HS TxVar (domainCtx G0))
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
  Fixpoint shift_TmVar_Ctx (c : (Cutoff TmVar)) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shift_TmVar_Ctx c G0) T)
      | (evarx G0 T) => (evarx (shift_TmVar_Ctx c G0) T)
      | (etvar G0) => (etvar (shift_TmVar_Ctx c G0))
    end.
  Fixpoint shift_TxVar_Ctx (c : (Cutoff TxVar)) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shift_TxVar_Ctx c G0) T)
      | (evarx G0 T) => (evarx (shift_TxVar_Ctx c G0) T)
      | (etvar G0) => (etvar (shift_TxVar_Ctx c G0))
    end.
  Fixpoint shift_TyVar_Ctx (c : (Cutoff TyVar)) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shift_TyVar_Ctx c G0) (shift_TyVar_Ty (weakenCutoffTyVar c (domainCtx G0)) T))
      | (evarx G0 T) => (evarx (shift_TyVar_Ctx c G0) (shift_TyVar_Ty (weakenCutoffTyVar c (domainCtx G0)) T))
      | (etvar G0) => (etvar (shift_TyVar_Ctx c G0))
    end.
  Fixpoint weakenCtx (G : Ctx) (k8 : Hvl) {struct k8} :
  Ctx :=
    match k8 with
      | (H0) => G
      | (HS TmVar k8) => (weakenCtx G k8)
      | (HS TxVar k8) => (weakenCtx G k8)
      | (HS TyVar k8) => (shift_TyVar_Ctx C0 (weakenCtx G k8))
    end.
  Fixpoint subst_TmVar_Ctx (d : (Trace TmVar)) (s5 : Tm) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (subst_TmVar_Ctx d s5 G0) T)
      | (evarx G0 T) => (evarx (subst_TmVar_Ctx d s5 G0) T)
      | (etvar G0) => (etvar (subst_TmVar_Ctx d s5 G0))
    end.
  Fixpoint subst_TxVar_Ctx (d : (Trace TxVar)) (s5 : Tm) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (subst_TxVar_Ctx d s5 G0) T)
      | (evarx G0 T) => (evarx (subst_TxVar_Ctx d s5 G0) T)
      | (etvar G0) => (etvar (subst_TxVar_Ctx d s5 G0))
    end.
  Fixpoint subst_TyVar_Ctx (d : (Trace TyVar)) (S3 : Ty) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (subst_TyVar_Ctx d S3 G0) (subst_TyVar_Ty (weakenTrace d (domainCtx G0)) S3 T))
      | (evarx G0 T) => (evarx (subst_TyVar_Ctx d S3 G0) (subst_TyVar_Ty (weakenTrace d (domainCtx G0)) S3 T))
      | (etvar G0) => (etvar (subst_TyVar_Ctx d S3 G0))
    end.
  Lemma domainCtx_shift_TmVar_Ctx  :
    (forall (c : (Cutoff TmVar)) (G : Ctx) ,
      ((domainCtx (shift_TmVar_Ctx c G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainCtx_shift_TxVar_Ctx  :
    (forall (c : (Cutoff TxVar)) (G : Ctx) ,
      ((domainCtx (shift_TxVar_Ctx c G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainCtx_shift_TyVar_Ctx  :
    (forall (c : (Cutoff TyVar)) (G : Ctx) ,
      ((domainCtx (shift_TyVar_Ctx c G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainCtx_subst_TmVar_Ctx  :
    (forall (d : (Trace TmVar)) (s5 : Tm) (G : Ctx) ,
      ((domainCtx (subst_TmVar_Ctx d s5 G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainCtx_subst_TxVar_Ctx  :
    (forall (d : (Trace TxVar)) (s5 : Tm) (G : Ctx) ,
      ((domainCtx (subst_TxVar_Ctx d s5 G)) = (domainCtx G))).
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
    Lemma shift_TmVar_Ctx_appendCtx  :
      (forall (c : (Cutoff TmVar)) (G : Ctx) (G0 : Ctx) ,
        ((shift_TmVar_Ctx c (appendCtx G G0)) = (appendCtx (shift_TmVar_Ctx c G) (shift_TmVar_Ctx (weakenCutoffTmVar c (domainCtx G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma shift_TxVar_Ctx_appendCtx  :
      (forall (c : (Cutoff TxVar)) (G : Ctx) (G0 : Ctx) ,
        ((shift_TxVar_Ctx c (appendCtx G G0)) = (appendCtx (shift_TxVar_Ctx c G) (shift_TxVar_Ctx (weakenCutoffTxVar c (domainCtx G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma shift_TyVar_Ctx_appendCtx  :
      (forall (c : (Cutoff TyVar)) (G : Ctx) (G0 : Ctx) ,
        ((shift_TyVar_Ctx c (appendCtx G G0)) = (appendCtx (shift_TyVar_Ctx c G) (shift_TyVar_Ctx (weakenCutoffTyVar c (domainCtx G)) G0)))).
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
    Lemma subst_TxVar_Ctx_appendCtx  :
      (forall (d : (Trace TxVar)) (s5 : Tm) (G : Ctx) (G0 : Ctx) ,
        ((subst_TxVar_Ctx d s5 (appendCtx G G0)) = (appendCtx (subst_TxVar_Ctx d s5 G) (subst_TxVar_Ctx (weakenTrace d (domainCtx G)) s5 G0)))).
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
    (forall (S3 : Ty) (k8 : Hvl) (k9 : Hvl) ,
      ((weakenTy (weakenTy S3 k8) k9) = (weakenTy S3 (appendHvl k8 k9)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s5 : Tm) (k8 : Hvl) (k9 : Hvl) ,
      ((weakenTm (weakenTm s5 k8) k9) = (weakenTm s5 (appendHvl k8 k9)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Ctx -> (Index TmVar) -> Ty -> Prop :=
      | lookup_evar_here {G : Ctx}
          (T6 : Ty) :
          (wfTy (domainCtx G) T6) -> (lookup_evar (evar G T6) I0 T6)
      | lookup_evar_there_evar
          {G : Ctx} {x3 : (Index TmVar)}
          (T7 : Ty) (T8 : Ty) :
          (lookup_evar G x3 T7) -> (lookup_evar (evar G T8) (IS x3) T7)
      | lookup_evar_there_evarx
          {G : Ctx} {x3 : (Index TmVar)}
          (T7 : Ty) (T8 : Ty) :
          (lookup_evar G x3 T7) -> (lookup_evar (evarx G T8) x3 T7)
      | lookup_evar_there_etvar
          {G : Ctx} {x3 : (Index TmVar)}
          (T7 : Ty) :
          (lookup_evar G x3 T7) -> (lookup_evar (etvar G) x3 (shift_TyVar_Ty C0 T7)).
    Inductive lookup_evarx : Ctx -> (Index TxVar) -> Ty -> Prop :=
      | lookup_evarx_here {G : Ctx}
          (T7 : Ty) :
          (wfTy (domainCtx G) T7) -> (lookup_evarx (evarx G T7) I0 T7)
      | lookup_evarx_there_evar
          {G : Ctx} {a1 : (Index TxVar)}
          (T8 : Ty) (T9 : Ty) :
          (lookup_evarx G a1 T8) -> (lookup_evarx (evar G T9) a1 T8)
      | lookup_evarx_there_evarx
          {G : Ctx} {a1 : (Index TxVar)}
          (T8 : Ty) (T9 : Ty) :
          (lookup_evarx G a1 T8) -> (lookup_evarx (evarx G T9) (IS a1) T8)
      | lookup_evarx_there_etvar
          {G : Ctx} {a1 : (Index TxVar)}
          (T8 : Ty) :
          (lookup_evarx G a1 T8) -> (lookup_evarx (etvar G) a1 (shift_TyVar_Ty C0 T8)).
    Inductive lookup_etvar : Ctx -> (Index TyVar) -> Prop :=
      | lookup_etvar_here {G : Ctx}
          : (lookup_etvar (etvar G) I0)
      | lookup_etvar_there_evar
          {G : Ctx} {X7 : (Index TyVar)}
          (T8 : Ty) :
          (lookup_etvar G X7) -> (lookup_etvar (evar G T8) X7)
      | lookup_etvar_there_evarx
          {G : Ctx} {X7 : (Index TyVar)}
          (T8 : Ty) :
          (lookup_etvar G X7) -> (lookup_etvar (evarx G T8) X7)
      | lookup_etvar_there_etvar
          {G : Ctx} {X7 : (Index TyVar)} :
          (lookup_etvar G X7) -> (lookup_etvar (etvar G) (IS X7)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Ctx) (T8 : Ty) (T9 : Ty) ,
        (lookup_evar (evar G T8) I0 T9) -> (T8 = T9)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evarx_inversion_here  :
      (forall (G : Ctx) (T8 : Ty) (T9 : Ty) ,
        (lookup_evarx (evarx G T8) I0 T9) -> (T8 = T9)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Ctx} {x3 : (Index TmVar)} ,
        (forall (T8 : Ty) ,
          (lookup_evar G x3 T8) -> (forall (T9 : Ty) ,
            (lookup_evar G x3 T9) -> (T8 = T9)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evarx_functional  :
      (forall {G : Ctx} {a1 : (Index TxVar)} ,
        (forall (T8 : Ty) ,
          (lookup_evarx G a1 T8) -> (forall (T9 : Ty) ,
            (lookup_evarx G a1 T9) -> (T8 = T9)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Ctx} {x3 : (Index TmVar)} (T8 : Ty) ,
        (lookup_evar G x3 T8) -> (wfTy (domainCtx G) T8)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_evarx_wf  :
      (forall {G : Ctx} {a1 : (Index TxVar)} (T8 : Ty) ,
        (lookup_evarx G a1 T8) -> (wfTy (domainCtx G) T8)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Ctx} (G0 : Ctx) {x3 : (Index TmVar)} (T8 : Ty) ,
        (lookup_evar G x3 T8) -> (lookup_evar (appendCtx G G0) (weakenIndexTmVar x3 (domainCtx G0)) (weakenTy T8 (domainCtx G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_evarx  :
      (forall {G : Ctx} (G0 : Ctx) {a1 : (Index TxVar)} (T8 : Ty) ,
        (lookup_evarx G a1 T8) -> (lookup_evarx (appendCtx G G0) (weakenIndexTxVar a1 (domainCtx G0)) (weakenTy T8 (domainCtx G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Ctx} (G0 : Ctx) {X7 : (Index TyVar)} ,
        (lookup_etvar G X7) -> (lookup_etvar (appendCtx G G0) (weakenIndexTyVar X7 (domainCtx G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Ctx} {x3 : (Index TmVar)} (T12 : Ty) ,
        (lookup_evar G x3 T12) -> (wfindex (domainCtx G) x3)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_evarx_wfindex  :
      (forall {G : Ctx} {a1 : (Index TxVar)} (T12 : Ty) ,
        (lookup_evarx G a1 T12) -> (wfindex (domainCtx G) a1)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Ctx} {X7 : (Index TyVar)} ,
        (lookup_etvar G X7) -> (wfindex (domainCtx G) X7)).
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
        (shift_evar c G G0) -> (shift_evar (CS c) (evar G T) (evar G0 T))
    | shiftevar_there_evarx
        {c : (Cutoff TmVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_evar c G G0) -> (shift_evar c (evarx G T) (evarx G0 T))
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
  Inductive shift_evarx : (Cutoff TxVar) -> Ctx -> Ctx -> Prop :=
    | shift_evarx_here {G : Ctx}
        {T8 : Ty} :
        (shift_evarx C0 G (evarx G T8))
    | shiftevarx_there_evar
        {c : (Cutoff TxVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_evarx c G G0) -> (shift_evarx c (evar G T) (evar G0 T))
    | shiftevarx_there_evarx
        {c : (Cutoff TxVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_evarx c G G0) -> (shift_evarx (CS c) (evarx G T) (evarx G0 T))
    | shiftevarx_there_etvar
        {c : (Cutoff TxVar)} {G : Ctx}
        {G0 : Ctx} :
        (shift_evarx c G G0) -> (shift_evarx c (etvar G) (etvar G0)).
  Lemma weaken_shift_evarx  :
    (forall (G : Ctx) {c : (Cutoff TxVar)} {G0 : Ctx} {G1 : Ctx} ,
      (shift_evarx c G0 G1) -> (shift_evarx (weakenCutoffTxVar c (domainCtx G)) (appendCtx G0 G) (appendCtx G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff TyVar) -> Ctx -> Ctx -> Prop :=
    | shift_etvar_here {G : Ctx} :
        (shift_etvar C0 G (etvar G))
    | shiftetvar_there_evar
        {c : (Cutoff TyVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_etvar c G G0) -> (shift_etvar c (evar G T) (evar G0 (shift_TyVar_Ty c T)))
    | shiftetvar_there_evarx
        {c : (Cutoff TyVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_etvar c G G0) -> (shift_etvar c (evarx G T) (evarx G0 (shift_TyVar_Ty c T)))
    | shiftetvar_there_etvar
        {c : (Cutoff TyVar)} {G : Ctx}
        {G0 : Ctx} :
        (shift_etvar c G G0) -> (shift_etvar (CS c) (etvar G) (etvar G0)).
  Lemma weaken_shift_etvar  :
    (forall (G : Ctx) {c : (Cutoff TyVar)} {G0 : Ctx} {G1 : Ctx} ,
      (shift_etvar c G0 G1) -> (shift_etvar (weakenCutoffTyVar c (domainCtx G)) (appendCtx G0 G) (appendCtx G1 (shift_TyVar_Ctx c G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_TmVar  :
    (forall {c : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} ,
      (shift_evar c G G0) -> (shifthvl_TmVar c (domainCtx G) (domainCtx G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_evarx_shifthvl_TxVar  :
    (forall {c : (Cutoff TxVar)} {G : Ctx} {G0 : Ctx} ,
      (shift_evarx c G G0) -> (shifthvl_TxVar c (domainCtx G) (domainCtx G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_etvar_shifthvl_TyVar  :
    (forall {c : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} ,
      (shift_etvar c G G0) -> (shifthvl_TyVar c (domainCtx G) (domainCtx G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Ctx) (T8 : Ty) (s5 : Tm) : (Trace TmVar) -> Ctx -> Ctx -> Prop :=
    | subst_evar_here :
        (subst_evar G T8 s5 X0 (evar G T8) G)
    | subst_evar_there_evar
        {d : (Trace TmVar)} {G0 : Ctx}
        {G1 : Ctx} (T9 : Ty) :
        (subst_evar G T8 s5 d G0 G1) -> (subst_evar G T8 s5 (XS TmVar d) (evar G0 T9) (evar G1 T9))
    | subst_evar_there_evarx
        {d : (Trace TmVar)} {G0 : Ctx}
        {G1 : Ctx} (T9 : Ty) :
        (subst_evar G T8 s5 d G0 G1) -> (subst_evar G T8 s5 (XS TxVar d) (evarx G0 T9) (evarx G1 T9))
    | subst_evar_there_etvar
        {d : (Trace TmVar)} {G0 : Ctx}
        {G1 : Ctx} :
        (subst_evar G T8 s5 d G0 G1) -> (subst_evar G T8 s5 (XS TyVar d) (etvar G0) (etvar G1)).
  Lemma weaken_subst_evar {G : Ctx} (T8 : Ty) {s5 : Tm} :
    (forall (G0 : Ctx) {d : (Trace TmVar)} {G1 : Ctx} {G2 : Ctx} ,
      (subst_evar G T8 s5 d G1 G2) -> (subst_evar G T8 s5 (weakenTrace d (domainCtx G0)) (appendCtx G1 G0) (appendCtx G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_evarx (G : Ctx) (T8 : Ty) (s5 : Tm) : (Trace TxVar) -> Ctx -> Ctx -> Prop :=
    | subst_evarx_here :
        (subst_evarx G T8 s5 X0 (evarx G T8) G)
    | subst_evarx_there_evar
        {d : (Trace TxVar)} {G0 : Ctx}
        {G1 : Ctx} (T9 : Ty) :
        (subst_evarx G T8 s5 d G0 G1) -> (subst_evarx G T8 s5 (XS TmVar d) (evar G0 T9) (evar G1 T9))
    | subst_evarx_there_evarx
        {d : (Trace TxVar)} {G0 : Ctx}
        {G1 : Ctx} (T9 : Ty) :
        (subst_evarx G T8 s5 d G0 G1) -> (subst_evarx G T8 s5 (XS TxVar d) (evarx G0 T9) (evarx G1 T9))
    | subst_evarx_there_etvar
        {d : (Trace TxVar)} {G0 : Ctx}
        {G1 : Ctx} :
        (subst_evarx G T8 s5 d G0 G1) -> (subst_evarx G T8 s5 (XS TyVar d) (etvar G0) (etvar G1)).
  Lemma weaken_subst_evarx {G : Ctx} (T8 : Ty) {s5 : Tm} :
    (forall (G0 : Ctx) {d : (Trace TxVar)} {G1 : Ctx} {G2 : Ctx} ,
      (subst_evarx G T8 s5 d G1 G2) -> (subst_evarx G T8 s5 (weakenTrace d (domainCtx G0)) (appendCtx G1 G0) (appendCtx G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Ctx) (S3 : Ty) : (Trace TyVar) -> Ctx -> Ctx -> Prop :=
    | subst_etvar_here :
        (subst_etvar G S3 X0 (etvar G) G)
    | subst_etvar_there_evar
        {d : (Trace TyVar)} {G0 : Ctx}
        {G1 : Ctx} (T8 : Ty) :
        (subst_etvar G S3 d G0 G1) -> (subst_etvar G S3 (XS TmVar d) (evar G0 T8) (evar G1 (subst_TyVar_Ty d S3 T8)))
    | subst_etvar_there_evarx
        {d : (Trace TyVar)} {G0 : Ctx}
        {G1 : Ctx} (T8 : Ty) :
        (subst_etvar G S3 d G0 G1) -> (subst_etvar G S3 (XS TxVar d) (evarx G0 T8) (evarx G1 (subst_TyVar_Ty d S3 T8)))
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
  Lemma subst_evar_substhvl_TmVar {G : Ctx} {s5 : Tm} (T8 : Ty) :
    (forall {d : (Trace TmVar)} {G0 : Ctx} {G1 : Ctx} ,
      (subst_evar G T8 s5 d G0 G1) -> (substhvl_TmVar (domainCtx G) d (domainCtx G0) (domainCtx G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_evarx_substhvl_TxVar {G : Ctx} {s5 : Tm} (T9 : Ty) :
    (forall {d : (Trace TxVar)} {G0 : Ctx} {G1 : Ctx} ,
      (subst_evarx G T9 s5 d G0 G1) -> (substhvl_TxVar (domainCtx G) d (domainCtx G0) (domainCtx G1))).
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
 Hint Rewrite domainCtx_shift_TyVar_Ctx : interaction.
 Hint Rewrite domainCtx_shift_TyVar_Ctx : env_domain_shift.
 Hint Rewrite domainCtx_subst_TyVar_Ctx : interaction.
 Hint Rewrite domainCtx_subst_TyVar_Ctx : env_domain_subst.
 Hint Rewrite shift_TyVar_Ctx_appendCtx : interaction.
 Hint Rewrite shift_TyVar_Ctx_appendCtx : env_shift_append.
 Hint Rewrite subst_TyVar_Ctx_appendCtx : interaction.
 Hint Rewrite subst_TyVar_Ctx_appendCtx : env_shift_append.
 Hint Constructors lookup_evar lookup_evarx lookup_etvar : infra.
 Hint Constructors lookup_evar lookup_evarx lookup_etvar : lookup.
 Hint Constructors lookup_evar lookup_evarx lookup_etvar : shift.
 Hint Constructors lookup_evar lookup_evarx lookup_etvar : subst.
 Hint Resolve weaken_lookup_evar weaken_lookup_evarx weaken_lookup_etvar : infra.
 Hint Resolve weaken_lookup_evar weaken_lookup_evarx weaken_lookup_etvar : lookup.
 Hint Resolve weaken_lookup_evar weaken_lookup_evarx weaken_lookup_etvar : shift.
 Hint Resolve weaken_lookup_evar weaken_lookup_evarx weaken_lookup_etvar : weaken.
Lemma weaken_lookup_evar_here  :
  (forall {G : Ctx} (G0 : Ctx) {T8 : Ty} (wf : (wfTy (domainCtx G) T8)) ,
    (lookup_evar (appendCtx (evar G T8) G0) (weakenIndexTmVar I0 (domainCtx G0)) (weakenTy T8 (domainCtx G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_evarx_here  :
  (forall {G : Ctx} (G0 : Ctx) {T8 : Ty} (wf : (wfTy (domainCtx G) T8)) ,
    (lookup_evarx (appendCtx (evarx G T8) G0) (weakenIndexTxVar I0 (domainCtx G0)) (weakenTy T8 (domainCtx G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Ctx} (G0 : Ctx) ,
    (lookup_etvar (appendCtx (etvar G) G0) (weakenIndexTyVar I0 (domainCtx G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfTm wfTy : infra.
 Hint Constructors wfTm wfTy : wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H31 : (wfTy _ (TVar _)) |- _ => inversion H31; subst; clear H31
  | H31 : (wfTy _ (TArr _ _)) |- _ => inversion H31; subst; clear H31
  | H31 : (wfTy _ (TAll _)) |- _ => inversion H31; subst; clear H31
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H31 : (wfTm _ (Var _)) |- _ => inversion H31; subst; clear H31
  | H31 : (wfTm _ (XVar _)) |- _ => inversion H31; subst; clear H31
  | H31 : (wfTm _ (Abs _ _)) |- _ => inversion H31; subst; clear H31
  | H31 : (wfTm _ (App _ _)) |- _ => inversion H31; subst; clear H31
  | H31 : (wfTm _ (TAbs _)) |- _ => inversion H31; subst; clear H31
  | H31 : (wfTm _ (TApp _ _)) |- _ => inversion H31; subst; clear H31
end : infra wf.
 Hint Resolve lookup_evar_wf lookup_evarx_wf : infra.
 Hint Resolve lookup_evar_wf lookup_evarx_wf : wf.
 Hint Resolve lookup_evar_wfindex lookup_evarx_wfindex lookup_etvar_wfindex : infra.
 Hint Resolve lookup_evar_wfindex lookup_evarx_wfindex lookup_etvar_wfindex : lookup.
 Hint Resolve lookup_evar_wfindex lookup_evarx_wfindex lookup_etvar_wfindex : wf.
 Hint Constructors shift_evar shift_evarx shift_etvar : infra.
 Hint Constructors shift_evar shift_evarx shift_etvar : shift.
 Hint Constructors shift_evar shift_evarx shift_etvar : subst.
 Hint Resolve weaken_shift_evar weaken_shift_evarx weaken_shift_etvar : infra.
 Hint Resolve weaken_shift_evar weaken_shift_evarx weaken_shift_etvar : shift.
 Hint Resolve shift_evar_shifthvl_TmVar shift_evarx_shifthvl_TxVar shift_etvar_shifthvl_TyVar : infra.
 Hint Resolve shift_evar_shifthvl_TmVar shift_evarx_shifthvl_TxVar shift_etvar_shifthvl_TyVar : shift.
 Hint Resolve shift_evar_shifthvl_TmVar shift_evarx_shifthvl_TxVar shift_etvar_shifthvl_TyVar : shift_wf.
 Hint Resolve shift_evar_shifthvl_TmVar shift_evarx_shifthvl_TxVar shift_etvar_shifthvl_TyVar : wf.
 Hint Constructors subst_evar subst_evarx subst_etvar : infra.
 Hint Constructors subst_evar subst_evarx subst_etvar : subst.
 Hint Resolve weaken_subst_evar weaken_subst_evarx weaken_subst_etvar : infra.
 Hint Resolve weaken_subst_evar weaken_subst_evarx weaken_subst_etvar : subst.
 Hint Resolve subst_evar_substhvl_TmVar subst_evarx_substhvl_TxVar subst_etvar_substhvl_TyVar : infra.
 Hint Resolve subst_evar_substhvl_TmVar subst_evarx_substhvl_TxVar subst_etvar_substhvl_TyVar : subst.
 Hint Resolve subst_evar_substhvl_TmVar subst_evarx_substhvl_TxVar subst_etvar_substhvl_TyVar : subst_wf.
 Hint Resolve subst_evar_substhvl_TmVar subst_evarx_substhvl_TxVar subst_etvar_substhvl_TyVar : wf.
 Hint Resolve subst_evar_substhvl_TmVar subst_evarx_substhvl_TxVar subst_etvar_substhvl_TyVar : substenv_substhvl.
Lemma shift_evar_lookup_evar  :
  (forall {c : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evar c G G0)) {x3 : (Index TmVar)} {T8 : Ty} ,
    (lookup_evar G x3 T8) -> (lookup_evar G0 (shift_TmVar_Index c x3) T8)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_evarx  :
  (forall {c : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evar c G G0)) {a1 : (Index TxVar)} {T8 : Ty} ,
    (lookup_evarx G a1 T8) -> (lookup_evarx G0 a1 T8)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evar c G G0)) {X7 : (Index TyVar)} ,
    (lookup_etvar G X7) -> (lookup_etvar G0 X7)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evarx_lookup_evar  :
  (forall {c : (Cutoff TxVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evarx c G G0)) {x3 : (Index TmVar)} {T8 : Ty} ,
    (lookup_evar G x3 T8) -> (lookup_evar G0 x3 T8)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evarx_lookup_evarx  :
  (forall {c : (Cutoff TxVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evarx c G G0)) {a1 : (Index TxVar)} {T8 : Ty} ,
    (lookup_evarx G a1 T8) -> (lookup_evarx G0 (shift_TxVar_Index c a1) T8)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evarx_lookup_etvar  :
  (forall {c : (Cutoff TxVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evarx c G G0)) {X7 : (Index TyVar)} ,
    (lookup_etvar G X7) -> (lookup_etvar G0 X7)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_etvar c G G0)) {x3 : (Index TmVar)} {T8 : Ty} ,
    (lookup_evar G x3 T8) -> (lookup_evar G0 x3 (shift_TyVar_Ty c T8))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evarx  :
  (forall {c : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_etvar c G G0)) {a1 : (Index TxVar)} {T8 : Ty} ,
    (lookup_evarx G a1 T8) -> (lookup_evarx G0 a1 (shift_TyVar_Ty c T8))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_etvar c G G0)) {X7 : (Index TyVar)} ,
    (lookup_etvar G X7) -> (lookup_etvar G0 (shift_TyVar_Index c X7))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_evarx shift_evar_lookup_etvar shift_evarx_lookup_evar shift_evarx_lookup_evarx shift_evarx_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_evarx shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_evarx shift_evar_lookup_etvar shift_evarx_lookup_evar shift_evarx_lookup_evarx shift_evarx_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_evarx shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_evarx shift_evar_lookup_etvar shift_evarx_lookup_evar shift_evarx_lookup_evarx shift_evarx_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_evarx shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_evarx {G : Ctx} (T10 : Ty) {s5 : Tm} :
  (forall {d : (Trace TmVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_evar G T10 s5 d G0 G1)) {a1 : (Index TxVar)} (T11 : Ty) ,
    (lookup_evarx G0 a1 T11) -> (lookup_evarx G1 a1 T11)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_evar_lookup_etvar {G : Ctx} (T10 : Ty) {s5 : Tm} :
  (forall {d : (Trace TmVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_evar G T10 s5 d G0 G1)) {X7 : (Index TyVar)} ,
    (lookup_etvar G0 X7) -> (lookup_etvar G1 X7)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_evarx_lookup_evar {G : Ctx} (T10 : Ty) {s5 : Tm} :
  (forall {d : (Trace TxVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_evarx G T10 s5 d G0 G1)) {x3 : (Index TmVar)} (T11 : Ty) ,
    (lookup_evar G0 x3 T11) -> (lookup_evar G1 x3 T11)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_evarx_lookup_etvar {G : Ctx} (T10 : Ty) {s5 : Tm} :
  (forall {d : (Trace TxVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_evarx G T10 s5 d G0 G1)) {X7 : (Index TyVar)} ,
    (lookup_etvar G0 X7) -> (lookup_etvar G1 X7)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Ctx} {S3 : Ty} (wf : (wfTy (domainCtx G) S3)) :
  (forall {d : (Trace TyVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_etvar G S3 d G0 G1)) {x3 : (Index TmVar)} (T10 : Ty) ,
    (lookup_evar G0 x3 T10) -> (lookup_evar G1 x3 (subst_TyVar_Ty d S3 T10))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evarx {G : Ctx} {S3 : Ty} (wf : (wfTy (domainCtx G) S3)) :
  (forall {d : (Trace TyVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_etvar G S3 d G0 G1)) {a1 : (Index TxVar)} (T10 : Ty) ,
    (lookup_evarx G0 a1 T10) -> (lookup_evarx G1 a1 (subst_TyVar_Ty d S3 T10))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_evarx subst_evar_lookup_etvar subst_evarx_lookup_evar subst_evarx_lookup_etvar subst_etvar_lookup_evar subst_etvar_lookup_evarx : infra.
 Hint Resolve subst_evar_lookup_evarx subst_evar_lookup_etvar subst_evarx_lookup_evar subst_evarx_lookup_etvar subst_etvar_lookup_evar subst_etvar_lookup_evarx : lookup.
 Hint Resolve subst_evar_lookup_evarx subst_evar_lookup_etvar subst_evarx_lookup_evar subst_evarx_lookup_etvar subst_etvar_lookup_evar subst_etvar_lookup_evarx : subst.
Fixpoint size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (TVar X7) => 1
    | (TArr T6 T7) => (plus 1 (plus (size_Ty T6) (size_Ty T7)))
    | (TAll T8) => (plus 1 (size_Ty T8))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (Var x3) => 1
    | (XVar a1) => 1
    | (Abs T6 t4) => (plus 1 (plus (size_Ty T6) (size_Tm t4)))
    | (App t5 t6) => (plus 1 (plus (size_Tm t5) (size_Tm t6)))
    | (TAbs t7) => (plus 1 (size_Tm t7))
    | (TApp t8 T7) => (plus 1 (plus (size_Tm t8) (size_Ty T7)))
  end.
Fixpoint shift_TyVar__size_Ty (S0 : Ty) (c : (Cutoff TyVar)) {struct S0} :
((size_Ty (shift_TyVar_Ty c S0)) = (size_Ty S0)) :=
  match S0 return ((size_Ty (shift_TyVar_Ty c S0)) = (size_Ty S0)) with
    | (TVar _) => eq_refl
    | (TArr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T1 c) (shift_TyVar__size_Ty T2 c)))
    | (TAll T) => (f_equal2 plus eq_refl (shift_TyVar__size_Ty T (CS c)))
  end.
Fixpoint shift_TmVar__size_Tm (s : Tm) (c : (Cutoff TmVar)) {struct s} :
((size_Tm (shift_TmVar_Tm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shift_TmVar_Tm c s)) = (size_Tm s)) with
    | (Var _) => eq_refl
    | (XVar _) => eq_refl
    | (Abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_TmVar__size_Tm t (CS c))))
    | (App t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t1 c) (shift_TmVar__size_Tm t2 c)))
    | (TAbs t) => (f_equal2 plus eq_refl (shift_TmVar__size_Tm t c))
    | (TApp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t c) eq_refl))
  end.
Fixpoint shift_TxVar__size_Tm (s : Tm) (c : (Cutoff TxVar)) {struct s} :
((size_Tm (shift_TxVar_Tm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shift_TxVar_Tm c s)) = (size_Tm s)) with
    | (Var _) => eq_refl
    | (XVar _) => eq_refl
    | (Abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_TxVar__size_Tm t c)))
    | (App t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TxVar__size_Tm t1 c) (shift_TxVar__size_Tm t2 c)))
    | (TAbs t) => (f_equal2 plus eq_refl (shift_TxVar__size_Tm t c))
    | (TApp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TxVar__size_Tm t c) eq_refl))
  end.
Fixpoint shift_TyVar__size_Tm (s : Tm) (c : (Cutoff TyVar)) {struct s} :
((size_Tm (shift_TyVar_Tm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shift_TyVar_Tm c s)) = (size_Tm s)) with
    | (Var _) => eq_refl
    | (XVar _) => eq_refl
    | (Abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T c) (shift_TyVar__size_Tm t c)))
    | (App t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Tm t1 c) (shift_TyVar__size_Tm t2 c)))
    | (TAbs t) => (f_equal2 plus eq_refl (shift_TyVar__size_Tm t (CS c)))
    | (TApp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Tm t c) (shift_TyVar__size_Ty T c)))
  end.
 Hint Rewrite shift_TmVar__size_Tm shift_TxVar__size_Tm shift_TyVar__size_Tm shift_TyVar__size_Ty : interaction.
 Hint Rewrite shift_TmVar__size_Tm shift_TxVar__size_Tm shift_TyVar__size_Tm shift_TyVar__size_Ty : shift_size.
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
 Hint Rewrite weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Tm weaken_size_Ty : weaken_size.
 Hint Rewrite appendCtx_assoc : interaction.
 Hint Rewrite <- weakenCutoffTmVar_append weakenCutoffTxVar_append weakenCutoffTyVar_append weakenTrace_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.