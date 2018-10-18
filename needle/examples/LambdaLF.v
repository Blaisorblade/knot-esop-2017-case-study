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
  
  Fixpoint weakenIndexTmVar (x7 : (Index TmVar)) (k : Hvl) {struct k} :
  (Index TmVar) :=
    match k with
      | (H0) => x7
      | (HS a k) => match a with
        | (TmVar) => (IS (weakenIndexTmVar x7 k))
        | _ => (weakenIndexTmVar x7 k)
      end
    end.
  Fixpoint weakenIndexTyVar (X3 : (Index TyVar)) (k : Hvl) {struct k} :
  (Index TyVar) :=
    match k with
      | (H0) => X3
      | (HS a k) => match a with
        | (TyVar) => (IS (weakenIndexTyVar X3 k))
        | _ => (weakenIndexTyVar X3 k)
      end
    end.
  Lemma weakenIndexTmVar_append  :
    (forall (x7 : (Index TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTmVar (weakenIndexTmVar x7 k) k0) = (weakenIndexTmVar x7 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexTyVar_append  :
    (forall (X3 : (Index TyVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTyVar (weakenIndexTyVar X3 k) k0) = (weakenIndexTyVar X3 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Tm : Set :=
    | Var (x : (Index TmVar))
    | Abs (T : Ty) (t : Tm)
    | App (t1 : Tm) (t2 : Tm)
  with Ty : Set :=
    | TVar (X : (Index TyVar))
    | TPi (T1 : Ty) (T2 : Ty)
    | TApp (T : Ty) (t : Tm).
  Scheme ind_Tm := Induction for Tm Sort Prop
  with ind_Ty := Induction for Ty Sort Prop.
  Combined Scheme ind_Tm_Ty from ind_Tm, ind_Ty.
  
  Inductive Kind : Set :=
    | Star 
    | KPi (T : Ty) (K : Kind).
  Scheme ind_Kind := Induction for Kind Sort Prop.
End Terms.

Section Functions.
  
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
  Fixpoint shift_TmVar_Index (c : (Cutoff TmVar)) (x7 : (Index TmVar)) {struct c} :
  (Index TmVar) :=
    match c with
      | (C0) => (IS x7)
      | (CS c) => match x7 with
        | (I0) => I0
        | (IS x7) => (IS (shift_TmVar_Index c x7))
      end
    end.
  Fixpoint shift_TyVar_Index (c : (Cutoff TyVar)) (X3 : (Index TyVar)) {struct c} :
  (Index TyVar) :=
    match c with
      | (C0) => (IS X3)
      | (CS c) => match X3 with
        | (I0) => I0
        | (IS X3) => (IS (shift_TyVar_Index c X3))
      end
    end.
  Fixpoint shift_TmVar_Tm (c : (Cutoff TmVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x7) => (Var (shift_TmVar_Index c x7))
      | (Abs T5 t3) => (Abs (shift_TmVar_Ty c T5) (shift_TmVar_Tm (CS c) t3))
      | (App t4 t5) => (App (shift_TmVar_Tm c t4) (shift_TmVar_Tm c t5))
    end
  with shift_TmVar_Ty (c : (Cutoff TmVar)) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (TVar X3) => (TVar X3)
      | (TPi T5 T6) => (TPi (shift_TmVar_Ty c T5) (shift_TmVar_Ty (CS c) T6))
      | (TApp T7 t3) => (TApp (shift_TmVar_Ty c T7) (shift_TmVar_Tm c t3))
    end.
  Fixpoint shift_TyVar_Tm (c : (Cutoff TyVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x7) => (Var x7)
      | (Abs T5 t3) => (Abs (shift_TyVar_Ty c T5) (shift_TyVar_Tm c t3))
      | (App t4 t5) => (App (shift_TyVar_Tm c t4) (shift_TyVar_Tm c t5))
    end
  with shift_TyVar_Ty (c : (Cutoff TyVar)) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (TVar X3) => (TVar (shift_TyVar_Index c X3))
      | (TPi T5 T6) => (TPi (shift_TyVar_Ty c T5) (shift_TyVar_Ty c T6))
      | (TApp T7 t3) => (TApp (shift_TyVar_Ty c T7) (shift_TyVar_Tm c t3))
    end.
  Fixpoint shift_TmVar_Kind (c : (Cutoff TmVar)) (K1 : Kind) {struct K1} :
  Kind :=
    match K1 with
      | (Star) => (Star)
      | (KPi T5 K2) => (KPi (shift_TmVar_Ty c T5) (shift_TmVar_Kind (CS c) K2))
    end.
  Fixpoint shift_TyVar_Kind (c : (Cutoff TyVar)) (K1 : Kind) {struct K1} :
  Kind :=
    match K1 with
      | (Star) => (Star)
      | (KPi T5 K2) => (KPi (shift_TyVar_Ty c T5) (shift_TyVar_Kind c K2))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} :
  Tm :=
    match k with
      | (H0) => s
      | (HS TmVar k) => (shift_TmVar_Tm C0 (weakenTm s k))
      | (HS TyVar k) => (shift_TyVar_Tm C0 (weakenTm s k))
    end.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S0
      | (HS TmVar k) => (shift_TmVar_Ty C0 (weakenTy S0 k))
      | (HS TyVar k) => (shift_TyVar_Ty C0 (weakenTy S0 k))
    end.
  Fixpoint weakenKind (K1 : Kind) (k : Hvl) {struct k} :
  Kind :=
    match k with
      | (H0) => K1
      | (HS TmVar k) => (shift_TmVar_Kind C0 (weakenKind K1 k))
      | (HS TyVar k) => (shift_TyVar_Kind C0 (weakenKind K1 k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T5 : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x7 : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x7
      | (HS b k) => (XS b (weakenTrace x7 k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x7 : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x7 k) k0) = (weakenTrace x7 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint subst_TmVar_Index (d : (Trace TmVar)) (s : Tm) (x7 : (Index TmVar)) {struct d} :
  Tm :=
    match d with
      | (X0) => match x7 with
        | (I0) => s
        | (IS x7) => (Var x7)
      end
      | (XS TmVar d) => match x7 with
        | (I0) => (Var I0)
        | (IS x7) => (shift_TmVar_Tm C0 (subst_TmVar_Index d s x7))
      end
      | (XS TyVar d) => (shift_TyVar_Tm C0 (subst_TmVar_Index d s x7))
    end.
  Fixpoint subst_TyVar_Index (d : (Trace TyVar)) (S0 : Ty) (X3 : (Index TyVar)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X3 with
        | (I0) => S0
        | (IS X3) => (TVar X3)
      end
      | (XS TmVar d) => (shift_TmVar_Ty C0 (subst_TyVar_Index d S0 X3))
      | (XS TyVar d) => match X3 with
        | (I0) => (TVar I0)
        | (IS X3) => (shift_TyVar_Ty C0 (subst_TyVar_Index d S0 X3))
      end
    end.
  Fixpoint subst_TmVar_Tm (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (Var x7) => (subst_TmVar_Index d s x7)
      | (Abs T5 t3) => (Abs (subst_TmVar_Ty d s T5) (subst_TmVar_Tm (weakenTrace d (HS TmVar H0)) s t3))
      | (App t4 t5) => (App (subst_TmVar_Tm d s t4) (subst_TmVar_Tm d s t5))
    end
  with subst_TmVar_Ty (d : (Trace TmVar)) (s : Tm) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (TVar X3) => (TVar X3)
      | (TPi T5 T6) => (TPi (subst_TmVar_Ty d s T5) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s T6))
      | (TApp T7 t3) => (TApp (subst_TmVar_Ty d s T7) (subst_TmVar_Tm d s t3))
    end.
  Fixpoint subst_TyVar_Tm (d : (Trace TyVar)) (S0 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x7) => (Var x7)
      | (Abs T5 t3) => (Abs (subst_TyVar_Ty d S0 T5) (subst_TyVar_Tm (weakenTrace d (HS TmVar H0)) S0 t3))
      | (App t4 t5) => (App (subst_TyVar_Tm d S0 t4) (subst_TyVar_Tm d S0 t5))
    end
  with subst_TyVar_Ty (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) {struct S1} :
  Ty :=
    match S1 with
      | (TVar X3) => (subst_TyVar_Index d S0 X3)
      | (TPi T5 T6) => (TPi (subst_TyVar_Ty d S0 T5) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S0 T6))
      | (TApp T7 t3) => (TApp (subst_TyVar_Ty d S0 T7) (subst_TyVar_Tm d S0 t3))
    end.
  Fixpoint subst_TmVar_Kind (d : (Trace TmVar)) (s : Tm) (K1 : Kind) {struct K1} :
  Kind :=
    match K1 with
      | (Star) => (Star)
      | (KPi T5 K2) => (KPi (subst_TmVar_Ty d s T5) (subst_TmVar_Kind (weakenTrace d (HS TmVar H0)) s K2))
    end.
  Fixpoint subst_TyVar_Kind (d : (Trace TyVar)) (S0 : Ty) (K1 : Kind) {struct K1} :
  Kind :=
    match K1 with
      | (Star) => (Star)
      | (KPi T5 K2) => (KPi (subst_TyVar_Ty d S0 T5) (subst_TyVar_Kind (weakenTrace d (HS TmVar H0)) S0 K2))
    end.
End Subst.

Global Hint Resolve (f_equal (shift_TmVar_Kind C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TyVar_Kind C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TmVar_Tm C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TyVar_Tm C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TmVar_Ty C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TyVar_Ty C0)) : cong_shift0.
 Hint Rewrite weakenCutoffTmVar_append weakenCutoffTyVar_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Section SubstShiftReflection.
  Lemma subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x7 : (Index TmVar)) ,
      ((subst_TmVar_Index (weakenTrace X0 k) s (shift_TmVar_Index (weakenCutoffTmVar C0 k) x7)) = (Var x7))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma subst_TyVar_Index0_shift_TyVar_Index0_reflection_ind (S0 : Ty) :
    (forall (k : Hvl) (X3 : (Index TyVar)) ,
      ((subst_TyVar_Index (weakenTrace X0 k) S0 (shift_TyVar_Index (weakenCutoffTyVar C0 k) X3)) = (TVar X3))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((subst_TmVar_Tm (weakenTrace X0 k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = s0) :=
    match s0 return ((subst_TmVar_Tm (weakenTrace X0 k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = s0) with
      | (Var x7) => (subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind s k x7)
      | (Abs T5 t3) => (f_equal2 Abs (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T5 k s) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t3 (HS TmVar k) s)))
      | (App t4 t5) => (f_equal2 App (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t4 k s) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t5 k s))
    end
  with subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind (S0 : Ty) (k : Hvl) (s : Tm) {struct S0} :
  ((subst_TmVar_Ty (weakenTrace X0 k) s (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S0)) = S0) :=
    match S0 return ((subst_TmVar_Ty (weakenTrace X0 k) s (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S0)) = S0) with
      | (TVar X3) => eq_refl
      | (TPi T7 T8) => (f_equal2 TPi (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T7 k s) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T8 (HS TmVar k) s)))
      | (TApp T6 t6) => (f_equal2 TApp (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T6 k s) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t6 k s))
    end.
  Fixpoint subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind (s : Tm) (k : Hvl) (S0 : Ty) {struct s} :
  ((subst_TyVar_Tm (weakenTrace X0 k) S0 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = s) :=
    match s return ((subst_TyVar_Tm (weakenTrace X0 k) S0 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = s) with
      | (Var x7) => eq_refl
      | (Abs T5 t3) => (f_equal2 Abs (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T5 k S0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t3 (HS TmVar k) S0)))
      | (App t4 t5) => (f_equal2 App (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t4 k S0) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t5 k S0))
    end
  with subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind (S1 : Ty) (k : Hvl) (S0 : Ty) {struct S1} :
  ((subst_TyVar_Ty (weakenTrace X0 k) S0 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = S1) :=
    match S1 return ((subst_TyVar_Ty (weakenTrace X0 k) S0 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = S1) with
      | (TVar X3) => (subst_TyVar_Index0_shift_TyVar_Index0_reflection_ind S0 k X3)
      | (TPi T7 T8) => (f_equal2 TPi (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T7 k S0) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T8 (HS TmVar k) S0)))
      | (TApp T6 t6) => (f_equal2 TApp (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T6 k S0) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t6 k S0))
    end.
  Fixpoint subst_TmVar_0_shift_TmVar_0_Kind_reflection_ind (K1 : Kind) (k : Hvl) (s : Tm) {struct K1} :
  ((subst_TmVar_Kind (weakenTrace X0 k) s (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K1)) = K1) :=
    match K1 return ((subst_TmVar_Kind (weakenTrace X0 k) s (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K1)) = K1) with
      | (Star) => eq_refl
      | (KPi T5 K2) => (f_equal2 KPi (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T5 k s) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Kind_reflection_ind K2 (HS TmVar k) s)))
    end.
  Fixpoint subst_TyVar_0_shift_TyVar_0_Kind_reflection_ind (K1 : Kind) (k : Hvl) (S0 : Ty) {struct K1} :
  ((subst_TyVar_Kind (weakenTrace X0 k) S0 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K1)) = K1) :=
    match K1 return ((subst_TyVar_Kind (weakenTrace X0 k) S0 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K1)) = K1) with
      | (Star) => eq_refl
      | (KPi T5 K2) => (f_equal2 KPi (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T5 k S0) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Kind_reflection_ind K2 (HS TmVar k) S0)))
    end.
  Definition subst_TmVar_Tm0_shift_TmVar_Tm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((subst_TmVar_Tm X0 s (shift_TmVar_Tm C0 s0)) = s0)) := (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind s0 H0).
  Definition subst_TmVar_Ty0_shift_TmVar_Ty0_reflection (S0 : Ty) : (forall (s : Tm) ,
    ((subst_TmVar_Ty X0 s (shift_TmVar_Ty C0 S0)) = S0)) := (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind S0 H0).
  Definition subst_TyVar_Tm0_shift_TyVar_Tm0_reflection (s : Tm) : (forall (S0 : Ty) ,
    ((subst_TyVar_Tm X0 S0 (shift_TyVar_Tm C0 s)) = s)) := (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind s H0).
  Definition subst_TyVar_Ty0_shift_TyVar_Ty0_reflection (S1 : Ty) : (forall (S0 : Ty) ,
    ((subst_TyVar_Ty X0 S0 (shift_TyVar_Ty C0 S1)) = S1)) := (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind S1 H0).
  Definition subst_TmVar_Kind0_shift_TmVar_Kind0_reflection (K1 : Kind) : (forall (s : Tm) ,
    ((subst_TmVar_Kind X0 s (shift_TmVar_Kind C0 K1)) = K1)) := (subst_TmVar_0_shift_TmVar_0_Kind_reflection_ind K1 H0).
  Definition subst_TyVar_Kind0_shift_TyVar_Kind0_reflection (K1 : Kind) : (forall (S0 : Ty) ,
    ((subst_TyVar_Kind X0 S0 (shift_TyVar_Kind C0 K1)) = K1)) := (subst_TyVar_0_shift_TyVar_0_Kind_reflection_ind K1 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shift_TmVar_Index_shift_TmVar_Index0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff TmVar)) (x7 : (Index TmVar)) ,
        ((shift_TmVar_Index (weakenCutoffTmVar (CS c) k) (shift_TmVar_Index (weakenCutoffTmVar C0 k) x7)) = (shift_TmVar_Index (weakenCutoffTmVar C0 k) (shift_TmVar_Index (weakenCutoffTmVar c k) x7)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma shift_TyVar_Index_shift_TyVar_Index0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff TyVar)) (X3 : (Index TyVar)) ,
        ((shift_TyVar_Index (weakenCutoffTyVar (CS c) k) (shift_TyVar_Index (weakenCutoffTyVar C0 k) X3)) = (shift_TyVar_Index (weakenCutoffTyVar C0 k) (shift_TyVar_Index (weakenCutoffTyVar c k) X3)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint shift_TmVar__shift_TmVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TmVar)) {struct s} :
    ((shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) :=
      match s return ((shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) with
        | (Var x7) => (f_equal Var (shift_TmVar_Index_shift_TmVar_Index0_comm_ind k c x7))
        | (Abs T5 t3) => (f_equal2 Abs (shift_TmVar__shift_TmVar_0_Ty_comm_ind T5 k c) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t3 (HS TmVar k) c))
        | (App t4 t5) => (f_equal2 App (shift_TmVar__shift_TmVar_0_Tm_comm_ind t4 k c) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t5 k c))
      end
    with shift_TmVar__shift_TmVar_0_Ty_comm_ind (S0 : Ty) (k : Hvl) (c : (Cutoff TmVar)) {struct S0} :
    ((shift_TmVar_Ty (weakenCutoffTmVar (CS c) k) (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S0)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (shift_TmVar_Ty (weakenCutoffTmVar c k) S0))) :=
      match S0 return ((shift_TmVar_Ty (weakenCutoffTmVar (CS c) k) (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S0)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (shift_TmVar_Ty (weakenCutoffTmVar c k) S0))) with
        | (TVar X3) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (shift_TmVar__shift_TmVar_0_Ty_comm_ind T7 k c) (shift_TmVar__shift_TmVar_0_Ty_comm_ind T8 (HS TmVar k) c))
        | (TApp T6 t6) => (f_equal2 TApp (shift_TmVar__shift_TmVar_0_Ty_comm_ind T6 k c) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t6 k c))
      end.
    Fixpoint shift_TmVar__shift_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TmVar)) {struct s} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) :=
      match s return ((shift_TmVar_Tm (weakenCutoffTmVar c k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) with
        | (Var x7) => eq_refl
        | (Abs T5 t3) => (f_equal2 Abs (shift_TmVar__shift_TyVar_0_Ty_comm_ind T5 k c) (shift_TmVar__shift_TyVar_0_Tm_comm_ind t3 (HS TmVar k) c))
        | (App t4 t5) => (f_equal2 App (shift_TmVar__shift_TyVar_0_Tm_comm_ind t4 k c) (shift_TmVar__shift_TyVar_0_Tm_comm_ind t5 k c))
      end
    with shift_TmVar__shift_TyVar_0_Ty_comm_ind (S0 : Ty) (k : Hvl) (c : (Cutoff TmVar)) {struct S0} :
    ((shift_TmVar_Ty (weakenCutoffTmVar c k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S0)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TmVar_Ty (weakenCutoffTmVar c k) S0))) :=
      match S0 return ((shift_TmVar_Ty (weakenCutoffTmVar c k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S0)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TmVar_Ty (weakenCutoffTmVar c k) S0))) with
        | (TVar X3) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (shift_TmVar__shift_TyVar_0_Ty_comm_ind T7 k c) (shift_TmVar__shift_TyVar_0_Ty_comm_ind T8 (HS TmVar k) c))
        | (TApp T6 t6) => (f_equal2 TApp (shift_TmVar__shift_TyVar_0_Ty_comm_ind T6 k c) (shift_TmVar__shift_TyVar_0_Tm_comm_ind t6 k c))
      end.
    Fixpoint shift_TyVar__shift_TmVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TyVar)) {struct s} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c k) s))) :=
      match s return ((shift_TyVar_Tm (weakenCutoffTyVar c k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c k) s))) with
        | (Var x7) => eq_refl
        | (Abs T5 t3) => (f_equal2 Abs (shift_TyVar__shift_TmVar_0_Ty_comm_ind T5 k c) (shift_TyVar__shift_TmVar_0_Tm_comm_ind t3 (HS TmVar k) c))
        | (App t4 t5) => (f_equal2 App (shift_TyVar__shift_TmVar_0_Tm_comm_ind t4 k c) (shift_TyVar__shift_TmVar_0_Tm_comm_ind t5 k c))
      end
    with shift_TyVar__shift_TmVar_0_Ty_comm_ind (S0 : Ty) (k : Hvl) (c : (Cutoff TyVar)) {struct S0} :
    ((shift_TyVar_Ty (weakenCutoffTyVar c k) (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S0)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c k) S0))) :=
      match S0 return ((shift_TyVar_Ty (weakenCutoffTyVar c k) (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S0)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c k) S0))) with
        | (TVar X3) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (shift_TyVar__shift_TmVar_0_Ty_comm_ind T7 k c) (shift_TyVar__shift_TmVar_0_Ty_comm_ind T8 (HS TmVar k) c))
        | (TApp T6 t6) => (f_equal2 TApp (shift_TyVar__shift_TmVar_0_Ty_comm_ind T6 k c) (shift_TyVar__shift_TmVar_0_Tm_comm_ind t6 k c))
      end.
    Fixpoint shift_TyVar__shift_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TyVar)) {struct s} :
    ((shift_TyVar_Tm (weakenCutoffTyVar (CS c) k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c k) s))) :=
      match s return ((shift_TyVar_Tm (weakenCutoffTyVar (CS c) k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c k) s))) with
        | (Var x7) => eq_refl
        | (Abs T5 t3) => (f_equal2 Abs (shift_TyVar__shift_TyVar_0_Ty_comm_ind T5 k c) (shift_TyVar__shift_TyVar_0_Tm_comm_ind t3 (HS TmVar k) c))
        | (App t4 t5) => (f_equal2 App (shift_TyVar__shift_TyVar_0_Tm_comm_ind t4 k c) (shift_TyVar__shift_TyVar_0_Tm_comm_ind t5 k c))
      end
    with shift_TyVar__shift_TyVar_0_Ty_comm_ind (S0 : Ty) (k : Hvl) (c : (Cutoff TyVar)) {struct S0} :
    ((shift_TyVar_Ty (weakenCutoffTyVar (CS c) k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S0)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c k) S0))) :=
      match S0 return ((shift_TyVar_Ty (weakenCutoffTyVar (CS c) k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S0)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c k) S0))) with
        | (TVar X3) => (f_equal TVar (shift_TyVar_Index_shift_TyVar_Index0_comm_ind k c X3))
        | (TPi T7 T8) => (f_equal2 TPi (shift_TyVar__shift_TyVar_0_Ty_comm_ind T7 k c) (shift_TyVar__shift_TyVar_0_Ty_comm_ind T8 (HS TmVar k) c))
        | (TApp T6 t6) => (f_equal2 TApp (shift_TyVar__shift_TyVar_0_Ty_comm_ind T6 k c) (shift_TyVar__shift_TyVar_0_Tm_comm_ind t6 k c))
      end.
    Fixpoint shift_TmVar__shift_TmVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (c : (Cutoff TmVar)) {struct K1} :
    ((shift_TmVar_Kind (weakenCutoffTmVar (CS c) k) (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K1)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (shift_TmVar_Kind (weakenCutoffTmVar c k) K1))) :=
      match K1 return ((shift_TmVar_Kind (weakenCutoffTmVar (CS c) k) (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K1)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (shift_TmVar_Kind (weakenCutoffTmVar c k) K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (shift_TmVar__shift_TmVar_0_Ty_comm_ind T5 k c) (shift_TmVar__shift_TmVar_0_Kind_comm_ind K2 (HS TmVar k) c))
      end.
    Fixpoint shift_TmVar__shift_TyVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (c : (Cutoff TmVar)) {struct K1} :
    ((shift_TmVar_Kind (weakenCutoffTmVar c k) (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K1)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (shift_TmVar_Kind (weakenCutoffTmVar c k) K1))) :=
      match K1 return ((shift_TmVar_Kind (weakenCutoffTmVar c k) (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K1)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (shift_TmVar_Kind (weakenCutoffTmVar c k) K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (shift_TmVar__shift_TyVar_0_Ty_comm_ind T5 k c) (shift_TmVar__shift_TyVar_0_Kind_comm_ind K2 (HS TmVar k) c))
      end.
    Fixpoint shift_TyVar__shift_TmVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (c : (Cutoff TyVar)) {struct K1} :
    ((shift_TyVar_Kind (weakenCutoffTyVar c k) (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K1)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (shift_TyVar_Kind (weakenCutoffTyVar c k) K1))) :=
      match K1 return ((shift_TyVar_Kind (weakenCutoffTyVar c k) (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K1)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (shift_TyVar_Kind (weakenCutoffTyVar c k) K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (shift_TyVar__shift_TmVar_0_Ty_comm_ind T5 k c) (shift_TyVar__shift_TmVar_0_Kind_comm_ind K2 (HS TmVar k) c))
      end.
    Fixpoint shift_TyVar__shift_TyVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (c : (Cutoff TyVar)) {struct K1} :
    ((shift_TyVar_Kind (weakenCutoffTyVar (CS c) k) (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K1)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (shift_TyVar_Kind (weakenCutoffTyVar c k) K1))) :=
      match K1 return ((shift_TyVar_Kind (weakenCutoffTyVar (CS c) k) (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K1)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (shift_TyVar_Kind (weakenCutoffTyVar c k) K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (shift_TyVar__shift_TyVar_0_Ty_comm_ind T5 k c) (shift_TyVar__shift_TyVar_0_Kind_comm_ind K2 (HS TmVar k) c))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition shift_TmVar__shift_TmVar_0_Tm_comm (s : Tm) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Tm (CS c) (shift_TmVar_Tm C0 s)) = (shift_TmVar_Tm C0 (shift_TmVar_Tm c s)))) := (shift_TmVar__shift_TmVar_0_Tm_comm_ind s H0).
    Definition shift_TmVar__shift_TmVar_0_Ty_comm (S0 : Ty) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Ty (CS c) (shift_TmVar_Ty C0 S0)) = (shift_TmVar_Ty C0 (shift_TmVar_Ty c S0)))) := (shift_TmVar__shift_TmVar_0_Ty_comm_ind S0 H0).
    Definition shift_TmVar__shift_TyVar_0_Tm_comm (s : Tm) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Tm c (shift_TyVar_Tm C0 s)) = (shift_TyVar_Tm C0 (shift_TmVar_Tm c s)))) := (shift_TmVar__shift_TyVar_0_Tm_comm_ind s H0).
    Definition shift_TmVar__shift_TyVar_0_Ty_comm (S0 : Ty) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Ty c (shift_TyVar_Ty C0 S0)) = (shift_TyVar_Ty C0 (shift_TmVar_Ty c S0)))) := (shift_TmVar__shift_TyVar_0_Ty_comm_ind S0 H0).
    Definition shift_TyVar__shift_TmVar_0_Tm_comm (s : Tm) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Tm c (shift_TmVar_Tm C0 s)) = (shift_TmVar_Tm C0 (shift_TyVar_Tm c s)))) := (shift_TyVar__shift_TmVar_0_Tm_comm_ind s H0).
    Definition shift_TyVar__shift_TmVar_0_Ty_comm (S0 : Ty) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Ty c (shift_TmVar_Ty C0 S0)) = (shift_TmVar_Ty C0 (shift_TyVar_Ty c S0)))) := (shift_TyVar__shift_TmVar_0_Ty_comm_ind S0 H0).
    Definition shift_TyVar__shift_TyVar_0_Tm_comm (s : Tm) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Tm (CS c) (shift_TyVar_Tm C0 s)) = (shift_TyVar_Tm C0 (shift_TyVar_Tm c s)))) := (shift_TyVar__shift_TyVar_0_Tm_comm_ind s H0).
    Definition shift_TyVar__shift_TyVar_0_Ty_comm (S0 : Ty) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Ty (CS c) (shift_TyVar_Ty C0 S0)) = (shift_TyVar_Ty C0 (shift_TyVar_Ty c S0)))) := (shift_TyVar__shift_TyVar_0_Ty_comm_ind S0 H0).
    Definition shift_TmVar__shift_TmVar_0_Kind_comm (K1 : Kind) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Kind (CS c) (shift_TmVar_Kind C0 K1)) = (shift_TmVar_Kind C0 (shift_TmVar_Kind c K1)))) := (shift_TmVar__shift_TmVar_0_Kind_comm_ind K1 H0).
    Definition shift_TmVar__shift_TyVar_0_Kind_comm (K1 : Kind) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Kind c (shift_TyVar_Kind C0 K1)) = (shift_TyVar_Kind C0 (shift_TmVar_Kind c K1)))) := (shift_TmVar__shift_TyVar_0_Kind_comm_ind K1 H0).
    Definition shift_TyVar__shift_TmVar_0_Kind_comm (K1 : Kind) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Kind c (shift_TmVar_Kind C0 K1)) = (shift_TmVar_Kind C0 (shift_TyVar_Kind c K1)))) := (shift_TyVar__shift_TmVar_0_Kind_comm_ind K1 H0).
    Definition shift_TyVar__shift_TyVar_0_Kind_comm (K1 : Kind) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Kind (CS c) (shift_TyVar_Kind C0 K1)) = (shift_TyVar_Kind C0 (shift_TyVar_Kind c K1)))) := (shift_TyVar__shift_TyVar_0_Kind_comm_ind K1 H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_TmVar__shift_TmVar_0_Kind_comm shift_TmVar__shift_TyVar_0_Kind_comm shift_TyVar__shift_TmVar_0_Kind_comm shift_TyVar__shift_TyVar_0_Kind_comm shift_TmVar__shift_TmVar_0_Tm_comm shift_TmVar__shift_TyVar_0_Tm_comm shift_TyVar__shift_TmVar_0_Tm_comm shift_TyVar__shift_TyVar_0_Tm_comm shift_TmVar__shift_TmVar_0_Ty_comm shift_TmVar__shift_TyVar_0_Ty_comm shift_TyVar__shift_TmVar_0_Ty_comm shift_TyVar__shift_TyVar_0_Ty_comm : interaction.
 Hint Rewrite shift_TmVar__shift_TmVar_0_Kind_comm shift_TmVar__shift_TyVar_0_Kind_comm shift_TyVar__shift_TmVar_0_Kind_comm shift_TyVar__shift_TyVar_0_Kind_comm shift_TmVar__shift_TmVar_0_Tm_comm shift_TmVar__shift_TyVar_0_Tm_comm shift_TyVar__shift_TmVar_0_Tm_comm shift_TyVar__shift_TyVar_0_Tm_comm shift_TmVar__shift_TmVar_0_Ty_comm shift_TmVar__shift_TyVar_0_Ty_comm shift_TyVar__shift_TmVar_0_Ty_comm shift_TyVar__shift_TyVar_0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTm_shift_TmVar_Tm  :
    (forall (k : Hvl) (c : (Cutoff TmVar)) (s : Tm) ,
      ((weakenTm (shift_TmVar_Tm c s) k) = (shift_TmVar_Tm (weakenCutoffTmVar c k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTy_shift_TmVar_Ty  :
    (forall (k : Hvl) (c : (Cutoff TmVar)) (S0 : Ty) ,
      ((weakenTy (shift_TmVar_Ty c S0) k) = (shift_TmVar_Ty (weakenCutoffTmVar c k) (weakenTy S0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shift_TyVar_Tm  :
    (forall (k : Hvl) (c : (Cutoff TyVar)) (s : Tm) ,
      ((weakenTm (shift_TyVar_Tm c s) k) = (shift_TyVar_Tm (weakenCutoffTyVar c k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTy_shift_TyVar_Ty  :
    (forall (k : Hvl) (c : (Cutoff TyVar)) (S0 : Ty) ,
      ((weakenTy (shift_TyVar_Ty c S0) k) = (shift_TyVar_Ty (weakenCutoffTyVar c k) (weakenTy S0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenKind_shift_TmVar_Kind  :
    (forall (k : Hvl) (c : (Cutoff TmVar)) (K1 : Kind) ,
      ((weakenKind (shift_TmVar_Kind c K1) k) = (shift_TmVar_Kind (weakenCutoffTmVar c k) (weakenKind K1 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenKind_shift_TyVar_Kind  :
    (forall (k : Hvl) (c : (Cutoff TyVar)) (K1 : Kind) ,
      ((weakenKind (shift_TyVar_Kind c K1) k) = (shift_TyVar_Kind (weakenCutoffTyVar c k) (weakenKind K1 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shift_TmVar_Tm_subst_TmVar_Index0_comm_ind (c : (Cutoff TmVar)) (s : Tm) :
      (forall (k : Hvl) (x7 : (Index TmVar)) ,
        ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Index (weakenTrace X0 k) s x7)) = (subst_TmVar_Index (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Index (weakenCutoffTmVar (CS c) k) x7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TyVar_Tm_subst_TmVar_Index0_comm_ind (c : (Cutoff TyVar)) (s : Tm) :
      (forall (k : Hvl) (x7 : (Index TmVar)) ,
        ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TmVar_Index (weakenTrace X0 k) s x7)) = (subst_TmVar_Index (weakenTrace X0 k) (shift_TyVar_Tm c s) x7))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TmVar_Ty_subst_TyVar_Index0_comm_ind (c : (Cutoff TmVar)) (S0 : Ty) :
      (forall (k : Hvl) (X3 : (Index TyVar)) ,
        ((shift_TmVar_Ty (weakenCutoffTmVar c k) (subst_TyVar_Index (weakenTrace X0 k) S0 X3)) = (subst_TyVar_Index (weakenTrace X0 k) (shift_TmVar_Ty c S0) X3))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TyVar_Ty_subst_TyVar_Index0_comm_ind (c : (Cutoff TyVar)) (S0 : Ty) :
      (forall (k : Hvl) (X3 : (Index TyVar)) ,
        ((shift_TyVar_Ty (weakenCutoffTyVar c k) (subst_TyVar_Index (weakenTrace X0 k) S0 X3)) = (subst_TyVar_Index (weakenTrace X0 k) (shift_TyVar_Ty c S0) (shift_TyVar_Index (weakenCutoffTyVar (CS c) k) X3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint shift_TmVar__subst_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff TmVar)) (s : Tm) {struct s0} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) s0))) :=
      match s0 return ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) s0))) with
        | (Var x7) => (shift_TmVar_Tm_subst_TmVar_Index0_comm_ind c s k x7)
        | (Abs T5 t3) => (f_equal2 Abs (shift_TmVar__subst_TmVar_0_Ty_comm_ind T5 k c s) (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind t3 (HS TmVar k) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t4 t5) => (f_equal2 App (shift_TmVar__subst_TmVar_0_Tm_comm_ind t4 k c s) (shift_TmVar__subst_TmVar_0_Tm_comm_ind t5 k c s))
      end
    with shift_TmVar__subst_TmVar_0_Ty_comm_ind (S0 : Ty) (k : Hvl) (c : (Cutoff TmVar)) (s : Tm) {struct S0} :
    ((shift_TmVar_Ty (weakenCutoffTmVar c k) (subst_TmVar_Ty (weakenTrace X0 k) s S0)) = (subst_TmVar_Ty (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Ty (weakenCutoffTmVar (CS c) k) S0))) :=
      match S0 return ((shift_TmVar_Ty (weakenCutoffTmVar c k) (subst_TmVar_Ty (weakenTrace X0 k) s S0)) = (subst_TmVar_Ty (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Ty (weakenCutoffTmVar (CS c) k) S0))) with
        | (TVar X3) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (shift_TmVar__subst_TmVar_0_Ty_comm_ind T7 k c s) (eq_trans (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Ty_comm_ind T8 (HS TmVar k) c s) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (TApp T6 t6) => (f_equal2 TApp (shift_TmVar__subst_TmVar_0_Ty_comm_ind T6 k c s) (shift_TmVar__subst_TmVar_0_Tm_comm_ind t6 k c s))
      end.
    Fixpoint shift_TmVar__subst_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TmVar)) (S0 : Ty) {struct s} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S0 s)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TmVar_Ty c S0) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) :=
      match s return ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S0 s)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TmVar_Ty c S0) (shift_TmVar_Tm (weakenCutoffTmVar c k) s))) with
        | (Var x7) => eq_refl
        | (Abs T5 t3) => (f_equal2 Abs (shift_TmVar__subst_TyVar_0_Ty_comm_ind T5 k c S0) (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Tm_comm_ind t3 (HS TmVar k) c S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t4 t5) => (f_equal2 App (shift_TmVar__subst_TyVar_0_Tm_comm_ind t4 k c S0) (shift_TmVar__subst_TyVar_0_Tm_comm_ind t5 k c S0))
      end
    with shift_TmVar__subst_TyVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c : (Cutoff TmVar)) (S0 : Ty) {struct S1} :
    ((shift_TmVar_Ty (weakenCutoffTmVar c k) (subst_TyVar_Ty (weakenTrace X0 k) S0 S1)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TmVar_Ty c S0) (shift_TmVar_Ty (weakenCutoffTmVar c k) S1))) :=
      match S1 return ((shift_TmVar_Ty (weakenCutoffTmVar c k) (subst_TyVar_Ty (weakenTrace X0 k) S0 S1)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TmVar_Ty c S0) (shift_TmVar_Ty (weakenCutoffTmVar c k) S1))) with
        | (TVar X3) => (shift_TmVar_Ty_subst_TyVar_Index0_comm_ind c S0 k X3)
        | (TPi T7 T8) => (f_equal2 TPi (shift_TmVar__subst_TyVar_0_Ty_comm_ind T7 k c S0) (eq_trans (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Ty_comm_ind T8 (HS TmVar k) c S0) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (TApp T6 t6) => (f_equal2 TApp (shift_TmVar__subst_TyVar_0_Ty_comm_ind T6 k c S0) (shift_TmVar__subst_TyVar_0_Tm_comm_ind t6 k c S0))
      end.
    Fixpoint shift_TyVar__subst_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff TyVar)) (s : Tm) {struct s0} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TyVar_Tm c s) (shift_TyVar_Tm (weakenCutoffTyVar c k) s0))) :=
      match s0 return ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TyVar_Tm c s) (shift_TyVar_Tm (weakenCutoffTyVar c k) s0))) with
        | (Var x7) => (shift_TyVar_Tm_subst_TmVar_Index0_comm_ind c s k x7)
        | (Abs T5 t3) => (f_equal2 Abs (shift_TyVar__subst_TmVar_0_Ty_comm_ind T5 k c s) (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Tm_comm_ind t3 (HS TmVar k) c s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t4 t5) => (f_equal2 App (shift_TyVar__subst_TmVar_0_Tm_comm_ind t4 k c s) (shift_TyVar__subst_TmVar_0_Tm_comm_ind t5 k c s))
      end
    with shift_TyVar__subst_TmVar_0_Ty_comm_ind (S0 : Ty) (k : Hvl) (c : (Cutoff TyVar)) (s : Tm) {struct S0} :
    ((shift_TyVar_Ty (weakenCutoffTyVar c k) (subst_TmVar_Ty (weakenTrace X0 k) s S0)) = (subst_TmVar_Ty (weakenTrace X0 k) (shift_TyVar_Tm c s) (shift_TyVar_Ty (weakenCutoffTyVar c k) S0))) :=
      match S0 return ((shift_TyVar_Ty (weakenCutoffTyVar c k) (subst_TmVar_Ty (weakenTrace X0 k) s S0)) = (subst_TmVar_Ty (weakenTrace X0 k) (shift_TyVar_Tm c s) (shift_TyVar_Ty (weakenCutoffTyVar c k) S0))) with
        | (TVar X3) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (shift_TyVar__subst_TmVar_0_Ty_comm_ind T7 k c s) (eq_trans (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Ty_comm_ind T8 (HS TmVar k) c s) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (TApp T6 t6) => (f_equal2 TApp (shift_TyVar__subst_TmVar_0_Ty_comm_ind T6 k c s) (shift_TyVar__subst_TmVar_0_Tm_comm_ind t6 k c s))
      end.
    Fixpoint shift_TyVar__subst_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff TyVar)) (S0 : Ty) {struct s} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S0 s)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TyVar_Ty c S0) (shift_TyVar_Tm (weakenCutoffTyVar (CS c) k) s))) :=
      match s return ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S0 s)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TyVar_Ty c S0) (shift_TyVar_Tm (weakenCutoffTyVar (CS c) k) s))) with
        | (Var x7) => eq_refl
        | (Abs T5 t3) => (f_equal2 Abs (shift_TyVar__subst_TyVar_0_Ty_comm_ind T5 k c S0) (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Tm_comm_ind t3 (HS TmVar k) c S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t4 t5) => (f_equal2 App (shift_TyVar__subst_TyVar_0_Tm_comm_ind t4 k c S0) (shift_TyVar__subst_TyVar_0_Tm_comm_ind t5 k c S0))
      end
    with shift_TyVar__subst_TyVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c : (Cutoff TyVar)) (S0 : Ty) {struct S1} :
    ((shift_TyVar_Ty (weakenCutoffTyVar c k) (subst_TyVar_Ty (weakenTrace X0 k) S0 S1)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TyVar_Ty c S0) (shift_TyVar_Ty (weakenCutoffTyVar (CS c) k) S1))) :=
      match S1 return ((shift_TyVar_Ty (weakenCutoffTyVar c k) (subst_TyVar_Ty (weakenTrace X0 k) S0 S1)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TyVar_Ty c S0) (shift_TyVar_Ty (weakenCutoffTyVar (CS c) k) S1))) with
        | (TVar X3) => (shift_TyVar_Ty_subst_TyVar_Index0_comm_ind c S0 k X3)
        | (TPi T7 T8) => (f_equal2 TPi (shift_TyVar__subst_TyVar_0_Ty_comm_ind T7 k c S0) (eq_trans (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Ty_comm_ind T8 (HS TmVar k) c S0) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (TApp T6 t6) => (f_equal2 TApp (shift_TyVar__subst_TyVar_0_Ty_comm_ind T6 k c S0) (shift_TyVar__subst_TyVar_0_Tm_comm_ind t6 k c S0))
      end.
    Fixpoint shift_TmVar__subst_TmVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (c : (Cutoff TmVar)) (s : Tm) {struct K1} :
    ((shift_TmVar_Kind (weakenCutoffTmVar c k) (subst_TmVar_Kind (weakenTrace X0 k) s K1)) = (subst_TmVar_Kind (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Kind (weakenCutoffTmVar (CS c) k) K1))) :=
      match K1 return ((shift_TmVar_Kind (weakenCutoffTmVar c k) (subst_TmVar_Kind (weakenTrace X0 k) s K1)) = (subst_TmVar_Kind (weakenTrace X0 k) (shift_TmVar_Tm c s) (shift_TmVar_Kind (weakenCutoffTmVar (CS c) k) K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (shift_TmVar__subst_TmVar_0_Ty_comm_ind T5 k c s) (eq_trans (f_equal2 shift_TmVar_Kind eq_refl (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Kind_comm_ind K2 (HS TmVar k) c s) (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_TmVar__subst_TyVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (c : (Cutoff TmVar)) (S0 : Ty) {struct K1} :
    ((shift_TmVar_Kind (weakenCutoffTmVar c k) (subst_TyVar_Kind (weakenTrace X0 k) S0 K1)) = (subst_TyVar_Kind (weakenTrace X0 k) (shift_TmVar_Ty c S0) (shift_TmVar_Kind (weakenCutoffTmVar c k) K1))) :=
      match K1 return ((shift_TmVar_Kind (weakenCutoffTmVar c k) (subst_TyVar_Kind (weakenTrace X0 k) S0 K1)) = (subst_TyVar_Kind (weakenTrace X0 k) (shift_TmVar_Ty c S0) (shift_TmVar_Kind (weakenCutoffTmVar c k) K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (shift_TmVar__subst_TyVar_0_Ty_comm_ind T5 k c S0) (eq_trans (f_equal2 shift_TmVar_Kind eq_refl (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Kind_comm_ind K2 (HS TmVar k) c S0) (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_TyVar__subst_TmVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (c : (Cutoff TyVar)) (s : Tm) {struct K1} :
    ((shift_TyVar_Kind (weakenCutoffTyVar c k) (subst_TmVar_Kind (weakenTrace X0 k) s K1)) = (subst_TmVar_Kind (weakenTrace X0 k) (shift_TyVar_Tm c s) (shift_TyVar_Kind (weakenCutoffTyVar c k) K1))) :=
      match K1 return ((shift_TyVar_Kind (weakenCutoffTyVar c k) (subst_TmVar_Kind (weakenTrace X0 k) s K1)) = (subst_TmVar_Kind (weakenTrace X0 k) (shift_TyVar_Tm c s) (shift_TyVar_Kind (weakenCutoffTyVar c k) K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (shift_TyVar__subst_TmVar_0_Ty_comm_ind T5 k c s) (eq_trans (f_equal2 shift_TyVar_Kind eq_refl (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Kind_comm_ind K2 (HS TmVar k) c s) (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_TyVar__subst_TyVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (c : (Cutoff TyVar)) (S0 : Ty) {struct K1} :
    ((shift_TyVar_Kind (weakenCutoffTyVar c k) (subst_TyVar_Kind (weakenTrace X0 k) S0 K1)) = (subst_TyVar_Kind (weakenTrace X0 k) (shift_TyVar_Ty c S0) (shift_TyVar_Kind (weakenCutoffTyVar (CS c) k) K1))) :=
      match K1 return ((shift_TyVar_Kind (weakenCutoffTyVar c k) (subst_TyVar_Kind (weakenTrace X0 k) S0 K1)) = (subst_TyVar_Kind (weakenTrace X0 k) (shift_TyVar_Ty c S0) (shift_TyVar_Kind (weakenCutoffTyVar (CS c) k) K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (shift_TyVar__subst_TyVar_0_Ty_comm_ind T5 k c S0) (eq_trans (f_equal2 shift_TyVar_Kind eq_refl (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Kind_comm_ind K2 (HS TmVar k) c S0) (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shift_TmVar_Tm_subst_TmVar_Tm0_comm (s0 : Tm) : (forall (c : (Cutoff TmVar)) (s : Tm) ,
      ((shift_TmVar_Tm c (subst_TmVar_Tm X0 s s0)) = (subst_TmVar_Tm X0 (shift_TmVar_Tm c s) (shift_TmVar_Tm (CS c) s0)))) := (shift_TmVar__subst_TmVar_0_Tm_comm_ind s0 H0).
    Definition shift_TmVar_Ty_subst_TmVar_Ty0_comm (S0 : Ty) : (forall (c : (Cutoff TmVar)) (s : Tm) ,
      ((shift_TmVar_Ty c (subst_TmVar_Ty X0 s S0)) = (subst_TmVar_Ty X0 (shift_TmVar_Tm c s) (shift_TmVar_Ty (CS c) S0)))) := (shift_TmVar__subst_TmVar_0_Ty_comm_ind S0 H0).
    Definition shift_TmVar_Tm_subst_TyVar_Tm0_comm (s : Tm) : (forall (c : (Cutoff TmVar)) (S0 : Ty) ,
      ((shift_TmVar_Tm c (subst_TyVar_Tm X0 S0 s)) = (subst_TyVar_Tm X0 (shift_TmVar_Ty c S0) (shift_TmVar_Tm c s)))) := (shift_TmVar__subst_TyVar_0_Tm_comm_ind s H0).
    Definition shift_TmVar_Ty_subst_TyVar_Ty0_comm (S1 : Ty) : (forall (c : (Cutoff TmVar)) (S0 : Ty) ,
      ((shift_TmVar_Ty c (subst_TyVar_Ty X0 S0 S1)) = (subst_TyVar_Ty X0 (shift_TmVar_Ty c S0) (shift_TmVar_Ty c S1)))) := (shift_TmVar__subst_TyVar_0_Ty_comm_ind S1 H0).
    Definition shift_TyVar_Tm_subst_TmVar_Tm0_comm (s0 : Tm) : (forall (c : (Cutoff TyVar)) (s : Tm) ,
      ((shift_TyVar_Tm c (subst_TmVar_Tm X0 s s0)) = (subst_TmVar_Tm X0 (shift_TyVar_Tm c s) (shift_TyVar_Tm c s0)))) := (shift_TyVar__subst_TmVar_0_Tm_comm_ind s0 H0).
    Definition shift_TyVar_Ty_subst_TmVar_Ty0_comm (S0 : Ty) : (forall (c : (Cutoff TyVar)) (s : Tm) ,
      ((shift_TyVar_Ty c (subst_TmVar_Ty X0 s S0)) = (subst_TmVar_Ty X0 (shift_TyVar_Tm c s) (shift_TyVar_Ty c S0)))) := (shift_TyVar__subst_TmVar_0_Ty_comm_ind S0 H0).
    Definition shift_TyVar_Tm_subst_TyVar_Tm0_comm (s : Tm) : (forall (c : (Cutoff TyVar)) (S0 : Ty) ,
      ((shift_TyVar_Tm c (subst_TyVar_Tm X0 S0 s)) = (subst_TyVar_Tm X0 (shift_TyVar_Ty c S0) (shift_TyVar_Tm (CS c) s)))) := (shift_TyVar__subst_TyVar_0_Tm_comm_ind s H0).
    Definition shift_TyVar_Ty_subst_TyVar_Ty0_comm (S1 : Ty) : (forall (c : (Cutoff TyVar)) (S0 : Ty) ,
      ((shift_TyVar_Ty c (subst_TyVar_Ty X0 S0 S1)) = (subst_TyVar_Ty X0 (shift_TyVar_Ty c S0) (shift_TyVar_Ty (CS c) S1)))) := (shift_TyVar__subst_TyVar_0_Ty_comm_ind S1 H0).
    Definition shift_TmVar_Kind_subst_TmVar_Kind0_comm (K1 : Kind) : (forall (c : (Cutoff TmVar)) (s : Tm) ,
      ((shift_TmVar_Kind c (subst_TmVar_Kind X0 s K1)) = (subst_TmVar_Kind X0 (shift_TmVar_Tm c s) (shift_TmVar_Kind (CS c) K1)))) := (shift_TmVar__subst_TmVar_0_Kind_comm_ind K1 H0).
    Definition shift_TmVar_Kind_subst_TyVar_Kind0_comm (K1 : Kind) : (forall (c : (Cutoff TmVar)) (S0 : Ty) ,
      ((shift_TmVar_Kind c (subst_TyVar_Kind X0 S0 K1)) = (subst_TyVar_Kind X0 (shift_TmVar_Ty c S0) (shift_TmVar_Kind c K1)))) := (shift_TmVar__subst_TyVar_0_Kind_comm_ind K1 H0).
    Definition shift_TyVar_Kind_subst_TmVar_Kind0_comm (K1 : Kind) : (forall (c : (Cutoff TyVar)) (s : Tm) ,
      ((shift_TyVar_Kind c (subst_TmVar_Kind X0 s K1)) = (subst_TmVar_Kind X0 (shift_TyVar_Tm c s) (shift_TyVar_Kind c K1)))) := (shift_TyVar__subst_TmVar_0_Kind_comm_ind K1 H0).
    Definition shift_TyVar_Kind_subst_TyVar_Kind0_comm (K1 : Kind) : (forall (c : (Cutoff TyVar)) (S0 : Ty) ,
      ((shift_TyVar_Kind c (subst_TyVar_Kind X0 S0 K1)) = (subst_TyVar_Kind X0 (shift_TyVar_Ty c S0) (shift_TyVar_Kind (CS c) K1)))) := (shift_TyVar__subst_TyVar_0_Kind_comm_ind K1 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma subst_TmVar_Index_shift_TmVar_Tm0_comm_ind (d : (Trace TmVar)) (s : Tm) :
      (forall (k : Hvl) (x7 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TmVar d) k) s (shift_TmVar_Index (weakenCutoffTmVar C0 k) x7)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Index (weakenTrace d k) s x7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Index_shift_TyVar_Tm0_comm_ind (d : (Trace TmVar)) (s : Tm) :
      (forall (k : Hvl) (x7 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TyVar d) k) s x7) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Index (weakenTrace d k) s x7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Index_shift_TmVar_Ty0_comm_ind (d : (Trace TyVar)) (S0 : Ty) :
      (forall (k : Hvl) (X3 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace (XS TmVar d) k) S0 X3) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TyVar_Index (weakenTrace d k) S0 X3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Index_shift_TyVar_Ty0_comm_ind (d : (Trace TyVar)) (S0 : Ty) :
      (forall (k : Hvl) (X3 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace (XS TyVar d) k) S0 (shift_TyVar_Index (weakenCutoffTyVar C0 k) X3)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Index (weakenTrace d k) S0 X3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_TmVar__shift_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) {struct s0} :
    ((subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) :=
      match s0 return ((subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) with
        | (Var x7) => (subst_TmVar_Index_shift_TmVar_Tm0_comm_ind d s k x7)
        | (Abs T5 t3) => (f_equal2 Abs (subst_TmVar__shift_TmVar_0_Ty_comm_ind T5 k d s) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind t3 (HS TmVar k) d s) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t4 t5) => (f_equal2 App (subst_TmVar__shift_TmVar_0_Tm_comm_ind t4 k d s) (subst_TmVar__shift_TmVar_0_Tm_comm_ind t5 k d s))
      end
    with subst_TmVar__shift_TmVar_0_Ty_comm_ind (S0 : Ty) (k : Hvl) (d : (Trace TmVar)) (s : Tm) {struct S0} :
    ((subst_TmVar_Ty (weakenTrace (XS TmVar d) k) s (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S0)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TmVar_Ty (weakenTrace d k) s S0))) :=
      match S0 return ((subst_TmVar_Ty (weakenTrace (XS TmVar d) k) s (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S0)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TmVar_Ty (weakenTrace d k) s S0))) with
        | (TVar X3) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (subst_TmVar__shift_TmVar_0_Ty_comm_ind T7 k d s) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Ty_comm_ind T8 (HS TmVar k) d s) (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t6) => (f_equal2 TApp (subst_TmVar__shift_TmVar_0_Ty_comm_ind T6 k d s) (subst_TmVar__shift_TmVar_0_Tm_comm_ind t6 k d s))
      end.
    Fixpoint subst_TmVar__shift_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) {struct s0} :
    ((subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) :=
      match s0 return ((subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s s0))) with
        | (Var x7) => (subst_TmVar_Index_shift_TyVar_Tm0_comm_ind d s k x7)
        | (Abs T5 t3) => (f_equal2 Abs (subst_TmVar__shift_TyVar_0_Ty_comm_ind T5 k d s) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Tm_comm_ind t3 (HS TmVar k) d s) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t4 t5) => (f_equal2 App (subst_TmVar__shift_TyVar_0_Tm_comm_ind t4 k d s) (subst_TmVar__shift_TyVar_0_Tm_comm_ind t5 k d s))
      end
    with subst_TmVar__shift_TyVar_0_Ty_comm_ind (S0 : Ty) (k : Hvl) (d : (Trace TmVar)) (s : Tm) {struct S0} :
    ((subst_TmVar_Ty (weakenTrace (XS TyVar d) k) s (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S0)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TmVar_Ty (weakenTrace d k) s S0))) :=
      match S0 return ((subst_TmVar_Ty (weakenTrace (XS TyVar d) k) s (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S0)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TmVar_Ty (weakenTrace d k) s S0))) with
        | (TVar X3) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (subst_TmVar__shift_TyVar_0_Ty_comm_ind T7 k d s) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Ty_comm_ind T8 (HS TmVar k) d s) (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t6) => (f_equal2 TApp (subst_TmVar__shift_TyVar_0_Ty_comm_ind T6 k d s) (subst_TmVar__shift_TyVar_0_Tm_comm_ind t6 k d s))
      end.
    Fixpoint subst_TyVar__shift_TmVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct s} :
    ((subst_TyVar_Tm (weakenTrace (XS TmVar d) k) S0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S0 s))) :=
      match s return ((subst_TyVar_Tm (weakenTrace (XS TmVar d) k) S0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S0 s))) with
        | (Var x7) => eq_refl
        | (Abs T5 t3) => (f_equal2 Abs (subst_TyVar__shift_TmVar_0_Ty_comm_ind T5 k d S0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Tm_comm_ind t3 (HS TmVar k) d S0) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t4 t5) => (f_equal2 App (subst_TyVar__shift_TmVar_0_Tm_comm_ind t4 k d S0) (subst_TyVar__shift_TmVar_0_Tm_comm_ind t5 k d S0))
      end
    with subst_TyVar__shift_TmVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct S1} :
    ((subst_TyVar_Ty (weakenTrace (XS TmVar d) k) S0 (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S1)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TyVar_Ty (weakenTrace d k) S0 S1))) :=
      match S1 return ((subst_TyVar_Ty (weakenTrace (XS TmVar d) k) S0 (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S1)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TyVar_Ty (weakenTrace d k) S0 S1))) with
        | (TVar X3) => (subst_TyVar_Index_shift_TmVar_Ty0_comm_ind d S0 k X3)
        | (TPi T7 T8) => (f_equal2 TPi (subst_TyVar__shift_TmVar_0_Ty_comm_ind T7 k d S0) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Ty_comm_ind T8 (HS TmVar k) d S0) (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t6) => (f_equal2 TApp (subst_TyVar__shift_TmVar_0_Ty_comm_ind T6 k d S0) (subst_TyVar__shift_TmVar_0_Tm_comm_ind t6 k d S0))
      end.
    Fixpoint subst_TyVar__shift_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct s} :
    ((subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S0 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S0 s))) :=
      match s return ((subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S0 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S0 s))) with
        | (Var x7) => eq_refl
        | (Abs T5 t3) => (f_equal2 Abs (subst_TyVar__shift_TyVar_0_Ty_comm_ind T5 k d S0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Tm_comm_ind t3 (HS TmVar k) d S0) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t4 t5) => (f_equal2 App (subst_TyVar__shift_TyVar_0_Tm_comm_ind t4 k d S0) (subst_TyVar__shift_TyVar_0_Tm_comm_ind t5 k d S0))
      end
    with subst_TyVar__shift_TyVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct S1} :
    ((subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S0 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Ty (weakenTrace d k) S0 S1))) :=
      match S1 return ((subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S0 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Ty (weakenTrace d k) S0 S1))) with
        | (TVar X3) => (subst_TyVar_Index_shift_TyVar_Ty0_comm_ind d S0 k X3)
        | (TPi T7 T8) => (f_equal2 TPi (subst_TyVar__shift_TyVar_0_Ty_comm_ind T7 k d S0) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Ty_comm_ind T8 (HS TmVar k) d S0) (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t6) => (f_equal2 TApp (subst_TyVar__shift_TyVar_0_Ty_comm_ind T6 k d S0) (subst_TyVar__shift_TyVar_0_Tm_comm_ind t6 k d S0))
      end.
    Fixpoint subst_TmVar__shift_TmVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (d : (Trace TmVar)) (s : Tm) {struct K1} :
    ((subst_TmVar_Kind (weakenTrace (XS TmVar d) k) s (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K1)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (subst_TmVar_Kind (weakenTrace d k) s K1))) :=
      match K1 return ((subst_TmVar_Kind (weakenTrace (XS TmVar d) k) s (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K1)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (subst_TmVar_Kind (weakenTrace d k) s K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (subst_TmVar__shift_TmVar_0_Ty_comm_ind T5 k d s) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Kind_comm_ind K2 (HS TmVar k) d s) (f_equal2 shift_TmVar_Kind eq_refl (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__shift_TyVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (d : (Trace TmVar)) (s : Tm) {struct K1} :
    ((subst_TmVar_Kind (weakenTrace (XS TyVar d) k) s (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K1)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (subst_TmVar_Kind (weakenTrace d k) s K1))) :=
      match K1 return ((subst_TmVar_Kind (weakenTrace (XS TyVar d) k) s (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K1)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (subst_TmVar_Kind (weakenTrace d k) s K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (subst_TmVar__shift_TyVar_0_Ty_comm_ind T5 k d s) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Kind_comm_ind K2 (HS TmVar k) d s) (f_equal2 shift_TyVar_Kind eq_refl (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__shift_TmVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct K1} :
    ((subst_TyVar_Kind (weakenTrace (XS TmVar d) k) S0 (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K1)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (subst_TyVar_Kind (weakenTrace d k) S0 K1))) :=
      match K1 return ((subst_TyVar_Kind (weakenTrace (XS TmVar d) k) S0 (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K1)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (subst_TyVar_Kind (weakenTrace d k) S0 K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (subst_TyVar__shift_TmVar_0_Ty_comm_ind T5 k d S0) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Kind_comm_ind K2 (HS TmVar k) d S0) (f_equal2 shift_TmVar_Kind eq_refl (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__shift_TyVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) {struct K1} :
    ((subst_TyVar_Kind (weakenTrace (XS TyVar d) k) S0 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K1)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (subst_TyVar_Kind (weakenTrace d k) S0 K1))) :=
      match K1 return ((subst_TyVar_Kind (weakenTrace (XS TyVar d) k) S0 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K1)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (subst_TyVar_Kind (weakenTrace d k) S0 K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (subst_TyVar__shift_TyVar_0_Ty_comm_ind T5 k d S0) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Kind_comm_ind K2 (HS TmVar k) d S0) (f_equal2 shift_TyVar_Kind eq_refl (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition subst_TmVar_Tm_shift_TmVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) ,
      ((subst_TmVar_Tm (XS TmVar d) s (shift_TmVar_Tm C0 s0)) = (shift_TmVar_Tm C0 (subst_TmVar_Tm d s s0)))) := (subst_TmVar__shift_TmVar_0_Tm_comm_ind s0 H0).
    Definition subst_TmVar_Ty_shift_TmVar_Ty0_comm (S0 : Ty) : (forall (d : (Trace TmVar)) (s : Tm) ,
      ((subst_TmVar_Ty (XS TmVar d) s (shift_TmVar_Ty C0 S0)) = (shift_TmVar_Ty C0 (subst_TmVar_Ty d s S0)))) := (subst_TmVar__shift_TmVar_0_Ty_comm_ind S0 H0).
    Definition subst_TmVar_Tm_shift_TyVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) ,
      ((subst_TmVar_Tm (XS TyVar d) s (shift_TyVar_Tm C0 s0)) = (shift_TyVar_Tm C0 (subst_TmVar_Tm d s s0)))) := (subst_TmVar__shift_TyVar_0_Tm_comm_ind s0 H0).
    Definition subst_TmVar_Ty_shift_TyVar_Ty0_comm (S0 : Ty) : (forall (d : (Trace TmVar)) (s : Tm) ,
      ((subst_TmVar_Ty (XS TyVar d) s (shift_TyVar_Ty C0 S0)) = (shift_TyVar_Ty C0 (subst_TmVar_Ty d s S0)))) := (subst_TmVar__shift_TyVar_0_Ty_comm_ind S0 H0).
    Definition subst_TyVar_Tm_shift_TmVar_Tm0_comm (s : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Tm (XS TmVar d) S0 (shift_TmVar_Tm C0 s)) = (shift_TmVar_Tm C0 (subst_TyVar_Tm d S0 s)))) := (subst_TyVar__shift_TmVar_0_Tm_comm_ind s H0).
    Definition subst_TyVar_Ty_shift_TmVar_Ty0_comm (S1 : Ty) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Ty (XS TmVar d) S0 (shift_TmVar_Ty C0 S1)) = (shift_TmVar_Ty C0 (subst_TyVar_Ty d S0 S1)))) := (subst_TyVar__shift_TmVar_0_Ty_comm_ind S1 H0).
    Definition subst_TyVar_Tm_shift_TyVar_Tm0_comm (s : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Tm (XS TyVar d) S0 (shift_TyVar_Tm C0 s)) = (shift_TyVar_Tm C0 (subst_TyVar_Tm d S0 s)))) := (subst_TyVar__shift_TyVar_0_Tm_comm_ind s H0).
    Definition subst_TyVar_Ty_shift_TyVar_Ty0_comm (S1 : Ty) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Ty (XS TyVar d) S0 (shift_TyVar_Ty C0 S1)) = (shift_TyVar_Ty C0 (subst_TyVar_Ty d S0 S1)))) := (subst_TyVar__shift_TyVar_0_Ty_comm_ind S1 H0).
    Definition subst_TmVar_Kind_shift_TmVar_Kind0_comm (K1 : Kind) : (forall (d : (Trace TmVar)) (s : Tm) ,
      ((subst_TmVar_Kind (XS TmVar d) s (shift_TmVar_Kind C0 K1)) = (shift_TmVar_Kind C0 (subst_TmVar_Kind d s K1)))) := (subst_TmVar__shift_TmVar_0_Kind_comm_ind K1 H0).
    Definition subst_TmVar_Kind_shift_TyVar_Kind0_comm (K1 : Kind) : (forall (d : (Trace TmVar)) (s : Tm) ,
      ((subst_TmVar_Kind (XS TyVar d) s (shift_TyVar_Kind C0 K1)) = (shift_TyVar_Kind C0 (subst_TmVar_Kind d s K1)))) := (subst_TmVar__shift_TyVar_0_Kind_comm_ind K1 H0).
    Definition subst_TyVar_Kind_shift_TmVar_Kind0_comm (K1 : Kind) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Kind (XS TmVar d) S0 (shift_TmVar_Kind C0 K1)) = (shift_TmVar_Kind C0 (subst_TyVar_Kind d S0 K1)))) := (subst_TyVar__shift_TmVar_0_Kind_comm_ind K1 H0).
    Definition subst_TyVar_Kind_shift_TyVar_Kind0_comm (K1 : Kind) : (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((subst_TyVar_Kind (XS TyVar d) S0 (shift_TyVar_Kind C0 K1)) = (shift_TyVar_Kind C0 (subst_TyVar_Kind d S0 K1)))) := (subst_TyVar__shift_TyVar_0_Kind_comm_ind K1 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    
  End SubstSubordInd.
  Section SubstSubord.
    
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite subst_TmVar_Kind0_shift_TmVar_Kind0_reflection subst_TyVar_Kind0_shift_TyVar_Kind0_reflection subst_TmVar_Tm0_shift_TmVar_Tm0_reflection subst_TyVar_Tm0_shift_TyVar_Tm0_reflection subst_TmVar_Ty0_shift_TmVar_Ty0_reflection subst_TyVar_Ty0_shift_TyVar_Ty0_reflection : interaction.
 Hint Rewrite subst_TmVar_Kind0_shift_TmVar_Kind0_reflection subst_TyVar_Kind0_shift_TyVar_Kind0_reflection subst_TmVar_Tm0_shift_TmVar_Tm0_reflection subst_TyVar_Tm0_shift_TyVar_Tm0_reflection subst_TmVar_Ty0_shift_TmVar_Ty0_reflection subst_TyVar_Ty0_shift_TyVar_Ty0_reflection : reflection.
 Hint Rewrite subst_TmVar_Kind_shift_TmVar_Kind0_comm subst_TmVar_Kind_shift_TyVar_Kind0_comm subst_TyVar_Kind_shift_TmVar_Kind0_comm subst_TyVar_Kind_shift_TyVar_Kind0_comm subst_TmVar_Tm_shift_TmVar_Tm0_comm subst_TmVar_Tm_shift_TyVar_Tm0_comm subst_TyVar_Tm_shift_TmVar_Tm0_comm subst_TyVar_Tm_shift_TyVar_Tm0_comm subst_TmVar_Ty_shift_TmVar_Ty0_comm subst_TmVar_Ty_shift_TyVar_Ty0_comm subst_TyVar_Ty_shift_TmVar_Ty0_comm subst_TyVar_Ty_shift_TyVar_Ty0_comm : interaction.
 Hint Rewrite subst_TmVar_Kind_shift_TmVar_Kind0_comm subst_TmVar_Kind_shift_TyVar_Kind0_comm subst_TyVar_Kind_shift_TmVar_Kind0_comm subst_TyVar_Kind_shift_TyVar_Kind0_comm subst_TmVar_Tm_shift_TmVar_Tm0_comm subst_TmVar_Tm_shift_TyVar_Tm0_comm subst_TyVar_Tm_shift_TmVar_Tm0_comm subst_TyVar_Tm_shift_TyVar_Tm0_comm subst_TmVar_Ty_shift_TmVar_Ty0_comm subst_TmVar_Ty_shift_TyVar_Ty0_comm subst_TyVar_Ty_shift_TmVar_Ty0_comm subst_TyVar_Ty_shift_TyVar_Ty0_comm : subst_shift0.
 Hint Rewrite shift_TmVar_Kind_subst_TmVar_Kind0_comm shift_TmVar_Kind_subst_TyVar_Kind0_comm shift_TyVar_Kind_subst_TmVar_Kind0_comm shift_TyVar_Kind_subst_TyVar_Kind0_comm shift_TmVar_Tm_subst_TmVar_Tm0_comm shift_TmVar_Tm_subst_TyVar_Tm0_comm shift_TyVar_Tm_subst_TmVar_Tm0_comm shift_TyVar_Tm_subst_TyVar_Tm0_comm shift_TmVar_Ty_subst_TmVar_Ty0_comm shift_TmVar_Ty_subst_TyVar_Ty0_comm shift_TyVar_Ty_subst_TmVar_Ty0_comm shift_TyVar_Ty_subst_TyVar_Ty0_comm : interaction.
 Hint Rewrite shift_TmVar_Kind_subst_TmVar_Kind0_comm shift_TmVar_Kind_subst_TyVar_Kind0_comm shift_TyVar_Kind_subst_TmVar_Kind0_comm shift_TyVar_Kind_subst_TyVar_Kind0_comm shift_TmVar_Tm_subst_TmVar_Tm0_comm shift_TmVar_Tm_subst_TyVar_Tm0_comm shift_TyVar_Tm_subst_TmVar_Tm0_comm shift_TyVar_Tm_subst_TyVar_Tm0_comm shift_TmVar_Ty_subst_TmVar_Ty0_comm shift_TmVar_Ty_subst_TyVar_Ty0_comm shift_TyVar_Ty_subst_TmVar_Ty0_comm shift_TyVar_Ty_subst_TyVar_Ty0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma subst_TmVar_Tm_subst_TmVar_Index0_commright_ind (d : (Trace TmVar)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (x7 : (Index TmVar)) ,
        ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Index (weakenTrace X0 k) s0 x7)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Index (weakenTrace (XS TmVar d) k) s x7)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Tm_subst_TmVar_Index0_commright_ind (d : (Trace TyVar)) (S0 : Ty) (s : Tm) :
      (forall (k : Hvl) (x7 : (Index TmVar)) ,
        ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TmVar_Index (weakenTrace X0 k) s x7)) = (subst_TmVar_Index (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) x7))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Ty_subst_TyVar_Index0_commright_ind (d : (Trace TmVar)) (s : Tm) (S0 : Ty) :
      (forall (k : Hvl) (X3 : (Index TyVar)) ,
        ((subst_TmVar_Ty (weakenTrace d k) s (subst_TyVar_Index (weakenTrace X0 k) S0 X3)) = (subst_TyVar_Index (weakenTrace X0 k) (subst_TmVar_Ty d s S0) X3))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Ty_subst_TyVar_Index0_commright_ind (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) :
      (forall (k : Hvl) (X3 : (Index TyVar)) ,
        ((subst_TyVar_Ty (weakenTrace d k) S0 (subst_TyVar_Index (weakenTrace X0 k) S1 X3)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Index (weakenTrace (XS TyVar d) k) S0 X3)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Ty_subst_TyVar_Index0_commleft_ind (d : (Trace TmVar)) (s : Tm) (S0 : Ty) :
      (forall (k : Hvl) (x7 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace d k) s x7) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TmVar_Ty d s S0) (subst_TmVar_Index (weakenTrace (XS TyVar d) k) s x7)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Tm_subst_TmVar_Index0_commleft_ind (d : (Trace TyVar)) (S0 : Ty) (s : Tm) :
      (forall (k : Hvl) (X3 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace d k) S0 X3) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) (subst_TyVar_Index (weakenTrace (XS TmVar d) k) S0 X3)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_TmVar__subst_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s1} :
    ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s s1))) :=
      match s1 return ((subst_TmVar_Tm (weakenTrace d k) s (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s s1))) with
        | (Var x7) => (subst_TmVar_Tm_subst_TmVar_Index0_commright_ind d s s0 k x7)
        | (Abs T5 t3) => (f_equal2 Abs (subst_TmVar__subst_TmVar_0_Ty_comm_ind T5 k d s s0) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t3 (HS TmVar k) d s s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t4 t5) => (f_equal2 App (subst_TmVar__subst_TmVar_0_Tm_comm_ind t4 k d s s0) (subst_TmVar__subst_TmVar_0_Tm_comm_ind t5 k d s s0))
      end
    with subst_TmVar__subst_TmVar_0_Ty_comm_ind (S0 : Ty) (k : Hvl) (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct S0} :
    ((subst_TmVar_Ty (weakenTrace d k) s (subst_TmVar_Ty (weakenTrace X0 k) s0 S0)) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Ty (weakenTrace (XS TmVar d) k) s S0))) :=
      match S0 return ((subst_TmVar_Ty (weakenTrace d k) s (subst_TmVar_Ty (weakenTrace X0 k) s0 S0)) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Ty (weakenTrace (XS TmVar d) k) s S0))) with
        | (TVar X3) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (subst_TmVar__subst_TmVar_0_Ty_comm_ind T7 k d s s0) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Ty_comm_ind T8 (HS TmVar k) d s s0) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t6) => (f_equal2 TApp (subst_TmVar__subst_TmVar_0_Ty_comm_ind T6 k d s s0) (subst_TmVar__subst_TmVar_0_Tm_comm_ind t6 k d s s0))
      end.
    Fixpoint subst_TmVar__subst_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TmVar)) (s : Tm) (S0 : Ty) {struct s0} :
    ((subst_TmVar_Tm (weakenTrace d k) s (subst_TyVar_Tm (weakenTrace X0 k) S0 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TmVar_Ty d s S0) (subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s s0))) :=
      match s0 return ((subst_TmVar_Tm (weakenTrace d k) s (subst_TyVar_Tm (weakenTrace X0 k) S0 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TmVar_Ty d s S0) (subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s s0))) with
        | (Var x7) => (subst_TmVar_Ty_subst_TyVar_Index0_commleft_ind d s S0 k x7)
        | (Abs T5 t3) => (f_equal2 Abs (subst_TmVar__subst_TyVar_0_Ty_comm_ind T5 k d s S0) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Tm_comm_ind t3 (HS TmVar k) d s S0) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t4 t5) => (f_equal2 App (subst_TmVar__subst_TyVar_0_Tm_comm_ind t4 k d s S0) (subst_TmVar__subst_TyVar_0_Tm_comm_ind t5 k d s S0))
      end
    with subst_TmVar__subst_TyVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (d : (Trace TmVar)) (s : Tm) (S0 : Ty) {struct S1} :
    ((subst_TmVar_Ty (weakenTrace d k) s (subst_TyVar_Ty (weakenTrace X0 k) S0 S1)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TmVar_Ty d s S0) (subst_TmVar_Ty (weakenTrace (XS TyVar d) k) s S1))) :=
      match S1 return ((subst_TmVar_Ty (weakenTrace d k) s (subst_TyVar_Ty (weakenTrace X0 k) S0 S1)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TmVar_Ty d s S0) (subst_TmVar_Ty (weakenTrace (XS TyVar d) k) s S1))) with
        | (TVar X3) => (subst_TmVar_Ty_subst_TyVar_Index0_commright_ind d s S0 k X3)
        | (TPi T7 T8) => (f_equal2 TPi (subst_TmVar__subst_TyVar_0_Ty_comm_ind T7 k d s S0) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Ty_comm_ind T8 (HS TmVar k) d s S0) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t6) => (f_equal2 TApp (subst_TmVar__subst_TyVar_0_Ty_comm_ind T6 k d s S0) (subst_TmVar__subst_TyVar_0_Tm_comm_ind t6 k d s S0))
      end.
    Fixpoint subst_TyVar__subst_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (s : Tm) {struct s0} :
    ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) (subst_TyVar_Tm (weakenTrace (XS TmVar d) k) S0 s0))) :=
      match s0 return ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TmVar_Tm (weakenTrace X0 k) s s0)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) (subst_TyVar_Tm (weakenTrace (XS TmVar d) k) S0 s0))) with
        | (Var x7) => (subst_TyVar_Tm_subst_TmVar_Index0_commright_ind d S0 s k x7)
        | (Abs T5 t3) => (f_equal2 Abs (subst_TyVar__subst_TmVar_0_Ty_comm_ind T5 k d S0 s) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Tm_comm_ind t3 (HS TmVar k) d S0 s) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t4 t5) => (f_equal2 App (subst_TyVar__subst_TmVar_0_Tm_comm_ind t4 k d S0 s) (subst_TyVar__subst_TmVar_0_Tm_comm_ind t5 k d S0 s))
      end
    with subst_TyVar__subst_TmVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (s : Tm) {struct S1} :
    ((subst_TyVar_Ty (weakenTrace d k) S0 (subst_TmVar_Ty (weakenTrace X0 k) s S1)) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) (subst_TyVar_Ty (weakenTrace (XS TmVar d) k) S0 S1))) :=
      match S1 return ((subst_TyVar_Ty (weakenTrace d k) S0 (subst_TmVar_Ty (weakenTrace X0 k) s S1)) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) (subst_TyVar_Ty (weakenTrace (XS TmVar d) k) S0 S1))) with
        | (TVar X3) => (subst_TyVar_Tm_subst_TmVar_Index0_commleft_ind d S0 s k X3)
        | (TPi T7 T8) => (f_equal2 TPi (subst_TyVar__subst_TmVar_0_Ty_comm_ind T7 k d S0 s) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Ty_comm_ind T8 (HS TmVar k) d S0 s) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t6) => (f_equal2 TApp (subst_TyVar__subst_TmVar_0_Ty_comm_ind T6 k d S0 s) (subst_TyVar__subst_TmVar_0_Tm_comm_ind t6 k d S0 s))
      end.
    Fixpoint subst_TyVar__subst_TyVar_0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) {struct s} :
    ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TyVar_Tm (weakenTrace X0 k) S1 s)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S0 s))) :=
      match s return ((subst_TyVar_Tm (weakenTrace d k) S0 (subst_TyVar_Tm (weakenTrace X0 k) S1 s)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S0 s))) with
        | (Var x7) => eq_refl
        | (Abs T5 t3) => (f_equal2 Abs (subst_TyVar__subst_TyVar_0_Ty_comm_ind T5 k d S0 S1) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Tm_comm_ind t3 (HS TmVar k) d S0 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t4 t5) => (f_equal2 App (subst_TyVar__subst_TyVar_0_Tm_comm_ind t4 k d S0 S1) (subst_TyVar__subst_TyVar_0_Tm_comm_ind t5 k d S0 S1))
      end
    with subst_TyVar__subst_TyVar_0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) {struct S2} :
    ((subst_TyVar_Ty (weakenTrace d k) S0 (subst_TyVar_Ty (weakenTrace X0 k) S1 S2)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S0 S2))) :=
      match S2 return ((subst_TyVar_Ty (weakenTrace d k) S0 (subst_TyVar_Ty (weakenTrace X0 k) S1 S2)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S0 S2))) with
        | (TVar X3) => (subst_TyVar_Ty_subst_TyVar_Index0_commright_ind d S0 S1 k X3)
        | (TPi T7 T8) => (f_equal2 TPi (subst_TyVar__subst_TyVar_0_Ty_comm_ind T7 k d S0 S1) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Ty_comm_ind T8 (HS TmVar k) d S0 S1) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t6) => (f_equal2 TApp (subst_TyVar__subst_TyVar_0_Ty_comm_ind T6 k d S0 S1) (subst_TyVar__subst_TyVar_0_Tm_comm_ind t6 k d S0 S1))
      end.
    Fixpoint subst_TmVar__subst_TmVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct K1} :
    ((subst_TmVar_Kind (weakenTrace d k) s (subst_TmVar_Kind (weakenTrace X0 k) s0 K1)) = (subst_TmVar_Kind (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Kind (weakenTrace (XS TmVar d) k) s K1))) :=
      match K1 return ((subst_TmVar_Kind (weakenTrace d k) s (subst_TmVar_Kind (weakenTrace X0 k) s0 K1)) = (subst_TmVar_Kind (weakenTrace X0 k) (subst_TmVar_Tm d s s0) (subst_TmVar_Kind (weakenTrace (XS TmVar d) k) s K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (subst_TmVar__subst_TmVar_0_Ty_comm_ind T5 k d s s0) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Kind_comm_ind K2 (HS TmVar k) d s s0) (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__subst_TyVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (d : (Trace TmVar)) (s : Tm) (S0 : Ty) {struct K1} :
    ((subst_TmVar_Kind (weakenTrace d k) s (subst_TyVar_Kind (weakenTrace X0 k) S0 K1)) = (subst_TyVar_Kind (weakenTrace X0 k) (subst_TmVar_Ty d s S0) (subst_TmVar_Kind (weakenTrace (XS TyVar d) k) s K1))) :=
      match K1 return ((subst_TmVar_Kind (weakenTrace d k) s (subst_TyVar_Kind (weakenTrace X0 k) S0 K1)) = (subst_TyVar_Kind (weakenTrace X0 k) (subst_TmVar_Ty d s S0) (subst_TmVar_Kind (weakenTrace (XS TyVar d) k) s K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (subst_TmVar__subst_TyVar_0_Ty_comm_ind T5 k d s S0) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Kind_comm_ind K2 (HS TmVar k) d s S0) (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__subst_TmVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (s : Tm) {struct K1} :
    ((subst_TyVar_Kind (weakenTrace d k) S0 (subst_TmVar_Kind (weakenTrace X0 k) s K1)) = (subst_TmVar_Kind (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) (subst_TyVar_Kind (weakenTrace (XS TmVar d) k) S0 K1))) :=
      match K1 return ((subst_TyVar_Kind (weakenTrace d k) S0 (subst_TmVar_Kind (weakenTrace X0 k) s K1)) = (subst_TmVar_Kind (weakenTrace X0 k) (subst_TyVar_Tm d S0 s) (subst_TyVar_Kind (weakenTrace (XS TmVar d) k) S0 K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (subst_TyVar__subst_TmVar_0_Ty_comm_ind T5 k d S0 s) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Kind_comm_ind K2 (HS TmVar k) d S0 s) (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__subst_TyVar_0_Kind_comm_ind (K1 : Kind) (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) {struct K1} :
    ((subst_TyVar_Kind (weakenTrace d k) S0 (subst_TyVar_Kind (weakenTrace X0 k) S1 K1)) = (subst_TyVar_Kind (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Kind (weakenTrace (XS TyVar d) k) S0 K1))) :=
      match K1 return ((subst_TyVar_Kind (weakenTrace d k) S0 (subst_TyVar_Kind (weakenTrace X0 k) S1 K1)) = (subst_TyVar_Kind (weakenTrace X0 k) (subst_TyVar_Ty d S0 S1) (subst_TyVar_Kind (weakenTrace (XS TyVar d) k) S0 K1))) with
        | (Star) => eq_refl
        | (KPi T5 K2) => (f_equal2 KPi (subst_TyVar__subst_TyVar_0_Ty_comm_ind T5 k d S0 S1) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Kind_comm_ind K2 (HS TmVar k) d S0 S1) (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition subst_TmVar_Tm_subst_TmVar_Tm0_comm (s1 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) (s0 : Tm) ,
      ((subst_TmVar_Tm d s (subst_TmVar_Tm X0 s0 s1)) = (subst_TmVar_Tm X0 (subst_TmVar_Tm d s s0) (subst_TmVar_Tm (XS TmVar d) s s1)))) := (subst_TmVar__subst_TmVar_0_Tm_comm_ind s1 H0).
    Definition subst_TmVar_Ty_subst_TmVar_Ty0_comm (S0 : Ty) : (forall (d : (Trace TmVar)) (s : Tm) (s0 : Tm) ,
      ((subst_TmVar_Ty d s (subst_TmVar_Ty X0 s0 S0)) = (subst_TmVar_Ty X0 (subst_TmVar_Tm d s s0) (subst_TmVar_Ty (XS TmVar d) s S0)))) := (subst_TmVar__subst_TmVar_0_Ty_comm_ind S0 H0).
    Definition subst_TmVar_Tm_subst_TyVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TmVar)) (s : Tm) (S0 : Ty) ,
      ((subst_TmVar_Tm d s (subst_TyVar_Tm X0 S0 s0)) = (subst_TyVar_Tm X0 (subst_TmVar_Ty d s S0) (subst_TmVar_Tm (XS TyVar d) s s0)))) := (subst_TmVar__subst_TyVar_0_Tm_comm_ind s0 H0).
    Definition subst_TmVar_Ty_subst_TyVar_Ty0_comm (S1 : Ty) : (forall (d : (Trace TmVar)) (s : Tm) (S0 : Ty) ,
      ((subst_TmVar_Ty d s (subst_TyVar_Ty X0 S0 S1)) = (subst_TyVar_Ty X0 (subst_TmVar_Ty d s S0) (subst_TmVar_Ty (XS TyVar d) s S1)))) := (subst_TmVar__subst_TyVar_0_Ty_comm_ind S1 H0).
    Definition subst_TyVar_Tm_subst_TmVar_Tm0_comm (s0 : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) (s : Tm) ,
      ((subst_TyVar_Tm d S0 (subst_TmVar_Tm X0 s s0)) = (subst_TmVar_Tm X0 (subst_TyVar_Tm d S0 s) (subst_TyVar_Tm (XS TmVar d) S0 s0)))) := (subst_TyVar__subst_TmVar_0_Tm_comm_ind s0 H0).
    Definition subst_TyVar_Ty_subst_TmVar_Ty0_comm (S1 : Ty) : (forall (d : (Trace TyVar)) (S0 : Ty) (s : Tm) ,
      ((subst_TyVar_Ty d S0 (subst_TmVar_Ty X0 s S1)) = (subst_TmVar_Ty X0 (subst_TyVar_Tm d S0 s) (subst_TyVar_Ty (XS TmVar d) S0 S1)))) := (subst_TyVar__subst_TmVar_0_Ty_comm_ind S1 H0).
    Definition subst_TyVar_Tm_subst_TyVar_Tm0_comm (s : Tm) : (forall (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) ,
      ((subst_TyVar_Tm d S0 (subst_TyVar_Tm X0 S1 s)) = (subst_TyVar_Tm X0 (subst_TyVar_Ty d S0 S1) (subst_TyVar_Tm (XS TyVar d) S0 s)))) := (subst_TyVar__subst_TyVar_0_Tm_comm_ind s H0).
    Definition subst_TyVar_Ty_subst_TyVar_Ty0_comm (S2 : Ty) : (forall (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) ,
      ((subst_TyVar_Ty d S0 (subst_TyVar_Ty X0 S1 S2)) = (subst_TyVar_Ty X0 (subst_TyVar_Ty d S0 S1) (subst_TyVar_Ty (XS TyVar d) S0 S2)))) := (subst_TyVar__subst_TyVar_0_Ty_comm_ind S2 H0).
    Definition subst_TmVar_Kind_subst_TmVar_Kind0_comm (K1 : Kind) : (forall (d : (Trace TmVar)) (s : Tm) (s0 : Tm) ,
      ((subst_TmVar_Kind d s (subst_TmVar_Kind X0 s0 K1)) = (subst_TmVar_Kind X0 (subst_TmVar_Tm d s s0) (subst_TmVar_Kind (XS TmVar d) s K1)))) := (subst_TmVar__subst_TmVar_0_Kind_comm_ind K1 H0).
    Definition subst_TmVar_Kind_subst_TyVar_Kind0_comm (K1 : Kind) : (forall (d : (Trace TmVar)) (s : Tm) (S0 : Ty) ,
      ((subst_TmVar_Kind d s (subst_TyVar_Kind X0 S0 K1)) = (subst_TyVar_Kind X0 (subst_TmVar_Ty d s S0) (subst_TmVar_Kind (XS TyVar d) s K1)))) := (subst_TmVar__subst_TyVar_0_Kind_comm_ind K1 H0).
    Definition subst_TyVar_Kind_subst_TmVar_Kind0_comm (K1 : Kind) : (forall (d : (Trace TyVar)) (S0 : Ty) (s : Tm) ,
      ((subst_TyVar_Kind d S0 (subst_TmVar_Kind X0 s K1)) = (subst_TmVar_Kind X0 (subst_TyVar_Tm d S0 s) (subst_TyVar_Kind (XS TmVar d) S0 K1)))) := (subst_TyVar__subst_TmVar_0_Kind_comm_ind K1 H0).
    Definition subst_TyVar_Kind_subst_TyVar_Kind0_comm (K1 : Kind) : (forall (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) ,
      ((subst_TyVar_Kind d S0 (subst_TyVar_Kind X0 S1 K1)) = (subst_TyVar_Kind X0 (subst_TyVar_Ty d S0 S1) (subst_TyVar_Kind (XS TyVar d) S0 K1)))) := (subst_TyVar__subst_TyVar_0_Kind_comm_ind K1 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTm_subst_TmVar_Tm  :
      (forall (k : Hvl) (d : (Trace TmVar)) (s : Tm) (s0 : Tm) ,
        ((weakenTm (subst_TmVar_Tm d s s0) k) = (subst_TmVar_Tm (weakenTrace d k) s (weakenTm s0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTy_subst_TmVar_Ty  :
      (forall (k : Hvl) (d : (Trace TmVar)) (s : Tm) (S0 : Ty) ,
        ((weakenTy (subst_TmVar_Ty d s S0) k) = (subst_TmVar_Ty (weakenTrace d k) s (weakenTy S0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_subst_TyVar_Tm  :
      (forall (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (s : Tm) ,
        ((weakenTm (subst_TyVar_Tm d S0 s) k) = (subst_TyVar_Tm (weakenTrace d k) S0 (weakenTm s k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTy_subst_TyVar_Ty  :
      (forall (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) ,
        ((weakenTy (subst_TyVar_Ty d S0 S1) k) = (subst_TyVar_Ty (weakenTrace d k) S0 (weakenTy S1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenKind_subst_TmVar_Kind  :
      (forall (k : Hvl) (d : (Trace TmVar)) (s : Tm) (K1 : Kind) ,
        ((weakenKind (subst_TmVar_Kind d s K1) k) = (subst_TmVar_Kind (weakenTrace d k) s (weakenKind K1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenKind_subst_TyVar_Kind  :
      (forall (k : Hvl) (d : (Trace TyVar)) (S0 : Ty) (K1 : Kind) ,
        ((weakenKind (subst_TyVar_Kind d S0 K1) k) = (subst_TyVar_Kind (weakenTrace d k) S0 (weakenKind K1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite subst_TmVar_Kind_subst_TmVar_Kind0_comm subst_TyVar_Kind_subst_TyVar_Kind0_comm subst_TmVar_Tm_subst_TmVar_Tm0_comm subst_TyVar_Tm_subst_TyVar_Tm0_comm subst_TmVar_Ty_subst_TmVar_Ty0_comm subst_TyVar_Ty_subst_TyVar_Ty0_comm : interaction.
 Hint Rewrite subst_TmVar_Kind_subst_TmVar_Kind0_comm subst_TyVar_Kind_subst_TyVar_Kind0_comm subst_TmVar_Tm_subst_TmVar_Tm0_comm subst_TyVar_Tm_subst_TyVar_Tm0_comm subst_TmVar_Ty_subst_TmVar_Ty0_comm subst_TyVar_Ty_subst_TyVar_Ty0_comm : subst_subst0.
 Hint Rewrite weakenKind_shift_TmVar_Kind weakenKind_shift_TyVar_Kind weakenTm_shift_TmVar_Tm weakenTm_shift_TyVar_Tm weakenTy_shift_TmVar_Ty weakenTy_shift_TyVar_Ty : weaken_shift.
 Hint Rewrite weakenKind_subst_TmVar_Kind weakenKind_subst_TyVar_Kind weakenTm_subst_TmVar_Tm weakenTm_subst_TyVar_Tm weakenTy_subst_TmVar_Ty weakenTy_subst_TyVar_Ty : weaken_subst.
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
    | wfTm_Var
        (x7 : (Index TmVar))
        (wfi : (wfindex k x7)) :
        (wfTm k (Var x7))
    | wfTm_Abs {T5 : Ty}
        (wf : (wfTy k T5)) {t3 : Tm}
        (wf0 : (wfTm (HS TmVar k) t3)) :
        (wfTm k (Abs T5 t3))
    | wfTm_App {t4 : Tm}
        (wf : (wfTm k t4)) {t5 : Tm}
        (wf0 : (wfTm k t5)) :
        (wfTm k (App t4 t5))
  with wfTy (k : Hvl) : Ty -> Prop :=
    | wfTy_TVar
        (X3 : (Index TyVar))
        (wfi : (wfindex k X3)) :
        (wfTy k (TVar X3))
    | wfTy_TPi {T5 : Ty}
        (wf : (wfTy k T5)) {T6 : Ty}
        (wf0 : (wfTy (HS TmVar k) T6)) :
        (wfTy k (TPi T5 T6))
    | wfTy_TApp {T7 : Ty}
        (wf : (wfTy k T7)) {t3 : Tm}
        (wf0 : (wfTm k t3)) :
        (wfTy k (TApp T7 t3)).
  Inductive wfKind (k : Hvl) : Kind -> Prop :=
    | wfKind_Star :
        (wfKind k (Star))
    | wfKind_KPi {T5 : Ty}
        (wf : (wfTy k T5)) {K1 : Kind}
        (wf0 : (wfKind (HS TmVar k) K1))
        : (wfKind k (KPi T5 K1)).
  Definition inversion_wfTm_Var_1 (k : Hvl) (x : (Index TmVar)) (H15 : (wfTm k (Var x))) : (wfindex k x) := match H15 in (wfTm _ s) return match s return Prop with
    | (Var x) => (wfindex k x)
    | _ => True
  end with
    | (wfTm_Var x H1) => H1
    | _ => I
  end.
  Definition inversion_wfTm_Abs_1 (k0 : Hvl) (T : Ty) (t : Tm) (H16 : (wfTm k0 (Abs T t))) : (wfTy k0 T) := match H16 in (wfTm _ s0) return match s0 return Prop with
    | (Abs T t) => (wfTy k0 T)
    | _ => True
  end with
    | (wfTm_Abs T H2 t H3) => H2
    | _ => I
  end.
  Definition inversion_wfTm_Abs_2 (k0 : Hvl) (T : Ty) (t : Tm) (H16 : (wfTm k0 (Abs T t))) : (wfTm (HS TmVar k0) t) := match H16 in (wfTm _ s0) return match s0 return Prop with
    | (Abs T t) => (wfTm (HS TmVar k0) t)
    | _ => True
  end with
    | (wfTm_Abs T H2 t H3) => H3
    | _ => I
  end.
  Definition inversion_wfTm_App_0 (k1 : Hvl) (t1 : Tm) (t2 : Tm) (H17 : (wfTm k1 (App t1 t2))) : (wfTm k1 t1) := match H17 in (wfTm _ s1) return match s1 return Prop with
    | (App t1 t2) => (wfTm k1 t1)
    | _ => True
  end with
    | (wfTm_App t1 H4 t2 H5) => H4
    | _ => I
  end.
  Definition inversion_wfTm_App_1 (k1 : Hvl) (t1 : Tm) (t2 : Tm) (H17 : (wfTm k1 (App t1 t2))) : (wfTm k1 t2) := match H17 in (wfTm _ s1) return match s1 return Prop with
    | (App t1 t2) => (wfTm k1 t2)
    | _ => True
  end with
    | (wfTm_App t1 H4 t2 H5) => H5
    | _ => I
  end.
  Definition inversion_wfTy_TVar_1 (k2 : Hvl) (X : (Index TyVar)) (H18 : (wfTy k2 (TVar X))) : (wfindex k2 X) := match H18 in (wfTy _ S0) return match S0 return Prop with
    | (TVar X) => (wfindex k2 X)
    | _ => True
  end with
    | (wfTy_TVar X H6) => H6
    | _ => I
  end.
  Definition inversion_wfTy_TPi_1 (k3 : Hvl) (T1 : Ty) (T2 : Ty) (H19 : (wfTy k3 (TPi T1 T2))) : (wfTy k3 T1) := match H19 in (wfTy _ S1) return match S1 return Prop with
    | (TPi T1 T2) => (wfTy k3 T1)
    | _ => True
  end with
    | (wfTy_TPi T1 H7 T2 H8) => H7
    | _ => I
  end.
  Definition inversion_wfTy_TPi_2 (k3 : Hvl) (T1 : Ty) (T2 : Ty) (H19 : (wfTy k3 (TPi T1 T2))) : (wfTy (HS TmVar k3) T2) := match H19 in (wfTy _ S1) return match S1 return Prop with
    | (TPi T1 T2) => (wfTy (HS TmVar k3) T2)
    | _ => True
  end with
    | (wfTy_TPi T1 H7 T2 H8) => H8
    | _ => I
  end.
  Definition inversion_wfTy_TApp_0 (k4 : Hvl) (T : Ty) (t : Tm) (H20 : (wfTy k4 (TApp T t))) : (wfTy k4 T) := match H20 in (wfTy _ S2) return match S2 return Prop with
    | (TApp T t) => (wfTy k4 T)
    | _ => True
  end with
    | (wfTy_TApp T H9 t H10) => H9
    | _ => I
  end.
  Definition inversion_wfTy_TApp_1 (k4 : Hvl) (T : Ty) (t : Tm) (H20 : (wfTy k4 (TApp T t))) : (wfTm k4 t) := match H20 in (wfTy _ S2) return match S2 return Prop with
    | (TApp T t) => (wfTm k4 t)
    | _ => True
  end with
    | (wfTy_TApp T H9 t H10) => H10
    | _ => I
  end.
  Definition inversion_wfKind_KPi_1 (k6 : Hvl) (T : Ty) (K : Kind) (H22 : (wfKind k6 (KPi T K))) : (wfTy k6 T) := match H22 in (wfKind _ K2) return match K2 return Prop with
    | (KPi T K) => (wfTy k6 T)
    | _ => True
  end with
    | (wfKind_KPi T H11 K H12) => H11
    | _ => I
  end.
  Definition inversion_wfKind_KPi_2 (k6 : Hvl) (T : Ty) (K : Kind) (H22 : (wfKind k6 (KPi T K))) : (wfKind (HS TmVar k6) K) := match H22 in (wfKind _ K2) return match K2 return Prop with
    | (KPi T K) => (wfKind (HS TmVar k6) K)
    | _ => True
  end with
    | (wfKind_KPi T H11 K H12) => H12
    | _ => I
  end.
  Scheme ind_wfTm := Induction for wfTm Sort Prop
  with ind_wfTy := Induction for wfTy Sort Prop.
  Combined Scheme ind_wfTm_Ty from ind_wfTm, ind_wfTy.
  Scheme ind_wfKind := Induction for wfKind Sort Prop.
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
  Lemma shift_TmVar__wfindex_TmVar  :
    (forall (c : (Cutoff TmVar)) (k7 : Hvl) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) (x7 : (Index TmVar)) ,
      (wfindex k7 x7) -> (wfindex k8 (shift_TmVar_Index c x7))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TmVar__wfindex_TyVar  :
    (forall (c : (Cutoff TmVar)) (k7 : Hvl) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) (X3 : (Index TyVar)) ,
      (wfindex k7 X3) -> (wfindex k8 X3)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TyVar__wfindex_TmVar  :
    (forall (c : (Cutoff TyVar)) (k7 : Hvl) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) (x7 : (Index TmVar)) ,
      (wfindex k7 x7) -> (wfindex k8 x7)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TyVar__wfindex_TyVar  :
    (forall (c : (Cutoff TyVar)) (k7 : Hvl) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) (X3 : (Index TyVar)) ,
      (wfindex k7 X3) -> (wfindex k8 (shift_TyVar_Index c X3))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_TmVar__wfTm_Ty : (forall (k7 : Hvl) ,
    (forall (s2 : Tm) (wf : (wfTm k7 s2)) ,
      (forall (c : (Cutoff TmVar)) (k8 : Hvl) ,
        (shifthvl_TmVar c k7 k8) -> (wfTm k8 (shift_TmVar_Tm c s2)))) /\
    (forall (S3 : Ty) (wf : (wfTy k7 S3)) ,
      (forall (c : (Cutoff TmVar)) (k8 : Hvl) ,
        (shifthvl_TmVar c k7 k8) -> (wfTy k8 (shift_TmVar_Ty c S3))))) := (ind_wfTm_Ty (fun (k7 : Hvl) (s2 : Tm) (wf : (wfTm k7 s2)) =>
    (forall (c : (Cutoff TmVar)) (k8 : Hvl) ,
      (shifthvl_TmVar c k7 k8) -> (wfTm k8 (shift_TmVar_Tm c s2)))) (fun (k7 : Hvl) (S3 : Ty) (wf : (wfTy k7 S3)) =>
    (forall (c : (Cutoff TmVar)) (k8 : Hvl) ,
      (shifthvl_TmVar c k7 k8) -> (wfTy k8 (shift_TmVar_Ty c S3)))) (fun (k7 : Hvl) (x7 : (Index TmVar)) (wfi : (wfindex k7 x7)) (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
    (wfTm_Var k8 _ (shift_TmVar__wfindex_TmVar c k7 k8 ins x7 wfi))) (fun (k7 : Hvl) (T : Ty) (wf : (wfTy k7 T)) IHT (t : Tm) (wf0 : (wfTm (HS TmVar k7) t)) IHt (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
    (wfTm_Abs k8 (IHT c k8 (weaken_shifthvl_TmVar H0 ins)) (IHt (CS c) (HS TmVar k8) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k7 : Hvl) (t1 : Tm) (wf : (wfTm k7 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k7 t2)) IHt2 (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
    (wfTm_App k8 (IHt1 c k8 (weaken_shifthvl_TmVar H0 ins)) (IHt2 c k8 (weaken_shifthvl_TmVar H0 ins)))) (fun (k7 : Hvl) (X3 : (Index TyVar)) (wfi : (wfindex k7 X3)) (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
    (wfTy_TVar k8 _ (shift_TmVar__wfindex_TyVar c k7 k8 ins X3 wfi))) (fun (k7 : Hvl) (T1 : Ty) (wf : (wfTy k7 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS TmVar k7) T2)) IHT2 (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
    (wfTy_TPi k8 (IHT1 c k8 (weaken_shifthvl_TmVar H0 ins)) (IHT2 (CS c) (HS TmVar k8) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k7 : Hvl) (T : Ty) (wf : (wfTy k7 T)) IHT (t : Tm) (wf0 : (wfTm k7 t)) IHt (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
    (wfTy_TApp k8 (IHT c k8 (weaken_shifthvl_TmVar H0 ins)) (IHt c k8 (weaken_shifthvl_TmVar H0 ins))))).
  Lemma shift_TmVar__wfTm (k7 : Hvl) :
    (forall (s2 : Tm) (wf : (wfTm k7 s2)) ,
      (forall (c : (Cutoff TmVar)) (k8 : Hvl) ,
        (shifthvl_TmVar c k7 k8) -> (wfTm k8 (shift_TmVar_Tm c s2)))).
  Proof.
    pose proof ((shift_TmVar__wfTm_Ty k7)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_TmVar__wfTy (k7 : Hvl) :
    (forall (S3 : Ty) (wf0 : (wfTy k7 S3)) ,
      (forall (c0 : (Cutoff TmVar)) (k9 : Hvl) ,
        (shifthvl_TmVar c0 k7 k9) -> (wfTy k9 (shift_TmVar_Ty c0 S3)))).
  Proof.
    pose proof ((shift_TmVar__wfTm_Ty k7)).
    destruct_conjs .
    easy .
  Qed.
  Definition shift_TyVar__wfTm_Ty : (forall (k7 : Hvl) ,
    (forall (s2 : Tm) (wf : (wfTm k7 s2)) ,
      (forall (c : (Cutoff TyVar)) (k8 : Hvl) ,
        (shifthvl_TyVar c k7 k8) -> (wfTm k8 (shift_TyVar_Tm c s2)))) /\
    (forall (S3 : Ty) (wf : (wfTy k7 S3)) ,
      (forall (c : (Cutoff TyVar)) (k8 : Hvl) ,
        (shifthvl_TyVar c k7 k8) -> (wfTy k8 (shift_TyVar_Ty c S3))))) := (ind_wfTm_Ty (fun (k7 : Hvl) (s2 : Tm) (wf : (wfTm k7 s2)) =>
    (forall (c : (Cutoff TyVar)) (k8 : Hvl) ,
      (shifthvl_TyVar c k7 k8) -> (wfTm k8 (shift_TyVar_Tm c s2)))) (fun (k7 : Hvl) (S3 : Ty) (wf : (wfTy k7 S3)) =>
    (forall (c : (Cutoff TyVar)) (k8 : Hvl) ,
      (shifthvl_TyVar c k7 k8) -> (wfTy k8 (shift_TyVar_Ty c S3)))) (fun (k7 : Hvl) (x7 : (Index TmVar)) (wfi : (wfindex k7 x7)) (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
    (wfTm_Var k8 _ (shift_TyVar__wfindex_TmVar c k7 k8 ins x7 wfi))) (fun (k7 : Hvl) (T : Ty) (wf : (wfTy k7 T)) IHT (t : Tm) (wf0 : (wfTm (HS TmVar k7) t)) IHt (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
    (wfTm_Abs k8 (IHT c k8 (weaken_shifthvl_TyVar H0 ins)) (IHt c (HS TmVar k8) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k7 : Hvl) (t1 : Tm) (wf : (wfTm k7 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k7 t2)) IHt2 (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
    (wfTm_App k8 (IHt1 c k8 (weaken_shifthvl_TyVar H0 ins)) (IHt2 c k8 (weaken_shifthvl_TyVar H0 ins)))) (fun (k7 : Hvl) (X3 : (Index TyVar)) (wfi : (wfindex k7 X3)) (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
    (wfTy_TVar k8 _ (shift_TyVar__wfindex_TyVar c k7 k8 ins X3 wfi))) (fun (k7 : Hvl) (T1 : Ty) (wf : (wfTy k7 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS TmVar k7) T2)) IHT2 (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
    (wfTy_TPi k8 (IHT1 c k8 (weaken_shifthvl_TyVar H0 ins)) (IHT2 c (HS TmVar k8) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k7 : Hvl) (T : Ty) (wf : (wfTy k7 T)) IHT (t : Tm) (wf0 : (wfTm k7 t)) IHt (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
    (wfTy_TApp k8 (IHT c k8 (weaken_shifthvl_TyVar H0 ins)) (IHt c k8 (weaken_shifthvl_TyVar H0 ins))))).
  Lemma shift_TyVar__wfTm (k7 : Hvl) :
    (forall (s2 : Tm) (wf : (wfTm k7 s2)) ,
      (forall (c : (Cutoff TyVar)) (k8 : Hvl) ,
        (shifthvl_TyVar c k7 k8) -> (wfTm k8 (shift_TyVar_Tm c s2)))).
  Proof.
    pose proof ((shift_TyVar__wfTm_Ty k7)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_TyVar__wfTy (k7 : Hvl) :
    (forall (S3 : Ty) (wf0 : (wfTy k7 S3)) ,
      (forall (c0 : (Cutoff TyVar)) (k9 : Hvl) ,
        (shifthvl_TyVar c0 k7 k9) -> (wfTy k9 (shift_TyVar_Ty c0 S3)))).
  Proof.
    pose proof ((shift_TyVar__wfTm_Ty k7)).
    destruct_conjs .
    easy .
  Qed.
  Definition shift_TmVar__wfKind : (forall (k7 : Hvl) ,
    (forall (K3 : Kind) (wf : (wfKind k7 K3)) ,
      (forall (c : (Cutoff TmVar)) (k8 : Hvl) ,
        (shifthvl_TmVar c k7 k8) -> (wfKind k8 (shift_TmVar_Kind c K3))))) := (ind_wfKind (fun (k7 : Hvl) (K3 : Kind) (wf : (wfKind k7 K3)) =>
    (forall (c : (Cutoff TmVar)) (k8 : Hvl) ,
      (shifthvl_TmVar c k7 k8) -> (wfKind k8 (shift_TmVar_Kind c K3)))) (fun (k7 : Hvl) (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
    (wfKind_Star k8)) (fun (k7 : Hvl) (T : Ty) (wf : (wfTy k7 T)) (K : Kind) (wf0 : (wfKind (HS TmVar k7) K)) IHK (c : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c k7 k8)) =>
    (wfKind_KPi k8 (shift_TmVar__wfTy k7 T wf c k8 (weaken_shifthvl_TmVar H0 ins)) (IHK (CS c) (HS TmVar k8) (weaken_shifthvl_TmVar (HS TmVar H0) ins))))).
  Definition shift_TyVar__wfKind : (forall (k7 : Hvl) ,
    (forall (K3 : Kind) (wf : (wfKind k7 K3)) ,
      (forall (c : (Cutoff TyVar)) (k8 : Hvl) ,
        (shifthvl_TyVar c k7 k8) -> (wfKind k8 (shift_TyVar_Kind c K3))))) := (ind_wfKind (fun (k7 : Hvl) (K3 : Kind) (wf : (wfKind k7 K3)) =>
    (forall (c : (Cutoff TyVar)) (k8 : Hvl) ,
      (shifthvl_TyVar c k7 k8) -> (wfKind k8 (shift_TyVar_Kind c K3)))) (fun (k7 : Hvl) (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
    (wfKind_Star k8)) (fun (k7 : Hvl) (T : Ty) (wf : (wfTy k7 T)) (K : Kind) (wf0 : (wfKind (HS TmVar k7) K)) IHK (c : (Cutoff TyVar)) (k8 : Hvl) (ins : (shifthvl_TyVar c k7 k8)) =>
    (wfKind_KPi k8 (shift_TyVar__wfTy k7 T wf c k8 (weaken_shifthvl_TyVar H0 ins)) (IHK c (HS TmVar k8) (weaken_shifthvl_TyVar (HS TmVar H0) ins))))).
  Fixpoint weaken_wfTm (k7 : Hvl) {struct k7} :
  (forall (k8 : Hvl) (s2 : Tm) (wf : (wfTm k8 s2)) ,
    (wfTm (appendHvl k8 k7) (weakenTm s2 k7))) :=
    match k7 return (forall (k8 : Hvl) (s2 : Tm) (wf : (wfTm k8 s2)) ,
      (wfTm (appendHvl k8 k7) (weakenTm s2 k7))) with
      | (H0) => (fun (k8 : Hvl) (s2 : Tm) (wf : (wfTm k8 s2)) =>
        wf)
      | (HS TmVar k7) => (fun (k8 : Hvl) (s2 : Tm) (wf : (wfTm k8 s2)) =>
        (shift_TmVar__wfTm (appendHvl k8 k7) (weakenTm s2 k7) (weaken_wfTm k7 k8 s2 wf) C0 (HS TmVar (appendHvl k8 k7)) (shifthvl_TmVar_here (appendHvl k8 k7))))
      | (HS TyVar k7) => (fun (k8 : Hvl) (s2 : Tm) (wf : (wfTm k8 s2)) =>
        (shift_TyVar__wfTm (appendHvl k8 k7) (weakenTm s2 k7) (weaken_wfTm k7 k8 s2 wf) C0 (HS TyVar (appendHvl k8 k7)) (shifthvl_TyVar_here (appendHvl k8 k7))))
    end.
  Fixpoint weaken_wfTy (k7 : Hvl) {struct k7} :
  (forall (k8 : Hvl) (S3 : Ty) (wf : (wfTy k8 S3)) ,
    (wfTy (appendHvl k8 k7) (weakenTy S3 k7))) :=
    match k7 return (forall (k8 : Hvl) (S3 : Ty) (wf : (wfTy k8 S3)) ,
      (wfTy (appendHvl k8 k7) (weakenTy S3 k7))) with
      | (H0) => (fun (k8 : Hvl) (S3 : Ty) (wf : (wfTy k8 S3)) =>
        wf)
      | (HS TmVar k7) => (fun (k8 : Hvl) (S3 : Ty) (wf : (wfTy k8 S3)) =>
        (shift_TmVar__wfTy (appendHvl k8 k7) (weakenTy S3 k7) (weaken_wfTy k7 k8 S3 wf) C0 (HS TmVar (appendHvl k8 k7)) (shifthvl_TmVar_here (appendHvl k8 k7))))
      | (HS TyVar k7) => (fun (k8 : Hvl) (S3 : Ty) (wf : (wfTy k8 S3)) =>
        (shift_TyVar__wfTy (appendHvl k8 k7) (weakenTy S3 k7) (weaken_wfTy k7 k8 S3 wf) C0 (HS TyVar (appendHvl k8 k7)) (shifthvl_TyVar_here (appendHvl k8 k7))))
    end.
  Fixpoint weaken_wfKind (k7 : Hvl) {struct k7} :
  (forall (k8 : Hvl) (K3 : Kind) (wf : (wfKind k8 K3)) ,
    (wfKind (appendHvl k8 k7) (weakenKind K3 k7))) :=
    match k7 return (forall (k8 : Hvl) (K3 : Kind) (wf : (wfKind k8 K3)) ,
      (wfKind (appendHvl k8 k7) (weakenKind K3 k7))) with
      | (H0) => (fun (k8 : Hvl) (K3 : Kind) (wf : (wfKind k8 K3)) =>
        wf)
      | (HS TmVar k7) => (fun (k8 : Hvl) (K3 : Kind) (wf : (wfKind k8 K3)) =>
        (shift_TmVar__wfKind (appendHvl k8 k7) (weakenKind K3 k7) (weaken_wfKind k7 k8 K3 wf) C0 (HS TmVar (appendHvl k8 k7)) (shifthvl_TmVar_here (appendHvl k8 k7))))
      | (HS TyVar k7) => (fun (k8 : Hvl) (K3 : Kind) (wf : (wfKind k8 K3)) =>
        (shift_TyVar__wfKind (appendHvl k8 k7) (weakenKind K3 k7) (weaken_wfKind k7 k8 K3 wf) C0 (HS TyVar (appendHvl k8 k7)) (shifthvl_TyVar_here (appendHvl k8 k7))))
    end.
End ShiftWellFormed.
Lemma wfTm_cast  :
  (forall (k7 : Hvl) (s2 : Tm) (k8 : Hvl) (s3 : Tm) ,
    (k7 = k8) -> (s2 = s3) -> (wfTm k7 s2) -> (wfTm k8 s3)).
Proof.
  congruence .
Qed.
Lemma wfTy_cast  :
  (forall (k7 : Hvl) (S3 : Ty) (k8 : Hvl) (S4 : Ty) ,
    (k7 = k8) -> (S3 = S4) -> (wfTy k7 S3) -> (wfTy k8 S4)).
Proof.
  congruence .
Qed.
Lemma wfKind_cast  :
  (forall (k7 : Hvl) (K3 : Kind) (k8 : Hvl) (K4 : Kind) ,
    (k7 = k8) -> (K3 = K4) -> (wfKind k7 K3) -> (wfKind k8 K4)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TyVar : infra.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TyVar : shift.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TyVar : shift_wf.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TyVar : wf.
 Hint Resolve shift_TmVar__wfKind shift_TmVar__wfTm shift_TmVar__wfTy shift_TyVar__wfKind shift_TyVar__wfTm shift_TyVar__wfTy : infra.
 Hint Resolve shift_TmVar__wfKind shift_TmVar__wfTm shift_TmVar__wfTy shift_TyVar__wfKind shift_TyVar__wfTm shift_TyVar__wfTy : shift.
 Hint Resolve shift_TmVar__wfKind shift_TmVar__wfTm shift_TmVar__wfTy shift_TyVar__wfKind shift_TyVar__wfTm shift_TyVar__wfTy : shift_wf.
 Hint Resolve shift_TmVar__wfKind shift_TmVar__wfTm shift_TmVar__wfTy shift_TyVar__wfKind shift_TyVar__wfTm shift_TyVar__wfTy : wf.
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
  Lemma substhvl_TmVar_wfindex_TmVar {k7 : Hvl} {s2 : Tm} (wft : (wfTm k7 s2)) :
    (forall {d : (Trace TmVar)} {k8 : Hvl} {k9 : Hvl} ,
      (substhvl_TmVar k7 d k8 k9) -> (forall {x7 : (Index TmVar)} ,
        (wfindex k8 x7) -> (wfTm k9 (subst_TmVar_Index d s2 x7)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TyVar_wfindex_TyVar {k7 : Hvl} {S3 : Ty} (wft : (wfTy k7 S3)) :
    (forall {d : (Trace TyVar)} {k8 : Hvl} {k9 : Hvl} ,
      (substhvl_TyVar k7 d k8 k9) -> (forall {X3 : (Index TyVar)} ,
        (wfindex k8 X3) -> (wfTy k9 (subst_TyVar_Index d S3 X3)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TmVar_wfindex_TyVar {k7 : Hvl} :
    (forall {d : (Trace TmVar)} {k8 : Hvl} {k9 : Hvl} ,
      (substhvl_TmVar k7 d k8 k9) -> (forall {X3 : (Index TyVar)} ,
        (wfindex k8 X3) -> (wfindex k9 X3))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_TyVar_wfindex_TmVar {k7 : Hvl} :
    (forall {d : (Trace TyVar)} {k8 : Hvl} {k9 : Hvl} ,
      (substhvl_TyVar k7 d k8 k9) -> (forall {x7 : (Index TmVar)} ,
        (wfindex k8 x7) -> (wfindex k9 x7))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_TmVar_wfTm_Ty {k7 : Hvl} {s2 : Tm} (wf : (wfTm k7 s2)) : (forall (k8 : Hvl) ,
    (forall (s3 : Tm) (wf0 : (wfTm k8 s3)) ,
      (forall {d : (Trace TmVar)} {k9 : Hvl} ,
        (substhvl_TmVar k7 d k8 k9) -> (wfTm k9 (subst_TmVar_Tm d s2 s3)))) /\
    (forall (S3 : Ty) (wf0 : (wfTy k8 S3)) ,
      (forall {d : (Trace TmVar)} {k9 : Hvl} ,
        (substhvl_TmVar k7 d k8 k9) -> (wfTy k9 (subst_TmVar_Ty d s2 S3))))) := (ind_wfTm_Ty (fun (k8 : Hvl) (s3 : Tm) (wf0 : (wfTm k8 s3)) =>
    (forall {d : (Trace TmVar)} {k9 : Hvl} ,
      (substhvl_TmVar k7 d k8 k9) -> (wfTm k9 (subst_TmVar_Tm d s2 s3)))) (fun (k8 : Hvl) (S3 : Ty) (wf0 : (wfTy k8 S3)) =>
    (forall {d : (Trace TmVar)} {k9 : Hvl} ,
      (substhvl_TmVar k7 d k8 k9) -> (wfTy k9 (subst_TmVar_Ty d s2 S3)))) (fun (k8 : Hvl) {x7 : (Index TmVar)} (wfi : (wfindex k8 x7)) {d : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d k8 k9)) =>
    (substhvl_TmVar_wfindex_TmVar wf del wfi)) (fun (k8 : Hvl) (T : Ty) (wf0 : (wfTy k8 T)) IHT (t : Tm) (wf1 : (wfTm (HS TmVar k8) t)) IHt {d : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d k8 k9)) =>
    (wfTm_Abs k9 (IHT (weakenTrace d H0) k9 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d (HS TmVar H0)) (HS TmVar k9) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k8 : Hvl) (t1 : Tm) (wf0 : (wfTm k8 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k8 t2)) IHt2 {d : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d k8 k9)) =>
    (wfTm_App k9 (IHt1 (weakenTrace d H0) k9 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d H0) k9 (weaken_substhvl_TmVar H0 del)))) (fun (k8 : Hvl) {X3 : (Index TyVar)} (wfi : (wfindex k8 X3)) {d : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d k8 k9)) =>
    (wfTy_TVar k9 _ (substhvl_TmVar_wfindex_TyVar del wfi))) (fun (k8 : Hvl) (T1 : Ty) (wf0 : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS TmVar k8) T2)) IHT2 {d : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d k8 k9)) =>
    (wfTy_TPi k9 (IHT1 (weakenTrace d H0) k9 (weaken_substhvl_TmVar H0 del)) (IHT2 (weakenTrace d (HS TmVar H0)) (HS TmVar k9) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k8 : Hvl) (T : Ty) (wf0 : (wfTy k8 T)) IHT (t : Tm) (wf1 : (wfTm k8 t)) IHt {d : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d k8 k9)) =>
    (wfTy_TApp k9 (IHT (weakenTrace d H0) k9 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d H0) k9 (weaken_substhvl_TmVar H0 del))))).
  Lemma substhvl_TmVar_wfTm {k7 : Hvl} {s2 : Tm} (wf : (wfTm k7 s2)) (k8 : Hvl) (s3 : Tm) (wf0 : (wfTm k8 s3)) :
    (forall {d : (Trace TmVar)} {k9 : Hvl} ,
      (substhvl_TmVar k7 d k8 k9) -> (wfTm k9 (subst_TmVar_Tm d s2 s3))).
  Proof.
    apply ((substhvl_TmVar_wfTm_Ty wf k8)).
    auto .
  Qed.
  Lemma substhvl_TmVar_wfTy {k7 : Hvl} {s2 : Tm} (wf : (wfTm k7 s2)) (k8 : Hvl) (S3 : Ty) (wf1 : (wfTy k8 S3)) :
    (forall {d0 : (Trace TmVar)} {k10 : Hvl} ,
      (substhvl_TmVar k7 d0 k8 k10) -> (wfTy k10 (subst_TmVar_Ty d0 s2 S3))).
  Proof.
    apply ((substhvl_TmVar_wfTm_Ty wf k8)).
    auto .
  Qed.
  Definition substhvl_TyVar_wfTm_Ty {k7 : Hvl} {S3 : Ty} (wf : (wfTy k7 S3)) : (forall (k8 : Hvl) ,
    (forall (s2 : Tm) (wf0 : (wfTm k8 s2)) ,
      (forall {d : (Trace TyVar)} {k9 : Hvl} ,
        (substhvl_TyVar k7 d k8 k9) -> (wfTm k9 (subst_TyVar_Tm d S3 s2)))) /\
    (forall (S4 : Ty) (wf0 : (wfTy k8 S4)) ,
      (forall {d : (Trace TyVar)} {k9 : Hvl} ,
        (substhvl_TyVar k7 d k8 k9) -> (wfTy k9 (subst_TyVar_Ty d S3 S4))))) := (ind_wfTm_Ty (fun (k8 : Hvl) (s2 : Tm) (wf0 : (wfTm k8 s2)) =>
    (forall {d : (Trace TyVar)} {k9 : Hvl} ,
      (substhvl_TyVar k7 d k8 k9) -> (wfTm k9 (subst_TyVar_Tm d S3 s2)))) (fun (k8 : Hvl) (S4 : Ty) (wf0 : (wfTy k8 S4)) =>
    (forall {d : (Trace TyVar)} {k9 : Hvl} ,
      (substhvl_TyVar k7 d k8 k9) -> (wfTy k9 (subst_TyVar_Ty d S3 S4)))) (fun (k8 : Hvl) {x7 : (Index TmVar)} (wfi : (wfindex k8 x7)) {d : (Trace TyVar)} {k9 : Hvl} (del : (substhvl_TyVar k7 d k8 k9)) =>
    (wfTm_Var k9 _ (substhvl_TyVar_wfindex_TmVar del wfi))) (fun (k8 : Hvl) (T : Ty) (wf0 : (wfTy k8 T)) IHT (t : Tm) (wf1 : (wfTm (HS TmVar k8) t)) IHt {d : (Trace TyVar)} {k9 : Hvl} (del : (substhvl_TyVar k7 d k8 k9)) =>
    (wfTm_Abs k9 (IHT (weakenTrace d H0) k9 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d (HS TmVar H0)) (HS TmVar k9) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k8 : Hvl) (t1 : Tm) (wf0 : (wfTm k8 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k8 t2)) IHt2 {d : (Trace TyVar)} {k9 : Hvl} (del : (substhvl_TyVar k7 d k8 k9)) =>
    (wfTm_App k9 (IHt1 (weakenTrace d H0) k9 (weaken_substhvl_TyVar H0 del)) (IHt2 (weakenTrace d H0) k9 (weaken_substhvl_TyVar H0 del)))) (fun (k8 : Hvl) {X3 : (Index TyVar)} (wfi : (wfindex k8 X3)) {d : (Trace TyVar)} {k9 : Hvl} (del : (substhvl_TyVar k7 d k8 k9)) =>
    (substhvl_TyVar_wfindex_TyVar wf del wfi)) (fun (k8 : Hvl) (T1 : Ty) (wf0 : (wfTy k8 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS TmVar k8) T2)) IHT2 {d : (Trace TyVar)} {k9 : Hvl} (del : (substhvl_TyVar k7 d k8 k9)) =>
    (wfTy_TPi k9 (IHT1 (weakenTrace d H0) k9 (weaken_substhvl_TyVar H0 del)) (IHT2 (weakenTrace d (HS TmVar H0)) (HS TmVar k9) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k8 : Hvl) (T : Ty) (wf0 : (wfTy k8 T)) IHT (t : Tm) (wf1 : (wfTm k8 t)) IHt {d : (Trace TyVar)} {k9 : Hvl} (del : (substhvl_TyVar k7 d k8 k9)) =>
    (wfTy_TApp k9 (IHT (weakenTrace d H0) k9 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d H0) k9 (weaken_substhvl_TyVar H0 del))))).
  Lemma substhvl_TyVar_wfTm {k7 : Hvl} {S3 : Ty} (wf : (wfTy k7 S3)) (k8 : Hvl) (s2 : Tm) (wf0 : (wfTm k8 s2)) :
    (forall {d : (Trace TyVar)} {k9 : Hvl} ,
      (substhvl_TyVar k7 d k8 k9) -> (wfTm k9 (subst_TyVar_Tm d S3 s2))).
  Proof.
    apply ((substhvl_TyVar_wfTm_Ty wf k8)).
    auto .
  Qed.
  Lemma substhvl_TyVar_wfTy {k7 : Hvl} {S3 : Ty} (wf : (wfTy k7 S3)) (k8 : Hvl) (S4 : Ty) (wf1 : (wfTy k8 S4)) :
    (forall {d0 : (Trace TyVar)} {k10 : Hvl} ,
      (substhvl_TyVar k7 d0 k8 k10) -> (wfTy k10 (subst_TyVar_Ty d0 S3 S4))).
  Proof.
    apply ((substhvl_TyVar_wfTm_Ty wf k8)).
    auto .
  Qed.
  Definition substhvl_TmVar_wfKind {k7 : Hvl} {s2 : Tm} (wf : (wfTm k7 s2)) : (forall (k8 : Hvl) ,
    (forall (K3 : Kind) (wf0 : (wfKind k8 K3)) ,
      (forall {d : (Trace TmVar)} {k9 : Hvl} ,
        (substhvl_TmVar k7 d k8 k9) -> (wfKind k9 (subst_TmVar_Kind d s2 K3))))) := (ind_wfKind (fun (k8 : Hvl) (K3 : Kind) (wf0 : (wfKind k8 K3)) =>
    (forall {d : (Trace TmVar)} {k9 : Hvl} ,
      (substhvl_TmVar k7 d k8 k9) -> (wfKind k9 (subst_TmVar_Kind d s2 K3)))) (fun (k8 : Hvl) {d : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d k8 k9)) =>
    (wfKind_Star k9)) (fun (k8 : Hvl) (T : Ty) (wf0 : (wfTy k8 T)) (K : Kind) (wf1 : (wfKind (HS TmVar k8) K)) IHK {d : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d k8 k9)) =>
    (wfKind_KPi k9 (substhvl_TmVar_wfTy wf k8 T wf0 (weaken_substhvl_TmVar H0 del)) (IHK (weakenTrace d (HS TmVar H0)) (HS TmVar k9) (weaken_substhvl_TmVar (HS TmVar H0) del))))).
  Definition substhvl_TyVar_wfKind {k7 : Hvl} {S3 : Ty} (wf : (wfTy k7 S3)) : (forall (k8 : Hvl) ,
    (forall (K3 : Kind) (wf0 : (wfKind k8 K3)) ,
      (forall {d : (Trace TyVar)} {k9 : Hvl} ,
        (substhvl_TyVar k7 d k8 k9) -> (wfKind k9 (subst_TyVar_Kind d S3 K3))))) := (ind_wfKind (fun (k8 : Hvl) (K3 : Kind) (wf0 : (wfKind k8 K3)) =>
    (forall {d : (Trace TyVar)} {k9 : Hvl} ,
      (substhvl_TyVar k7 d k8 k9) -> (wfKind k9 (subst_TyVar_Kind d S3 K3)))) (fun (k8 : Hvl) {d : (Trace TyVar)} {k9 : Hvl} (del : (substhvl_TyVar k7 d k8 k9)) =>
    (wfKind_Star k9)) (fun (k8 : Hvl) (T : Ty) (wf0 : (wfTy k8 T)) (K : Kind) (wf1 : (wfKind (HS TmVar k8) K)) IHK {d : (Trace TyVar)} {k9 : Hvl} (del : (substhvl_TyVar k7 d k8 k9)) =>
    (wfKind_KPi k9 (substhvl_TyVar_wfTy wf k8 T wf0 (weaken_substhvl_TyVar H0 del)) (IHK (weakenTrace d (HS TmVar H0)) (HS TmVar k9) (weaken_substhvl_TyVar (HS TmVar H0) del))))).
End SubstWellFormed.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : infra.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : subst.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : subst_wf.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : wf.
 Hint Resolve substhvl_TmVar_wfKind substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfKind substhvl_TyVar_wfTm substhvl_TyVar_wfTy : infra.
 Hint Resolve substhvl_TmVar_wfKind substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfKind substhvl_TyVar_wfTm substhvl_TyVar_wfTy : subst.
 Hint Resolve substhvl_TmVar_wfKind substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfKind substhvl_TyVar_wfTm substhvl_TyVar_wfTy : subst_wf.
 Hint Resolve substhvl_TmVar_wfKind substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfKind substhvl_TyVar_wfTm substhvl_TyVar_wfTy : wf.
 Hint Constructors substhvl_TmVar substhvl_TyVar : infra.
 Hint Constructors substhvl_TmVar substhvl_TyVar : subst.
 Hint Constructors substhvl_TmVar substhvl_TyVar : subst_wf.
 Hint Constructors substhvl_TmVar substhvl_TyVar : wf.
Section Context.
  Inductive Ctx : Type :=
    | empty 
    | evar (G : Ctx) (T : Ty)
    | etvar (G : Ctx) (K : Kind).
  Fixpoint appendCtx (G : Ctx) (G0 : Ctx) :
  Ctx :=
    match G0 with
      | (empty) => G
      | (evar G1 T) => (evar (appendCtx G G1) T)
      | (etvar G1 K) => (etvar (appendCtx G G1) K)
    end.
  Fixpoint domainCtx (G : Ctx) :
  Hvl :=
    match G with
      | (empty) => H0
      | (evar G0 T) => (HS TmVar (domainCtx G0))
      | (etvar G0 K) => (HS TyVar (domainCtx G0))
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
      | (evar G0 T) => (evar (shift_TmVar_Ctx c G0) (shift_TmVar_Ty (weakenCutoffTmVar c (domainCtx G0)) T))
      | (etvar G0 K) => (etvar (shift_TmVar_Ctx c G0) (shift_TmVar_Kind (weakenCutoffTmVar c (domainCtx G0)) K))
    end.
  Fixpoint shift_TyVar_Ctx (c : (Cutoff TyVar)) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shift_TyVar_Ctx c G0) (shift_TyVar_Ty (weakenCutoffTyVar c (domainCtx G0)) T))
      | (etvar G0 K) => (etvar (shift_TyVar_Ctx c G0) (shift_TyVar_Kind (weakenCutoffTyVar c (domainCtx G0)) K))
    end.
  Fixpoint weakenCtx (G : Ctx) (k7 : Hvl) {struct k7} :
  Ctx :=
    match k7 with
      | (H0) => G
      | (HS TmVar k7) => (shift_TmVar_Ctx C0 (weakenCtx G k7))
      | (HS TyVar k7) => (shift_TyVar_Ctx C0 (weakenCtx G k7))
    end.
  Fixpoint subst_TmVar_Ctx (d : (Trace TmVar)) (s2 : Tm) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (subst_TmVar_Ctx d s2 G0) (subst_TmVar_Ty (weakenTrace d (domainCtx G0)) s2 T))
      | (etvar G0 K) => (etvar (subst_TmVar_Ctx d s2 G0) (subst_TmVar_Kind (weakenTrace d (domainCtx G0)) s2 K))
    end.
  Fixpoint subst_TyVar_Ctx (d : (Trace TyVar)) (S3 : Ty) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (subst_TyVar_Ctx d S3 G0) (subst_TyVar_Ty (weakenTrace d (domainCtx G0)) S3 T))
      | (etvar G0 K) => (etvar (subst_TyVar_Ctx d S3 G0) (subst_TyVar_Kind (weakenTrace d (domainCtx G0)) S3 K))
    end.
  Lemma domainCtx_shift_TmVar_Ctx  :
    (forall (c : (Cutoff TmVar)) (G : Ctx) ,
      ((domainCtx (shift_TmVar_Ctx c G)) = (domainCtx G))).
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
    (forall (d : (Trace TmVar)) (s2 : Tm) (G : Ctx) ,
      ((domainCtx (subst_TmVar_Ctx d s2 G)) = (domainCtx G))).
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
    Lemma shift_TyVar_Ctx_appendCtx  :
      (forall (c : (Cutoff TyVar)) (G : Ctx) (G0 : Ctx) ,
        ((shift_TyVar_Ctx c (appendCtx G G0)) = (appendCtx (shift_TyVar_Ctx c G) (shift_TyVar_Ctx (weakenCutoffTyVar c (domainCtx G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma subst_TmVar_Ctx_appendCtx  :
      (forall (d : (Trace TmVar)) (s2 : Tm) (G : Ctx) (G0 : Ctx) ,
        ((subst_TmVar_Ctx d s2 (appendCtx G G0)) = (appendCtx (subst_TmVar_Ctx d s2 G) (subst_TmVar_Ctx (weakenTrace d (domainCtx G)) s2 G0)))).
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
  Lemma weakenTm_append  :
    (forall (s2 : Tm) (k7 : Hvl) (k8 : Hvl) ,
      ((weakenTm (weakenTm s2 k7) k8) = (weakenTm s2 (appendHvl k7 k8)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTy_append  :
    (forall (S3 : Ty) (k7 : Hvl) (k8 : Hvl) ,
      ((weakenTy (weakenTy S3 k7) k8) = (weakenTy S3 (appendHvl k7 k8)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenKind_append  :
    (forall (K3 : Kind) (k7 : Hvl) (k8 : Hvl) ,
      ((weakenKind (weakenKind K3 k7) k8) = (weakenKind K3 (appendHvl k7 k8)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Ctx -> (Index TmVar) -> Ty -> Prop :=
      | lookup_evar_here {G : Ctx}
          (T5 : Ty) :
          (wfTy (domainCtx G) T5) -> (lookup_evar (evar G T5) I0 (shift_TmVar_Ty C0 T5))
      | lookup_evar_there_evar
          {G : Ctx} {x7 : (Index TmVar)}
          (T6 : Ty) (T7 : Ty) :
          (lookup_evar G x7 T6) -> (lookup_evar (evar G T7) (IS x7) (shift_TmVar_Ty C0 T6))
      | lookup_evar_there_etvar
          {G : Ctx} {x7 : (Index TmVar)}
          (T6 : Ty) (K3 : Kind) :
          (lookup_evar G x7 T6) -> (lookup_evar (etvar G K3) x7 (shift_TyVar_Ty C0 T6)).
    Inductive lookup_etvar : Ctx -> (Index TyVar) -> Kind -> Prop :=
      | lookup_etvar_here {G : Ctx}
          (K3 : Kind) :
          (wfKind (domainCtx G) K3) -> (lookup_etvar (etvar G K3) I0 (shift_TyVar_Kind C0 K3))
      | lookup_etvar_there_evar
          {G : Ctx} {X3 : (Index TyVar)}
          (K4 : Kind) (T6 : Ty) :
          (lookup_etvar G X3 K4) -> (lookup_etvar (evar G T6) X3 (shift_TmVar_Kind C0 K4))
      | lookup_etvar_there_etvar
          {G : Ctx} {X3 : (Index TyVar)}
          (K4 : Kind) (K5 : Kind) :
          (lookup_etvar G X3 K4) -> (lookup_etvar (etvar G K5) (IS X3) (shift_TyVar_Kind C0 K4)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Ctx) (T6 : Ty) (T7 : Ty) ,
        (lookup_evar (evar G T6) I0 T7) -> ((shift_TmVar_Ty C0 T6) = T7)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Ctx) (K4 : Kind) (K5 : Kind) ,
        (lookup_etvar (etvar G K4) I0 K5) -> ((shift_TyVar_Kind C0 K4) = K5)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Ctx} {x7 : (Index TmVar)} ,
        (forall (T6 : Ty) ,
          (lookup_evar G x7 T6) -> (forall (T7 : Ty) ,
            (lookup_evar G x7 T7) -> (T6 = T7)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G : Ctx} {X3 : (Index TyVar)} ,
        (forall (K4 : Kind) ,
          (lookup_etvar G X3 K4) -> (forall (K5 : Kind) ,
            (lookup_etvar G X3 K5) -> (K4 = K5)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Ctx} {x7 : (Index TmVar)} (T6 : Ty) ,
        (lookup_evar G x7 T6) -> (wfTy (domainCtx G) T6)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G : Ctx} {X3 : (Index TyVar)} (K4 : Kind) ,
        (lookup_etvar G X3 K4) -> (wfKind (domainCtx G) K4)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Ctx} (G0 : Ctx) {x7 : (Index TmVar)} (T6 : Ty) ,
        (lookup_evar G x7 T6) -> (lookup_evar (appendCtx G G0) (weakenIndexTmVar x7 (domainCtx G0)) (weakenTy T6 (domainCtx G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Ctx} (G0 : Ctx) {X3 : (Index TyVar)} (K4 : Kind) ,
        (lookup_etvar G X3 K4) -> (lookup_etvar (appendCtx G G0) (weakenIndexTyVar X3 (domainCtx G0)) (weakenKind K4 (domainCtx G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Ctx} {x7 : (Index TmVar)} (T8 : Ty) ,
        (lookup_evar G x7 T8) -> (wfindex (domainCtx G) x7)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Ctx} {X3 : (Index TyVar)} (K6 : Kind) ,
        (lookup_etvar G X3 K6) -> (wfindex (domainCtx G) X3)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff TmVar) -> Ctx -> Ctx -> Prop :=
    | shift_evar_here {G : Ctx}
        {T6 : Ty} :
        (shift_evar C0 G (evar G T6))
    | shiftevar_there_evar
        {c : (Cutoff TmVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_evar c G G0) -> (shift_evar (CS c) (evar G T) (evar G0 (shift_TmVar_Ty c T)))
    | shiftevar_there_etvar
        {c : (Cutoff TmVar)} {G : Ctx}
        {G0 : Ctx} {K : Kind} :
        (shift_evar c G G0) -> (shift_evar c (etvar G K) (etvar G0 (shift_TmVar_Kind c K))).
  Lemma weaken_shift_evar  :
    (forall (G : Ctx) {c : (Cutoff TmVar)} {G0 : Ctx} {G1 : Ctx} ,
      (shift_evar c G0 G1) -> (shift_evar (weakenCutoffTmVar c (domainCtx G)) (appendCtx G0 G) (appendCtx G1 (shift_TmVar_Ctx c G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff TyVar) -> Ctx -> Ctx -> Prop :=
    | shift_etvar_here {G : Ctx}
        {K4 : Kind} :
        (shift_etvar C0 G (etvar G K4))
    | shiftetvar_there_evar
        {c : (Cutoff TyVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_etvar c G G0) -> (shift_etvar c (evar G T) (evar G0 (shift_TyVar_Ty c T)))
    | shiftetvar_there_etvar
        {c : (Cutoff TyVar)} {G : Ctx}
        {G0 : Ctx} {K : Kind} :
        (shift_etvar c G G0) -> (shift_etvar (CS c) (etvar G K) (etvar G0 (shift_TyVar_Kind c K))).
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
  Lemma shift_etvar_shifthvl_TyVar  :
    (forall {c : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} ,
      (shift_etvar c G G0) -> (shifthvl_TyVar c (domainCtx G) (domainCtx G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Ctx) (T6 : Ty) (s2 : Tm) : (Trace TmVar) -> Ctx -> Ctx -> Prop :=
    | subst_evar_here :
        (subst_evar G T6 s2 X0 (evar G T6) G)
    | subst_evar_there_evar
        {d : (Trace TmVar)} {G0 : Ctx}
        {G1 : Ctx} (T7 : Ty) :
        (subst_evar G T6 s2 d G0 G1) -> (subst_evar G T6 s2 (XS TmVar d) (evar G0 T7) (evar G1 (subst_TmVar_Ty d s2 T7)))
    | subst_evar_there_etvar
        {d : (Trace TmVar)} {G0 : Ctx}
        {G1 : Ctx} (K4 : Kind) :
        (subst_evar G T6 s2 d G0 G1) -> (subst_evar G T6 s2 (XS TyVar d) (etvar G0 K4) (etvar G1 (subst_TmVar_Kind d s2 K4))).
  Lemma weaken_subst_evar {G : Ctx} (T6 : Ty) {s2 : Tm} :
    (forall (G0 : Ctx) {d : (Trace TmVar)} {G1 : Ctx} {G2 : Ctx} ,
      (subst_evar G T6 s2 d G1 G2) -> (subst_evar G T6 s2 (weakenTrace d (domainCtx G0)) (appendCtx G1 G0) (appendCtx G2 (subst_TmVar_Ctx d s2 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Ctx) (K4 : Kind) (S3 : Ty) : (Trace TyVar) -> Ctx -> Ctx -> Prop :=
    | subst_etvar_here :
        (subst_etvar G K4 S3 X0 (etvar G K4) G)
    | subst_etvar_there_evar
        {d : (Trace TyVar)} {G0 : Ctx}
        {G1 : Ctx} (T6 : Ty) :
        (subst_etvar G K4 S3 d G0 G1) -> (subst_etvar G K4 S3 (XS TmVar d) (evar G0 T6) (evar G1 (subst_TyVar_Ty d S3 T6)))
    | subst_etvar_there_etvar
        {d : (Trace TyVar)} {G0 : Ctx}
        {G1 : Ctx} (K5 : Kind) :
        (subst_etvar G K4 S3 d G0 G1) -> (subst_etvar G K4 S3 (XS TyVar d) (etvar G0 K5) (etvar G1 (subst_TyVar_Kind d S3 K5))).
  Lemma weaken_subst_etvar {G : Ctx} (K4 : Kind) {S3 : Ty} :
    (forall (G0 : Ctx) {d : (Trace TyVar)} {G1 : Ctx} {G2 : Ctx} ,
      (subst_etvar G K4 S3 d G1 G2) -> (subst_etvar G K4 S3 (weakenTrace d (domainCtx G0)) (appendCtx G1 G0) (appendCtx G2 (subst_TyVar_Ctx d S3 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_TmVar {G : Ctx} {s2 : Tm} (T6 : Ty) :
    (forall {d : (Trace TmVar)} {G0 : Ctx} {G1 : Ctx} ,
      (subst_evar G T6 s2 d G0 G1) -> (substhvl_TmVar (domainCtx G) d (domainCtx G0) (domainCtx G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_TyVar {G : Ctx} {S3 : Ty} (K4 : Kind) :
    (forall {d : (Trace TyVar)} {G0 : Ctx} {G1 : Ctx} ,
      (subst_etvar G K4 S3 d G0 G1) -> (substhvl_TyVar (domainCtx G) d (domainCtx G0) (domainCtx G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
End ContextStuff.
 Hint Rewrite domainCtx_shift_TmVar_Ctx domainCtx_shift_TyVar_Ctx : interaction.
 Hint Rewrite domainCtx_shift_TmVar_Ctx domainCtx_shift_TyVar_Ctx : env_domain_shift.
 Hint Rewrite domainCtx_subst_TmVar_Ctx domainCtx_subst_TyVar_Ctx : interaction.
 Hint Rewrite domainCtx_subst_TmVar_Ctx domainCtx_subst_TyVar_Ctx : env_domain_subst.
 Hint Rewrite shift_TmVar_Ctx_appendCtx shift_TyVar_Ctx_appendCtx : interaction.
 Hint Rewrite shift_TmVar_Ctx_appendCtx shift_TyVar_Ctx_appendCtx : env_shift_append.
 Hint Rewrite subst_TmVar_Ctx_appendCtx subst_TyVar_Ctx_appendCtx : interaction.
 Hint Rewrite subst_TmVar_Ctx_appendCtx subst_TyVar_Ctx_appendCtx : env_shift_append.
 Hint Constructors lookup_evar lookup_etvar : infra.
 Hint Constructors lookup_evar lookup_etvar : lookup.
 Hint Constructors lookup_evar lookup_etvar : shift.
 Hint Constructors lookup_evar lookup_etvar : subst.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : infra.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : lookup.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : shift.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : weaken.
Lemma weaken_lookup_evar_here  :
  (forall {G : Ctx} (G0 : Ctx) {T6 : Ty} (wf : (wfTy (domainCtx G) T6)) ,
    (lookup_evar (appendCtx (evar G T6) G0) (weakenIndexTmVar I0 (domainCtx G0)) (weakenTy (shift_TmVar_Ty C0 T6) (domainCtx G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Ctx} (G0 : Ctx) {K4 : Kind} (wf : (wfKind (domainCtx G) K4)) ,
    (lookup_etvar (appendCtx (etvar G K4) G0) (weakenIndexTyVar I0 (domainCtx G0)) (weakenKind (shift_TyVar_Kind C0 K4) (domainCtx G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfKind wfTm wfTy : infra.
 Hint Constructors wfKind wfTm wfTy : wf.
 Hint Extern 10 ((wfKind _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H29 : (wfTm _ (Var _)) |- _ => inversion H29; subst; clear H29
  | H29 : (wfTm _ (Abs _ _)) |- _ => inversion H29; subst; clear H29
  | H29 : (wfTm _ (App _ _)) |- _ => inversion H29; subst; clear H29
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H29 : (wfTy _ (TVar _)) |- _ => inversion H29; subst; clear H29
  | H29 : (wfTy _ (TPi _ _)) |- _ => inversion H29; subst; clear H29
  | H29 : (wfTy _ (TApp _ _)) |- _ => inversion H29; subst; clear H29
end : infra wf.
 Hint Extern 2 ((wfKind _ _)) => match goal with
  | H29 : (wfKind _ (Star)) |- _ => inversion H29; subst; clear H29
  | H29 : (wfKind _ (KPi _ _)) |- _ => inversion H29; subst; clear H29
end : infra wf.
 Hint Resolve lookup_evar_wf lookup_etvar_wf : infra.
 Hint Resolve lookup_evar_wf lookup_etvar_wf : wf.
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
  (forall {c : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evar c G G0)) {x7 : (Index TmVar)} {T6 : Ty} ,
    (lookup_evar G x7 T6) -> (lookup_evar G0 (shift_TmVar_Index c x7) (shift_TmVar_Ty c T6))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evar c G G0)) {X3 : (Index TyVar)} {K4 : Kind} ,
    (lookup_etvar G X3 K4) -> (lookup_etvar G0 X3 (shift_TmVar_Kind c K4))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_etvar c G G0)) {x7 : (Index TmVar)} {T6 : Ty} ,
    (lookup_evar G x7 T6) -> (lookup_evar G0 x7 (shift_TyVar_Ty c T6))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_etvar c G G0)) {X3 : (Index TyVar)} {K4 : Kind} ,
    (lookup_etvar G X3 K4) -> (lookup_etvar G0 (shift_TyVar_Index c X3) (shift_TyVar_Kind c K4))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Ctx} (T7 : Ty) {s2 : Tm} (wf : (wfTm (domainCtx G) s2)) :
  (forall {d : (Trace TmVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_evar G T7 s2 d G0 G1)) {X3 : (Index TyVar)} (K5 : Kind) ,
    (lookup_etvar G0 X3 K5) -> (lookup_etvar G1 X3 (subst_TmVar_Kind d s2 K5))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Ctx} (K5 : Kind) {S3 : Ty} (wf : (wfTy (domainCtx G) S3)) :
  (forall {d : (Trace TyVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_etvar G K5 S3 d G0 G1)) {x7 : (Index TmVar)} (T7 : Ty) ,
    (lookup_evar G0 x7 T7) -> (lookup_evar G1 x7 (subst_TyVar_Ty d S3 T7))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (Var x7) => 1
    | (Abs T5 t3) => (plus 1 (plus (size_Ty T5) (size_Tm t3)))
    | (App t4 t5) => (plus 1 (plus (size_Tm t4) (size_Tm t5)))
  end
with size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (TVar X3) => 1
    | (TPi T5 T6) => (plus 1 (plus (size_Ty T5) (size_Ty T6)))
    | (TApp T7 t3) => (plus 1 (plus (size_Ty T7) (size_Tm t3)))
  end.
Fixpoint size_Kind (K1 : Kind) {struct K1} :
nat :=
  match K1 with
    | (Star) => 1
    | (KPi T5 K2) => (plus 1 (plus (size_Ty T5) (size_Kind K2)))
  end.
Fixpoint shift_TmVar__size_Tm (s : Tm) (c : (Cutoff TmVar)) {struct s} :
((size_Tm (shift_TmVar_Tm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shift_TmVar_Tm c s)) = (size_Tm s)) with
    | (Var _) => eq_refl
    | (Abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Ty T c) (shift_TmVar__size_Tm t (CS c))))
    | (App t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t1 c) (shift_TmVar__size_Tm t2 c)))
  end
with shift_TmVar__size_Ty (S0 : Ty) (c : (Cutoff TmVar)) {struct S0} :
((size_Ty (shift_TmVar_Ty c S0)) = (size_Ty S0)) :=
  match S0 return ((size_Ty (shift_TmVar_Ty c S0)) = (size_Ty S0)) with
    | (TVar _) => eq_refl
    | (TPi T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Ty T1 c) (shift_TmVar__size_Ty T2 (CS c))))
    | (TApp T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Ty T c) (shift_TmVar__size_Tm t c)))
  end.
Fixpoint shift_TyVar__size_Tm (s : Tm) (c : (Cutoff TyVar)) {struct s} :
((size_Tm (shift_TyVar_Tm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shift_TyVar_Tm c s)) = (size_Tm s)) with
    | (Var _) => eq_refl
    | (Abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T c) (shift_TyVar__size_Tm t c)))
    | (App t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Tm t1 c) (shift_TyVar__size_Tm t2 c)))
  end
with shift_TyVar__size_Ty (S0 : Ty) (c : (Cutoff TyVar)) {struct S0} :
((size_Ty (shift_TyVar_Ty c S0)) = (size_Ty S0)) :=
  match S0 return ((size_Ty (shift_TyVar_Ty c S0)) = (size_Ty S0)) with
    | (TVar _) => eq_refl
    | (TPi T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T1 c) (shift_TyVar__size_Ty T2 c)))
    | (TApp T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T c) (shift_TyVar__size_Tm t c)))
  end.
Fixpoint shift_TmVar__size_Kind (K1 : Kind) (c : (Cutoff TmVar)) {struct K1} :
((size_Kind (shift_TmVar_Kind c K1)) = (size_Kind K1)) :=
  match K1 return ((size_Kind (shift_TmVar_Kind c K1)) = (size_Kind K1)) with
    | (Star) => eq_refl
    | (KPi T K) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Ty T c) (shift_TmVar__size_Kind K (CS c))))
  end.
Fixpoint shift_TyVar__size_Kind (K1 : Kind) (c : (Cutoff TyVar)) {struct K1} :
((size_Kind (shift_TyVar_Kind c K1)) = (size_Kind K1)) :=
  match K1 return ((size_Kind (shift_TyVar_Kind c K1)) = (size_Kind K1)) with
    | (Star) => eq_refl
    | (KPi T K) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T c) (shift_TyVar__size_Kind K c)))
  end.
 Hint Rewrite shift_TmVar__size_Kind shift_TyVar__size_Kind shift_TmVar__size_Tm shift_TyVar__size_Tm shift_TmVar__size_Ty shift_TyVar__size_Ty : interaction.
 Hint Rewrite shift_TmVar__size_Kind shift_TyVar__size_Kind shift_TmVar__size_Tm shift_TyVar__size_Tm shift_TmVar__size_Ty shift_TyVar__size_Ty : shift_size.
Lemma weaken_size_Kind  :
  (forall (k : Hvl) (K1 : Kind) ,
    ((size_Kind (weakenKind K1 k)) = (size_Kind K1))).
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
 Hint Rewrite weaken_size_Kind weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Kind weaken_size_Tm weaken_size_Ty : weaken_size.
 Hint Rewrite appendCtx_assoc : interaction.
 Hint Rewrite <- weakenCutoffTmVar_append weakenCutoffTyVar_append weakenTrace_append weakenKind_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.