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
  
  Fixpoint weakenIndexTmVar (x66 : (Index TmVar)) (k : Hvl) {struct k} :
  (Index TmVar) :=
    match k with
      | (H0) => x66
      | (HS a k) => match a with
        | (TmVar) => (IS (weakenIndexTmVar x66 k))
        | _ => (weakenIndexTmVar x66 k)
      end
    end.
  Fixpoint weakenIndexTyVar (X5 : (Index TyVar)) (k : Hvl) {struct k} :
  (Index TyVar) :=
    match k with
      | (H0) => X5
      | (HS a k) => match a with
        | (TyVar) => (IS (weakenIndexTyVar X5 k))
        | _ => (weakenIndexTyVar X5 k)
      end
    end.
  Lemma weakenIndexTmVar_append  :
    (forall (x66 : (Index TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTmVar (weakenIndexTmVar x66 k) k0) = (weakenIndexTmVar x66 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexTyVar_append  :
    (forall (X5 : (Index TyVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTyVar (weakenIndexTyVar X5 k) k0) = (weakenIndexTyVar X5 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Tm : Set :=
    | var (x : (Index TmVar))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | pair (t1 : Tm) (t2 : Tm)
        (S1 : Ty) (T : Ty)
    | prj1 (t : Tm)
    | prj2 (t : Tm)
  with Ty : Set :=
    | tvar (X : (Index TyVar))
    | tpi (T1 : Ty) (T2 : Ty)
    | tapp (T : Ty) (t : Tm)
    | tsig (T : Ty) (U : Ty).
  Scheme ind_Tm := Induction for Tm Sort Prop
  with ind_Ty := Induction for Ty Sort Prop.
  Combined Scheme ind_Tm_Ty from ind_Tm, ind_Ty.
  
  Inductive Kind : Set :=
    | star 
    | kpi (T : Ty) (K : Kind).
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
  Fixpoint shift_TmVar_Index (c : (Cutoff TmVar)) (x66 : (Index TmVar)) {struct c} :
  (Index TmVar) :=
    match c with
      | (C0) => (IS x66)
      | (CS c) => match x66 with
        | (I0) => I0
        | (IS x66) => (IS (shift_TmVar_Index c x66))
      end
    end.
  Fixpoint shift_TyVar_Index (c : (Cutoff TyVar)) (X5 : (Index TyVar)) {struct c} :
  (Index TyVar) :=
    match c with
      | (C0) => (IS X5)
      | (CS c) => match X5 with
        | (I0) => I0
        | (IS X5) => (IS (shift_TyVar_Index c X5))
      end
    end.
  Fixpoint shift_TmVar_Tm (c : (Cutoff TmVar)) (s11 : Tm) {struct s11} :
  Tm :=
    match s11 with
      | (var x66) => (var (shift_TmVar_Index c x66))
      | (abs T86 t76) => (abs (shift_TmVar_Ty c T86) (shift_TmVar_Tm (CS c) t76))
      | (app t77 t78) => (app (shift_TmVar_Tm c t77) (shift_TmVar_Tm c t78))
      | (pair t79 t80 S55 T87) => (pair (shift_TmVar_Tm c t79) (shift_TmVar_Tm c t80) (shift_TmVar_Ty c S55) (shift_TmVar_Ty (CS c) T87))
      | (prj1 t81) => (prj1 (shift_TmVar_Tm c t81))
      | (prj2 t82) => (prj2 (shift_TmVar_Tm c t82))
    end
  with shift_TmVar_Ty (c : (Cutoff TmVar)) (S55 : Ty) {struct S55} :
  Ty :=
    match S55 with
      | (tvar X5) => (tvar X5)
      | (tpi T86 T87) => (tpi (shift_TmVar_Ty c T86) (shift_TmVar_Ty (CS c) T87))
      | (tapp T88 t76) => (tapp (shift_TmVar_Ty c T88) (shift_TmVar_Tm c t76))
      | (tsig T89 U2) => (tsig (shift_TmVar_Ty c T89) (shift_TmVar_Ty (CS c) U2))
    end.
  Fixpoint shift_TyVar_Tm (c : (Cutoff TyVar)) (s11 : Tm) {struct s11} :
  Tm :=
    match s11 with
      | (var x66) => (var x66)
      | (abs T86 t76) => (abs (shift_TyVar_Ty c T86) (shift_TyVar_Tm c t76))
      | (app t77 t78) => (app (shift_TyVar_Tm c t77) (shift_TyVar_Tm c t78))
      | (pair t79 t80 S55 T87) => (pair (shift_TyVar_Tm c t79) (shift_TyVar_Tm c t80) (shift_TyVar_Ty c S55) (shift_TyVar_Ty c T87))
      | (prj1 t81) => (prj1 (shift_TyVar_Tm c t81))
      | (prj2 t82) => (prj2 (shift_TyVar_Tm c t82))
    end
  with shift_TyVar_Ty (c : (Cutoff TyVar)) (S55 : Ty) {struct S55} :
  Ty :=
    match S55 with
      | (tvar X5) => (tvar (shift_TyVar_Index c X5))
      | (tpi T86 T87) => (tpi (shift_TyVar_Ty c T86) (shift_TyVar_Ty c T87))
      | (tapp T88 t76) => (tapp (shift_TyVar_Ty c T88) (shift_TyVar_Tm c t76))
      | (tsig T89 U2) => (tsig (shift_TyVar_Ty c T89) (shift_TyVar_Ty c U2))
    end.
  Fixpoint shift_TmVar_Kind (c : (Cutoff TmVar)) (K42 : Kind) {struct K42} :
  Kind :=
    match K42 with
      | (star) => (star)
      | (kpi T86 K43) => (kpi (shift_TmVar_Ty c T86) (shift_TmVar_Kind (CS c) K43))
    end.
  Fixpoint shift_TyVar_Kind (c : (Cutoff TyVar)) (K42 : Kind) {struct K42} :
  Kind :=
    match K42 with
      | (star) => (star)
      | (kpi T86 K43) => (kpi (shift_TyVar_Ty c T86) (shift_TyVar_Kind c K43))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTm (s11 : Tm) (k : Hvl) {struct k} :
  Tm :=
    match k with
      | (H0) => s11
      | (HS TmVar k) => (shift_TmVar_Tm C0 (weakenTm s11 k))
      | (HS TyVar k) => (shift_TyVar_Tm C0 (weakenTm s11 k))
    end.
  Fixpoint weakenTy (S55 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S55
      | (HS TmVar k) => (shift_TmVar_Ty C0 (weakenTy S55 k))
      | (HS TyVar k) => (shift_TyVar_Ty C0 (weakenTy S55 k))
    end.
  Fixpoint weakenKind (K42 : Kind) (k : Hvl) {struct k} :
  Kind :=
    match k with
      | (H0) => K42
      | (HS TmVar k) => (shift_TmVar_Kind C0 (weakenKind K42 k))
      | (HS TyVar k) => (shift_TyVar_Kind C0 (weakenKind K42 k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T86 : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x66 : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x66
      | (HS b k) => (XS b (weakenTrace x66 k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x66 : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x66 k) k0) = (weakenTrace x66 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint subst_TmVar_Index (d : (Trace TmVar)) (s11 : Tm) (x66 : (Index TmVar)) {struct d} :
  Tm :=
    match d with
      | (X0) => match x66 with
        | (I0) => s11
        | (IS x66) => (var x66)
      end
      | (XS TmVar d) => match x66 with
        | (I0) => (var I0)
        | (IS x66) => (shift_TmVar_Tm C0 (subst_TmVar_Index d s11 x66))
      end
      | (XS TyVar d) => (shift_TyVar_Tm C0 (subst_TmVar_Index d s11 x66))
    end.
  Fixpoint subst_TyVar_Index (d : (Trace TyVar)) (S55 : Ty) (X5 : (Index TyVar)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X5 with
        | (I0) => S55
        | (IS X5) => (tvar X5)
      end
      | (XS TmVar d) => (shift_TmVar_Ty C0 (subst_TyVar_Index d S55 X5))
      | (XS TyVar d) => match X5 with
        | (I0) => (tvar I0)
        | (IS X5) => (shift_TyVar_Ty C0 (subst_TyVar_Index d S55 X5))
      end
    end.
  Fixpoint subst_TmVar_Tm (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) {struct s12} :
  Tm :=
    match s12 with
      | (var x66) => (subst_TmVar_Index d s11 x66)
      | (abs T86 t76) => (abs (subst_TmVar_Ty d s11 T86) (subst_TmVar_Tm (weakenTrace d (HS TmVar H0)) s11 t76))
      | (app t77 t78) => (app (subst_TmVar_Tm d s11 t77) (subst_TmVar_Tm d s11 t78))
      | (pair t79 t80 S55 T87) => (pair (subst_TmVar_Tm d s11 t79) (subst_TmVar_Tm d s11 t80) (subst_TmVar_Ty d s11 S55) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s11 T87))
      | (prj1 t81) => (prj1 (subst_TmVar_Tm d s11 t81))
      | (prj2 t82) => (prj2 (subst_TmVar_Tm d s11 t82))
    end
  with subst_TmVar_Ty (d : (Trace TmVar)) (s11 : Tm) (S55 : Ty) {struct S55} :
  Ty :=
    match S55 with
      | (tvar X5) => (tvar X5)
      | (tpi T86 T87) => (tpi (subst_TmVar_Ty d s11 T86) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s11 T87))
      | (tapp T88 t76) => (tapp (subst_TmVar_Ty d s11 T88) (subst_TmVar_Tm d s11 t76))
      | (tsig T89 U2) => (tsig (subst_TmVar_Ty d s11 T89) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s11 U2))
    end.
  Fixpoint subst_TyVar_Tm (d : (Trace TyVar)) (S55 : Ty) (s11 : Tm) {struct s11} :
  Tm :=
    match s11 with
      | (var x66) => (var x66)
      | (abs T86 t76) => (abs (subst_TyVar_Ty d S55 T86) (subst_TyVar_Tm (weakenTrace d (HS TmVar H0)) S55 t76))
      | (app t77 t78) => (app (subst_TyVar_Tm d S55 t77) (subst_TyVar_Tm d S55 t78))
      | (pair t79 t80 S56 T87) => (pair (subst_TyVar_Tm d S55 t79) (subst_TyVar_Tm d S55 t80) (subst_TyVar_Ty d S55 S56) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S55 T87))
      | (prj1 t81) => (prj1 (subst_TyVar_Tm d S55 t81))
      | (prj2 t82) => (prj2 (subst_TyVar_Tm d S55 t82))
    end
  with subst_TyVar_Ty (d : (Trace TyVar)) (S55 : Ty) (S56 : Ty) {struct S56} :
  Ty :=
    match S56 with
      | (tvar X5) => (subst_TyVar_Index d S55 X5)
      | (tpi T86 T87) => (tpi (subst_TyVar_Ty d S55 T86) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S55 T87))
      | (tapp T88 t76) => (tapp (subst_TyVar_Ty d S55 T88) (subst_TyVar_Tm d S55 t76))
      | (tsig T89 U2) => (tsig (subst_TyVar_Ty d S55 T89) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S55 U2))
    end.
  Fixpoint subst_TmVar_Kind (d : (Trace TmVar)) (s11 : Tm) (K42 : Kind) {struct K42} :
  Kind :=
    match K42 with
      | (star) => (star)
      | (kpi T86 K43) => (kpi (subst_TmVar_Ty d s11 T86) (subst_TmVar_Kind (weakenTrace d (HS TmVar H0)) s11 K43))
    end.
  Fixpoint subst_TyVar_Kind (d : (Trace TyVar)) (S55 : Ty) (K42 : Kind) {struct K42} :
  Kind :=
    match K42 with
      | (star) => (star)
      | (kpi T86 K43) => (kpi (subst_TyVar_Ty d S55 T86) (subst_TyVar_Kind (weakenTrace d (HS TmVar H0)) S55 K43))
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
  Lemma subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind (s11 : Tm) :
    (forall (k : Hvl) (x66 : (Index TmVar)) ,
      ((subst_TmVar_Index (weakenTrace X0 k) s11 (shift_TmVar_Index (weakenCutoffTmVar C0 k) x66)) = (var x66))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma subst_TyVar_Index0_shift_TyVar_Index0_reflection_ind (S55 : Ty) :
    (forall (k : Hvl) (X5 : (Index TyVar)) ,
      ((subst_TyVar_Index (weakenTrace X0 k) S55 (shift_TyVar_Index (weakenCutoffTyVar C0 k) X5)) = (tvar X5))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind (s12 : Tm) (k : Hvl) (s11 : Tm) {struct s12} :
  ((subst_TmVar_Tm (weakenTrace X0 k) s11 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s12)) = s12) :=
    match s12 return ((subst_TmVar_Tm (weakenTrace X0 k) s11 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s12)) = s12) with
      | (var x66) => (subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind s11 k x66)
      | (abs T86 t76) => (f_equal2 abs (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T86 k s11) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t76 (HS TmVar k) s11)))
      | (app t77 t78) => (f_equal2 app (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t77 k s11) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t78 k s11))
      | (pair t77 t78 S55 T86) => (f_equal4 pair (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t77 k s11) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t78 k s11) (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind S55 k s11) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T86 (HS TmVar k) s11)))
      | (prj1 t76) => (f_equal prj1 (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t76 k s11))
      | (prj2 t76) => (f_equal prj2 (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t76 k s11))
    end
  with subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind (S56 : Ty) (k : Hvl) (s11 : Tm) {struct S56} :
  ((subst_TmVar_Ty (weakenTrace X0 k) s11 (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S56)) = S56) :=
    match S56 return ((subst_TmVar_Ty (weakenTrace X0 k) s11 (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S56)) = S56) with
      | (tvar X5) => eq_refl
      | (tpi T88 T89) => (f_equal2 tpi (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T88 k s11) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T89 (HS TmVar k) s11)))
      | (tapp T87 t79) => (f_equal2 tapp (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T87 k s11) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t79 k s11))
      | (tsig T87 U2) => (f_equal2 tsig (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T87 k s11) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind U2 (HS TmVar k) s11)))
    end.
  Fixpoint subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind (s11 : Tm) (k : Hvl) (S55 : Ty) {struct s11} :
  ((subst_TyVar_Tm (weakenTrace X0 k) S55 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s11)) = s11) :=
    match s11 return ((subst_TyVar_Tm (weakenTrace X0 k) S55 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s11)) = s11) with
      | (var x66) => eq_refl
      | (abs T86 t76) => (f_equal2 abs (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T86 k S55) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t76 (HS TmVar k) S55)))
      | (app t77 t78) => (f_equal2 app (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t77 k S55) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t78 k S55))
      | (pair t77 t78 S56 T86) => (f_equal4 pair (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t77 k S55) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t78 k S55) (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind S56 k S55) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T86 (HS TmVar k) S55)))
      | (prj1 t76) => (f_equal prj1 (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t76 k S55))
      | (prj2 t76) => (f_equal prj2 (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t76 k S55))
    end
  with subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind (S57 : Ty) (k : Hvl) (S55 : Ty) {struct S57} :
  ((subst_TyVar_Ty (weakenTrace X0 k) S55 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S57)) = S57) :=
    match S57 return ((subst_TyVar_Ty (weakenTrace X0 k) S55 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S57)) = S57) with
      | (tvar X5) => (subst_TyVar_Index0_shift_TyVar_Index0_reflection_ind S55 k X5)
      | (tpi T88 T89) => (f_equal2 tpi (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T88 k S55) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T89 (HS TmVar k) S55)))
      | (tapp T87 t79) => (f_equal2 tapp (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T87 k S55) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t79 k S55))
      | (tsig T87 U2) => (f_equal2 tsig (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T87 k S55) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind U2 (HS TmVar k) S55)))
    end.
  Fixpoint subst_TmVar_0_shift_TmVar_0_Kind_reflection_ind (K42 : Kind) (k : Hvl) (s11 : Tm) {struct K42} :
  ((subst_TmVar_Kind (weakenTrace X0 k) s11 (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K42)) = K42) :=
    match K42 return ((subst_TmVar_Kind (weakenTrace X0 k) s11 (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K42)) = K42) with
      | (star) => eq_refl
      | (kpi T86 K43) => (f_equal2 kpi (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T86 k s11) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Kind_reflection_ind K43 (HS TmVar k) s11)))
    end.
  Fixpoint subst_TyVar_0_shift_TyVar_0_Kind_reflection_ind (K42 : Kind) (k : Hvl) (S55 : Ty) {struct K42} :
  ((subst_TyVar_Kind (weakenTrace X0 k) S55 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K42)) = K42) :=
    match K42 return ((subst_TyVar_Kind (weakenTrace X0 k) S55 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K42)) = K42) with
      | (star) => eq_refl
      | (kpi T86 K43) => (f_equal2 kpi (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T86 k S55) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Kind_reflection_ind K43 (HS TmVar k) S55)))
    end.
  Definition subst_TmVar_Tm0_shift_TmVar_Tm0_reflection (s12 : Tm) : (forall (s11 : Tm) ,
    ((subst_TmVar_Tm X0 s11 (shift_TmVar_Tm C0 s12)) = s12)) := (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind s12 H0).
  Definition subst_TmVar_Ty0_shift_TmVar_Ty0_reflection (S55 : Ty) : (forall (s11 : Tm) ,
    ((subst_TmVar_Ty X0 s11 (shift_TmVar_Ty C0 S55)) = S55)) := (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind S55 H0).
  Definition subst_TyVar_Tm0_shift_TyVar_Tm0_reflection (s11 : Tm) : (forall (S55 : Ty) ,
    ((subst_TyVar_Tm X0 S55 (shift_TyVar_Tm C0 s11)) = s11)) := (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind s11 H0).
  Definition subst_TyVar_Ty0_shift_TyVar_Ty0_reflection (S56 : Ty) : (forall (S55 : Ty) ,
    ((subst_TyVar_Ty X0 S55 (shift_TyVar_Ty C0 S56)) = S56)) := (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind S56 H0).
  Definition subst_TmVar_Kind0_shift_TmVar_Kind0_reflection (K42 : Kind) : (forall (s11 : Tm) ,
    ((subst_TmVar_Kind X0 s11 (shift_TmVar_Kind C0 K42)) = K42)) := (subst_TmVar_0_shift_TmVar_0_Kind_reflection_ind K42 H0).
  Definition subst_TyVar_Kind0_shift_TyVar_Kind0_reflection (K42 : Kind) : (forall (S55 : Ty) ,
    ((subst_TyVar_Kind X0 S55 (shift_TyVar_Kind C0 K42)) = K42)) := (subst_TyVar_0_shift_TyVar_0_Kind_reflection_ind K42 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shift_TmVar_Index_shift_TmVar_Index0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff TmVar)) (x66 : (Index TmVar)) ,
        ((shift_TmVar_Index (weakenCutoffTmVar (CS c) k) (shift_TmVar_Index (weakenCutoffTmVar C0 k) x66)) = (shift_TmVar_Index (weakenCutoffTmVar C0 k) (shift_TmVar_Index (weakenCutoffTmVar c k) x66)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma shift_TyVar_Index_shift_TyVar_Index0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff TyVar)) (X5 : (Index TyVar)) ,
        ((shift_TyVar_Index (weakenCutoffTyVar (CS c) k) (shift_TyVar_Index (weakenCutoffTyVar C0 k) X5)) = (shift_TyVar_Index (weakenCutoffTyVar C0 k) (shift_TyVar_Index (weakenCutoffTyVar c k) X5)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint shift_TmVar__shift_TmVar_0_Tm_comm_ind (s11 : Tm) (k : Hvl) (c : (Cutoff TmVar)) {struct s11} :
    ((shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s11)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s11))) :=
      match s11 return ((shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s11)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s11))) with
        | (var x66) => (f_equal var (shift_TmVar_Index_shift_TmVar_Index0_comm_ind k c x66))
        | (abs T86 t76) => (f_equal2 abs (shift_TmVar__shift_TmVar_0_Ty_comm_ind T86 k c) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t76 (HS TmVar k) c))
        | (app t77 t78) => (f_equal2 app (shift_TmVar__shift_TmVar_0_Tm_comm_ind t77 k c) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t78 k c))
        | (pair t77 t78 S55 T86) => (f_equal4 pair (shift_TmVar__shift_TmVar_0_Tm_comm_ind t77 k c) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t78 k c) (shift_TmVar__shift_TmVar_0_Ty_comm_ind S55 k c) (shift_TmVar__shift_TmVar_0_Ty_comm_ind T86 (HS TmVar k) c))
        | (prj1 t76) => (f_equal prj1 (shift_TmVar__shift_TmVar_0_Tm_comm_ind t76 k c))
        | (prj2 t76) => (f_equal prj2 (shift_TmVar__shift_TmVar_0_Tm_comm_ind t76 k c))
      end
    with shift_TmVar__shift_TmVar_0_Ty_comm_ind (S56 : Ty) (k : Hvl) (c : (Cutoff TmVar)) {struct S56} :
    ((shift_TmVar_Ty (weakenCutoffTmVar (CS c) k) (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S56)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (shift_TmVar_Ty (weakenCutoffTmVar c k) S56))) :=
      match S56 return ((shift_TmVar_Ty (weakenCutoffTmVar (CS c) k) (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S56)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (shift_TmVar_Ty (weakenCutoffTmVar c k) S56))) with
        | (tvar X5) => eq_refl
        | (tpi T88 T89) => (f_equal2 tpi (shift_TmVar__shift_TmVar_0_Ty_comm_ind T88 k c) (shift_TmVar__shift_TmVar_0_Ty_comm_ind T89 (HS TmVar k) c))
        | (tapp T87 t79) => (f_equal2 tapp (shift_TmVar__shift_TmVar_0_Ty_comm_ind T87 k c) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t79 k c))
        | (tsig T87 U2) => (f_equal2 tsig (shift_TmVar__shift_TmVar_0_Ty_comm_ind T87 k c) (shift_TmVar__shift_TmVar_0_Ty_comm_ind U2 (HS TmVar k) c))
      end.
    Fixpoint shift_TmVar__shift_TyVar_0_Tm_comm_ind (s11 : Tm) (k : Hvl) (c : (Cutoff TmVar)) {struct s11} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s11)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s11))) :=
      match s11 return ((shift_TmVar_Tm (weakenCutoffTmVar c k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s11)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c k) s11))) with
        | (var x66) => eq_refl
        | (abs T86 t76) => (f_equal2 abs (shift_TmVar__shift_TyVar_0_Ty_comm_ind T86 k c) (shift_TmVar__shift_TyVar_0_Tm_comm_ind t76 (HS TmVar k) c))
        | (app t77 t78) => (f_equal2 app (shift_TmVar__shift_TyVar_0_Tm_comm_ind t77 k c) (shift_TmVar__shift_TyVar_0_Tm_comm_ind t78 k c))
        | (pair t77 t78 S55 T86) => (f_equal4 pair (shift_TmVar__shift_TyVar_0_Tm_comm_ind t77 k c) (shift_TmVar__shift_TyVar_0_Tm_comm_ind t78 k c) (shift_TmVar__shift_TyVar_0_Ty_comm_ind S55 k c) (shift_TmVar__shift_TyVar_0_Ty_comm_ind T86 (HS TmVar k) c))
        | (prj1 t76) => (f_equal prj1 (shift_TmVar__shift_TyVar_0_Tm_comm_ind t76 k c))
        | (prj2 t76) => (f_equal prj2 (shift_TmVar__shift_TyVar_0_Tm_comm_ind t76 k c))
      end
    with shift_TmVar__shift_TyVar_0_Ty_comm_ind (S56 : Ty) (k : Hvl) (c : (Cutoff TmVar)) {struct S56} :
    ((shift_TmVar_Ty (weakenCutoffTmVar c k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S56)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TmVar_Ty (weakenCutoffTmVar c k) S56))) :=
      match S56 return ((shift_TmVar_Ty (weakenCutoffTmVar c k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S56)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TmVar_Ty (weakenCutoffTmVar c k) S56))) with
        | (tvar X5) => eq_refl
        | (tpi T88 T89) => (f_equal2 tpi (shift_TmVar__shift_TyVar_0_Ty_comm_ind T88 k c) (shift_TmVar__shift_TyVar_0_Ty_comm_ind T89 (HS TmVar k) c))
        | (tapp T87 t79) => (f_equal2 tapp (shift_TmVar__shift_TyVar_0_Ty_comm_ind T87 k c) (shift_TmVar__shift_TyVar_0_Tm_comm_ind t79 k c))
        | (tsig T87 U2) => (f_equal2 tsig (shift_TmVar__shift_TyVar_0_Ty_comm_ind T87 k c) (shift_TmVar__shift_TyVar_0_Ty_comm_ind U2 (HS TmVar k) c))
      end.
    Fixpoint shift_TyVar__shift_TmVar_0_Tm_comm_ind (s11 : Tm) (k : Hvl) (c : (Cutoff TyVar)) {struct s11} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s11)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c k) s11))) :=
      match s11 return ((shift_TyVar_Tm (weakenCutoffTyVar c k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s11)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c k) s11))) with
        | (var x66) => eq_refl
        | (abs T86 t76) => (f_equal2 abs (shift_TyVar__shift_TmVar_0_Ty_comm_ind T86 k c) (shift_TyVar__shift_TmVar_0_Tm_comm_ind t76 (HS TmVar k) c))
        | (app t77 t78) => (f_equal2 app (shift_TyVar__shift_TmVar_0_Tm_comm_ind t77 k c) (shift_TyVar__shift_TmVar_0_Tm_comm_ind t78 k c))
        | (pair t77 t78 S55 T86) => (f_equal4 pair (shift_TyVar__shift_TmVar_0_Tm_comm_ind t77 k c) (shift_TyVar__shift_TmVar_0_Tm_comm_ind t78 k c) (shift_TyVar__shift_TmVar_0_Ty_comm_ind S55 k c) (shift_TyVar__shift_TmVar_0_Ty_comm_ind T86 (HS TmVar k) c))
        | (prj1 t76) => (f_equal prj1 (shift_TyVar__shift_TmVar_0_Tm_comm_ind t76 k c))
        | (prj2 t76) => (f_equal prj2 (shift_TyVar__shift_TmVar_0_Tm_comm_ind t76 k c))
      end
    with shift_TyVar__shift_TmVar_0_Ty_comm_ind (S56 : Ty) (k : Hvl) (c : (Cutoff TyVar)) {struct S56} :
    ((shift_TyVar_Ty (weakenCutoffTyVar c k) (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S56)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c k) S56))) :=
      match S56 return ((shift_TyVar_Ty (weakenCutoffTyVar c k) (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S56)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c k) S56))) with
        | (tvar X5) => eq_refl
        | (tpi T88 T89) => (f_equal2 tpi (shift_TyVar__shift_TmVar_0_Ty_comm_ind T88 k c) (shift_TyVar__shift_TmVar_0_Ty_comm_ind T89 (HS TmVar k) c))
        | (tapp T87 t79) => (f_equal2 tapp (shift_TyVar__shift_TmVar_0_Ty_comm_ind T87 k c) (shift_TyVar__shift_TmVar_0_Tm_comm_ind t79 k c))
        | (tsig T87 U2) => (f_equal2 tsig (shift_TyVar__shift_TmVar_0_Ty_comm_ind T87 k c) (shift_TyVar__shift_TmVar_0_Ty_comm_ind U2 (HS TmVar k) c))
      end.
    Fixpoint shift_TyVar__shift_TyVar_0_Tm_comm_ind (s11 : Tm) (k : Hvl) (c : (Cutoff TyVar)) {struct s11} :
    ((shift_TyVar_Tm (weakenCutoffTyVar (CS c) k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s11)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c k) s11))) :=
      match s11 return ((shift_TyVar_Tm (weakenCutoffTyVar (CS c) k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s11)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c k) s11))) with
        | (var x66) => eq_refl
        | (abs T86 t76) => (f_equal2 abs (shift_TyVar__shift_TyVar_0_Ty_comm_ind T86 k c) (shift_TyVar__shift_TyVar_0_Tm_comm_ind t76 (HS TmVar k) c))
        | (app t77 t78) => (f_equal2 app (shift_TyVar__shift_TyVar_0_Tm_comm_ind t77 k c) (shift_TyVar__shift_TyVar_0_Tm_comm_ind t78 k c))
        | (pair t77 t78 S55 T86) => (f_equal4 pair (shift_TyVar__shift_TyVar_0_Tm_comm_ind t77 k c) (shift_TyVar__shift_TyVar_0_Tm_comm_ind t78 k c) (shift_TyVar__shift_TyVar_0_Ty_comm_ind S55 k c) (shift_TyVar__shift_TyVar_0_Ty_comm_ind T86 (HS TmVar k) c))
        | (prj1 t76) => (f_equal prj1 (shift_TyVar__shift_TyVar_0_Tm_comm_ind t76 k c))
        | (prj2 t76) => (f_equal prj2 (shift_TyVar__shift_TyVar_0_Tm_comm_ind t76 k c))
      end
    with shift_TyVar__shift_TyVar_0_Ty_comm_ind (S56 : Ty) (k : Hvl) (c : (Cutoff TyVar)) {struct S56} :
    ((shift_TyVar_Ty (weakenCutoffTyVar (CS c) k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S56)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c k) S56))) :=
      match S56 return ((shift_TyVar_Ty (weakenCutoffTyVar (CS c) k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S56)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c k) S56))) with
        | (tvar X5) => (f_equal tvar (shift_TyVar_Index_shift_TyVar_Index0_comm_ind k c X5))
        | (tpi T88 T89) => (f_equal2 tpi (shift_TyVar__shift_TyVar_0_Ty_comm_ind T88 k c) (shift_TyVar__shift_TyVar_0_Ty_comm_ind T89 (HS TmVar k) c))
        | (tapp T87 t79) => (f_equal2 tapp (shift_TyVar__shift_TyVar_0_Ty_comm_ind T87 k c) (shift_TyVar__shift_TyVar_0_Tm_comm_ind t79 k c))
        | (tsig T87 U2) => (f_equal2 tsig (shift_TyVar__shift_TyVar_0_Ty_comm_ind T87 k c) (shift_TyVar__shift_TyVar_0_Ty_comm_ind U2 (HS TmVar k) c))
      end.
    Fixpoint shift_TmVar__shift_TmVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TmVar)) {struct K42} :
    ((shift_TmVar_Kind (weakenCutoffTmVar (CS c) k) (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K42)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (shift_TmVar_Kind (weakenCutoffTmVar c k) K42))) :=
      match K42 return ((shift_TmVar_Kind (weakenCutoffTmVar (CS c) k) (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K42)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (shift_TmVar_Kind (weakenCutoffTmVar c k) K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (shift_TmVar__shift_TmVar_0_Ty_comm_ind T86 k c) (shift_TmVar__shift_TmVar_0_Kind_comm_ind K43 (HS TmVar k) c))
      end.
    Fixpoint shift_TmVar__shift_TyVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TmVar)) {struct K42} :
    ((shift_TmVar_Kind (weakenCutoffTmVar c k) (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K42)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (shift_TmVar_Kind (weakenCutoffTmVar c k) K42))) :=
      match K42 return ((shift_TmVar_Kind (weakenCutoffTmVar c k) (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K42)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (shift_TmVar_Kind (weakenCutoffTmVar c k) K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (shift_TmVar__shift_TyVar_0_Ty_comm_ind T86 k c) (shift_TmVar__shift_TyVar_0_Kind_comm_ind K43 (HS TmVar k) c))
      end.
    Fixpoint shift_TyVar__shift_TmVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TyVar)) {struct K42} :
    ((shift_TyVar_Kind (weakenCutoffTyVar c k) (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K42)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (shift_TyVar_Kind (weakenCutoffTyVar c k) K42))) :=
      match K42 return ((shift_TyVar_Kind (weakenCutoffTyVar c k) (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K42)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (shift_TyVar_Kind (weakenCutoffTyVar c k) K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (shift_TyVar__shift_TmVar_0_Ty_comm_ind T86 k c) (shift_TyVar__shift_TmVar_0_Kind_comm_ind K43 (HS TmVar k) c))
      end.
    Fixpoint shift_TyVar__shift_TyVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TyVar)) {struct K42} :
    ((shift_TyVar_Kind (weakenCutoffTyVar (CS c) k) (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K42)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (shift_TyVar_Kind (weakenCutoffTyVar c k) K42))) :=
      match K42 return ((shift_TyVar_Kind (weakenCutoffTyVar (CS c) k) (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K42)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (shift_TyVar_Kind (weakenCutoffTyVar c k) K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (shift_TyVar__shift_TyVar_0_Ty_comm_ind T86 k c) (shift_TyVar__shift_TyVar_0_Kind_comm_ind K43 (HS TmVar k) c))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition shift_TmVar__shift_TmVar_0_Tm_comm (s11 : Tm) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Tm (CS c) (shift_TmVar_Tm C0 s11)) = (shift_TmVar_Tm C0 (shift_TmVar_Tm c s11)))) := (shift_TmVar__shift_TmVar_0_Tm_comm_ind s11 H0).
    Definition shift_TmVar__shift_TmVar_0_Ty_comm (S55 : Ty) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Ty (CS c) (shift_TmVar_Ty C0 S55)) = (shift_TmVar_Ty C0 (shift_TmVar_Ty c S55)))) := (shift_TmVar__shift_TmVar_0_Ty_comm_ind S55 H0).
    Definition shift_TmVar__shift_TyVar_0_Tm_comm (s11 : Tm) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Tm c (shift_TyVar_Tm C0 s11)) = (shift_TyVar_Tm C0 (shift_TmVar_Tm c s11)))) := (shift_TmVar__shift_TyVar_0_Tm_comm_ind s11 H0).
    Definition shift_TmVar__shift_TyVar_0_Ty_comm (S55 : Ty) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Ty c (shift_TyVar_Ty C0 S55)) = (shift_TyVar_Ty C0 (shift_TmVar_Ty c S55)))) := (shift_TmVar__shift_TyVar_0_Ty_comm_ind S55 H0).
    Definition shift_TyVar__shift_TmVar_0_Tm_comm (s11 : Tm) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Tm c (shift_TmVar_Tm C0 s11)) = (shift_TmVar_Tm C0 (shift_TyVar_Tm c s11)))) := (shift_TyVar__shift_TmVar_0_Tm_comm_ind s11 H0).
    Definition shift_TyVar__shift_TmVar_0_Ty_comm (S55 : Ty) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Ty c (shift_TmVar_Ty C0 S55)) = (shift_TmVar_Ty C0 (shift_TyVar_Ty c S55)))) := (shift_TyVar__shift_TmVar_0_Ty_comm_ind S55 H0).
    Definition shift_TyVar__shift_TyVar_0_Tm_comm (s11 : Tm) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Tm (CS c) (shift_TyVar_Tm C0 s11)) = (shift_TyVar_Tm C0 (shift_TyVar_Tm c s11)))) := (shift_TyVar__shift_TyVar_0_Tm_comm_ind s11 H0).
    Definition shift_TyVar__shift_TyVar_0_Ty_comm (S55 : Ty) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Ty (CS c) (shift_TyVar_Ty C0 S55)) = (shift_TyVar_Ty C0 (shift_TyVar_Ty c S55)))) := (shift_TyVar__shift_TyVar_0_Ty_comm_ind S55 H0).
    Definition shift_TmVar__shift_TmVar_0_Kind_comm (K42 : Kind) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Kind (CS c) (shift_TmVar_Kind C0 K42)) = (shift_TmVar_Kind C0 (shift_TmVar_Kind c K42)))) := (shift_TmVar__shift_TmVar_0_Kind_comm_ind K42 H0).
    Definition shift_TmVar__shift_TyVar_0_Kind_comm (K42 : Kind) : (forall (c : (Cutoff TmVar)) ,
      ((shift_TmVar_Kind c (shift_TyVar_Kind C0 K42)) = (shift_TyVar_Kind C0 (shift_TmVar_Kind c K42)))) := (shift_TmVar__shift_TyVar_0_Kind_comm_ind K42 H0).
    Definition shift_TyVar__shift_TmVar_0_Kind_comm (K42 : Kind) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Kind c (shift_TmVar_Kind C0 K42)) = (shift_TmVar_Kind C0 (shift_TyVar_Kind c K42)))) := (shift_TyVar__shift_TmVar_0_Kind_comm_ind K42 H0).
    Definition shift_TyVar__shift_TyVar_0_Kind_comm (K42 : Kind) : (forall (c : (Cutoff TyVar)) ,
      ((shift_TyVar_Kind (CS c) (shift_TyVar_Kind C0 K42)) = (shift_TyVar_Kind C0 (shift_TyVar_Kind c K42)))) := (shift_TyVar__shift_TyVar_0_Kind_comm_ind K42 H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_TmVar__shift_TmVar_0_Kind_comm shift_TmVar__shift_TyVar_0_Kind_comm shift_TyVar__shift_TmVar_0_Kind_comm shift_TyVar__shift_TyVar_0_Kind_comm shift_TmVar__shift_TmVar_0_Tm_comm shift_TmVar__shift_TyVar_0_Tm_comm shift_TyVar__shift_TmVar_0_Tm_comm shift_TyVar__shift_TyVar_0_Tm_comm shift_TmVar__shift_TmVar_0_Ty_comm shift_TmVar__shift_TyVar_0_Ty_comm shift_TyVar__shift_TmVar_0_Ty_comm shift_TyVar__shift_TyVar_0_Ty_comm : interaction.
 Hint Rewrite shift_TmVar__shift_TmVar_0_Kind_comm shift_TmVar__shift_TyVar_0_Kind_comm shift_TyVar__shift_TmVar_0_Kind_comm shift_TyVar__shift_TyVar_0_Kind_comm shift_TmVar__shift_TmVar_0_Tm_comm shift_TmVar__shift_TyVar_0_Tm_comm shift_TyVar__shift_TmVar_0_Tm_comm shift_TyVar__shift_TyVar_0_Tm_comm shift_TmVar__shift_TmVar_0_Ty_comm shift_TmVar__shift_TyVar_0_Ty_comm shift_TyVar__shift_TmVar_0_Ty_comm shift_TyVar__shift_TyVar_0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTm_shift_TmVar_Tm  :
    (forall (k : Hvl) (c : (Cutoff TmVar)) (s11 : Tm) ,
      ((weakenTm (shift_TmVar_Tm c s11) k) = (shift_TmVar_Tm (weakenCutoffTmVar c k) (weakenTm s11 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTy_shift_TmVar_Ty  :
    (forall (k : Hvl) (c : (Cutoff TmVar)) (S55 : Ty) ,
      ((weakenTy (shift_TmVar_Ty c S55) k) = (shift_TmVar_Ty (weakenCutoffTmVar c k) (weakenTy S55 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shift_TyVar_Tm  :
    (forall (k : Hvl) (c : (Cutoff TyVar)) (s11 : Tm) ,
      ((weakenTm (shift_TyVar_Tm c s11) k) = (shift_TyVar_Tm (weakenCutoffTyVar c k) (weakenTm s11 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTy_shift_TyVar_Ty  :
    (forall (k : Hvl) (c : (Cutoff TyVar)) (S55 : Ty) ,
      ((weakenTy (shift_TyVar_Ty c S55) k) = (shift_TyVar_Ty (weakenCutoffTyVar c k) (weakenTy S55 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenKind_shift_TmVar_Kind  :
    (forall (k : Hvl) (c : (Cutoff TmVar)) (K42 : Kind) ,
      ((weakenKind (shift_TmVar_Kind c K42) k) = (shift_TmVar_Kind (weakenCutoffTmVar c k) (weakenKind K42 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenKind_shift_TyVar_Kind  :
    (forall (k : Hvl) (c : (Cutoff TyVar)) (K42 : Kind) ,
      ((weakenKind (shift_TyVar_Kind c K42) k) = (shift_TyVar_Kind (weakenCutoffTyVar c k) (weakenKind K42 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shift_TmVar_Tm_subst_TmVar_Index0_comm_ind (c : (Cutoff TmVar)) (s11 : Tm) :
      (forall (k : Hvl) (x66 : (Index TmVar)) ,
        ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Index (weakenTrace X0 k) s11 x66)) = (subst_TmVar_Index (weakenTrace X0 k) (shift_TmVar_Tm c s11) (shift_TmVar_Index (weakenCutoffTmVar (CS c) k) x66)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TyVar_Tm_subst_TmVar_Index0_comm_ind (c : (Cutoff TyVar)) (s11 : Tm) :
      (forall (k : Hvl) (x66 : (Index TmVar)) ,
        ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TmVar_Index (weakenTrace X0 k) s11 x66)) = (subst_TmVar_Index (weakenTrace X0 k) (shift_TyVar_Tm c s11) x66))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TmVar_Ty_subst_TyVar_Index0_comm_ind (c : (Cutoff TmVar)) (S55 : Ty) :
      (forall (k : Hvl) (X5 : (Index TyVar)) ,
        ((shift_TmVar_Ty (weakenCutoffTmVar c k) (subst_TyVar_Index (weakenTrace X0 k) S55 X5)) = (subst_TyVar_Index (weakenTrace X0 k) (shift_TmVar_Ty c S55) X5))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TyVar_Ty_subst_TyVar_Index0_comm_ind (c : (Cutoff TyVar)) (S55 : Ty) :
      (forall (k : Hvl) (X5 : (Index TyVar)) ,
        ((shift_TyVar_Ty (weakenCutoffTyVar c k) (subst_TyVar_Index (weakenTrace X0 k) S55 X5)) = (subst_TyVar_Index (weakenTrace X0 k) (shift_TyVar_Ty c S55) (shift_TyVar_Index (weakenCutoffTyVar (CS c) k) X5)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint shift_TmVar__subst_TmVar_0_Tm_comm_ind (s12 : Tm) (k : Hvl) (c : (Cutoff TmVar)) (s11 : Tm) {struct s12} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s11 s12)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c s11) (shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) s12))) :=
      match s12 return ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s11 s12)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c s11) (shift_TmVar_Tm (weakenCutoffTmVar (CS c) k) s12))) with
        | (var x66) => (shift_TmVar_Tm_subst_TmVar_Index0_comm_ind c s11 k x66)
        | (abs T86 t76) => (f_equal2 abs (shift_TmVar__subst_TmVar_0_Ty_comm_ind T86 k c s11) (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind t76 (HS TmVar k) c s11) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (app t77 t78) => (f_equal2 app (shift_TmVar__subst_TmVar_0_Tm_comm_ind t77 k c s11) (shift_TmVar__subst_TmVar_0_Tm_comm_ind t78 k c s11))
        | (pair t77 t78 S55 T86) => (f_equal4 pair (shift_TmVar__subst_TmVar_0_Tm_comm_ind t77 k c s11) (shift_TmVar__subst_TmVar_0_Tm_comm_ind t78 k c s11) (shift_TmVar__subst_TmVar_0_Ty_comm_ind S55 k c s11) (eq_trans (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Ty_comm_ind T86 (HS TmVar k) c s11) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (prj1 t76) => (f_equal prj1 (shift_TmVar__subst_TmVar_0_Tm_comm_ind t76 k c s11))
        | (prj2 t76) => (f_equal prj2 (shift_TmVar__subst_TmVar_0_Tm_comm_ind t76 k c s11))
      end
    with shift_TmVar__subst_TmVar_0_Ty_comm_ind (S56 : Ty) (k : Hvl) (c : (Cutoff TmVar)) (s11 : Tm) {struct S56} :
    ((shift_TmVar_Ty (weakenCutoffTmVar c k) (subst_TmVar_Ty (weakenTrace X0 k) s11 S56)) = (subst_TmVar_Ty (weakenTrace X0 k) (shift_TmVar_Tm c s11) (shift_TmVar_Ty (weakenCutoffTmVar (CS c) k) S56))) :=
      match S56 return ((shift_TmVar_Ty (weakenCutoffTmVar c k) (subst_TmVar_Ty (weakenTrace X0 k) s11 S56)) = (subst_TmVar_Ty (weakenTrace X0 k) (shift_TmVar_Tm c s11) (shift_TmVar_Ty (weakenCutoffTmVar (CS c) k) S56))) with
        | (tvar X5) => eq_refl
        | (tpi T88 T89) => (f_equal2 tpi (shift_TmVar__subst_TmVar_0_Ty_comm_ind T88 k c s11) (eq_trans (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Ty_comm_ind T89 (HS TmVar k) c s11) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (tapp T87 t79) => (f_equal2 tapp (shift_TmVar__subst_TmVar_0_Ty_comm_ind T87 k c s11) (shift_TmVar__subst_TmVar_0_Tm_comm_ind t79 k c s11))
        | (tsig T87 U2) => (f_equal2 tsig (shift_TmVar__subst_TmVar_0_Ty_comm_ind T87 k c s11) (eq_trans (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Ty_comm_ind U2 (HS TmVar k) c s11) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_TmVar__subst_TyVar_0_Tm_comm_ind (s11 : Tm) (k : Hvl) (c : (Cutoff TmVar)) (S55 : Ty) {struct s11} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S55 s11)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TmVar_Ty c S55) (shift_TmVar_Tm (weakenCutoffTmVar c k) s11))) :=
      match s11 return ((shift_TmVar_Tm (weakenCutoffTmVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S55 s11)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TmVar_Ty c S55) (shift_TmVar_Tm (weakenCutoffTmVar c k) s11))) with
        | (var x66) => eq_refl
        | (abs T86 t76) => (f_equal2 abs (shift_TmVar__subst_TyVar_0_Ty_comm_ind T86 k c S55) (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Tm_comm_ind t76 (HS TmVar k) c S55) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (app t77 t78) => (f_equal2 app (shift_TmVar__subst_TyVar_0_Tm_comm_ind t77 k c S55) (shift_TmVar__subst_TyVar_0_Tm_comm_ind t78 k c S55))
        | (pair t77 t78 S56 T86) => (f_equal4 pair (shift_TmVar__subst_TyVar_0_Tm_comm_ind t77 k c S55) (shift_TmVar__subst_TyVar_0_Tm_comm_ind t78 k c S55) (shift_TmVar__subst_TyVar_0_Ty_comm_ind S56 k c S55) (eq_trans (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Ty_comm_ind T86 (HS TmVar k) c S55) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (prj1 t76) => (f_equal prj1 (shift_TmVar__subst_TyVar_0_Tm_comm_ind t76 k c S55))
        | (prj2 t76) => (f_equal prj2 (shift_TmVar__subst_TyVar_0_Tm_comm_ind t76 k c S55))
      end
    with shift_TmVar__subst_TyVar_0_Ty_comm_ind (S57 : Ty) (k : Hvl) (c : (Cutoff TmVar)) (S55 : Ty) {struct S57} :
    ((shift_TmVar_Ty (weakenCutoffTmVar c k) (subst_TyVar_Ty (weakenTrace X0 k) S55 S57)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TmVar_Ty c S55) (shift_TmVar_Ty (weakenCutoffTmVar c k) S57))) :=
      match S57 return ((shift_TmVar_Ty (weakenCutoffTmVar c k) (subst_TyVar_Ty (weakenTrace X0 k) S55 S57)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TmVar_Ty c S55) (shift_TmVar_Ty (weakenCutoffTmVar c k) S57))) with
        | (tvar X5) => (shift_TmVar_Ty_subst_TyVar_Index0_comm_ind c S55 k X5)
        | (tpi T88 T89) => (f_equal2 tpi (shift_TmVar__subst_TyVar_0_Ty_comm_ind T88 k c S55) (eq_trans (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Ty_comm_ind T89 (HS TmVar k) c S55) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (tapp T87 t79) => (f_equal2 tapp (shift_TmVar__subst_TyVar_0_Ty_comm_ind T87 k c S55) (shift_TmVar__subst_TyVar_0_Tm_comm_ind t79 k c S55))
        | (tsig T87 U2) => (f_equal2 tsig (shift_TmVar__subst_TyVar_0_Ty_comm_ind T87 k c S55) (eq_trans (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Ty_comm_ind U2 (HS TmVar k) c S55) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_TyVar__subst_TmVar_0_Tm_comm_ind (s12 : Tm) (k : Hvl) (c : (Cutoff TyVar)) (s11 : Tm) {struct s12} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s11 s12)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TyVar_Tm c s11) (shift_TyVar_Tm (weakenCutoffTyVar c k) s12))) :=
      match s12 return ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TmVar_Tm (weakenTrace X0 k) s11 s12)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TyVar_Tm c s11) (shift_TyVar_Tm (weakenCutoffTyVar c k) s12))) with
        | (var x66) => (shift_TyVar_Tm_subst_TmVar_Index0_comm_ind c s11 k x66)
        | (abs T86 t76) => (f_equal2 abs (shift_TyVar__subst_TmVar_0_Ty_comm_ind T86 k c s11) (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Tm_comm_ind t76 (HS TmVar k) c s11) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (app t77 t78) => (f_equal2 app (shift_TyVar__subst_TmVar_0_Tm_comm_ind t77 k c s11) (shift_TyVar__subst_TmVar_0_Tm_comm_ind t78 k c s11))
        | (pair t77 t78 S55 T86) => (f_equal4 pair (shift_TyVar__subst_TmVar_0_Tm_comm_ind t77 k c s11) (shift_TyVar__subst_TmVar_0_Tm_comm_ind t78 k c s11) (shift_TyVar__subst_TmVar_0_Ty_comm_ind S55 k c s11) (eq_trans (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Ty_comm_ind T86 (HS TmVar k) c s11) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (prj1 t76) => (f_equal prj1 (shift_TyVar__subst_TmVar_0_Tm_comm_ind t76 k c s11))
        | (prj2 t76) => (f_equal prj2 (shift_TyVar__subst_TmVar_0_Tm_comm_ind t76 k c s11))
      end
    with shift_TyVar__subst_TmVar_0_Ty_comm_ind (S56 : Ty) (k : Hvl) (c : (Cutoff TyVar)) (s11 : Tm) {struct S56} :
    ((shift_TyVar_Ty (weakenCutoffTyVar c k) (subst_TmVar_Ty (weakenTrace X0 k) s11 S56)) = (subst_TmVar_Ty (weakenTrace X0 k) (shift_TyVar_Tm c s11) (shift_TyVar_Ty (weakenCutoffTyVar c k) S56))) :=
      match S56 return ((shift_TyVar_Ty (weakenCutoffTyVar c k) (subst_TmVar_Ty (weakenTrace X0 k) s11 S56)) = (subst_TmVar_Ty (weakenTrace X0 k) (shift_TyVar_Tm c s11) (shift_TyVar_Ty (weakenCutoffTyVar c k) S56))) with
        | (tvar X5) => eq_refl
        | (tpi T88 T89) => (f_equal2 tpi (shift_TyVar__subst_TmVar_0_Ty_comm_ind T88 k c s11) (eq_trans (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Ty_comm_ind T89 (HS TmVar k) c s11) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (tapp T87 t79) => (f_equal2 tapp (shift_TyVar__subst_TmVar_0_Ty_comm_ind T87 k c s11) (shift_TyVar__subst_TmVar_0_Tm_comm_ind t79 k c s11))
        | (tsig T87 U2) => (f_equal2 tsig (shift_TyVar__subst_TmVar_0_Ty_comm_ind T87 k c s11) (eq_trans (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Ty_comm_ind U2 (HS TmVar k) c s11) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_TyVar__subst_TyVar_0_Tm_comm_ind (s11 : Tm) (k : Hvl) (c : (Cutoff TyVar)) (S55 : Ty) {struct s11} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S55 s11)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TyVar_Ty c S55) (shift_TyVar_Tm (weakenCutoffTyVar (CS c) k) s11))) :=
      match s11 return ((shift_TyVar_Tm (weakenCutoffTyVar c k) (subst_TyVar_Tm (weakenTrace X0 k) S55 s11)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TyVar_Ty c S55) (shift_TyVar_Tm (weakenCutoffTyVar (CS c) k) s11))) with
        | (var x66) => eq_refl
        | (abs T86 t76) => (f_equal2 abs (shift_TyVar__subst_TyVar_0_Ty_comm_ind T86 k c S55) (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Tm_comm_ind t76 (HS TmVar k) c S55) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (app t77 t78) => (f_equal2 app (shift_TyVar__subst_TyVar_0_Tm_comm_ind t77 k c S55) (shift_TyVar__subst_TyVar_0_Tm_comm_ind t78 k c S55))
        | (pair t77 t78 S56 T86) => (f_equal4 pair (shift_TyVar__subst_TyVar_0_Tm_comm_ind t77 k c S55) (shift_TyVar__subst_TyVar_0_Tm_comm_ind t78 k c S55) (shift_TyVar__subst_TyVar_0_Ty_comm_ind S56 k c S55) (eq_trans (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Ty_comm_ind T86 (HS TmVar k) c S55) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (prj1 t76) => (f_equal prj1 (shift_TyVar__subst_TyVar_0_Tm_comm_ind t76 k c S55))
        | (prj2 t76) => (f_equal prj2 (shift_TyVar__subst_TyVar_0_Tm_comm_ind t76 k c S55))
      end
    with shift_TyVar__subst_TyVar_0_Ty_comm_ind (S57 : Ty) (k : Hvl) (c : (Cutoff TyVar)) (S55 : Ty) {struct S57} :
    ((shift_TyVar_Ty (weakenCutoffTyVar c k) (subst_TyVar_Ty (weakenTrace X0 k) S55 S57)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TyVar_Ty c S55) (shift_TyVar_Ty (weakenCutoffTyVar (CS c) k) S57))) :=
      match S57 return ((shift_TyVar_Ty (weakenCutoffTyVar c k) (subst_TyVar_Ty (weakenTrace X0 k) S55 S57)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TyVar_Ty c S55) (shift_TyVar_Ty (weakenCutoffTyVar (CS c) k) S57))) with
        | (tvar X5) => (shift_TyVar_Ty_subst_TyVar_Index0_comm_ind c S55 k X5)
        | (tpi T88 T89) => (f_equal2 tpi (shift_TyVar__subst_TyVar_0_Ty_comm_ind T88 k c S55) (eq_trans (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Ty_comm_ind T89 (HS TmVar k) c S55) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (tapp T87 t79) => (f_equal2 tapp (shift_TyVar__subst_TyVar_0_Ty_comm_ind T87 k c S55) (shift_TyVar__subst_TyVar_0_Tm_comm_ind t79 k c S55))
        | (tsig T87 U2) => (f_equal2 tsig (shift_TyVar__subst_TyVar_0_Ty_comm_ind T87 k c S55) (eq_trans (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Ty_comm_ind U2 (HS TmVar k) c S55) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_TmVar__subst_TmVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TmVar)) (s11 : Tm) {struct K42} :
    ((shift_TmVar_Kind (weakenCutoffTmVar c k) (subst_TmVar_Kind (weakenTrace X0 k) s11 K42)) = (subst_TmVar_Kind (weakenTrace X0 k) (shift_TmVar_Tm c s11) (shift_TmVar_Kind (weakenCutoffTmVar (CS c) k) K42))) :=
      match K42 return ((shift_TmVar_Kind (weakenCutoffTmVar c k) (subst_TmVar_Kind (weakenTrace X0 k) s11 K42)) = (subst_TmVar_Kind (weakenTrace X0 k) (shift_TmVar_Tm c s11) (shift_TmVar_Kind (weakenCutoffTmVar (CS c) k) K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (shift_TmVar__subst_TmVar_0_Ty_comm_ind T86 k c s11) (eq_trans (f_equal2 shift_TmVar_Kind eq_refl (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Kind_comm_ind K43 (HS TmVar k) c s11) (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_TmVar__subst_TyVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TmVar)) (S55 : Ty) {struct K42} :
    ((shift_TmVar_Kind (weakenCutoffTmVar c k) (subst_TyVar_Kind (weakenTrace X0 k) S55 K42)) = (subst_TyVar_Kind (weakenTrace X0 k) (shift_TmVar_Ty c S55) (shift_TmVar_Kind (weakenCutoffTmVar c k) K42))) :=
      match K42 return ((shift_TmVar_Kind (weakenCutoffTmVar c k) (subst_TyVar_Kind (weakenTrace X0 k) S55 K42)) = (subst_TyVar_Kind (weakenTrace X0 k) (shift_TmVar_Ty c S55) (shift_TmVar_Kind (weakenCutoffTmVar c k) K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (shift_TmVar__subst_TyVar_0_Ty_comm_ind T86 k c S55) (eq_trans (f_equal2 shift_TmVar_Kind eq_refl (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Kind_comm_ind K43 (HS TmVar k) c S55) (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_TyVar__subst_TmVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TyVar)) (s11 : Tm) {struct K42} :
    ((shift_TyVar_Kind (weakenCutoffTyVar c k) (subst_TmVar_Kind (weakenTrace X0 k) s11 K42)) = (subst_TmVar_Kind (weakenTrace X0 k) (shift_TyVar_Tm c s11) (shift_TyVar_Kind (weakenCutoffTyVar c k) K42))) :=
      match K42 return ((shift_TyVar_Kind (weakenCutoffTyVar c k) (subst_TmVar_Kind (weakenTrace X0 k) s11 K42)) = (subst_TmVar_Kind (weakenTrace X0 k) (shift_TyVar_Tm c s11) (shift_TyVar_Kind (weakenCutoffTyVar c k) K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (shift_TyVar__subst_TmVar_0_Ty_comm_ind T86 k c s11) (eq_trans (f_equal2 shift_TyVar_Kind eq_refl (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Kind_comm_ind K43 (HS TmVar k) c s11) (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_TyVar__subst_TyVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TyVar)) (S55 : Ty) {struct K42} :
    ((shift_TyVar_Kind (weakenCutoffTyVar c k) (subst_TyVar_Kind (weakenTrace X0 k) S55 K42)) = (subst_TyVar_Kind (weakenTrace X0 k) (shift_TyVar_Ty c S55) (shift_TyVar_Kind (weakenCutoffTyVar (CS c) k) K42))) :=
      match K42 return ((shift_TyVar_Kind (weakenCutoffTyVar c k) (subst_TyVar_Kind (weakenTrace X0 k) S55 K42)) = (subst_TyVar_Kind (weakenTrace X0 k) (shift_TyVar_Ty c S55) (shift_TyVar_Kind (weakenCutoffTyVar (CS c) k) K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (shift_TyVar__subst_TyVar_0_Ty_comm_ind T86 k c S55) (eq_trans (f_equal2 shift_TyVar_Kind eq_refl (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Kind_comm_ind K43 (HS TmVar k) c S55) (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shift_TmVar_Tm_subst_TmVar_Tm0_comm (s12 : Tm) : (forall (c : (Cutoff TmVar)) (s11 : Tm) ,
      ((shift_TmVar_Tm c (subst_TmVar_Tm X0 s11 s12)) = (subst_TmVar_Tm X0 (shift_TmVar_Tm c s11) (shift_TmVar_Tm (CS c) s12)))) := (shift_TmVar__subst_TmVar_0_Tm_comm_ind s12 H0).
    Definition shift_TmVar_Ty_subst_TmVar_Ty0_comm (S55 : Ty) : (forall (c : (Cutoff TmVar)) (s11 : Tm) ,
      ((shift_TmVar_Ty c (subst_TmVar_Ty X0 s11 S55)) = (subst_TmVar_Ty X0 (shift_TmVar_Tm c s11) (shift_TmVar_Ty (CS c) S55)))) := (shift_TmVar__subst_TmVar_0_Ty_comm_ind S55 H0).
    Definition shift_TmVar_Tm_subst_TyVar_Tm0_comm (s11 : Tm) : (forall (c : (Cutoff TmVar)) (S55 : Ty) ,
      ((shift_TmVar_Tm c (subst_TyVar_Tm X0 S55 s11)) = (subst_TyVar_Tm X0 (shift_TmVar_Ty c S55) (shift_TmVar_Tm c s11)))) := (shift_TmVar__subst_TyVar_0_Tm_comm_ind s11 H0).
    Definition shift_TmVar_Ty_subst_TyVar_Ty0_comm (S56 : Ty) : (forall (c : (Cutoff TmVar)) (S55 : Ty) ,
      ((shift_TmVar_Ty c (subst_TyVar_Ty X0 S55 S56)) = (subst_TyVar_Ty X0 (shift_TmVar_Ty c S55) (shift_TmVar_Ty c S56)))) := (shift_TmVar__subst_TyVar_0_Ty_comm_ind S56 H0).
    Definition shift_TyVar_Tm_subst_TmVar_Tm0_comm (s12 : Tm) : (forall (c : (Cutoff TyVar)) (s11 : Tm) ,
      ((shift_TyVar_Tm c (subst_TmVar_Tm X0 s11 s12)) = (subst_TmVar_Tm X0 (shift_TyVar_Tm c s11) (shift_TyVar_Tm c s12)))) := (shift_TyVar__subst_TmVar_0_Tm_comm_ind s12 H0).
    Definition shift_TyVar_Ty_subst_TmVar_Ty0_comm (S55 : Ty) : (forall (c : (Cutoff TyVar)) (s11 : Tm) ,
      ((shift_TyVar_Ty c (subst_TmVar_Ty X0 s11 S55)) = (subst_TmVar_Ty X0 (shift_TyVar_Tm c s11) (shift_TyVar_Ty c S55)))) := (shift_TyVar__subst_TmVar_0_Ty_comm_ind S55 H0).
    Definition shift_TyVar_Tm_subst_TyVar_Tm0_comm (s11 : Tm) : (forall (c : (Cutoff TyVar)) (S55 : Ty) ,
      ((shift_TyVar_Tm c (subst_TyVar_Tm X0 S55 s11)) = (subst_TyVar_Tm X0 (shift_TyVar_Ty c S55) (shift_TyVar_Tm (CS c) s11)))) := (shift_TyVar__subst_TyVar_0_Tm_comm_ind s11 H0).
    Definition shift_TyVar_Ty_subst_TyVar_Ty0_comm (S56 : Ty) : (forall (c : (Cutoff TyVar)) (S55 : Ty) ,
      ((shift_TyVar_Ty c (subst_TyVar_Ty X0 S55 S56)) = (subst_TyVar_Ty X0 (shift_TyVar_Ty c S55) (shift_TyVar_Ty (CS c) S56)))) := (shift_TyVar__subst_TyVar_0_Ty_comm_ind S56 H0).
    Definition shift_TmVar_Kind_subst_TmVar_Kind0_comm (K42 : Kind) : (forall (c : (Cutoff TmVar)) (s11 : Tm) ,
      ((shift_TmVar_Kind c (subst_TmVar_Kind X0 s11 K42)) = (subst_TmVar_Kind X0 (shift_TmVar_Tm c s11) (shift_TmVar_Kind (CS c) K42)))) := (shift_TmVar__subst_TmVar_0_Kind_comm_ind K42 H0).
    Definition shift_TmVar_Kind_subst_TyVar_Kind0_comm (K42 : Kind) : (forall (c : (Cutoff TmVar)) (S55 : Ty) ,
      ((shift_TmVar_Kind c (subst_TyVar_Kind X0 S55 K42)) = (subst_TyVar_Kind X0 (shift_TmVar_Ty c S55) (shift_TmVar_Kind c K42)))) := (shift_TmVar__subst_TyVar_0_Kind_comm_ind K42 H0).
    Definition shift_TyVar_Kind_subst_TmVar_Kind0_comm (K42 : Kind) : (forall (c : (Cutoff TyVar)) (s11 : Tm) ,
      ((shift_TyVar_Kind c (subst_TmVar_Kind X0 s11 K42)) = (subst_TmVar_Kind X0 (shift_TyVar_Tm c s11) (shift_TyVar_Kind c K42)))) := (shift_TyVar__subst_TmVar_0_Kind_comm_ind K42 H0).
    Definition shift_TyVar_Kind_subst_TyVar_Kind0_comm (K42 : Kind) : (forall (c : (Cutoff TyVar)) (S55 : Ty) ,
      ((shift_TyVar_Kind c (subst_TyVar_Kind X0 S55 K42)) = (subst_TyVar_Kind X0 (shift_TyVar_Ty c S55) (shift_TyVar_Kind (CS c) K42)))) := (shift_TyVar__subst_TyVar_0_Kind_comm_ind K42 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma subst_TmVar_Index_shift_TmVar_Tm0_comm_ind (d : (Trace TmVar)) (s11 : Tm) :
      (forall (k : Hvl) (x66 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TmVar d) k) s11 (shift_TmVar_Index (weakenCutoffTmVar C0 k) x66)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Index (weakenTrace d k) s11 x66)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Index_shift_TyVar_Tm0_comm_ind (d : (Trace TmVar)) (s11 : Tm) :
      (forall (k : Hvl) (x66 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TyVar d) k) s11 x66) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Index (weakenTrace d k) s11 x66)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Index_shift_TmVar_Ty0_comm_ind (d : (Trace TyVar)) (S55 : Ty) :
      (forall (k : Hvl) (X5 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace (XS TmVar d) k) S55 X5) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TyVar_Index (weakenTrace d k) S55 X5)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Index_shift_TyVar_Ty0_comm_ind (d : (Trace TyVar)) (S55 : Ty) :
      (forall (k : Hvl) (X5 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace (XS TyVar d) k) S55 (shift_TyVar_Index (weakenCutoffTyVar C0 k) X5)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Index (weakenTrace d k) S55 X5)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_TmVar__shift_TmVar_0_Tm_comm_ind (s12 : Tm) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) {struct s12} :
    ((subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s11 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s12)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s11 s12))) :=
      match s12 return ((subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s11 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s12)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s11 s12))) with
        | (var x66) => (subst_TmVar_Index_shift_TmVar_Tm0_comm_ind d s11 k x66)
        | (abs T86 t76) => (f_equal2 abs (subst_TmVar__shift_TmVar_0_Ty_comm_ind T86 k d s11) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind t76 (HS TmVar k) d s11) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t77 t78) => (f_equal2 app (subst_TmVar__shift_TmVar_0_Tm_comm_ind t77 k d s11) (subst_TmVar__shift_TmVar_0_Tm_comm_ind t78 k d s11))
        | (pair t77 t78 S55 T86) => (f_equal4 pair (subst_TmVar__shift_TmVar_0_Tm_comm_ind t77 k d s11) (subst_TmVar__shift_TmVar_0_Tm_comm_ind t78 k d s11) (subst_TmVar__shift_TmVar_0_Ty_comm_ind S55 k d s11) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Ty_comm_ind T86 (HS TmVar k) d s11) (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (prj1 t76) => (f_equal prj1 (subst_TmVar__shift_TmVar_0_Tm_comm_ind t76 k d s11))
        | (prj2 t76) => (f_equal prj2 (subst_TmVar__shift_TmVar_0_Tm_comm_ind t76 k d s11))
      end
    with subst_TmVar__shift_TmVar_0_Ty_comm_ind (S56 : Ty) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) {struct S56} :
    ((subst_TmVar_Ty (weakenTrace (XS TmVar d) k) s11 (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S56)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TmVar_Ty (weakenTrace d k) s11 S56))) :=
      match S56 return ((subst_TmVar_Ty (weakenTrace (XS TmVar d) k) s11 (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S56)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TmVar_Ty (weakenTrace d k) s11 S56))) with
        | (tvar X5) => eq_refl
        | (tpi T88 T89) => (f_equal2 tpi (subst_TmVar__shift_TmVar_0_Ty_comm_ind T88 k d s11) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Ty_comm_ind T89 (HS TmVar k) d s11) (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T87 t79) => (f_equal2 tapp (subst_TmVar__shift_TmVar_0_Ty_comm_ind T87 k d s11) (subst_TmVar__shift_TmVar_0_Tm_comm_ind t79 k d s11))
        | (tsig T87 U2) => (f_equal2 tsig (subst_TmVar__shift_TmVar_0_Ty_comm_ind T87 k d s11) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Ty_comm_ind U2 (HS TmVar k) d s11) (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__shift_TyVar_0_Tm_comm_ind (s12 : Tm) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) {struct s12} :
    ((subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s11 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s12)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s11 s12))) :=
      match s12 return ((subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s11 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s12)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Tm (weakenTrace d k) s11 s12))) with
        | (var x66) => (subst_TmVar_Index_shift_TyVar_Tm0_comm_ind d s11 k x66)
        | (abs T86 t76) => (f_equal2 abs (subst_TmVar__shift_TyVar_0_Ty_comm_ind T86 k d s11) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Tm_comm_ind t76 (HS TmVar k) d s11) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t77 t78) => (f_equal2 app (subst_TmVar__shift_TyVar_0_Tm_comm_ind t77 k d s11) (subst_TmVar__shift_TyVar_0_Tm_comm_ind t78 k d s11))
        | (pair t77 t78 S55 T86) => (f_equal4 pair (subst_TmVar__shift_TyVar_0_Tm_comm_ind t77 k d s11) (subst_TmVar__shift_TyVar_0_Tm_comm_ind t78 k d s11) (subst_TmVar__shift_TyVar_0_Ty_comm_ind S55 k d s11) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Ty_comm_ind T86 (HS TmVar k) d s11) (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (prj1 t76) => (f_equal prj1 (subst_TmVar__shift_TyVar_0_Tm_comm_ind t76 k d s11))
        | (prj2 t76) => (f_equal prj2 (subst_TmVar__shift_TyVar_0_Tm_comm_ind t76 k d s11))
      end
    with subst_TmVar__shift_TyVar_0_Ty_comm_ind (S56 : Ty) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) {struct S56} :
    ((subst_TmVar_Ty (weakenTrace (XS TyVar d) k) s11 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S56)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TmVar_Ty (weakenTrace d k) s11 S56))) :=
      match S56 return ((subst_TmVar_Ty (weakenTrace (XS TyVar d) k) s11 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S56)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TmVar_Ty (weakenTrace d k) s11 S56))) with
        | (tvar X5) => eq_refl
        | (tpi T88 T89) => (f_equal2 tpi (subst_TmVar__shift_TyVar_0_Ty_comm_ind T88 k d s11) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Ty_comm_ind T89 (HS TmVar k) d s11) (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T87 t79) => (f_equal2 tapp (subst_TmVar__shift_TyVar_0_Ty_comm_ind T87 k d s11) (subst_TmVar__shift_TyVar_0_Tm_comm_ind t79 k d s11))
        | (tsig T87 U2) => (f_equal2 tsig (subst_TmVar__shift_TyVar_0_Ty_comm_ind T87 k d s11) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Ty_comm_ind U2 (HS TmVar k) d s11) (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__shift_TmVar_0_Tm_comm_ind (s11 : Tm) (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) {struct s11} :
    ((subst_TyVar_Tm (weakenTrace (XS TmVar d) k) S55 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s11)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S55 s11))) :=
      match s11 return ((subst_TyVar_Tm (weakenTrace (XS TmVar d) k) S55 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s11)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S55 s11))) with
        | (var x66) => eq_refl
        | (abs T86 t76) => (f_equal2 abs (subst_TyVar__shift_TmVar_0_Ty_comm_ind T86 k d S55) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Tm_comm_ind t76 (HS TmVar k) d S55) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t77 t78) => (f_equal2 app (subst_TyVar__shift_TmVar_0_Tm_comm_ind t77 k d S55) (subst_TyVar__shift_TmVar_0_Tm_comm_ind t78 k d S55))
        | (pair t77 t78 S56 T86) => (f_equal4 pair (subst_TyVar__shift_TmVar_0_Tm_comm_ind t77 k d S55) (subst_TyVar__shift_TmVar_0_Tm_comm_ind t78 k d S55) (subst_TyVar__shift_TmVar_0_Ty_comm_ind S56 k d S55) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Ty_comm_ind T86 (HS TmVar k) d S55) (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (prj1 t76) => (f_equal prj1 (subst_TyVar__shift_TmVar_0_Tm_comm_ind t76 k d S55))
        | (prj2 t76) => (f_equal prj2 (subst_TyVar__shift_TmVar_0_Tm_comm_ind t76 k d S55))
      end
    with subst_TyVar__shift_TmVar_0_Ty_comm_ind (S57 : Ty) (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) {struct S57} :
    ((subst_TyVar_Ty (weakenTrace (XS TmVar d) k) S55 (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S57)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TyVar_Ty (weakenTrace d k) S55 S57))) :=
      match S57 return ((subst_TyVar_Ty (weakenTrace (XS TmVar d) k) S55 (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S57)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TyVar_Ty (weakenTrace d k) S55 S57))) with
        | (tvar X5) => (subst_TyVar_Index_shift_TmVar_Ty0_comm_ind d S55 k X5)
        | (tpi T88 T89) => (f_equal2 tpi (subst_TyVar__shift_TmVar_0_Ty_comm_ind T88 k d S55) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Ty_comm_ind T89 (HS TmVar k) d S55) (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T87 t79) => (f_equal2 tapp (subst_TyVar__shift_TmVar_0_Ty_comm_ind T87 k d S55) (subst_TyVar__shift_TmVar_0_Tm_comm_ind t79 k d S55))
        | (tsig T87 U2) => (f_equal2 tsig (subst_TyVar__shift_TmVar_0_Ty_comm_ind T87 k d S55) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Ty_comm_ind U2 (HS TmVar k) d S55) (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__shift_TyVar_0_Tm_comm_ind (s11 : Tm) (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) {struct s11} :
    ((subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S55 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s11)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S55 s11))) :=
      match s11 return ((subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S55 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s11)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TyVar_Tm (weakenTrace d k) S55 s11))) with
        | (var x66) => eq_refl
        | (abs T86 t76) => (f_equal2 abs (subst_TyVar__shift_TyVar_0_Ty_comm_ind T86 k d S55) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Tm_comm_ind t76 (HS TmVar k) d S55) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t77 t78) => (f_equal2 app (subst_TyVar__shift_TyVar_0_Tm_comm_ind t77 k d S55) (subst_TyVar__shift_TyVar_0_Tm_comm_ind t78 k d S55))
        | (pair t77 t78 S56 T86) => (f_equal4 pair (subst_TyVar__shift_TyVar_0_Tm_comm_ind t77 k d S55) (subst_TyVar__shift_TyVar_0_Tm_comm_ind t78 k d S55) (subst_TyVar__shift_TyVar_0_Ty_comm_ind S56 k d S55) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Ty_comm_ind T86 (HS TmVar k) d S55) (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (prj1 t76) => (f_equal prj1 (subst_TyVar__shift_TyVar_0_Tm_comm_ind t76 k d S55))
        | (prj2 t76) => (f_equal prj2 (subst_TyVar__shift_TyVar_0_Tm_comm_ind t76 k d S55))
      end
    with subst_TyVar__shift_TyVar_0_Ty_comm_ind (S57 : Ty) (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) {struct S57} :
    ((subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S55 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S57)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Ty (weakenTrace d k) S55 S57))) :=
      match S57 return ((subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S55 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S57)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Ty (weakenTrace d k) S55 S57))) with
        | (tvar X5) => (subst_TyVar_Index_shift_TyVar_Ty0_comm_ind d S55 k X5)
        | (tpi T88 T89) => (f_equal2 tpi (subst_TyVar__shift_TyVar_0_Ty_comm_ind T88 k d S55) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Ty_comm_ind T89 (HS TmVar k) d S55) (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T87 t79) => (f_equal2 tapp (subst_TyVar__shift_TyVar_0_Ty_comm_ind T87 k d S55) (subst_TyVar__shift_TyVar_0_Tm_comm_ind t79 k d S55))
        | (tsig T87 U2) => (f_equal2 tsig (subst_TyVar__shift_TyVar_0_Ty_comm_ind T87 k d S55) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Ty_comm_ind U2 (HS TmVar k) d S55) (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__shift_TmVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) {struct K42} :
    ((subst_TmVar_Kind (weakenTrace (XS TmVar d) k) s11 (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K42)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (subst_TmVar_Kind (weakenTrace d k) s11 K42))) :=
      match K42 return ((subst_TmVar_Kind (weakenTrace (XS TmVar d) k) s11 (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K42)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (subst_TmVar_Kind (weakenTrace d k) s11 K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (subst_TmVar__shift_TmVar_0_Ty_comm_ind T86 k d s11) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Kind_comm_ind K43 (HS TmVar k) d s11) (f_equal2 shift_TmVar_Kind eq_refl (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__shift_TyVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) {struct K42} :
    ((subst_TmVar_Kind (weakenTrace (XS TyVar d) k) s11 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K42)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (subst_TmVar_Kind (weakenTrace d k) s11 K42))) :=
      match K42 return ((subst_TmVar_Kind (weakenTrace (XS TyVar d) k) s11 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K42)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (subst_TmVar_Kind (weakenTrace d k) s11 K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (subst_TmVar__shift_TyVar_0_Ty_comm_ind T86 k d s11) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Kind_comm_ind K43 (HS TmVar k) d s11) (f_equal2 shift_TyVar_Kind eq_refl (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__shift_TmVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) {struct K42} :
    ((subst_TyVar_Kind (weakenTrace (XS TmVar d) k) S55 (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K42)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (subst_TyVar_Kind (weakenTrace d k) S55 K42))) :=
      match K42 return ((subst_TyVar_Kind (weakenTrace (XS TmVar d) k) S55 (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K42)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (subst_TyVar_Kind (weakenTrace d k) S55 K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (subst_TyVar__shift_TmVar_0_Ty_comm_ind T86 k d S55) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Kind_comm_ind K43 (HS TmVar k) d S55) (f_equal2 shift_TmVar_Kind eq_refl (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__shift_TyVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) {struct K42} :
    ((subst_TyVar_Kind (weakenTrace (XS TyVar d) k) S55 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K42)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (subst_TyVar_Kind (weakenTrace d k) S55 K42))) :=
      match K42 return ((subst_TyVar_Kind (weakenTrace (XS TyVar d) k) S55 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K42)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (subst_TyVar_Kind (weakenTrace d k) S55 K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (subst_TyVar__shift_TyVar_0_Ty_comm_ind T86 k d S55) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Kind_comm_ind K43 (HS TmVar k) d S55) (f_equal2 shift_TyVar_Kind eq_refl (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition subst_TmVar_Tm_shift_TmVar_Tm0_comm (s12 : Tm) : (forall (d : (Trace TmVar)) (s11 : Tm) ,
      ((subst_TmVar_Tm (XS TmVar d) s11 (shift_TmVar_Tm C0 s12)) = (shift_TmVar_Tm C0 (subst_TmVar_Tm d s11 s12)))) := (subst_TmVar__shift_TmVar_0_Tm_comm_ind s12 H0).
    Definition subst_TmVar_Ty_shift_TmVar_Ty0_comm (S55 : Ty) : (forall (d : (Trace TmVar)) (s11 : Tm) ,
      ((subst_TmVar_Ty (XS TmVar d) s11 (shift_TmVar_Ty C0 S55)) = (shift_TmVar_Ty C0 (subst_TmVar_Ty d s11 S55)))) := (subst_TmVar__shift_TmVar_0_Ty_comm_ind S55 H0).
    Definition subst_TmVar_Tm_shift_TyVar_Tm0_comm (s12 : Tm) : (forall (d : (Trace TmVar)) (s11 : Tm) ,
      ((subst_TmVar_Tm (XS TyVar d) s11 (shift_TyVar_Tm C0 s12)) = (shift_TyVar_Tm C0 (subst_TmVar_Tm d s11 s12)))) := (subst_TmVar__shift_TyVar_0_Tm_comm_ind s12 H0).
    Definition subst_TmVar_Ty_shift_TyVar_Ty0_comm (S55 : Ty) : (forall (d : (Trace TmVar)) (s11 : Tm) ,
      ((subst_TmVar_Ty (XS TyVar d) s11 (shift_TyVar_Ty C0 S55)) = (shift_TyVar_Ty C0 (subst_TmVar_Ty d s11 S55)))) := (subst_TmVar__shift_TyVar_0_Ty_comm_ind S55 H0).
    Definition subst_TyVar_Tm_shift_TmVar_Tm0_comm (s11 : Tm) : (forall (d : (Trace TyVar)) (S55 : Ty) ,
      ((subst_TyVar_Tm (XS TmVar d) S55 (shift_TmVar_Tm C0 s11)) = (shift_TmVar_Tm C0 (subst_TyVar_Tm d S55 s11)))) := (subst_TyVar__shift_TmVar_0_Tm_comm_ind s11 H0).
    Definition subst_TyVar_Ty_shift_TmVar_Ty0_comm (S56 : Ty) : (forall (d : (Trace TyVar)) (S55 : Ty) ,
      ((subst_TyVar_Ty (XS TmVar d) S55 (shift_TmVar_Ty C0 S56)) = (shift_TmVar_Ty C0 (subst_TyVar_Ty d S55 S56)))) := (subst_TyVar__shift_TmVar_0_Ty_comm_ind S56 H0).
    Definition subst_TyVar_Tm_shift_TyVar_Tm0_comm (s11 : Tm) : (forall (d : (Trace TyVar)) (S55 : Ty) ,
      ((subst_TyVar_Tm (XS TyVar d) S55 (shift_TyVar_Tm C0 s11)) = (shift_TyVar_Tm C0 (subst_TyVar_Tm d S55 s11)))) := (subst_TyVar__shift_TyVar_0_Tm_comm_ind s11 H0).
    Definition subst_TyVar_Ty_shift_TyVar_Ty0_comm (S56 : Ty) : (forall (d : (Trace TyVar)) (S55 : Ty) ,
      ((subst_TyVar_Ty (XS TyVar d) S55 (shift_TyVar_Ty C0 S56)) = (shift_TyVar_Ty C0 (subst_TyVar_Ty d S55 S56)))) := (subst_TyVar__shift_TyVar_0_Ty_comm_ind S56 H0).
    Definition subst_TmVar_Kind_shift_TmVar_Kind0_comm (K42 : Kind) : (forall (d : (Trace TmVar)) (s11 : Tm) ,
      ((subst_TmVar_Kind (XS TmVar d) s11 (shift_TmVar_Kind C0 K42)) = (shift_TmVar_Kind C0 (subst_TmVar_Kind d s11 K42)))) := (subst_TmVar__shift_TmVar_0_Kind_comm_ind K42 H0).
    Definition subst_TmVar_Kind_shift_TyVar_Kind0_comm (K42 : Kind) : (forall (d : (Trace TmVar)) (s11 : Tm) ,
      ((subst_TmVar_Kind (XS TyVar d) s11 (shift_TyVar_Kind C0 K42)) = (shift_TyVar_Kind C0 (subst_TmVar_Kind d s11 K42)))) := (subst_TmVar__shift_TyVar_0_Kind_comm_ind K42 H0).
    Definition subst_TyVar_Kind_shift_TmVar_Kind0_comm (K42 : Kind) : (forall (d : (Trace TyVar)) (S55 : Ty) ,
      ((subst_TyVar_Kind (XS TmVar d) S55 (shift_TmVar_Kind C0 K42)) = (shift_TmVar_Kind C0 (subst_TyVar_Kind d S55 K42)))) := (subst_TyVar__shift_TmVar_0_Kind_comm_ind K42 H0).
    Definition subst_TyVar_Kind_shift_TyVar_Kind0_comm (K42 : Kind) : (forall (d : (Trace TyVar)) (S55 : Ty) ,
      ((subst_TyVar_Kind (XS TyVar d) S55 (shift_TyVar_Kind C0 K42)) = (shift_TyVar_Kind C0 (subst_TyVar_Kind d S55 K42)))) := (subst_TyVar__shift_TyVar_0_Kind_comm_ind K42 H0).
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
    Lemma subst_TmVar_Tm_subst_TmVar_Index0_commright_ind (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) :
      (forall (k : Hvl) (x66 : (Index TmVar)) ,
        ((subst_TmVar_Tm (weakenTrace d k) s11 (subst_TmVar_Index (weakenTrace X0 k) s12 x66)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s11 s12) (subst_TmVar_Index (weakenTrace (XS TmVar d) k) s11 x66)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Tm_subst_TmVar_Index0_commright_ind (d : (Trace TyVar)) (S55 : Ty) (s11 : Tm) :
      (forall (k : Hvl) (x66 : (Index TmVar)) ,
        ((subst_TyVar_Tm (weakenTrace d k) S55 (subst_TmVar_Index (weakenTrace X0 k) s11 x66)) = (subst_TmVar_Index (weakenTrace X0 k) (subst_TyVar_Tm d S55 s11) x66))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Ty_subst_TyVar_Index0_commright_ind (d : (Trace TmVar)) (s11 : Tm) (S55 : Ty) :
      (forall (k : Hvl) (X5 : (Index TyVar)) ,
        ((subst_TmVar_Ty (weakenTrace d k) s11 (subst_TyVar_Index (weakenTrace X0 k) S55 X5)) = (subst_TyVar_Index (weakenTrace X0 k) (subst_TmVar_Ty d s11 S55) X5))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Ty_subst_TyVar_Index0_commright_ind (d : (Trace TyVar)) (S55 : Ty) (S56 : Ty) :
      (forall (k : Hvl) (X5 : (Index TyVar)) ,
        ((subst_TyVar_Ty (weakenTrace d k) S55 (subst_TyVar_Index (weakenTrace X0 k) S56 X5)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d S55 S56) (subst_TyVar_Index (weakenTrace (XS TyVar d) k) S55 X5)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Ty_subst_TyVar_Index0_commleft_ind (d : (Trace TmVar)) (s11 : Tm) (S55 : Ty) :
      (forall (k : Hvl) (x66 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace d k) s11 x66) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TmVar_Ty d s11 S55) (subst_TmVar_Index (weakenTrace (XS TyVar d) k) s11 x66)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Tm_subst_TmVar_Index0_commleft_ind (d : (Trace TyVar)) (S55 : Ty) (s11 : Tm) :
      (forall (k : Hvl) (X5 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace d k) S55 X5) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TyVar_Tm d S55 s11) (subst_TyVar_Index (weakenTrace (XS TmVar d) k) S55 X5)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_TmVar__subst_TmVar_0_Tm_comm_ind (s13 : Tm) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) {struct s13} :
    ((subst_TmVar_Tm (weakenTrace d k) s11 (subst_TmVar_Tm (weakenTrace X0 k) s12 s13)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s11 s12) (subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s11 s13))) :=
      match s13 return ((subst_TmVar_Tm (weakenTrace d k) s11 (subst_TmVar_Tm (weakenTrace X0 k) s12 s13)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d s11 s12) (subst_TmVar_Tm (weakenTrace (XS TmVar d) k) s11 s13))) with
        | (var x66) => (subst_TmVar_Tm_subst_TmVar_Index0_commright_ind d s11 s12 k x66)
        | (abs T86 t76) => (f_equal2 abs (subst_TmVar__subst_TmVar_0_Ty_comm_ind T86 k d s11 s12) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t76 (HS TmVar k) d s11 s12) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t77 t78) => (f_equal2 app (subst_TmVar__subst_TmVar_0_Tm_comm_ind t77 k d s11 s12) (subst_TmVar__subst_TmVar_0_Tm_comm_ind t78 k d s11 s12))
        | (pair t77 t78 S55 T86) => (f_equal4 pair (subst_TmVar__subst_TmVar_0_Tm_comm_ind t77 k d s11 s12) (subst_TmVar__subst_TmVar_0_Tm_comm_ind t78 k d s11 s12) (subst_TmVar__subst_TmVar_0_Ty_comm_ind S55 k d s11 s12) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Ty_comm_ind T86 (HS TmVar k) d s11 s12) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (prj1 t76) => (f_equal prj1 (subst_TmVar__subst_TmVar_0_Tm_comm_ind t76 k d s11 s12))
        | (prj2 t76) => (f_equal prj2 (subst_TmVar__subst_TmVar_0_Tm_comm_ind t76 k d s11 s12))
      end
    with subst_TmVar__subst_TmVar_0_Ty_comm_ind (S56 : Ty) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) {struct S56} :
    ((subst_TmVar_Ty (weakenTrace d k) s11 (subst_TmVar_Ty (weakenTrace X0 k) s12 S56)) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TmVar_Tm d s11 s12) (subst_TmVar_Ty (weakenTrace (XS TmVar d) k) s11 S56))) :=
      match S56 return ((subst_TmVar_Ty (weakenTrace d k) s11 (subst_TmVar_Ty (weakenTrace X0 k) s12 S56)) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TmVar_Tm d s11 s12) (subst_TmVar_Ty (weakenTrace (XS TmVar d) k) s11 S56))) with
        | (tvar X5) => eq_refl
        | (tpi T88 T89) => (f_equal2 tpi (subst_TmVar__subst_TmVar_0_Ty_comm_ind T88 k d s11 s12) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Ty_comm_ind T89 (HS TmVar k) d s11 s12) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T87 t79) => (f_equal2 tapp (subst_TmVar__subst_TmVar_0_Ty_comm_ind T87 k d s11 s12) (subst_TmVar__subst_TmVar_0_Tm_comm_ind t79 k d s11 s12))
        | (tsig T87 U2) => (f_equal2 tsig (subst_TmVar__subst_TmVar_0_Ty_comm_ind T87 k d s11 s12) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Ty_comm_ind U2 (HS TmVar k) d s11 s12) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__subst_TyVar_0_Tm_comm_ind (s12 : Tm) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (S55 : Ty) {struct s12} :
    ((subst_TmVar_Tm (weakenTrace d k) s11 (subst_TyVar_Tm (weakenTrace X0 k) S55 s12)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TmVar_Ty d s11 S55) (subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s11 s12))) :=
      match s12 return ((subst_TmVar_Tm (weakenTrace d k) s11 (subst_TyVar_Tm (weakenTrace X0 k) S55 s12)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TmVar_Ty d s11 S55) (subst_TmVar_Tm (weakenTrace (XS TyVar d) k) s11 s12))) with
        | (var x66) => (subst_TmVar_Ty_subst_TyVar_Index0_commleft_ind d s11 S55 k x66)
        | (abs T86 t76) => (f_equal2 abs (subst_TmVar__subst_TyVar_0_Ty_comm_ind T86 k d s11 S55) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Tm_comm_ind t76 (HS TmVar k) d s11 S55) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t77 t78) => (f_equal2 app (subst_TmVar__subst_TyVar_0_Tm_comm_ind t77 k d s11 S55) (subst_TmVar__subst_TyVar_0_Tm_comm_ind t78 k d s11 S55))
        | (pair t77 t78 S56 T86) => (f_equal4 pair (subst_TmVar__subst_TyVar_0_Tm_comm_ind t77 k d s11 S55) (subst_TmVar__subst_TyVar_0_Tm_comm_ind t78 k d s11 S55) (subst_TmVar__subst_TyVar_0_Ty_comm_ind S56 k d s11 S55) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Ty_comm_ind T86 (HS TmVar k) d s11 S55) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (prj1 t76) => (f_equal prj1 (subst_TmVar__subst_TyVar_0_Tm_comm_ind t76 k d s11 S55))
        | (prj2 t76) => (f_equal prj2 (subst_TmVar__subst_TyVar_0_Tm_comm_ind t76 k d s11 S55))
      end
    with subst_TmVar__subst_TyVar_0_Ty_comm_ind (S57 : Ty) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (S55 : Ty) {struct S57} :
    ((subst_TmVar_Ty (weakenTrace d k) s11 (subst_TyVar_Ty (weakenTrace X0 k) S55 S57)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TmVar_Ty d s11 S55) (subst_TmVar_Ty (weakenTrace (XS TyVar d) k) s11 S57))) :=
      match S57 return ((subst_TmVar_Ty (weakenTrace d k) s11 (subst_TyVar_Ty (weakenTrace X0 k) S55 S57)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TmVar_Ty d s11 S55) (subst_TmVar_Ty (weakenTrace (XS TyVar d) k) s11 S57))) with
        | (tvar X5) => (subst_TmVar_Ty_subst_TyVar_Index0_commright_ind d s11 S55 k X5)
        | (tpi T88 T89) => (f_equal2 tpi (subst_TmVar__subst_TyVar_0_Ty_comm_ind T88 k d s11 S55) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Ty_comm_ind T89 (HS TmVar k) d s11 S55) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T87 t79) => (f_equal2 tapp (subst_TmVar__subst_TyVar_0_Ty_comm_ind T87 k d s11 S55) (subst_TmVar__subst_TyVar_0_Tm_comm_ind t79 k d s11 S55))
        | (tsig T87 U2) => (f_equal2 tsig (subst_TmVar__subst_TyVar_0_Ty_comm_ind T87 k d s11 S55) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Ty_comm_ind U2 (HS TmVar k) d s11 S55) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__subst_TmVar_0_Tm_comm_ind (s12 : Tm) (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) (s11 : Tm) {struct s12} :
    ((subst_TyVar_Tm (weakenTrace d k) S55 (subst_TmVar_Tm (weakenTrace X0 k) s11 s12)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TyVar_Tm d S55 s11) (subst_TyVar_Tm (weakenTrace (XS TmVar d) k) S55 s12))) :=
      match s12 return ((subst_TyVar_Tm (weakenTrace d k) S55 (subst_TmVar_Tm (weakenTrace X0 k) s11 s12)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TyVar_Tm d S55 s11) (subst_TyVar_Tm (weakenTrace (XS TmVar d) k) S55 s12))) with
        | (var x66) => (subst_TyVar_Tm_subst_TmVar_Index0_commright_ind d S55 s11 k x66)
        | (abs T86 t76) => (f_equal2 abs (subst_TyVar__subst_TmVar_0_Ty_comm_ind T86 k d S55 s11) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Tm_comm_ind t76 (HS TmVar k) d S55 s11) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t77 t78) => (f_equal2 app (subst_TyVar__subst_TmVar_0_Tm_comm_ind t77 k d S55 s11) (subst_TyVar__subst_TmVar_0_Tm_comm_ind t78 k d S55 s11))
        | (pair t77 t78 S56 T86) => (f_equal4 pair (subst_TyVar__subst_TmVar_0_Tm_comm_ind t77 k d S55 s11) (subst_TyVar__subst_TmVar_0_Tm_comm_ind t78 k d S55 s11) (subst_TyVar__subst_TmVar_0_Ty_comm_ind S56 k d S55 s11) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Ty_comm_ind T86 (HS TmVar k) d S55 s11) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (prj1 t76) => (f_equal prj1 (subst_TyVar__subst_TmVar_0_Tm_comm_ind t76 k d S55 s11))
        | (prj2 t76) => (f_equal prj2 (subst_TyVar__subst_TmVar_0_Tm_comm_ind t76 k d S55 s11))
      end
    with subst_TyVar__subst_TmVar_0_Ty_comm_ind (S57 : Ty) (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) (s11 : Tm) {struct S57} :
    ((subst_TyVar_Ty (weakenTrace d k) S55 (subst_TmVar_Ty (weakenTrace X0 k) s11 S57)) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TyVar_Tm d S55 s11) (subst_TyVar_Ty (weakenTrace (XS TmVar d) k) S55 S57))) :=
      match S57 return ((subst_TyVar_Ty (weakenTrace d k) S55 (subst_TmVar_Ty (weakenTrace X0 k) s11 S57)) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TyVar_Tm d S55 s11) (subst_TyVar_Ty (weakenTrace (XS TmVar d) k) S55 S57))) with
        | (tvar X5) => (subst_TyVar_Tm_subst_TmVar_Index0_commleft_ind d S55 s11 k X5)
        | (tpi T88 T89) => (f_equal2 tpi (subst_TyVar__subst_TmVar_0_Ty_comm_ind T88 k d S55 s11) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Ty_comm_ind T89 (HS TmVar k) d S55 s11) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T87 t79) => (f_equal2 tapp (subst_TyVar__subst_TmVar_0_Ty_comm_ind T87 k d S55 s11) (subst_TyVar__subst_TmVar_0_Tm_comm_ind t79 k d S55 s11))
        | (tsig T87 U2) => (f_equal2 tsig (subst_TyVar__subst_TmVar_0_Ty_comm_ind T87 k d S55 s11) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Ty_comm_ind U2 (HS TmVar k) d S55 s11) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__subst_TyVar_0_Tm_comm_ind (s11 : Tm) (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) (S56 : Ty) {struct s11} :
    ((subst_TyVar_Tm (weakenTrace d k) S55 (subst_TyVar_Tm (weakenTrace X0 k) S56 s11)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TyVar_Ty d S55 S56) (subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S55 s11))) :=
      match s11 return ((subst_TyVar_Tm (weakenTrace d k) S55 (subst_TyVar_Tm (weakenTrace X0 k) S56 s11)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TyVar_Ty d S55 S56) (subst_TyVar_Tm (weakenTrace (XS TyVar d) k) S55 s11))) with
        | (var x66) => eq_refl
        | (abs T86 t76) => (f_equal2 abs (subst_TyVar__subst_TyVar_0_Ty_comm_ind T86 k d S55 S56) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Tm_comm_ind t76 (HS TmVar k) d S55 S56) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t77 t78) => (f_equal2 app (subst_TyVar__subst_TyVar_0_Tm_comm_ind t77 k d S55 S56) (subst_TyVar__subst_TyVar_0_Tm_comm_ind t78 k d S55 S56))
        | (pair t77 t78 S57 T86) => (f_equal4 pair (subst_TyVar__subst_TyVar_0_Tm_comm_ind t77 k d S55 S56) (subst_TyVar__subst_TyVar_0_Tm_comm_ind t78 k d S55 S56) (subst_TyVar__subst_TyVar_0_Ty_comm_ind S57 k d S55 S56) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Ty_comm_ind T86 (HS TmVar k) d S55 S56) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (prj1 t76) => (f_equal prj1 (subst_TyVar__subst_TyVar_0_Tm_comm_ind t76 k d S55 S56))
        | (prj2 t76) => (f_equal prj2 (subst_TyVar__subst_TyVar_0_Tm_comm_ind t76 k d S55 S56))
      end
    with subst_TyVar__subst_TyVar_0_Ty_comm_ind (S58 : Ty) (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) (S56 : Ty) {struct S58} :
    ((subst_TyVar_Ty (weakenTrace d k) S55 (subst_TyVar_Ty (weakenTrace X0 k) S56 S58)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d S55 S56) (subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S55 S58))) :=
      match S58 return ((subst_TyVar_Ty (weakenTrace d k) S55 (subst_TyVar_Ty (weakenTrace X0 k) S56 S58)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d S55 S56) (subst_TyVar_Ty (weakenTrace (XS TyVar d) k) S55 S58))) with
        | (tvar X5) => (subst_TyVar_Ty_subst_TyVar_Index0_commright_ind d S55 S56 k X5)
        | (tpi T88 T89) => (f_equal2 tpi (subst_TyVar__subst_TyVar_0_Ty_comm_ind T88 k d S55 S56) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Ty_comm_ind T89 (HS TmVar k) d S55 S56) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T87 t79) => (f_equal2 tapp (subst_TyVar__subst_TyVar_0_Ty_comm_ind T87 k d S55 S56) (subst_TyVar__subst_TyVar_0_Tm_comm_ind t79 k d S55 S56))
        | (tsig T87 U2) => (f_equal2 tsig (subst_TyVar__subst_TyVar_0_Ty_comm_ind T87 k d S55 S56) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Ty_comm_ind U2 (HS TmVar k) d S55 S56) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__subst_TmVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) {struct K42} :
    ((subst_TmVar_Kind (weakenTrace d k) s11 (subst_TmVar_Kind (weakenTrace X0 k) s12 K42)) = (subst_TmVar_Kind (weakenTrace X0 k) (subst_TmVar_Tm d s11 s12) (subst_TmVar_Kind (weakenTrace (XS TmVar d) k) s11 K42))) :=
      match K42 return ((subst_TmVar_Kind (weakenTrace d k) s11 (subst_TmVar_Kind (weakenTrace X0 k) s12 K42)) = (subst_TmVar_Kind (weakenTrace X0 k) (subst_TmVar_Tm d s11 s12) (subst_TmVar_Kind (weakenTrace (XS TmVar d) k) s11 K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (subst_TmVar__subst_TmVar_0_Ty_comm_ind T86 k d s11 s12) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Kind_comm_ind K43 (HS TmVar k) d s11 s12) (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__subst_TyVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (S55 : Ty) {struct K42} :
    ((subst_TmVar_Kind (weakenTrace d k) s11 (subst_TyVar_Kind (weakenTrace X0 k) S55 K42)) = (subst_TyVar_Kind (weakenTrace X0 k) (subst_TmVar_Ty d s11 S55) (subst_TmVar_Kind (weakenTrace (XS TyVar d) k) s11 K42))) :=
      match K42 return ((subst_TmVar_Kind (weakenTrace d k) s11 (subst_TyVar_Kind (weakenTrace X0 k) S55 K42)) = (subst_TyVar_Kind (weakenTrace X0 k) (subst_TmVar_Ty d s11 S55) (subst_TmVar_Kind (weakenTrace (XS TyVar d) k) s11 K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (subst_TmVar__subst_TyVar_0_Ty_comm_ind T86 k d s11 S55) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Kind_comm_ind K43 (HS TmVar k) d s11 S55) (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__subst_TmVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) (s11 : Tm) {struct K42} :
    ((subst_TyVar_Kind (weakenTrace d k) S55 (subst_TmVar_Kind (weakenTrace X0 k) s11 K42)) = (subst_TmVar_Kind (weakenTrace X0 k) (subst_TyVar_Tm d S55 s11) (subst_TyVar_Kind (weakenTrace (XS TmVar d) k) S55 K42))) :=
      match K42 return ((subst_TyVar_Kind (weakenTrace d k) S55 (subst_TmVar_Kind (weakenTrace X0 k) s11 K42)) = (subst_TmVar_Kind (weakenTrace X0 k) (subst_TyVar_Tm d S55 s11) (subst_TyVar_Kind (weakenTrace (XS TmVar d) k) S55 K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (subst_TyVar__subst_TmVar_0_Ty_comm_ind T86 k d S55 s11) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Kind_comm_ind K43 (HS TmVar k) d S55 s11) (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__subst_TyVar_0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) (S56 : Ty) {struct K42} :
    ((subst_TyVar_Kind (weakenTrace d k) S55 (subst_TyVar_Kind (weakenTrace X0 k) S56 K42)) = (subst_TyVar_Kind (weakenTrace X0 k) (subst_TyVar_Ty d S55 S56) (subst_TyVar_Kind (weakenTrace (XS TyVar d) k) S55 K42))) :=
      match K42 return ((subst_TyVar_Kind (weakenTrace d k) S55 (subst_TyVar_Kind (weakenTrace X0 k) S56 K42)) = (subst_TyVar_Kind (weakenTrace X0 k) (subst_TyVar_Ty d S55 S56) (subst_TyVar_Kind (weakenTrace (XS TyVar d) k) S55 K42))) with
        | (star) => eq_refl
        | (kpi T86 K43) => (f_equal2 kpi (subst_TyVar__subst_TyVar_0_Ty_comm_ind T86 k d S55 S56) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Kind_comm_ind K43 (HS TmVar k) d S55 S56) (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition subst_TmVar_Tm_subst_TmVar_Tm0_comm (s13 : Tm) : (forall (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) ,
      ((subst_TmVar_Tm d s11 (subst_TmVar_Tm X0 s12 s13)) = (subst_TmVar_Tm X0 (subst_TmVar_Tm d s11 s12) (subst_TmVar_Tm (XS TmVar d) s11 s13)))) := (subst_TmVar__subst_TmVar_0_Tm_comm_ind s13 H0).
    Definition subst_TmVar_Ty_subst_TmVar_Ty0_comm (S55 : Ty) : (forall (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) ,
      ((subst_TmVar_Ty d s11 (subst_TmVar_Ty X0 s12 S55)) = (subst_TmVar_Ty X0 (subst_TmVar_Tm d s11 s12) (subst_TmVar_Ty (XS TmVar d) s11 S55)))) := (subst_TmVar__subst_TmVar_0_Ty_comm_ind S55 H0).
    Definition subst_TmVar_Tm_subst_TyVar_Tm0_comm (s12 : Tm) : (forall (d : (Trace TmVar)) (s11 : Tm) (S55 : Ty) ,
      ((subst_TmVar_Tm d s11 (subst_TyVar_Tm X0 S55 s12)) = (subst_TyVar_Tm X0 (subst_TmVar_Ty d s11 S55) (subst_TmVar_Tm (XS TyVar d) s11 s12)))) := (subst_TmVar__subst_TyVar_0_Tm_comm_ind s12 H0).
    Definition subst_TmVar_Ty_subst_TyVar_Ty0_comm (S56 : Ty) : (forall (d : (Trace TmVar)) (s11 : Tm) (S55 : Ty) ,
      ((subst_TmVar_Ty d s11 (subst_TyVar_Ty X0 S55 S56)) = (subst_TyVar_Ty X0 (subst_TmVar_Ty d s11 S55) (subst_TmVar_Ty (XS TyVar d) s11 S56)))) := (subst_TmVar__subst_TyVar_0_Ty_comm_ind S56 H0).
    Definition subst_TyVar_Tm_subst_TmVar_Tm0_comm (s12 : Tm) : (forall (d : (Trace TyVar)) (S55 : Ty) (s11 : Tm) ,
      ((subst_TyVar_Tm d S55 (subst_TmVar_Tm X0 s11 s12)) = (subst_TmVar_Tm X0 (subst_TyVar_Tm d S55 s11) (subst_TyVar_Tm (XS TmVar d) S55 s12)))) := (subst_TyVar__subst_TmVar_0_Tm_comm_ind s12 H0).
    Definition subst_TyVar_Ty_subst_TmVar_Ty0_comm (S56 : Ty) : (forall (d : (Trace TyVar)) (S55 : Ty) (s11 : Tm) ,
      ((subst_TyVar_Ty d S55 (subst_TmVar_Ty X0 s11 S56)) = (subst_TmVar_Ty X0 (subst_TyVar_Tm d S55 s11) (subst_TyVar_Ty (XS TmVar d) S55 S56)))) := (subst_TyVar__subst_TmVar_0_Ty_comm_ind S56 H0).
    Definition subst_TyVar_Tm_subst_TyVar_Tm0_comm (s11 : Tm) : (forall (d : (Trace TyVar)) (S55 : Ty) (S56 : Ty) ,
      ((subst_TyVar_Tm d S55 (subst_TyVar_Tm X0 S56 s11)) = (subst_TyVar_Tm X0 (subst_TyVar_Ty d S55 S56) (subst_TyVar_Tm (XS TyVar d) S55 s11)))) := (subst_TyVar__subst_TyVar_0_Tm_comm_ind s11 H0).
    Definition subst_TyVar_Ty_subst_TyVar_Ty0_comm (S57 : Ty) : (forall (d : (Trace TyVar)) (S55 : Ty) (S56 : Ty) ,
      ((subst_TyVar_Ty d S55 (subst_TyVar_Ty X0 S56 S57)) = (subst_TyVar_Ty X0 (subst_TyVar_Ty d S55 S56) (subst_TyVar_Ty (XS TyVar d) S55 S57)))) := (subst_TyVar__subst_TyVar_0_Ty_comm_ind S57 H0).
    Definition subst_TmVar_Kind_subst_TmVar_Kind0_comm (K42 : Kind) : (forall (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) ,
      ((subst_TmVar_Kind d s11 (subst_TmVar_Kind X0 s12 K42)) = (subst_TmVar_Kind X0 (subst_TmVar_Tm d s11 s12) (subst_TmVar_Kind (XS TmVar d) s11 K42)))) := (subst_TmVar__subst_TmVar_0_Kind_comm_ind K42 H0).
    Definition subst_TmVar_Kind_subst_TyVar_Kind0_comm (K42 : Kind) : (forall (d : (Trace TmVar)) (s11 : Tm) (S55 : Ty) ,
      ((subst_TmVar_Kind d s11 (subst_TyVar_Kind X0 S55 K42)) = (subst_TyVar_Kind X0 (subst_TmVar_Ty d s11 S55) (subst_TmVar_Kind (XS TyVar d) s11 K42)))) := (subst_TmVar__subst_TyVar_0_Kind_comm_ind K42 H0).
    Definition subst_TyVar_Kind_subst_TmVar_Kind0_comm (K42 : Kind) : (forall (d : (Trace TyVar)) (S55 : Ty) (s11 : Tm) ,
      ((subst_TyVar_Kind d S55 (subst_TmVar_Kind X0 s11 K42)) = (subst_TmVar_Kind X0 (subst_TyVar_Tm d S55 s11) (subst_TyVar_Kind (XS TmVar d) S55 K42)))) := (subst_TyVar__subst_TmVar_0_Kind_comm_ind K42 H0).
    Definition subst_TyVar_Kind_subst_TyVar_Kind0_comm (K42 : Kind) : (forall (d : (Trace TyVar)) (S55 : Ty) (S56 : Ty) ,
      ((subst_TyVar_Kind d S55 (subst_TyVar_Kind X0 S56 K42)) = (subst_TyVar_Kind X0 (subst_TyVar_Ty d S55 S56) (subst_TyVar_Kind (XS TyVar d) S55 K42)))) := (subst_TyVar__subst_TyVar_0_Kind_comm_ind K42 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTm_subst_TmVar_Tm  :
      (forall (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) ,
        ((weakenTm (subst_TmVar_Tm d s11 s12) k) = (subst_TmVar_Tm (weakenTrace d k) s11 (weakenTm s12 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTy_subst_TmVar_Ty  :
      (forall (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (S55 : Ty) ,
        ((weakenTy (subst_TmVar_Ty d s11 S55) k) = (subst_TmVar_Ty (weakenTrace d k) s11 (weakenTy S55 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_subst_TyVar_Tm  :
      (forall (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) (s11 : Tm) ,
        ((weakenTm (subst_TyVar_Tm d S55 s11) k) = (subst_TyVar_Tm (weakenTrace d k) S55 (weakenTm s11 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTy_subst_TyVar_Ty  :
      (forall (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) (S56 : Ty) ,
        ((weakenTy (subst_TyVar_Ty d S55 S56) k) = (subst_TyVar_Ty (weakenTrace d k) S55 (weakenTy S56 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenKind_subst_TmVar_Kind  :
      (forall (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (K42 : Kind) ,
        ((weakenKind (subst_TmVar_Kind d s11 K42) k) = (subst_TmVar_Kind (weakenTrace d k) s11 (weakenKind K42 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenKind_subst_TyVar_Kind  :
      (forall (k : Hvl) (d : (Trace TyVar)) (S55 : Ty) (K42 : Kind) ,
        ((weakenKind (subst_TyVar_Kind d S55 K42) k) = (subst_TyVar_Kind (weakenTrace d k) S55 (weakenKind K42 k)))).
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
    | wfTm_var
        (x66 : (Index TmVar))
        (wfi : (wfindex k x66)) :
        (wfTm k (var x66))
    | wfTm_abs {T86 : Ty}
        (wf : (wfTy k T86)) {t76 : Tm}
        (wf0 : (wfTm (HS TmVar k) t76))
        : (wfTm k (abs T86 t76))
    | wfTm_app {t77 : Tm}
        (wf : (wfTm k t77)) {t78 : Tm}
        (wf0 : (wfTm k t78)) :
        (wfTm k (app t77 t78))
    | wfTm_pair {t79 : Tm}
        (wf : (wfTm k t79)) {t80 : Tm}
        (wf0 : (wfTm k t80)) {S55 : Ty}
        (wf1 : (wfTy k S55)) {T87 : Ty}
        (wf2 : (wfTy (HS TmVar k) T87))
        :
        (wfTm k (pair t79 t80 S55 T87))
    | wfTm_prj1 {t81 : Tm}
        (wf : (wfTm k t81)) :
        (wfTm k (prj1 t81))
    | wfTm_prj2 {t82 : Tm}
        (wf : (wfTm k t82)) :
        (wfTm k (prj2 t82))
  with wfTy (k : Hvl) : Ty -> Prop :=
    | wfTy_tvar
        (X5 : (Index TyVar))
        (wfi : (wfindex k X5)) :
        (wfTy k (tvar X5))
    | wfTy_tpi {T86 : Ty}
        (wf : (wfTy k T86)) {T87 : Ty}
        (wf0 : (wfTy (HS TmVar k) T87))
        : (wfTy k (tpi T86 T87))
    | wfTy_tapp {T88 : Ty}
        (wf : (wfTy k T88)) {t76 : Tm}
        (wf0 : (wfTm k t76)) :
        (wfTy k (tapp T88 t76))
    | wfTy_tsig {T89 : Ty}
        (wf : (wfTy k T89)) {U2 : Ty}
        (wf0 : (wfTy (HS TmVar k) U2)) :
        (wfTy k (tsig T89 U2)).
  Inductive wfKind (k : Hvl) : Kind -> Prop :=
    | wfKind_star :
        (wfKind k (star))
    | wfKind_kpi {T86 : Ty}
        (wf : (wfTy k T86)) {K42 : Kind}
        (wf0 : (wfKind (HS TmVar k) K42))
        : (wfKind k (kpi T86 K42)).
  Definition inversion_wfTm_var_1 (k : Hvl) (x : (Index TmVar)) (H23 : (wfTm k (var x))) : (wfindex k x) := match H23 in (wfTm _ s11) return match s11 return Prop with
    | (var x) => (wfindex k x)
    | _ => True
  end with
    | (wfTm_var x H1) => H1
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k0 : Hvl) (T : Ty) (t : Tm) (H24 : (wfTm k0 (abs T t))) : (wfTy k0 T) := match H24 in (wfTm _ s12) return match s12 return Prop with
    | (abs T t) => (wfTy k0 T)
    | _ => True
  end with
    | (wfTm_abs T H2 t H3) => H2
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k0 : Hvl) (T : Ty) (t : Tm) (H24 : (wfTm k0 (abs T t))) : (wfTm (HS TmVar k0) t) := match H24 in (wfTm _ s12) return match s12 return Prop with
    | (abs T t) => (wfTm (HS TmVar k0) t)
    | _ => True
  end with
    | (wfTm_abs T H2 t H3) => H3
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k1 : Hvl) (t1 : Tm) (t2 : Tm) (H25 : (wfTm k1 (app t1 t2))) : (wfTm k1 t1) := match H25 in (wfTm _ s13) return match s13 return Prop with
    | (app t1 t2) => (wfTm k1 t1)
    | _ => True
  end with
    | (wfTm_app t1 H4 t2 H5) => H4
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k1 : Hvl) (t1 : Tm) (t2 : Tm) (H25 : (wfTm k1 (app t1 t2))) : (wfTm k1 t2) := match H25 in (wfTm _ s13) return match s13 return Prop with
    | (app t1 t2) => (wfTm k1 t2)
    | _ => True
  end with
    | (wfTm_app t1 H4 t2 H5) => H5
    | _ => I
  end.
  Definition inversion_wfTm_pair_0 (k2 : Hvl) (t1 : Tm) (t2 : Tm) (S1 : Ty) (T : Ty) (H26 : (wfTm k2 (pair t1 t2 S1 T))) : (wfTm k2 t1) := match H26 in (wfTm _ s14) return match s14 return Prop with
    | (pair t1 t2 S1 T) => (wfTm k2 t1)
    | _ => True
  end with
    | (wfTm_pair t1 H6 t2 H7 S1 H8 T H9) => H6
    | _ => I
  end.
  Definition inversion_wfTm_pair_1 (k2 : Hvl) (t1 : Tm) (t2 : Tm) (S1 : Ty) (T : Ty) (H26 : (wfTm k2 (pair t1 t2 S1 T))) : (wfTm k2 t2) := match H26 in (wfTm _ s14) return match s14 return Prop with
    | (pair t1 t2 S1 T) => (wfTm k2 t2)
    | _ => True
  end with
    | (wfTm_pair t1 H6 t2 H7 S1 H8 T H9) => H7
    | _ => I
  end.
  Definition inversion_wfTm_pair_3 (k2 : Hvl) (t1 : Tm) (t2 : Tm) (S1 : Ty) (T : Ty) (H26 : (wfTm k2 (pair t1 t2 S1 T))) : (wfTy k2 S1) := match H26 in (wfTm _ s14) return match s14 return Prop with
    | (pair t1 t2 S1 T) => (wfTy k2 S1)
    | _ => True
  end with
    | (wfTm_pair t1 H6 t2 H7 S1 H8 T H9) => H8
    | _ => I
  end.
  Definition inversion_wfTm_pair_4 (k2 : Hvl) (t1 : Tm) (t2 : Tm) (S1 : Ty) (T : Ty) (H26 : (wfTm k2 (pair t1 t2 S1 T))) : (wfTy (HS TmVar k2) T) := match H26 in (wfTm _ s14) return match s14 return Prop with
    | (pair t1 t2 S1 T) => (wfTy (HS TmVar k2) T)
    | _ => True
  end with
    | (wfTm_pair t1 H6 t2 H7 S1 H8 T H9) => H9
    | _ => I
  end.
  Definition inversion_wfTm_prj1_0 (k3 : Hvl) (t : Tm) (H27 : (wfTm k3 (prj1 t))) : (wfTm k3 t) := match H27 in (wfTm _ s15) return match s15 return Prop with
    | (prj1 t) => (wfTm k3 t)
    | _ => True
  end with
    | (wfTm_prj1 t H10) => H10
    | _ => I
  end.
  Definition inversion_wfTm_prj2_0 (k4 : Hvl) (t : Tm) (H28 : (wfTm k4 (prj2 t))) : (wfTm k4 t) := match H28 in (wfTm _ s16) return match s16 return Prop with
    | (prj2 t) => (wfTm k4 t)
    | _ => True
  end with
    | (wfTm_prj2 t H11) => H11
    | _ => I
  end.
  Definition inversion_wfTy_tvar_1 (k5 : Hvl) (X : (Index TyVar)) (H29 : (wfTy k5 (tvar X))) : (wfindex k5 X) := match H29 in (wfTy _ S55) return match S55 return Prop with
    | (tvar X) => (wfindex k5 X)
    | _ => True
  end with
    | (wfTy_tvar X H12) => H12
    | _ => I
  end.
  Definition inversion_wfTy_tpi_1 (k6 : Hvl) (T1 : Ty) (T2 : Ty) (H30 : (wfTy k6 (tpi T1 T2))) : (wfTy k6 T1) := match H30 in (wfTy _ S56) return match S56 return Prop with
    | (tpi T1 T2) => (wfTy k6 T1)
    | _ => True
  end with
    | (wfTy_tpi T1 H13 T2 H14) => H13
    | _ => I
  end.
  Definition inversion_wfTy_tpi_2 (k6 : Hvl) (T1 : Ty) (T2 : Ty) (H30 : (wfTy k6 (tpi T1 T2))) : (wfTy (HS TmVar k6) T2) := match H30 in (wfTy _ S56) return match S56 return Prop with
    | (tpi T1 T2) => (wfTy (HS TmVar k6) T2)
    | _ => True
  end with
    | (wfTy_tpi T1 H13 T2 H14) => H14
    | _ => I
  end.
  Definition inversion_wfTy_tapp_0 (k7 : Hvl) (T : Ty) (t : Tm) (H31 : (wfTy k7 (tapp T t))) : (wfTy k7 T) := match H31 in (wfTy _ S57) return match S57 return Prop with
    | (tapp T t) => (wfTy k7 T)
    | _ => True
  end with
    | (wfTy_tapp T H15 t H16) => H15
    | _ => I
  end.
  Definition inversion_wfTy_tapp_1 (k7 : Hvl) (T : Ty) (t : Tm) (H31 : (wfTy k7 (tapp T t))) : (wfTm k7 t) := match H31 in (wfTy _ S57) return match S57 return Prop with
    | (tapp T t) => (wfTm k7 t)
    | _ => True
  end with
    | (wfTy_tapp T H15 t H16) => H16
    | _ => I
  end.
  Definition inversion_wfTy_tsig_1 (k8 : Hvl) (T : Ty) (U : Ty) (H32 : (wfTy k8 (tsig T U))) : (wfTy k8 T) := match H32 in (wfTy _ S58) return match S58 return Prop with
    | (tsig T U) => (wfTy k8 T)
    | _ => True
  end with
    | (wfTy_tsig T H17 U H18) => H17
    | _ => I
  end.
  Definition inversion_wfTy_tsig_2 (k8 : Hvl) (T : Ty) (U : Ty) (H32 : (wfTy k8 (tsig T U))) : (wfTy (HS TmVar k8) U) := match H32 in (wfTy _ S58) return match S58 return Prop with
    | (tsig T U) => (wfTy (HS TmVar k8) U)
    | _ => True
  end with
    | (wfTy_tsig T H17 U H18) => H18
    | _ => I
  end.
  Definition inversion_wfKind_kpi_1 (k10 : Hvl) (T : Ty) (K : Kind) (H34 : (wfKind k10 (kpi T K))) : (wfTy k10 T) := match H34 in (wfKind _ K43) return match K43 return Prop with
    | (kpi T K) => (wfTy k10 T)
    | _ => True
  end with
    | (wfKind_kpi T H19 K H20) => H19
    | _ => I
  end.
  Definition inversion_wfKind_kpi_2 (k10 : Hvl) (T : Ty) (K : Kind) (H34 : (wfKind k10 (kpi T K))) : (wfKind (HS TmVar k10) K) := match H34 in (wfKind _ K43) return match K43 return Prop with
    | (kpi T K) => (wfKind (HS TmVar k10) K)
    | _ => True
  end with
    | (wfKind_kpi T H19 K H20) => H20
    | _ => I
  end.
  Scheme ind_wfTm := Induction for wfTm Sort Prop
  with ind_wfTy := Induction for wfTy Sort Prop.
  Combined Scheme ind_wfTm_Ty from ind_wfTm, ind_wfTy.
  Scheme ind_wfKind := Induction for wfKind Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_TmVar : (forall (c : (Cutoff TmVar)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | shifthvl_TmVar_here
        (k11 : Hvl) :
        (shifthvl_TmVar C0 k11 (HS TmVar k11))
    | shifthvl_TmVar_there_TmVar
        (c : (Cutoff TmVar)) (k11 : Hvl)
        (k12 : Hvl) :
        (shifthvl_TmVar c k11 k12) -> (shifthvl_TmVar (CS c) (HS TmVar k11) (HS TmVar k12))
    | shifthvl_TmVar_there_TyVar
        (c : (Cutoff TmVar)) (k11 : Hvl)
        (k12 : Hvl) :
        (shifthvl_TmVar c k11 k12) -> (shifthvl_TmVar c (HS TyVar k11) (HS TyVar k12)).
  Inductive shifthvl_TyVar : (forall (c : (Cutoff TyVar)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | shifthvl_TyVar_here
        (k11 : Hvl) :
        (shifthvl_TyVar C0 k11 (HS TyVar k11))
    | shifthvl_TyVar_there_TmVar
        (c : (Cutoff TyVar)) (k11 : Hvl)
        (k12 : Hvl) :
        (shifthvl_TyVar c k11 k12) -> (shifthvl_TyVar c (HS TmVar k11) (HS TmVar k12))
    | shifthvl_TyVar_there_TyVar
        (c : (Cutoff TyVar)) (k11 : Hvl)
        (k12 : Hvl) :
        (shifthvl_TyVar c k11 k12) -> (shifthvl_TyVar (CS c) (HS TyVar k11) (HS TyVar k12)).
  Lemma weaken_shifthvl_TmVar  :
    (forall (k11 : Hvl) {c : (Cutoff TmVar)} {k12 : Hvl} {k13 : Hvl} ,
      (shifthvl_TmVar c k12 k13) -> (shifthvl_TmVar (weakenCutoffTmVar c k11) (appendHvl k12 k11) (appendHvl k13 k11))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_TyVar  :
    (forall (k11 : Hvl) {c : (Cutoff TyVar)} {k12 : Hvl} {k13 : Hvl} ,
      (shifthvl_TyVar c k12 k13) -> (shifthvl_TyVar (weakenCutoffTyVar c k11) (appendHvl k12 k11) (appendHvl k13 k11))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_TmVar__wfindex_TmVar  :
    (forall (c : (Cutoff TmVar)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_TmVar c k11 k12)) (x66 : (Index TmVar)) ,
      (wfindex k11 x66) -> (wfindex k12 (shift_TmVar_Index c x66))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TmVar__wfindex_TyVar  :
    (forall (c : (Cutoff TmVar)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_TmVar c k11 k12)) (X5 : (Index TyVar)) ,
      (wfindex k11 X5) -> (wfindex k12 X5)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TyVar__wfindex_TmVar  :
    (forall (c : (Cutoff TyVar)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_TyVar c k11 k12)) (x66 : (Index TmVar)) ,
      (wfindex k11 x66) -> (wfindex k12 x66)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TyVar__wfindex_TyVar  :
    (forall (c : (Cutoff TyVar)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_TyVar c k11 k12)) (X5 : (Index TyVar)) ,
      (wfindex k11 X5) -> (wfindex k12 (shift_TyVar_Index c X5))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_TmVar__wfTm_Ty : (forall (k11 : Hvl) ,
    (forall (s17 : Tm) (wf : (wfTm k11 s17)) ,
      (forall (c : (Cutoff TmVar)) (k12 : Hvl) ,
        (shifthvl_TmVar c k11 k12) -> (wfTm k12 (shift_TmVar_Tm c s17)))) /\
    (forall (S59 : Ty) (wf : (wfTy k11 S59)) ,
      (forall (c : (Cutoff TmVar)) (k12 : Hvl) ,
        (shifthvl_TmVar c k11 k12) -> (wfTy k12 (shift_TmVar_Ty c S59))))) := (ind_wfTm_Ty (fun (k11 : Hvl) (s17 : Tm) (wf : (wfTm k11 s17)) =>
    (forall (c : (Cutoff TmVar)) (k12 : Hvl) ,
      (shifthvl_TmVar c k11 k12) -> (wfTm k12 (shift_TmVar_Tm c s17)))) (fun (k11 : Hvl) (S59 : Ty) (wf : (wfTy k11 S59)) =>
    (forall (c : (Cutoff TmVar)) (k12 : Hvl) ,
      (shifthvl_TmVar c k11 k12) -> (wfTy k12 (shift_TmVar_Ty c S59)))) (fun (k11 : Hvl) (x66 : (Index TmVar)) (wfi : (wfindex k11 x66)) (c : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c k11 k12)) =>
    (wfTm_var k12 _ (shift_TmVar__wfindex_TmVar c k11 k12 ins x66 wfi))) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) IHT (t : Tm) (wf0 : (wfTm (HS TmVar k11) t)) IHt (c : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c k11 k12)) =>
    (wfTm_abs k12 (IHT c k12 (weaken_shifthvl_TmVar H0 ins)) (IHt (CS c) (HS TmVar k12) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k11 : Hvl) (t1 : Tm) (wf : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k11 t2)) IHt2 (c : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c k11 k12)) =>
    (wfTm_app k12 (IHt1 c k12 (weaken_shifthvl_TmVar H0 ins)) (IHt2 c k12 (weaken_shifthvl_TmVar H0 ins)))) (fun (k11 : Hvl) (t1 : Tm) (wf : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k11 t2)) IHt2 (S1 : Ty) (wf1 : (wfTy k11 S1)) IHS1 (T : Ty) (wf2 : (wfTy (HS TmVar k11) T)) IHT (c : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c k11 k12)) =>
    (wfTm_pair k12 (IHt1 c k12 (weaken_shifthvl_TmVar H0 ins)) (IHt2 c k12 (weaken_shifthvl_TmVar H0 ins)) (IHS1 c k12 (weaken_shifthvl_TmVar H0 ins)) (IHT (CS c) (HS TmVar k12) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k11 : Hvl) (t : Tm) (wf : (wfTm k11 t)) IHt (c : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c k11 k12)) =>
    (wfTm_prj1 k12 (IHt c k12 (weaken_shifthvl_TmVar H0 ins)))) (fun (k11 : Hvl) (t : Tm) (wf : (wfTm k11 t)) IHt (c : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c k11 k12)) =>
    (wfTm_prj2 k12 (IHt c k12 (weaken_shifthvl_TmVar H0 ins)))) (fun (k11 : Hvl) (X5 : (Index TyVar)) (wfi : (wfindex k11 X5)) (c : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c k11 k12)) =>
    (wfTy_tvar k12 _ (shift_TmVar__wfindex_TyVar c k11 k12 ins X5 wfi))) (fun (k11 : Hvl) (T1 : Ty) (wf : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS TmVar k11) T2)) IHT2 (c : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c k11 k12)) =>
    (wfTy_tpi k12 (IHT1 c k12 (weaken_shifthvl_TmVar H0 ins)) (IHT2 (CS c) (HS TmVar k12) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) IHT (t : Tm) (wf0 : (wfTm k11 t)) IHt (c : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c k11 k12)) =>
    (wfTy_tapp k12 (IHT c k12 (weaken_shifthvl_TmVar H0 ins)) (IHt c k12 (weaken_shifthvl_TmVar H0 ins)))) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) IHT (U : Ty) (wf0 : (wfTy (HS TmVar k11) U)) IHU (c : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c k11 k12)) =>
    (wfTy_tsig k12 (IHT c k12 (weaken_shifthvl_TmVar H0 ins)) (IHU (CS c) (HS TmVar k12) (weaken_shifthvl_TmVar (HS TmVar H0) ins))))).
  Lemma shift_TmVar__wfTm (k11 : Hvl) :
    (forall (s17 : Tm) (wf : (wfTm k11 s17)) ,
      (forall (c : (Cutoff TmVar)) (k12 : Hvl) ,
        (shifthvl_TmVar c k11 k12) -> (wfTm k12 (shift_TmVar_Tm c s17)))).
  Proof.
    pose proof ((shift_TmVar__wfTm_Ty k11)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_TmVar__wfTy (k11 : Hvl) :
    (forall (S59 : Ty) (wf0 : (wfTy k11 S59)) ,
      (forall (c0 : (Cutoff TmVar)) (k13 : Hvl) ,
        (shifthvl_TmVar c0 k11 k13) -> (wfTy k13 (shift_TmVar_Ty c0 S59)))).
  Proof.
    pose proof ((shift_TmVar__wfTm_Ty k11)).
    destruct_conjs .
    easy .
  Qed.
  Definition shift_TyVar__wfTm_Ty : (forall (k11 : Hvl) ,
    (forall (s17 : Tm) (wf : (wfTm k11 s17)) ,
      (forall (c : (Cutoff TyVar)) (k12 : Hvl) ,
        (shifthvl_TyVar c k11 k12) -> (wfTm k12 (shift_TyVar_Tm c s17)))) /\
    (forall (S59 : Ty) (wf : (wfTy k11 S59)) ,
      (forall (c : (Cutoff TyVar)) (k12 : Hvl) ,
        (shifthvl_TyVar c k11 k12) -> (wfTy k12 (shift_TyVar_Ty c S59))))) := (ind_wfTm_Ty (fun (k11 : Hvl) (s17 : Tm) (wf : (wfTm k11 s17)) =>
    (forall (c : (Cutoff TyVar)) (k12 : Hvl) ,
      (shifthvl_TyVar c k11 k12) -> (wfTm k12 (shift_TyVar_Tm c s17)))) (fun (k11 : Hvl) (S59 : Ty) (wf : (wfTy k11 S59)) =>
    (forall (c : (Cutoff TyVar)) (k12 : Hvl) ,
      (shifthvl_TyVar c k11 k12) -> (wfTy k12 (shift_TyVar_Ty c S59)))) (fun (k11 : Hvl) (x66 : (Index TmVar)) (wfi : (wfindex k11 x66)) (c : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c k11 k12)) =>
    (wfTm_var k12 _ (shift_TyVar__wfindex_TmVar c k11 k12 ins x66 wfi))) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) IHT (t : Tm) (wf0 : (wfTm (HS TmVar k11) t)) IHt (c : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c k11 k12)) =>
    (wfTm_abs k12 (IHT c k12 (weaken_shifthvl_TyVar H0 ins)) (IHt c (HS TmVar k12) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k11 : Hvl) (t1 : Tm) (wf : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k11 t2)) IHt2 (c : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c k11 k12)) =>
    (wfTm_app k12 (IHt1 c k12 (weaken_shifthvl_TyVar H0 ins)) (IHt2 c k12 (weaken_shifthvl_TyVar H0 ins)))) (fun (k11 : Hvl) (t1 : Tm) (wf : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k11 t2)) IHt2 (S1 : Ty) (wf1 : (wfTy k11 S1)) IHS1 (T : Ty) (wf2 : (wfTy (HS TmVar k11) T)) IHT (c : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c k11 k12)) =>
    (wfTm_pair k12 (IHt1 c k12 (weaken_shifthvl_TyVar H0 ins)) (IHt2 c k12 (weaken_shifthvl_TyVar H0 ins)) (IHS1 c k12 (weaken_shifthvl_TyVar H0 ins)) (IHT c (HS TmVar k12) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k11 : Hvl) (t : Tm) (wf : (wfTm k11 t)) IHt (c : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c k11 k12)) =>
    (wfTm_prj1 k12 (IHt c k12 (weaken_shifthvl_TyVar H0 ins)))) (fun (k11 : Hvl) (t : Tm) (wf : (wfTm k11 t)) IHt (c : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c k11 k12)) =>
    (wfTm_prj2 k12 (IHt c k12 (weaken_shifthvl_TyVar H0 ins)))) (fun (k11 : Hvl) (X5 : (Index TyVar)) (wfi : (wfindex k11 X5)) (c : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c k11 k12)) =>
    (wfTy_tvar k12 _ (shift_TyVar__wfindex_TyVar c k11 k12 ins X5 wfi))) (fun (k11 : Hvl) (T1 : Ty) (wf : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS TmVar k11) T2)) IHT2 (c : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c k11 k12)) =>
    (wfTy_tpi k12 (IHT1 c k12 (weaken_shifthvl_TyVar H0 ins)) (IHT2 c (HS TmVar k12) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) IHT (t : Tm) (wf0 : (wfTm k11 t)) IHt (c : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c k11 k12)) =>
    (wfTy_tapp k12 (IHT c k12 (weaken_shifthvl_TyVar H0 ins)) (IHt c k12 (weaken_shifthvl_TyVar H0 ins)))) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) IHT (U : Ty) (wf0 : (wfTy (HS TmVar k11) U)) IHU (c : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c k11 k12)) =>
    (wfTy_tsig k12 (IHT c k12 (weaken_shifthvl_TyVar H0 ins)) (IHU c (HS TmVar k12) (weaken_shifthvl_TyVar (HS TmVar H0) ins))))).
  Lemma shift_TyVar__wfTm (k11 : Hvl) :
    (forall (s17 : Tm) (wf : (wfTm k11 s17)) ,
      (forall (c : (Cutoff TyVar)) (k12 : Hvl) ,
        (shifthvl_TyVar c k11 k12) -> (wfTm k12 (shift_TyVar_Tm c s17)))).
  Proof.
    pose proof ((shift_TyVar__wfTm_Ty k11)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_TyVar__wfTy (k11 : Hvl) :
    (forall (S59 : Ty) (wf0 : (wfTy k11 S59)) ,
      (forall (c0 : (Cutoff TyVar)) (k13 : Hvl) ,
        (shifthvl_TyVar c0 k11 k13) -> (wfTy k13 (shift_TyVar_Ty c0 S59)))).
  Proof.
    pose proof ((shift_TyVar__wfTm_Ty k11)).
    destruct_conjs .
    easy .
  Qed.
  Definition shift_TmVar__wfKind : (forall (k11 : Hvl) ,
    (forall (K44 : Kind) (wf : (wfKind k11 K44)) ,
      (forall (c : (Cutoff TmVar)) (k12 : Hvl) ,
        (shifthvl_TmVar c k11 k12) -> (wfKind k12 (shift_TmVar_Kind c K44))))) := (ind_wfKind (fun (k11 : Hvl) (K44 : Kind) (wf : (wfKind k11 K44)) =>
    (forall (c : (Cutoff TmVar)) (k12 : Hvl) ,
      (shifthvl_TmVar c k11 k12) -> (wfKind k12 (shift_TmVar_Kind c K44)))) (fun (k11 : Hvl) (c : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c k11 k12)) =>
    (wfKind_star k12)) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) (K : Kind) (wf0 : (wfKind (HS TmVar k11) K)) IHK (c : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c k11 k12)) =>
    (wfKind_kpi k12 (shift_TmVar__wfTy k11 T wf c k12 (weaken_shifthvl_TmVar H0 ins)) (IHK (CS c) (HS TmVar k12) (weaken_shifthvl_TmVar (HS TmVar H0) ins))))).
  Definition shift_TyVar__wfKind : (forall (k11 : Hvl) ,
    (forall (K44 : Kind) (wf : (wfKind k11 K44)) ,
      (forall (c : (Cutoff TyVar)) (k12 : Hvl) ,
        (shifthvl_TyVar c k11 k12) -> (wfKind k12 (shift_TyVar_Kind c K44))))) := (ind_wfKind (fun (k11 : Hvl) (K44 : Kind) (wf : (wfKind k11 K44)) =>
    (forall (c : (Cutoff TyVar)) (k12 : Hvl) ,
      (shifthvl_TyVar c k11 k12) -> (wfKind k12 (shift_TyVar_Kind c K44)))) (fun (k11 : Hvl) (c : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c k11 k12)) =>
    (wfKind_star k12)) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) (K : Kind) (wf0 : (wfKind (HS TmVar k11) K)) IHK (c : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c k11 k12)) =>
    (wfKind_kpi k12 (shift_TyVar__wfTy k11 T wf c k12 (weaken_shifthvl_TyVar H0 ins)) (IHK c (HS TmVar k12) (weaken_shifthvl_TyVar (HS TmVar H0) ins))))).
  Fixpoint weaken_wfTm (k11 : Hvl) {struct k11} :
  (forall (k12 : Hvl) (s17 : Tm) (wf : (wfTm k12 s17)) ,
    (wfTm (appendHvl k12 k11) (weakenTm s17 k11))) :=
    match k11 return (forall (k12 : Hvl) (s17 : Tm) (wf : (wfTm k12 s17)) ,
      (wfTm (appendHvl k12 k11) (weakenTm s17 k11))) with
      | (H0) => (fun (k12 : Hvl) (s17 : Tm) (wf : (wfTm k12 s17)) =>
        wf)
      | (HS TmVar k11) => (fun (k12 : Hvl) (s17 : Tm) (wf : (wfTm k12 s17)) =>
        (shift_TmVar__wfTm (appendHvl k12 k11) (weakenTm s17 k11) (weaken_wfTm k11 k12 s17 wf) C0 (HS TmVar (appendHvl k12 k11)) (shifthvl_TmVar_here (appendHvl k12 k11))))
      | (HS TyVar k11) => (fun (k12 : Hvl) (s17 : Tm) (wf : (wfTm k12 s17)) =>
        (shift_TyVar__wfTm (appendHvl k12 k11) (weakenTm s17 k11) (weaken_wfTm k11 k12 s17 wf) C0 (HS TyVar (appendHvl k12 k11)) (shifthvl_TyVar_here (appendHvl k12 k11))))
    end.
  Fixpoint weaken_wfTy (k11 : Hvl) {struct k11} :
  (forall (k12 : Hvl) (S59 : Ty) (wf : (wfTy k12 S59)) ,
    (wfTy (appendHvl k12 k11) (weakenTy S59 k11))) :=
    match k11 return (forall (k12 : Hvl) (S59 : Ty) (wf : (wfTy k12 S59)) ,
      (wfTy (appendHvl k12 k11) (weakenTy S59 k11))) with
      | (H0) => (fun (k12 : Hvl) (S59 : Ty) (wf : (wfTy k12 S59)) =>
        wf)
      | (HS TmVar k11) => (fun (k12 : Hvl) (S59 : Ty) (wf : (wfTy k12 S59)) =>
        (shift_TmVar__wfTy (appendHvl k12 k11) (weakenTy S59 k11) (weaken_wfTy k11 k12 S59 wf) C0 (HS TmVar (appendHvl k12 k11)) (shifthvl_TmVar_here (appendHvl k12 k11))))
      | (HS TyVar k11) => (fun (k12 : Hvl) (S59 : Ty) (wf : (wfTy k12 S59)) =>
        (shift_TyVar__wfTy (appendHvl k12 k11) (weakenTy S59 k11) (weaken_wfTy k11 k12 S59 wf) C0 (HS TyVar (appendHvl k12 k11)) (shifthvl_TyVar_here (appendHvl k12 k11))))
    end.
  Fixpoint weaken_wfKind (k11 : Hvl) {struct k11} :
  (forall (k12 : Hvl) (K44 : Kind) (wf : (wfKind k12 K44)) ,
    (wfKind (appendHvl k12 k11) (weakenKind K44 k11))) :=
    match k11 return (forall (k12 : Hvl) (K44 : Kind) (wf : (wfKind k12 K44)) ,
      (wfKind (appendHvl k12 k11) (weakenKind K44 k11))) with
      | (H0) => (fun (k12 : Hvl) (K44 : Kind) (wf : (wfKind k12 K44)) =>
        wf)
      | (HS TmVar k11) => (fun (k12 : Hvl) (K44 : Kind) (wf : (wfKind k12 K44)) =>
        (shift_TmVar__wfKind (appendHvl k12 k11) (weakenKind K44 k11) (weaken_wfKind k11 k12 K44 wf) C0 (HS TmVar (appendHvl k12 k11)) (shifthvl_TmVar_here (appendHvl k12 k11))))
      | (HS TyVar k11) => (fun (k12 : Hvl) (K44 : Kind) (wf : (wfKind k12 K44)) =>
        (shift_TyVar__wfKind (appendHvl k12 k11) (weakenKind K44 k11) (weaken_wfKind k11 k12 K44 wf) C0 (HS TyVar (appendHvl k12 k11)) (shifthvl_TyVar_here (appendHvl k12 k11))))
    end.
End ShiftWellFormed.
Lemma wfTm_cast  :
  (forall (k11 : Hvl) (s17 : Tm) (k12 : Hvl) (s18 : Tm) ,
    (k11 = k12) -> (s17 = s18) -> (wfTm k11 s17) -> (wfTm k12 s18)).
Proof.
  congruence .
Qed.
Lemma wfTy_cast  :
  (forall (k11 : Hvl) (S59 : Ty) (k12 : Hvl) (S60 : Ty) ,
    (k11 = k12) -> (S59 = S60) -> (wfTy k11 S59) -> (wfTy k12 S60)).
Proof.
  congruence .
Qed.
Lemma wfKind_cast  :
  (forall (k11 : Hvl) (K44 : Kind) (k12 : Hvl) (K45 : Kind) ,
    (k11 = k12) -> (K44 = K45) -> (wfKind k11 K44) -> (wfKind k12 K45)).
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
  Inductive substhvl_TmVar (k11 : Hvl) : (forall (d : (Trace TmVar)) (k12 : Hvl) (k13 : Hvl) ,
    Prop) :=
    | substhvl_TmVar_here :
        (substhvl_TmVar k11 X0 (HS TmVar k11) k11)
    | substhvl_TmVar_there_TmVar
        {d : (Trace TmVar)} {k12 : Hvl}
        {k13 : Hvl} :
        (substhvl_TmVar k11 d k12 k13) -> (substhvl_TmVar k11 (XS TmVar d) (HS TmVar k12) (HS TmVar k13))
    | substhvl_TmVar_there_TyVar
        {d : (Trace TmVar)} {k12 : Hvl}
        {k13 : Hvl} :
        (substhvl_TmVar k11 d k12 k13) -> (substhvl_TmVar k11 (XS TyVar d) (HS TyVar k12) (HS TyVar k13)).
  Inductive substhvl_TyVar (k11 : Hvl) : (forall (d : (Trace TyVar)) (k12 : Hvl) (k13 : Hvl) ,
    Prop) :=
    | substhvl_TyVar_here :
        (substhvl_TyVar k11 X0 (HS TyVar k11) k11)
    | substhvl_TyVar_there_TmVar
        {d : (Trace TyVar)} {k12 : Hvl}
        {k13 : Hvl} :
        (substhvl_TyVar k11 d k12 k13) -> (substhvl_TyVar k11 (XS TmVar d) (HS TmVar k12) (HS TmVar k13))
    | substhvl_TyVar_there_TyVar
        {d : (Trace TyVar)} {k12 : Hvl}
        {k13 : Hvl} :
        (substhvl_TyVar k11 d k12 k13) -> (substhvl_TyVar k11 (XS TyVar d) (HS TyVar k12) (HS TyVar k13)).
  Lemma weaken_substhvl_TmVar  :
    (forall {k12 : Hvl} (k11 : Hvl) {d : (Trace TmVar)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_TmVar k12 d k13 k14) -> (substhvl_TmVar k12 (weakenTrace d k11) (appendHvl k13 k11) (appendHvl k14 k11))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_TyVar  :
    (forall {k12 : Hvl} (k11 : Hvl) {d : (Trace TyVar)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_TyVar k12 d k13 k14) -> (substhvl_TyVar k12 (weakenTrace d k11) (appendHvl k13 k11) (appendHvl k14 k11))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_TmVar_wfindex_TmVar {k11 : Hvl} {s17 : Tm} (wft : (wfTm k11 s17)) :
    (forall {d : (Trace TmVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TmVar k11 d k12 k13) -> (forall {x66 : (Index TmVar)} ,
        (wfindex k12 x66) -> (wfTm k13 (subst_TmVar_Index d s17 x66)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TyVar_wfindex_TyVar {k11 : Hvl} {S59 : Ty} (wft : (wfTy k11 S59)) :
    (forall {d : (Trace TyVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TyVar k11 d k12 k13) -> (forall {X5 : (Index TyVar)} ,
        (wfindex k12 X5) -> (wfTy k13 (subst_TyVar_Index d S59 X5)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TmVar_wfindex_TyVar {k11 : Hvl} :
    (forall {d : (Trace TmVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TmVar k11 d k12 k13) -> (forall {X5 : (Index TyVar)} ,
        (wfindex k12 X5) -> (wfindex k13 X5))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_TyVar_wfindex_TmVar {k11 : Hvl} :
    (forall {d : (Trace TyVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TyVar k11 d k12 k13) -> (forall {x66 : (Index TmVar)} ,
        (wfindex k12 x66) -> (wfindex k13 x66))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_TmVar_wfTm_Ty {k11 : Hvl} {s17 : Tm} (wf : (wfTm k11 s17)) : (forall (k12 : Hvl) ,
    (forall (s18 : Tm) (wf0 : (wfTm k12 s18)) ,
      (forall {d : (Trace TmVar)} {k13 : Hvl} ,
        (substhvl_TmVar k11 d k12 k13) -> (wfTm k13 (subst_TmVar_Tm d s17 s18)))) /\
    (forall (S59 : Ty) (wf0 : (wfTy k12 S59)) ,
      (forall {d : (Trace TmVar)} {k13 : Hvl} ,
        (substhvl_TmVar k11 d k12 k13) -> (wfTy k13 (subst_TmVar_Ty d s17 S59))))) := (ind_wfTm_Ty (fun (k12 : Hvl) (s18 : Tm) (wf0 : (wfTm k12 s18)) =>
    (forall {d : (Trace TmVar)} {k13 : Hvl} ,
      (substhvl_TmVar k11 d k12 k13) -> (wfTm k13 (subst_TmVar_Tm d s17 s18)))) (fun (k12 : Hvl) (S59 : Ty) (wf0 : (wfTy k12 S59)) =>
    (forall {d : (Trace TmVar)} {k13 : Hvl} ,
      (substhvl_TmVar k11 d k12 k13) -> (wfTy k13 (subst_TmVar_Ty d s17 S59)))) (fun (k12 : Hvl) {x66 : (Index TmVar)} (wfi : (wfindex k12 x66)) {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (substhvl_TmVar_wfindex_TmVar wf del wfi)) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) IHT (t : Tm) (wf1 : (wfTm (HS TmVar k12) t)) IHt {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfTm_abs k13 (IHT (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k12 : Hvl) (t1 : Tm) (wf0 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k12 t2)) IHt2 {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfTm_app k13 (IHt1 (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)))) (fun (k12 : Hvl) (t1 : Tm) (wf0 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k12 t2)) IHt2 (S1 : Ty) (wf2 : (wfTy k12 S1)) IHS1 (T : Ty) (wf3 : (wfTy (HS TmVar k12) T)) IHT {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfTm_pair k13 (IHt1 (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)) (IHS1 (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)) (IHT (weakenTrace d (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k12 : Hvl) (t : Tm) (wf0 : (wfTm k12 t)) IHt {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfTm_prj1 k13 (IHt (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)))) (fun (k12 : Hvl) (t : Tm) (wf0 : (wfTm k12 t)) IHt {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfTm_prj2 k13 (IHt (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)))) (fun (k12 : Hvl) {X5 : (Index TyVar)} (wfi : (wfindex k12 X5)) {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfTy_tvar k13 _ (substhvl_TmVar_wfindex_TyVar del wfi))) (fun (k12 : Hvl) (T1 : Ty) (wf0 : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS TmVar k12) T2)) IHT2 {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfTy_tpi k13 (IHT1 (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)) (IHT2 (weakenTrace d (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) IHT (t : Tm) (wf1 : (wfTm k12 t)) IHt {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfTy_tapp k13 (IHT (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)))) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) IHT (U : Ty) (wf1 : (wfTy (HS TmVar k12) U)) IHU {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfTy_tsig k13 (IHT (weakenTrace d H0) k13 (weaken_substhvl_TmVar H0 del)) (IHU (weakenTrace d (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TmVar (HS TmVar H0) del))))).
  Lemma substhvl_TmVar_wfTm {k11 : Hvl} {s17 : Tm} (wf : (wfTm k11 s17)) (k12 : Hvl) (s18 : Tm) (wf0 : (wfTm k12 s18)) :
    (forall {d : (Trace TmVar)} {k13 : Hvl} ,
      (substhvl_TmVar k11 d k12 k13) -> (wfTm k13 (subst_TmVar_Tm d s17 s18))).
  Proof.
    apply ((substhvl_TmVar_wfTm_Ty wf k12)).
    auto .
  Qed.
  Lemma substhvl_TmVar_wfTy {k11 : Hvl} {s17 : Tm} (wf : (wfTm k11 s17)) (k12 : Hvl) (S59 : Ty) (wf1 : (wfTy k12 S59)) :
    (forall {d0 : (Trace TmVar)} {k14 : Hvl} ,
      (substhvl_TmVar k11 d0 k12 k14) -> (wfTy k14 (subst_TmVar_Ty d0 s17 S59))).
  Proof.
    apply ((substhvl_TmVar_wfTm_Ty wf k12)).
    auto .
  Qed.
  Definition substhvl_TyVar_wfTm_Ty {k11 : Hvl} {S59 : Ty} (wf : (wfTy k11 S59)) : (forall (k12 : Hvl) ,
    (forall (s17 : Tm) (wf0 : (wfTm k12 s17)) ,
      (forall {d : (Trace TyVar)} {k13 : Hvl} ,
        (substhvl_TyVar k11 d k12 k13) -> (wfTm k13 (subst_TyVar_Tm d S59 s17)))) /\
    (forall (S60 : Ty) (wf0 : (wfTy k12 S60)) ,
      (forall {d : (Trace TyVar)} {k13 : Hvl} ,
        (substhvl_TyVar k11 d k12 k13) -> (wfTy k13 (subst_TyVar_Ty d S59 S60))))) := (ind_wfTm_Ty (fun (k12 : Hvl) (s17 : Tm) (wf0 : (wfTm k12 s17)) =>
    (forall {d : (Trace TyVar)} {k13 : Hvl} ,
      (substhvl_TyVar k11 d k12 k13) -> (wfTm k13 (subst_TyVar_Tm d S59 s17)))) (fun (k12 : Hvl) (S60 : Ty) (wf0 : (wfTy k12 S60)) =>
    (forall {d : (Trace TyVar)} {k13 : Hvl} ,
      (substhvl_TyVar k11 d k12 k13) -> (wfTy k13 (subst_TyVar_Ty d S59 S60)))) (fun (k12 : Hvl) {x66 : (Index TmVar)} (wfi : (wfindex k12 x66)) {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfTm_var k13 _ (substhvl_TyVar_wfindex_TmVar del wfi))) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) IHT (t : Tm) (wf1 : (wfTm (HS TmVar k12) t)) IHt {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfTm_abs k13 (IHT (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k12 : Hvl) (t1 : Tm) (wf0 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k12 t2)) IHt2 {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfTm_app k13 (IHt1 (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)) (IHt2 (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)))) (fun (k12 : Hvl) (t1 : Tm) (wf0 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k12 t2)) IHt2 (S1 : Ty) (wf2 : (wfTy k12 S1)) IHS1 (T : Ty) (wf3 : (wfTy (HS TmVar k12) T)) IHT {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfTm_pair k13 (IHt1 (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)) (IHt2 (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)) (IHS1 (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)) (IHT (weakenTrace d (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k12 : Hvl) (t : Tm) (wf0 : (wfTm k12 t)) IHt {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfTm_prj1 k13 (IHt (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)))) (fun (k12 : Hvl) (t : Tm) (wf0 : (wfTm k12 t)) IHt {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfTm_prj2 k13 (IHt (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)))) (fun (k12 : Hvl) {X5 : (Index TyVar)} (wfi : (wfindex k12 X5)) {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (substhvl_TyVar_wfindex_TyVar wf del wfi)) (fun (k12 : Hvl) (T1 : Ty) (wf0 : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS TmVar k12) T2)) IHT2 {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfTy_tpi k13 (IHT1 (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)) (IHT2 (weakenTrace d (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) IHT (t : Tm) (wf1 : (wfTm k12 t)) IHt {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfTy_tapp k13 (IHT (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)))) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) IHT (U : Ty) (wf1 : (wfTy (HS TmVar k12) U)) IHU {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfTy_tsig k13 (IHT (weakenTrace d H0) k13 (weaken_substhvl_TyVar H0 del)) (IHU (weakenTrace d (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TyVar (HS TmVar H0) del))))).
  Lemma substhvl_TyVar_wfTm {k11 : Hvl} {S59 : Ty} (wf : (wfTy k11 S59)) (k12 : Hvl) (s17 : Tm) (wf0 : (wfTm k12 s17)) :
    (forall {d : (Trace TyVar)} {k13 : Hvl} ,
      (substhvl_TyVar k11 d k12 k13) -> (wfTm k13 (subst_TyVar_Tm d S59 s17))).
  Proof.
    apply ((substhvl_TyVar_wfTm_Ty wf k12)).
    auto .
  Qed.
  Lemma substhvl_TyVar_wfTy {k11 : Hvl} {S59 : Ty} (wf : (wfTy k11 S59)) (k12 : Hvl) (S60 : Ty) (wf1 : (wfTy k12 S60)) :
    (forall {d0 : (Trace TyVar)} {k14 : Hvl} ,
      (substhvl_TyVar k11 d0 k12 k14) -> (wfTy k14 (subst_TyVar_Ty d0 S59 S60))).
  Proof.
    apply ((substhvl_TyVar_wfTm_Ty wf k12)).
    auto .
  Qed.
  Definition substhvl_TmVar_wfKind {k11 : Hvl} {s17 : Tm} (wf : (wfTm k11 s17)) : (forall (k12 : Hvl) ,
    (forall (K44 : Kind) (wf0 : (wfKind k12 K44)) ,
      (forall {d : (Trace TmVar)} {k13 : Hvl} ,
        (substhvl_TmVar k11 d k12 k13) -> (wfKind k13 (subst_TmVar_Kind d s17 K44))))) := (ind_wfKind (fun (k12 : Hvl) (K44 : Kind) (wf0 : (wfKind k12 K44)) =>
    (forall {d : (Trace TmVar)} {k13 : Hvl} ,
      (substhvl_TmVar k11 d k12 k13) -> (wfKind k13 (subst_TmVar_Kind d s17 K44)))) (fun (k12 : Hvl) {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfKind_star k13)) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) (K : Kind) (wf1 : (wfKind (HS TmVar k12) K)) IHK {d : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d k12 k13)) =>
    (wfKind_kpi k13 (substhvl_TmVar_wfTy wf k12 T wf0 (weaken_substhvl_TmVar H0 del)) (IHK (weakenTrace d (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TmVar (HS TmVar H0) del))))).
  Definition substhvl_TyVar_wfKind {k11 : Hvl} {S59 : Ty} (wf : (wfTy k11 S59)) : (forall (k12 : Hvl) ,
    (forall (K44 : Kind) (wf0 : (wfKind k12 K44)) ,
      (forall {d : (Trace TyVar)} {k13 : Hvl} ,
        (substhvl_TyVar k11 d k12 k13) -> (wfKind k13 (subst_TyVar_Kind d S59 K44))))) := (ind_wfKind (fun (k12 : Hvl) (K44 : Kind) (wf0 : (wfKind k12 K44)) =>
    (forall {d : (Trace TyVar)} {k13 : Hvl} ,
      (substhvl_TyVar k11 d k12 k13) -> (wfKind k13 (subst_TyVar_Kind d S59 K44)))) (fun (k12 : Hvl) {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfKind_star k13)) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) (K : Kind) (wf1 : (wfKind (HS TmVar k12) K)) IHK {d : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d k12 k13)) =>
    (wfKind_kpi k13 (substhvl_TyVar_wfTy wf k12 T wf0 (weaken_substhvl_TyVar H0 del)) (IHK (weakenTrace d (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TyVar (HS TmVar H0) del))))).
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
  Inductive Env : Type :=
    | empty 
    | evar (G : Env) (T : Ty)
    | etvar (G : Env) (K : Kind).
  Fixpoint appendEnv (G : Env) (G0 : Env) :
  Env :=
    match G0 with
      | (empty) => G
      | (evar G1 T) => (evar (appendEnv G G1) T)
      | (etvar G1 K) => (etvar (appendEnv G G1) K)
    end.
  Fixpoint domainEnv (G : Env) :
  Hvl :=
    match G with
      | (empty) => H0
      | (evar G0 T) => (HS TmVar (domainEnv G0))
      | (etvar G0 K) => (HS TyVar (domainEnv G0))
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
  Fixpoint shift_TmVar_Env (c : (Cutoff TmVar)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shift_TmVar_Env c G0) (shift_TmVar_Ty (weakenCutoffTmVar c (domainEnv G0)) T))
      | (etvar G0 K) => (etvar (shift_TmVar_Env c G0) (shift_TmVar_Kind (weakenCutoffTmVar c (domainEnv G0)) K))
    end.
  Fixpoint shift_TyVar_Env (c : (Cutoff TyVar)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shift_TyVar_Env c G0) (shift_TyVar_Ty (weakenCutoffTyVar c (domainEnv G0)) T))
      | (etvar G0 K) => (etvar (shift_TyVar_Env c G0) (shift_TyVar_Kind (weakenCutoffTyVar c (domainEnv G0)) K))
    end.
  Fixpoint weakenEnv (G : Env) (k11 : Hvl) {struct k11} :
  Env :=
    match k11 with
      | (H0) => G
      | (HS TmVar k11) => (shift_TmVar_Env C0 (weakenEnv G k11))
      | (HS TyVar k11) => (shift_TyVar_Env C0 (weakenEnv G k11))
    end.
  Fixpoint subst_TmVar_Env (d : (Trace TmVar)) (s17 : Tm) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (subst_TmVar_Env d s17 G0) (subst_TmVar_Ty (weakenTrace d (domainEnv G0)) s17 T))
      | (etvar G0 K) => (etvar (subst_TmVar_Env d s17 G0) (subst_TmVar_Kind (weakenTrace d (domainEnv G0)) s17 K))
    end.
  Fixpoint subst_TyVar_Env (d : (Trace TyVar)) (S59 : Ty) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (subst_TyVar_Env d S59 G0) (subst_TyVar_Ty (weakenTrace d (domainEnv G0)) S59 T))
      | (etvar G0 K) => (etvar (subst_TyVar_Env d S59 G0) (subst_TyVar_Kind (weakenTrace d (domainEnv G0)) S59 K))
    end.
  Lemma domainEnv_shift_TmVar_Env  :
    (forall (c : (Cutoff TmVar)) (G : Env) ,
      ((domainEnv (shift_TmVar_Env c G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_shift_TyVar_Env  :
    (forall (c : (Cutoff TyVar)) (G : Env) ,
      ((domainEnv (shift_TyVar_Env c G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_subst_TmVar_Env  :
    (forall (d : (Trace TmVar)) (s17 : Tm) (G : Env) ,
      ((domainEnv (subst_TmVar_Env d s17 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_subst_TyVar_Env  :
    (forall (d : (Trace TyVar)) (S59 : Ty) (G : Env) ,
      ((domainEnv (subst_TyVar_Env d S59 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shift_TmVar_Env_appendEnv  :
      (forall (c : (Cutoff TmVar)) (G : Env) (G0 : Env) ,
        ((shift_TmVar_Env c (appendEnv G G0)) = (appendEnv (shift_TmVar_Env c G) (shift_TmVar_Env (weakenCutoffTmVar c (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma shift_TyVar_Env_appendEnv  :
      (forall (c : (Cutoff TyVar)) (G : Env) (G0 : Env) ,
        ((shift_TyVar_Env c (appendEnv G G0)) = (appendEnv (shift_TyVar_Env c G) (shift_TyVar_Env (weakenCutoffTyVar c (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma subst_TmVar_Env_appendEnv  :
      (forall (d : (Trace TmVar)) (s17 : Tm) (G : Env) (G0 : Env) ,
        ((subst_TmVar_Env d s17 (appendEnv G G0)) = (appendEnv (subst_TmVar_Env d s17 G) (subst_TmVar_Env (weakenTrace d (domainEnv G)) s17 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma subst_TyVar_Env_appendEnv  :
      (forall (d : (Trace TyVar)) (S59 : Ty) (G : Env) (G0 : Env) ,
        ((subst_TyVar_Env d S59 (appendEnv G G0)) = (appendEnv (subst_TyVar_Env d S59 G) (subst_TyVar_Env (weakenTrace d (domainEnv G)) S59 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTm_append  :
    (forall (s17 : Tm) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenTm (weakenTm s17 k11) k12) = (weakenTm s17 (appendHvl k11 k12)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTy_append  :
    (forall (S59 : Ty) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenTy (weakenTy S59 k11) k12) = (weakenTy S59 (appendHvl k11 k12)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenKind_append  :
    (forall (K44 : Kind) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenKind (weakenKind K44 k11) k12) = (weakenKind K44 (appendHvl k11 k12)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index TmVar) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          (T86 : Ty) :
          (wfTy (domainEnv G) T86) -> (lookup_evar (evar G T86) I0 (shift_TmVar_Ty C0 T86))
      | lookup_evar_there_evar
          {G : Env} {x66 : (Index TmVar)}
          (T87 : Ty) (T88 : Ty) :
          (lookup_evar G x66 T87) -> (lookup_evar (evar G T88) (IS x66) (shift_TmVar_Ty C0 T87))
      | lookup_evar_there_etvar
          {G : Env} {x66 : (Index TmVar)}
          (T87 : Ty) (K44 : Kind) :
          (lookup_evar G x66 T87) -> (lookup_evar (etvar G K44) x66 (shift_TyVar_Ty C0 T87)).
    Inductive lookup_etvar : Env -> (Index TyVar) -> Kind -> Prop :=
      | lookup_etvar_here {G : Env}
          (K44 : Kind) :
          (wfKind (domainEnv G) K44) -> (lookup_etvar (etvar G K44) I0 (shift_TyVar_Kind C0 K44))
      | lookup_etvar_there_evar
          {G : Env} {X5 : (Index TyVar)}
          (K45 : Kind) (T87 : Ty) :
          (lookup_etvar G X5 K45) -> (lookup_etvar (evar G T87) X5 (shift_TmVar_Kind C0 K45))
      | lookup_etvar_there_etvar
          {G : Env} {X5 : (Index TyVar)}
          (K45 : Kind) (K46 : Kind) :
          (lookup_etvar G X5 K45) -> (lookup_etvar (etvar G K46) (IS X5) (shift_TyVar_Kind C0 K45)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (T87 : Ty) (T88 : Ty) ,
        (lookup_evar (evar G T87) I0 T88) -> ((shift_TmVar_Ty C0 T87) = T88)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Env) (K45 : Kind) (K46 : Kind) ,
        (lookup_etvar (etvar G K45) I0 K46) -> ((shift_TyVar_Kind C0 K45) = K46)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x66 : (Index TmVar)} ,
        (forall (T87 : Ty) ,
          (lookup_evar G x66 T87) -> (forall (T88 : Ty) ,
            (lookup_evar G x66 T88) -> (T87 = T88)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G : Env} {X5 : (Index TyVar)} ,
        (forall (K45 : Kind) ,
          (lookup_etvar G X5 K45) -> (forall (K46 : Kind) ,
            (lookup_etvar G X5 K46) -> (K45 = K46)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x66 : (Index TmVar)} (T87 : Ty) ,
        (lookup_evar G x66 T87) -> (wfTy (domainEnv G) T87)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G : Env} {X5 : (Index TyVar)} (K45 : Kind) ,
        (lookup_etvar G X5 K45) -> (wfKind (domainEnv G) K45)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x66 : (Index TmVar)} (T87 : Ty) ,
        (lookup_evar G x66 T87) -> (lookup_evar (appendEnv G G0) (weakenIndexTmVar x66 (domainEnv G0)) (weakenTy T87 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X5 : (Index TyVar)} (K45 : Kind) ,
        (lookup_etvar G X5 K45) -> (lookup_etvar (appendEnv G G0) (weakenIndexTyVar X5 (domainEnv G0)) (weakenKind K45 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x66 : (Index TmVar)} (T89 : Ty) ,
        (lookup_evar G x66 T89) -> (wfindex (domainEnv G) x66)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X5 : (Index TyVar)} (K47 : Kind) ,
        (lookup_etvar G X5 K47) -> (wfindex (domainEnv G) X5)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff TmVar) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T87 : Ty} :
        (shift_evar C0 G (evar G T87))
    | shiftevar_there_evar
        {c : (Cutoff TmVar)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c G G0) -> (shift_evar (CS c) (evar G T) (evar G0 (shift_TmVar_Ty c T)))
    | shiftevar_there_etvar
        {c : (Cutoff TmVar)} {G : Env}
        {G0 : Env} {K : Kind} :
        (shift_evar c G G0) -> (shift_evar c (etvar G K) (etvar G0 (shift_TmVar_Kind c K))).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c : (Cutoff TmVar)} {G0 : Env} {G1 : Env} ,
      (shift_evar c G0 G1) -> (shift_evar (weakenCutoffTmVar c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 (shift_TmVar_Env c G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff TyVar) -> Env -> Env -> Prop :=
    | shift_etvar_here {G : Env}
        {K45 : Kind} :
        (shift_etvar C0 G (etvar G K45))
    | shiftetvar_there_evar
        {c : (Cutoff TyVar)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c G G0) -> (shift_etvar c (evar G T) (evar G0 (shift_TyVar_Ty c T)))
    | shiftetvar_there_etvar
        {c : (Cutoff TyVar)} {G : Env}
        {G0 : Env} {K : Kind} :
        (shift_etvar c G G0) -> (shift_etvar (CS c) (etvar G K) (etvar G0 (shift_TyVar_Kind c K))).
  Lemma weaken_shift_etvar  :
    (forall (G : Env) {c : (Cutoff TyVar)} {G0 : Env} {G1 : Env} ,
      (shift_etvar c G0 G1) -> (shift_etvar (weakenCutoffTyVar c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 (shift_TyVar_Env c G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_TmVar  :
    (forall {c : (Cutoff TmVar)} {G : Env} {G0 : Env} ,
      (shift_evar c G G0) -> (shifthvl_TmVar c (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_etvar_shifthvl_TyVar  :
    (forall {c : (Cutoff TyVar)} {G : Env} {G0 : Env} ,
      (shift_etvar c G G0) -> (shifthvl_TyVar c (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Env) (T87 : Ty) (s17 : Tm) : (Trace TmVar) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T87 s17 X0 (evar G T87) G)
    | subst_evar_there_evar
        {d : (Trace TmVar)} {G0 : Env}
        {G1 : Env} (T88 : Ty) :
        (subst_evar G T87 s17 d G0 G1) -> (subst_evar G T87 s17 (XS TmVar d) (evar G0 T88) (evar G1 (subst_TmVar_Ty d s17 T88)))
    | subst_evar_there_etvar
        {d : (Trace TmVar)} {G0 : Env}
        {G1 : Env} (K45 : Kind) :
        (subst_evar G T87 s17 d G0 G1) -> (subst_evar G T87 s17 (XS TyVar d) (etvar G0 K45) (etvar G1 (subst_TmVar_Kind d s17 K45))).
  Lemma weaken_subst_evar {G : Env} (T87 : Ty) {s17 : Tm} :
    (forall (G0 : Env) {d : (Trace TmVar)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T87 s17 d G1 G2) -> (subst_evar G T87 s17 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (subst_TmVar_Env d s17 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (K45 : Kind) (S59 : Ty) : (Trace TyVar) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G K45 S59 X0 (etvar G K45) G)
    | subst_etvar_there_evar
        {d : (Trace TyVar)} {G0 : Env}
        {G1 : Env} (T87 : Ty) :
        (subst_etvar G K45 S59 d G0 G1) -> (subst_etvar G K45 S59 (XS TmVar d) (evar G0 T87) (evar G1 (subst_TyVar_Ty d S59 T87)))
    | subst_etvar_there_etvar
        {d : (Trace TyVar)} {G0 : Env}
        {G1 : Env} (K46 : Kind) :
        (subst_etvar G K45 S59 d G0 G1) -> (subst_etvar G K45 S59 (XS TyVar d) (etvar G0 K46) (etvar G1 (subst_TyVar_Kind d S59 K46))).
  Lemma weaken_subst_etvar {G : Env} (K45 : Kind) {S59 : Ty} :
    (forall (G0 : Env) {d : (Trace TyVar)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G K45 S59 d G1 G2) -> (subst_etvar G K45 S59 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (subst_TyVar_Env d S59 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_TmVar {G : Env} {s17 : Tm} (T87 : Ty) :
    (forall {d : (Trace TmVar)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T87 s17 d G0 G1) -> (substhvl_TmVar (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_TyVar {G : Env} {S59 : Ty} (K45 : Kind) :
    (forall {d : (Trace TyVar)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G K45 S59 d G0 G1) -> (substhvl_TyVar (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
End ContextStuff.
 Hint Rewrite domainEnv_shift_TmVar_Env domainEnv_shift_TyVar_Env : interaction.
 Hint Rewrite domainEnv_shift_TmVar_Env domainEnv_shift_TyVar_Env : env_domain_shift.
 Hint Rewrite domainEnv_subst_TmVar_Env domainEnv_subst_TyVar_Env : interaction.
 Hint Rewrite domainEnv_subst_TmVar_Env domainEnv_subst_TyVar_Env : env_domain_subst.
 Hint Rewrite shift_TmVar_Env_appendEnv shift_TyVar_Env_appendEnv : interaction.
 Hint Rewrite shift_TmVar_Env_appendEnv shift_TyVar_Env_appendEnv : env_shift_append.
 Hint Rewrite subst_TmVar_Env_appendEnv subst_TyVar_Env_appendEnv : interaction.
 Hint Rewrite subst_TmVar_Env_appendEnv subst_TyVar_Env_appendEnv : env_shift_append.
 Hint Constructors lookup_evar lookup_etvar : infra.
 Hint Constructors lookup_evar lookup_etvar : lookup.
 Hint Constructors lookup_evar lookup_etvar : shift.
 Hint Constructors lookup_evar lookup_etvar : subst.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : infra.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : lookup.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : shift.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : weaken.
Lemma weaken_lookup_evar_here  :
  (forall {G : Env} (G0 : Env) {T87 : Ty} (wf : (wfTy (domainEnv G) T87)) ,
    (lookup_evar (appendEnv (evar G T87) G0) (weakenIndexTmVar I0 (domainEnv G0)) (weakenTy (shift_TmVar_Ty C0 T87) (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) {K45 : Kind} (wf : (wfKind (domainEnv G) K45)) ,
    (lookup_etvar (appendEnv (etvar G K45) G0) (weakenIndexTyVar I0 (domainEnv G0)) (weakenKind (shift_TyVar_Kind C0 K45) (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfKind wfTm wfTy : infra.
 Hint Constructors wfKind wfTm wfTy : wf.
 Hint Extern 10 ((wfKind _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H41 : (wfTm _ (var _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (abs _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (app _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (pair _ _ _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (prj1 _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (prj2 _)) |- _ => inversion H41; subst; clear H41
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H41 : (wfTy _ (tvar _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTy _ (tpi _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTy _ (tapp _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTy _ (tsig _ _)) |- _ => inversion H41; subst; clear H41
end : infra wf.
 Hint Extern 2 ((wfKind _ _)) => match goal with
  | H41 : (wfKind _ (star)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfKind _ (kpi _ _)) |- _ => inversion H41; subst; clear H41
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
  (forall {c : (Cutoff TmVar)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {x66 : (Index TmVar)} {T87 : Ty} ,
    (lookup_evar G x66 T87) -> (lookup_evar G0 (shift_TmVar_Index c x66) (shift_TmVar_Ty c T87))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c : (Cutoff TmVar)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {X5 : (Index TyVar)} {K45 : Kind} ,
    (lookup_etvar G X5 K45) -> (lookup_etvar G0 X5 (shift_TmVar_Kind c K45))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c : (Cutoff TyVar)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {x66 : (Index TmVar)} {T87 : Ty} ,
    (lookup_evar G x66 T87) -> (lookup_evar G0 x66 (shift_TyVar_Ty c T87))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c : (Cutoff TyVar)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {X5 : (Index TyVar)} {K45 : Kind} ,
    (lookup_etvar G X5 K45) -> (lookup_etvar G0 (shift_TyVar_Index c X5) (shift_TyVar_Kind c K45))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} (T88 : Ty) {s17 : Tm} (wf : (wfTm (domainEnv G) s17)) :
  (forall {d : (Trace TmVar)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T88 s17 d G0 G1)) {X5 : (Index TyVar)} (K46 : Kind) ,
    (lookup_etvar G0 X5 K46) -> (lookup_etvar G1 X5 (subst_TmVar_Kind d s17 K46))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} (K46 : Kind) {S59 : Ty} (wf : (wfTy (domainEnv G) S59)) :
  (forall {d : (Trace TyVar)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G K46 S59 d G0 G1)) {x66 : (Index TmVar)} (T88 : Ty) ,
    (lookup_evar G0 x66 T88) -> (lookup_evar G1 x66 (subst_TyVar_Ty d S59 T88))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Tm (s11 : Tm) {struct s11} :
nat :=
  match s11 with
    | (var x66) => 1
    | (abs T86 t76) => (plus 1 (plus (size_Ty T86) (size_Tm t76)))
    | (app t77 t78) => (plus 1 (plus (size_Tm t77) (size_Tm t78)))
    | (pair t79 t80 S55 T87) => (plus 1 (plus (size_Tm t79) (plus (size_Tm t80) (plus (size_Ty S55) (size_Ty T87)))))
    | (prj1 t81) => (plus 1 (size_Tm t81))
    | (prj2 t82) => (plus 1 (size_Tm t82))
  end
with size_Ty (S55 : Ty) {struct S55} :
nat :=
  match S55 with
    | (tvar X5) => 1
    | (tpi T86 T87) => (plus 1 (plus (size_Ty T86) (size_Ty T87)))
    | (tapp T88 t76) => (plus 1 (plus (size_Ty T88) (size_Tm t76)))
    | (tsig T89 U2) => (plus 1 (plus (size_Ty T89) (size_Ty U2)))
  end.
Fixpoint size_Kind (K42 : Kind) {struct K42} :
nat :=
  match K42 with
    | (star) => 1
    | (kpi T86 K43) => (plus 1 (plus (size_Ty T86) (size_Kind K43)))
  end.
Fixpoint shift_TmVar__size_Tm (s11 : Tm) (c : (Cutoff TmVar)) {struct s11} :
((size_Tm (shift_TmVar_Tm c s11)) = (size_Tm s11)) :=
  match s11 return ((size_Tm (shift_TmVar_Tm c s11)) = (size_Tm s11)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Ty T c) (shift_TmVar__size_Tm t (CS c))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t1 c) (shift_TmVar__size_Tm t2 c)))
    | (pair t1 t2 S1 T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t1 c) (f_equal2 plus (shift_TmVar__size_Tm t2 c) (f_equal2 plus (shift_TmVar__size_Ty S1 c) (shift_TmVar__size_Ty T (CS c))))))
    | (prj1 t) => (f_equal2 plus eq_refl (shift_TmVar__size_Tm t c))
    | (prj2 t) => (f_equal2 plus eq_refl (shift_TmVar__size_Tm t c))
  end
with shift_TmVar__size_Ty (S55 : Ty) (c : (Cutoff TmVar)) {struct S55} :
((size_Ty (shift_TmVar_Ty c S55)) = (size_Ty S55)) :=
  match S55 return ((size_Ty (shift_TmVar_Ty c S55)) = (size_Ty S55)) with
    | (tvar _) => eq_refl
    | (tpi T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Ty T1 c) (shift_TmVar__size_Ty T2 (CS c))))
    | (tapp T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Ty T c) (shift_TmVar__size_Tm t c)))
    | (tsig T U) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Ty T c) (shift_TmVar__size_Ty U (CS c))))
  end.
Fixpoint shift_TyVar__size_Tm (s11 : Tm) (c : (Cutoff TyVar)) {struct s11} :
((size_Tm (shift_TyVar_Tm c s11)) = (size_Tm s11)) :=
  match s11 return ((size_Tm (shift_TyVar_Tm c s11)) = (size_Tm s11)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T c) (shift_TyVar__size_Tm t c)))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Tm t1 c) (shift_TyVar__size_Tm t2 c)))
    | (pair t1 t2 S1 T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Tm t1 c) (f_equal2 plus (shift_TyVar__size_Tm t2 c) (f_equal2 plus (shift_TyVar__size_Ty S1 c) (shift_TyVar__size_Ty T c)))))
    | (prj1 t) => (f_equal2 plus eq_refl (shift_TyVar__size_Tm t c))
    | (prj2 t) => (f_equal2 plus eq_refl (shift_TyVar__size_Tm t c))
  end
with shift_TyVar__size_Ty (S55 : Ty) (c : (Cutoff TyVar)) {struct S55} :
((size_Ty (shift_TyVar_Ty c S55)) = (size_Ty S55)) :=
  match S55 return ((size_Ty (shift_TyVar_Ty c S55)) = (size_Ty S55)) with
    | (tvar _) => eq_refl
    | (tpi T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T1 c) (shift_TyVar__size_Ty T2 c)))
    | (tapp T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T c) (shift_TyVar__size_Tm t c)))
    | (tsig T U) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T c) (shift_TyVar__size_Ty U c)))
  end.
Fixpoint shift_TmVar__size_Kind (K42 : Kind) (c : (Cutoff TmVar)) {struct K42} :
((size_Kind (shift_TmVar_Kind c K42)) = (size_Kind K42)) :=
  match K42 return ((size_Kind (shift_TmVar_Kind c K42)) = (size_Kind K42)) with
    | (star) => eq_refl
    | (kpi T K) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Ty T c) (shift_TmVar__size_Kind K (CS c))))
  end.
Fixpoint shift_TyVar__size_Kind (K42 : Kind) (c : (Cutoff TyVar)) {struct K42} :
((size_Kind (shift_TyVar_Kind c K42)) = (size_Kind K42)) :=
  match K42 return ((size_Kind (shift_TyVar_Kind c K42)) = (size_Kind K42)) with
    | (star) => eq_refl
    | (kpi T K) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T c) (shift_TyVar__size_Kind K c)))
  end.
 Hint Rewrite shift_TmVar__size_Kind shift_TyVar__size_Kind shift_TmVar__size_Tm shift_TyVar__size_Tm shift_TmVar__size_Ty shift_TyVar__size_Ty : interaction.
 Hint Rewrite shift_TmVar__size_Kind shift_TyVar__size_Kind shift_TmVar__size_Tm shift_TyVar__size_Tm shift_TmVar__size_Ty shift_TyVar__size_Ty : shift_size.
Lemma weaken_size_Kind  :
  (forall (k : Hvl) (K42 : Kind) ,
    ((size_Kind (weakenKind K42 k)) = (size_Kind K42))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Tm  :
  (forall (k : Hvl) (s11 : Tm) ,
    ((size_Tm (weakenTm s11 k)) = (size_Tm s11))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k : Hvl) (S55 : Ty) ,
    ((size_Ty (weakenTy S55 k)) = (size_Ty S55))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Kind weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Kind weaken_size_Tm weaken_size_Ty : weaken_size.
Inductive KindEq (G : Env) : Kind -> Kind -> Prop :=
  | QK_Pi (K1 : Kind)
      (K2 : Kind) (T1 : Ty) (T2 : Ty)
      (jm20 : (TyEq G T1 T2 (star)))
      (jm21 : (KindEq (evar G T1) K1 K2))
      :
      (KindEq G (kpi T1 K1) (kpi T2 K2))
  | QK_Refl (K : Kind)
      (jm22 : (WfKind G K)) :
      (KindEq G K K)
  | QK_Sym (K1 : Kind) (K2 : Kind)
      (jm23 : (KindEq G K1 K2)) :
      (KindEq G K2 K1)
  | QK_Trans (K1 : Kind)
      (K2 : Kind) (K3 : Kind)
      (jm24 : (KindEq G K1 K2))
      (jm25 : (KindEq G K2 K3)) :
      (KindEq G K1 K3)
with TyEq (G : Env) : Ty -> Ty -> Kind -> Prop :=
  | QT_Pi (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm26 : (TyEq G S1 T1 (star)))
      (jm27 : (TyEq (evar G T1) S2 T2 (star)))
      :
      (TyEq G (tpi S1 S2) (tpi T1 T2) (star))
  | QT_App (K : Kind) (S1 : Ty)
      (S2 : Ty) (T : Ty) (t1 : Tm)
      (t2 : Tm)
      (jm28 : (TyEq G S1 S2 (kpi T K)))
      (jm29 : (TermEq G t1 t2 T)) :
      (TyEq G (tapp S1 t1) (tapp S2 t2) (subst_TmVar_Kind X0 t1 K))
  | QT_Refl (K : Kind) (T : Ty)
      (jm30 : (Kinding G T K)) :
      (TyEq G T T K)
  | QT_Symm (K : Kind) (S1 : Ty)
      (T : Ty)
      (jm31 : (TyEq G T S1 K)) :
      (TyEq G S1 T K)
  | QT_Trans (K : Kind) (S1 : Ty)
      (T : Ty) (U : Ty)
      (jm32 : (TyEq G S1 U K))
      (jm33 : (TyEq G U T K)) :
      (TyEq G S1 T K)
with TermEq (G : Env) : Tm -> Tm -> Ty -> Prop :=
  | Q_Abs (S1 : Ty) (S2 : Ty)
      (T : Ty) (t1 : Tm) (t2 : Tm)
      (jm34 : (TyEq G S1 S2 (star)))
      (jm35 : (TermEq (evar G S1) t1 t2 T))
      :
      (TermEq G (abs S1 t1) (abs S2 t2) (tpi S1 T))
  | Q_App (S1 : Ty) (T : Ty)
      (s1 : Tm) (s2 : Tm) (t1 : Tm)
      (t2 : Tm)
      (jm36 : (TermEq G t1 s1 (tpi S1 T)))
      (jm37 : (TermEq G t2 s2 S1)) :
      (TermEq G (app t1 t2) (app s1 s2) (subst_TmVar_Ty X0 t2 T))
  | Q_Beta (S1 : Ty) (T : Ty)
      (s : Tm) (t : Tm)
      (jm38 : (Typing (evar G S1) t T))
      (jm39 : (Typing G s S1)) :
      (TermEq G (app (abs S1 t) s) (subst_TmVar_Tm X0 s t) (subst_TmVar_Ty X0 s T))
  | Q_Eta (S1 : Ty) (T : Ty)
      (t : Tm)
      (jm40 : (Typing G t (tpi S1 T)))
      :
      (TermEq G (abs S1 (app (weakenTm t (HS TmVar H0)) (var I0))) t (tpi S1 T))
  | Q_Proj1 (S1 : Ty) (T : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm41 : (Kinding G (tsig S1 T) (star)))
      (jm42 : (Typing G t1 S1))
      (jm43 : (Typing G t2 (subst_TmVar_Ty X0 t1 T)))
      :
      (TermEq G (prj1 (pair t1 t2 S1 T)) t1 S1)
  | Q_Proj2 (S1 : Ty) (T : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm44 : (Kinding G (tsig S1 T) (star)))
      (jm45 : (Typing G t1 S1))
      (jm46 : (Typing G t2 (subst_TmVar_Ty X0 t1 T)))
      :
      (TermEq G (prj2 (pair t1 t2 S1 T)) t2 (subst_TmVar_Ty X0 t1 T))
  | Q_SjPair (S1 : Ty) (T : Ty)
      (t : Tm)
      (jm47 : (Typing G t (tsig S1 T)))
      :
      (TermEq G (pair (prj1 t) (prj2 t) S1 T) t (tsig S1 T))
  | Q_Refl (T : Ty) (t : Tm)
      (jm48 : (Typing G t T)) :
      (TermEq G t t T)
  | Q_Symm (T : Ty) (s : Tm)
      (t : Tm)
      (jm49 : (TermEq G t s T)) :
      (TermEq G s t T)
  | Q_Trans (T : Ty) (s : Tm)
      (t : Tm) (u : Tm)
      (jm50 : (TermEq G s u T))
      (jm51 : (TermEq G u t T)) :
      (TermEq G s t T)
with Typing (G : Env) : Tm -> Ty -> Prop :=
  | T_Var (T : Ty)
      (x : (Index TmVar))
      (lk : (lookup_evar G x T))
      (H25 : (wfTy (domainEnv G) T))
      (H26 : (wfindex (domainEnv G) x))
      : (Typing G (var x) T)
  | T_Abs (S1 : Ty) (T : Ty)
      (t : Tm)
      (jm9 : (Kinding G S1 (star)))
      (jm10 : (Typing (evar G S1) t T))
      :
      (Typing G (abs S1 t) (tpi S1 T))
  | T_App (S1 : Ty) (T : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm11 : (Typing G t1 (tpi S1 T)))
      (jm12 : (Typing G t2 S1)) :
      (Typing G (app t1 t2) (subst_TmVar_Ty X0 t2 T))
  | T_Pair (S1 : Ty) (T : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm13 : (Kinding G (tsig S1 T) (star)))
      (jm14 : (Typing G t1 S1))
      (jm15 : (Typing G t2 (subst_TmVar_Ty X0 t1 T)))
      :
      (Typing G (pair t1 t2 S1 T) (tsig S1 T))
  | T_Proj1 (S1 : Ty) (T : Ty)
      (t : Tm)
      (jm16 : (Typing G t (tsig S1 T)))
      : (Typing G (prj1 t) S1)
  | T_Proj2 (S1 : Ty) (T : Ty)
      (t : Tm)
      (jm17 : (Typing G t (tsig S1 T)))
      :
      (Typing G (prj2 t) (subst_TmVar_Ty X0 (prj1 t) T))
  | T_Conv (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm18 : (Typing G t T1))
      (jm19 : (TyEq G T1 T2 (star))) :
      (Typing G t T2)
with Kinding (G : Env) : Ty -> Kind -> Prop :=
  | K_TVar (K : Kind)
      (X : (Index TyVar))
      (lk0 : (lookup_etvar G X K))
      (H25 : (wfKind (domainEnv G) K))
      (H26 : (wfindex (domainEnv G) X))
      : (Kinding G (tvar X) K)
  | K_Pi (T1 : Ty) (T2 : Ty)
      (jm1 : (Kinding G T1 (star)))
      (jm2 : (Kinding (evar G T1) T2 (star)))
      : (Kinding G (tpi T1 T2) (star))
  | K_App (K : Kind) (S1 : Ty)
      (T : Ty) (t : Tm)
      (jm3 : (Kinding G S1 (kpi T K)))
      (jm4 : (Typing G t T)) :
      (Kinding G (tapp S1 t) (subst_TmVar_Kind X0 t K))
  | K_Sigma (S1 : Ty) (T : Ty)
      (jm5 : (Kinding G S1 (star)))
      (jm6 : (Kinding (evar G S1) T (star)))
      : (Kinding G (tsig S1 T) (star))
  | K_Conv (K1 : Kind) (K2 : Kind)
      (T : Ty)
      (jm7 : (Kinding G T K1))
      (jm8 : (KindEq G K1 K2)) :
      (Kinding G T K2)
with WfKind (G : Env) : Kind -> Prop :=
  | WfStar : (WfKind G (star))
  | WfPi (K : Kind) (T : Ty)
      (jm : (Kinding G T (star)))
      (jm0 : (WfKind G K)) :
      (WfKind G (kpi T (weakenKind K (HS TmVar H0)))).
Lemma KindEq_cast  :
  (forall (G : Env) (K47 : Kind) (K48 : Kind) (G0 : Env) (K49 : Kind) (K50 : Kind) ,
    (G = G0) -> (K47 = K49) -> (K48 = K50) -> (KindEq G K47 K48) -> (KindEq G0 K49 K50)).
Proof.
  congruence .
Qed.
Lemma TyEq_cast  :
  (forall (G : Env) (T89 : Ty) (T90 : Ty) (K47 : Kind) (G0 : Env) (T91 : Ty) (T92 : Ty) (K48 : Kind) ,
    (G = G0) -> (T89 = T91) -> (T90 = T92) -> (K47 = K48) -> (TyEq G T89 T90 K47) -> (TyEq G0 T91 T92 K48)).
Proof.
  congruence .
Qed.
Lemma TermEq_cast  :
  (forall (G : Env) (t76 : Tm) (t77 : Tm) (T89 : Ty) (G0 : Env) (t78 : Tm) (t79 : Tm) (T90 : Ty) ,
    (G = G0) -> (t76 = t78) -> (t77 = t79) -> (T89 = T90) -> (TermEq G t76 t77 T89) -> (TermEq G0 t78 t79 T90)).
Proof.
  congruence .
Qed.
Lemma Typing_cast  :
  (forall (G : Env) (t76 : Tm) (T89 : Ty) (G0 : Env) (t77 : Tm) (T90 : Ty) ,
    (G = G0) -> (t76 = t77) -> (T89 = T90) -> (Typing G t76 T89) -> (Typing G0 t77 T90)).
Proof.
  congruence .
Qed.
Lemma Kinding_cast  :
  (forall (G : Env) (T89 : Ty) (K47 : Kind) (G0 : Env) (T90 : Ty) (K48 : Kind) ,
    (G = G0) -> (T89 = T90) -> (K47 = K48) -> (Kinding G T89 K47) -> (Kinding G0 T90 K48)).
Proof.
  congruence .
Qed.
Lemma WfKind_cast  :
  (forall (G : Env) (K47 : Kind) (G0 : Env) (K48 : Kind) ,
    (G = G0) -> (K47 = K48) -> (WfKind G K47) -> (WfKind G0 K48)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_KindEq (G11 : Env) (K62 : Kind) (K63 : Kind) (jm64 : (KindEq G11 K62 K63)) :
(forall (c : (Cutoff TmVar)) (G12 : Env) (H78 : (shift_evar c G11 G12)) ,
  (KindEq G12 (shift_TmVar_Kind c K62) (shift_TmVar_Kind c K63))) :=
  match jm64 in (KindEq _ K62 K63) return (forall (c : (Cutoff TmVar)) (G12 : Env) (H78 : (shift_evar c G11 G12)) ,
    (KindEq G12 (shift_TmVar_Kind c K62) (shift_TmVar_Kind c K63))) with
    | (QK_Pi K59 K60 T100 T101 jm58 jm59) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H78 : (shift_evar c G11 G12)) =>
      (QK_Pi G12 (shift_TmVar_Kind (CS c) K59) (shift_TmVar_Kind (CS c) K60) (shift_TmVar_Ty c T100) (shift_TmVar_Ty c T101) (shift_evar_TyEq G11 T100 T101 (star) jm58 c G12 (weaken_shift_evar empty H78)) (shift_evar_KindEq (evar G11 T100) K59 K60 jm59 (CS c) (evar G12 (shift_TmVar_Ty c T100)) (weaken_shift_evar (evar empty T100) H78))))
    | (QK_Refl K58 jm60) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H78 : (shift_evar c G11 G12)) =>
      (QK_Refl G12 (shift_TmVar_Kind c K58) (shift_evar_WfKind G11 K58 jm60 c G12 (weaken_shift_evar empty H78))))
    | (QK_Sym K59 K60 jm61) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H78 : (shift_evar c G11 G12)) =>
      (QK_Sym G12 (shift_TmVar_Kind c K59) (shift_TmVar_Kind c K60) (shift_evar_KindEq G11 K59 K60 jm61 c G12 (weaken_shift_evar empty H78))))
    | (QK_Trans K59 K60 K61 jm62 jm63) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H78 : (shift_evar c G11 G12)) =>
      (QK_Trans G12 (shift_TmVar_Kind c K59) (shift_TmVar_Kind c K60) (shift_TmVar_Kind c K61) (shift_evar_KindEq G11 K59 K60 jm62 c G12 (weaken_shift_evar empty H78)) (shift_evar_KindEq G11 K60 K61 jm63 c G12 (weaken_shift_evar empty H78))))
  end
with shift_evar_TyEq (G11 : Env) (T103 : Ty) (T104 : Ty) (K59 : Kind) (jm66 : (TyEq G11 T103 T104 K59)) :
(forall (c : (Cutoff TmVar)) (G12 : Env) (H88 : (shift_evar c G11 G12)) ,
  (TyEq G12 (shift_TmVar_Ty c T103) (shift_TmVar_Ty c T104) (shift_TmVar_Kind c K59))) :=
  match jm66 in (TyEq _ T103 T104 K59) return (forall (c : (Cutoff TmVar)) (G12 : Env) (H88 : (shift_evar c G11 G12)) ,
    (TyEq G12 (shift_TmVar_Ty c T103) (shift_TmVar_Ty c T104) (shift_TmVar_Kind c K59))) with
    | (QT_Pi S59 S60 T101 T102 jm58 jm59) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H88 : (shift_evar c G11 G12)) =>
      (QT_Pi G12 (shift_TmVar_Ty c S59) (shift_TmVar_Ty (CS c) S60) (shift_TmVar_Ty c T101) (shift_TmVar_Ty (CS c) T102) (shift_evar_TyEq G11 S59 T101 (star) jm58 c G12 (weaken_shift_evar empty H88)) (shift_evar_TyEq (evar G11 T101) S60 T102 (star) jm59 (CS c) (evar G12 (shift_TmVar_Ty c T101)) (weaken_shift_evar (evar empty T101) H88))))
    | (QT_App K58 S59 S60 T100 t79 t80 jm60 jm61) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H88 : (shift_evar c G11 G12)) =>
      (TyEq_cast G12 _ _ _ G12 (shift_TmVar_Ty c (tapp S59 t79)) (shift_TmVar_Ty c (tapp S60 t80)) (shift_TmVar_Kind c (subst_TmVar_Kind X0 t79 K58)) eq_refl eq_refl eq_refl (eq_sym (shift_TmVar_Kind_subst_TmVar_Kind0_comm K58 c t79)) (QT_App G12 (shift_TmVar_Kind (CS c) K58) (shift_TmVar_Ty c S59) (shift_TmVar_Ty c S60) (shift_TmVar_Ty c T100) (shift_TmVar_Tm c t79) (shift_TmVar_Tm c t80) (shift_evar_TyEq G11 S59 S60 (kpi T100 K58) jm60 c G12 (weaken_shift_evar empty H88)) (shift_evar_TermEq G11 t79 t80 T100 jm61 c G12 (weaken_shift_evar empty H88)))))
    | (QT_Refl K58 T100 jm62) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H88 : (shift_evar c G11 G12)) =>
      (QT_Refl G12 (shift_TmVar_Kind c K58) (shift_TmVar_Ty c T100) (shift_evar_Kinding G11 T100 K58 jm62 c G12 (weaken_shift_evar empty H88))))
    | (QT_Symm K58 S59 T100 jm63) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H88 : (shift_evar c G11 G12)) =>
      (QT_Symm G12 (shift_TmVar_Kind c K58) (shift_TmVar_Ty c S59) (shift_TmVar_Ty c T100) (shift_evar_TyEq G11 T100 S59 K58 jm63 c G12 (weaken_shift_evar empty H88))))
    | (QT_Trans K58 S59 T100 U2 jm64 jm65) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H88 : (shift_evar c G11 G12)) =>
      (QT_Trans G12 (shift_TmVar_Kind c K58) (shift_TmVar_Ty c S59) (shift_TmVar_Ty c T100) (shift_TmVar_Ty c U2) (shift_evar_TyEq G11 S59 U2 K58 jm64 c G12 (weaken_shift_evar empty H88)) (shift_evar_TyEq G11 U2 T100 K58 jm65 c G12 (weaken_shift_evar empty H88))))
  end
with shift_evar_TermEq (G11 : Env) (t82 : Tm) (t83 : Tm) (T101 : Ty) (jm76 : (TermEq G11 t82 t83 T101)) :
(forall (c : (Cutoff TmVar)) (G12 : Env) (H107 : (shift_evar c G11 G12)) ,
  (TermEq G12 (shift_TmVar_Tm c t82) (shift_TmVar_Tm c t83) (shift_TmVar_Ty c T101))) :=
  match jm76 in (TermEq _ t82 t83 T101) return (forall (c : (Cutoff TmVar)) (G12 : Env) (H107 : (shift_evar c G11 G12)) ,
    (TermEq G12 (shift_TmVar_Tm c t82) (shift_TmVar_Tm c t83) (shift_TmVar_Ty c T101))) with
    | (Q_Abs S59 S60 T100 t80 t81 jm58 jm59) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H107 : (shift_evar c G11 G12)) =>
      (Q_Abs G12 (shift_TmVar_Ty c S59) (shift_TmVar_Ty c S60) (shift_TmVar_Ty (CS c) T100) (shift_TmVar_Tm (CS c) t80) (shift_TmVar_Tm (CS c) t81) (shift_evar_TyEq G11 S59 S60 (star) jm58 c G12 (weaken_shift_evar empty H107)) (shift_evar_TermEq (evar G11 S59) t80 t81 T100 jm59 (CS c) (evar G12 (shift_TmVar_Ty c S59)) (weaken_shift_evar (evar empty S59) H107))))
    | (Q_App S59 T100 s18 s19 t80 t81 jm60 jm61) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H107 : (shift_evar c G11 G12)) =>
      (TermEq_cast G12 _ _ _ G12 (shift_TmVar_Tm c (app t80 t81)) (shift_TmVar_Tm c (app s18 s19)) (shift_TmVar_Ty c (subst_TmVar_Ty X0 t81 T100)) eq_refl eq_refl eq_refl (eq_sym (shift_TmVar_Ty_subst_TmVar_Ty0_comm T100 c t81)) (Q_App G12 (shift_TmVar_Ty c S59) (shift_TmVar_Ty (CS c) T100) (shift_TmVar_Tm c s18) (shift_TmVar_Tm c s19) (shift_TmVar_Tm c t80) (shift_TmVar_Tm c t81) (shift_evar_TermEq G11 t80 s18 (tpi S59 T100) jm60 c G12 (weaken_shift_evar empty H107)) (shift_evar_TermEq G11 t81 s19 S59 jm61 c G12 (weaken_shift_evar empty H107)))))
    | (Q_Beta S59 T100 s17 t79 jm62 jm63) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H107 : (shift_evar c G11 G12)) =>
      (TermEq_cast G12 _ _ _ G12 (shift_TmVar_Tm c (app (abs S59 t79) s17)) (shift_TmVar_Tm c (subst_TmVar_Tm X0 s17 t79)) (shift_TmVar_Ty c (subst_TmVar_Ty X0 s17 T100)) eq_refl eq_refl (eq_sym (shift_TmVar_Tm_subst_TmVar_Tm0_comm t79 c s17)) (eq_sym (shift_TmVar_Ty_subst_TmVar_Ty0_comm T100 c s17)) (Q_Beta G12 (shift_TmVar_Ty c S59) (shift_TmVar_Ty (CS c) T100) (shift_TmVar_Tm c s17) (shift_TmVar_Tm (CS c) t79) (shift_evar_Typing (evar G11 S59) t79 T100 jm62 (CS c) (evar G12 (shift_TmVar_Ty c S59)) (weaken_shift_evar (evar empty S59) H107)) (shift_evar_Typing G11 s17 S59 jm63 c G12 (weaken_shift_evar empty H107)))))
    | (Q_Eta S59 T100 t79 jm64) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H107 : (shift_evar c G11 G12)) =>
      (TermEq_cast G12 _ _ _ G12 (shift_TmVar_Tm c (abs S59 (app (weakenTm t79 (HS TmVar H0)) (var I0)))) (shift_TmVar_Tm c t79) (shift_TmVar_Ty c (tpi S59 T100)) eq_refl (f_equal2 abs eq_refl (f_equal2 app (weakenTm_shift_TmVar_Tm (HS TmVar H0) c t79) eq_refl)) eq_refl eq_refl (Q_Eta G12 (shift_TmVar_Ty c S59) (shift_TmVar_Ty (CS c) T100) (shift_TmVar_Tm c t79) (shift_evar_Typing G11 t79 (tpi S59 T100) jm64 c G12 (weaken_shift_evar empty H107)))))
    | (Q_Proj1 S59 T100 t80 t81 jm65 jm66 jm67) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H107 : (shift_evar c G11 G12)) =>
      (Q_Proj1 G12 (shift_TmVar_Ty c S59) (shift_TmVar_Ty (CS c) T100) (shift_TmVar_Tm c t80) (shift_TmVar_Tm c t81) (shift_evar_Kinding G11 (tsig S59 T100) (star) jm65 c G12 (weaken_shift_evar empty H107)) (shift_evar_Typing G11 t80 S59 jm66 c G12 (weaken_shift_evar empty H107)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (shift_TmVar_Ty_subst_TmVar_Ty0_comm T100 c t80) (shift_evar_Typing G11 t81 (subst_TmVar_Ty X0 t80 T100) jm67 c G12 (weaken_shift_evar empty H107)))))
    | (Q_Proj2 S59 T100 t80 t81 jm68 jm69 jm70) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H107 : (shift_evar c G11 G12)) =>
      (TermEq_cast G12 _ _ _ G12 (shift_TmVar_Tm c (prj2 (pair t80 t81 S59 T100))) (shift_TmVar_Tm c t81) (shift_TmVar_Ty c (subst_TmVar_Ty X0 t80 T100)) eq_refl eq_refl eq_refl (eq_sym (shift_TmVar_Ty_subst_TmVar_Ty0_comm T100 c t80)) (Q_Proj2 G12 (shift_TmVar_Ty c S59) (shift_TmVar_Ty (CS c) T100) (shift_TmVar_Tm c t80) (shift_TmVar_Tm c t81) (shift_evar_Kinding G11 (tsig S59 T100) (star) jm68 c G12 (weaken_shift_evar empty H107)) (shift_evar_Typing G11 t80 S59 jm69 c G12 (weaken_shift_evar empty H107)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (shift_TmVar_Ty_subst_TmVar_Ty0_comm T100 c t80) (shift_evar_Typing G11 t81 (subst_TmVar_Ty X0 t80 T100) jm70 c G12 (weaken_shift_evar empty H107))))))
    | (Q_SjPair S59 T100 t79 jm71) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H107 : (shift_evar c G11 G12)) =>
      (Q_SjPair G12 (shift_TmVar_Ty c S59) (shift_TmVar_Ty (CS c) T100) (shift_TmVar_Tm c t79) (shift_evar_Typing G11 t79 (tsig S59 T100) jm71 c G12 (weaken_shift_evar empty H107))))
    | (Q_Refl T100 t79 jm72) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H107 : (shift_evar c G11 G12)) =>
      (Q_Refl G12 (shift_TmVar_Ty c T100) (shift_TmVar_Tm c t79) (shift_evar_Typing G11 t79 T100 jm72 c G12 (weaken_shift_evar empty H107))))
    | (Q_Symm T100 s17 t79 jm73) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H107 : (shift_evar c G11 G12)) =>
      (Q_Symm G12 (shift_TmVar_Ty c T100) (shift_TmVar_Tm c s17) (shift_TmVar_Tm c t79) (shift_evar_TermEq G11 t79 s17 T100 jm73 c G12 (weaken_shift_evar empty H107))))
    | (Q_Trans T100 s17 t79 u1 jm74 jm75) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H107 : (shift_evar c G11 G12)) =>
      (Q_Trans G12 (shift_TmVar_Ty c T100) (shift_TmVar_Tm c s17) (shift_TmVar_Tm c t79) (shift_TmVar_Tm c u1) (shift_evar_TermEq G11 s17 u1 T100 jm74 c G12 (weaken_shift_evar empty H107)) (shift_evar_TermEq G11 u1 t79 T100 jm75 c G12 (weaken_shift_evar empty H107))))
  end
with shift_evar_Typing (G11 : Env) (t82 : Tm) (T103 : Ty) (jm69 : (Typing G11 t82 T103)) :
(forall (c : (Cutoff TmVar)) (G12 : Env) (H90 : (shift_evar c G11 G12)) ,
  (Typing G12 (shift_TmVar_Tm c t82) (shift_TmVar_Ty c T103))) :=
  match jm69 in (Typing _ t82 T103) return (forall (c : (Cutoff TmVar)) (G12 : Env) (H90 : (shift_evar c G11 G12)) ,
    (Typing G12 (shift_TmVar_Tm c t82) (shift_TmVar_Ty c T103))) with
    | (T_Var T100 x72 lk1 H66 H67) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H90 : (shift_evar c G11 G12)) =>
      (T_Var G12 (shift_TmVar_Ty c T100) (shift_TmVar_Index c x72) (shift_evar_lookup_evar H90 lk1) (shift_TmVar__wfTy _ _ H66 _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H90))) (shift_TmVar__wfindex_TmVar _ _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H90)) _ H67)))
    | (T_Abs S59 T100 t79 jm68 jm58) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H90 : (shift_evar c G11 G12)) =>
      (T_Abs G12 (shift_TmVar_Ty c S59) (shift_TmVar_Ty (CS c) T100) (shift_TmVar_Tm (CS c) t79) (shift_evar_Kinding G11 S59 (star) jm68 c G12 (weaken_shift_evar empty H90)) (shift_evar_Typing (evar G11 S59) t79 T100 jm58 (CS c) (evar G12 (shift_TmVar_Ty c S59)) (weaken_shift_evar (evar empty S59) H90))))
    | (T_App S59 T100 t80 t81 jm59 jm60) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H90 : (shift_evar c G11 G12)) =>
      (Typing_cast G12 _ _ G12 (shift_TmVar_Tm c (app t80 t81)) (shift_TmVar_Ty c (subst_TmVar_Ty X0 t81 T100)) eq_refl eq_refl (eq_sym (shift_TmVar_Ty_subst_TmVar_Ty0_comm T100 c t81)) (T_App G12 (shift_TmVar_Ty c S59) (shift_TmVar_Ty (CS c) T100) (shift_TmVar_Tm c t80) (shift_TmVar_Tm c t81) (shift_evar_Typing G11 t80 (tpi S59 T100) jm59 c G12 (weaken_shift_evar empty H90)) (shift_evar_Typing G11 t81 S59 jm60 c G12 (weaken_shift_evar empty H90)))))
    | (T_Pair S59 T100 t80 t81 jm61 jm62 jm63) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H90 : (shift_evar c G11 G12)) =>
      (T_Pair G12 (shift_TmVar_Ty c S59) (shift_TmVar_Ty (CS c) T100) (shift_TmVar_Tm c t80) (shift_TmVar_Tm c t81) (shift_evar_Kinding G11 (tsig S59 T100) (star) jm61 c G12 (weaken_shift_evar empty H90)) (shift_evar_Typing G11 t80 S59 jm62 c G12 (weaken_shift_evar empty H90)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (shift_TmVar_Ty_subst_TmVar_Ty0_comm T100 c t80) (shift_evar_Typing G11 t81 (subst_TmVar_Ty X0 t80 T100) jm63 c G12 (weaken_shift_evar empty H90)))))
    | (T_Proj1 S59 T100 t79 jm64) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H90 : (shift_evar c G11 G12)) =>
      (T_Proj1 G12 (shift_TmVar_Ty c S59) (shift_TmVar_Ty (CS c) T100) (shift_TmVar_Tm c t79) (shift_evar_Typing G11 t79 (tsig S59 T100) jm64 c G12 (weaken_shift_evar empty H90))))
    | (T_Proj2 S59 T100 t79 jm65) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H90 : (shift_evar c G11 G12)) =>
      (Typing_cast G12 _ _ G12 (shift_TmVar_Tm c (prj2 t79)) (shift_TmVar_Ty c (subst_TmVar_Ty X0 (prj1 t79) T100)) eq_refl eq_refl (eq_sym (shift_TmVar_Ty_subst_TmVar_Ty0_comm T100 c (prj1 t79))) (T_Proj2 G12 (shift_TmVar_Ty c S59) (shift_TmVar_Ty (CS c) T100) (shift_TmVar_Tm c t79) (shift_evar_Typing G11 t79 (tsig S59 T100) jm65 c G12 (weaken_shift_evar empty H90)))))
    | (T_Conv T101 T102 t79 jm66 jm67) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H90 : (shift_evar c G11 G12)) =>
      (T_Conv G12 (shift_TmVar_Ty c T101) (shift_TmVar_Ty c T102) (shift_TmVar_Tm c t79) (shift_evar_Typing G11 t79 T101 jm66 c G12 (weaken_shift_evar empty H90)) (shift_evar_TyEq G11 T101 T102 (star) jm67 c G12 (weaken_shift_evar empty H90))))
  end
with shift_evar_Kinding (G11 : Env) (T103 : Ty) (K61 : Kind) (jm66 : (Kinding G11 T103 K61)) :
(forall (c : (Cutoff TmVar)) (G12 : Env) (H81 : (shift_evar c G11 G12)) ,
  (Kinding G12 (shift_TmVar_Ty c T103) (shift_TmVar_Kind c K61))) :=
  match jm66 in (Kinding _ T103 K61) return (forall (c : (Cutoff TmVar)) (G12 : Env) (H81 : (shift_evar c G11 G12)) ,
    (Kinding G12 (shift_TmVar_Ty c T103) (shift_TmVar_Kind c K61))) with
    | (K_TVar K58 X11 lk1 H66 H67) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H81 : (shift_evar c G11 G12)) =>
      (K_TVar G12 (shift_TmVar_Kind c K58) X11 (shift_evar_lookup_etvar H81 lk1) (shift_TmVar__wfKind _ _ H66 _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H81))) (shift_TmVar__wfindex_TyVar _ _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H81)) _ H67)))
    | (K_Pi T101 T102 jm58 jm59) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H81 : (shift_evar c G11 G12)) =>
      (K_Pi G12 (shift_TmVar_Ty c T101) (shift_TmVar_Ty (CS c) T102) (shift_evar_Kinding G11 T101 (star) jm58 c G12 (weaken_shift_evar empty H81)) (shift_evar_Kinding (evar G11 T101) T102 (star) jm59 (CS c) (evar G12 (shift_TmVar_Ty c T101)) (weaken_shift_evar (evar empty T101) H81))))
    | (K_App K58 S59 T100 t79 jm60 jm61) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H81 : (shift_evar c G11 G12)) =>
      (Kinding_cast G12 _ _ G12 (shift_TmVar_Ty c (tapp S59 t79)) (shift_TmVar_Kind c (subst_TmVar_Kind X0 t79 K58)) eq_refl eq_refl (eq_sym (shift_TmVar_Kind_subst_TmVar_Kind0_comm K58 c t79)) (K_App G12 (shift_TmVar_Kind (CS c) K58) (shift_TmVar_Ty c S59) (shift_TmVar_Ty c T100) (shift_TmVar_Tm c t79) (shift_evar_Kinding G11 S59 (kpi T100 K58) jm60 c G12 (weaken_shift_evar empty H81)) (shift_evar_Typing G11 t79 T100 jm61 c G12 (weaken_shift_evar empty H81)))))
    | (K_Sigma S59 T100 jm62 jm63) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H81 : (shift_evar c G11 G12)) =>
      (K_Sigma G12 (shift_TmVar_Ty c S59) (shift_TmVar_Ty (CS c) T100) (shift_evar_Kinding G11 S59 (star) jm62 c G12 (weaken_shift_evar empty H81)) (shift_evar_Kinding (evar G11 S59) T100 (star) jm63 (CS c) (evar G12 (shift_TmVar_Ty c S59)) (weaken_shift_evar (evar empty S59) H81))))
    | (K_Conv K59 K60 T100 jm64 jm65) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H81 : (shift_evar c G11 G12)) =>
      (K_Conv G12 (shift_TmVar_Kind c K59) (shift_TmVar_Kind c K60) (shift_TmVar_Ty c T100) (shift_evar_Kinding G11 T100 K59 jm64 c G12 (weaken_shift_evar empty H81)) (shift_evar_KindEq G11 K59 K60 jm65 c G12 (weaken_shift_evar empty H81))))
  end
with shift_evar_WfKind (G11 : Env) (K59 : Kind) (jm60 : (WfKind G11 K59)) :
(forall (c : (Cutoff TmVar)) (G12 : Env) (H69 : (shift_evar c G11 G12)) ,
  (WfKind G12 (shift_TmVar_Kind c K59))) :=
  match jm60 in (WfKind _ K59) return (forall (c : (Cutoff TmVar)) (G12 : Env) (H69 : (shift_evar c G11 G12)) ,
    (WfKind G12 (shift_TmVar_Kind c K59))) with
    | (WfStar) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H69 : (shift_evar c G11 G12)) =>
      (WfStar G12))
    | (WfPi K58 T100 jm58 jm59) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H69 : (shift_evar c G11 G12)) =>
      (WfKind_cast G12 _ G12 (shift_TmVar_Kind c (kpi T100 (weakenKind K58 (HS TmVar H0)))) eq_refl (f_equal2 kpi eq_refl (weakenKind_shift_TmVar_Kind (HS TmVar H0) c K58)) (WfPi G12 (shift_TmVar_Kind c K58) (shift_TmVar_Ty c T100) (shift_evar_Kinding G11 T100 (star) jm58 c G12 (weaken_shift_evar empty H69)) (shift_evar_WfKind G11 K58 jm59 c G12 (weaken_shift_evar empty H69)))))
  end.
Fixpoint shift_etvar_KindEq (G11 : Env) (K62 : Kind) (K63 : Kind) (jm64 : (KindEq G11 K62 K63)) :
(forall (c : (Cutoff TyVar)) (G12 : Env) (H78 : (shift_etvar c G11 G12)) ,
  (KindEq G12 (shift_TyVar_Kind c K62) (shift_TyVar_Kind c K63))) :=
  match jm64 in (KindEq _ K62 K63) return (forall (c : (Cutoff TyVar)) (G12 : Env) (H78 : (shift_etvar c G11 G12)) ,
    (KindEq G12 (shift_TyVar_Kind c K62) (shift_TyVar_Kind c K63))) with
    | (QK_Pi K59 K60 T100 T101 jm58 jm59) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H78 : (shift_etvar c G11 G12)) =>
      (QK_Pi G12 (shift_TyVar_Kind c K59) (shift_TyVar_Kind c K60) (shift_TyVar_Ty c T100) (shift_TyVar_Ty c T101) (shift_etvar_TyEq G11 T100 T101 (star) jm58 c G12 (weaken_shift_etvar empty H78)) (shift_etvar_KindEq (evar G11 T100) K59 K60 jm59 c (evar G12 (shift_TyVar_Ty c T100)) (weaken_shift_etvar (evar empty T100) H78))))
    | (QK_Refl K58 jm60) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H78 : (shift_etvar c G11 G12)) =>
      (QK_Refl G12 (shift_TyVar_Kind c K58) (shift_etvar_WfKind G11 K58 jm60 c G12 (weaken_shift_etvar empty H78))))
    | (QK_Sym K59 K60 jm61) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H78 : (shift_etvar c G11 G12)) =>
      (QK_Sym G12 (shift_TyVar_Kind c K59) (shift_TyVar_Kind c K60) (shift_etvar_KindEq G11 K59 K60 jm61 c G12 (weaken_shift_etvar empty H78))))
    | (QK_Trans K59 K60 K61 jm62 jm63) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H78 : (shift_etvar c G11 G12)) =>
      (QK_Trans G12 (shift_TyVar_Kind c K59) (shift_TyVar_Kind c K60) (shift_TyVar_Kind c K61) (shift_etvar_KindEq G11 K59 K60 jm62 c G12 (weaken_shift_etvar empty H78)) (shift_etvar_KindEq G11 K60 K61 jm63 c G12 (weaken_shift_etvar empty H78))))
  end
with shift_etvar_TyEq (G11 : Env) (T103 : Ty) (T104 : Ty) (K59 : Kind) (jm66 : (TyEq G11 T103 T104 K59)) :
(forall (c : (Cutoff TyVar)) (G12 : Env) (H88 : (shift_etvar c G11 G12)) ,
  (TyEq G12 (shift_TyVar_Ty c T103) (shift_TyVar_Ty c T104) (shift_TyVar_Kind c K59))) :=
  match jm66 in (TyEq _ T103 T104 K59) return (forall (c : (Cutoff TyVar)) (G12 : Env) (H88 : (shift_etvar c G11 G12)) ,
    (TyEq G12 (shift_TyVar_Ty c T103) (shift_TyVar_Ty c T104) (shift_TyVar_Kind c K59))) with
    | (QT_Pi S59 S60 T101 T102 jm58 jm59) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H88 : (shift_etvar c G11 G12)) =>
      (QT_Pi G12 (shift_TyVar_Ty c S59) (shift_TyVar_Ty c S60) (shift_TyVar_Ty c T101) (shift_TyVar_Ty c T102) (shift_etvar_TyEq G11 S59 T101 (star) jm58 c G12 (weaken_shift_etvar empty H88)) (shift_etvar_TyEq (evar G11 T101) S60 T102 (star) jm59 c (evar G12 (shift_TyVar_Ty c T101)) (weaken_shift_etvar (evar empty T101) H88))))
    | (QT_App K58 S59 S60 T100 t79 t80 jm60 jm61) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H88 : (shift_etvar c G11 G12)) =>
      (TyEq_cast G12 _ _ _ G12 (shift_TyVar_Ty c (tapp S59 t79)) (shift_TyVar_Ty c (tapp S60 t80)) (shift_TyVar_Kind c (subst_TmVar_Kind X0 t79 K58)) eq_refl eq_refl eq_refl (eq_sym (shift_TyVar_Kind_subst_TmVar_Kind0_comm K58 c t79)) (QT_App G12 (shift_TyVar_Kind c K58) (shift_TyVar_Ty c S59) (shift_TyVar_Ty c S60) (shift_TyVar_Ty c T100) (shift_TyVar_Tm c t79) (shift_TyVar_Tm c t80) (shift_etvar_TyEq G11 S59 S60 (kpi T100 K58) jm60 c G12 (weaken_shift_etvar empty H88)) (shift_etvar_TermEq G11 t79 t80 T100 jm61 c G12 (weaken_shift_etvar empty H88)))))
    | (QT_Refl K58 T100 jm62) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H88 : (shift_etvar c G11 G12)) =>
      (QT_Refl G12 (shift_TyVar_Kind c K58) (shift_TyVar_Ty c T100) (shift_etvar_Kinding G11 T100 K58 jm62 c G12 (weaken_shift_etvar empty H88))))
    | (QT_Symm K58 S59 T100 jm63) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H88 : (shift_etvar c G11 G12)) =>
      (QT_Symm G12 (shift_TyVar_Kind c K58) (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_etvar_TyEq G11 T100 S59 K58 jm63 c G12 (weaken_shift_etvar empty H88))))
    | (QT_Trans K58 S59 T100 U2 jm64 jm65) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H88 : (shift_etvar c G11 G12)) =>
      (QT_Trans G12 (shift_TyVar_Kind c K58) (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_TyVar_Ty c U2) (shift_etvar_TyEq G11 S59 U2 K58 jm64 c G12 (weaken_shift_etvar empty H88)) (shift_etvar_TyEq G11 U2 T100 K58 jm65 c G12 (weaken_shift_etvar empty H88))))
  end
with shift_etvar_TermEq (G11 : Env) (t82 : Tm) (t83 : Tm) (T101 : Ty) (jm76 : (TermEq G11 t82 t83 T101)) :
(forall (c : (Cutoff TyVar)) (G12 : Env) (H107 : (shift_etvar c G11 G12)) ,
  (TermEq G12 (shift_TyVar_Tm c t82) (shift_TyVar_Tm c t83) (shift_TyVar_Ty c T101))) :=
  match jm76 in (TermEq _ t82 t83 T101) return (forall (c : (Cutoff TyVar)) (G12 : Env) (H107 : (shift_etvar c G11 G12)) ,
    (TermEq G12 (shift_TyVar_Tm c t82) (shift_TyVar_Tm c t83) (shift_TyVar_Ty c T101))) with
    | (Q_Abs S59 S60 T100 t80 t81 jm58 jm59) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H107 : (shift_etvar c G11 G12)) =>
      (Q_Abs G12 (shift_TyVar_Ty c S59) (shift_TyVar_Ty c S60) (shift_TyVar_Ty c T100) (shift_TyVar_Tm c t80) (shift_TyVar_Tm c t81) (shift_etvar_TyEq G11 S59 S60 (star) jm58 c G12 (weaken_shift_etvar empty H107)) (shift_etvar_TermEq (evar G11 S59) t80 t81 T100 jm59 c (evar G12 (shift_TyVar_Ty c S59)) (weaken_shift_etvar (evar empty S59) H107))))
    | (Q_App S59 T100 s18 s19 t80 t81 jm60 jm61) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H107 : (shift_etvar c G11 G12)) =>
      (TermEq_cast G12 _ _ _ G12 (shift_TyVar_Tm c (app t80 t81)) (shift_TyVar_Tm c (app s18 s19)) (shift_TyVar_Ty c (subst_TmVar_Ty X0 t81 T100)) eq_refl eq_refl eq_refl (eq_sym (shift_TyVar_Ty_subst_TmVar_Ty0_comm T100 c t81)) (Q_App G12 (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_TyVar_Tm c s18) (shift_TyVar_Tm c s19) (shift_TyVar_Tm c t80) (shift_TyVar_Tm c t81) (shift_etvar_TermEq G11 t80 s18 (tpi S59 T100) jm60 c G12 (weaken_shift_etvar empty H107)) (shift_etvar_TermEq G11 t81 s19 S59 jm61 c G12 (weaken_shift_etvar empty H107)))))
    | (Q_Beta S59 T100 s17 t79 jm62 jm63) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H107 : (shift_etvar c G11 G12)) =>
      (TermEq_cast G12 _ _ _ G12 (shift_TyVar_Tm c (app (abs S59 t79) s17)) (shift_TyVar_Tm c (subst_TmVar_Tm X0 s17 t79)) (shift_TyVar_Ty c (subst_TmVar_Ty X0 s17 T100)) eq_refl eq_refl (eq_sym (shift_TyVar_Tm_subst_TmVar_Tm0_comm t79 c s17)) (eq_sym (shift_TyVar_Ty_subst_TmVar_Ty0_comm T100 c s17)) (Q_Beta G12 (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_TyVar_Tm c s17) (shift_TyVar_Tm c t79) (shift_etvar_Typing (evar G11 S59) t79 T100 jm62 c (evar G12 (shift_TyVar_Ty c S59)) (weaken_shift_etvar (evar empty S59) H107)) (shift_etvar_Typing G11 s17 S59 jm63 c G12 (weaken_shift_etvar empty H107)))))
    | (Q_Eta S59 T100 t79 jm64) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H107 : (shift_etvar c G11 G12)) =>
      (TermEq_cast G12 _ _ _ G12 (shift_TyVar_Tm c (abs S59 (app (weakenTm t79 (HS TmVar H0)) (var I0)))) (shift_TyVar_Tm c t79) (shift_TyVar_Ty c (tpi S59 T100)) eq_refl (f_equal2 abs eq_refl (f_equal2 app (weakenTm_shift_TyVar_Tm (HS TmVar H0) c t79) eq_refl)) eq_refl eq_refl (Q_Eta G12 (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_TyVar_Tm c t79) (shift_etvar_Typing G11 t79 (tpi S59 T100) jm64 c G12 (weaken_shift_etvar empty H107)))))
    | (Q_Proj1 S59 T100 t80 t81 jm65 jm66 jm67) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H107 : (shift_etvar c G11 G12)) =>
      (Q_Proj1 G12 (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_TyVar_Tm c t80) (shift_TyVar_Tm c t81) (shift_etvar_Kinding G11 (tsig S59 T100) (star) jm65 c G12 (weaken_shift_etvar empty H107)) (shift_etvar_Typing G11 t80 S59 jm66 c G12 (weaken_shift_etvar empty H107)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (shift_TyVar_Ty_subst_TmVar_Ty0_comm T100 c t80) (shift_etvar_Typing G11 t81 (subst_TmVar_Ty X0 t80 T100) jm67 c G12 (weaken_shift_etvar empty H107)))))
    | (Q_Proj2 S59 T100 t80 t81 jm68 jm69 jm70) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H107 : (shift_etvar c G11 G12)) =>
      (TermEq_cast G12 _ _ _ G12 (shift_TyVar_Tm c (prj2 (pair t80 t81 S59 T100))) (shift_TyVar_Tm c t81) (shift_TyVar_Ty c (subst_TmVar_Ty X0 t80 T100)) eq_refl eq_refl eq_refl (eq_sym (shift_TyVar_Ty_subst_TmVar_Ty0_comm T100 c t80)) (Q_Proj2 G12 (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_TyVar_Tm c t80) (shift_TyVar_Tm c t81) (shift_etvar_Kinding G11 (tsig S59 T100) (star) jm68 c G12 (weaken_shift_etvar empty H107)) (shift_etvar_Typing G11 t80 S59 jm69 c G12 (weaken_shift_etvar empty H107)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (shift_TyVar_Ty_subst_TmVar_Ty0_comm T100 c t80) (shift_etvar_Typing G11 t81 (subst_TmVar_Ty X0 t80 T100) jm70 c G12 (weaken_shift_etvar empty H107))))))
    | (Q_SjPair S59 T100 t79 jm71) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H107 : (shift_etvar c G11 G12)) =>
      (Q_SjPair G12 (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_TyVar_Tm c t79) (shift_etvar_Typing G11 t79 (tsig S59 T100) jm71 c G12 (weaken_shift_etvar empty H107))))
    | (Q_Refl T100 t79 jm72) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H107 : (shift_etvar c G11 G12)) =>
      (Q_Refl G12 (shift_TyVar_Ty c T100) (shift_TyVar_Tm c t79) (shift_etvar_Typing G11 t79 T100 jm72 c G12 (weaken_shift_etvar empty H107))))
    | (Q_Symm T100 s17 t79 jm73) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H107 : (shift_etvar c G11 G12)) =>
      (Q_Symm G12 (shift_TyVar_Ty c T100) (shift_TyVar_Tm c s17) (shift_TyVar_Tm c t79) (shift_etvar_TermEq G11 t79 s17 T100 jm73 c G12 (weaken_shift_etvar empty H107))))
    | (Q_Trans T100 s17 t79 u1 jm74 jm75) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H107 : (shift_etvar c G11 G12)) =>
      (Q_Trans G12 (shift_TyVar_Ty c T100) (shift_TyVar_Tm c s17) (shift_TyVar_Tm c t79) (shift_TyVar_Tm c u1) (shift_etvar_TermEq G11 s17 u1 T100 jm74 c G12 (weaken_shift_etvar empty H107)) (shift_etvar_TermEq G11 u1 t79 T100 jm75 c G12 (weaken_shift_etvar empty H107))))
  end
with shift_etvar_Typing (G11 : Env) (t82 : Tm) (T103 : Ty) (jm69 : (Typing G11 t82 T103)) :
(forall (c : (Cutoff TyVar)) (G12 : Env) (H90 : (shift_etvar c G11 G12)) ,
  (Typing G12 (shift_TyVar_Tm c t82) (shift_TyVar_Ty c T103))) :=
  match jm69 in (Typing _ t82 T103) return (forall (c : (Cutoff TyVar)) (G12 : Env) (H90 : (shift_etvar c G11 G12)) ,
    (Typing G12 (shift_TyVar_Tm c t82) (shift_TyVar_Ty c T103))) with
    | (T_Var T100 x72 lk1 H66 H67) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H90 : (shift_etvar c G11 G12)) =>
      (T_Var G12 (shift_TyVar_Ty c T100) x72 (shift_etvar_lookup_evar H90 lk1) (shift_TyVar__wfTy _ _ H66 _ _ (weaken_shifthvl_TyVar H0 (shift_etvar_shifthvl_TyVar H90))) (shift_TyVar__wfindex_TmVar _ _ _ (weaken_shifthvl_TyVar H0 (shift_etvar_shifthvl_TyVar H90)) _ H67)))
    | (T_Abs S59 T100 t79 jm68 jm58) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H90 : (shift_etvar c G11 G12)) =>
      (T_Abs G12 (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_TyVar_Tm c t79) (shift_etvar_Kinding G11 S59 (star) jm68 c G12 (weaken_shift_etvar empty H90)) (shift_etvar_Typing (evar G11 S59) t79 T100 jm58 c (evar G12 (shift_TyVar_Ty c S59)) (weaken_shift_etvar (evar empty S59) H90))))
    | (T_App S59 T100 t80 t81 jm59 jm60) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H90 : (shift_etvar c G11 G12)) =>
      (Typing_cast G12 _ _ G12 (shift_TyVar_Tm c (app t80 t81)) (shift_TyVar_Ty c (subst_TmVar_Ty X0 t81 T100)) eq_refl eq_refl (eq_sym (shift_TyVar_Ty_subst_TmVar_Ty0_comm T100 c t81)) (T_App G12 (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_TyVar_Tm c t80) (shift_TyVar_Tm c t81) (shift_etvar_Typing G11 t80 (tpi S59 T100) jm59 c G12 (weaken_shift_etvar empty H90)) (shift_etvar_Typing G11 t81 S59 jm60 c G12 (weaken_shift_etvar empty H90)))))
    | (T_Pair S59 T100 t80 t81 jm61 jm62 jm63) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H90 : (shift_etvar c G11 G12)) =>
      (T_Pair G12 (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_TyVar_Tm c t80) (shift_TyVar_Tm c t81) (shift_etvar_Kinding G11 (tsig S59 T100) (star) jm61 c G12 (weaken_shift_etvar empty H90)) (shift_etvar_Typing G11 t80 S59 jm62 c G12 (weaken_shift_etvar empty H90)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (shift_TyVar_Ty_subst_TmVar_Ty0_comm T100 c t80) (shift_etvar_Typing G11 t81 (subst_TmVar_Ty X0 t80 T100) jm63 c G12 (weaken_shift_etvar empty H90)))))
    | (T_Proj1 S59 T100 t79 jm64) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H90 : (shift_etvar c G11 G12)) =>
      (T_Proj1 G12 (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_TyVar_Tm c t79) (shift_etvar_Typing G11 t79 (tsig S59 T100) jm64 c G12 (weaken_shift_etvar empty H90))))
    | (T_Proj2 S59 T100 t79 jm65) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H90 : (shift_etvar c G11 G12)) =>
      (Typing_cast G12 _ _ G12 (shift_TyVar_Tm c (prj2 t79)) (shift_TyVar_Ty c (subst_TmVar_Ty X0 (prj1 t79) T100)) eq_refl eq_refl (eq_sym (shift_TyVar_Ty_subst_TmVar_Ty0_comm T100 c (prj1 t79))) (T_Proj2 G12 (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_TyVar_Tm c t79) (shift_etvar_Typing G11 t79 (tsig S59 T100) jm65 c G12 (weaken_shift_etvar empty H90)))))
    | (T_Conv T101 T102 t79 jm66 jm67) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H90 : (shift_etvar c G11 G12)) =>
      (T_Conv G12 (shift_TyVar_Ty c T101) (shift_TyVar_Ty c T102) (shift_TyVar_Tm c t79) (shift_etvar_Typing G11 t79 T101 jm66 c G12 (weaken_shift_etvar empty H90)) (shift_etvar_TyEq G11 T101 T102 (star) jm67 c G12 (weaken_shift_etvar empty H90))))
  end
with shift_etvar_Kinding (G11 : Env) (T103 : Ty) (K61 : Kind) (jm66 : (Kinding G11 T103 K61)) :
(forall (c : (Cutoff TyVar)) (G12 : Env) (H81 : (shift_etvar c G11 G12)) ,
  (Kinding G12 (shift_TyVar_Ty c T103) (shift_TyVar_Kind c K61))) :=
  match jm66 in (Kinding _ T103 K61) return (forall (c : (Cutoff TyVar)) (G12 : Env) (H81 : (shift_etvar c G11 G12)) ,
    (Kinding G12 (shift_TyVar_Ty c T103) (shift_TyVar_Kind c K61))) with
    | (K_TVar K58 X11 lk1 H66 H67) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H81 : (shift_etvar c G11 G12)) =>
      (K_TVar G12 (shift_TyVar_Kind c K58) (shift_TyVar_Index c X11) (shift_etvar_lookup_etvar H81 lk1) (shift_TyVar__wfKind _ _ H66 _ _ (weaken_shifthvl_TyVar H0 (shift_etvar_shifthvl_TyVar H81))) (shift_TyVar__wfindex_TyVar _ _ _ (weaken_shifthvl_TyVar H0 (shift_etvar_shifthvl_TyVar H81)) _ H67)))
    | (K_Pi T101 T102 jm58 jm59) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H81 : (shift_etvar c G11 G12)) =>
      (K_Pi G12 (shift_TyVar_Ty c T101) (shift_TyVar_Ty c T102) (shift_etvar_Kinding G11 T101 (star) jm58 c G12 (weaken_shift_etvar empty H81)) (shift_etvar_Kinding (evar G11 T101) T102 (star) jm59 c (evar G12 (shift_TyVar_Ty c T101)) (weaken_shift_etvar (evar empty T101) H81))))
    | (K_App K58 S59 T100 t79 jm60 jm61) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H81 : (shift_etvar c G11 G12)) =>
      (Kinding_cast G12 _ _ G12 (shift_TyVar_Ty c (tapp S59 t79)) (shift_TyVar_Kind c (subst_TmVar_Kind X0 t79 K58)) eq_refl eq_refl (eq_sym (shift_TyVar_Kind_subst_TmVar_Kind0_comm K58 c t79)) (K_App G12 (shift_TyVar_Kind c K58) (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_TyVar_Tm c t79) (shift_etvar_Kinding G11 S59 (kpi T100 K58) jm60 c G12 (weaken_shift_etvar empty H81)) (shift_etvar_Typing G11 t79 T100 jm61 c G12 (weaken_shift_etvar empty H81)))))
    | (K_Sigma S59 T100 jm62 jm63) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H81 : (shift_etvar c G11 G12)) =>
      (K_Sigma G12 (shift_TyVar_Ty c S59) (shift_TyVar_Ty c T100) (shift_etvar_Kinding G11 S59 (star) jm62 c G12 (weaken_shift_etvar empty H81)) (shift_etvar_Kinding (evar G11 S59) T100 (star) jm63 c (evar G12 (shift_TyVar_Ty c S59)) (weaken_shift_etvar (evar empty S59) H81))))
    | (K_Conv K59 K60 T100 jm64 jm65) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H81 : (shift_etvar c G11 G12)) =>
      (K_Conv G12 (shift_TyVar_Kind c K59) (shift_TyVar_Kind c K60) (shift_TyVar_Ty c T100) (shift_etvar_Kinding G11 T100 K59 jm64 c G12 (weaken_shift_etvar empty H81)) (shift_etvar_KindEq G11 K59 K60 jm65 c G12 (weaken_shift_etvar empty H81))))
  end
with shift_etvar_WfKind (G11 : Env) (K59 : Kind) (jm60 : (WfKind G11 K59)) :
(forall (c : (Cutoff TyVar)) (G12 : Env) (H69 : (shift_etvar c G11 G12)) ,
  (WfKind G12 (shift_TyVar_Kind c K59))) :=
  match jm60 in (WfKind _ K59) return (forall (c : (Cutoff TyVar)) (G12 : Env) (H69 : (shift_etvar c G11 G12)) ,
    (WfKind G12 (shift_TyVar_Kind c K59))) with
    | (WfStar) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H69 : (shift_etvar c G11 G12)) =>
      (WfStar G12))
    | (WfPi K58 T100 jm58 jm59) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H69 : (shift_etvar c G11 G12)) =>
      (WfKind_cast G12 _ G12 (shift_TyVar_Kind c (kpi T100 (weakenKind K58 (HS TmVar H0)))) eq_refl (f_equal2 kpi eq_refl (weakenKind_shift_TyVar_Kind (HS TmVar H0) c K58)) (WfPi G12 (shift_TyVar_Kind c K58) (shift_TyVar_Ty c T100) (shift_etvar_Kinding G11 T100 (star) jm58 c G12 (weaken_shift_etvar empty H69)) (shift_etvar_WfKind G11 K58 jm59 c G12 (weaken_shift_etvar empty H69)))))
  end.
 Hint Resolve shift_evar_KindEq shift_etvar_KindEq shift_evar_Kinding shift_etvar_Kinding shift_evar_TermEq shift_etvar_TermEq shift_evar_TyEq shift_etvar_TyEq shift_evar_Typing shift_etvar_Typing shift_evar_WfKind shift_etvar_WfKind : infra.
 Hint Resolve shift_evar_KindEq shift_etvar_KindEq shift_evar_Kinding shift_etvar_Kinding shift_evar_TermEq shift_etvar_TermEq shift_evar_TyEq shift_etvar_TyEq shift_evar_Typing shift_etvar_Typing shift_evar_WfKind shift_etvar_WfKind : shift.
Fixpoint weaken_KindEq (G : Env) :
(forall (G0 : Env) (K47 : Kind) (K48 : Kind) (jm52 : (KindEq G0 K47 K48)) ,
  (KindEq (appendEnv G0 G) (weakenKind K47 (domainEnv G)) (weakenKind K48 (domainEnv G)))) :=
  match G return (forall (G0 : Env) (K47 : Kind) (K48 : Kind) (jm52 : (KindEq G0 K47 K48)) ,
    (KindEq (appendEnv G0 G) (weakenKind K47 (domainEnv G)) (weakenKind K48 (domainEnv G)))) with
    | (empty) => (fun (G0 : Env) (K47 : Kind) (K48 : Kind) (jm52 : (KindEq G0 K47 K48)) =>
      jm52)
    | (evar G T89) => (fun (G0 : Env) (K47 : Kind) (K48 : Kind) (jm52 : (KindEq G0 K47 K48)) =>
      (shift_evar_KindEq (appendEnv G0 G) (weakenKind K47 (domainEnv G)) (weakenKind K48 (domainEnv G)) (weaken_KindEq G G0 K47 K48 jm52) C0 (evar (appendEnv G0 G) T89) shift_evar_here))
    | (etvar G K49) => (fun (G0 : Env) (K47 : Kind) (K48 : Kind) (jm52 : (KindEq G0 K47 K48)) =>
      (shift_etvar_KindEq (appendEnv G0 G) (weakenKind K47 (domainEnv G)) (weakenKind K48 (domainEnv G)) (weaken_KindEq G G0 K47 K48 jm52) C0 (etvar (appendEnv G0 G) K49) shift_etvar_here))
  end.
Fixpoint weaken_TyEq (G1 : Env) :
(forall (G2 : Env) (T90 : Ty) (T91 : Ty) (K50 : Kind) (jm53 : (TyEq G2 T90 T91 K50)) ,
  (TyEq (appendEnv G2 G1) (weakenTy T90 (domainEnv G1)) (weakenTy T91 (domainEnv G1)) (weakenKind K50 (domainEnv G1)))) :=
  match G1 return (forall (G2 : Env) (T90 : Ty) (T91 : Ty) (K50 : Kind) (jm53 : (TyEq G2 T90 T91 K50)) ,
    (TyEq (appendEnv G2 G1) (weakenTy T90 (domainEnv G1)) (weakenTy T91 (domainEnv G1)) (weakenKind K50 (domainEnv G1)))) with
    | (empty) => (fun (G2 : Env) (T90 : Ty) (T91 : Ty) (K50 : Kind) (jm53 : (TyEq G2 T90 T91 K50)) =>
      jm53)
    | (evar G1 T92) => (fun (G2 : Env) (T90 : Ty) (T91 : Ty) (K50 : Kind) (jm53 : (TyEq G2 T90 T91 K50)) =>
      (shift_evar_TyEq (appendEnv G2 G1) (weakenTy T90 (domainEnv G1)) (weakenTy T91 (domainEnv G1)) (weakenKind K50 (domainEnv G1)) (weaken_TyEq G1 G2 T90 T91 K50 jm53) C0 (evar (appendEnv G2 G1) T92) shift_evar_here))
    | (etvar G1 K51) => (fun (G2 : Env) (T90 : Ty) (T91 : Ty) (K50 : Kind) (jm53 : (TyEq G2 T90 T91 K50)) =>
      (shift_etvar_TyEq (appendEnv G2 G1) (weakenTy T90 (domainEnv G1)) (weakenTy T91 (domainEnv G1)) (weakenKind K50 (domainEnv G1)) (weaken_TyEq G1 G2 T90 T91 K50 jm53) C0 (etvar (appendEnv G2 G1) K51) shift_etvar_here))
  end.
Fixpoint weaken_TermEq (G3 : Env) :
(forall (G4 : Env) (t76 : Tm) (t77 : Tm) (T93 : Ty) (jm54 : (TermEq G4 t76 t77 T93)) ,
  (TermEq (appendEnv G4 G3) (weakenTm t76 (domainEnv G3)) (weakenTm t77 (domainEnv G3)) (weakenTy T93 (domainEnv G3)))) :=
  match G3 return (forall (G4 : Env) (t76 : Tm) (t77 : Tm) (T93 : Ty) (jm54 : (TermEq G4 t76 t77 T93)) ,
    (TermEq (appendEnv G4 G3) (weakenTm t76 (domainEnv G3)) (weakenTm t77 (domainEnv G3)) (weakenTy T93 (domainEnv G3)))) with
    | (empty) => (fun (G4 : Env) (t76 : Tm) (t77 : Tm) (T93 : Ty) (jm54 : (TermEq G4 t76 t77 T93)) =>
      jm54)
    | (evar G3 T94) => (fun (G4 : Env) (t76 : Tm) (t77 : Tm) (T93 : Ty) (jm54 : (TermEq G4 t76 t77 T93)) =>
      (shift_evar_TermEq (appendEnv G4 G3) (weakenTm t76 (domainEnv G3)) (weakenTm t77 (domainEnv G3)) (weakenTy T93 (domainEnv G3)) (weaken_TermEq G3 G4 t76 t77 T93 jm54) C0 (evar (appendEnv G4 G3) T94) shift_evar_here))
    | (etvar G3 K52) => (fun (G4 : Env) (t76 : Tm) (t77 : Tm) (T93 : Ty) (jm54 : (TermEq G4 t76 t77 T93)) =>
      (shift_etvar_TermEq (appendEnv G4 G3) (weakenTm t76 (domainEnv G3)) (weakenTm t77 (domainEnv G3)) (weakenTy T93 (domainEnv G3)) (weaken_TermEq G3 G4 t76 t77 T93 jm54) C0 (etvar (appendEnv G4 G3) K52) shift_etvar_here))
  end.
Fixpoint weaken_Typing (G5 : Env) :
(forall (G6 : Env) (t78 : Tm) (T95 : Ty) (jm55 : (Typing G6 t78 T95)) ,
  (Typing (appendEnv G6 G5) (weakenTm t78 (domainEnv G5)) (weakenTy T95 (domainEnv G5)))) :=
  match G5 return (forall (G6 : Env) (t78 : Tm) (T95 : Ty) (jm55 : (Typing G6 t78 T95)) ,
    (Typing (appendEnv G6 G5) (weakenTm t78 (domainEnv G5)) (weakenTy T95 (domainEnv G5)))) with
    | (empty) => (fun (G6 : Env) (t78 : Tm) (T95 : Ty) (jm55 : (Typing G6 t78 T95)) =>
      jm55)
    | (evar G5 T96) => (fun (G6 : Env) (t78 : Tm) (T95 : Ty) (jm55 : (Typing G6 t78 T95)) =>
      (shift_evar_Typing (appendEnv G6 G5) (weakenTm t78 (domainEnv G5)) (weakenTy T95 (domainEnv G5)) (weaken_Typing G5 G6 t78 T95 jm55) C0 (evar (appendEnv G6 G5) T96) shift_evar_here))
    | (etvar G5 K53) => (fun (G6 : Env) (t78 : Tm) (T95 : Ty) (jm55 : (Typing G6 t78 T95)) =>
      (shift_etvar_Typing (appendEnv G6 G5) (weakenTm t78 (domainEnv G5)) (weakenTy T95 (domainEnv G5)) (weaken_Typing G5 G6 t78 T95 jm55) C0 (etvar (appendEnv G6 G5) K53) shift_etvar_here))
  end.
Fixpoint weaken_Kinding (G7 : Env) :
(forall (G8 : Env) (T97 : Ty) (K54 : Kind) (jm56 : (Kinding G8 T97 K54)) ,
  (Kinding (appendEnv G8 G7) (weakenTy T97 (domainEnv G7)) (weakenKind K54 (domainEnv G7)))) :=
  match G7 return (forall (G8 : Env) (T97 : Ty) (K54 : Kind) (jm56 : (Kinding G8 T97 K54)) ,
    (Kinding (appendEnv G8 G7) (weakenTy T97 (domainEnv G7)) (weakenKind K54 (domainEnv G7)))) with
    | (empty) => (fun (G8 : Env) (T97 : Ty) (K54 : Kind) (jm56 : (Kinding G8 T97 K54)) =>
      jm56)
    | (evar G7 T98) => (fun (G8 : Env) (T97 : Ty) (K54 : Kind) (jm56 : (Kinding G8 T97 K54)) =>
      (shift_evar_Kinding (appendEnv G8 G7) (weakenTy T97 (domainEnv G7)) (weakenKind K54 (domainEnv G7)) (weaken_Kinding G7 G8 T97 K54 jm56) C0 (evar (appendEnv G8 G7) T98) shift_evar_here))
    | (etvar G7 K55) => (fun (G8 : Env) (T97 : Ty) (K54 : Kind) (jm56 : (Kinding G8 T97 K54)) =>
      (shift_etvar_Kinding (appendEnv G8 G7) (weakenTy T97 (domainEnv G7)) (weakenKind K54 (domainEnv G7)) (weaken_Kinding G7 G8 T97 K54 jm56) C0 (etvar (appendEnv G8 G7) K55) shift_etvar_here))
  end.
Fixpoint weaken_WfKind (G9 : Env) :
(forall (G10 : Env) (K56 : Kind) (jm57 : (WfKind G10 K56)) ,
  (WfKind (appendEnv G10 G9) (weakenKind K56 (domainEnv G9)))) :=
  match G9 return (forall (G10 : Env) (K56 : Kind) (jm57 : (WfKind G10 K56)) ,
    (WfKind (appendEnv G10 G9) (weakenKind K56 (domainEnv G9)))) with
    | (empty) => (fun (G10 : Env) (K56 : Kind) (jm57 : (WfKind G10 K56)) =>
      jm57)
    | (evar G9 T99) => (fun (G10 : Env) (K56 : Kind) (jm57 : (WfKind G10 K56)) =>
      (shift_evar_WfKind (appendEnv G10 G9) (weakenKind K56 (domainEnv G9)) (weaken_WfKind G9 G10 K56 jm57) C0 (evar (appendEnv G10 G9) T99) shift_evar_here))
    | (etvar G9 K57) => (fun (G10 : Env) (K56 : Kind) (jm57 : (WfKind G10 K56)) =>
      (shift_etvar_WfKind (appendEnv G10 G9) (weakenKind K56 (domainEnv G9)) (weaken_WfKind G9 G10 K56 jm57) C0 (etvar (appendEnv G10 G9) K57) shift_etvar_here))
  end.
Fixpoint KindEq_wf_0 (G : Env) (K58 : Kind) (K59 : Kind) (jm58 : (KindEq G K58 K59)) {struct jm58} :
(wfKind (domainEnv G) K58) :=
  match jm58 in (KindEq _ K58 K59) return (wfKind (domainEnv G) K58) with
    | (QK_Pi K1 K2 T1 T2 jm20 jm21) => (wfKind_kpi (domainEnv G) (TyEq_wf_0 G T1 T2 (star) jm20) (KindEq_wf_0 (evar G T1) K1 K2 jm21))
    | (QK_Refl K jm22) => (WfKind_wf_0 G K jm22)
    | (QK_Sym K1 K2 jm23) => (KindEq_wf_1 G K1 K2 jm23)
    | (QK_Trans K1 K2 K3 jm24 jm25) => (KindEq_wf_0 G K1 K2 jm24)
  end
with KindEq_wf_1 (G : Env) (K58 : Kind) (K59 : Kind) (jm59 : (KindEq G K58 K59)) {struct jm59} :
(wfKind (domainEnv G) K59) :=
  match jm59 in (KindEq _ K58 K59) return (wfKind (domainEnv G) K59) with
    | (QK_Pi K1 K2 T1 T2 jm20 jm21) => (wfKind_kpi (domainEnv G) (TyEq_wf_1 G T1 T2 (star) jm20) (KindEq_wf_1 (evar G T1) K1 K2 jm21))
    | (QK_Refl K jm22) => (WfKind_wf_0 G K jm22)
    | (QK_Sym K1 K2 jm23) => (KindEq_wf_0 G K1 K2 jm23)
    | (QK_Trans K1 K2 K3 jm24 jm25) => (KindEq_wf_1 G K2 K3 jm25)
  end
with TyEq_wf_0 (G : Env) (T100 : Ty) (T101 : Ty) (K60 : Kind) (jm60 : (TyEq G T100 T101 K60)) {struct jm60} :
(wfTy (domainEnv G) T100) :=
  match jm60 in (TyEq _ T100 T101 K60) return (wfTy (domainEnv G) T100) with
    | (QT_Pi S1 S2 T1 T2 jm26 jm27) => (wfTy_tpi (domainEnv G) (TyEq_wf_0 G S1 T1 (star) jm26) (TyEq_wf_0 (evar G T1) S2 T2 (star) jm27))
    | (QT_App K S1 S2 T t1 t2 jm28 jm29) => (wfTy_tapp (domainEnv G) (TyEq_wf_0 G S1 S2 (kpi T K) jm28) (TermEq_wf_0 G t1 t2 T jm29))
    | (QT_Refl K T jm30) => (Kinding_wf_0 G T K jm30)
    | (QT_Symm K S1 T jm31) => (TyEq_wf_1 G T S1 K jm31)
    | (QT_Trans K S1 T U jm32 jm33) => (TyEq_wf_0 G S1 U K jm32)
  end
with TyEq_wf_1 (G : Env) (T100 : Ty) (T101 : Ty) (K60 : Kind) (jm61 : (TyEq G T100 T101 K60)) {struct jm61} :
(wfTy (domainEnv G) T101) :=
  match jm61 in (TyEq _ T100 T101 K60) return (wfTy (domainEnv G) T101) with
    | (QT_Pi S1 S2 T1 T2 jm26 jm27) => (wfTy_tpi (domainEnv G) (TyEq_wf_1 G S1 T1 (star) jm26) (TyEq_wf_1 (evar G T1) S2 T2 (star) jm27))
    | (QT_App K S1 S2 T t1 t2 jm28 jm29) => (wfTy_tapp (domainEnv G) (TyEq_wf_1 G S1 S2 (kpi T K) jm28) (TermEq_wf_1 G t1 t2 T jm29))
    | (QT_Refl K T jm30) => (Kinding_wf_0 G T K jm30)
    | (QT_Symm K S1 T jm31) => (TyEq_wf_0 G T S1 K jm31)
    | (QT_Trans K S1 T U jm32 jm33) => (TyEq_wf_1 G U T K jm33)
  end
with TyEq_wf_2 (G : Env) (T100 : Ty) (T101 : Ty) (K60 : Kind) (jm62 : (TyEq G T100 T101 K60)) {struct jm62} :
(wfKind (domainEnv G) K60) :=
  match jm62 in (TyEq _ T100 T101 K60) return (wfKind (domainEnv G) K60) with
    | (QT_Pi S1 S2 T1 T2 jm26 jm27) => (wfKind_star (domainEnv G))
    | (QT_App K S1 S2 T t1 t2 jm28 jm29) => (substhvl_TmVar_wfKind (TermEq_wf_0 G t1 t2 T jm29) (HS TmVar (domainEnv G)) K (inversion_wfKind_kpi_2 (domainEnv G) T K (TyEq_wf_2 G S1 S2 (kpi T K) jm28)) (substhvl_TmVar_here (domainEnv G)))
    | (QT_Refl K T jm30) => (Kinding_wf_1 G T K jm30)
    | (QT_Symm K S1 T jm31) => (TyEq_wf_2 G T S1 K jm31)
    | (QT_Trans K S1 T U jm32 jm33) => (TyEq_wf_2 G U T K jm33)
  end
with TermEq_wf_0 (G : Env) (t79 : Tm) (t80 : Tm) (T102 : Ty) (jm63 : (TermEq G t79 t80 T102)) {struct jm63} :
(wfTm (domainEnv G) t79) :=
  match jm63 in (TermEq _ t79 t80 T102) return (wfTm (domainEnv G) t79) with
    | (Q_Abs S1 S2 T t1 t2 jm34 jm35) => (wfTm_abs (domainEnv G) (TyEq_wf_0 G S1 S2 (star) jm34) (TermEq_wf_0 (evar G S1) t1 t2 T jm35))
    | (Q_App S1 T s1 s2 t1 t2 jm36 jm37) => (wfTm_app (domainEnv G) (TermEq_wf_0 G t1 s1 (tpi S1 T) jm36) (TermEq_wf_0 G t2 s2 S1 jm37))
    | (Q_Beta S1 T s t jm38 jm39) => (wfTm_app (domainEnv G) (wfTm_abs (domainEnv G) (Typing_wf_1 G s S1 jm39) (Typing_wf_0 (evar G S1) t T jm38)) (Typing_wf_0 G s S1 jm39))
    | (Q_Eta S1 T t jm40) => (wfTm_abs (domainEnv G) (inversion_wfTy_tpi_1 (domainEnv G) S1 T (Typing_wf_1 G t (tpi S1 T) jm40)) (wfTm_app (HS TmVar (domainEnv G)) (weaken_wfTm (HS TmVar H0) (domainEnv G) t (Typing_wf_0 G t (tpi S1 T) jm40)) (wfTm_var (HS TmVar (domainEnv G)) I0 I)))
    | (Q_Proj1 S1 T t1 t2 jm41 jm42 jm43) => (wfTm_prj1 (domainEnv G) (wfTm_pair (domainEnv G) (Typing_wf_0 G t1 S1 jm42) (Typing_wf_0 G t2 (subst_TmVar_Ty X0 t1 T) jm43) (Typing_wf_1 G t1 S1 jm42) (inversion_wfTy_tsig_2 (domainEnv G) S1 T (Kinding_wf_0 G (tsig S1 T) (star) jm41))))
    | (Q_Proj2 S1 T t1 t2 jm44 jm45 jm46) => (wfTm_prj2 (domainEnv G) (wfTm_pair (domainEnv G) (Typing_wf_0 G t1 S1 jm45) (Typing_wf_0 G t2 (subst_TmVar_Ty X0 t1 T) jm46) (Typing_wf_1 G t1 S1 jm45) (inversion_wfTy_tsig_2 (domainEnv G) S1 T (Kinding_wf_0 G (tsig S1 T) (star) jm44))))
    | (Q_SjPair S1 T t jm47) => (wfTm_pair (domainEnv G) (wfTm_prj1 (domainEnv G) (Typing_wf_0 G t (tsig S1 T) jm47)) (wfTm_prj2 (domainEnv G) (Typing_wf_0 G t (tsig S1 T) jm47)) (inversion_wfTy_tsig_1 (domainEnv G) S1 T (Typing_wf_1 G t (tsig S1 T) jm47)) (inversion_wfTy_tsig_2 (domainEnv G) S1 T (Typing_wf_1 G t (tsig S1 T) jm47)))
    | (Q_Refl T t jm48) => (Typing_wf_0 G t T jm48)
    | (Q_Symm T s t jm49) => (TermEq_wf_1 G t s T jm49)
    | (Q_Trans T s t u jm50 jm51) => (TermEq_wf_0 G s u T jm50)
  end
with TermEq_wf_1 (G : Env) (t79 : Tm) (t80 : Tm) (T102 : Ty) (jm64 : (TermEq G t79 t80 T102)) {struct jm64} :
(wfTm (domainEnv G) t80) :=
  match jm64 in (TermEq _ t79 t80 T102) return (wfTm (domainEnv G) t80) with
    | (Q_Abs S1 S2 T t1 t2 jm34 jm35) => (wfTm_abs (domainEnv G) (TyEq_wf_1 G S1 S2 (star) jm34) (TermEq_wf_1 (evar G S1) t1 t2 T jm35))
    | (Q_App S1 T s1 s2 t1 t2 jm36 jm37) => (wfTm_app (domainEnv G) (TermEq_wf_1 G t1 s1 (tpi S1 T) jm36) (TermEq_wf_1 G t2 s2 S1 jm37))
    | (Q_Beta S1 T s t jm38 jm39) => (substhvl_TmVar_wfTm (Typing_wf_0 G s S1 jm39) (HS TmVar (domainEnv G)) t (Typing_wf_0 (evar G S1) t T jm38) (substhvl_TmVar_here (domainEnv G)))
    | (Q_Eta S1 T t jm40) => (Typing_wf_0 G t (tpi S1 T) jm40)
    | (Q_Proj1 S1 T t1 t2 jm41 jm42 jm43) => (Typing_wf_0 G t1 S1 jm42)
    | (Q_Proj2 S1 T t1 t2 jm44 jm45 jm46) => (Typing_wf_0 G t2 (subst_TmVar_Ty X0 t1 T) jm46)
    | (Q_SjPair S1 T t jm47) => (Typing_wf_0 G t (tsig S1 T) jm47)
    | (Q_Refl T t jm48) => (Typing_wf_0 G t T jm48)
    | (Q_Symm T s t jm49) => (TermEq_wf_0 G t s T jm49)
    | (Q_Trans T s t u jm50 jm51) => (TermEq_wf_1 G u t T jm51)
  end
with TermEq_wf_2 (G : Env) (t79 : Tm) (t80 : Tm) (T102 : Ty) (jm65 : (TermEq G t79 t80 T102)) {struct jm65} :
(wfTy (domainEnv G) T102) :=
  match jm65 in (TermEq _ t79 t80 T102) return (wfTy (domainEnv G) T102) with
    | (Q_Abs S1 S2 T t1 t2 jm34 jm35) => (wfTy_tpi (domainEnv G) (TyEq_wf_0 G S1 S2 (star) jm34) (TermEq_wf_2 (evar G S1) t1 t2 T jm35))
    | (Q_App S1 T s1 s2 t1 t2 jm36 jm37) => (substhvl_TmVar_wfTy (TermEq_wf_0 G t2 s2 S1 jm37) (HS TmVar (domainEnv G)) T (inversion_wfTy_tpi_2 (domainEnv G) S1 T (TermEq_wf_2 G t1 s1 (tpi S1 T) jm36)) (substhvl_TmVar_here (domainEnv G)))
    | (Q_Beta S1 T s t jm38 jm39) => (substhvl_TmVar_wfTy (Typing_wf_0 G s S1 jm39) (HS TmVar (domainEnv G)) T (Typing_wf_1 (evar G S1) t T jm38) (substhvl_TmVar_here (domainEnv G)))
    | (Q_Eta S1 T t jm40) => (wfTy_tpi (domainEnv G) (inversion_wfTy_tpi_1 (domainEnv G) S1 T (Typing_wf_1 G t (tpi S1 T) jm40)) (inversion_wfTy_tpi_2 (domainEnv G) S1 T (Typing_wf_1 G t (tpi S1 T) jm40)))
    | (Q_Proj1 S1 T t1 t2 jm41 jm42 jm43) => (Typing_wf_1 G t1 S1 jm42)
    | (Q_Proj2 S1 T t1 t2 jm44 jm45 jm46) => (substhvl_TmVar_wfTy (Typing_wf_0 G t1 S1 jm45) (HS TmVar (domainEnv G)) T (inversion_wfTy_tsig_2 (domainEnv G) S1 T (Kinding_wf_0 G (tsig S1 T) (star) jm44)) (substhvl_TmVar_here (domainEnv G)))
    | (Q_SjPair S1 T t jm47) => (wfTy_tsig (domainEnv G) (inversion_wfTy_tsig_1 (domainEnv G) S1 T (Typing_wf_1 G t (tsig S1 T) jm47)) (inversion_wfTy_tsig_2 (domainEnv G) S1 T (Typing_wf_1 G t (tsig S1 T) jm47)))
    | (Q_Refl T t jm48) => (Typing_wf_1 G t T jm48)
    | (Q_Symm T s t jm49) => (TermEq_wf_2 G t s T jm49)
    | (Q_Trans T s t u jm50 jm51) => (TermEq_wf_2 G u t T jm51)
  end
with Typing_wf_0 (G : Env) (t81 : Tm) (T103 : Ty) (jm66 : (Typing G t81 T103)) {struct jm66} :
(wfTm (domainEnv G) t81) :=
  match jm66 in (Typing _ t81 T103) return (wfTm (domainEnv G) t81) with
    | (T_Var T x lk1 H25 H26) => (wfTm_var (domainEnv G) _ H26)
    | (T_Abs S1 T t jm9 jm10) => (wfTm_abs (domainEnv G) (Kinding_wf_0 G S1 (star) jm9) (Typing_wf_0 (evar G S1) t T jm10))
    | (T_App S1 T t1 t2 jm11 jm12) => (wfTm_app (domainEnv G) (Typing_wf_0 G t1 (tpi S1 T) jm11) (Typing_wf_0 G t2 S1 jm12))
    | (T_Pair S1 T t1 t2 jm13 jm14 jm15) => (wfTm_pair (domainEnv G) (Typing_wf_0 G t1 S1 jm14) (Typing_wf_0 G t2 (subst_TmVar_Ty X0 t1 T) jm15) (Typing_wf_1 G t1 S1 jm14) (inversion_wfTy_tsig_2 (domainEnv G) S1 T (Kinding_wf_0 G (tsig S1 T) (star) jm13)))
    | (T_Proj1 S1 T t jm16) => (wfTm_prj1 (domainEnv G) (Typing_wf_0 G t (tsig S1 T) jm16))
    | (T_Proj2 S1 T t jm17) => (wfTm_prj2 (domainEnv G) (Typing_wf_0 G t (tsig S1 T) jm17))
    | (T_Conv T1 T2 t jm18 jm19) => (Typing_wf_0 G t T1 jm18)
  end
with Typing_wf_1 (G : Env) (t81 : Tm) (T103 : Ty) (jm67 : (Typing G t81 T103)) {struct jm67} :
(wfTy (domainEnv G) T103) :=
  match jm67 in (Typing _ t81 T103) return (wfTy (domainEnv G) T103) with
    | (T_Var T x lk2 H25 H26) => H25
    | (T_Abs S1 T t jm9 jm10) => (wfTy_tpi (domainEnv G) (Kinding_wf_0 G S1 (star) jm9) (Typing_wf_1 (evar G S1) t T jm10))
    | (T_App S1 T t1 t2 jm11 jm12) => (substhvl_TmVar_wfTy (Typing_wf_0 G t2 S1 jm12) (HS TmVar (domainEnv G)) T (inversion_wfTy_tpi_2 (domainEnv G) S1 T (Typing_wf_1 G t1 (tpi S1 T) jm11)) (substhvl_TmVar_here (domainEnv G)))
    | (T_Pair S1 T t1 t2 jm13 jm14 jm15) => (wfTy_tsig (domainEnv G) (Typing_wf_1 G t1 S1 jm14) (inversion_wfTy_tsig_2 (domainEnv G) S1 T (Kinding_wf_0 G (tsig S1 T) (star) jm13)))
    | (T_Proj1 S1 T t jm16) => (inversion_wfTy_tsig_1 (domainEnv G) S1 T (Typing_wf_1 G t (tsig S1 T) jm16))
    | (T_Proj2 S1 T t jm17) => (substhvl_TmVar_wfTy (wfTm_prj1 (domainEnv G) (Typing_wf_0 G t (tsig S1 T) jm17)) (HS TmVar (domainEnv G)) T (inversion_wfTy_tsig_2 (domainEnv G) S1 T (Typing_wf_1 G t (tsig S1 T) jm17)) (substhvl_TmVar_here (domainEnv G)))
    | (T_Conv T1 T2 t jm18 jm19) => (TyEq_wf_1 G T1 T2 (star) jm19)
  end
with Kinding_wf_0 (G : Env) (T104 : Ty) (K61 : Kind) (jm68 : (Kinding G T104 K61)) {struct jm68} :
(wfTy (domainEnv G) T104) :=
  match jm68 in (Kinding _ T104 K61) return (wfTy (domainEnv G) T104) with
    | (K_TVar K X lk3 H25 H26) => (wfTy_tvar (domainEnv G) _ H26)
    | (K_Pi T1 T2 jm1 jm2) => (wfTy_tpi (domainEnv G) (Kinding_wf_0 G T1 (star) jm1) (Kinding_wf_0 (evar G T1) T2 (star) jm2))
    | (K_App K S1 T t jm3 jm4) => (wfTy_tapp (domainEnv G) (Kinding_wf_0 G S1 (kpi T K) jm3) (Typing_wf_0 G t T jm4))
    | (K_Sigma S1 T jm5 jm6) => (wfTy_tsig (domainEnv G) (Kinding_wf_0 G S1 (star) jm5) (Kinding_wf_0 (evar G S1) T (star) jm6))
    | (K_Conv K1 K2 T jm7 jm8) => (Kinding_wf_0 G T K1 jm7)
  end
with Kinding_wf_1 (G : Env) (T104 : Ty) (K61 : Kind) (jm69 : (Kinding G T104 K61)) {struct jm69} :
(wfKind (domainEnv G) K61) :=
  match jm69 in (Kinding _ T104 K61) return (wfKind (domainEnv G) K61) with
    | (K_TVar K X lk4 H25 H26) => H25
    | (K_Pi T1 T2 jm1 jm2) => (wfKind_star (domainEnv G))
    | (K_App K S1 T t jm3 jm4) => (substhvl_TmVar_wfKind (Typing_wf_0 G t T jm4) (HS TmVar (domainEnv G)) K (inversion_wfKind_kpi_2 (domainEnv G) T K (Kinding_wf_1 G S1 (kpi T K) jm3)) (substhvl_TmVar_here (domainEnv G)))
    | (K_Sigma S1 T jm5 jm6) => (wfKind_star (domainEnv G))
    | (K_Conv K1 K2 T jm7 jm8) => (KindEq_wf_1 G K1 K2 jm8)
  end
with WfKind_wf_0 (G : Env) (K62 : Kind) (jm70 : (WfKind G K62)) {struct jm70} :
(wfKind (domainEnv G) K62) :=
  match jm70 in (WfKind _ K62) return (wfKind (domainEnv G) K62) with
    | (WfStar) => (wfKind_star (domainEnv G))
    | (WfPi K T jm jm0) => (wfKind_kpi (domainEnv G) (Kinding_wf_0 G T (star) jm) (weaken_wfKind (HS TmVar H0) (domainEnv G) K (WfKind_wf_0 G K jm0)))
  end.
 Hint Extern 8 => match goal with
  | H79 : (KindEq _ _ _) |- _ => pose proof ((KindEq_wf_0 _ _ _ H79)); pose proof ((KindEq_wf_1 _ _ _ H79)); clear H79
end : wf.
 Hint Extern 8 => match goal with
  | H80 : (TyEq _ _ _ _) |- _ => pose proof ((TyEq_wf_0 _ _ _ _ H80)); pose proof ((TyEq_wf_1 _ _ _ _ H80)); pose proof ((TyEq_wf_2 _ _ _ _ H80)); clear H80
end : wf.
 Hint Extern 8 => match goal with
  | H81 : (TermEq _ _ _ _) |- _ => pose proof ((TermEq_wf_0 _ _ _ _ H81)); pose proof ((TermEq_wf_1 _ _ _ _ H81)); pose proof ((TermEq_wf_2 _ _ _ _ H81)); clear H81
end : wf.
 Hint Extern 8 => match goal with
  | H82 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H82)); pose proof ((Typing_wf_1 _ _ _ H82)); clear H82
end : wf.
 Hint Extern 8 => match goal with
  | H83 : (Kinding _ _ _) |- _ => pose proof ((Kinding_wf_0 _ _ _ H83)); pose proof ((Kinding_wf_1 _ _ _ H83)); clear H83
end : wf.
 Hint Extern 8 => match goal with
  | H84 : (WfKind _ _) |- _ => pose proof ((WfKind_wf_0 _ _ H84)); clear H84
end : wf.
Lemma subst_evar_lookup_evar (G11 : Env) (s17 : Tm) (T105 : Ty) (jm71 : (Typing G11 s17 T105)) :
  (forall (d : (Trace TmVar)) (G12 : Env) (G14 : Env) (sub : (subst_evar G11 T105 s17 d G12 G14)) (x72 : (Index TmVar)) (T106 : Ty) ,
    (lookup_evar G12 x72 T106) -> (Typing G14 (subst_TmVar_Index d s17 x72) (subst_TmVar_Ty d s17 T106))).
Proof.
  needleGenericSubstEnvLookupHom (T_Var).
Qed.
Lemma subst_etvar_lookup_etvar (G11 : Env) (S59 : Ty) (K63 : Kind) (jm71 : (Kinding G11 S59 K63)) :
  (forall (d : (Trace TyVar)) (G12 : Env) (G14 : Env) (sub : (subst_etvar G11 K63 S59 d G12 G14)) (X11 : (Index TyVar)) (K64 : Kind) ,
    (lookup_etvar G12 X11 K64) -> (Kinding G14 (subst_TyVar_Index d S59 X11) (subst_TyVar_Kind d S59 K64))).
Proof.
  needleGenericSubstEnvLookupHom (K_TVar).
Qed.
Fixpoint subst_evar_KindEq (G12 : Env) (s17 : Tm) (T105 : Ty) (jm77 : (Typing G12 s17 T105)) (G11 : Env) (K1 : Kind) (K2 : Kind) (jm78 : (KindEq G11 K1 K2)) :
(forall (G13 : Env) (d : (Trace TmVar)) (H96 : (subst_evar G12 T105 s17 d G11 G13)) ,
  (KindEq G13 (subst_TmVar_Kind d s17 K1) (subst_TmVar_Kind d s17 K2))) :=
  match jm78 in (KindEq _ K1 K2) return (forall (G13 : Env) (d : (Trace TmVar)) (H96 : (subst_evar G12 T105 s17 d G11 G13)) ,
    (KindEq G13 (subst_TmVar_Kind d s17 K1) (subst_TmVar_Kind d s17 K2))) with
    | (QK_Pi K64 K65 T106 T107 jm71 jm72) => (fun (G13 : Env) (d : (Trace TmVar)) (H96 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (QK_Pi G13 (subst_TmVar_Kind (weakenTrace d (HS TmVar H0)) s17 K64) (subst_TmVar_Kind (weakenTrace d (HS TmVar H0)) s17 K65) (subst_TmVar_Ty (weakenTrace d H0) s17 T106) (subst_TmVar_Ty (weakenTrace d H0) s17 T107) (subst_evar_TyEq G12 s17 T105 jm77 G11 T106 T107 (star) jm71 G13 d (weaken_subst_evar _ empty H96)) (subst_evar_KindEq G12 s17 T105 jm77 (evar G11 T106) K64 K65 jm72 (appendEnv G13 (subst_TmVar_Env d s17 (evar empty T106))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty T106) H96))))
    | (QK_Refl K63 jm73) => (fun (G13 : Env) (d : (Trace TmVar)) (H96 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (QK_Refl G13 (subst_TmVar_Kind (weakenTrace d H0) s17 K63) (subst_evar_WfKind G12 s17 T105 jm77 G11 K63 jm73 G13 d (weaken_subst_evar _ empty H96))))
    | (QK_Sym K64 K65 jm74) => (fun (G13 : Env) (d : (Trace TmVar)) (H96 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (QK_Sym G13 (subst_TmVar_Kind (weakenTrace d H0) s17 K64) (subst_TmVar_Kind (weakenTrace d H0) s17 K65) (subst_evar_KindEq G12 s17 T105 jm77 G11 K64 K65 jm74 G13 d (weaken_subst_evar _ empty H96))))
    | (QK_Trans K64 K65 K66 jm75 jm76) => (fun (G13 : Env) (d : (Trace TmVar)) (H96 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (QK_Trans G13 (subst_TmVar_Kind (weakenTrace d H0) s17 K64) (subst_TmVar_Kind (weakenTrace d H0) s17 K65) (subst_TmVar_Kind (weakenTrace d H0) s17 K66) (subst_evar_KindEq G12 s17 T105 jm77 G11 K64 K65 jm75 G13 d (weaken_subst_evar _ empty H96)) (subst_evar_KindEq G12 s17 T105 jm77 G11 K65 K66 jm76 G13 d (weaken_subst_evar _ empty H96))))
  end
with subst_evar_TyEq (G12 : Env) (s17 : Tm) (T105 : Ty) (jm79 : (Typing G12 s17 T105)) (G11 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm80 : (TyEq G11 T1 T2 K)) :
(forall (G13 : Env) (d : (Trace TmVar)) (H105 : (subst_evar G12 T105 s17 d G11 G13)) ,
  (TyEq G13 (subst_TmVar_Ty d s17 T1) (subst_TmVar_Ty d s17 T2) (subst_TmVar_Kind d s17 K))) :=
  match jm80 in (TyEq _ T1 T2 K) return (forall (G13 : Env) (d : (Trace TmVar)) (H105 : (subst_evar G12 T105 s17 d G11 G13)) ,
    (TyEq G13 (subst_TmVar_Ty d s17 T1) (subst_TmVar_Ty d s17 T2) (subst_TmVar_Kind d s17 K))) with
    | (QT_Pi S59 S60 T107 T108 jm71 jm72) => (fun (G13 : Env) (d : (Trace TmVar)) (H105 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (QT_Pi G13 (subst_TmVar_Ty (weakenTrace d H0) s17 S59) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s17 S60) (subst_TmVar_Ty (weakenTrace d H0) s17 T107) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s17 T108) (subst_evar_TyEq G12 s17 T105 jm79 G11 S59 T107 (star) jm71 G13 d (weaken_subst_evar _ empty H105)) (subst_evar_TyEq G12 s17 T105 jm79 (evar G11 T107) S60 T108 (star) jm72 (appendEnv G13 (subst_TmVar_Env d s17 (evar empty T107))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty T107) H105))))
    | (QT_App K63 S59 S60 T106 t82 t83 jm73 jm74) => (fun (G13 : Env) (d : (Trace TmVar)) (H105 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (TyEq_cast G13 _ _ _ G13 (subst_TmVar_Ty d s17 (tapp S59 t82)) (subst_TmVar_Ty d s17 (tapp S60 t83)) (subst_TmVar_Kind d s17 (subst_TmVar_Kind X0 t82 K63)) eq_refl eq_refl eq_refl (eq_sym (subst_TmVar_Kind_subst_TmVar_Kind0_comm K63 d s17 t82)) (QT_App G13 (subst_TmVar_Kind (weakenTrace d (HS TmVar H0)) s17 K63) (subst_TmVar_Ty (weakenTrace d H0) s17 S59) (subst_TmVar_Ty (weakenTrace d H0) s17 S60) (subst_TmVar_Ty (weakenTrace d H0) s17 T106) (subst_TmVar_Tm (weakenTrace d H0) s17 t82) (subst_TmVar_Tm (weakenTrace d H0) s17 t83) (subst_evar_TyEq G12 s17 T105 jm79 G11 S59 S60 (kpi T106 K63) jm73 G13 d (weaken_subst_evar _ empty H105)) (subst_evar_TermEq G12 s17 T105 jm79 G11 t82 t83 T106 jm74 G13 d (weaken_subst_evar _ empty H105)))))
    | (QT_Refl K63 T106 jm75) => (fun (G13 : Env) (d : (Trace TmVar)) (H105 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (QT_Refl G13 (subst_TmVar_Kind (weakenTrace d H0) s17 K63) (subst_TmVar_Ty (weakenTrace d H0) s17 T106) (subst_evar_Kinding G12 s17 T105 jm79 G11 T106 K63 jm75 G13 d (weaken_subst_evar _ empty H105))))
    | (QT_Symm K63 S59 T106 jm76) => (fun (G13 : Env) (d : (Trace TmVar)) (H105 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (QT_Symm G13 (subst_TmVar_Kind (weakenTrace d H0) s17 K63) (subst_TmVar_Ty (weakenTrace d H0) s17 S59) (subst_TmVar_Ty (weakenTrace d H0) s17 T106) (subst_evar_TyEq G12 s17 T105 jm79 G11 T106 S59 K63 jm76 G13 d (weaken_subst_evar _ empty H105))))
    | (QT_Trans K63 S59 T106 U2 jm77 jm78) => (fun (G13 : Env) (d : (Trace TmVar)) (H105 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (QT_Trans G13 (subst_TmVar_Kind (weakenTrace d H0) s17 K63) (subst_TmVar_Ty (weakenTrace d H0) s17 S59) (subst_TmVar_Ty (weakenTrace d H0) s17 T106) (subst_TmVar_Ty (weakenTrace d H0) s17 U2) (subst_evar_TyEq G12 s17 T105 jm79 G11 S59 U2 K63 jm77 G13 d (weaken_subst_evar _ empty H105)) (subst_evar_TyEq G12 s17 T105 jm79 G11 U2 T106 K63 jm78 G13 d (weaken_subst_evar _ empty H105))))
  end
with subst_evar_TermEq (G12 : Env) (s20 : Tm) (T105 : Ty) (jm89 : (Typing G12 s20 T105)) (G11 : Env) (t1 : Tm) (t2 : Tm) (T : Ty) (jm90 : (TermEq G11 t1 t2 T)) :
(forall (G13 : Env) (d : (Trace TmVar)) (H124 : (subst_evar G12 T105 s20 d G11 G13)) ,
  (TermEq G13 (subst_TmVar_Tm d s20 t1) (subst_TmVar_Tm d s20 t2) (subst_TmVar_Ty d s20 T))) :=
  match jm90 in (TermEq _ t1 t2 T) return (forall (G13 : Env) (d : (Trace TmVar)) (H124 : (subst_evar G12 T105 s20 d G11 G13)) ,
    (TermEq G13 (subst_TmVar_Tm d s20 t1) (subst_TmVar_Tm d s20 t2) (subst_TmVar_Ty d s20 T))) with
    | (Q_Abs S59 S60 T106 t83 t84 jm71 jm72) => (fun (G13 : Env) (d : (Trace TmVar)) (H124 : (subst_evar G12 T105 s20 d G11 G13)) =>
      (Q_Abs G13 (subst_TmVar_Ty (weakenTrace d H0) s20 S59) (subst_TmVar_Ty (weakenTrace d H0) s20 S60) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s20 T106) (subst_TmVar_Tm (weakenTrace d (HS TmVar H0)) s20 t83) (subst_TmVar_Tm (weakenTrace d (HS TmVar H0)) s20 t84) (subst_evar_TyEq G12 s20 T105 jm89 G11 S59 S60 (star) jm71 G13 d (weaken_subst_evar _ empty H124)) (subst_evar_TermEq G12 s20 T105 jm89 (evar G11 S59) t83 t84 T106 jm72 (appendEnv G13 (subst_TmVar_Env d s20 (evar empty S59))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty S59) H124))))
    | (Q_App S59 T106 s18 s19 t83 t84 jm73 jm74) => (fun (G13 : Env) (d : (Trace TmVar)) (H124 : (subst_evar G12 T105 s20 d G11 G13)) =>
      (TermEq_cast G13 _ _ _ G13 (subst_TmVar_Tm d s20 (app t83 t84)) (subst_TmVar_Tm d s20 (app s18 s19)) (subst_TmVar_Ty d s20 (subst_TmVar_Ty X0 t84 T106)) eq_refl eq_refl eq_refl (eq_sym (subst_TmVar_Ty_subst_TmVar_Ty0_comm T106 d s20 t84)) (Q_App G13 (subst_TmVar_Ty (weakenTrace d H0) s20 S59) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s20 T106) (subst_TmVar_Tm (weakenTrace d H0) s20 s18) (subst_TmVar_Tm (weakenTrace d H0) s20 s19) (subst_TmVar_Tm (weakenTrace d H0) s20 t83) (subst_TmVar_Tm (weakenTrace d H0) s20 t84) (subst_evar_TermEq G12 s20 T105 jm89 G11 t83 s18 (tpi S59 T106) jm73 G13 d (weaken_subst_evar _ empty H124)) (subst_evar_TermEq G12 s20 T105 jm89 G11 t84 s19 S59 jm74 G13 d (weaken_subst_evar _ empty H124)))))
    | (Q_Beta S59 T106 s17 t82 jm75 jm76) => (fun (G13 : Env) (d : (Trace TmVar)) (H124 : (subst_evar G12 T105 s20 d G11 G13)) =>
      (TermEq_cast G13 _ _ _ G13 (subst_TmVar_Tm d s20 (app (abs S59 t82) s17)) (subst_TmVar_Tm d s20 (subst_TmVar_Tm X0 s17 t82)) (subst_TmVar_Ty d s20 (subst_TmVar_Ty X0 s17 T106)) eq_refl eq_refl (eq_sym (subst_TmVar_Tm_subst_TmVar_Tm0_comm t82 d s20 s17)) (eq_sym (subst_TmVar_Ty_subst_TmVar_Ty0_comm T106 d s20 s17)) (Q_Beta G13 (subst_TmVar_Ty (weakenTrace d H0) s20 S59) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s20 T106) (subst_TmVar_Tm (weakenTrace d H0) s20 s17) (subst_TmVar_Tm (weakenTrace d (HS TmVar H0)) s20 t82) (subst_evar_Typing G12 s20 T105 jm89 (evar G11 S59) t82 T106 jm75 (appendEnv G13 (subst_TmVar_Env d s20 (evar empty S59))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty S59) H124)) (subst_evar_Typing G12 s20 T105 jm89 G11 s17 S59 jm76 G13 d (weaken_subst_evar _ empty H124)))))
    | (Q_Eta S59 T106 t82 jm77) => (fun (G13 : Env) (d : (Trace TmVar)) (H124 : (subst_evar G12 T105 s20 d G11 G13)) =>
      (TermEq_cast G13 _ _ _ G13 (subst_TmVar_Tm d s20 (abs S59 (app (weakenTm t82 (HS TmVar H0)) (var I0)))) (subst_TmVar_Tm d s20 t82) (subst_TmVar_Ty d s20 (tpi S59 T106)) eq_refl (f_equal2 abs eq_refl (f_equal2 app (weakenTm_subst_TmVar_Tm (HS TmVar H0) d s20 t82) eq_refl)) eq_refl eq_refl (Q_Eta G13 (subst_TmVar_Ty (weakenTrace d H0) s20 S59) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s20 T106) (subst_TmVar_Tm (weakenTrace d H0) s20 t82) (subst_evar_Typing G12 s20 T105 jm89 G11 t82 (tpi S59 T106) jm77 G13 d (weaken_subst_evar _ empty H124)))))
    | (Q_Proj1 S59 T106 t83 t84 jm78 jm79 jm80) => (fun (G13 : Env) (d : (Trace TmVar)) (H124 : (subst_evar G12 T105 s20 d G11 G13)) =>
      (Q_Proj1 G13 (subst_TmVar_Ty (weakenTrace d H0) s20 S59) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s20 T106) (subst_TmVar_Tm (weakenTrace d H0) s20 t83) (subst_TmVar_Tm (weakenTrace d H0) s20 t84) (subst_evar_Kinding G12 s20 T105 jm89 G11 (tsig S59 T106) (star) jm78 G13 d (weaken_subst_evar _ empty H124)) (subst_evar_Typing G12 s20 T105 jm89 G11 t83 S59 jm79 G13 d (weaken_subst_evar _ empty H124)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (subst_TmVar_Ty_subst_TmVar_Ty0_comm T106 d s20 t83) (subst_evar_Typing G12 s20 T105 jm89 G11 t84 (subst_TmVar_Ty X0 t83 T106) jm80 G13 d (weaken_subst_evar _ empty H124)))))
    | (Q_Proj2 S59 T106 t83 t84 jm81 jm82 jm83) => (fun (G13 : Env) (d : (Trace TmVar)) (H124 : (subst_evar G12 T105 s20 d G11 G13)) =>
      (TermEq_cast G13 _ _ _ G13 (subst_TmVar_Tm d s20 (prj2 (pair t83 t84 S59 T106))) (subst_TmVar_Tm d s20 t84) (subst_TmVar_Ty d s20 (subst_TmVar_Ty X0 t83 T106)) eq_refl eq_refl eq_refl (eq_sym (subst_TmVar_Ty_subst_TmVar_Ty0_comm T106 d s20 t83)) (Q_Proj2 G13 (subst_TmVar_Ty (weakenTrace d H0) s20 S59) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s20 T106) (subst_TmVar_Tm (weakenTrace d H0) s20 t83) (subst_TmVar_Tm (weakenTrace d H0) s20 t84) (subst_evar_Kinding G12 s20 T105 jm89 G11 (tsig S59 T106) (star) jm81 G13 d (weaken_subst_evar _ empty H124)) (subst_evar_Typing G12 s20 T105 jm89 G11 t83 S59 jm82 G13 d (weaken_subst_evar _ empty H124)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (subst_TmVar_Ty_subst_TmVar_Ty0_comm T106 d s20 t83) (subst_evar_Typing G12 s20 T105 jm89 G11 t84 (subst_TmVar_Ty X0 t83 T106) jm83 G13 d (weaken_subst_evar _ empty H124))))))
    | (Q_SjPair S59 T106 t82 jm84) => (fun (G13 : Env) (d : (Trace TmVar)) (H124 : (subst_evar G12 T105 s20 d G11 G13)) =>
      (Q_SjPair G13 (subst_TmVar_Ty (weakenTrace d H0) s20 S59) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s20 T106) (subst_TmVar_Tm (weakenTrace d H0) s20 t82) (subst_evar_Typing G12 s20 T105 jm89 G11 t82 (tsig S59 T106) jm84 G13 d (weaken_subst_evar _ empty H124))))
    | (Q_Refl T106 t82 jm85) => (fun (G13 : Env) (d : (Trace TmVar)) (H124 : (subst_evar G12 T105 s20 d G11 G13)) =>
      (Q_Refl G13 (subst_TmVar_Ty (weakenTrace d H0) s20 T106) (subst_TmVar_Tm (weakenTrace d H0) s20 t82) (subst_evar_Typing G12 s20 T105 jm89 G11 t82 T106 jm85 G13 d (weaken_subst_evar _ empty H124))))
    | (Q_Symm T106 s17 t82 jm86) => (fun (G13 : Env) (d : (Trace TmVar)) (H124 : (subst_evar G12 T105 s20 d G11 G13)) =>
      (Q_Symm G13 (subst_TmVar_Ty (weakenTrace d H0) s20 T106) (subst_TmVar_Tm (weakenTrace d H0) s20 s17) (subst_TmVar_Tm (weakenTrace d H0) s20 t82) (subst_evar_TermEq G12 s20 T105 jm89 G11 t82 s17 T106 jm86 G13 d (weaken_subst_evar _ empty H124))))
    | (Q_Trans T106 s17 t82 u1 jm87 jm88) => (fun (G13 : Env) (d : (Trace TmVar)) (H124 : (subst_evar G12 T105 s20 d G11 G13)) =>
      (Q_Trans G13 (subst_TmVar_Ty (weakenTrace d H0) s20 T106) (subst_TmVar_Tm (weakenTrace d H0) s20 s17) (subst_TmVar_Tm (weakenTrace d H0) s20 t82) (subst_TmVar_Tm (weakenTrace d H0) s20 u1) (subst_evar_TermEq G12 s20 T105 jm89 G11 s17 u1 T106 jm87 G13 d (weaken_subst_evar _ empty H124)) (subst_evar_TermEq G12 s20 T105 jm89 G11 u1 t82 T106 jm88 G13 d (weaken_subst_evar _ empty H124))))
  end
with subst_evar_Typing (G12 : Env) (s17 : Tm) (T105 : Ty) (jm82 : (Typing G12 s17 T105)) (G11 : Env) (t : Tm) (T : Ty) (jm83 : (Typing G11 t T)) :
(forall (G13 : Env) (d : (Trace TmVar)) (H108 : (subst_evar G12 T105 s17 d G11 G13)) ,
  (Typing G13 (subst_TmVar_Tm d s17 t) (subst_TmVar_Ty d s17 T))) :=
  match jm83 in (Typing _ t T) return (forall (G13 : Env) (d : (Trace TmVar)) (H108 : (subst_evar G12 T105 s17 d G11 G13)) ,
    (Typing G13 (subst_TmVar_Tm d s17 t) (subst_TmVar_Ty d s17 T))) with
    | (T_Var T106 x72 lk5 H86 H87) => (fun (G13 : Env) (d : (Trace TmVar)) (H108 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (subst_evar_lookup_evar G12 s17 T105 jm82 d G11 G13 H108 x72 T106 lk5))
    | (T_Abs S59 T106 t82 jm81 jm71) => (fun (G13 : Env) (d : (Trace TmVar)) (H108 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (T_Abs G13 (subst_TmVar_Ty (weakenTrace d H0) s17 S59) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s17 T106) (subst_TmVar_Tm (weakenTrace d (HS TmVar H0)) s17 t82) (subst_evar_Kinding G12 s17 T105 jm82 G11 S59 (star) jm81 G13 d (weaken_subst_evar _ empty H108)) (subst_evar_Typing G12 s17 T105 jm82 (evar G11 S59) t82 T106 jm71 (appendEnv G13 (subst_TmVar_Env d s17 (evar empty S59))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty S59) H108))))
    | (T_App S59 T106 t83 t84 jm72 jm73) => (fun (G13 : Env) (d : (Trace TmVar)) (H108 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (Typing_cast G13 _ _ G13 (subst_TmVar_Tm d s17 (app t83 t84)) (subst_TmVar_Ty d s17 (subst_TmVar_Ty X0 t84 T106)) eq_refl eq_refl (eq_sym (subst_TmVar_Ty_subst_TmVar_Ty0_comm T106 d s17 t84)) (T_App G13 (subst_TmVar_Ty (weakenTrace d H0) s17 S59) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s17 T106) (subst_TmVar_Tm (weakenTrace d H0) s17 t83) (subst_TmVar_Tm (weakenTrace d H0) s17 t84) (subst_evar_Typing G12 s17 T105 jm82 G11 t83 (tpi S59 T106) jm72 G13 d (weaken_subst_evar _ empty H108)) (subst_evar_Typing G12 s17 T105 jm82 G11 t84 S59 jm73 G13 d (weaken_subst_evar _ empty H108)))))
    | (T_Pair S59 T106 t83 t84 jm74 jm75 jm76) => (fun (G13 : Env) (d : (Trace TmVar)) (H108 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (T_Pair G13 (subst_TmVar_Ty (weakenTrace d H0) s17 S59) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s17 T106) (subst_TmVar_Tm (weakenTrace d H0) s17 t83) (subst_TmVar_Tm (weakenTrace d H0) s17 t84) (subst_evar_Kinding G12 s17 T105 jm82 G11 (tsig S59 T106) (star) jm74 G13 d (weaken_subst_evar _ empty H108)) (subst_evar_Typing G12 s17 T105 jm82 G11 t83 S59 jm75 G13 d (weaken_subst_evar _ empty H108)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (subst_TmVar_Ty_subst_TmVar_Ty0_comm T106 d s17 t83) (subst_evar_Typing G12 s17 T105 jm82 G11 t84 (subst_TmVar_Ty X0 t83 T106) jm76 G13 d (weaken_subst_evar _ empty H108)))))
    | (T_Proj1 S59 T106 t82 jm77) => (fun (G13 : Env) (d : (Trace TmVar)) (H108 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (T_Proj1 G13 (subst_TmVar_Ty (weakenTrace d H0) s17 S59) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s17 T106) (subst_TmVar_Tm (weakenTrace d H0) s17 t82) (subst_evar_Typing G12 s17 T105 jm82 G11 t82 (tsig S59 T106) jm77 G13 d (weaken_subst_evar _ empty H108))))
    | (T_Proj2 S59 T106 t82 jm78) => (fun (G13 : Env) (d : (Trace TmVar)) (H108 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (Typing_cast G13 _ _ G13 (subst_TmVar_Tm d s17 (prj2 t82)) (subst_TmVar_Ty d s17 (subst_TmVar_Ty X0 (prj1 t82) T106)) eq_refl eq_refl (eq_sym (subst_TmVar_Ty_subst_TmVar_Ty0_comm T106 d s17 (prj1 t82))) (T_Proj2 G13 (subst_TmVar_Ty (weakenTrace d H0) s17 S59) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s17 T106) (subst_TmVar_Tm (weakenTrace d H0) s17 t82) (subst_evar_Typing G12 s17 T105 jm82 G11 t82 (tsig S59 T106) jm78 G13 d (weaken_subst_evar _ empty H108)))))
    | (T_Conv T107 T108 t82 jm79 jm80) => (fun (G13 : Env) (d : (Trace TmVar)) (H108 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (T_Conv G13 (subst_TmVar_Ty (weakenTrace d H0) s17 T107) (subst_TmVar_Ty (weakenTrace d H0) s17 T108) (subst_TmVar_Tm (weakenTrace d H0) s17 t82) (subst_evar_Typing G12 s17 T105 jm82 G11 t82 T107 jm79 G13 d (weaken_subst_evar _ empty H108)) (subst_evar_TyEq G12 s17 T105 jm82 G11 T107 T108 (star) jm80 G13 d (weaken_subst_evar _ empty H108))))
  end
with subst_evar_Kinding (G12 : Env) (s17 : Tm) (T105 : Ty) (jm79 : (Typing G12 s17 T105)) (G11 : Env) (T : Ty) (K : Kind) (jm80 : (Kinding G11 T K)) :
(forall (G13 : Env) (d : (Trace TmVar)) (H99 : (subst_evar G12 T105 s17 d G11 G13)) ,
  (Kinding G13 (subst_TmVar_Ty d s17 T) (subst_TmVar_Kind d s17 K))) :=
  match jm80 in (Kinding _ T K) return (forall (G13 : Env) (d : (Trace TmVar)) (H99 : (subst_evar G12 T105 s17 d G11 G13)) ,
    (Kinding G13 (subst_TmVar_Ty d s17 T) (subst_TmVar_Kind d s17 K))) with
    | (K_TVar K63 X11 lk5 H86 H87) => (fun (G13 : Env) (d : (Trace TmVar)) (H99 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (K_TVar G13 (subst_TmVar_Kind (weakenTrace d H0) s17 K63) X11 (subst_evar_lookup_etvar T105 (Typing_wf_0 G12 s17 T105 jm79) H99 K63 lk5) (substhvl_TmVar_wfKind (Typing_wf_0 G12 s17 T105 jm79) _ _ H86 (weaken_substhvl_TmVar H0 (subst_evar_substhvl_TmVar _ H99))) (substhvl_TmVar_wfindex_TyVar (weaken_substhvl_TmVar H0 (subst_evar_substhvl_TmVar _ H99)) H87)))
    | (K_Pi T107 T108 jm71 jm72) => (fun (G13 : Env) (d : (Trace TmVar)) (H99 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (K_Pi G13 (subst_TmVar_Ty (weakenTrace d H0) s17 T107) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s17 T108) (subst_evar_Kinding G12 s17 T105 jm79 G11 T107 (star) jm71 G13 d (weaken_subst_evar _ empty H99)) (subst_evar_Kinding G12 s17 T105 jm79 (evar G11 T107) T108 (star) jm72 (appendEnv G13 (subst_TmVar_Env d s17 (evar empty T107))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty T107) H99))))
    | (K_App K63 S59 T106 t82 jm73 jm74) => (fun (G13 : Env) (d : (Trace TmVar)) (H99 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (Kinding_cast G13 _ _ G13 (subst_TmVar_Ty d s17 (tapp S59 t82)) (subst_TmVar_Kind d s17 (subst_TmVar_Kind X0 t82 K63)) eq_refl eq_refl (eq_sym (subst_TmVar_Kind_subst_TmVar_Kind0_comm K63 d s17 t82)) (K_App G13 (subst_TmVar_Kind (weakenTrace d (HS TmVar H0)) s17 K63) (subst_TmVar_Ty (weakenTrace d H0) s17 S59) (subst_TmVar_Ty (weakenTrace d H0) s17 T106) (subst_TmVar_Tm (weakenTrace d H0) s17 t82) (subst_evar_Kinding G12 s17 T105 jm79 G11 S59 (kpi T106 K63) jm73 G13 d (weaken_subst_evar _ empty H99)) (subst_evar_Typing G12 s17 T105 jm79 G11 t82 T106 jm74 G13 d (weaken_subst_evar _ empty H99)))))
    | (K_Sigma S59 T106 jm75 jm76) => (fun (G13 : Env) (d : (Trace TmVar)) (H99 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (K_Sigma G13 (subst_TmVar_Ty (weakenTrace d H0) s17 S59) (subst_TmVar_Ty (weakenTrace d (HS TmVar H0)) s17 T106) (subst_evar_Kinding G12 s17 T105 jm79 G11 S59 (star) jm75 G13 d (weaken_subst_evar _ empty H99)) (subst_evar_Kinding G12 s17 T105 jm79 (evar G11 S59) T106 (star) jm76 (appendEnv G13 (subst_TmVar_Env d s17 (evar empty S59))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty S59) H99))))
    | (K_Conv K64 K65 T106 jm77 jm78) => (fun (G13 : Env) (d : (Trace TmVar)) (H99 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (K_Conv G13 (subst_TmVar_Kind (weakenTrace d H0) s17 K64) (subst_TmVar_Kind (weakenTrace d H0) s17 K65) (subst_TmVar_Ty (weakenTrace d H0) s17 T106) (subst_evar_Kinding G12 s17 T105 jm79 G11 T106 K64 jm77 G13 d (weaken_subst_evar _ empty H99)) (subst_evar_KindEq G12 s17 T105 jm79 G11 K64 K65 jm78 G13 d (weaken_subst_evar _ empty H99))))
  end
with subst_evar_WfKind (G12 : Env) (s17 : Tm) (T105 : Ty) (jm73 : (Typing G12 s17 T105)) (G11 : Env) (K : Kind) (jm74 : (WfKind G11 K)) :
(forall (G13 : Env) (d : (Trace TmVar)) (H88 : (subst_evar G12 T105 s17 d G11 G13)) ,
  (WfKind G13 (subst_TmVar_Kind d s17 K))) :=
  match jm74 in (WfKind _ K) return (forall (G13 : Env) (d : (Trace TmVar)) (H88 : (subst_evar G12 T105 s17 d G11 G13)) ,
    (WfKind G13 (subst_TmVar_Kind d s17 K))) with
    | (WfStar) => (fun (G13 : Env) (d : (Trace TmVar)) (H88 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (WfStar G13))
    | (WfPi K63 T106 jm71 jm72) => (fun (G13 : Env) (d : (Trace TmVar)) (H88 : (subst_evar G12 T105 s17 d G11 G13)) =>
      (WfKind_cast G13 _ G13 (subst_TmVar_Kind d s17 (kpi T106 (weakenKind K63 (HS TmVar H0)))) eq_refl (f_equal2 kpi eq_refl (weakenKind_subst_TmVar_Kind (HS TmVar H0) d s17 K63)) (WfPi G13 (subst_TmVar_Kind (weakenTrace d H0) s17 K63) (subst_TmVar_Ty (weakenTrace d H0) s17 T106) (subst_evar_Kinding G12 s17 T105 jm73 G11 T106 (star) jm71 G13 d (weaken_subst_evar _ empty H88)) (subst_evar_WfKind G12 s17 T105 jm73 G11 K63 jm72 G13 d (weaken_subst_evar _ empty H88)))))
  end.
Fixpoint subst_etvar_KindEq (G12 : Env) (S59 : Ty) (K63 : Kind) (jm77 : (Kinding G12 S59 K63)) (G11 : Env) (K1 : Kind) (K2 : Kind) (jm78 : (KindEq G11 K1 K2)) :
(forall (G13 : Env) (d : (Trace TyVar)) (H97 : (subst_etvar G12 K63 S59 d G11 G13)) ,
  (KindEq G13 (subst_TyVar_Kind d S59 K1) (subst_TyVar_Kind d S59 K2))) :=
  match jm78 in (KindEq _ K1 K2) return (forall (G13 : Env) (d : (Trace TyVar)) (H97 : (subst_etvar G12 K63 S59 d G11 G13)) ,
    (KindEq G13 (subst_TyVar_Kind d S59 K1) (subst_TyVar_Kind d S59 K2))) with
    | (QK_Pi K65 K66 T106 T107 jm71 jm72) => (fun (G13 : Env) (d : (Trace TyVar)) (H97 : (subst_etvar G12 K63 S59 d G11 G13)) =>
      (QK_Pi G13 (subst_TyVar_Kind (weakenTrace d (HS TmVar H0)) S59 K65) (subst_TyVar_Kind (weakenTrace d (HS TmVar H0)) S59 K66) (subst_TyVar_Ty (weakenTrace d H0) S59 T106) (subst_TyVar_Ty (weakenTrace d H0) S59 T107) (subst_etvar_TyEq G12 S59 K63 jm77 G11 T106 T107 (star) jm71 G13 d (weaken_subst_etvar _ empty H97)) (subst_etvar_KindEq G12 S59 K63 jm77 (evar G11 T106) K65 K66 jm72 (appendEnv G13 (subst_TyVar_Env d S59 (evar empty T106))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty T106) H97))))
    | (QK_Refl K64 jm73) => (fun (G13 : Env) (d : (Trace TyVar)) (H97 : (subst_etvar G12 K63 S59 d G11 G13)) =>
      (QK_Refl G13 (subst_TyVar_Kind (weakenTrace d H0) S59 K64) (subst_etvar_WfKind G12 S59 K63 jm77 G11 K64 jm73 G13 d (weaken_subst_etvar _ empty H97))))
    | (QK_Sym K65 K66 jm74) => (fun (G13 : Env) (d : (Trace TyVar)) (H97 : (subst_etvar G12 K63 S59 d G11 G13)) =>
      (QK_Sym G13 (subst_TyVar_Kind (weakenTrace d H0) S59 K65) (subst_TyVar_Kind (weakenTrace d H0) S59 K66) (subst_etvar_KindEq G12 S59 K63 jm77 G11 K65 K66 jm74 G13 d (weaken_subst_etvar _ empty H97))))
    | (QK_Trans K65 K66 K67 jm75 jm76) => (fun (G13 : Env) (d : (Trace TyVar)) (H97 : (subst_etvar G12 K63 S59 d G11 G13)) =>
      (QK_Trans G13 (subst_TyVar_Kind (weakenTrace d H0) S59 K65) (subst_TyVar_Kind (weakenTrace d H0) S59 K66) (subst_TyVar_Kind (weakenTrace d H0) S59 K67) (subst_etvar_KindEq G12 S59 K63 jm77 G11 K65 K66 jm75 G13 d (weaken_subst_etvar _ empty H97)) (subst_etvar_KindEq G12 S59 K63 jm77 G11 K66 K67 jm76 G13 d (weaken_subst_etvar _ empty H97))))
  end
with subst_etvar_TyEq (G12 : Env) (S61 : Ty) (K63 : Kind) (jm79 : (Kinding G12 S61 K63)) (G11 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm80 : (TyEq G11 T1 T2 K)) :
(forall (G13 : Env) (d : (Trace TyVar)) (H106 : (subst_etvar G12 K63 S61 d G11 G13)) ,
  (TyEq G13 (subst_TyVar_Ty d S61 T1) (subst_TyVar_Ty d S61 T2) (subst_TyVar_Kind d S61 K))) :=
  match jm80 in (TyEq _ T1 T2 K) return (forall (G13 : Env) (d : (Trace TyVar)) (H106 : (subst_etvar G12 K63 S61 d G11 G13)) ,
    (TyEq G13 (subst_TyVar_Ty d S61 T1) (subst_TyVar_Ty d S61 T2) (subst_TyVar_Kind d S61 K))) with
    | (QT_Pi S59 S60 T107 T108 jm71 jm72) => (fun (G13 : Env) (d : (Trace TyVar)) (H106 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (QT_Pi G13 (subst_TyVar_Ty (weakenTrace d H0) S61 S59) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S61 S60) (subst_TyVar_Ty (weakenTrace d H0) S61 T107) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S61 T108) (subst_etvar_TyEq G12 S61 K63 jm79 G11 S59 T107 (star) jm71 G13 d (weaken_subst_etvar _ empty H106)) (subst_etvar_TyEq G12 S61 K63 jm79 (evar G11 T107) S60 T108 (star) jm72 (appendEnv G13 (subst_TyVar_Env d S61 (evar empty T107))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty T107) H106))))
    | (QT_App K64 S59 S60 T106 t82 t83 jm73 jm74) => (fun (G13 : Env) (d : (Trace TyVar)) (H106 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (TyEq_cast G13 _ _ _ G13 (subst_TyVar_Ty d S61 (tapp S59 t82)) (subst_TyVar_Ty d S61 (tapp S60 t83)) (subst_TyVar_Kind d S61 (subst_TmVar_Kind X0 t82 K64)) eq_refl eq_refl eq_refl (eq_sym (subst_TyVar_Kind_subst_TmVar_Kind0_comm K64 d S61 t82)) (QT_App G13 (subst_TyVar_Kind (weakenTrace d (HS TmVar H0)) S61 K64) (subst_TyVar_Ty (weakenTrace d H0) S61 S59) (subst_TyVar_Ty (weakenTrace d H0) S61 S60) (subst_TyVar_Ty (weakenTrace d H0) S61 T106) (subst_TyVar_Tm (weakenTrace d H0) S61 t82) (subst_TyVar_Tm (weakenTrace d H0) S61 t83) (subst_etvar_TyEq G12 S61 K63 jm79 G11 S59 S60 (kpi T106 K64) jm73 G13 d (weaken_subst_etvar _ empty H106)) (subst_etvar_TermEq G12 S61 K63 jm79 G11 t82 t83 T106 jm74 G13 d (weaken_subst_etvar _ empty H106)))))
    | (QT_Refl K64 T106 jm75) => (fun (G13 : Env) (d : (Trace TyVar)) (H106 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (QT_Refl G13 (subst_TyVar_Kind (weakenTrace d H0) S61 K64) (subst_TyVar_Ty (weakenTrace d H0) S61 T106) (subst_etvar_Kinding G12 S61 K63 jm79 G11 T106 K64 jm75 G13 d (weaken_subst_etvar _ empty H106))))
    | (QT_Symm K64 S59 T106 jm76) => (fun (G13 : Env) (d : (Trace TyVar)) (H106 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (QT_Symm G13 (subst_TyVar_Kind (weakenTrace d H0) S61 K64) (subst_TyVar_Ty (weakenTrace d H0) S61 S59) (subst_TyVar_Ty (weakenTrace d H0) S61 T106) (subst_etvar_TyEq G12 S61 K63 jm79 G11 T106 S59 K64 jm76 G13 d (weaken_subst_etvar _ empty H106))))
    | (QT_Trans K64 S59 T106 U2 jm77 jm78) => (fun (G13 : Env) (d : (Trace TyVar)) (H106 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (QT_Trans G13 (subst_TyVar_Kind (weakenTrace d H0) S61 K64) (subst_TyVar_Ty (weakenTrace d H0) S61 S59) (subst_TyVar_Ty (weakenTrace d H0) S61 T106) (subst_TyVar_Ty (weakenTrace d H0) S61 U2) (subst_etvar_TyEq G12 S61 K63 jm79 G11 S59 U2 K64 jm77 G13 d (weaken_subst_etvar _ empty H106)) (subst_etvar_TyEq G12 S61 K63 jm79 G11 U2 T106 K64 jm78 G13 d (weaken_subst_etvar _ empty H106))))
  end
with subst_etvar_TermEq (G12 : Env) (S61 : Ty) (K63 : Kind) (jm89 : (Kinding G12 S61 K63)) (G11 : Env) (t1 : Tm) (t2 : Tm) (T : Ty) (jm90 : (TermEq G11 t1 t2 T)) :
(forall (G13 : Env) (d : (Trace TyVar)) (H125 : (subst_etvar G12 K63 S61 d G11 G13)) ,
  (TermEq G13 (subst_TyVar_Tm d S61 t1) (subst_TyVar_Tm d S61 t2) (subst_TyVar_Ty d S61 T))) :=
  match jm90 in (TermEq _ t1 t2 T) return (forall (G13 : Env) (d : (Trace TyVar)) (H125 : (subst_etvar G12 K63 S61 d G11 G13)) ,
    (TermEq G13 (subst_TyVar_Tm d S61 t1) (subst_TyVar_Tm d S61 t2) (subst_TyVar_Ty d S61 T))) with
    | (Q_Abs S59 S60 T106 t83 t84 jm71 jm72) => (fun (G13 : Env) (d : (Trace TyVar)) (H125 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (Q_Abs G13 (subst_TyVar_Ty (weakenTrace d H0) S61 S59) (subst_TyVar_Ty (weakenTrace d H0) S61 S60) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S61 T106) (subst_TyVar_Tm (weakenTrace d (HS TmVar H0)) S61 t83) (subst_TyVar_Tm (weakenTrace d (HS TmVar H0)) S61 t84) (subst_etvar_TyEq G12 S61 K63 jm89 G11 S59 S60 (star) jm71 G13 d (weaken_subst_etvar _ empty H125)) (subst_etvar_TermEq G12 S61 K63 jm89 (evar G11 S59) t83 t84 T106 jm72 (appendEnv G13 (subst_TyVar_Env d S61 (evar empty S59))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty S59) H125))))
    | (Q_App S59 T106 s18 s19 t83 t84 jm73 jm74) => (fun (G13 : Env) (d : (Trace TyVar)) (H125 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (TermEq_cast G13 _ _ _ G13 (subst_TyVar_Tm d S61 (app t83 t84)) (subst_TyVar_Tm d S61 (app s18 s19)) (subst_TyVar_Ty d S61 (subst_TmVar_Ty X0 t84 T106)) eq_refl eq_refl eq_refl (eq_sym (subst_TyVar_Ty_subst_TmVar_Ty0_comm T106 d S61 t84)) (Q_App G13 (subst_TyVar_Ty (weakenTrace d H0) S61 S59) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S61 T106) (subst_TyVar_Tm (weakenTrace d H0) S61 s18) (subst_TyVar_Tm (weakenTrace d H0) S61 s19) (subst_TyVar_Tm (weakenTrace d H0) S61 t83) (subst_TyVar_Tm (weakenTrace d H0) S61 t84) (subst_etvar_TermEq G12 S61 K63 jm89 G11 t83 s18 (tpi S59 T106) jm73 G13 d (weaken_subst_etvar _ empty H125)) (subst_etvar_TermEq G12 S61 K63 jm89 G11 t84 s19 S59 jm74 G13 d (weaken_subst_etvar _ empty H125)))))
    | (Q_Beta S59 T106 s17 t82 jm75 jm76) => (fun (G13 : Env) (d : (Trace TyVar)) (H125 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (TermEq_cast G13 _ _ _ G13 (subst_TyVar_Tm d S61 (app (abs S59 t82) s17)) (subst_TyVar_Tm d S61 (subst_TmVar_Tm X0 s17 t82)) (subst_TyVar_Ty d S61 (subst_TmVar_Ty X0 s17 T106)) eq_refl eq_refl (eq_sym (subst_TyVar_Tm_subst_TmVar_Tm0_comm t82 d S61 s17)) (eq_sym (subst_TyVar_Ty_subst_TmVar_Ty0_comm T106 d S61 s17)) (Q_Beta G13 (subst_TyVar_Ty (weakenTrace d H0) S61 S59) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S61 T106) (subst_TyVar_Tm (weakenTrace d H0) S61 s17) (subst_TyVar_Tm (weakenTrace d (HS TmVar H0)) S61 t82) (subst_etvar_Typing G12 S61 K63 jm89 (evar G11 S59) t82 T106 jm75 (appendEnv G13 (subst_TyVar_Env d S61 (evar empty S59))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty S59) H125)) (subst_etvar_Typing G12 S61 K63 jm89 G11 s17 S59 jm76 G13 d (weaken_subst_etvar _ empty H125)))))
    | (Q_Eta S59 T106 t82 jm77) => (fun (G13 : Env) (d : (Trace TyVar)) (H125 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (TermEq_cast G13 _ _ _ G13 (subst_TyVar_Tm d S61 (abs S59 (app (weakenTm t82 (HS TmVar H0)) (var I0)))) (subst_TyVar_Tm d S61 t82) (subst_TyVar_Ty d S61 (tpi S59 T106)) eq_refl (f_equal2 abs eq_refl (f_equal2 app (weakenTm_subst_TyVar_Tm (HS TmVar H0) d S61 t82) eq_refl)) eq_refl eq_refl (Q_Eta G13 (subst_TyVar_Ty (weakenTrace d H0) S61 S59) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S61 T106) (subst_TyVar_Tm (weakenTrace d H0) S61 t82) (subst_etvar_Typing G12 S61 K63 jm89 G11 t82 (tpi S59 T106) jm77 G13 d (weaken_subst_etvar _ empty H125)))))
    | (Q_Proj1 S59 T106 t83 t84 jm78 jm79 jm80) => (fun (G13 : Env) (d : (Trace TyVar)) (H125 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (Q_Proj1 G13 (subst_TyVar_Ty (weakenTrace d H0) S61 S59) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S61 T106) (subst_TyVar_Tm (weakenTrace d H0) S61 t83) (subst_TyVar_Tm (weakenTrace d H0) S61 t84) (subst_etvar_Kinding G12 S61 K63 jm89 G11 (tsig S59 T106) (star) jm78 G13 d (weaken_subst_etvar _ empty H125)) (subst_etvar_Typing G12 S61 K63 jm89 G11 t83 S59 jm79 G13 d (weaken_subst_etvar _ empty H125)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (subst_TyVar_Ty_subst_TmVar_Ty0_comm T106 d S61 t83) (subst_etvar_Typing G12 S61 K63 jm89 G11 t84 (subst_TmVar_Ty X0 t83 T106) jm80 G13 d (weaken_subst_etvar _ empty H125)))))
    | (Q_Proj2 S59 T106 t83 t84 jm81 jm82 jm83) => (fun (G13 : Env) (d : (Trace TyVar)) (H125 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (TermEq_cast G13 _ _ _ G13 (subst_TyVar_Tm d S61 (prj2 (pair t83 t84 S59 T106))) (subst_TyVar_Tm d S61 t84) (subst_TyVar_Ty d S61 (subst_TmVar_Ty X0 t83 T106)) eq_refl eq_refl eq_refl (eq_sym (subst_TyVar_Ty_subst_TmVar_Ty0_comm T106 d S61 t83)) (Q_Proj2 G13 (subst_TyVar_Ty (weakenTrace d H0) S61 S59) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S61 T106) (subst_TyVar_Tm (weakenTrace d H0) S61 t83) (subst_TyVar_Tm (weakenTrace d H0) S61 t84) (subst_etvar_Kinding G12 S61 K63 jm89 G11 (tsig S59 T106) (star) jm81 G13 d (weaken_subst_etvar _ empty H125)) (subst_etvar_Typing G12 S61 K63 jm89 G11 t83 S59 jm82 G13 d (weaken_subst_etvar _ empty H125)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (subst_TyVar_Ty_subst_TmVar_Ty0_comm T106 d S61 t83) (subst_etvar_Typing G12 S61 K63 jm89 G11 t84 (subst_TmVar_Ty X0 t83 T106) jm83 G13 d (weaken_subst_etvar _ empty H125))))))
    | (Q_SjPair S59 T106 t82 jm84) => (fun (G13 : Env) (d : (Trace TyVar)) (H125 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (Q_SjPair G13 (subst_TyVar_Ty (weakenTrace d H0) S61 S59) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S61 T106) (subst_TyVar_Tm (weakenTrace d H0) S61 t82) (subst_etvar_Typing G12 S61 K63 jm89 G11 t82 (tsig S59 T106) jm84 G13 d (weaken_subst_etvar _ empty H125))))
    | (Q_Refl T106 t82 jm85) => (fun (G13 : Env) (d : (Trace TyVar)) (H125 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (Q_Refl G13 (subst_TyVar_Ty (weakenTrace d H0) S61 T106) (subst_TyVar_Tm (weakenTrace d H0) S61 t82) (subst_etvar_Typing G12 S61 K63 jm89 G11 t82 T106 jm85 G13 d (weaken_subst_etvar _ empty H125))))
    | (Q_Symm T106 s17 t82 jm86) => (fun (G13 : Env) (d : (Trace TyVar)) (H125 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (Q_Symm G13 (subst_TyVar_Ty (weakenTrace d H0) S61 T106) (subst_TyVar_Tm (weakenTrace d H0) S61 s17) (subst_TyVar_Tm (weakenTrace d H0) S61 t82) (subst_etvar_TermEq G12 S61 K63 jm89 G11 t82 s17 T106 jm86 G13 d (weaken_subst_etvar _ empty H125))))
    | (Q_Trans T106 s17 t82 u1 jm87 jm88) => (fun (G13 : Env) (d : (Trace TyVar)) (H125 : (subst_etvar G12 K63 S61 d G11 G13)) =>
      (Q_Trans G13 (subst_TyVar_Ty (weakenTrace d H0) S61 T106) (subst_TyVar_Tm (weakenTrace d H0) S61 s17) (subst_TyVar_Tm (weakenTrace d H0) S61 t82) (subst_TyVar_Tm (weakenTrace d H0) S61 u1) (subst_etvar_TermEq G12 S61 K63 jm89 G11 s17 u1 T106 jm87 G13 d (weaken_subst_etvar _ empty H125)) (subst_etvar_TermEq G12 S61 K63 jm89 G11 u1 t82 T106 jm88 G13 d (weaken_subst_etvar _ empty H125))))
  end
with subst_etvar_Typing (G12 : Env) (S60 : Ty) (K63 : Kind) (jm82 : (Kinding G12 S60 K63)) (G11 : Env) (t : Tm) (T : Ty) (jm83 : (Typing G11 t T)) :
(forall (G13 : Env) (d : (Trace TyVar)) (H109 : (subst_etvar G12 K63 S60 d G11 G13)) ,
  (Typing G13 (subst_TyVar_Tm d S60 t) (subst_TyVar_Ty d S60 T))) :=
  match jm83 in (Typing _ t T) return (forall (G13 : Env) (d : (Trace TyVar)) (H109 : (subst_etvar G12 K63 S60 d G11 G13)) ,
    (Typing G13 (subst_TyVar_Tm d S60 t) (subst_TyVar_Ty d S60 T))) with
    | (T_Var T106 x72 lk5 H87 H88) => (fun (G13 : Env) (d : (Trace TyVar)) (H109 : (subst_etvar G12 K63 S60 d G11 G13)) =>
      (T_Var G13 (subst_TyVar_Ty (weakenTrace d H0) S60 T106) x72 (subst_etvar_lookup_evar K63 (Kinding_wf_0 G12 S60 K63 jm82) H109 T106 lk5) (substhvl_TyVar_wfTy (Kinding_wf_0 G12 S60 K63 jm82) _ _ H87 (weaken_substhvl_TyVar H0 (subst_etvar_substhvl_TyVar _ H109))) (substhvl_TyVar_wfindex_TmVar (weaken_substhvl_TyVar H0 (subst_etvar_substhvl_TyVar _ H109)) H88)))
    | (T_Abs S59 T106 t82 jm81 jm71) => (fun (G13 : Env) (d : (Trace TyVar)) (H109 : (subst_etvar G12 K63 S60 d G11 G13)) =>
      (T_Abs G13 (subst_TyVar_Ty (weakenTrace d H0) S60 S59) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S60 T106) (subst_TyVar_Tm (weakenTrace d (HS TmVar H0)) S60 t82) (subst_etvar_Kinding G12 S60 K63 jm82 G11 S59 (star) jm81 G13 d (weaken_subst_etvar _ empty H109)) (subst_etvar_Typing G12 S60 K63 jm82 (evar G11 S59) t82 T106 jm71 (appendEnv G13 (subst_TyVar_Env d S60 (evar empty S59))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty S59) H109))))
    | (T_App S59 T106 t83 t84 jm72 jm73) => (fun (G13 : Env) (d : (Trace TyVar)) (H109 : (subst_etvar G12 K63 S60 d G11 G13)) =>
      (Typing_cast G13 _ _ G13 (subst_TyVar_Tm d S60 (app t83 t84)) (subst_TyVar_Ty d S60 (subst_TmVar_Ty X0 t84 T106)) eq_refl eq_refl (eq_sym (subst_TyVar_Ty_subst_TmVar_Ty0_comm T106 d S60 t84)) (T_App G13 (subst_TyVar_Ty (weakenTrace d H0) S60 S59) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S60 T106) (subst_TyVar_Tm (weakenTrace d H0) S60 t83) (subst_TyVar_Tm (weakenTrace d H0) S60 t84) (subst_etvar_Typing G12 S60 K63 jm82 G11 t83 (tpi S59 T106) jm72 G13 d (weaken_subst_etvar _ empty H109)) (subst_etvar_Typing G12 S60 K63 jm82 G11 t84 S59 jm73 G13 d (weaken_subst_etvar _ empty H109)))))
    | (T_Pair S59 T106 t83 t84 jm74 jm75 jm76) => (fun (G13 : Env) (d : (Trace TyVar)) (H109 : (subst_etvar G12 K63 S60 d G11 G13)) =>
      (T_Pair G13 (subst_TyVar_Ty (weakenTrace d H0) S60 S59) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S60 T106) (subst_TyVar_Tm (weakenTrace d H0) S60 t83) (subst_TyVar_Tm (weakenTrace d H0) S60 t84) (subst_etvar_Kinding G12 S60 K63 jm82 G11 (tsig S59 T106) (star) jm74 G13 d (weaken_subst_etvar _ empty H109)) (subst_etvar_Typing G12 S60 K63 jm82 G11 t83 S59 jm75 G13 d (weaken_subst_etvar _ empty H109)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (subst_TyVar_Ty_subst_TmVar_Ty0_comm T106 d S60 t83) (subst_etvar_Typing G12 S60 K63 jm82 G11 t84 (subst_TmVar_Ty X0 t83 T106) jm76 G13 d (weaken_subst_etvar _ empty H109)))))
    | (T_Proj1 S59 T106 t82 jm77) => (fun (G13 : Env) (d : (Trace TyVar)) (H109 : (subst_etvar G12 K63 S60 d G11 G13)) =>
      (T_Proj1 G13 (subst_TyVar_Ty (weakenTrace d H0) S60 S59) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S60 T106) (subst_TyVar_Tm (weakenTrace d H0) S60 t82) (subst_etvar_Typing G12 S60 K63 jm82 G11 t82 (tsig S59 T106) jm77 G13 d (weaken_subst_etvar _ empty H109))))
    | (T_Proj2 S59 T106 t82 jm78) => (fun (G13 : Env) (d : (Trace TyVar)) (H109 : (subst_etvar G12 K63 S60 d G11 G13)) =>
      (Typing_cast G13 _ _ G13 (subst_TyVar_Tm d S60 (prj2 t82)) (subst_TyVar_Ty d S60 (subst_TmVar_Ty X0 (prj1 t82) T106)) eq_refl eq_refl (eq_sym (subst_TyVar_Ty_subst_TmVar_Ty0_comm T106 d S60 (prj1 t82))) (T_Proj2 G13 (subst_TyVar_Ty (weakenTrace d H0) S60 S59) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S60 T106) (subst_TyVar_Tm (weakenTrace d H0) S60 t82) (subst_etvar_Typing G12 S60 K63 jm82 G11 t82 (tsig S59 T106) jm78 G13 d (weaken_subst_etvar _ empty H109)))))
    | (T_Conv T107 T108 t82 jm79 jm80) => (fun (G13 : Env) (d : (Trace TyVar)) (H109 : (subst_etvar G12 K63 S60 d G11 G13)) =>
      (T_Conv G13 (subst_TyVar_Ty (weakenTrace d H0) S60 T107) (subst_TyVar_Ty (weakenTrace d H0) S60 T108) (subst_TyVar_Tm (weakenTrace d H0) S60 t82) (subst_etvar_Typing G12 S60 K63 jm82 G11 t82 T107 jm79 G13 d (weaken_subst_etvar _ empty H109)) (subst_etvar_TyEq G12 S60 K63 jm82 G11 T107 T108 (star) jm80 G13 d (weaken_subst_etvar _ empty H109))))
  end
with subst_etvar_Kinding (G12 : Env) (S60 : Ty) (K63 : Kind) (jm79 : (Kinding G12 S60 K63)) (G11 : Env) (T : Ty) (K : Kind) (jm80 : (Kinding G11 T K)) :
(forall (G13 : Env) (d : (Trace TyVar)) (H100 : (subst_etvar G12 K63 S60 d G11 G13)) ,
  (Kinding G13 (subst_TyVar_Ty d S60 T) (subst_TyVar_Kind d S60 K))) :=
  match jm80 in (Kinding _ T K) return (forall (G13 : Env) (d : (Trace TyVar)) (H100 : (subst_etvar G12 K63 S60 d G11 G13)) ,
    (Kinding G13 (subst_TyVar_Ty d S60 T) (subst_TyVar_Kind d S60 K))) with
    | (K_TVar K64 X11 lk5 H87 H88) => (fun (G13 : Env) (d : (Trace TyVar)) (H100 : (subst_etvar G12 K63 S60 d G11 G13)) =>
      (subst_etvar_lookup_etvar G12 S60 K63 jm79 d G11 G13 H100 X11 K64 lk5))
    | (K_Pi T107 T108 jm71 jm72) => (fun (G13 : Env) (d : (Trace TyVar)) (H100 : (subst_etvar G12 K63 S60 d G11 G13)) =>
      (K_Pi G13 (subst_TyVar_Ty (weakenTrace d H0) S60 T107) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S60 T108) (subst_etvar_Kinding G12 S60 K63 jm79 G11 T107 (star) jm71 G13 d (weaken_subst_etvar _ empty H100)) (subst_etvar_Kinding G12 S60 K63 jm79 (evar G11 T107) T108 (star) jm72 (appendEnv G13 (subst_TyVar_Env d S60 (evar empty T107))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty T107) H100))))
    | (K_App K64 S59 T106 t82 jm73 jm74) => (fun (G13 : Env) (d : (Trace TyVar)) (H100 : (subst_etvar G12 K63 S60 d G11 G13)) =>
      (Kinding_cast G13 _ _ G13 (subst_TyVar_Ty d S60 (tapp S59 t82)) (subst_TyVar_Kind d S60 (subst_TmVar_Kind X0 t82 K64)) eq_refl eq_refl (eq_sym (subst_TyVar_Kind_subst_TmVar_Kind0_comm K64 d S60 t82)) (K_App G13 (subst_TyVar_Kind (weakenTrace d (HS TmVar H0)) S60 K64) (subst_TyVar_Ty (weakenTrace d H0) S60 S59) (subst_TyVar_Ty (weakenTrace d H0) S60 T106) (subst_TyVar_Tm (weakenTrace d H0) S60 t82) (subst_etvar_Kinding G12 S60 K63 jm79 G11 S59 (kpi T106 K64) jm73 G13 d (weaken_subst_etvar _ empty H100)) (subst_etvar_Typing G12 S60 K63 jm79 G11 t82 T106 jm74 G13 d (weaken_subst_etvar _ empty H100)))))
    | (K_Sigma S59 T106 jm75 jm76) => (fun (G13 : Env) (d : (Trace TyVar)) (H100 : (subst_etvar G12 K63 S60 d G11 G13)) =>
      (K_Sigma G13 (subst_TyVar_Ty (weakenTrace d H0) S60 S59) (subst_TyVar_Ty (weakenTrace d (HS TmVar H0)) S60 T106) (subst_etvar_Kinding G12 S60 K63 jm79 G11 S59 (star) jm75 G13 d (weaken_subst_etvar _ empty H100)) (subst_etvar_Kinding G12 S60 K63 jm79 (evar G11 S59) T106 (star) jm76 (appendEnv G13 (subst_TyVar_Env d S60 (evar empty S59))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty S59) H100))))
    | (K_Conv K65 K66 T106 jm77 jm78) => (fun (G13 : Env) (d : (Trace TyVar)) (H100 : (subst_etvar G12 K63 S60 d G11 G13)) =>
      (K_Conv G13 (subst_TyVar_Kind (weakenTrace d H0) S60 K65) (subst_TyVar_Kind (weakenTrace d H0) S60 K66) (subst_TyVar_Ty (weakenTrace d H0) S60 T106) (subst_etvar_Kinding G12 S60 K63 jm79 G11 T106 K65 jm77 G13 d (weaken_subst_etvar _ empty H100)) (subst_etvar_KindEq G12 S60 K63 jm79 G11 K65 K66 jm78 G13 d (weaken_subst_etvar _ empty H100))))
  end
with subst_etvar_WfKind (G12 : Env) (S59 : Ty) (K63 : Kind) (jm73 : (Kinding G12 S59 K63)) (G11 : Env) (K : Kind) (jm74 : (WfKind G11 K)) :
(forall (G13 : Env) (d : (Trace TyVar)) (H89 : (subst_etvar G12 K63 S59 d G11 G13)) ,
  (WfKind G13 (subst_TyVar_Kind d S59 K))) :=
  match jm74 in (WfKind _ K) return (forall (G13 : Env) (d : (Trace TyVar)) (H89 : (subst_etvar G12 K63 S59 d G11 G13)) ,
    (WfKind G13 (subst_TyVar_Kind d S59 K))) with
    | (WfStar) => (fun (G13 : Env) (d : (Trace TyVar)) (H89 : (subst_etvar G12 K63 S59 d G11 G13)) =>
      (WfStar G13))
    | (WfPi K64 T106 jm71 jm72) => (fun (G13 : Env) (d : (Trace TyVar)) (H89 : (subst_etvar G12 K63 S59 d G11 G13)) =>
      (WfKind_cast G13 _ G13 (subst_TyVar_Kind d S59 (kpi T106 (weakenKind K64 (HS TmVar H0)))) eq_refl (f_equal2 kpi eq_refl (weakenKind_subst_TyVar_Kind (HS TmVar H0) d S59 K64)) (WfPi G13 (subst_TyVar_Kind (weakenTrace d H0) S59 K64) (subst_TyVar_Ty (weakenTrace d H0) S59 T106) (subst_etvar_Kinding G12 S59 K63 jm73 G11 T106 (star) jm71 G13 d (weaken_subst_etvar _ empty H89)) (subst_etvar_WfKind G12 S59 K63 jm73 G11 K64 jm72 G13 d (weaken_subst_etvar _ empty H89)))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutoffTmVar_append weakenCutoffTyVar_append weakenTrace_append weakenKind_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.