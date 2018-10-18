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
  
  Fixpoint weakenIndexTmVar (x11 : (Index TmVar)) (k : Hvl) {struct k} :
  (Index TmVar) :=
    match k with
      | (H0) => x11
      | (HS a k) => match a with
        | (TmVar) => (IS (weakenIndexTmVar x11 k))
        | _ => (weakenIndexTmVar x11 k)
      end
    end.
  Fixpoint weakenIndexTyVar (X7 : (Index TyVar)) (k : Hvl) {struct k} :
  (Index TyVar) :=
    match k with
      | (H0) => X7
      | (HS a k) => match a with
        | (TyVar) => (IS (weakenIndexTyVar X7 k))
        | _ => (weakenIndexTyVar X7 k)
      end
    end.
  Lemma weakenIndexTmVar_append  :
    (forall (x11 : (Index TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTmVar (weakenIndexTmVar x11 k) k0) = (weakenIndexTmVar x11 (appendHvl k k0)))).
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
  Inductive Decls : Set :=
    | DNil 
    | DConsTm (t : Tm) (d : Decls)
    | DConsTy (K : Kind) (d : Decls)
  with Kind : Set :=
    | Star 
    | KPi (T : Ty) (K : Kind)
  with Ty : Set :=
    | TVar (X : (Index TyVar))
    | TPi (T1 : Ty) (T2 : Ty)
    | TApp (T : Ty) (t : Tm)
  with Tm : Set :=
    | Var (x : (Index TmVar))
    | Abs (T : Ty) (t : Tm)
    | App (t1 : Tm) (t2 : Tm)
    | Let (d : Decls) (t : Tm).
  Scheme ind_Decls := Induction for Decls Sort Prop
  with ind_Kind := Induction for Kind Sort Prop
  with ind_Ty := Induction for Ty Sort Prop
  with ind_Tm := Induction for Tm Sort Prop.
  Combined Scheme ind_Decls_Kind_Ty_Tm from ind_Decls, ind_Kind, ind_Ty, ind_Tm.
End Terms.

Section Functions.
  Fixpoint bind (d7 : Decls) {struct d7} :
  Hvl :=
    match d7 with
      | (DNil) => H0
      | (DConsTm t d) => (appendHvl (HS TmVar H0) (bind d))
      | (DConsTy K d) => (appendHvl (HS TyVar H0) (bind d))
    end.
  Scheme ind_bind_Decls := Induction for Decls Sort Prop.
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
  Fixpoint shift_TmVar_Index (c : (Cutoff TmVar)) (x11 : (Index TmVar)) {struct c} :
  (Index TmVar) :=
    match c with
      | (C0) => (IS x11)
      | (CS c) => match x11 with
        | (I0) => I0
        | (IS x11) => (IS (shift_TmVar_Index c x11))
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
  Fixpoint shift_TmVar_Decls (c : (Cutoff TmVar)) (d8 : Decls) {struct d8} :
  Decls :=
    match d8 with
      | (DNil) => (DNil)
      | (DConsTm t6 d9) => (DConsTm (shift_TmVar_Tm c t6) (shift_TmVar_Decls (CS c) d9))
      | (DConsTy K3 d10) => (DConsTy (shift_TmVar_Kind c K3) (shift_TmVar_Decls c d10))
    end
  with shift_TmVar_Kind (c : (Cutoff TmVar)) (K3 : Kind) {struct K3} :
  Kind :=
    match K3 with
      | (Star) => (Star)
      | (KPi T5 K4) => (KPi (shift_TmVar_Ty c T5) (shift_TmVar_Kind (CS c) K4))
    end
  with shift_TmVar_Ty (c : (Cutoff TmVar)) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (TVar X7) => (TVar X7)
      | (TPi T5 T6) => (TPi (shift_TmVar_Ty c T5) (shift_TmVar_Ty (CS c) T6))
      | (TApp T7 t6) => (TApp (shift_TmVar_Ty c T7) (shift_TmVar_Tm c t6))
    end
  with shift_TmVar_Tm (c : (Cutoff TmVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x11) => (Var (shift_TmVar_Index c x11))
      | (Abs T5 t6) => (Abs (shift_TmVar_Ty c T5) (shift_TmVar_Tm (CS c) t6))
      | (App t7 t8) => (App (shift_TmVar_Tm c t7) (shift_TmVar_Tm c t8))
      | (Let d8 t9) => (Let (shift_TmVar_Decls c d8) (shift_TmVar_Tm (weakenCutoffTmVar c (appendHvl H0 (bind d8))) t9))
    end.
  Fixpoint shift_TyVar_Decls (c : (Cutoff TyVar)) (d8 : Decls) {struct d8} :
  Decls :=
    match d8 with
      | (DNil) => (DNil)
      | (DConsTm t6 d9) => (DConsTm (shift_TyVar_Tm c t6) (shift_TyVar_Decls c d9))
      | (DConsTy K3 d10) => (DConsTy (shift_TyVar_Kind c K3) (shift_TyVar_Decls (CS c) d10))
    end
  with shift_TyVar_Kind (c : (Cutoff TyVar)) (K3 : Kind) {struct K3} :
  Kind :=
    match K3 with
      | (Star) => (Star)
      | (KPi T5 K4) => (KPi (shift_TyVar_Ty c T5) (shift_TyVar_Kind c K4))
    end
  with shift_TyVar_Ty (c : (Cutoff TyVar)) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (TVar X7) => (TVar (shift_TyVar_Index c X7))
      | (TPi T5 T6) => (TPi (shift_TyVar_Ty c T5) (shift_TyVar_Ty c T6))
      | (TApp T7 t6) => (TApp (shift_TyVar_Ty c T7) (shift_TyVar_Tm c t6))
    end
  with shift_TyVar_Tm (c : (Cutoff TyVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x11) => (Var x11)
      | (Abs T5 t6) => (Abs (shift_TyVar_Ty c T5) (shift_TyVar_Tm c t6))
      | (App t7 t8) => (App (shift_TyVar_Tm c t7) (shift_TyVar_Tm c t8))
      | (Let d8 t9) => (Let (shift_TyVar_Decls c d8) (shift_TyVar_Tm (weakenCutoffTyVar c (appendHvl H0 (bind d8))) t9))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenDecls (d8 : Decls) (k : Hvl) {struct k} :
  Decls :=
    match k with
      | (H0) => d8
      | (HS TmVar k) => (shift_TmVar_Decls C0 (weakenDecls d8 k))
      | (HS TyVar k) => (shift_TyVar_Decls C0 (weakenDecls d8 k))
    end.
  Fixpoint weakenKind (K3 : Kind) (k : Hvl) {struct k} :
  Kind :=
    match k with
      | (H0) => K3
      | (HS TmVar k) => (shift_TmVar_Kind C0 (weakenKind K3 k))
      | (HS TyVar k) => (shift_TyVar_Kind C0 (weakenKind K3 k))
    end.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S0
      | (HS TmVar k) => (shift_TmVar_Ty C0 (weakenTy S0 k))
      | (HS TyVar k) => (shift_TyVar_Ty C0 (weakenTy S0 k))
    end.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} :
  Tm :=
    match k with
      | (H0) => s
      | (HS TmVar k) => (shift_TmVar_Tm C0 (weakenTm s k))
      | (HS TyVar k) => (shift_TyVar_Tm C0 (weakenTm s k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T5 : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x11 : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x11
      | (HS b k) => (XS b (weakenTrace x11 k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x11 : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x11 k) k0) = (weakenTrace x11 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint subst_TmVar_Index (d8 : (Trace TmVar)) (s : Tm) (x11 : (Index TmVar)) {struct d8} :
  Tm :=
    match d8 with
      | (X0) => match x11 with
        | (I0) => s
        | (IS x11) => (Var x11)
      end
      | (XS TmVar d8) => match x11 with
        | (I0) => (Var I0)
        | (IS x11) => (shift_TmVar_Tm C0 (subst_TmVar_Index d8 s x11))
      end
      | (XS TyVar d8) => (shift_TyVar_Tm C0 (subst_TmVar_Index d8 s x11))
    end.
  Fixpoint subst_TyVar_Index (d8 : (Trace TyVar)) (S0 : Ty) (X7 : (Index TyVar)) {struct d8} :
  Ty :=
    match d8 with
      | (X0) => match X7 with
        | (I0) => S0
        | (IS X7) => (TVar X7)
      end
      | (XS TmVar d8) => (shift_TmVar_Ty C0 (subst_TyVar_Index d8 S0 X7))
      | (XS TyVar d8) => match X7 with
        | (I0) => (TVar I0)
        | (IS X7) => (shift_TyVar_Ty C0 (subst_TyVar_Index d8 S0 X7))
      end
    end.
  Fixpoint subst_TmVar_Decls (d8 : (Trace TmVar)) (s : Tm) (d9 : Decls) {struct d9} :
  Decls :=
    match d9 with
      | (DNil) => (DNil)
      | (DConsTm t6 d10) => (DConsTm (subst_TmVar_Tm d8 s t6) (subst_TmVar_Decls (weakenTrace d8 (HS TmVar H0)) s d10))
      | (DConsTy K3 d11) => (DConsTy (subst_TmVar_Kind d8 s K3) (subst_TmVar_Decls (weakenTrace d8 (HS TyVar H0)) s d11))
    end
  with subst_TmVar_Kind (d8 : (Trace TmVar)) (s : Tm) (K3 : Kind) {struct K3} :
  Kind :=
    match K3 with
      | (Star) => (Star)
      | (KPi T5 K4) => (KPi (subst_TmVar_Ty d8 s T5) (subst_TmVar_Kind (weakenTrace d8 (HS TmVar H0)) s K4))
    end
  with subst_TmVar_Ty (d8 : (Trace TmVar)) (s : Tm) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (TVar X7) => (TVar X7)
      | (TPi T5 T6) => (TPi (subst_TmVar_Ty d8 s T5) (subst_TmVar_Ty (weakenTrace d8 (HS TmVar H0)) s T6))
      | (TApp T7 t6) => (TApp (subst_TmVar_Ty d8 s T7) (subst_TmVar_Tm d8 s t6))
    end
  with subst_TmVar_Tm (d8 : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (Var x11) => (subst_TmVar_Index d8 s x11)
      | (Abs T5 t6) => (Abs (subst_TmVar_Ty d8 s T5) (subst_TmVar_Tm (weakenTrace d8 (HS TmVar H0)) s t6))
      | (App t7 t8) => (App (subst_TmVar_Tm d8 s t7) (subst_TmVar_Tm d8 s t8))
      | (Let d9 t9) => (Let (subst_TmVar_Decls d8 s d9) (subst_TmVar_Tm (weakenTrace d8 (appendHvl H0 (bind d9))) s t9))
    end.
  Fixpoint subst_TyVar_Decls (d8 : (Trace TyVar)) (S0 : Ty) (d9 : Decls) {struct d9} :
  Decls :=
    match d9 with
      | (DNil) => (DNil)
      | (DConsTm t6 d10) => (DConsTm (subst_TyVar_Tm d8 S0 t6) (subst_TyVar_Decls (weakenTrace d8 (HS TmVar H0)) S0 d10))
      | (DConsTy K3 d11) => (DConsTy (subst_TyVar_Kind d8 S0 K3) (subst_TyVar_Decls (weakenTrace d8 (HS TyVar H0)) S0 d11))
    end
  with subst_TyVar_Kind (d8 : (Trace TyVar)) (S0 : Ty) (K3 : Kind) {struct K3} :
  Kind :=
    match K3 with
      | (Star) => (Star)
      | (KPi T5 K4) => (KPi (subst_TyVar_Ty d8 S0 T5) (subst_TyVar_Kind (weakenTrace d8 (HS TmVar H0)) S0 K4))
    end
  with subst_TyVar_Ty (d8 : (Trace TyVar)) (S0 : Ty) (S1 : Ty) {struct S1} :
  Ty :=
    match S1 with
      | (TVar X7) => (subst_TyVar_Index d8 S0 X7)
      | (TPi T5 T6) => (TPi (subst_TyVar_Ty d8 S0 T5) (subst_TyVar_Ty (weakenTrace d8 (HS TmVar H0)) S0 T6))
      | (TApp T7 t6) => (TApp (subst_TyVar_Ty d8 S0 T7) (subst_TyVar_Tm d8 S0 t6))
    end
  with subst_TyVar_Tm (d8 : (Trace TyVar)) (S0 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x11) => (Var x11)
      | (Abs T5 t6) => (Abs (subst_TyVar_Ty d8 S0 T5) (subst_TyVar_Tm (weakenTrace d8 (HS TmVar H0)) S0 t6))
      | (App t7 t8) => (App (subst_TyVar_Tm d8 S0 t7) (subst_TyVar_Tm d8 S0 t8))
      | (Let d9 t9) => (Let (subst_TyVar_Decls d8 S0 d9) (subst_TyVar_Tm (weakenTrace d8 (appendHvl H0 (bind d9))) S0 t9))
    end.
End Subst.

Global Hint Resolve (f_equal (shift_TmVar_Decls C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TyVar_Decls C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TmVar_Kind C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TyVar_Kind C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TmVar_Tm C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TyVar_Tm C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TmVar_Ty C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TyVar_Ty C0)) : cong_shift0.
 Hint Rewrite weakenCutoffTmVar_append weakenCutoffTyVar_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_shift_TmVar__bind  :
  (forall (d8 : Decls) ,
    (forall (c : (Cutoff TmVar)) ,
      ((bind (shift_TmVar_Decls c d8)) = (bind d8)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
Lemma stability_shift_TyVar__bind  :
  (forall (d9 : Decls) ,
    (forall (c0 : (Cutoff TyVar)) ,
      ((bind (shift_TyVar_Decls c0 d9)) = (bind d9)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_shift_TmVar__bind stability_shift_TyVar__bind : interaction.
 Hint Rewrite stability_shift_TmVar__bind stability_shift_TyVar__bind : stability_shift.
Lemma stability_weaken_bind  :
  (forall (k : Hvl) (d10 : Decls) ,
    ((bind (weakenDecls d10 k)) = (bind d10))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bind : interaction.
 Hint Rewrite stability_weaken_bind : stability_weaken.
Lemma stability_subst_TmVar__bind  :
  (forall (d10 : Decls) ,
    (forall (d11 : (Trace TmVar)) (s : Tm) ,
      ((bind (subst_TmVar_Decls d11 s d10)) = (bind d10)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
Lemma stability_subst_TyVar__bind  :
  (forall (d12 : Decls) ,
    (forall (d13 : (Trace TyVar)) (S0 : Ty) ,
      ((bind (subst_TyVar_Decls d13 S0 d12)) = (bind d12)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_subst_TmVar__bind stability_subst_TyVar__bind : interaction.
 Hint Rewrite stability_subst_TmVar__bind stability_subst_TyVar__bind : stability_subst.
Section SubstShiftReflection.
  Lemma subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind (s0 : Tm) :
    (forall (k : Hvl) (x11 : (Index TmVar)) ,
      ((subst_TmVar_Index (weakenTrace X0 k) s0 (shift_TmVar_Index (weakenCutoffTmVar C0 k) x11)) = (Var x11))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma subst_TyVar_Index0_shift_TyVar_Index0_reflection_ind (S1 : Ty) :
    (forall (k : Hvl) (X7 : (Index TyVar)) ,
      ((subst_TyVar_Index (weakenTrace X0 k) S1 (shift_TyVar_Index (weakenCutoffTyVar C0 k) X7)) = (TVar X7))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst_TmVar_0_shift_TmVar_0_Decls_reflection_ind (d14 : Decls) (k : Hvl) (s0 : Tm) {struct d14} :
  ((subst_TmVar_Decls (weakenTrace X0 k) s0 (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d14)) = d14) :=
    match d14 return ((subst_TmVar_Decls (weakenTrace X0 k) s0 (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d14)) = d14) with
      | (DNil) => eq_refl
      | (DConsTm t6 d15) => (f_equal2 DConsTm (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t6 k s0) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Decls_reflection_ind d15 (HS TmVar k) s0)))
      | (DConsTy K3 d15) => (f_equal2 DConsTy (subst_TmVar_0_shift_TmVar_0_Kind_reflection_ind K3 k s0) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Decls_reflection_ind d15 (HS TyVar k) s0)))
    end
  with subst_TmVar_0_shift_TmVar_0_Kind_reflection_ind (K4 : Kind) (k : Hvl) (s0 : Tm) {struct K4} :
  ((subst_TmVar_Kind (weakenTrace X0 k) s0 (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K4)) = K4) :=
    match K4 return ((subst_TmVar_Kind (weakenTrace X0 k) s0 (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K4)) = K4) with
      | (Star) => eq_refl
      | (KPi T5 K5) => (f_equal2 KPi (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T5 k s0) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Kind_reflection_ind K5 (HS TmVar k) s0)))
    end
  with subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind (S1 : Ty) (k : Hvl) (s0 : Tm) {struct S1} :
  ((subst_TmVar_Ty (weakenTrace X0 k) s0 (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S1)) = S1) :=
    match S1 return ((subst_TmVar_Ty (weakenTrace X0 k) s0 (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S1)) = S1) with
      | (TVar X8) => eq_refl
      | (TPi T7 T8) => (f_equal2 TPi (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T7 k s0) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T8 (HS TmVar k) s0)))
      | (TApp T6 t7) => (f_equal2 TApp (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T6 k s0) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t7 k s0))
    end
  with subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind (s1 : Tm) (k : Hvl) (s0 : Tm) {struct s1} :
  ((subst_TmVar_Tm (weakenTrace X0 k) s0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s1)) = s1) :=
    match s1 return ((subst_TmVar_Tm (weakenTrace X0 k) s0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s1)) = s1) with
      | (Var x14) => (subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind s0 k x14)
      | (Abs T9 t8) => (f_equal2 Abs (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind T9 k s0) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t8 (HS TmVar k) s0)))
      | (App t9 t10) => (f_equal2 App (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t9 k s0) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t10 k s0))
      | (Let d16 t8) => (f_equal2 Let (subst_TmVar_0_shift_TmVar_0_Decls_reflection_ind d16 k s0) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d16)))) eq_refl (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d16))) eq_refl)) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t8 (appendHvl k (appendHvl H0 (bind d16))) s0)))
    end.
  Fixpoint subst_TyVar_0_shift_TyVar_0_Decls_reflection_ind (d14 : Decls) (k : Hvl) (S1 : Ty) {struct d14} :
  ((subst_TyVar_Decls (weakenTrace X0 k) S1 (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d14)) = d14) :=
    match d14 return ((subst_TyVar_Decls (weakenTrace X0 k) S1 (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d14)) = d14) with
      | (DNil) => eq_refl
      | (DConsTm t6 d15) => (f_equal2 DConsTm (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t6 k S1) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Decls_reflection_ind d15 (HS TmVar k) S1)))
      | (DConsTy K3 d15) => (f_equal2 DConsTy (subst_TyVar_0_shift_TyVar_0_Kind_reflection_ind K3 k S1) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Decls_reflection_ind d15 (HS TyVar k) S1)))
    end
  with subst_TyVar_0_shift_TyVar_0_Kind_reflection_ind (K4 : Kind) (k : Hvl) (S1 : Ty) {struct K4} :
  ((subst_TyVar_Kind (weakenTrace X0 k) S1 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K4)) = K4) :=
    match K4 return ((subst_TyVar_Kind (weakenTrace X0 k) S1 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K4)) = K4) with
      | (Star) => eq_refl
      | (KPi T5 K5) => (f_equal2 KPi (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T5 k S1) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Kind_reflection_ind K5 (HS TmVar k) S1)))
    end
  with subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind (S2 : Ty) (k : Hvl) (S1 : Ty) {struct S2} :
  ((subst_TyVar_Ty (weakenTrace X0 k) S1 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S2)) = S2) :=
    match S2 return ((subst_TyVar_Ty (weakenTrace X0 k) S1 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S2)) = S2) with
      | (TVar X8) => (subst_TyVar_Index0_shift_TyVar_Index0_reflection_ind S1 k X8)
      | (TPi T7 T8) => (f_equal2 TPi (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T7 k S1) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T8 (HS TmVar k) S1)))
      | (TApp T6 t7) => (f_equal2 TApp (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T6 k S1) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t7 k S1))
    end
  with subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (S1 : Ty) {struct s0} :
  ((subst_TyVar_Tm (weakenTrace X0 k) S1 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = s0) :=
    match s0 return ((subst_TyVar_Tm (weakenTrace X0 k) S1 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = s0) with
      | (Var x14) => eq_refl
      | (Abs T9 t8) => (f_equal2 Abs (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T9 k S1) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t8 (HS TmVar k) S1)))
      | (App t9 t10) => (f_equal2 App (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t9 k S1) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t10 k S1))
      | (Let d16 t8) => (f_equal2 Let (subst_TyVar_0_shift_TyVar_0_Decls_reflection_ind d16 k S1) (eq_trans (f_equal3 subst_TyVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TyVar__bind _ _))) (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d16)))) eq_refl (f_equal2 shift_TyVar_Tm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d16))) eq_refl)) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t8 (appendHvl k (appendHvl H0 (bind d16))) S1)))
    end.
  Definition subst_TmVar_Decls0_shift_TmVar_Decls0_reflection (d14 : Decls) : (forall (s0 : Tm) ,
    ((subst_TmVar_Decls X0 s0 (shift_TmVar_Decls C0 d14)) = d14)) := (subst_TmVar_0_shift_TmVar_0_Decls_reflection_ind d14 H0).
  Definition subst_TmVar_Kind0_shift_TmVar_Kind0_reflection (K3 : Kind) : (forall (s0 : Tm) ,
    ((subst_TmVar_Kind X0 s0 (shift_TmVar_Kind C0 K3)) = K3)) := (subst_TmVar_0_shift_TmVar_0_Kind_reflection_ind K3 H0).
  Definition subst_TmVar_Ty0_shift_TmVar_Ty0_reflection (S1 : Ty) : (forall (s0 : Tm) ,
    ((subst_TmVar_Ty X0 s0 (shift_TmVar_Ty C0 S1)) = S1)) := (subst_TmVar_0_shift_TmVar_0_Ty_reflection_ind S1 H0).
  Definition subst_TmVar_Tm0_shift_TmVar_Tm0_reflection (s1 : Tm) : (forall (s0 : Tm) ,
    ((subst_TmVar_Tm X0 s0 (shift_TmVar_Tm C0 s1)) = s1)) := (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind s1 H0).
  Definition subst_TyVar_Decls0_shift_TyVar_Decls0_reflection (d14 : Decls) : (forall (S1 : Ty) ,
    ((subst_TyVar_Decls X0 S1 (shift_TyVar_Decls C0 d14)) = d14)) := (subst_TyVar_0_shift_TyVar_0_Decls_reflection_ind d14 H0).
  Definition subst_TyVar_Kind0_shift_TyVar_Kind0_reflection (K3 : Kind) : (forall (S1 : Ty) ,
    ((subst_TyVar_Kind X0 S1 (shift_TyVar_Kind C0 K3)) = K3)) := (subst_TyVar_0_shift_TyVar_0_Kind_reflection_ind K3 H0).
  Definition subst_TyVar_Ty0_shift_TyVar_Ty0_reflection (S2 : Ty) : (forall (S1 : Ty) ,
    ((subst_TyVar_Ty X0 S1 (shift_TyVar_Ty C0 S2)) = S2)) := (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind S2 H0).
  Definition subst_TyVar_Tm0_shift_TyVar_Tm0_reflection (s0 : Tm) : (forall (S1 : Ty) ,
    ((subst_TyVar_Tm X0 S1 (shift_TyVar_Tm C0 s0)) = s0)) := (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind s0 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shift_TmVar_Index_shift_TmVar_Index0_comm_ind  :
      (forall (k : Hvl) (c1 : (Cutoff TmVar)) (x11 : (Index TmVar)) ,
        ((shift_TmVar_Index (weakenCutoffTmVar (CS c1) k) (shift_TmVar_Index (weakenCutoffTmVar C0 k) x11)) = (shift_TmVar_Index (weakenCutoffTmVar C0 k) (shift_TmVar_Index (weakenCutoffTmVar c1 k) x11)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma shift_TyVar_Index_shift_TyVar_Index0_comm_ind  :
      (forall (k : Hvl) (c1 : (Cutoff TyVar)) (X7 : (Index TyVar)) ,
        ((shift_TyVar_Index (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Index (weakenCutoffTyVar C0 k) X7)) = (shift_TyVar_Index (weakenCutoffTyVar C0 k) (shift_TyVar_Index (weakenCutoffTyVar c1 k) X7)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint shift_TmVar__shift_TmVar_0_Decls_comm_ind (d14 : Decls) (k : Hvl) (c1 : (Cutoff TmVar)) {struct d14} :
    ((shift_TmVar_Decls (weakenCutoffTmVar (CS c1) k) (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d14)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (shift_TmVar_Decls (weakenCutoffTmVar c1 k) d14))) :=
      match d14 return ((shift_TmVar_Decls (weakenCutoffTmVar (CS c1) k) (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d14)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (shift_TmVar_Decls (weakenCutoffTmVar c1 k) d14))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d15) => (f_equal2 DConsTm (shift_TmVar__shift_TmVar_0_Tm_comm_ind t6 k c1) (shift_TmVar__shift_TmVar_0_Decls_comm_ind d15 (HS TmVar k) c1))
        | (DConsTy K3 d15) => (f_equal2 DConsTy (shift_TmVar__shift_TmVar_0_Kind_comm_ind K3 k c1) (shift_TmVar__shift_TmVar_0_Decls_comm_ind d15 (HS TyVar k) c1))
      end
    with shift_TmVar__shift_TmVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (c1 : (Cutoff TmVar)) {struct K4} :
    ((shift_TmVar_Kind (weakenCutoffTmVar (CS c1) k) (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K4)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (shift_TmVar_Kind (weakenCutoffTmVar c1 k) K4))) :=
      match K4 return ((shift_TmVar_Kind (weakenCutoffTmVar (CS c1) k) (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K4)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (shift_TmVar_Kind (weakenCutoffTmVar c1 k) K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (shift_TmVar__shift_TmVar_0_Ty_comm_ind T5 k c1) (shift_TmVar__shift_TmVar_0_Kind_comm_ind K5 (HS TmVar k) c1))
      end
    with shift_TmVar__shift_TmVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c1 : (Cutoff TmVar)) {struct S1} :
    ((shift_TmVar_Ty (weakenCutoffTmVar (CS c1) k) (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S1)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (shift_TmVar_Ty (weakenCutoffTmVar c1 k) S1))) :=
      match S1 return ((shift_TmVar_Ty (weakenCutoffTmVar (CS c1) k) (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S1)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (shift_TmVar_Ty (weakenCutoffTmVar c1 k) S1))) with
        | (TVar X8) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (shift_TmVar__shift_TmVar_0_Ty_comm_ind T7 k c1) (shift_TmVar__shift_TmVar_0_Ty_comm_ind T8 (HS TmVar k) c1))
        | (TApp T6 t7) => (f_equal2 TApp (shift_TmVar__shift_TmVar_0_Ty_comm_ind T6 k c1) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t7 k c1))
      end
    with shift_TmVar__shift_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff TmVar)) {struct s0} :
    ((shift_TmVar_Tm (weakenCutoffTmVar (CS c1) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c1 k) s0))) :=
      match s0 return ((shift_TmVar_Tm (weakenCutoffTmVar (CS c1) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c1 k) s0))) with
        | (Var x14) => (f_equal Var (shift_TmVar_Index_shift_TmVar_Index0_comm_ind k c1 x14))
        | (Abs T9 t8) => (f_equal2 Abs (shift_TmVar__shift_TmVar_0_Ty_comm_ind T9 k c1) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t8 (HS TmVar k) c1))
        | (App t9 t10) => (f_equal2 App (shift_TmVar__shift_TmVar_0_Tm_comm_ind t9 k c1) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t10 k c1))
        | (Let d16 t8) => (f_equal2 Let (shift_TmVar__shift_TmVar_0_Decls_comm_ind d16 k c1) (eq_trans (f_equal2 shift_TmVar_Tm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenCutoffTmVar_append (CS c1) k (appendHvl H0 (bind d16)))) (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d16))) eq_refl)) (eq_trans (shift_TmVar__shift_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d16))) c1) (f_equal2 shift_TmVar_Tm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d16)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _))))) (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append c1 k (appendHvl H0 (bind d16)))) eq_refl)))))
      end.
    Fixpoint shift_TmVar__shift_TyVar_0_Decls_comm_ind (d14 : Decls) (k : Hvl) (c1 : (Cutoff TmVar)) {struct d14} :
    ((shift_TmVar_Decls (weakenCutoffTmVar c1 k) (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d14)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (shift_TmVar_Decls (weakenCutoffTmVar c1 k) d14))) :=
      match d14 return ((shift_TmVar_Decls (weakenCutoffTmVar c1 k) (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d14)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (shift_TmVar_Decls (weakenCutoffTmVar c1 k) d14))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d15) => (f_equal2 DConsTm (shift_TmVar__shift_TyVar_0_Tm_comm_ind t6 k c1) (shift_TmVar__shift_TyVar_0_Decls_comm_ind d15 (HS TmVar k) c1))
        | (DConsTy K3 d15) => (f_equal2 DConsTy (shift_TmVar__shift_TyVar_0_Kind_comm_ind K3 k c1) (shift_TmVar__shift_TyVar_0_Decls_comm_ind d15 (HS TyVar k) c1))
      end
    with shift_TmVar__shift_TyVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (c1 : (Cutoff TmVar)) {struct K4} :
    ((shift_TmVar_Kind (weakenCutoffTmVar c1 k) (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K4)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (shift_TmVar_Kind (weakenCutoffTmVar c1 k) K4))) :=
      match K4 return ((shift_TmVar_Kind (weakenCutoffTmVar c1 k) (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K4)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (shift_TmVar_Kind (weakenCutoffTmVar c1 k) K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (shift_TmVar__shift_TyVar_0_Ty_comm_ind T5 k c1) (shift_TmVar__shift_TyVar_0_Kind_comm_ind K5 (HS TmVar k) c1))
      end
    with shift_TmVar__shift_TyVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c1 : (Cutoff TmVar)) {struct S1} :
    ((shift_TmVar_Ty (weakenCutoffTmVar c1 k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TmVar_Ty (weakenCutoffTmVar c1 k) S1))) :=
      match S1 return ((shift_TmVar_Ty (weakenCutoffTmVar c1 k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TmVar_Ty (weakenCutoffTmVar c1 k) S1))) with
        | (TVar X8) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (shift_TmVar__shift_TyVar_0_Ty_comm_ind T7 k c1) (shift_TmVar__shift_TyVar_0_Ty_comm_ind T8 (HS TmVar k) c1))
        | (TApp T6 t7) => (f_equal2 TApp (shift_TmVar__shift_TyVar_0_Ty_comm_ind T6 k c1) (shift_TmVar__shift_TyVar_0_Tm_comm_ind t7 k c1))
      end
    with shift_TmVar__shift_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff TmVar)) {struct s0} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c1 k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c1 k) s0))) :=
      match s0 return ((shift_TmVar_Tm (weakenCutoffTmVar c1 k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c1 k) s0))) with
        | (Var x14) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs (shift_TmVar__shift_TyVar_0_Ty_comm_ind T9 k c1) (shift_TmVar__shift_TyVar_0_Tm_comm_ind t8 (HS TmVar k) c1))
        | (App t9 t10) => (f_equal2 App (shift_TmVar__shift_TyVar_0_Tm_comm_ind t9 k c1) (shift_TmVar__shift_TyVar_0_Tm_comm_ind t10 k c1))
        | (Let d16 t8) => (f_equal2 Let (shift_TmVar__shift_TyVar_0_Decls_comm_ind d16 k c1) (eq_trans (f_equal2 shift_TmVar_Tm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TyVar__bind _ _))) (weakenCutoffTmVar_append c1 k (appendHvl H0 (bind d16)))) (f_equal2 shift_TyVar_Tm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d16))) eq_refl)) (eq_trans (shift_TmVar__shift_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d16))) c1) (f_equal2 shift_TyVar_Tm (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d16)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _))))) (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append c1 k (appendHvl H0 (bind d16)))) eq_refl)))))
      end.
    Fixpoint shift_TyVar__shift_TmVar_0_Decls_comm_ind (d14 : Decls) (k : Hvl) (c1 : (Cutoff TyVar)) {struct d14} :
    ((shift_TyVar_Decls (weakenCutoffTyVar c1 k) (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d14)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (shift_TyVar_Decls (weakenCutoffTyVar c1 k) d14))) :=
      match d14 return ((shift_TyVar_Decls (weakenCutoffTyVar c1 k) (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d14)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (shift_TyVar_Decls (weakenCutoffTyVar c1 k) d14))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d15) => (f_equal2 DConsTm (shift_TyVar__shift_TmVar_0_Tm_comm_ind t6 k c1) (shift_TyVar__shift_TmVar_0_Decls_comm_ind d15 (HS TmVar k) c1))
        | (DConsTy K3 d15) => (f_equal2 DConsTy (shift_TyVar__shift_TmVar_0_Kind_comm_ind K3 k c1) (shift_TyVar__shift_TmVar_0_Decls_comm_ind d15 (HS TyVar k) c1))
      end
    with shift_TyVar__shift_TmVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (c1 : (Cutoff TyVar)) {struct K4} :
    ((shift_TyVar_Kind (weakenCutoffTyVar c1 k) (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K4)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (shift_TyVar_Kind (weakenCutoffTyVar c1 k) K4))) :=
      match K4 return ((shift_TyVar_Kind (weakenCutoffTyVar c1 k) (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K4)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (shift_TyVar_Kind (weakenCutoffTyVar c1 k) K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (shift_TyVar__shift_TmVar_0_Ty_comm_ind T5 k c1) (shift_TyVar__shift_TmVar_0_Kind_comm_ind K5 (HS TmVar k) c1))
      end
    with shift_TyVar__shift_TmVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c1 : (Cutoff TyVar)) {struct S1} :
    ((shift_TyVar_Ty (weakenCutoffTyVar c1 k) (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S1)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c1 k) S1))) :=
      match S1 return ((shift_TyVar_Ty (weakenCutoffTyVar c1 k) (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S1)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c1 k) S1))) with
        | (TVar X8) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (shift_TyVar__shift_TmVar_0_Ty_comm_ind T7 k c1) (shift_TyVar__shift_TmVar_0_Ty_comm_ind T8 (HS TmVar k) c1))
        | (TApp T6 t7) => (f_equal2 TApp (shift_TyVar__shift_TmVar_0_Ty_comm_ind T6 k c1) (shift_TyVar__shift_TmVar_0_Tm_comm_ind t7 k c1))
      end
    with shift_TyVar__shift_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff TyVar)) {struct s0} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c1 k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c1 k) s0))) :=
      match s0 return ((shift_TyVar_Tm (weakenCutoffTyVar c1 k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c1 k) s0))) with
        | (Var x14) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs (shift_TyVar__shift_TmVar_0_Ty_comm_ind T9 k c1) (shift_TyVar__shift_TmVar_0_Tm_comm_ind t8 (HS TmVar k) c1))
        | (App t9 t10) => (f_equal2 App (shift_TyVar__shift_TmVar_0_Tm_comm_ind t9 k c1) (shift_TyVar__shift_TmVar_0_Tm_comm_ind t10 k c1))
        | (Let d16 t8) => (f_equal2 Let (shift_TyVar__shift_TmVar_0_Decls_comm_ind d16 k c1) (eq_trans (f_equal2 shift_TyVar_Tm (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenCutoffTyVar_append c1 k (appendHvl H0 (bind d16)))) (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d16))) eq_refl)) (eq_trans (shift_TyVar__shift_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d16))) c1) (f_equal2 shift_TmVar_Tm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d16)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TyVar__bind _ _))))) (f_equal2 shift_TyVar_Tm (eq_sym (weakenCutoffTyVar_append c1 k (appendHvl H0 (bind d16)))) eq_refl)))))
      end.
    Fixpoint shift_TyVar__shift_TyVar_0_Decls_comm_ind (d14 : Decls) (k : Hvl) (c1 : (Cutoff TyVar)) {struct d14} :
    ((shift_TyVar_Decls (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d14)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (shift_TyVar_Decls (weakenCutoffTyVar c1 k) d14))) :=
      match d14 return ((shift_TyVar_Decls (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d14)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (shift_TyVar_Decls (weakenCutoffTyVar c1 k) d14))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d15) => (f_equal2 DConsTm (shift_TyVar__shift_TyVar_0_Tm_comm_ind t6 k c1) (shift_TyVar__shift_TyVar_0_Decls_comm_ind d15 (HS TmVar k) c1))
        | (DConsTy K3 d15) => (f_equal2 DConsTy (shift_TyVar__shift_TyVar_0_Kind_comm_ind K3 k c1) (shift_TyVar__shift_TyVar_0_Decls_comm_ind d15 (HS TyVar k) c1))
      end
    with shift_TyVar__shift_TyVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (c1 : (Cutoff TyVar)) {struct K4} :
    ((shift_TyVar_Kind (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K4)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (shift_TyVar_Kind (weakenCutoffTyVar c1 k) K4))) :=
      match K4 return ((shift_TyVar_Kind (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K4)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (shift_TyVar_Kind (weakenCutoffTyVar c1 k) K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (shift_TyVar__shift_TyVar_0_Ty_comm_ind T5 k c1) (shift_TyVar__shift_TyVar_0_Kind_comm_ind K5 (HS TmVar k) c1))
      end
    with shift_TyVar__shift_TyVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c1 : (Cutoff TyVar)) {struct S1} :
    ((shift_TyVar_Ty (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c1 k) S1))) :=
      match S1 return ((shift_TyVar_Ty (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c1 k) S1))) with
        | (TVar X8) => (f_equal TVar (shift_TyVar_Index_shift_TyVar_Index0_comm_ind k c1 X8))
        | (TPi T7 T8) => (f_equal2 TPi (shift_TyVar__shift_TyVar_0_Ty_comm_ind T7 k c1) (shift_TyVar__shift_TyVar_0_Ty_comm_ind T8 (HS TmVar k) c1))
        | (TApp T6 t7) => (f_equal2 TApp (shift_TyVar__shift_TyVar_0_Ty_comm_ind T6 k c1) (shift_TyVar__shift_TyVar_0_Tm_comm_ind t7 k c1))
      end
    with shift_TyVar__shift_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff TyVar)) {struct s0} :
    ((shift_TyVar_Tm (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c1 k) s0))) :=
      match s0 return ((shift_TyVar_Tm (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c1 k) s0))) with
        | (Var x14) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs (shift_TyVar__shift_TyVar_0_Ty_comm_ind T9 k c1) (shift_TyVar__shift_TyVar_0_Tm_comm_ind t8 (HS TmVar k) c1))
        | (App t9 t10) => (f_equal2 App (shift_TyVar__shift_TyVar_0_Tm_comm_ind t9 k c1) (shift_TyVar__shift_TyVar_0_Tm_comm_ind t10 k c1))
        | (Let d16 t8) => (f_equal2 Let (shift_TyVar__shift_TyVar_0_Decls_comm_ind d16 k c1) (eq_trans (f_equal2 shift_TyVar_Tm (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TyVar__bind _ _))) (weakenCutoffTyVar_append (CS c1) k (appendHvl H0 (bind d16)))) (f_equal2 shift_TyVar_Tm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d16))) eq_refl)) (eq_trans (shift_TyVar__shift_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d16))) c1) (f_equal2 shift_TyVar_Tm (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d16)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TyVar__bind _ _))))) (f_equal2 shift_TyVar_Tm (eq_sym (weakenCutoffTyVar_append c1 k (appendHvl H0 (bind d16)))) eq_refl)))))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition shift_TmVar__shift_TmVar_0_Decls_comm (d14 : Decls) : (forall (c1 : (Cutoff TmVar)) ,
      ((shift_TmVar_Decls (CS c1) (shift_TmVar_Decls C0 d14)) = (shift_TmVar_Decls C0 (shift_TmVar_Decls c1 d14)))) := (shift_TmVar__shift_TmVar_0_Decls_comm_ind d14 H0).
    Definition shift_TmVar__shift_TmVar_0_Kind_comm (K3 : Kind) : (forall (c1 : (Cutoff TmVar)) ,
      ((shift_TmVar_Kind (CS c1) (shift_TmVar_Kind C0 K3)) = (shift_TmVar_Kind C0 (shift_TmVar_Kind c1 K3)))) := (shift_TmVar__shift_TmVar_0_Kind_comm_ind K3 H0).
    Definition shift_TmVar__shift_TmVar_0_Ty_comm (S1 : Ty) : (forall (c1 : (Cutoff TmVar)) ,
      ((shift_TmVar_Ty (CS c1) (shift_TmVar_Ty C0 S1)) = (shift_TmVar_Ty C0 (shift_TmVar_Ty c1 S1)))) := (shift_TmVar__shift_TmVar_0_Ty_comm_ind S1 H0).
    Definition shift_TmVar__shift_TmVar_0_Tm_comm (s0 : Tm) : (forall (c1 : (Cutoff TmVar)) ,
      ((shift_TmVar_Tm (CS c1) (shift_TmVar_Tm C0 s0)) = (shift_TmVar_Tm C0 (shift_TmVar_Tm c1 s0)))) := (shift_TmVar__shift_TmVar_0_Tm_comm_ind s0 H0).
    Definition shift_TmVar__shift_TyVar_0_Decls_comm (d14 : Decls) : (forall (c1 : (Cutoff TmVar)) ,
      ((shift_TmVar_Decls c1 (shift_TyVar_Decls C0 d14)) = (shift_TyVar_Decls C0 (shift_TmVar_Decls c1 d14)))) := (shift_TmVar__shift_TyVar_0_Decls_comm_ind d14 H0).
    Definition shift_TmVar__shift_TyVar_0_Kind_comm (K3 : Kind) : (forall (c1 : (Cutoff TmVar)) ,
      ((shift_TmVar_Kind c1 (shift_TyVar_Kind C0 K3)) = (shift_TyVar_Kind C0 (shift_TmVar_Kind c1 K3)))) := (shift_TmVar__shift_TyVar_0_Kind_comm_ind K3 H0).
    Definition shift_TmVar__shift_TyVar_0_Ty_comm (S1 : Ty) : (forall (c1 : (Cutoff TmVar)) ,
      ((shift_TmVar_Ty c1 (shift_TyVar_Ty C0 S1)) = (shift_TyVar_Ty C0 (shift_TmVar_Ty c1 S1)))) := (shift_TmVar__shift_TyVar_0_Ty_comm_ind S1 H0).
    Definition shift_TmVar__shift_TyVar_0_Tm_comm (s0 : Tm) : (forall (c1 : (Cutoff TmVar)) ,
      ((shift_TmVar_Tm c1 (shift_TyVar_Tm C0 s0)) = (shift_TyVar_Tm C0 (shift_TmVar_Tm c1 s0)))) := (shift_TmVar__shift_TyVar_0_Tm_comm_ind s0 H0).
    Definition shift_TyVar__shift_TmVar_0_Decls_comm (d14 : Decls) : (forall (c1 : (Cutoff TyVar)) ,
      ((shift_TyVar_Decls c1 (shift_TmVar_Decls C0 d14)) = (shift_TmVar_Decls C0 (shift_TyVar_Decls c1 d14)))) := (shift_TyVar__shift_TmVar_0_Decls_comm_ind d14 H0).
    Definition shift_TyVar__shift_TmVar_0_Kind_comm (K3 : Kind) : (forall (c1 : (Cutoff TyVar)) ,
      ((shift_TyVar_Kind c1 (shift_TmVar_Kind C0 K3)) = (shift_TmVar_Kind C0 (shift_TyVar_Kind c1 K3)))) := (shift_TyVar__shift_TmVar_0_Kind_comm_ind K3 H0).
    Definition shift_TyVar__shift_TmVar_0_Ty_comm (S1 : Ty) : (forall (c1 : (Cutoff TyVar)) ,
      ((shift_TyVar_Ty c1 (shift_TmVar_Ty C0 S1)) = (shift_TmVar_Ty C0 (shift_TyVar_Ty c1 S1)))) := (shift_TyVar__shift_TmVar_0_Ty_comm_ind S1 H0).
    Definition shift_TyVar__shift_TmVar_0_Tm_comm (s0 : Tm) : (forall (c1 : (Cutoff TyVar)) ,
      ((shift_TyVar_Tm c1 (shift_TmVar_Tm C0 s0)) = (shift_TmVar_Tm C0 (shift_TyVar_Tm c1 s0)))) := (shift_TyVar__shift_TmVar_0_Tm_comm_ind s0 H0).
    Definition shift_TyVar__shift_TyVar_0_Decls_comm (d14 : Decls) : (forall (c1 : (Cutoff TyVar)) ,
      ((shift_TyVar_Decls (CS c1) (shift_TyVar_Decls C0 d14)) = (shift_TyVar_Decls C0 (shift_TyVar_Decls c1 d14)))) := (shift_TyVar__shift_TyVar_0_Decls_comm_ind d14 H0).
    Definition shift_TyVar__shift_TyVar_0_Kind_comm (K3 : Kind) : (forall (c1 : (Cutoff TyVar)) ,
      ((shift_TyVar_Kind (CS c1) (shift_TyVar_Kind C0 K3)) = (shift_TyVar_Kind C0 (shift_TyVar_Kind c1 K3)))) := (shift_TyVar__shift_TyVar_0_Kind_comm_ind K3 H0).
    Definition shift_TyVar__shift_TyVar_0_Ty_comm (S1 : Ty) : (forall (c1 : (Cutoff TyVar)) ,
      ((shift_TyVar_Ty (CS c1) (shift_TyVar_Ty C0 S1)) = (shift_TyVar_Ty C0 (shift_TyVar_Ty c1 S1)))) := (shift_TyVar__shift_TyVar_0_Ty_comm_ind S1 H0).
    Definition shift_TyVar__shift_TyVar_0_Tm_comm (s0 : Tm) : (forall (c1 : (Cutoff TyVar)) ,
      ((shift_TyVar_Tm (CS c1) (shift_TyVar_Tm C0 s0)) = (shift_TyVar_Tm C0 (shift_TyVar_Tm c1 s0)))) := (shift_TyVar__shift_TyVar_0_Tm_comm_ind s0 H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_TmVar__shift_TmVar_0_Decls_comm shift_TmVar__shift_TyVar_0_Decls_comm shift_TyVar__shift_TmVar_0_Decls_comm shift_TyVar__shift_TyVar_0_Decls_comm shift_TmVar__shift_TmVar_0_Kind_comm shift_TmVar__shift_TyVar_0_Kind_comm shift_TyVar__shift_TmVar_0_Kind_comm shift_TyVar__shift_TyVar_0_Kind_comm shift_TmVar__shift_TmVar_0_Tm_comm shift_TmVar__shift_TyVar_0_Tm_comm shift_TyVar__shift_TmVar_0_Tm_comm shift_TyVar__shift_TyVar_0_Tm_comm shift_TmVar__shift_TmVar_0_Ty_comm shift_TmVar__shift_TyVar_0_Ty_comm shift_TyVar__shift_TmVar_0_Ty_comm shift_TyVar__shift_TyVar_0_Ty_comm : interaction.
 Hint Rewrite shift_TmVar__shift_TmVar_0_Decls_comm shift_TmVar__shift_TyVar_0_Decls_comm shift_TyVar__shift_TmVar_0_Decls_comm shift_TyVar__shift_TyVar_0_Decls_comm shift_TmVar__shift_TmVar_0_Kind_comm shift_TmVar__shift_TyVar_0_Kind_comm shift_TyVar__shift_TmVar_0_Kind_comm shift_TyVar__shift_TyVar_0_Kind_comm shift_TmVar__shift_TmVar_0_Tm_comm shift_TmVar__shift_TyVar_0_Tm_comm shift_TyVar__shift_TmVar_0_Tm_comm shift_TyVar__shift_TyVar_0_Tm_comm shift_TmVar__shift_TmVar_0_Ty_comm shift_TmVar__shift_TyVar_0_Ty_comm shift_TyVar__shift_TmVar_0_Ty_comm shift_TyVar__shift_TyVar_0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenDecls_shift_TmVar_Decls  :
    (forall (k : Hvl) (c1 : (Cutoff TmVar)) (d14 : Decls) ,
      ((weakenDecls (shift_TmVar_Decls c1 d14) k) = (shift_TmVar_Decls (weakenCutoffTmVar c1 k) (weakenDecls d14 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenKind_shift_TmVar_Kind  :
    (forall (k : Hvl) (c1 : (Cutoff TmVar)) (K3 : Kind) ,
      ((weakenKind (shift_TmVar_Kind c1 K3) k) = (shift_TmVar_Kind (weakenCutoffTmVar c1 k) (weakenKind K3 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTy_shift_TmVar_Ty  :
    (forall (k : Hvl) (c1 : (Cutoff TmVar)) (S1 : Ty) ,
      ((weakenTy (shift_TmVar_Ty c1 S1) k) = (shift_TmVar_Ty (weakenCutoffTmVar c1 k) (weakenTy S1 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shift_TmVar_Tm  :
    (forall (k : Hvl) (c1 : (Cutoff TmVar)) (s0 : Tm) ,
      ((weakenTm (shift_TmVar_Tm c1 s0) k) = (shift_TmVar_Tm (weakenCutoffTmVar c1 k) (weakenTm s0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenDecls_shift_TyVar_Decls  :
    (forall (k : Hvl) (c1 : (Cutoff TyVar)) (d14 : Decls) ,
      ((weakenDecls (shift_TyVar_Decls c1 d14) k) = (shift_TyVar_Decls (weakenCutoffTyVar c1 k) (weakenDecls d14 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenKind_shift_TyVar_Kind  :
    (forall (k : Hvl) (c1 : (Cutoff TyVar)) (K3 : Kind) ,
      ((weakenKind (shift_TyVar_Kind c1 K3) k) = (shift_TyVar_Kind (weakenCutoffTyVar c1 k) (weakenKind K3 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTy_shift_TyVar_Ty  :
    (forall (k : Hvl) (c1 : (Cutoff TyVar)) (S1 : Ty) ,
      ((weakenTy (shift_TyVar_Ty c1 S1) k) = (shift_TyVar_Ty (weakenCutoffTyVar c1 k) (weakenTy S1 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shift_TyVar_Tm  :
    (forall (k : Hvl) (c1 : (Cutoff TyVar)) (s0 : Tm) ,
      ((weakenTm (shift_TyVar_Tm c1 s0) k) = (shift_TyVar_Tm (weakenCutoffTyVar c1 k) (weakenTm s0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shift_TmVar_Tm_subst_TmVar_Index0_comm_ind (c1 : (Cutoff TmVar)) (s0 : Tm) :
      (forall (k : Hvl) (x11 : (Index TmVar)) ,
        ((shift_TmVar_Tm (weakenCutoffTmVar c1 k) (subst_TmVar_Index (weakenTrace X0 k) s0 x11)) = (subst_TmVar_Index (weakenTrace X0 k) (shift_TmVar_Tm c1 s0) (shift_TmVar_Index (weakenCutoffTmVar (CS c1) k) x11)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TyVar_Tm_subst_TmVar_Index0_comm_ind (c1 : (Cutoff TyVar)) (s0 : Tm) :
      (forall (k : Hvl) (x11 : (Index TmVar)) ,
        ((shift_TyVar_Tm (weakenCutoffTyVar c1 k) (subst_TmVar_Index (weakenTrace X0 k) s0 x11)) = (subst_TmVar_Index (weakenTrace X0 k) (shift_TyVar_Tm c1 s0) x11))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TmVar_Ty_subst_TyVar_Index0_comm_ind (c1 : (Cutoff TmVar)) (S1 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((shift_TmVar_Ty (weakenCutoffTmVar c1 k) (subst_TyVar_Index (weakenTrace X0 k) S1 X7)) = (subst_TyVar_Index (weakenTrace X0 k) (shift_TmVar_Ty c1 S1) X7))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TyVar_Ty_subst_TyVar_Index0_comm_ind (c1 : (Cutoff TyVar)) (S1 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((shift_TyVar_Ty (weakenCutoffTyVar c1 k) (subst_TyVar_Index (weakenTrace X0 k) S1 X7)) = (subst_TyVar_Index (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Index (weakenCutoffTyVar (CS c1) k) X7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint shift_TmVar__subst_TmVar_0_Decls_comm_ind (d14 : Decls) (k : Hvl) (c1 : (Cutoff TmVar)) (s0 : Tm) {struct d14} :
    ((shift_TmVar_Decls (weakenCutoffTmVar c1 k) (subst_TmVar_Decls (weakenTrace X0 k) s0 d14)) = (subst_TmVar_Decls (weakenTrace X0 k) (shift_TmVar_Tm c1 s0) (shift_TmVar_Decls (weakenCutoffTmVar (CS c1) k) d14))) :=
      match d14 return ((shift_TmVar_Decls (weakenCutoffTmVar c1 k) (subst_TmVar_Decls (weakenTrace X0 k) s0 d14)) = (subst_TmVar_Decls (weakenTrace X0 k) (shift_TmVar_Tm c1 s0) (shift_TmVar_Decls (weakenCutoffTmVar (CS c1) k) d14))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d15) => (f_equal2 DConsTm (shift_TmVar__subst_TmVar_0_Tm_comm_ind t6 k c1 s0) (eq_trans (f_equal2 shift_TmVar_Decls eq_refl (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Decls_comm_ind d15 (HS TmVar k) c1 s0) (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (DConsTy K3 d15) => (f_equal2 DConsTy (shift_TmVar__subst_TmVar_0_Kind_comm_ind K3 k c1 s0) (eq_trans (f_equal2 shift_TmVar_Decls eq_refl (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Decls_comm_ind d15 (HS TyVar k) c1 s0) (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
      end
    with shift_TmVar__subst_TmVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (c1 : (Cutoff TmVar)) (s0 : Tm) {struct K4} :
    ((shift_TmVar_Kind (weakenCutoffTmVar c1 k) (subst_TmVar_Kind (weakenTrace X0 k) s0 K4)) = (subst_TmVar_Kind (weakenTrace X0 k) (shift_TmVar_Tm c1 s0) (shift_TmVar_Kind (weakenCutoffTmVar (CS c1) k) K4))) :=
      match K4 return ((shift_TmVar_Kind (weakenCutoffTmVar c1 k) (subst_TmVar_Kind (weakenTrace X0 k) s0 K4)) = (subst_TmVar_Kind (weakenTrace X0 k) (shift_TmVar_Tm c1 s0) (shift_TmVar_Kind (weakenCutoffTmVar (CS c1) k) K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (shift_TmVar__subst_TmVar_0_Ty_comm_ind T5 k c1 s0) (eq_trans (f_equal2 shift_TmVar_Kind eq_refl (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Kind_comm_ind K5 (HS TmVar k) c1 s0) (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end
    with shift_TmVar__subst_TmVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c1 : (Cutoff TmVar)) (s0 : Tm) {struct S1} :
    ((shift_TmVar_Ty (weakenCutoffTmVar c1 k) (subst_TmVar_Ty (weakenTrace X0 k) s0 S1)) = (subst_TmVar_Ty (weakenTrace X0 k) (shift_TmVar_Tm c1 s0) (shift_TmVar_Ty (weakenCutoffTmVar (CS c1) k) S1))) :=
      match S1 return ((shift_TmVar_Ty (weakenCutoffTmVar c1 k) (subst_TmVar_Ty (weakenTrace X0 k) s0 S1)) = (subst_TmVar_Ty (weakenTrace X0 k) (shift_TmVar_Tm c1 s0) (shift_TmVar_Ty (weakenCutoffTmVar (CS c1) k) S1))) with
        | (TVar X8) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (shift_TmVar__subst_TmVar_0_Ty_comm_ind T7 k c1 s0) (eq_trans (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Ty_comm_ind T8 (HS TmVar k) c1 s0) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (TApp T6 t7) => (f_equal2 TApp (shift_TmVar__subst_TmVar_0_Ty_comm_ind T6 k c1 s0) (shift_TmVar__subst_TmVar_0_Tm_comm_ind t7 k c1 s0))
      end
    with shift_TmVar__subst_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (c1 : (Cutoff TmVar)) (s0 : Tm) {struct s1} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c1 k) (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c1 s0) (shift_TmVar_Tm (weakenCutoffTmVar (CS c1) k) s1))) :=
      match s1 return ((shift_TmVar_Tm (weakenCutoffTmVar c1 k) (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c1 s0) (shift_TmVar_Tm (weakenCutoffTmVar (CS c1) k) s1))) with
        | (Var x14) => (shift_TmVar_Tm_subst_TmVar_Index0_comm_ind c1 s0 k x14)
        | (Abs T9 t8) => (f_equal2 Abs (shift_TmVar__subst_TmVar_0_Ty_comm_ind T9 k c1 s0) (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind t8 (HS TmVar k) c1 s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t9 t10) => (f_equal2 App (shift_TmVar__subst_TmVar_0_Tm_comm_ind t9 k c1 s0) (shift_TmVar__subst_TmVar_0_Tm_comm_ind t10 k c1 s0))
        | (Let d16 t8) => (f_equal2 Let (shift_TmVar__subst_TmVar_0_Decls_comm_ind d16 k c1 s0) (eq_trans (f_equal2 shift_TmVar_Tm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TmVar__bind _ _ _) (eq_refl H0)))) (weakenCutoffTmVar_append c1 k (appendHvl H0 (bind d16)))) (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d16))) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d16))) c1 s0) (f_equal3 subst_TmVar_Tm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d16)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _))))) eq_refl (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append (CS c1) k (appendHvl H0 (bind d16)))) eq_refl)))))
      end.
    Fixpoint shift_TmVar__subst_TyVar_0_Decls_comm_ind (d14 : Decls) (k : Hvl) (c1 : (Cutoff TmVar)) (S1 : Ty) {struct d14} :
    ((shift_TmVar_Decls (weakenCutoffTmVar c1 k) (subst_TyVar_Decls (weakenTrace X0 k) S1 d14)) = (subst_TyVar_Decls (weakenTrace X0 k) (shift_TmVar_Ty c1 S1) (shift_TmVar_Decls (weakenCutoffTmVar c1 k) d14))) :=
      match d14 return ((shift_TmVar_Decls (weakenCutoffTmVar c1 k) (subst_TyVar_Decls (weakenTrace X0 k) S1 d14)) = (subst_TyVar_Decls (weakenTrace X0 k) (shift_TmVar_Ty c1 S1) (shift_TmVar_Decls (weakenCutoffTmVar c1 k) d14))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d15) => (f_equal2 DConsTm (shift_TmVar__subst_TyVar_0_Tm_comm_ind t6 k c1 S1) (eq_trans (f_equal2 shift_TmVar_Decls eq_refl (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Decls_comm_ind d15 (HS TmVar k) c1 S1) (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (DConsTy K3 d15) => (f_equal2 DConsTy (shift_TmVar__subst_TyVar_0_Kind_comm_ind K3 k c1 S1) (eq_trans (f_equal2 shift_TmVar_Decls eq_refl (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Decls_comm_ind d15 (HS TyVar k) c1 S1) (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
      end
    with shift_TmVar__subst_TyVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (c1 : (Cutoff TmVar)) (S1 : Ty) {struct K4} :
    ((shift_TmVar_Kind (weakenCutoffTmVar c1 k) (subst_TyVar_Kind (weakenTrace X0 k) S1 K4)) = (subst_TyVar_Kind (weakenTrace X0 k) (shift_TmVar_Ty c1 S1) (shift_TmVar_Kind (weakenCutoffTmVar c1 k) K4))) :=
      match K4 return ((shift_TmVar_Kind (weakenCutoffTmVar c1 k) (subst_TyVar_Kind (weakenTrace X0 k) S1 K4)) = (subst_TyVar_Kind (weakenTrace X0 k) (shift_TmVar_Ty c1 S1) (shift_TmVar_Kind (weakenCutoffTmVar c1 k) K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (shift_TmVar__subst_TyVar_0_Ty_comm_ind T5 k c1 S1) (eq_trans (f_equal2 shift_TmVar_Kind eq_refl (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Kind_comm_ind K5 (HS TmVar k) c1 S1) (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end
    with shift_TmVar__subst_TyVar_0_Ty_comm_ind (S2 : Ty) (k : Hvl) (c1 : (Cutoff TmVar)) (S1 : Ty) {struct S2} :
    ((shift_TmVar_Ty (weakenCutoffTmVar c1 k) (subst_TyVar_Ty (weakenTrace X0 k) S1 S2)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TmVar_Ty c1 S1) (shift_TmVar_Ty (weakenCutoffTmVar c1 k) S2))) :=
      match S2 return ((shift_TmVar_Ty (weakenCutoffTmVar c1 k) (subst_TyVar_Ty (weakenTrace X0 k) S1 S2)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TmVar_Ty c1 S1) (shift_TmVar_Ty (weakenCutoffTmVar c1 k) S2))) with
        | (TVar X8) => (shift_TmVar_Ty_subst_TyVar_Index0_comm_ind c1 S1 k X8)
        | (TPi T7 T8) => (f_equal2 TPi (shift_TmVar__subst_TyVar_0_Ty_comm_ind T7 k c1 S1) (eq_trans (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Ty_comm_ind T8 (HS TmVar k) c1 S1) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (TApp T6 t7) => (f_equal2 TApp (shift_TmVar__subst_TyVar_0_Ty_comm_ind T6 k c1 S1) (shift_TmVar__subst_TyVar_0_Tm_comm_ind t7 k c1 S1))
      end
    with shift_TmVar__subst_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff TmVar)) (S1 : Ty) {struct s0} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c1 k) (subst_TyVar_Tm (weakenTrace X0 k) S1 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TmVar_Ty c1 S1) (shift_TmVar_Tm (weakenCutoffTmVar c1 k) s0))) :=
      match s0 return ((shift_TmVar_Tm (weakenCutoffTmVar c1 k) (subst_TyVar_Tm (weakenTrace X0 k) S1 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TmVar_Ty c1 S1) (shift_TmVar_Tm (weakenCutoffTmVar c1 k) s0))) with
        | (Var x14) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs (shift_TmVar__subst_TyVar_0_Ty_comm_ind T9 k c1 S1) (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Tm_comm_ind t8 (HS TmVar k) c1 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t9 t10) => (f_equal2 App (shift_TmVar__subst_TyVar_0_Tm_comm_ind t9 k c1 S1) (shift_TmVar__subst_TyVar_0_Tm_comm_ind t10 k c1 S1))
        | (Let d16 t8) => (f_equal2 Let (shift_TmVar__subst_TyVar_0_Decls_comm_ind d16 k c1 S1) (eq_trans (f_equal2 shift_TmVar_Tm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TyVar__bind _ _ _) (eq_refl H0)))) (weakenCutoffTmVar_append c1 k (appendHvl H0 (bind d16)))) (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d16))) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d16))) c1 S1) (f_equal3 subst_TyVar_Tm (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d16)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _))))) eq_refl (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append c1 k (appendHvl H0 (bind d16)))) eq_refl)))))
      end.
    Fixpoint shift_TyVar__subst_TmVar_0_Decls_comm_ind (d14 : Decls) (k : Hvl) (c1 : (Cutoff TyVar)) (s0 : Tm) {struct d14} :
    ((shift_TyVar_Decls (weakenCutoffTyVar c1 k) (subst_TmVar_Decls (weakenTrace X0 k) s0 d14)) = (subst_TmVar_Decls (weakenTrace X0 k) (shift_TyVar_Tm c1 s0) (shift_TyVar_Decls (weakenCutoffTyVar c1 k) d14))) :=
      match d14 return ((shift_TyVar_Decls (weakenCutoffTyVar c1 k) (subst_TmVar_Decls (weakenTrace X0 k) s0 d14)) = (subst_TmVar_Decls (weakenTrace X0 k) (shift_TyVar_Tm c1 s0) (shift_TyVar_Decls (weakenCutoffTyVar c1 k) d14))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d15) => (f_equal2 DConsTm (shift_TyVar__subst_TmVar_0_Tm_comm_ind t6 k c1 s0) (eq_trans (f_equal2 shift_TyVar_Decls eq_refl (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Decls_comm_ind d15 (HS TmVar k) c1 s0) (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (DConsTy K3 d15) => (f_equal2 DConsTy (shift_TyVar__subst_TmVar_0_Kind_comm_ind K3 k c1 s0) (eq_trans (f_equal2 shift_TyVar_Decls eq_refl (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Decls_comm_ind d15 (HS TyVar k) c1 s0) (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
      end
    with shift_TyVar__subst_TmVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (c1 : (Cutoff TyVar)) (s0 : Tm) {struct K4} :
    ((shift_TyVar_Kind (weakenCutoffTyVar c1 k) (subst_TmVar_Kind (weakenTrace X0 k) s0 K4)) = (subst_TmVar_Kind (weakenTrace X0 k) (shift_TyVar_Tm c1 s0) (shift_TyVar_Kind (weakenCutoffTyVar c1 k) K4))) :=
      match K4 return ((shift_TyVar_Kind (weakenCutoffTyVar c1 k) (subst_TmVar_Kind (weakenTrace X0 k) s0 K4)) = (subst_TmVar_Kind (weakenTrace X0 k) (shift_TyVar_Tm c1 s0) (shift_TyVar_Kind (weakenCutoffTyVar c1 k) K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (shift_TyVar__subst_TmVar_0_Ty_comm_ind T5 k c1 s0) (eq_trans (f_equal2 shift_TyVar_Kind eq_refl (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Kind_comm_ind K5 (HS TmVar k) c1 s0) (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end
    with shift_TyVar__subst_TmVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c1 : (Cutoff TyVar)) (s0 : Tm) {struct S1} :
    ((shift_TyVar_Ty (weakenCutoffTyVar c1 k) (subst_TmVar_Ty (weakenTrace X0 k) s0 S1)) = (subst_TmVar_Ty (weakenTrace X0 k) (shift_TyVar_Tm c1 s0) (shift_TyVar_Ty (weakenCutoffTyVar c1 k) S1))) :=
      match S1 return ((shift_TyVar_Ty (weakenCutoffTyVar c1 k) (subst_TmVar_Ty (weakenTrace X0 k) s0 S1)) = (subst_TmVar_Ty (weakenTrace X0 k) (shift_TyVar_Tm c1 s0) (shift_TyVar_Ty (weakenCutoffTyVar c1 k) S1))) with
        | (TVar X8) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (shift_TyVar__subst_TmVar_0_Ty_comm_ind T7 k c1 s0) (eq_trans (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Ty_comm_ind T8 (HS TmVar k) c1 s0) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (TApp T6 t7) => (f_equal2 TApp (shift_TyVar__subst_TmVar_0_Ty_comm_ind T6 k c1 s0) (shift_TyVar__subst_TmVar_0_Tm_comm_ind t7 k c1 s0))
      end
    with shift_TyVar__subst_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (c1 : (Cutoff TyVar)) (s0 : Tm) {struct s1} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c1 k) (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TyVar_Tm c1 s0) (shift_TyVar_Tm (weakenCutoffTyVar c1 k) s1))) :=
      match s1 return ((shift_TyVar_Tm (weakenCutoffTyVar c1 k) (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TyVar_Tm c1 s0) (shift_TyVar_Tm (weakenCutoffTyVar c1 k) s1))) with
        | (Var x14) => (shift_TyVar_Tm_subst_TmVar_Index0_comm_ind c1 s0 k x14)
        | (Abs T9 t8) => (f_equal2 Abs (shift_TyVar__subst_TmVar_0_Ty_comm_ind T9 k c1 s0) (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Tm_comm_ind t8 (HS TmVar k) c1 s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t9 t10) => (f_equal2 App (shift_TyVar__subst_TmVar_0_Tm_comm_ind t9 k c1 s0) (shift_TyVar__subst_TmVar_0_Tm_comm_ind t10 k c1 s0))
        | (Let d16 t8) => (f_equal2 Let (shift_TyVar__subst_TmVar_0_Decls_comm_ind d16 k c1 s0) (eq_trans (f_equal2 shift_TyVar_Tm (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TmVar__bind _ _ _) (eq_refl H0)))) (weakenCutoffTyVar_append c1 k (appendHvl H0 (bind d16)))) (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d16))) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d16))) c1 s0) (f_equal3 subst_TmVar_Tm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d16)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TyVar__bind _ _))))) eq_refl (f_equal2 shift_TyVar_Tm (eq_sym (weakenCutoffTyVar_append c1 k (appendHvl H0 (bind d16)))) eq_refl)))))
      end.
    Fixpoint shift_TyVar__subst_TyVar_0_Decls_comm_ind (d14 : Decls) (k : Hvl) (c1 : (Cutoff TyVar)) (S1 : Ty) {struct d14} :
    ((shift_TyVar_Decls (weakenCutoffTyVar c1 k) (subst_TyVar_Decls (weakenTrace X0 k) S1 d14)) = (subst_TyVar_Decls (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Decls (weakenCutoffTyVar (CS c1) k) d14))) :=
      match d14 return ((shift_TyVar_Decls (weakenCutoffTyVar c1 k) (subst_TyVar_Decls (weakenTrace X0 k) S1 d14)) = (subst_TyVar_Decls (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Decls (weakenCutoffTyVar (CS c1) k) d14))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d15) => (f_equal2 DConsTm (shift_TyVar__subst_TyVar_0_Tm_comm_ind t6 k c1 S1) (eq_trans (f_equal2 shift_TyVar_Decls eq_refl (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Decls_comm_ind d15 (HS TmVar k) c1 S1) (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (DConsTy K3 d15) => (f_equal2 DConsTy (shift_TyVar__subst_TyVar_0_Kind_comm_ind K3 k c1 S1) (eq_trans (f_equal2 shift_TyVar_Decls eq_refl (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Decls_comm_ind d15 (HS TyVar k) c1 S1) (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
      end
    with shift_TyVar__subst_TyVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (c1 : (Cutoff TyVar)) (S1 : Ty) {struct K4} :
    ((shift_TyVar_Kind (weakenCutoffTyVar c1 k) (subst_TyVar_Kind (weakenTrace X0 k) S1 K4)) = (subst_TyVar_Kind (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Kind (weakenCutoffTyVar (CS c1) k) K4))) :=
      match K4 return ((shift_TyVar_Kind (weakenCutoffTyVar c1 k) (subst_TyVar_Kind (weakenTrace X0 k) S1 K4)) = (subst_TyVar_Kind (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Kind (weakenCutoffTyVar (CS c1) k) K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (shift_TyVar__subst_TyVar_0_Ty_comm_ind T5 k c1 S1) (eq_trans (f_equal2 shift_TyVar_Kind eq_refl (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Kind_comm_ind K5 (HS TmVar k) c1 S1) (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end
    with shift_TyVar__subst_TyVar_0_Ty_comm_ind (S2 : Ty) (k : Hvl) (c1 : (Cutoff TyVar)) (S1 : Ty) {struct S2} :
    ((shift_TyVar_Ty (weakenCutoffTyVar c1 k) (subst_TyVar_Ty (weakenTrace X0 k) S1 S2)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Ty (weakenCutoffTyVar (CS c1) k) S2))) :=
      match S2 return ((shift_TyVar_Ty (weakenCutoffTyVar c1 k) (subst_TyVar_Ty (weakenTrace X0 k) S1 S2)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Ty (weakenCutoffTyVar (CS c1) k) S2))) with
        | (TVar X8) => (shift_TyVar_Ty_subst_TyVar_Index0_comm_ind c1 S1 k X8)
        | (TPi T7 T8) => (f_equal2 TPi (shift_TyVar__subst_TyVar_0_Ty_comm_ind T7 k c1 S1) (eq_trans (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Ty_comm_ind T8 (HS TmVar k) c1 S1) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (TApp T6 t7) => (f_equal2 TApp (shift_TyVar__subst_TyVar_0_Ty_comm_ind T6 k c1 S1) (shift_TyVar__subst_TyVar_0_Tm_comm_ind t7 k c1 S1))
      end
    with shift_TyVar__subst_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff TyVar)) (S1 : Ty) {struct s0} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c1 k) (subst_TyVar_Tm (weakenTrace X0 k) S1 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Tm (weakenCutoffTyVar (CS c1) k) s0))) :=
      match s0 return ((shift_TyVar_Tm (weakenCutoffTyVar c1 k) (subst_TyVar_Tm (weakenTrace X0 k) S1 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Tm (weakenCutoffTyVar (CS c1) k) s0))) with
        | (Var x14) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs (shift_TyVar__subst_TyVar_0_Ty_comm_ind T9 k c1 S1) (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Tm_comm_ind t8 (HS TmVar k) c1 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t9 t10) => (f_equal2 App (shift_TyVar__subst_TyVar_0_Tm_comm_ind t9 k c1 S1) (shift_TyVar__subst_TyVar_0_Tm_comm_ind t10 k c1 S1))
        | (Let d16 t8) => (f_equal2 Let (shift_TyVar__subst_TyVar_0_Decls_comm_ind d16 k c1 S1) (eq_trans (f_equal2 shift_TyVar_Tm (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TyVar__bind _ _ _) (eq_refl H0)))) (weakenCutoffTyVar_append c1 k (appendHvl H0 (bind d16)))) (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d16))) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d16))) c1 S1) (f_equal3 subst_TyVar_Tm (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d16)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TyVar__bind _ _))))) eq_refl (f_equal2 shift_TyVar_Tm (eq_sym (weakenCutoffTyVar_append (CS c1) k (appendHvl H0 (bind d16)))) eq_refl)))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shift_TmVar_Decls_subst_TmVar_Decls0_comm (d14 : Decls) : (forall (c1 : (Cutoff TmVar)) (s0 : Tm) ,
      ((shift_TmVar_Decls c1 (subst_TmVar_Decls X0 s0 d14)) = (subst_TmVar_Decls X0 (shift_TmVar_Tm c1 s0) (shift_TmVar_Decls (CS c1) d14)))) := (shift_TmVar__subst_TmVar_0_Decls_comm_ind d14 H0).
    Definition shift_TmVar_Kind_subst_TmVar_Kind0_comm (K3 : Kind) : (forall (c1 : (Cutoff TmVar)) (s0 : Tm) ,
      ((shift_TmVar_Kind c1 (subst_TmVar_Kind X0 s0 K3)) = (subst_TmVar_Kind X0 (shift_TmVar_Tm c1 s0) (shift_TmVar_Kind (CS c1) K3)))) := (shift_TmVar__subst_TmVar_0_Kind_comm_ind K3 H0).
    Definition shift_TmVar_Ty_subst_TmVar_Ty0_comm (S1 : Ty) : (forall (c1 : (Cutoff TmVar)) (s0 : Tm) ,
      ((shift_TmVar_Ty c1 (subst_TmVar_Ty X0 s0 S1)) = (subst_TmVar_Ty X0 (shift_TmVar_Tm c1 s0) (shift_TmVar_Ty (CS c1) S1)))) := (shift_TmVar__subst_TmVar_0_Ty_comm_ind S1 H0).
    Definition shift_TmVar_Tm_subst_TmVar_Tm0_comm (s1 : Tm) : (forall (c1 : (Cutoff TmVar)) (s0 : Tm) ,
      ((shift_TmVar_Tm c1 (subst_TmVar_Tm X0 s0 s1)) = (subst_TmVar_Tm X0 (shift_TmVar_Tm c1 s0) (shift_TmVar_Tm (CS c1) s1)))) := (shift_TmVar__subst_TmVar_0_Tm_comm_ind s1 H0).
    Definition shift_TmVar_Decls_subst_TyVar_Decls0_comm (d14 : Decls) : (forall (c1 : (Cutoff TmVar)) (S1 : Ty) ,
      ((shift_TmVar_Decls c1 (subst_TyVar_Decls X0 S1 d14)) = (subst_TyVar_Decls X0 (shift_TmVar_Ty c1 S1) (shift_TmVar_Decls c1 d14)))) := (shift_TmVar__subst_TyVar_0_Decls_comm_ind d14 H0).
    Definition shift_TmVar_Kind_subst_TyVar_Kind0_comm (K3 : Kind) : (forall (c1 : (Cutoff TmVar)) (S1 : Ty) ,
      ((shift_TmVar_Kind c1 (subst_TyVar_Kind X0 S1 K3)) = (subst_TyVar_Kind X0 (shift_TmVar_Ty c1 S1) (shift_TmVar_Kind c1 K3)))) := (shift_TmVar__subst_TyVar_0_Kind_comm_ind K3 H0).
    Definition shift_TmVar_Ty_subst_TyVar_Ty0_comm (S2 : Ty) : (forall (c1 : (Cutoff TmVar)) (S1 : Ty) ,
      ((shift_TmVar_Ty c1 (subst_TyVar_Ty X0 S1 S2)) = (subst_TyVar_Ty X0 (shift_TmVar_Ty c1 S1) (shift_TmVar_Ty c1 S2)))) := (shift_TmVar__subst_TyVar_0_Ty_comm_ind S2 H0).
    Definition shift_TmVar_Tm_subst_TyVar_Tm0_comm (s0 : Tm) : (forall (c1 : (Cutoff TmVar)) (S1 : Ty) ,
      ((shift_TmVar_Tm c1 (subst_TyVar_Tm X0 S1 s0)) = (subst_TyVar_Tm X0 (shift_TmVar_Ty c1 S1) (shift_TmVar_Tm c1 s0)))) := (shift_TmVar__subst_TyVar_0_Tm_comm_ind s0 H0).
    Definition shift_TyVar_Decls_subst_TmVar_Decls0_comm (d14 : Decls) : (forall (c1 : (Cutoff TyVar)) (s0 : Tm) ,
      ((shift_TyVar_Decls c1 (subst_TmVar_Decls X0 s0 d14)) = (subst_TmVar_Decls X0 (shift_TyVar_Tm c1 s0) (shift_TyVar_Decls c1 d14)))) := (shift_TyVar__subst_TmVar_0_Decls_comm_ind d14 H0).
    Definition shift_TyVar_Kind_subst_TmVar_Kind0_comm (K3 : Kind) : (forall (c1 : (Cutoff TyVar)) (s0 : Tm) ,
      ((shift_TyVar_Kind c1 (subst_TmVar_Kind X0 s0 K3)) = (subst_TmVar_Kind X0 (shift_TyVar_Tm c1 s0) (shift_TyVar_Kind c1 K3)))) := (shift_TyVar__subst_TmVar_0_Kind_comm_ind K3 H0).
    Definition shift_TyVar_Ty_subst_TmVar_Ty0_comm (S1 : Ty) : (forall (c1 : (Cutoff TyVar)) (s0 : Tm) ,
      ((shift_TyVar_Ty c1 (subst_TmVar_Ty X0 s0 S1)) = (subst_TmVar_Ty X0 (shift_TyVar_Tm c1 s0) (shift_TyVar_Ty c1 S1)))) := (shift_TyVar__subst_TmVar_0_Ty_comm_ind S1 H0).
    Definition shift_TyVar_Tm_subst_TmVar_Tm0_comm (s1 : Tm) : (forall (c1 : (Cutoff TyVar)) (s0 : Tm) ,
      ((shift_TyVar_Tm c1 (subst_TmVar_Tm X0 s0 s1)) = (subst_TmVar_Tm X0 (shift_TyVar_Tm c1 s0) (shift_TyVar_Tm c1 s1)))) := (shift_TyVar__subst_TmVar_0_Tm_comm_ind s1 H0).
    Definition shift_TyVar_Decls_subst_TyVar_Decls0_comm (d14 : Decls) : (forall (c1 : (Cutoff TyVar)) (S1 : Ty) ,
      ((shift_TyVar_Decls c1 (subst_TyVar_Decls X0 S1 d14)) = (subst_TyVar_Decls X0 (shift_TyVar_Ty c1 S1) (shift_TyVar_Decls (CS c1) d14)))) := (shift_TyVar__subst_TyVar_0_Decls_comm_ind d14 H0).
    Definition shift_TyVar_Kind_subst_TyVar_Kind0_comm (K3 : Kind) : (forall (c1 : (Cutoff TyVar)) (S1 : Ty) ,
      ((shift_TyVar_Kind c1 (subst_TyVar_Kind X0 S1 K3)) = (subst_TyVar_Kind X0 (shift_TyVar_Ty c1 S1) (shift_TyVar_Kind (CS c1) K3)))) := (shift_TyVar__subst_TyVar_0_Kind_comm_ind K3 H0).
    Definition shift_TyVar_Ty_subst_TyVar_Ty0_comm (S2 : Ty) : (forall (c1 : (Cutoff TyVar)) (S1 : Ty) ,
      ((shift_TyVar_Ty c1 (subst_TyVar_Ty X0 S1 S2)) = (subst_TyVar_Ty X0 (shift_TyVar_Ty c1 S1) (shift_TyVar_Ty (CS c1) S2)))) := (shift_TyVar__subst_TyVar_0_Ty_comm_ind S2 H0).
    Definition shift_TyVar_Tm_subst_TyVar_Tm0_comm (s0 : Tm) : (forall (c1 : (Cutoff TyVar)) (S1 : Ty) ,
      ((shift_TyVar_Tm c1 (subst_TyVar_Tm X0 S1 s0)) = (subst_TyVar_Tm X0 (shift_TyVar_Ty c1 S1) (shift_TyVar_Tm (CS c1) s0)))) := (shift_TyVar__subst_TyVar_0_Tm_comm_ind s0 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma subst_TmVar_Index_shift_TmVar_Tm0_comm_ind (d14 : (Trace TmVar)) (s0 : Tm) :
      (forall (k : Hvl) (x11 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TmVar d14) k) s0 (shift_TmVar_Index (weakenCutoffTmVar C0 k) x11)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Index (weakenTrace d14 k) s0 x11)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Index_shift_TyVar_Tm0_comm_ind (d14 : (Trace TmVar)) (s0 : Tm) :
      (forall (k : Hvl) (x11 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TyVar d14) k) s0 x11) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Index (weakenTrace d14 k) s0 x11)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Index_shift_TmVar_Ty0_comm_ind (d14 : (Trace TyVar)) (S1 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace (XS TmVar d14) k) S1 X7) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TyVar_Index (weakenTrace d14 k) S1 X7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Index_shift_TyVar_Ty0_comm_ind (d14 : (Trace TyVar)) (S1 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace (XS TyVar d14) k) S1 (shift_TyVar_Index (weakenCutoffTyVar C0 k) X7)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Index (weakenTrace d14 k) S1 X7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_TmVar__shift_TmVar_0_Decls_comm_ind (d15 : Decls) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) {struct d15} :
    ((subst_TmVar_Decls (weakenTrace (XS TmVar d14) k) s0 (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d15)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (subst_TmVar_Decls (weakenTrace d14 k) s0 d15))) :=
      match d15 return ((subst_TmVar_Decls (weakenTrace (XS TmVar d14) k) s0 (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d15)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (subst_TmVar_Decls (weakenTrace d14 k) s0 d15))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d16) => (f_equal2 DConsTm (subst_TmVar__shift_TmVar_0_Tm_comm_ind t6 k d14 s0) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar (XS TmVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Decls_comm_ind d16 (HS TmVar k) d14 s0) (f_equal2 shift_TmVar_Decls eq_refl (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (DConsTy K3 d16) => (f_equal2 DConsTy (subst_TmVar__shift_TmVar_0_Kind_comm_ind K3 k d14 s0) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar (XS TmVar d14) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Decls_comm_ind d16 (HS TyVar k) d14 s0) (f_equal2 shift_TmVar_Decls eq_refl (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar d14 k (HS TyVar H0))) eq_refl eq_refl)))))
      end
    with subst_TmVar__shift_TmVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) {struct K4} :
    ((subst_TmVar_Kind (weakenTrace (XS TmVar d14) k) s0 (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K4)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (subst_TmVar_Kind (weakenTrace d14 k) s0 K4))) :=
      match K4 return ((subst_TmVar_Kind (weakenTrace (XS TmVar d14) k) s0 (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K4)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (subst_TmVar_Kind (weakenTrace d14 k) s0 K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (subst_TmVar__shift_TmVar_0_Ty_comm_ind T5 k d14 s0) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar (XS TmVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Kind_comm_ind K5 (HS TmVar k) d14 s0) (f_equal2 shift_TmVar_Kind eq_refl (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TmVar__shift_TmVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) {struct S1} :
    ((subst_TmVar_Ty (weakenTrace (XS TmVar d14) k) s0 (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S1)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TmVar_Ty (weakenTrace d14 k) s0 S1))) :=
      match S1 return ((subst_TmVar_Ty (weakenTrace (XS TmVar d14) k) s0 (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S1)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TmVar_Ty (weakenTrace d14 k) s0 S1))) with
        | (TVar X8) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (subst_TmVar__shift_TmVar_0_Ty_comm_ind T7 k d14 s0) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar (XS TmVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Ty_comm_ind T8 (HS TmVar k) d14 s0) (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t7) => (f_equal2 TApp (subst_TmVar__shift_TmVar_0_Ty_comm_ind T6 k d14 s0) (subst_TmVar__shift_TmVar_0_Tm_comm_ind t7 k d14 s0))
      end
    with subst_TmVar__shift_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) {struct s1} :
    ((subst_TmVar_Tm (weakenTrace (XS TmVar d14) k) s0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s1)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d14 k) s0 s1))) :=
      match s1 return ((subst_TmVar_Tm (weakenTrace (XS TmVar d14) k) s0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s1)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d14 k) s0 s1))) with
        | (Var x14) => (subst_TmVar_Index_shift_TmVar_Tm0_comm_ind d14 s0 k x14)
        | (Abs T9 t8) => (f_equal2 Abs (subst_TmVar__shift_TmVar_0_Ty_comm_ind T9 k d14 s0) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TmVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind t8 (HS TmVar k) d14 s0) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TmVar__shift_TmVar_0_Tm_comm_ind t9 k d14 s0) (subst_TmVar__shift_TmVar_0_Tm_comm_ind t10 k d14 s0))
        | (Let d17 t8) => (f_equal2 Let (subst_TmVar__shift_TmVar_0_Decls_comm_ind d17 k d14 s0) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenTrace_append TmVar (XS TmVar d14) k (appendHvl H0 (bind d17)))) eq_refl (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d17))) eq_refl)) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d17))) d14 s0) (f_equal2 shift_TmVar_Tm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d17)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0))))) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d14 k (appendHvl H0 (bind d17)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__shift_TyVar_0_Decls_comm_ind (d15 : Decls) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) {struct d15} :
    ((subst_TmVar_Decls (weakenTrace (XS TyVar d14) k) s0 (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d15)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (subst_TmVar_Decls (weakenTrace d14 k) s0 d15))) :=
      match d15 return ((subst_TmVar_Decls (weakenTrace (XS TyVar d14) k) s0 (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d15)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (subst_TmVar_Decls (weakenTrace d14 k) s0 d15))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d16) => (f_equal2 DConsTm (subst_TmVar__shift_TyVar_0_Tm_comm_ind t6 k d14 s0) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar (XS TyVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Decls_comm_ind d16 (HS TmVar k) d14 s0) (f_equal2 shift_TyVar_Decls eq_refl (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (DConsTy K3 d16) => (f_equal2 DConsTy (subst_TmVar__shift_TyVar_0_Kind_comm_ind K3 k d14 s0) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar (XS TyVar d14) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Decls_comm_ind d16 (HS TyVar k) d14 s0) (f_equal2 shift_TyVar_Decls eq_refl (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar d14 k (HS TyVar H0))) eq_refl eq_refl)))))
      end
    with subst_TmVar__shift_TyVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) {struct K4} :
    ((subst_TmVar_Kind (weakenTrace (XS TyVar d14) k) s0 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K4)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (subst_TmVar_Kind (weakenTrace d14 k) s0 K4))) :=
      match K4 return ((subst_TmVar_Kind (weakenTrace (XS TyVar d14) k) s0 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K4)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (subst_TmVar_Kind (weakenTrace d14 k) s0 K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (subst_TmVar__shift_TyVar_0_Ty_comm_ind T5 k d14 s0) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar (XS TyVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Kind_comm_ind K5 (HS TmVar k) d14 s0) (f_equal2 shift_TyVar_Kind eq_refl (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TmVar__shift_TyVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) {struct S1} :
    ((subst_TmVar_Ty (weakenTrace (XS TyVar d14) k) s0 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TmVar_Ty (weakenTrace d14 k) s0 S1))) :=
      match S1 return ((subst_TmVar_Ty (weakenTrace (XS TyVar d14) k) s0 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TmVar_Ty (weakenTrace d14 k) s0 S1))) with
        | (TVar X8) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (subst_TmVar__shift_TyVar_0_Ty_comm_ind T7 k d14 s0) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar (XS TyVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Ty_comm_ind T8 (HS TmVar k) d14 s0) (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t7) => (f_equal2 TApp (subst_TmVar__shift_TyVar_0_Ty_comm_ind T6 k d14 s0) (subst_TmVar__shift_TyVar_0_Tm_comm_ind t7 k d14 s0))
      end
    with subst_TmVar__shift_TyVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) {struct s1} :
    ((subst_TmVar_Tm (weakenTrace (XS TyVar d14) k) s0 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s1)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Tm (weakenTrace d14 k) s0 s1))) :=
      match s1 return ((subst_TmVar_Tm (weakenTrace (XS TyVar d14) k) s0 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s1)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Tm (weakenTrace d14 k) s0 s1))) with
        | (Var x14) => (subst_TmVar_Index_shift_TyVar_Tm0_comm_ind d14 s0 k x14)
        | (Abs T9 t8) => (f_equal2 Abs (subst_TmVar__shift_TyVar_0_Ty_comm_ind T9 k d14 s0) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TyVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Tm_comm_ind t8 (HS TmVar k) d14 s0) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TmVar__shift_TyVar_0_Tm_comm_ind t9 k d14 s0) (subst_TmVar__shift_TyVar_0_Tm_comm_ind t10 k d14 s0))
        | (Let d17 t8) => (f_equal2 Let (subst_TmVar__shift_TyVar_0_Decls_comm_ind d17 k d14 s0) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TyVar__bind _ _))) (weakenTrace_append TmVar (XS TyVar d14) k (appendHvl H0 (bind d17)))) eq_refl (f_equal2 shift_TyVar_Tm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d17))) eq_refl)) (eq_trans (subst_TmVar__shift_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d17))) d14 s0) (f_equal2 shift_TyVar_Tm (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d17)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0))))) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d14 k (appendHvl H0 (bind d17)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__shift_TmVar_0_Decls_comm_ind (d15 : Decls) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) {struct d15} :
    ((subst_TyVar_Decls (weakenTrace (XS TmVar d14) k) S1 (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d15)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (subst_TyVar_Decls (weakenTrace d14 k) S1 d15))) :=
      match d15 return ((subst_TyVar_Decls (weakenTrace (XS TmVar d14) k) S1 (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d15)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (subst_TyVar_Decls (weakenTrace d14 k) S1 d15))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d16) => (f_equal2 DConsTm (subst_TyVar__shift_TmVar_0_Tm_comm_ind t6 k d14 S1) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar (XS TmVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Decls_comm_ind d16 (HS TmVar k) d14 S1) (f_equal2 shift_TmVar_Decls eq_refl (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (DConsTy K3 d16) => (f_equal2 DConsTy (subst_TyVar__shift_TmVar_0_Kind_comm_ind K3 k d14 S1) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar (XS TmVar d14) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Decls_comm_ind d16 (HS TyVar k) d14 S1) (f_equal2 shift_TmVar_Decls eq_refl (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar d14 k (HS TyVar H0))) eq_refl eq_refl)))))
      end
    with subst_TyVar__shift_TmVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) {struct K4} :
    ((subst_TyVar_Kind (weakenTrace (XS TmVar d14) k) S1 (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K4)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (subst_TyVar_Kind (weakenTrace d14 k) S1 K4))) :=
      match K4 return ((subst_TyVar_Kind (weakenTrace (XS TmVar d14) k) S1 (shift_TmVar_Kind (weakenCutoffTmVar C0 k) K4)) = (shift_TmVar_Kind (weakenCutoffTmVar C0 k) (subst_TyVar_Kind (weakenTrace d14 k) S1 K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (subst_TyVar__shift_TmVar_0_Ty_comm_ind T5 k d14 S1) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar (XS TmVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Kind_comm_ind K5 (HS TmVar k) d14 S1) (f_equal2 shift_TmVar_Kind eq_refl (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TyVar__shift_TmVar_0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) {struct S2} :
    ((subst_TyVar_Ty (weakenTrace (XS TmVar d14) k) S1 (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S2)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TyVar_Ty (weakenTrace d14 k) S1 S2))) :=
      match S2 return ((subst_TyVar_Ty (weakenTrace (XS TmVar d14) k) S1 (shift_TmVar_Ty (weakenCutoffTmVar C0 k) S2)) = (shift_TmVar_Ty (weakenCutoffTmVar C0 k) (subst_TyVar_Ty (weakenTrace d14 k) S1 S2))) with
        | (TVar X8) => (subst_TyVar_Index_shift_TmVar_Ty0_comm_ind d14 S1 k X8)
        | (TPi T7 T8) => (f_equal2 TPi (subst_TyVar__shift_TmVar_0_Ty_comm_ind T7 k d14 S1) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TmVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Ty_comm_ind T8 (HS TmVar k) d14 S1) (f_equal2 shift_TmVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t7) => (f_equal2 TApp (subst_TyVar__shift_TmVar_0_Ty_comm_ind T6 k d14 S1) (subst_TyVar__shift_TmVar_0_Tm_comm_ind t7 k d14 S1))
      end
    with subst_TyVar__shift_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) {struct s0} :
    ((subst_TyVar_Tm (weakenTrace (XS TmVar d14) k) S1 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TyVar_Tm (weakenTrace d14 k) S1 s0))) :=
      match s0 return ((subst_TyVar_Tm (weakenTrace (XS TmVar d14) k) S1 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TyVar_Tm (weakenTrace d14 k) S1 s0))) with
        | (Var x14) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs (subst_TyVar__shift_TmVar_0_Ty_comm_ind T9 k d14 S1) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TmVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Tm_comm_ind t8 (HS TmVar k) d14 S1) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TyVar__shift_TmVar_0_Tm_comm_ind t9 k d14 S1) (subst_TyVar__shift_TmVar_0_Tm_comm_ind t10 k d14 S1))
        | (Let d17 t8) => (f_equal2 Let (subst_TyVar__shift_TmVar_0_Decls_comm_ind d17 k d14 S1) (eq_trans (f_equal3 subst_TyVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenTrace_append TyVar (XS TmVar d14) k (appendHvl H0 (bind d17)))) eq_refl (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d17))) eq_refl)) (eq_trans (subst_TyVar__shift_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d17))) d14 S1) (f_equal2 shift_TmVar_Tm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d17)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TyVar__bind _ _ _)) (eq_refl H0))))) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d14 k (appendHvl H0 (bind d17)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__shift_TyVar_0_Decls_comm_ind (d15 : Decls) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) {struct d15} :
    ((subst_TyVar_Decls (weakenTrace (XS TyVar d14) k) S1 (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d15)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (subst_TyVar_Decls (weakenTrace d14 k) S1 d15))) :=
      match d15 return ((subst_TyVar_Decls (weakenTrace (XS TyVar d14) k) S1 (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d15)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (subst_TyVar_Decls (weakenTrace d14 k) S1 d15))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d16) => (f_equal2 DConsTm (subst_TyVar__shift_TyVar_0_Tm_comm_ind t6 k d14 S1) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar (XS TyVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Decls_comm_ind d16 (HS TmVar k) d14 S1) (f_equal2 shift_TyVar_Decls eq_refl (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (DConsTy K3 d16) => (f_equal2 DConsTy (subst_TyVar__shift_TyVar_0_Kind_comm_ind K3 k d14 S1) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar (XS TyVar d14) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Decls_comm_ind d16 (HS TyVar k) d14 S1) (f_equal2 shift_TyVar_Decls eq_refl (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar d14 k (HS TyVar H0))) eq_refl eq_refl)))))
      end
    with subst_TyVar__shift_TyVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) {struct K4} :
    ((subst_TyVar_Kind (weakenTrace (XS TyVar d14) k) S1 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K4)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (subst_TyVar_Kind (weakenTrace d14 k) S1 K4))) :=
      match K4 return ((subst_TyVar_Kind (weakenTrace (XS TyVar d14) k) S1 (shift_TyVar_Kind (weakenCutoffTyVar C0 k) K4)) = (shift_TyVar_Kind (weakenCutoffTyVar C0 k) (subst_TyVar_Kind (weakenTrace d14 k) S1 K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (subst_TyVar__shift_TyVar_0_Ty_comm_ind T5 k d14 S1) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar (XS TyVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Kind_comm_ind K5 (HS TmVar k) d14 S1) (f_equal2 shift_TyVar_Kind eq_refl (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TyVar__shift_TyVar_0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) {struct S2} :
    ((subst_TyVar_Ty (weakenTrace (XS TyVar d14) k) S1 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S2)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Ty (weakenTrace d14 k) S1 S2))) :=
      match S2 return ((subst_TyVar_Ty (weakenTrace (XS TyVar d14) k) S1 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S2)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Ty (weakenTrace d14 k) S1 S2))) with
        | (TVar X8) => (subst_TyVar_Index_shift_TyVar_Ty0_comm_ind d14 S1 k X8)
        | (TPi T7 T8) => (f_equal2 TPi (subst_TyVar__shift_TyVar_0_Ty_comm_ind T7 k d14 S1) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TyVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Ty_comm_ind T8 (HS TmVar k) d14 S1) (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t7) => (f_equal2 TApp (subst_TyVar__shift_TyVar_0_Ty_comm_ind T6 k d14 S1) (subst_TyVar__shift_TyVar_0_Tm_comm_ind t7 k d14 S1))
      end
    with subst_TyVar__shift_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) {struct s0} :
    ((subst_TyVar_Tm (weakenTrace (XS TyVar d14) k) S1 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TyVar_Tm (weakenTrace d14 k) S1 s0))) :=
      match s0 return ((subst_TyVar_Tm (weakenTrace (XS TyVar d14) k) S1 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TyVar_Tm (weakenTrace d14 k) S1 s0))) with
        | (Var x14) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs (subst_TyVar__shift_TyVar_0_Ty_comm_ind T9 k d14 S1) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TyVar d14) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Tm_comm_ind t8 (HS TmVar k) d14 S1) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d14 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TyVar__shift_TyVar_0_Tm_comm_ind t9 k d14 S1) (subst_TyVar__shift_TyVar_0_Tm_comm_ind t10 k d14 S1))
        | (Let d17 t8) => (f_equal2 Let (subst_TyVar__shift_TyVar_0_Decls_comm_ind d17 k d14 S1) (eq_trans (f_equal3 subst_TyVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TyVar__bind _ _))) (weakenTrace_append TyVar (XS TyVar d14) k (appendHvl H0 (bind d17)))) eq_refl (f_equal2 shift_TyVar_Tm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d17))) eq_refl)) (eq_trans (subst_TyVar__shift_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d17))) d14 S1) (f_equal2 shift_TyVar_Tm (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d17)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TyVar__bind _ _ _)) (eq_refl H0))))) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d14 k (appendHvl H0 (bind d17)))) eq_refl eq_refl)))))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition subst_TmVar_Decls_shift_TmVar_Decls0_comm (d15 : Decls) : (forall (d14 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Decls (XS TmVar d14) s0 (shift_TmVar_Decls C0 d15)) = (shift_TmVar_Decls C0 (subst_TmVar_Decls d14 s0 d15)))) := (subst_TmVar__shift_TmVar_0_Decls_comm_ind d15 H0).
    Definition subst_TmVar_Kind_shift_TmVar_Kind0_comm (K3 : Kind) : (forall (d14 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Kind (XS TmVar d14) s0 (shift_TmVar_Kind C0 K3)) = (shift_TmVar_Kind C0 (subst_TmVar_Kind d14 s0 K3)))) := (subst_TmVar__shift_TmVar_0_Kind_comm_ind K3 H0).
    Definition subst_TmVar_Ty_shift_TmVar_Ty0_comm (S1 : Ty) : (forall (d14 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Ty (XS TmVar d14) s0 (shift_TmVar_Ty C0 S1)) = (shift_TmVar_Ty C0 (subst_TmVar_Ty d14 s0 S1)))) := (subst_TmVar__shift_TmVar_0_Ty_comm_ind S1 H0).
    Definition subst_TmVar_Tm_shift_TmVar_Tm0_comm (s1 : Tm) : (forall (d14 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Tm (XS TmVar d14) s0 (shift_TmVar_Tm C0 s1)) = (shift_TmVar_Tm C0 (subst_TmVar_Tm d14 s0 s1)))) := (subst_TmVar__shift_TmVar_0_Tm_comm_ind s1 H0).
    Definition subst_TmVar_Decls_shift_TyVar_Decls0_comm (d15 : Decls) : (forall (d14 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Decls (XS TyVar d14) s0 (shift_TyVar_Decls C0 d15)) = (shift_TyVar_Decls C0 (subst_TmVar_Decls d14 s0 d15)))) := (subst_TmVar__shift_TyVar_0_Decls_comm_ind d15 H0).
    Definition subst_TmVar_Kind_shift_TyVar_Kind0_comm (K3 : Kind) : (forall (d14 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Kind (XS TyVar d14) s0 (shift_TyVar_Kind C0 K3)) = (shift_TyVar_Kind C0 (subst_TmVar_Kind d14 s0 K3)))) := (subst_TmVar__shift_TyVar_0_Kind_comm_ind K3 H0).
    Definition subst_TmVar_Ty_shift_TyVar_Ty0_comm (S1 : Ty) : (forall (d14 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Ty (XS TyVar d14) s0 (shift_TyVar_Ty C0 S1)) = (shift_TyVar_Ty C0 (subst_TmVar_Ty d14 s0 S1)))) := (subst_TmVar__shift_TyVar_0_Ty_comm_ind S1 H0).
    Definition subst_TmVar_Tm_shift_TyVar_Tm0_comm (s1 : Tm) : (forall (d14 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Tm (XS TyVar d14) s0 (shift_TyVar_Tm C0 s1)) = (shift_TyVar_Tm C0 (subst_TmVar_Tm d14 s0 s1)))) := (subst_TmVar__shift_TyVar_0_Tm_comm_ind s1 H0).
    Definition subst_TyVar_Decls_shift_TmVar_Decls0_comm (d15 : Decls) : (forall (d14 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Decls (XS TmVar d14) S1 (shift_TmVar_Decls C0 d15)) = (shift_TmVar_Decls C0 (subst_TyVar_Decls d14 S1 d15)))) := (subst_TyVar__shift_TmVar_0_Decls_comm_ind d15 H0).
    Definition subst_TyVar_Kind_shift_TmVar_Kind0_comm (K3 : Kind) : (forall (d14 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Kind (XS TmVar d14) S1 (shift_TmVar_Kind C0 K3)) = (shift_TmVar_Kind C0 (subst_TyVar_Kind d14 S1 K3)))) := (subst_TyVar__shift_TmVar_0_Kind_comm_ind K3 H0).
    Definition subst_TyVar_Ty_shift_TmVar_Ty0_comm (S2 : Ty) : (forall (d14 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Ty (XS TmVar d14) S1 (shift_TmVar_Ty C0 S2)) = (shift_TmVar_Ty C0 (subst_TyVar_Ty d14 S1 S2)))) := (subst_TyVar__shift_TmVar_0_Ty_comm_ind S2 H0).
    Definition subst_TyVar_Tm_shift_TmVar_Tm0_comm (s0 : Tm) : (forall (d14 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Tm (XS TmVar d14) S1 (shift_TmVar_Tm C0 s0)) = (shift_TmVar_Tm C0 (subst_TyVar_Tm d14 S1 s0)))) := (subst_TyVar__shift_TmVar_0_Tm_comm_ind s0 H0).
    Definition subst_TyVar_Decls_shift_TyVar_Decls0_comm (d15 : Decls) : (forall (d14 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Decls (XS TyVar d14) S1 (shift_TyVar_Decls C0 d15)) = (shift_TyVar_Decls C0 (subst_TyVar_Decls d14 S1 d15)))) := (subst_TyVar__shift_TyVar_0_Decls_comm_ind d15 H0).
    Definition subst_TyVar_Kind_shift_TyVar_Kind0_comm (K3 : Kind) : (forall (d14 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Kind (XS TyVar d14) S1 (shift_TyVar_Kind C0 K3)) = (shift_TyVar_Kind C0 (subst_TyVar_Kind d14 S1 K3)))) := (subst_TyVar__shift_TyVar_0_Kind_comm_ind K3 H0).
    Definition subst_TyVar_Ty_shift_TyVar_Ty0_comm (S2 : Ty) : (forall (d14 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Ty (XS TyVar d14) S1 (shift_TyVar_Ty C0 S2)) = (shift_TyVar_Ty C0 (subst_TyVar_Ty d14 S1 S2)))) := (subst_TyVar__shift_TyVar_0_Ty_comm_ind S2 H0).
    Definition subst_TyVar_Tm_shift_TyVar_Tm0_comm (s0 : Tm) : (forall (d14 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Tm (XS TyVar d14) S1 (shift_TyVar_Tm C0 s0)) = (shift_TyVar_Tm C0 (subst_TyVar_Tm d14 S1 s0)))) := (subst_TyVar__shift_TyVar_0_Tm_comm_ind s0 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    
  End SubstSubordInd.
  Section SubstSubord.
    
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite subst_TmVar_Decls0_shift_TmVar_Decls0_reflection subst_TyVar_Decls0_shift_TyVar_Decls0_reflection subst_TmVar_Kind0_shift_TmVar_Kind0_reflection subst_TyVar_Kind0_shift_TyVar_Kind0_reflection subst_TmVar_Tm0_shift_TmVar_Tm0_reflection subst_TyVar_Tm0_shift_TyVar_Tm0_reflection subst_TmVar_Ty0_shift_TmVar_Ty0_reflection subst_TyVar_Ty0_shift_TyVar_Ty0_reflection : interaction.
 Hint Rewrite subst_TmVar_Decls0_shift_TmVar_Decls0_reflection subst_TyVar_Decls0_shift_TyVar_Decls0_reflection subst_TmVar_Kind0_shift_TmVar_Kind0_reflection subst_TyVar_Kind0_shift_TyVar_Kind0_reflection subst_TmVar_Tm0_shift_TmVar_Tm0_reflection subst_TyVar_Tm0_shift_TyVar_Tm0_reflection subst_TmVar_Ty0_shift_TmVar_Ty0_reflection subst_TyVar_Ty0_shift_TyVar_Ty0_reflection : reflection.
 Hint Rewrite subst_TmVar_Decls_shift_TmVar_Decls0_comm subst_TmVar_Decls_shift_TyVar_Decls0_comm subst_TyVar_Decls_shift_TmVar_Decls0_comm subst_TyVar_Decls_shift_TyVar_Decls0_comm subst_TmVar_Kind_shift_TmVar_Kind0_comm subst_TmVar_Kind_shift_TyVar_Kind0_comm subst_TyVar_Kind_shift_TmVar_Kind0_comm subst_TyVar_Kind_shift_TyVar_Kind0_comm subst_TmVar_Tm_shift_TmVar_Tm0_comm subst_TmVar_Tm_shift_TyVar_Tm0_comm subst_TyVar_Tm_shift_TmVar_Tm0_comm subst_TyVar_Tm_shift_TyVar_Tm0_comm subst_TmVar_Ty_shift_TmVar_Ty0_comm subst_TmVar_Ty_shift_TyVar_Ty0_comm subst_TyVar_Ty_shift_TmVar_Ty0_comm subst_TyVar_Ty_shift_TyVar_Ty0_comm : interaction.
 Hint Rewrite subst_TmVar_Decls_shift_TmVar_Decls0_comm subst_TmVar_Decls_shift_TyVar_Decls0_comm subst_TyVar_Decls_shift_TmVar_Decls0_comm subst_TyVar_Decls_shift_TyVar_Decls0_comm subst_TmVar_Kind_shift_TmVar_Kind0_comm subst_TmVar_Kind_shift_TyVar_Kind0_comm subst_TyVar_Kind_shift_TmVar_Kind0_comm subst_TyVar_Kind_shift_TyVar_Kind0_comm subst_TmVar_Tm_shift_TmVar_Tm0_comm subst_TmVar_Tm_shift_TyVar_Tm0_comm subst_TyVar_Tm_shift_TmVar_Tm0_comm subst_TyVar_Tm_shift_TyVar_Tm0_comm subst_TmVar_Ty_shift_TmVar_Ty0_comm subst_TmVar_Ty_shift_TyVar_Ty0_comm subst_TyVar_Ty_shift_TmVar_Ty0_comm subst_TyVar_Ty_shift_TyVar_Ty0_comm : subst_shift0.
 Hint Rewrite shift_TmVar_Decls_subst_TmVar_Decls0_comm shift_TmVar_Decls_subst_TyVar_Decls0_comm shift_TyVar_Decls_subst_TmVar_Decls0_comm shift_TyVar_Decls_subst_TyVar_Decls0_comm shift_TmVar_Kind_subst_TmVar_Kind0_comm shift_TmVar_Kind_subst_TyVar_Kind0_comm shift_TyVar_Kind_subst_TmVar_Kind0_comm shift_TyVar_Kind_subst_TyVar_Kind0_comm shift_TmVar_Tm_subst_TmVar_Tm0_comm shift_TmVar_Tm_subst_TyVar_Tm0_comm shift_TyVar_Tm_subst_TmVar_Tm0_comm shift_TyVar_Tm_subst_TyVar_Tm0_comm shift_TmVar_Ty_subst_TmVar_Ty0_comm shift_TmVar_Ty_subst_TyVar_Ty0_comm shift_TyVar_Ty_subst_TmVar_Ty0_comm shift_TyVar_Ty_subst_TyVar_Ty0_comm : interaction.
 Hint Rewrite shift_TmVar_Decls_subst_TmVar_Decls0_comm shift_TmVar_Decls_subst_TyVar_Decls0_comm shift_TyVar_Decls_subst_TmVar_Decls0_comm shift_TyVar_Decls_subst_TyVar_Decls0_comm shift_TmVar_Kind_subst_TmVar_Kind0_comm shift_TmVar_Kind_subst_TyVar_Kind0_comm shift_TyVar_Kind_subst_TmVar_Kind0_comm shift_TyVar_Kind_subst_TyVar_Kind0_comm shift_TmVar_Tm_subst_TmVar_Tm0_comm shift_TmVar_Tm_subst_TyVar_Tm0_comm shift_TyVar_Tm_subst_TmVar_Tm0_comm shift_TyVar_Tm_subst_TyVar_Tm0_comm shift_TmVar_Ty_subst_TmVar_Ty0_comm shift_TmVar_Ty_subst_TyVar_Ty0_comm shift_TyVar_Ty_subst_TmVar_Ty0_comm shift_TyVar_Ty_subst_TyVar_Ty0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma subst_TmVar_Tm_subst_TmVar_Index0_commright_ind (d14 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) :
      (forall (k : Hvl) (x11 : (Index TmVar)) ,
        ((subst_TmVar_Tm (weakenTrace d14 k) s0 (subst_TmVar_Index (weakenTrace X0 k) s1 x11)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d14 s0 s1) (subst_TmVar_Index (weakenTrace (XS TmVar d14) k) s0 x11)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Tm_subst_TmVar_Index0_commright_ind (d14 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) :
      (forall (k : Hvl) (x11 : (Index TmVar)) ,
        ((subst_TyVar_Tm (weakenTrace d14 k) S1 (subst_TmVar_Index (weakenTrace X0 k) s0 x11)) = (subst_TmVar_Index (weakenTrace X0 k) (subst_TyVar_Tm d14 S1 s0) x11))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Ty_subst_TyVar_Index0_commright_ind (d14 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((subst_TmVar_Ty (weakenTrace d14 k) s0 (subst_TyVar_Index (weakenTrace X0 k) S1 X7)) = (subst_TyVar_Index (weakenTrace X0 k) (subst_TmVar_Ty d14 s0 S1) X7))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Ty_subst_TyVar_Index0_commright_ind (d14 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((subst_TyVar_Ty (weakenTrace d14 k) S1 (subst_TyVar_Index (weakenTrace X0 k) S2 X7)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d14 S1 S2) (subst_TyVar_Index (weakenTrace (XS TyVar d14) k) S1 X7)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Ty_subst_TyVar_Index0_commleft_ind (d14 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) :
      (forall (k : Hvl) (x11 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace d14 k) s0 x11) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TmVar_Ty d14 s0 S1) (subst_TmVar_Index (weakenTrace (XS TyVar d14) k) s0 x11)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Tm_subst_TmVar_Index0_commleft_ind (d14 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace d14 k) S1 X7) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TyVar_Tm d14 S1 s0) (subst_TyVar_Index (weakenTrace (XS TmVar d14) k) S1 X7)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_TmVar__subst_TmVar_0_Decls_comm_ind (d15 : Decls) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) {struct d15} :
    ((subst_TmVar_Decls (weakenTrace d14 k) s0 (subst_TmVar_Decls (weakenTrace X0 k) s1 d15)) = (subst_TmVar_Decls (weakenTrace X0 k) (subst_TmVar_Tm d14 s0 s1) (subst_TmVar_Decls (weakenTrace (XS TmVar d14) k) s0 d15))) :=
      match d15 return ((subst_TmVar_Decls (weakenTrace d14 k) s0 (subst_TmVar_Decls (weakenTrace X0 k) s1 d15)) = (subst_TmVar_Decls (weakenTrace X0 k) (subst_TmVar_Tm d14 s0 s1) (subst_TmVar_Decls (weakenTrace (XS TmVar d14) k) s0 d15))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d16) => (f_equal2 DConsTm (subst_TmVar__subst_TmVar_0_Tm_comm_ind t6 k d14 s0 s1) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Decls_comm_ind d16 (HS TmVar k) d14 s0 s1) (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar (XS TmVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (DConsTy K3 d16) => (f_equal2 DConsTy (subst_TmVar__subst_TmVar_0_Kind_comm_ind K3 k d14 s0 s1) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar d14 k (HS TyVar H0)) eq_refl (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Decls_comm_ind d16 (HS TyVar k) d14 s0 s1) (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar (XS TmVar d14) k (HS TyVar H0))) eq_refl eq_refl)))))
      end
    with subst_TmVar__subst_TmVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) {struct K4} :
    ((subst_TmVar_Kind (weakenTrace d14 k) s0 (subst_TmVar_Kind (weakenTrace X0 k) s1 K4)) = (subst_TmVar_Kind (weakenTrace X0 k) (subst_TmVar_Tm d14 s0 s1) (subst_TmVar_Kind (weakenTrace (XS TmVar d14) k) s0 K4))) :=
      match K4 return ((subst_TmVar_Kind (weakenTrace d14 k) s0 (subst_TmVar_Kind (weakenTrace X0 k) s1 K4)) = (subst_TmVar_Kind (weakenTrace X0 k) (subst_TmVar_Tm d14 s0 s1) (subst_TmVar_Kind (weakenTrace (XS TmVar d14) k) s0 K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (subst_TmVar__subst_TmVar_0_Ty_comm_ind T5 k d14 s0 s1) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Kind_comm_ind K5 (HS TmVar k) d14 s0 s1) (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar (XS TmVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TmVar__subst_TmVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) {struct S1} :
    ((subst_TmVar_Ty (weakenTrace d14 k) s0 (subst_TmVar_Ty (weakenTrace X0 k) s1 S1)) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TmVar_Tm d14 s0 s1) (subst_TmVar_Ty (weakenTrace (XS TmVar d14) k) s0 S1))) :=
      match S1 return ((subst_TmVar_Ty (weakenTrace d14 k) s0 (subst_TmVar_Ty (weakenTrace X0 k) s1 S1)) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TmVar_Tm d14 s0 s1) (subst_TmVar_Ty (weakenTrace (XS TmVar d14) k) s0 S1))) with
        | (TVar X8) => eq_refl
        | (TPi T7 T8) => (f_equal2 TPi (subst_TmVar__subst_TmVar_0_Ty_comm_ind T7 k d14 s0 s1) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Ty_comm_ind T8 (HS TmVar k) d14 s0 s1) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar (XS TmVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t7) => (f_equal2 TApp (subst_TmVar__subst_TmVar_0_Ty_comm_ind T6 k d14 s0 s1) (subst_TmVar__subst_TmVar_0_Tm_comm_ind t7 k d14 s0 s1))
      end
    with subst_TmVar__subst_TmVar_0_Tm_comm_ind (s2 : Tm) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) {struct s2} :
    ((subst_TmVar_Tm (weakenTrace d14 k) s0 (subst_TmVar_Tm (weakenTrace X0 k) s1 s2)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d14 s0 s1) (subst_TmVar_Tm (weakenTrace (XS TmVar d14) k) s0 s2))) :=
      match s2 return ((subst_TmVar_Tm (weakenTrace d14 k) s0 (subst_TmVar_Tm (weakenTrace X0 k) s1 s2)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d14 s0 s1) (subst_TmVar_Tm (weakenTrace (XS TmVar d14) k) s0 s2))) with
        | (Var x14) => (subst_TmVar_Tm_subst_TmVar_Index0_commright_ind d14 s0 s1 k x14)
        | (Abs T9 t8) => (f_equal2 Abs (subst_TmVar__subst_TmVar_0_Ty_comm_ind T9 k d14 s0 s1) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t8 (HS TmVar k) d14 s0 s1) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TmVar__subst_TmVar_0_Tm_comm_ind t9 k d14 s0 s1) (subst_TmVar__subst_TmVar_0_Tm_comm_ind t10 k d14 s0 s1))
        | (Let d17 t8) => (f_equal2 Let (subst_TmVar__subst_TmVar_0_Decls_comm_ind d17 k d14 s0 s1) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TmVar__bind _ _ _) (eq_refl H0)))) (weakenTrace_append TmVar d14 k (appendHvl H0 (bind d17)))) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d17))) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d17))) d14 s0 s1) (f_equal3 subst_TmVar_Tm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d17)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d14) k (appendHvl H0 (bind d17)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__subst_TyVar_0_Decls_comm_ind (d15 : Decls) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) {struct d15} :
    ((subst_TmVar_Decls (weakenTrace d14 k) s0 (subst_TyVar_Decls (weakenTrace X0 k) S1 d15)) = (subst_TyVar_Decls (weakenTrace X0 k) (subst_TmVar_Ty d14 s0 S1) (subst_TmVar_Decls (weakenTrace (XS TyVar d14) k) s0 d15))) :=
      match d15 return ((subst_TmVar_Decls (weakenTrace d14 k) s0 (subst_TyVar_Decls (weakenTrace X0 k) S1 d15)) = (subst_TyVar_Decls (weakenTrace X0 k) (subst_TmVar_Ty d14 s0 S1) (subst_TmVar_Decls (weakenTrace (XS TyVar d14) k) s0 d15))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d16) => (f_equal2 DConsTm (subst_TmVar__subst_TyVar_0_Tm_comm_ind t6 k d14 s0 S1) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Decls_comm_ind d16 (HS TmVar k) d14 s0 S1) (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar (XS TyVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (DConsTy K3 d16) => (f_equal2 DConsTy (subst_TmVar__subst_TyVar_0_Kind_comm_ind K3 k d14 s0 S1) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar d14 k (HS TyVar H0)) eq_refl (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Decls_comm_ind d16 (HS TyVar k) d14 s0 S1) (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar (XS TyVar d14) k (HS TyVar H0))) eq_refl eq_refl)))))
      end
    with subst_TmVar__subst_TyVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) {struct K4} :
    ((subst_TmVar_Kind (weakenTrace d14 k) s0 (subst_TyVar_Kind (weakenTrace X0 k) S1 K4)) = (subst_TyVar_Kind (weakenTrace X0 k) (subst_TmVar_Ty d14 s0 S1) (subst_TmVar_Kind (weakenTrace (XS TyVar d14) k) s0 K4))) :=
      match K4 return ((subst_TmVar_Kind (weakenTrace d14 k) s0 (subst_TyVar_Kind (weakenTrace X0 k) S1 K4)) = (subst_TyVar_Kind (weakenTrace X0 k) (subst_TmVar_Ty d14 s0 S1) (subst_TmVar_Kind (weakenTrace (XS TyVar d14) k) s0 K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (subst_TmVar__subst_TyVar_0_Ty_comm_ind T5 k d14 s0 S1) (eq_trans (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Kind_comm_ind K5 (HS TmVar k) d14 s0 S1) (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar (XS TyVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TmVar__subst_TyVar_0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) {struct S2} :
    ((subst_TmVar_Ty (weakenTrace d14 k) s0 (subst_TyVar_Ty (weakenTrace X0 k) S1 S2)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TmVar_Ty d14 s0 S1) (subst_TmVar_Ty (weakenTrace (XS TyVar d14) k) s0 S2))) :=
      match S2 return ((subst_TmVar_Ty (weakenTrace d14 k) s0 (subst_TyVar_Ty (weakenTrace X0 k) S1 S2)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TmVar_Ty d14 s0 S1) (subst_TmVar_Ty (weakenTrace (XS TyVar d14) k) s0 S2))) with
        | (TVar X8) => (subst_TmVar_Ty_subst_TyVar_Index0_commright_ind d14 s0 S1 k X8)
        | (TPi T7 T8) => (f_equal2 TPi (subst_TmVar__subst_TyVar_0_Ty_comm_ind T7 k d14 s0 S1) (eq_trans (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Ty_comm_ind T8 (HS TmVar k) d14 s0 S1) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar (XS TyVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t7) => (f_equal2 TApp (subst_TmVar__subst_TyVar_0_Ty_comm_ind T6 k d14 s0 S1) (subst_TmVar__subst_TyVar_0_Tm_comm_ind t7 k d14 s0 S1))
      end
    with subst_TmVar__subst_TyVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) {struct s1} :
    ((subst_TmVar_Tm (weakenTrace d14 k) s0 (subst_TyVar_Tm (weakenTrace X0 k) S1 s1)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TmVar_Ty d14 s0 S1) (subst_TmVar_Tm (weakenTrace (XS TyVar d14) k) s0 s1))) :=
      match s1 return ((subst_TmVar_Tm (weakenTrace d14 k) s0 (subst_TyVar_Tm (weakenTrace X0 k) S1 s1)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TmVar_Ty d14 s0 S1) (subst_TmVar_Tm (weakenTrace (XS TyVar d14) k) s0 s1))) with
        | (Var x14) => (subst_TmVar_Ty_subst_TyVar_Index0_commleft_ind d14 s0 S1 k x14)
        | (Abs T9 t8) => (f_equal2 Abs (subst_TmVar__subst_TyVar_0_Ty_comm_ind T9 k d14 s0 S1) (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Tm_comm_ind t8 (HS TmVar k) d14 s0 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TyVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TmVar__subst_TyVar_0_Tm_comm_ind t9 k d14 s0 S1) (subst_TmVar__subst_TyVar_0_Tm_comm_ind t10 k d14 s0 S1))
        | (Let d17 t8) => (f_equal2 Let (subst_TmVar__subst_TyVar_0_Decls_comm_ind d17 k d14 s0 S1) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TyVar__bind _ _ _) (eq_refl H0)))) (weakenTrace_append TmVar d14 k (appendHvl H0 (bind d17)))) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d17))) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d17))) d14 s0 S1) (f_equal3 subst_TyVar_Tm (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d17)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TyVar d14) k (appendHvl H0 (bind d17)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__subst_TmVar_0_Decls_comm_ind (d15 : Decls) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) {struct d15} :
    ((subst_TyVar_Decls (weakenTrace d14 k) S1 (subst_TmVar_Decls (weakenTrace X0 k) s0 d15)) = (subst_TmVar_Decls (weakenTrace X0 k) (subst_TyVar_Tm d14 S1 s0) (subst_TyVar_Decls (weakenTrace (XS TmVar d14) k) S1 d15))) :=
      match d15 return ((subst_TyVar_Decls (weakenTrace d14 k) S1 (subst_TmVar_Decls (weakenTrace X0 k) s0 d15)) = (subst_TmVar_Decls (weakenTrace X0 k) (subst_TyVar_Tm d14 S1 s0) (subst_TyVar_Decls (weakenTrace (XS TmVar d14) k) S1 d15))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d16) => (f_equal2 DConsTm (subst_TyVar__subst_TmVar_0_Tm_comm_ind t6 k d14 S1 s0) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Decls_comm_ind d16 (HS TmVar k) d14 S1 s0) (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar (XS TmVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (DConsTy K3 d16) => (f_equal2 DConsTy (subst_TyVar__subst_TmVar_0_Kind_comm_ind K3 k d14 S1 s0) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar d14 k (HS TyVar H0)) eq_refl (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Decls_comm_ind d16 (HS TyVar k) d14 S1 s0) (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar (XS TmVar d14) k (HS TyVar H0))) eq_refl eq_refl)))))
      end
    with subst_TyVar__subst_TmVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) {struct K4} :
    ((subst_TyVar_Kind (weakenTrace d14 k) S1 (subst_TmVar_Kind (weakenTrace X0 k) s0 K4)) = (subst_TmVar_Kind (weakenTrace X0 k) (subst_TyVar_Tm d14 S1 s0) (subst_TyVar_Kind (weakenTrace (XS TmVar d14) k) S1 K4))) :=
      match K4 return ((subst_TyVar_Kind (weakenTrace d14 k) S1 (subst_TmVar_Kind (weakenTrace X0 k) s0 K4)) = (subst_TmVar_Kind (weakenTrace X0 k) (subst_TyVar_Tm d14 S1 s0) (subst_TyVar_Kind (weakenTrace (XS TmVar d14) k) S1 K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (subst_TyVar__subst_TmVar_0_Ty_comm_ind T5 k d14 S1 s0) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Kind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Kind_comm_ind K5 (HS TmVar k) d14 S1 s0) (f_equal3 subst_TmVar_Kind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar (XS TmVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TyVar__subst_TmVar_0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) {struct S2} :
    ((subst_TyVar_Ty (weakenTrace d14 k) S1 (subst_TmVar_Ty (weakenTrace X0 k) s0 S2)) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TyVar_Tm d14 S1 s0) (subst_TyVar_Ty (weakenTrace (XS TmVar d14) k) S1 S2))) :=
      match S2 return ((subst_TyVar_Ty (weakenTrace d14 k) S1 (subst_TmVar_Ty (weakenTrace X0 k) s0 S2)) = (subst_TmVar_Ty (weakenTrace X0 k) (subst_TyVar_Tm d14 S1 s0) (subst_TyVar_Ty (weakenTrace (XS TmVar d14) k) S1 S2))) with
        | (TVar X8) => (subst_TyVar_Tm_subst_TmVar_Index0_commleft_ind d14 S1 s0 k X8)
        | (TPi T7 T8) => (f_equal2 TPi (subst_TyVar__subst_TmVar_0_Ty_comm_ind T7 k d14 S1 s0) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Ty (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Ty_comm_ind T8 (HS TmVar k) d14 S1 s0) (f_equal3 subst_TmVar_Ty (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar (XS TmVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t7) => (f_equal2 TApp (subst_TyVar__subst_TmVar_0_Ty_comm_ind T6 k d14 S1 s0) (subst_TyVar__subst_TmVar_0_Tm_comm_ind t7 k d14 S1 s0))
      end
    with subst_TyVar__subst_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) {struct s1} :
    ((subst_TyVar_Tm (weakenTrace d14 k) S1 (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TyVar_Tm d14 S1 s0) (subst_TyVar_Tm (weakenTrace (XS TmVar d14) k) S1 s1))) :=
      match s1 return ((subst_TyVar_Tm (weakenTrace d14 k) S1 (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TyVar_Tm d14 S1 s0) (subst_TyVar_Tm (weakenTrace (XS TmVar d14) k) S1 s1))) with
        | (Var x14) => (subst_TyVar_Tm_subst_TmVar_Index0_commright_ind d14 S1 s0 k x14)
        | (Abs T9 t8) => (f_equal2 Abs (subst_TyVar__subst_TmVar_0_Ty_comm_ind T9 k d14 S1 s0) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Tm_comm_ind t8 (HS TmVar k) d14 S1 s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TmVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TyVar__subst_TmVar_0_Tm_comm_ind t9 k d14 S1 s0) (subst_TyVar__subst_TmVar_0_Tm_comm_ind t10 k d14 S1 s0))
        | (Let d17 t8) => (f_equal2 Let (subst_TyVar__subst_TmVar_0_Decls_comm_ind d17 k d14 S1 s0) (eq_trans (f_equal3 subst_TyVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TmVar__bind _ _ _) (eq_refl H0)))) (weakenTrace_append TyVar d14 k (appendHvl H0 (bind d17)))) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d17))) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d17))) d14 S1 s0) (f_equal3 subst_TmVar_Tm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d17)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TyVar__bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TmVar d14) k (appendHvl H0 (bind d17)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__subst_TyVar_0_Decls_comm_ind (d15 : Decls) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) {struct d15} :
    ((subst_TyVar_Decls (weakenTrace d14 k) S1 (subst_TyVar_Decls (weakenTrace X0 k) S2 d15)) = (subst_TyVar_Decls (weakenTrace X0 k) (subst_TyVar_Ty d14 S1 S2) (subst_TyVar_Decls (weakenTrace (XS TyVar d14) k) S1 d15))) :=
      match d15 return ((subst_TyVar_Decls (weakenTrace d14 k) S1 (subst_TyVar_Decls (weakenTrace X0 k) S2 d15)) = (subst_TyVar_Decls (weakenTrace X0 k) (subst_TyVar_Ty d14 S1 S2) (subst_TyVar_Decls (weakenTrace (XS TyVar d14) k) S1 d15))) with
        | (DNil) => eq_refl
        | (DConsTm t6 d16) => (f_equal2 DConsTm (subst_TyVar__subst_TyVar_0_Tm_comm_ind t6 k d14 S1 S2) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Decls_comm_ind d16 (HS TmVar k) d14 S1 S2) (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar (XS TyVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (DConsTy K3 d16) => (f_equal2 DConsTy (subst_TyVar__subst_TyVar_0_Kind_comm_ind K3 k d14 S1 S2) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar d14 k (HS TyVar H0)) eq_refl (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Decls_comm_ind d16 (HS TyVar k) d14 S1 S2) (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar (XS TyVar d14) k (HS TyVar H0))) eq_refl eq_refl)))))
      end
    with subst_TyVar__subst_TyVar_0_Kind_comm_ind (K4 : Kind) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) {struct K4} :
    ((subst_TyVar_Kind (weakenTrace d14 k) S1 (subst_TyVar_Kind (weakenTrace X0 k) S2 K4)) = (subst_TyVar_Kind (weakenTrace X0 k) (subst_TyVar_Ty d14 S1 S2) (subst_TyVar_Kind (weakenTrace (XS TyVar d14) k) S1 K4))) :=
      match K4 return ((subst_TyVar_Kind (weakenTrace d14 k) S1 (subst_TyVar_Kind (weakenTrace X0 k) S2 K4)) = (subst_TyVar_Kind (weakenTrace X0 k) (subst_TyVar_Ty d14 S1 S2) (subst_TyVar_Kind (weakenTrace (XS TyVar d14) k) S1 K4))) with
        | (Star) => eq_refl
        | (KPi T5 K5) => (f_equal2 KPi (subst_TyVar__subst_TyVar_0_Ty_comm_ind T5 k d14 S1 S2) (eq_trans (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Kind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Kind_comm_ind K5 (HS TmVar k) d14 S1 S2) (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Kind (eq_sym (weakenTrace_append TyVar (XS TyVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TyVar__subst_TyVar_0_Ty_comm_ind (S3 : Ty) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) {struct S3} :
    ((subst_TyVar_Ty (weakenTrace d14 k) S1 (subst_TyVar_Ty (weakenTrace X0 k) S2 S3)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d14 S1 S2) (subst_TyVar_Ty (weakenTrace (XS TyVar d14) k) S1 S3))) :=
      match S3 return ((subst_TyVar_Ty (weakenTrace d14 k) S1 (subst_TyVar_Ty (weakenTrace X0 k) S2 S3)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d14 S1 S2) (subst_TyVar_Ty (weakenTrace (XS TyVar d14) k) S1 S3))) with
        | (TVar X8) => (subst_TyVar_Ty_subst_TyVar_Index0_commright_ind d14 S1 S2 k X8)
        | (TPi T7 T8) => (f_equal2 TPi (subst_TyVar__subst_TyVar_0_Ty_comm_ind T7 k d14 S1 S2) (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Ty_comm_ind T8 (HS TmVar k) d14 S1 S2) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar (XS TyVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (TApp T6 t7) => (f_equal2 TApp (subst_TyVar__subst_TyVar_0_Ty_comm_ind T6 k d14 S1 S2) (subst_TyVar__subst_TyVar_0_Tm_comm_ind t7 k d14 S1 S2))
      end
    with subst_TyVar__subst_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) {struct s0} :
    ((subst_TyVar_Tm (weakenTrace d14 k) S1 (subst_TyVar_Tm (weakenTrace X0 k) S2 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TyVar_Ty d14 S1 S2) (subst_TyVar_Tm (weakenTrace (XS TyVar d14) k) S1 s0))) :=
      match s0 return ((subst_TyVar_Tm (weakenTrace d14 k) S1 (subst_TyVar_Tm (weakenTrace X0 k) S2 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TyVar_Ty d14 S1 S2) (subst_TyVar_Tm (weakenTrace (XS TyVar d14) k) S1 s0))) with
        | (Var x14) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs (subst_TyVar__subst_TyVar_0_Ty_comm_ind T9 k d14 S1 S2) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d14 k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Tm_comm_ind t8 (HS TmVar k) d14 S1 S2) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TyVar d14) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TyVar__subst_TyVar_0_Tm_comm_ind t9 k d14 S1 S2) (subst_TyVar__subst_TyVar_0_Tm_comm_ind t10 k d14 S1 S2))
        | (Let d17 t8) => (f_equal2 Let (subst_TyVar__subst_TyVar_0_Decls_comm_ind d17 k d14 S1 S2) (eq_trans (f_equal3 subst_TyVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TyVar__bind _ _ _) (eq_refl H0)))) (weakenTrace_append TyVar d14 k (appendHvl H0 (bind d17)))) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d17))) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d17))) d14 S1 S2) (f_equal3 subst_TyVar_Tm (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d17)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TyVar__bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TyVar d14) k (appendHvl H0 (bind d17)))) eq_refl eq_refl)))))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition subst_TmVar_Decls_subst_TmVar_Decls0_comm (d15 : Decls) : (forall (d14 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) ,
      ((subst_TmVar_Decls d14 s0 (subst_TmVar_Decls X0 s1 d15)) = (subst_TmVar_Decls X0 (subst_TmVar_Tm d14 s0 s1) (subst_TmVar_Decls (XS TmVar d14) s0 d15)))) := (subst_TmVar__subst_TmVar_0_Decls_comm_ind d15 H0).
    Definition subst_TmVar_Kind_subst_TmVar_Kind0_comm (K3 : Kind) : (forall (d14 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) ,
      ((subst_TmVar_Kind d14 s0 (subst_TmVar_Kind X0 s1 K3)) = (subst_TmVar_Kind X0 (subst_TmVar_Tm d14 s0 s1) (subst_TmVar_Kind (XS TmVar d14) s0 K3)))) := (subst_TmVar__subst_TmVar_0_Kind_comm_ind K3 H0).
    Definition subst_TmVar_Ty_subst_TmVar_Ty0_comm (S1 : Ty) : (forall (d14 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) ,
      ((subst_TmVar_Ty d14 s0 (subst_TmVar_Ty X0 s1 S1)) = (subst_TmVar_Ty X0 (subst_TmVar_Tm d14 s0 s1) (subst_TmVar_Ty (XS TmVar d14) s0 S1)))) := (subst_TmVar__subst_TmVar_0_Ty_comm_ind S1 H0).
    Definition subst_TmVar_Tm_subst_TmVar_Tm0_comm (s2 : Tm) : (forall (d14 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) ,
      ((subst_TmVar_Tm d14 s0 (subst_TmVar_Tm X0 s1 s2)) = (subst_TmVar_Tm X0 (subst_TmVar_Tm d14 s0 s1) (subst_TmVar_Tm (XS TmVar d14) s0 s2)))) := (subst_TmVar__subst_TmVar_0_Tm_comm_ind s2 H0).
    Definition subst_TmVar_Decls_subst_TyVar_Decls0_comm (d15 : Decls) : (forall (d14 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) ,
      ((subst_TmVar_Decls d14 s0 (subst_TyVar_Decls X0 S1 d15)) = (subst_TyVar_Decls X0 (subst_TmVar_Ty d14 s0 S1) (subst_TmVar_Decls (XS TyVar d14) s0 d15)))) := (subst_TmVar__subst_TyVar_0_Decls_comm_ind d15 H0).
    Definition subst_TmVar_Kind_subst_TyVar_Kind0_comm (K3 : Kind) : (forall (d14 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) ,
      ((subst_TmVar_Kind d14 s0 (subst_TyVar_Kind X0 S1 K3)) = (subst_TyVar_Kind X0 (subst_TmVar_Ty d14 s0 S1) (subst_TmVar_Kind (XS TyVar d14) s0 K3)))) := (subst_TmVar__subst_TyVar_0_Kind_comm_ind K3 H0).
    Definition subst_TmVar_Ty_subst_TyVar_Ty0_comm (S2 : Ty) : (forall (d14 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) ,
      ((subst_TmVar_Ty d14 s0 (subst_TyVar_Ty X0 S1 S2)) = (subst_TyVar_Ty X0 (subst_TmVar_Ty d14 s0 S1) (subst_TmVar_Ty (XS TyVar d14) s0 S2)))) := (subst_TmVar__subst_TyVar_0_Ty_comm_ind S2 H0).
    Definition subst_TmVar_Tm_subst_TyVar_Tm0_comm (s1 : Tm) : (forall (d14 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) ,
      ((subst_TmVar_Tm d14 s0 (subst_TyVar_Tm X0 S1 s1)) = (subst_TyVar_Tm X0 (subst_TmVar_Ty d14 s0 S1) (subst_TmVar_Tm (XS TyVar d14) s0 s1)))) := (subst_TmVar__subst_TyVar_0_Tm_comm_ind s1 H0).
    Definition subst_TyVar_Decls_subst_TmVar_Decls0_comm (d15 : Decls) : (forall (d14 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) ,
      ((subst_TyVar_Decls d14 S1 (subst_TmVar_Decls X0 s0 d15)) = (subst_TmVar_Decls X0 (subst_TyVar_Tm d14 S1 s0) (subst_TyVar_Decls (XS TmVar d14) S1 d15)))) := (subst_TyVar__subst_TmVar_0_Decls_comm_ind d15 H0).
    Definition subst_TyVar_Kind_subst_TmVar_Kind0_comm (K3 : Kind) : (forall (d14 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) ,
      ((subst_TyVar_Kind d14 S1 (subst_TmVar_Kind X0 s0 K3)) = (subst_TmVar_Kind X0 (subst_TyVar_Tm d14 S1 s0) (subst_TyVar_Kind (XS TmVar d14) S1 K3)))) := (subst_TyVar__subst_TmVar_0_Kind_comm_ind K3 H0).
    Definition subst_TyVar_Ty_subst_TmVar_Ty0_comm (S2 : Ty) : (forall (d14 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) ,
      ((subst_TyVar_Ty d14 S1 (subst_TmVar_Ty X0 s0 S2)) = (subst_TmVar_Ty X0 (subst_TyVar_Tm d14 S1 s0) (subst_TyVar_Ty (XS TmVar d14) S1 S2)))) := (subst_TyVar__subst_TmVar_0_Ty_comm_ind S2 H0).
    Definition subst_TyVar_Tm_subst_TmVar_Tm0_comm (s1 : Tm) : (forall (d14 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) ,
      ((subst_TyVar_Tm d14 S1 (subst_TmVar_Tm X0 s0 s1)) = (subst_TmVar_Tm X0 (subst_TyVar_Tm d14 S1 s0) (subst_TyVar_Tm (XS TmVar d14) S1 s1)))) := (subst_TyVar__subst_TmVar_0_Tm_comm_ind s1 H0).
    Definition subst_TyVar_Decls_subst_TyVar_Decls0_comm (d15 : Decls) : (forall (d14 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) ,
      ((subst_TyVar_Decls d14 S1 (subst_TyVar_Decls X0 S2 d15)) = (subst_TyVar_Decls X0 (subst_TyVar_Ty d14 S1 S2) (subst_TyVar_Decls (XS TyVar d14) S1 d15)))) := (subst_TyVar__subst_TyVar_0_Decls_comm_ind d15 H0).
    Definition subst_TyVar_Kind_subst_TyVar_Kind0_comm (K3 : Kind) : (forall (d14 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) ,
      ((subst_TyVar_Kind d14 S1 (subst_TyVar_Kind X0 S2 K3)) = (subst_TyVar_Kind X0 (subst_TyVar_Ty d14 S1 S2) (subst_TyVar_Kind (XS TyVar d14) S1 K3)))) := (subst_TyVar__subst_TyVar_0_Kind_comm_ind K3 H0).
    Definition subst_TyVar_Ty_subst_TyVar_Ty0_comm (S3 : Ty) : (forall (d14 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) ,
      ((subst_TyVar_Ty d14 S1 (subst_TyVar_Ty X0 S2 S3)) = (subst_TyVar_Ty X0 (subst_TyVar_Ty d14 S1 S2) (subst_TyVar_Ty (XS TyVar d14) S1 S3)))) := (subst_TyVar__subst_TyVar_0_Ty_comm_ind S3 H0).
    Definition subst_TyVar_Tm_subst_TyVar_Tm0_comm (s0 : Tm) : (forall (d14 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) ,
      ((subst_TyVar_Tm d14 S1 (subst_TyVar_Tm X0 S2 s0)) = (subst_TyVar_Tm X0 (subst_TyVar_Ty d14 S1 S2) (subst_TyVar_Tm (XS TyVar d14) S1 s0)))) := (subst_TyVar__subst_TyVar_0_Tm_comm_ind s0 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenDecls_subst_TmVar_Decls  :
      (forall (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) (d15 : Decls) ,
        ((weakenDecls (subst_TmVar_Decls d14 s0 d15) k) = (subst_TmVar_Decls (weakenTrace d14 k) s0 (weakenDecls d15 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenKind_subst_TmVar_Kind  :
      (forall (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) (K3 : Kind) ,
        ((weakenKind (subst_TmVar_Kind d14 s0 K3) k) = (subst_TmVar_Kind (weakenTrace d14 k) s0 (weakenKind K3 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTy_subst_TmVar_Ty  :
      (forall (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) ,
        ((weakenTy (subst_TmVar_Ty d14 s0 S1) k) = (subst_TmVar_Ty (weakenTrace d14 k) s0 (weakenTy S1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_subst_TmVar_Tm  :
      (forall (k : Hvl) (d14 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) ,
        ((weakenTm (subst_TmVar_Tm d14 s0 s1) k) = (subst_TmVar_Tm (weakenTrace d14 k) s0 (weakenTm s1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenDecls_subst_TyVar_Decls  :
      (forall (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) (d15 : Decls) ,
        ((weakenDecls (subst_TyVar_Decls d14 S1 d15) k) = (subst_TyVar_Decls (weakenTrace d14 k) S1 (weakenDecls d15 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenKind_subst_TyVar_Kind  :
      (forall (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) (K3 : Kind) ,
        ((weakenKind (subst_TyVar_Kind d14 S1 K3) k) = (subst_TyVar_Kind (weakenTrace d14 k) S1 (weakenKind K3 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTy_subst_TyVar_Ty  :
      (forall (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) ,
        ((weakenTy (subst_TyVar_Ty d14 S1 S2) k) = (subst_TyVar_Ty (weakenTrace d14 k) S1 (weakenTy S2 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_subst_TyVar_Tm  :
      (forall (k : Hvl) (d14 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) ,
        ((weakenTm (subst_TyVar_Tm d14 S1 s0) k) = (subst_TyVar_Tm (weakenTrace d14 k) S1 (weakenTm s0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite subst_TmVar_Decls_subst_TmVar_Decls0_comm subst_TyVar_Decls_subst_TyVar_Decls0_comm subst_TmVar_Kind_subst_TmVar_Kind0_comm subst_TyVar_Kind_subst_TyVar_Kind0_comm subst_TmVar_Tm_subst_TmVar_Tm0_comm subst_TyVar_Tm_subst_TyVar_Tm0_comm subst_TmVar_Ty_subst_TmVar_Ty0_comm subst_TyVar_Ty_subst_TyVar_Ty0_comm : interaction.
 Hint Rewrite subst_TmVar_Decls_subst_TmVar_Decls0_comm subst_TyVar_Decls_subst_TyVar_Decls0_comm subst_TmVar_Kind_subst_TmVar_Kind0_comm subst_TyVar_Kind_subst_TyVar_Kind0_comm subst_TmVar_Tm_subst_TmVar_Tm0_comm subst_TyVar_Tm_subst_TyVar_Tm0_comm subst_TmVar_Ty_subst_TmVar_Ty0_comm subst_TyVar_Ty_subst_TyVar_Ty0_comm : subst_subst0.
 Hint Rewrite weakenDecls_shift_TmVar_Decls weakenDecls_shift_TyVar_Decls weakenKind_shift_TmVar_Kind weakenKind_shift_TyVar_Kind weakenTm_shift_TmVar_Tm weakenTm_shift_TyVar_Tm weakenTy_shift_TmVar_Ty weakenTy_shift_TyVar_Ty : weaken_shift.
 Hint Rewrite weakenDecls_subst_TmVar_Decls weakenDecls_subst_TyVar_Decls weakenKind_subst_TmVar_Kind weakenKind_subst_TyVar_Kind weakenTm_subst_TmVar_Tm weakenTm_subst_TyVar_Tm weakenTy_subst_TmVar_Ty weakenTy_subst_TyVar_Ty : weaken_subst.
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
  Inductive wfDecls (k : Hvl) : Decls -> Prop :=
    | wfDecls_DNil :
        (wfDecls k (DNil))
    | wfDecls_DConsTm {t6 : Tm}
        (wf : (wfTm k t6)) {d14 : Decls}
        (wf0 : (wfDecls (HS TmVar k) d14))
        : (wfDecls k (DConsTm t6 d14))
    | wfDecls_DConsTy {K3 : Kind}
        (wf : (wfKind k K3))
        {d15 : Decls}
        (wf0 : (wfDecls (HS TyVar k) d15))
        : (wfDecls k (DConsTy K3 d15))
  with wfKind (k : Hvl) : Kind -> Prop :=
    | wfKind_Star :
        (wfKind k (Star))
    | wfKind_KPi {T5 : Ty}
        (wf : (wfTy k T5)) {K3 : Kind}
        (wf0 : (wfKind (HS TmVar k) K3))
        : (wfKind k (KPi T5 K3))
  with wfTy (k : Hvl) : Ty -> Prop :=
    | wfTy_TVar
        (X7 : (Index TyVar))
        (wfi : (wfindex k X7)) :
        (wfTy k (TVar X7))
    | wfTy_TPi {T5 : Ty}
        (wf : (wfTy k T5)) {T6 : Ty}
        (wf0 : (wfTy (HS TmVar k) T6)) :
        (wfTy k (TPi T5 T6))
    | wfTy_TApp {T7 : Ty}
        (wf : (wfTy k T7)) {t6 : Tm}
        (wf0 : (wfTm k t6)) :
        (wfTy k (TApp T7 t6))
  with wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_Var
        (x11 : (Index TmVar))
        (wfi : (wfindex k x11)) :
        (wfTm k (Var x11))
    | wfTm_Abs {T5 : Ty}
        (wf : (wfTy k T5)) {t6 : Tm}
        (wf0 : (wfTm (HS TmVar k) t6)) :
        (wfTm k (Abs T5 t6))
    | wfTm_App {t7 : Tm}
        (wf : (wfTm k t7)) {t8 : Tm}
        (wf0 : (wfTm k t8)) :
        (wfTm k (App t7 t8))
    | wfTm_Let {d14 : Decls}
        (wf : (wfDecls k d14)) {t9 : Tm}
        (wf0 : (wfTm (appendHvl k (appendHvl H0 (bind d14))) t9))
        : (wfTm k (Let d14 t9)).
  Definition inversion_wfDecls_DConsTm_1 (k0 : Hvl) (t : Tm) (d : Decls) (H22 : (wfDecls k0 (DConsTm t d))) : (wfTm k0 t) := match H22 in (wfDecls _ d15) return match d15 return Prop with
    | (DConsTm t d) => (wfTm k0 t)
    | _ => True
  end with
    | (wfDecls_DConsTm t H1 d H2) => H1
    | _ => I
  end.
  Definition inversion_wfDecls_DConsTm_2 (k0 : Hvl) (t : Tm) (d : Decls) (H22 : (wfDecls k0 (DConsTm t d))) : (wfDecls (HS TmVar k0) d) := match H22 in (wfDecls _ d15) return match d15 return Prop with
    | (DConsTm t d) => (wfDecls (HS TmVar k0) d)
    | _ => True
  end with
    | (wfDecls_DConsTm t H1 d H2) => H2
    | _ => I
  end.
  Definition inversion_wfDecls_DConsTy_1 (k1 : Hvl) (K : Kind) (d : Decls) (H23 : (wfDecls k1 (DConsTy K d))) : (wfKind k1 K) := match H23 in (wfDecls _ d16) return match d16 return Prop with
    | (DConsTy K d) => (wfKind k1 K)
    | _ => True
  end with
    | (wfDecls_DConsTy K H3 d H4) => H3
    | _ => I
  end.
  Definition inversion_wfDecls_DConsTy_2 (k1 : Hvl) (K : Kind) (d : Decls) (H23 : (wfDecls k1 (DConsTy K d))) : (wfDecls (HS TyVar k1) d) := match H23 in (wfDecls _ d16) return match d16 return Prop with
    | (DConsTy K d) => (wfDecls (HS TyVar k1) d)
    | _ => True
  end with
    | (wfDecls_DConsTy K H3 d H4) => H4
    | _ => I
  end.
  Definition inversion_wfKind_KPi_1 (k3 : Hvl) (T : Ty) (K : Kind) (H25 : (wfKind k3 (KPi T K))) : (wfTy k3 T) := match H25 in (wfKind _ K4) return match K4 return Prop with
    | (KPi T K) => (wfTy k3 T)
    | _ => True
  end with
    | (wfKind_KPi T H5 K H6) => H5
    | _ => I
  end.
  Definition inversion_wfKind_KPi_2 (k3 : Hvl) (T : Ty) (K : Kind) (H25 : (wfKind k3 (KPi T K))) : (wfKind (HS TmVar k3) K) := match H25 in (wfKind _ K4) return match K4 return Prop with
    | (KPi T K) => (wfKind (HS TmVar k3) K)
    | _ => True
  end with
    | (wfKind_KPi T H5 K H6) => H6
    | _ => I
  end.
  Definition inversion_wfTy_TVar_1 (k4 : Hvl) (X : (Index TyVar)) (H26 : (wfTy k4 (TVar X))) : (wfindex k4 X) := match H26 in (wfTy _ S1) return match S1 return Prop with
    | (TVar X) => (wfindex k4 X)
    | _ => True
  end with
    | (wfTy_TVar X H7) => H7
    | _ => I
  end.
  Definition inversion_wfTy_TPi_1 (k5 : Hvl) (T1 : Ty) (T2 : Ty) (H27 : (wfTy k5 (TPi T1 T2))) : (wfTy k5 T1) := match H27 in (wfTy _ S2) return match S2 return Prop with
    | (TPi T1 T2) => (wfTy k5 T1)
    | _ => True
  end with
    | (wfTy_TPi T1 H8 T2 H9) => H8
    | _ => I
  end.
  Definition inversion_wfTy_TPi_2 (k5 : Hvl) (T1 : Ty) (T2 : Ty) (H27 : (wfTy k5 (TPi T1 T2))) : (wfTy (HS TmVar k5) T2) := match H27 in (wfTy _ S2) return match S2 return Prop with
    | (TPi T1 T2) => (wfTy (HS TmVar k5) T2)
    | _ => True
  end with
    | (wfTy_TPi T1 H8 T2 H9) => H9
    | _ => I
  end.
  Definition inversion_wfTy_TApp_0 (k6 : Hvl) (T : Ty) (t : Tm) (H28 : (wfTy k6 (TApp T t))) : (wfTy k6 T) := match H28 in (wfTy _ S3) return match S3 return Prop with
    | (TApp T t) => (wfTy k6 T)
    | _ => True
  end with
    | (wfTy_TApp T H10 t H11) => H10
    | _ => I
  end.
  Definition inversion_wfTy_TApp_1 (k6 : Hvl) (T : Ty) (t : Tm) (H28 : (wfTy k6 (TApp T t))) : (wfTm k6 t) := match H28 in (wfTy _ S3) return match S3 return Prop with
    | (TApp T t) => (wfTm k6 t)
    | _ => True
  end with
    | (wfTy_TApp T H10 t H11) => H11
    | _ => I
  end.
  Definition inversion_wfTm_Var_1 (k7 : Hvl) (x : (Index TmVar)) (H29 : (wfTm k7 (Var x))) : (wfindex k7 x) := match H29 in (wfTm _ s0) return match s0 return Prop with
    | (Var x) => (wfindex k7 x)
    | _ => True
  end with
    | (wfTm_Var x H12) => H12
    | _ => I
  end.
  Definition inversion_wfTm_Abs_1 (k8 : Hvl) (T : Ty) (t : Tm) (H30 : (wfTm k8 (Abs T t))) : (wfTy k8 T) := match H30 in (wfTm _ s1) return match s1 return Prop with
    | (Abs T t) => (wfTy k8 T)
    | _ => True
  end with
    | (wfTm_Abs T H13 t H14) => H13
    | _ => I
  end.
  Definition inversion_wfTm_Abs_2 (k8 : Hvl) (T : Ty) (t : Tm) (H30 : (wfTm k8 (Abs T t))) : (wfTm (HS TmVar k8) t) := match H30 in (wfTm _ s1) return match s1 return Prop with
    | (Abs T t) => (wfTm (HS TmVar k8) t)
    | _ => True
  end with
    | (wfTm_Abs T H13 t H14) => H14
    | _ => I
  end.
  Definition inversion_wfTm_App_0 (k9 : Hvl) (t1 : Tm) (t2 : Tm) (H31 : (wfTm k9 (App t1 t2))) : (wfTm k9 t1) := match H31 in (wfTm _ s2) return match s2 return Prop with
    | (App t1 t2) => (wfTm k9 t1)
    | _ => True
  end with
    | (wfTm_App t1 H15 t2 H16) => H15
    | _ => I
  end.
  Definition inversion_wfTm_App_1 (k9 : Hvl) (t1 : Tm) (t2 : Tm) (H31 : (wfTm k9 (App t1 t2))) : (wfTm k9 t2) := match H31 in (wfTm _ s2) return match s2 return Prop with
    | (App t1 t2) => (wfTm k9 t2)
    | _ => True
  end with
    | (wfTm_App t1 H15 t2 H16) => H16
    | _ => I
  end.
  Definition inversion_wfTm_Let_0 (k10 : Hvl) (d : Decls) (t : Tm) (H32 : (wfTm k10 (Let d t))) : (wfDecls k10 d) := match H32 in (wfTm _ s3) return match s3 return Prop with
    | (Let d t) => (wfDecls k10 d)
    | _ => True
  end with
    | (wfTm_Let d H17 t H18) => H17
    | _ => I
  end.
  Definition inversion_wfTm_Let_1 (k10 : Hvl) (d : Decls) (t : Tm) (H32 : (wfTm k10 (Let d t))) : (wfTm (appendHvl k10 (appendHvl H0 (bind d))) t) := match H32 in (wfTm _ s3) return match s3 return Prop with
    | (Let d t) => (wfTm (appendHvl k10 (appendHvl H0 (bind d))) t)
    | _ => True
  end with
    | (wfTm_Let d H17 t H18) => H18
    | _ => I
  end.
  Scheme ind_wfDecls := Induction for wfDecls Sort Prop
  with ind_wfKind := Induction for wfKind Sort Prop
  with ind_wfTy := Induction for wfTy Sort Prop
  with ind_wfTm := Induction for wfTm Sort Prop.
  Combined Scheme ind_wfDecls_Kind_Ty_Tm from ind_wfDecls, ind_wfKind, ind_wfTy, ind_wfTm.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_TmVar : (forall (c1 : (Cutoff TmVar)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | shifthvl_TmVar_here
        (k11 : Hvl) :
        (shifthvl_TmVar C0 k11 (HS TmVar k11))
    | shifthvl_TmVar_there_TmVar
        (c1 : (Cutoff TmVar))
        (k11 : Hvl) (k12 : Hvl) :
        (shifthvl_TmVar c1 k11 k12) -> (shifthvl_TmVar (CS c1) (HS TmVar k11) (HS TmVar k12))
    | shifthvl_TmVar_there_TyVar
        (c1 : (Cutoff TmVar))
        (k11 : Hvl) (k12 : Hvl) :
        (shifthvl_TmVar c1 k11 k12) -> (shifthvl_TmVar c1 (HS TyVar k11) (HS TyVar k12)).
  Inductive shifthvl_TyVar : (forall (c1 : (Cutoff TyVar)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | shifthvl_TyVar_here
        (k11 : Hvl) :
        (shifthvl_TyVar C0 k11 (HS TyVar k11))
    | shifthvl_TyVar_there_TmVar
        (c1 : (Cutoff TyVar))
        (k11 : Hvl) (k12 : Hvl) :
        (shifthvl_TyVar c1 k11 k12) -> (shifthvl_TyVar c1 (HS TmVar k11) (HS TmVar k12))
    | shifthvl_TyVar_there_TyVar
        (c1 : (Cutoff TyVar))
        (k11 : Hvl) (k12 : Hvl) :
        (shifthvl_TyVar c1 k11 k12) -> (shifthvl_TyVar (CS c1) (HS TyVar k11) (HS TyVar k12)).
  Lemma weaken_shifthvl_TmVar  :
    (forall (k11 : Hvl) {c1 : (Cutoff TmVar)} {k12 : Hvl} {k13 : Hvl} ,
      (shifthvl_TmVar c1 k12 k13) -> (shifthvl_TmVar (weakenCutoffTmVar c1 k11) (appendHvl k12 k11) (appendHvl k13 k11))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_TyVar  :
    (forall (k11 : Hvl) {c1 : (Cutoff TyVar)} {k12 : Hvl} {k13 : Hvl} ,
      (shifthvl_TyVar c1 k12 k13) -> (shifthvl_TyVar (weakenCutoffTyVar c1 k11) (appendHvl k12 k11) (appendHvl k13 k11))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_TmVar__wfindex_TmVar  :
    (forall (c1 : (Cutoff TmVar)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_TmVar c1 k11 k12)) (x11 : (Index TmVar)) ,
      (wfindex k11 x11) -> (wfindex k12 (shift_TmVar_Index c1 x11))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TmVar__wfindex_TyVar  :
    (forall (c1 : (Cutoff TmVar)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_TmVar c1 k11 k12)) (X7 : (Index TyVar)) ,
      (wfindex k11 X7) -> (wfindex k12 X7)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TyVar__wfindex_TmVar  :
    (forall (c1 : (Cutoff TyVar)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_TyVar c1 k11 k12)) (x11 : (Index TmVar)) ,
      (wfindex k11 x11) -> (wfindex k12 x11)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TyVar__wfindex_TyVar  :
    (forall (c1 : (Cutoff TyVar)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_TyVar c1 k11 k12)) (X7 : (Index TyVar)) ,
      (wfindex k11 X7) -> (wfindex k12 (shift_TyVar_Index c1 X7))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_TmVar__wfDecls_Kind_Ty_Tm : (forall (k11 : Hvl) ,
    (forall (d17 : Decls) (wf : (wfDecls k11 d17)) ,
      (forall (c1 : (Cutoff TmVar)) (k12 : Hvl) ,
        (shifthvl_TmVar c1 k11 k12) -> (wfDecls k12 (shift_TmVar_Decls c1 d17)))) /\
    (forall (K5 : Kind) (wf : (wfKind k11 K5)) ,
      (forall (c1 : (Cutoff TmVar)) (k12 : Hvl) ,
        (shifthvl_TmVar c1 k11 k12) -> (wfKind k12 (shift_TmVar_Kind c1 K5)))) /\
    (forall (S4 : Ty) (wf : (wfTy k11 S4)) ,
      (forall (c1 : (Cutoff TmVar)) (k12 : Hvl) ,
        (shifthvl_TmVar c1 k11 k12) -> (wfTy k12 (shift_TmVar_Ty c1 S4)))) /\
    (forall (s4 : Tm) (wf : (wfTm k11 s4)) ,
      (forall (c1 : (Cutoff TmVar)) (k12 : Hvl) ,
        (shifthvl_TmVar c1 k11 k12) -> (wfTm k12 (shift_TmVar_Tm c1 s4))))) := (ind_wfDecls_Kind_Ty_Tm (fun (k11 : Hvl) (d17 : Decls) (wf : (wfDecls k11 d17)) =>
    (forall (c1 : (Cutoff TmVar)) (k12 : Hvl) ,
      (shifthvl_TmVar c1 k11 k12) -> (wfDecls k12 (shift_TmVar_Decls c1 d17)))) (fun (k11 : Hvl) (K5 : Kind) (wf : (wfKind k11 K5)) =>
    (forall (c1 : (Cutoff TmVar)) (k12 : Hvl) ,
      (shifthvl_TmVar c1 k11 k12) -> (wfKind k12 (shift_TmVar_Kind c1 K5)))) (fun (k11 : Hvl) (S4 : Ty) (wf : (wfTy k11 S4)) =>
    (forall (c1 : (Cutoff TmVar)) (k12 : Hvl) ,
      (shifthvl_TmVar c1 k11 k12) -> (wfTy k12 (shift_TmVar_Ty c1 S4)))) (fun (k11 : Hvl) (s4 : Tm) (wf : (wfTm k11 s4)) =>
    (forall (c1 : (Cutoff TmVar)) (k12 : Hvl) ,
      (shifthvl_TmVar c1 k11 k12) -> (wfTm k12 (shift_TmVar_Tm c1 s4)))) (fun (k11 : Hvl) (c1 : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c1 k11 k12)) =>
    (wfDecls_DNil k12)) (fun (k11 : Hvl) (t : Tm) (wf : (wfTm k11 t)) IHt (d : Decls) (wf0 : (wfDecls (HS TmVar k11) d)) IHd (c1 : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c1 k11 k12)) =>
    (wfDecls_DConsTm k12 (IHt c1 k12 (weaken_shifthvl_TmVar H0 ins)) (IHd (CS c1) (HS TmVar k12) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k11 : Hvl) (K : Kind) (wf : (wfKind k11 K)) IHK (d : Decls) (wf0 : (wfDecls (HS TyVar k11) d)) IHd (c1 : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c1 k11 k12)) =>
    (wfDecls_DConsTy k12 (IHK c1 k12 (weaken_shifthvl_TmVar H0 ins)) (IHd c1 (HS TyVar k12) (weaken_shifthvl_TmVar (HS TyVar H0) ins)))) (fun (k11 : Hvl) (c1 : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c1 k11 k12)) =>
    (wfKind_Star k12)) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) IHT (K : Kind) (wf0 : (wfKind (HS TmVar k11) K)) IHK (c1 : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c1 k11 k12)) =>
    (wfKind_KPi k12 (IHT c1 k12 (weaken_shifthvl_TmVar H0 ins)) (IHK (CS c1) (HS TmVar k12) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k11 : Hvl) (X7 : (Index TyVar)) (wfi : (wfindex k11 X7)) (c1 : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c1 k11 k12)) =>
    (wfTy_TVar k12 _ (shift_TmVar__wfindex_TyVar c1 k11 k12 ins X7 wfi))) (fun (k11 : Hvl) (T1 : Ty) (wf : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS TmVar k11) T2)) IHT2 (c1 : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c1 k11 k12)) =>
    (wfTy_TPi k12 (IHT1 c1 k12 (weaken_shifthvl_TmVar H0 ins)) (IHT2 (CS c1) (HS TmVar k12) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) IHT (t : Tm) (wf0 : (wfTm k11 t)) IHt (c1 : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c1 k11 k12)) =>
    (wfTy_TApp k12 (IHT c1 k12 (weaken_shifthvl_TmVar H0 ins)) (IHt c1 k12 (weaken_shifthvl_TmVar H0 ins)))) (fun (k11 : Hvl) (x11 : (Index TmVar)) (wfi : (wfindex k11 x11)) (c1 : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c1 k11 k12)) =>
    (wfTm_Var k12 _ (shift_TmVar__wfindex_TmVar c1 k11 k12 ins x11 wfi))) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) IHT (t : Tm) (wf0 : (wfTm (HS TmVar k11) t)) IHt (c1 : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c1 k11 k12)) =>
    (wfTm_Abs k12 (IHT c1 k12 (weaken_shifthvl_TmVar H0 ins)) (IHt (CS c1) (HS TmVar k12) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k11 : Hvl) (t1 : Tm) (wf : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k11 t2)) IHt2 (c1 : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c1 k11 k12)) =>
    (wfTm_App k12 (IHt1 c1 k12 (weaken_shifthvl_TmVar H0 ins)) (IHt2 c1 k12 (weaken_shifthvl_TmVar H0 ins)))) (fun (k11 : Hvl) (d : Decls) (wf : (wfDecls k11 d)) IHd (t : Tm) (wf0 : (wfTm (appendHvl k11 (appendHvl H0 (bind d))) t)) IHt (c1 : (Cutoff TmVar)) (k12 : Hvl) (ins : (shifthvl_TmVar c1 k11 k12)) =>
    (wfTm_Let k12 (IHd c1 k12 (weaken_shifthvl_TmVar H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k12) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _)))) eq_refl (IHt (weakenCutoffTmVar c1 (appendHvl H0 (bind d))) (appendHvl k12 (appendHvl H0 (bind d))) (weaken_shifthvl_TmVar (appendHvl H0 (bind d)) ins)))))).
  Lemma shift_TmVar__wfDecls (k11 : Hvl) :
    (forall (d17 : Decls) (wf : (wfDecls k11 d17)) ,
      (forall (c1 : (Cutoff TmVar)) (k12 : Hvl) ,
        (shifthvl_TmVar c1 k11 k12) -> (wfDecls k12 (shift_TmVar_Decls c1 d17)))).
  Proof.
    pose proof ((shift_TmVar__wfDecls_Kind_Ty_Tm k11)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_TmVar__wfKind (k11 : Hvl) :
    (forall (K5 : Kind) (wf0 : (wfKind k11 K5)) ,
      (forall (c2 : (Cutoff TmVar)) (k13 : Hvl) ,
        (shifthvl_TmVar c2 k11 k13) -> (wfKind k13 (shift_TmVar_Kind c2 K5)))).
  Proof.
    pose proof ((shift_TmVar__wfDecls_Kind_Ty_Tm k11)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_TmVar__wfTy (k11 : Hvl) :
    (forall (S4 : Ty) (wf1 : (wfTy k11 S4)) ,
      (forall (c3 : (Cutoff TmVar)) (k14 : Hvl) ,
        (shifthvl_TmVar c3 k11 k14) -> (wfTy k14 (shift_TmVar_Ty c3 S4)))).
  Proof.
    pose proof ((shift_TmVar__wfDecls_Kind_Ty_Tm k11)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_TmVar__wfTm (k11 : Hvl) :
    (forall (s4 : Tm) (wf2 : (wfTm k11 s4)) ,
      (forall (c4 : (Cutoff TmVar)) (k15 : Hvl) ,
        (shifthvl_TmVar c4 k11 k15) -> (wfTm k15 (shift_TmVar_Tm c4 s4)))).
  Proof.
    pose proof ((shift_TmVar__wfDecls_Kind_Ty_Tm k11)).
    destruct_conjs .
    easy .
  Qed.
  Definition shift_TyVar__wfDecls_Kind_Ty_Tm : (forall (k11 : Hvl) ,
    (forall (d17 : Decls) (wf : (wfDecls k11 d17)) ,
      (forall (c1 : (Cutoff TyVar)) (k12 : Hvl) ,
        (shifthvl_TyVar c1 k11 k12) -> (wfDecls k12 (shift_TyVar_Decls c1 d17)))) /\
    (forall (K5 : Kind) (wf : (wfKind k11 K5)) ,
      (forall (c1 : (Cutoff TyVar)) (k12 : Hvl) ,
        (shifthvl_TyVar c1 k11 k12) -> (wfKind k12 (shift_TyVar_Kind c1 K5)))) /\
    (forall (S4 : Ty) (wf : (wfTy k11 S4)) ,
      (forall (c1 : (Cutoff TyVar)) (k12 : Hvl) ,
        (shifthvl_TyVar c1 k11 k12) -> (wfTy k12 (shift_TyVar_Ty c1 S4)))) /\
    (forall (s4 : Tm) (wf : (wfTm k11 s4)) ,
      (forall (c1 : (Cutoff TyVar)) (k12 : Hvl) ,
        (shifthvl_TyVar c1 k11 k12) -> (wfTm k12 (shift_TyVar_Tm c1 s4))))) := (ind_wfDecls_Kind_Ty_Tm (fun (k11 : Hvl) (d17 : Decls) (wf : (wfDecls k11 d17)) =>
    (forall (c1 : (Cutoff TyVar)) (k12 : Hvl) ,
      (shifthvl_TyVar c1 k11 k12) -> (wfDecls k12 (shift_TyVar_Decls c1 d17)))) (fun (k11 : Hvl) (K5 : Kind) (wf : (wfKind k11 K5)) =>
    (forall (c1 : (Cutoff TyVar)) (k12 : Hvl) ,
      (shifthvl_TyVar c1 k11 k12) -> (wfKind k12 (shift_TyVar_Kind c1 K5)))) (fun (k11 : Hvl) (S4 : Ty) (wf : (wfTy k11 S4)) =>
    (forall (c1 : (Cutoff TyVar)) (k12 : Hvl) ,
      (shifthvl_TyVar c1 k11 k12) -> (wfTy k12 (shift_TyVar_Ty c1 S4)))) (fun (k11 : Hvl) (s4 : Tm) (wf : (wfTm k11 s4)) =>
    (forall (c1 : (Cutoff TyVar)) (k12 : Hvl) ,
      (shifthvl_TyVar c1 k11 k12) -> (wfTm k12 (shift_TyVar_Tm c1 s4)))) (fun (k11 : Hvl) (c1 : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c1 k11 k12)) =>
    (wfDecls_DNil k12)) (fun (k11 : Hvl) (t : Tm) (wf : (wfTm k11 t)) IHt (d : Decls) (wf0 : (wfDecls (HS TmVar k11) d)) IHd (c1 : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c1 k11 k12)) =>
    (wfDecls_DConsTm k12 (IHt c1 k12 (weaken_shifthvl_TyVar H0 ins)) (IHd c1 (HS TmVar k12) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k11 : Hvl) (K : Kind) (wf : (wfKind k11 K)) IHK (d : Decls) (wf0 : (wfDecls (HS TyVar k11) d)) IHd (c1 : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c1 k11 k12)) =>
    (wfDecls_DConsTy k12 (IHK c1 k12 (weaken_shifthvl_TyVar H0 ins)) (IHd (CS c1) (HS TyVar k12) (weaken_shifthvl_TyVar (HS TyVar H0) ins)))) (fun (k11 : Hvl) (c1 : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c1 k11 k12)) =>
    (wfKind_Star k12)) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) IHT (K : Kind) (wf0 : (wfKind (HS TmVar k11) K)) IHK (c1 : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c1 k11 k12)) =>
    (wfKind_KPi k12 (IHT c1 k12 (weaken_shifthvl_TyVar H0 ins)) (IHK c1 (HS TmVar k12) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k11 : Hvl) (X7 : (Index TyVar)) (wfi : (wfindex k11 X7)) (c1 : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c1 k11 k12)) =>
    (wfTy_TVar k12 _ (shift_TyVar__wfindex_TyVar c1 k11 k12 ins X7 wfi))) (fun (k11 : Hvl) (T1 : Ty) (wf : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS TmVar k11) T2)) IHT2 (c1 : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c1 k11 k12)) =>
    (wfTy_TPi k12 (IHT1 c1 k12 (weaken_shifthvl_TyVar H0 ins)) (IHT2 c1 (HS TmVar k12) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) IHT (t : Tm) (wf0 : (wfTm k11 t)) IHt (c1 : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c1 k11 k12)) =>
    (wfTy_TApp k12 (IHT c1 k12 (weaken_shifthvl_TyVar H0 ins)) (IHt c1 k12 (weaken_shifthvl_TyVar H0 ins)))) (fun (k11 : Hvl) (x11 : (Index TmVar)) (wfi : (wfindex k11 x11)) (c1 : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c1 k11 k12)) =>
    (wfTm_Var k12 _ (shift_TyVar__wfindex_TmVar c1 k11 k12 ins x11 wfi))) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) IHT (t : Tm) (wf0 : (wfTm (HS TmVar k11) t)) IHt (c1 : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c1 k11 k12)) =>
    (wfTm_Abs k12 (IHT c1 k12 (weaken_shifthvl_TyVar H0 ins)) (IHt c1 (HS TmVar k12) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k11 : Hvl) (t1 : Tm) (wf : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k11 t2)) IHt2 (c1 : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c1 k11 k12)) =>
    (wfTm_App k12 (IHt1 c1 k12 (weaken_shifthvl_TyVar H0 ins)) (IHt2 c1 k12 (weaken_shifthvl_TyVar H0 ins)))) (fun (k11 : Hvl) (d : Decls) (wf : (wfDecls k11 d)) IHd (t : Tm) (wf0 : (wfTm (appendHvl k11 (appendHvl H0 (bind d))) t)) IHt (c1 : (Cutoff TyVar)) (k12 : Hvl) (ins : (shifthvl_TyVar c1 k11 k12)) =>
    (wfTm_Let k12 (IHd c1 k12 (weaken_shifthvl_TyVar H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k12) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TyVar__bind _ _)))) eq_refl (IHt (weakenCutoffTyVar c1 (appendHvl H0 (bind d))) (appendHvl k12 (appendHvl H0 (bind d))) (weaken_shifthvl_TyVar (appendHvl H0 (bind d)) ins)))))).
  Lemma shift_TyVar__wfDecls (k11 : Hvl) :
    (forall (d17 : Decls) (wf : (wfDecls k11 d17)) ,
      (forall (c1 : (Cutoff TyVar)) (k12 : Hvl) ,
        (shifthvl_TyVar c1 k11 k12) -> (wfDecls k12 (shift_TyVar_Decls c1 d17)))).
  Proof.
    pose proof ((shift_TyVar__wfDecls_Kind_Ty_Tm k11)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_TyVar__wfKind (k11 : Hvl) :
    (forall (K5 : Kind) (wf0 : (wfKind k11 K5)) ,
      (forall (c2 : (Cutoff TyVar)) (k13 : Hvl) ,
        (shifthvl_TyVar c2 k11 k13) -> (wfKind k13 (shift_TyVar_Kind c2 K5)))).
  Proof.
    pose proof ((shift_TyVar__wfDecls_Kind_Ty_Tm k11)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_TyVar__wfTy (k11 : Hvl) :
    (forall (S4 : Ty) (wf1 : (wfTy k11 S4)) ,
      (forall (c3 : (Cutoff TyVar)) (k14 : Hvl) ,
        (shifthvl_TyVar c3 k11 k14) -> (wfTy k14 (shift_TyVar_Ty c3 S4)))).
  Proof.
    pose proof ((shift_TyVar__wfDecls_Kind_Ty_Tm k11)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_TyVar__wfTm (k11 : Hvl) :
    (forall (s4 : Tm) (wf2 : (wfTm k11 s4)) ,
      (forall (c4 : (Cutoff TyVar)) (k15 : Hvl) ,
        (shifthvl_TyVar c4 k11 k15) -> (wfTm k15 (shift_TyVar_Tm c4 s4)))).
  Proof.
    pose proof ((shift_TyVar__wfDecls_Kind_Ty_Tm k11)).
    destruct_conjs .
    easy .
  Qed.
  Fixpoint weaken_wfDecls (k11 : Hvl) {struct k11} :
  (forall (k12 : Hvl) (d17 : Decls) (wf : (wfDecls k12 d17)) ,
    (wfDecls (appendHvl k12 k11) (weakenDecls d17 k11))) :=
    match k11 return (forall (k12 : Hvl) (d17 : Decls) (wf : (wfDecls k12 d17)) ,
      (wfDecls (appendHvl k12 k11) (weakenDecls d17 k11))) with
      | (H0) => (fun (k12 : Hvl) (d17 : Decls) (wf : (wfDecls k12 d17)) =>
        wf)
      | (HS TmVar k11) => (fun (k12 : Hvl) (d17 : Decls) (wf : (wfDecls k12 d17)) =>
        (shift_TmVar__wfDecls (appendHvl k12 k11) (weakenDecls d17 k11) (weaken_wfDecls k11 k12 d17 wf) C0 (HS TmVar (appendHvl k12 k11)) (shifthvl_TmVar_here (appendHvl k12 k11))))
      | (HS TyVar k11) => (fun (k12 : Hvl) (d17 : Decls) (wf : (wfDecls k12 d17)) =>
        (shift_TyVar__wfDecls (appendHvl k12 k11) (weakenDecls d17 k11) (weaken_wfDecls k11 k12 d17 wf) C0 (HS TyVar (appendHvl k12 k11)) (shifthvl_TyVar_here (appendHvl k12 k11))))
    end.
  Fixpoint weaken_wfKind (k11 : Hvl) {struct k11} :
  (forall (k12 : Hvl) (K5 : Kind) (wf : (wfKind k12 K5)) ,
    (wfKind (appendHvl k12 k11) (weakenKind K5 k11))) :=
    match k11 return (forall (k12 : Hvl) (K5 : Kind) (wf : (wfKind k12 K5)) ,
      (wfKind (appendHvl k12 k11) (weakenKind K5 k11))) with
      | (H0) => (fun (k12 : Hvl) (K5 : Kind) (wf : (wfKind k12 K5)) =>
        wf)
      | (HS TmVar k11) => (fun (k12 : Hvl) (K5 : Kind) (wf : (wfKind k12 K5)) =>
        (shift_TmVar__wfKind (appendHvl k12 k11) (weakenKind K5 k11) (weaken_wfKind k11 k12 K5 wf) C0 (HS TmVar (appendHvl k12 k11)) (shifthvl_TmVar_here (appendHvl k12 k11))))
      | (HS TyVar k11) => (fun (k12 : Hvl) (K5 : Kind) (wf : (wfKind k12 K5)) =>
        (shift_TyVar__wfKind (appendHvl k12 k11) (weakenKind K5 k11) (weaken_wfKind k11 k12 K5 wf) C0 (HS TyVar (appendHvl k12 k11)) (shifthvl_TyVar_here (appendHvl k12 k11))))
    end.
  Fixpoint weaken_wfTy (k11 : Hvl) {struct k11} :
  (forall (k12 : Hvl) (S4 : Ty) (wf : (wfTy k12 S4)) ,
    (wfTy (appendHvl k12 k11) (weakenTy S4 k11))) :=
    match k11 return (forall (k12 : Hvl) (S4 : Ty) (wf : (wfTy k12 S4)) ,
      (wfTy (appendHvl k12 k11) (weakenTy S4 k11))) with
      | (H0) => (fun (k12 : Hvl) (S4 : Ty) (wf : (wfTy k12 S4)) =>
        wf)
      | (HS TmVar k11) => (fun (k12 : Hvl) (S4 : Ty) (wf : (wfTy k12 S4)) =>
        (shift_TmVar__wfTy (appendHvl k12 k11) (weakenTy S4 k11) (weaken_wfTy k11 k12 S4 wf) C0 (HS TmVar (appendHvl k12 k11)) (shifthvl_TmVar_here (appendHvl k12 k11))))
      | (HS TyVar k11) => (fun (k12 : Hvl) (S4 : Ty) (wf : (wfTy k12 S4)) =>
        (shift_TyVar__wfTy (appendHvl k12 k11) (weakenTy S4 k11) (weaken_wfTy k11 k12 S4 wf) C0 (HS TyVar (appendHvl k12 k11)) (shifthvl_TyVar_here (appendHvl k12 k11))))
    end.
  Fixpoint weaken_wfTm (k11 : Hvl) {struct k11} :
  (forall (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) ,
    (wfTm (appendHvl k12 k11) (weakenTm s4 k11))) :=
    match k11 return (forall (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) ,
      (wfTm (appendHvl k12 k11) (weakenTm s4 k11))) with
      | (H0) => (fun (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) =>
        wf)
      | (HS TmVar k11) => (fun (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) =>
        (shift_TmVar__wfTm (appendHvl k12 k11) (weakenTm s4 k11) (weaken_wfTm k11 k12 s4 wf) C0 (HS TmVar (appendHvl k12 k11)) (shifthvl_TmVar_here (appendHvl k12 k11))))
      | (HS TyVar k11) => (fun (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) =>
        (shift_TyVar__wfTm (appendHvl k12 k11) (weakenTm s4 k11) (weaken_wfTm k11 k12 s4 wf) C0 (HS TyVar (appendHvl k12 k11)) (shifthvl_TyVar_here (appendHvl k12 k11))))
    end.
End ShiftWellFormed.
Lemma wfDecls_cast  :
  (forall (k11 : Hvl) (d17 : Decls) (k12 : Hvl) (d18 : Decls) ,
    (k11 = k12) -> (d17 = d18) -> (wfDecls k11 d17) -> (wfDecls k12 d18)).
Proof.
  congruence .
Qed.
Lemma wfKind_cast  :
  (forall (k11 : Hvl) (K5 : Kind) (k12 : Hvl) (K6 : Kind) ,
    (k11 = k12) -> (K5 = K6) -> (wfKind k11 K5) -> (wfKind k12 K6)).
Proof.
  congruence .
Qed.
Lemma wfTy_cast  :
  (forall (k11 : Hvl) (S4 : Ty) (k12 : Hvl) (S5 : Ty) ,
    (k11 = k12) -> (S4 = S5) -> (wfTy k11 S4) -> (wfTy k12 S5)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k11 : Hvl) (s4 : Tm) (k12 : Hvl) (s5 : Tm) ,
    (k11 = k12) -> (s4 = s5) -> (wfTm k11 s4) -> (wfTm k12 s5)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TyVar : infra.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TyVar : shift.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TyVar : shift_wf.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TyVar : wf.
 Hint Resolve shift_TmVar__wfDecls shift_TmVar__wfKind shift_TmVar__wfTm shift_TmVar__wfTy shift_TyVar__wfDecls shift_TyVar__wfKind shift_TyVar__wfTm shift_TyVar__wfTy : infra.
 Hint Resolve shift_TmVar__wfDecls shift_TmVar__wfKind shift_TmVar__wfTm shift_TmVar__wfTy shift_TyVar__wfDecls shift_TyVar__wfKind shift_TyVar__wfTm shift_TyVar__wfTy : shift.
 Hint Resolve shift_TmVar__wfDecls shift_TmVar__wfKind shift_TmVar__wfTm shift_TmVar__wfTy shift_TyVar__wfDecls shift_TyVar__wfKind shift_TyVar__wfTm shift_TyVar__wfTy : shift_wf.
 Hint Resolve shift_TmVar__wfDecls shift_TmVar__wfKind shift_TmVar__wfTm shift_TmVar__wfTy shift_TyVar__wfDecls shift_TyVar__wfKind shift_TyVar__wfTm shift_TyVar__wfTy : wf.
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
  Inductive substhvl_TmVar (k11 : Hvl) : (forall (d17 : (Trace TmVar)) (k12 : Hvl) (k13 : Hvl) ,
    Prop) :=
    | substhvl_TmVar_here :
        (substhvl_TmVar k11 X0 (HS TmVar k11) k11)
    | substhvl_TmVar_there_TmVar
        {d17 : (Trace TmVar)}
        {k12 : Hvl} {k13 : Hvl} :
        (substhvl_TmVar k11 d17 k12 k13) -> (substhvl_TmVar k11 (XS TmVar d17) (HS TmVar k12) (HS TmVar k13))
    | substhvl_TmVar_there_TyVar
        {d17 : (Trace TmVar)}
        {k12 : Hvl} {k13 : Hvl} :
        (substhvl_TmVar k11 d17 k12 k13) -> (substhvl_TmVar k11 (XS TyVar d17) (HS TyVar k12) (HS TyVar k13)).
  Inductive substhvl_TyVar (k11 : Hvl) : (forall (d17 : (Trace TyVar)) (k12 : Hvl) (k13 : Hvl) ,
    Prop) :=
    | substhvl_TyVar_here :
        (substhvl_TyVar k11 X0 (HS TyVar k11) k11)
    | substhvl_TyVar_there_TmVar
        {d17 : (Trace TyVar)}
        {k12 : Hvl} {k13 : Hvl} :
        (substhvl_TyVar k11 d17 k12 k13) -> (substhvl_TyVar k11 (XS TmVar d17) (HS TmVar k12) (HS TmVar k13))
    | substhvl_TyVar_there_TyVar
        {d17 : (Trace TyVar)}
        {k12 : Hvl} {k13 : Hvl} :
        (substhvl_TyVar k11 d17 k12 k13) -> (substhvl_TyVar k11 (XS TyVar d17) (HS TyVar k12) (HS TyVar k13)).
  Lemma weaken_substhvl_TmVar  :
    (forall {k12 : Hvl} (k11 : Hvl) {d17 : (Trace TmVar)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_TmVar k12 d17 k13 k14) -> (substhvl_TmVar k12 (weakenTrace d17 k11) (appendHvl k13 k11) (appendHvl k14 k11))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_TyVar  :
    (forall {k12 : Hvl} (k11 : Hvl) {d17 : (Trace TyVar)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_TyVar k12 d17 k13 k14) -> (substhvl_TyVar k12 (weakenTrace d17 k11) (appendHvl k13 k11) (appendHvl k14 k11))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_TmVar_wfindex_TmVar {k11 : Hvl} {s4 : Tm} (wft : (wfTm k11 s4)) :
    (forall {d17 : (Trace TmVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TmVar k11 d17 k12 k13) -> (forall {x11 : (Index TmVar)} ,
        (wfindex k12 x11) -> (wfTm k13 (subst_TmVar_Index d17 s4 x11)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TyVar_wfindex_TyVar {k11 : Hvl} {S4 : Ty} (wft : (wfTy k11 S4)) :
    (forall {d17 : (Trace TyVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TyVar k11 d17 k12 k13) -> (forall {X7 : (Index TyVar)} ,
        (wfindex k12 X7) -> (wfTy k13 (subst_TyVar_Index d17 S4 X7)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TmVar_wfindex_TyVar {k11 : Hvl} :
    (forall {d17 : (Trace TmVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TmVar k11 d17 k12 k13) -> (forall {X7 : (Index TyVar)} ,
        (wfindex k12 X7) -> (wfindex k13 X7))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_TyVar_wfindex_TmVar {k11 : Hvl} :
    (forall {d17 : (Trace TyVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TyVar k11 d17 k12 k13) -> (forall {x11 : (Index TmVar)} ,
        (wfindex k12 x11) -> (wfindex k13 x11))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_TmVar_wfDecls_Kind_Ty_Tm {k11 : Hvl} {s4 : Tm} (wf : (wfTm k11 s4)) : (forall (k12 : Hvl) ,
    (forall (d17 : Decls) (wf0 : (wfDecls k12 d17)) ,
      (forall {d18 : (Trace TmVar)} {k13 : Hvl} ,
        (substhvl_TmVar k11 d18 k12 k13) -> (wfDecls k13 (subst_TmVar_Decls d18 s4 d17)))) /\
    (forall (K5 : Kind) (wf0 : (wfKind k12 K5)) ,
      (forall {d17 : (Trace TmVar)} {k13 : Hvl} ,
        (substhvl_TmVar k11 d17 k12 k13) -> (wfKind k13 (subst_TmVar_Kind d17 s4 K5)))) /\
    (forall (S4 : Ty) (wf0 : (wfTy k12 S4)) ,
      (forall {d17 : (Trace TmVar)} {k13 : Hvl} ,
        (substhvl_TmVar k11 d17 k12 k13) -> (wfTy k13 (subst_TmVar_Ty d17 s4 S4)))) /\
    (forall (s5 : Tm) (wf0 : (wfTm k12 s5)) ,
      (forall {d17 : (Trace TmVar)} {k13 : Hvl} ,
        (substhvl_TmVar k11 d17 k12 k13) -> (wfTm k13 (subst_TmVar_Tm d17 s4 s5))))) := (ind_wfDecls_Kind_Ty_Tm (fun (k12 : Hvl) (d17 : Decls) (wf0 : (wfDecls k12 d17)) =>
    (forall {d18 : (Trace TmVar)} {k13 : Hvl} ,
      (substhvl_TmVar k11 d18 k12 k13) -> (wfDecls k13 (subst_TmVar_Decls d18 s4 d17)))) (fun (k12 : Hvl) (K5 : Kind) (wf0 : (wfKind k12 K5)) =>
    (forall {d17 : (Trace TmVar)} {k13 : Hvl} ,
      (substhvl_TmVar k11 d17 k12 k13) -> (wfKind k13 (subst_TmVar_Kind d17 s4 K5)))) (fun (k12 : Hvl) (S4 : Ty) (wf0 : (wfTy k12 S4)) =>
    (forall {d17 : (Trace TmVar)} {k13 : Hvl} ,
      (substhvl_TmVar k11 d17 k12 k13) -> (wfTy k13 (subst_TmVar_Ty d17 s4 S4)))) (fun (k12 : Hvl) (s5 : Tm) (wf0 : (wfTm k12 s5)) =>
    (forall {d17 : (Trace TmVar)} {k13 : Hvl} ,
      (substhvl_TmVar k11 d17 k12 k13) -> (wfTm k13 (subst_TmVar_Tm d17 s4 s5)))) (fun (k12 : Hvl) {d17 : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d17 k12 k13)) =>
    (wfDecls_DNil k13)) (fun (k12 : Hvl) (t : Tm) (wf0 : (wfTm k12 t)) IHt (d : Decls) (wf1 : (wfDecls (HS TmVar k12) d)) IHd {d17 : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d17 k12 k13)) =>
    (wfDecls_DConsTm k13 (IHt (weakenTrace d17 H0) k13 (weaken_substhvl_TmVar H0 del)) (IHd (weakenTrace d17 (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k12 : Hvl) (K : Kind) (wf0 : (wfKind k12 K)) IHK (d : Decls) (wf1 : (wfDecls (HS TyVar k12) d)) IHd {d17 : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d17 k12 k13)) =>
    (wfDecls_DConsTy k13 (IHK (weakenTrace d17 H0) k13 (weaken_substhvl_TmVar H0 del)) (IHd (weakenTrace d17 (HS TyVar H0)) (HS TyVar k13) (weaken_substhvl_TmVar (HS TyVar H0) del)))) (fun (k12 : Hvl) {d17 : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d17 k12 k13)) =>
    (wfKind_Star k13)) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) IHT (K : Kind) (wf1 : (wfKind (HS TmVar k12) K)) IHK {d17 : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d17 k12 k13)) =>
    (wfKind_KPi k13 (IHT (weakenTrace d17 H0) k13 (weaken_substhvl_TmVar H0 del)) (IHK (weakenTrace d17 (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k12 : Hvl) {X7 : (Index TyVar)} (wfi : (wfindex k12 X7)) {d17 : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d17 k12 k13)) =>
    (wfTy_TVar k13 _ (substhvl_TmVar_wfindex_TyVar del wfi))) (fun (k12 : Hvl) (T1 : Ty) (wf0 : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS TmVar k12) T2)) IHT2 {d17 : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d17 k12 k13)) =>
    (wfTy_TPi k13 (IHT1 (weakenTrace d17 H0) k13 (weaken_substhvl_TmVar H0 del)) (IHT2 (weakenTrace d17 (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) IHT (t : Tm) (wf1 : (wfTm k12 t)) IHt {d17 : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d17 k12 k13)) =>
    (wfTy_TApp k13 (IHT (weakenTrace d17 H0) k13 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d17 H0) k13 (weaken_substhvl_TmVar H0 del)))) (fun (k12 : Hvl) {x11 : (Index TmVar)} (wfi : (wfindex k12 x11)) {d17 : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d17 k12 k13)) =>
    (substhvl_TmVar_wfindex_TmVar wf del wfi)) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) IHT (t : Tm) (wf1 : (wfTm (HS TmVar k12) t)) IHt {d17 : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d17 k12 k13)) =>
    (wfTm_Abs k13 (IHT (weakenTrace d17 H0) k13 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d17 (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k12 : Hvl) (t1 : Tm) (wf0 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k12 t2)) IHt2 {d17 : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d17 k12 k13)) =>
    (wfTm_App k13 (IHt1 (weakenTrace d17 H0) k13 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d17 H0) k13 (weaken_substhvl_TmVar H0 del)))) (fun (k12 : Hvl) (d : Decls) (wf0 : (wfDecls k12 d)) IHd (t : Tm) (wf1 : (wfTm (appendHvl k12 (appendHvl H0 (bind d))) t)) IHt {d17 : (Trace TmVar)} {k13 : Hvl} (del : (substhvl_TmVar k11 d17 k12 k13)) =>
    (wfTm_Let k13 (IHd (weakenTrace d17 H0) k13 (weaken_substhvl_TmVar H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k13) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0)))) eq_refl (IHt (weakenTrace d17 (appendHvl H0 (bind d))) (appendHvl k13 (appendHvl H0 (bind d))) (weaken_substhvl_TmVar (appendHvl H0 (bind d)) del)))))).
  Lemma substhvl_TmVar_wfDecls {k11 : Hvl} {s4 : Tm} (wf : (wfTm k11 s4)) (k12 : Hvl) (d17 : Decls) (wf0 : (wfDecls k12 d17)) :
    (forall {d18 : (Trace TmVar)} {k13 : Hvl} ,
      (substhvl_TmVar k11 d18 k12 k13) -> (wfDecls k13 (subst_TmVar_Decls d18 s4 d17))).
  Proof.
    apply ((substhvl_TmVar_wfDecls_Kind_Ty_Tm wf k12)).
    auto .
  Qed.
  Lemma substhvl_TmVar_wfKind {k11 : Hvl} {s4 : Tm} (wf : (wfTm k11 s4)) (k12 : Hvl) (K5 : Kind) (wf1 : (wfKind k12 K5)) :
    (forall {d19 : (Trace TmVar)} {k14 : Hvl} ,
      (substhvl_TmVar k11 d19 k12 k14) -> (wfKind k14 (subst_TmVar_Kind d19 s4 K5))).
  Proof.
    apply ((substhvl_TmVar_wfDecls_Kind_Ty_Tm wf k12)).
    auto .
  Qed.
  Lemma substhvl_TmVar_wfTy {k11 : Hvl} {s4 : Tm} (wf : (wfTm k11 s4)) (k12 : Hvl) (S4 : Ty) (wf2 : (wfTy k12 S4)) :
    (forall {d20 : (Trace TmVar)} {k15 : Hvl} ,
      (substhvl_TmVar k11 d20 k12 k15) -> (wfTy k15 (subst_TmVar_Ty d20 s4 S4))).
  Proof.
    apply ((substhvl_TmVar_wfDecls_Kind_Ty_Tm wf k12)).
    auto .
  Qed.
  Lemma substhvl_TmVar_wfTm {k11 : Hvl} {s4 : Tm} (wf : (wfTm k11 s4)) (k12 : Hvl) (s5 : Tm) (wf3 : (wfTm k12 s5)) :
    (forall {d21 : (Trace TmVar)} {k16 : Hvl} ,
      (substhvl_TmVar k11 d21 k12 k16) -> (wfTm k16 (subst_TmVar_Tm d21 s4 s5))).
  Proof.
    apply ((substhvl_TmVar_wfDecls_Kind_Ty_Tm wf k12)).
    auto .
  Qed.
  Definition substhvl_TyVar_wfDecls_Kind_Ty_Tm {k11 : Hvl} {S4 : Ty} (wf : (wfTy k11 S4)) : (forall (k12 : Hvl) ,
    (forall (d17 : Decls) (wf0 : (wfDecls k12 d17)) ,
      (forall {d18 : (Trace TyVar)} {k13 : Hvl} ,
        (substhvl_TyVar k11 d18 k12 k13) -> (wfDecls k13 (subst_TyVar_Decls d18 S4 d17)))) /\
    (forall (K5 : Kind) (wf0 : (wfKind k12 K5)) ,
      (forall {d17 : (Trace TyVar)} {k13 : Hvl} ,
        (substhvl_TyVar k11 d17 k12 k13) -> (wfKind k13 (subst_TyVar_Kind d17 S4 K5)))) /\
    (forall (S5 : Ty) (wf0 : (wfTy k12 S5)) ,
      (forall {d17 : (Trace TyVar)} {k13 : Hvl} ,
        (substhvl_TyVar k11 d17 k12 k13) -> (wfTy k13 (subst_TyVar_Ty d17 S4 S5)))) /\
    (forall (s4 : Tm) (wf0 : (wfTm k12 s4)) ,
      (forall {d17 : (Trace TyVar)} {k13 : Hvl} ,
        (substhvl_TyVar k11 d17 k12 k13) -> (wfTm k13 (subst_TyVar_Tm d17 S4 s4))))) := (ind_wfDecls_Kind_Ty_Tm (fun (k12 : Hvl) (d17 : Decls) (wf0 : (wfDecls k12 d17)) =>
    (forall {d18 : (Trace TyVar)} {k13 : Hvl} ,
      (substhvl_TyVar k11 d18 k12 k13) -> (wfDecls k13 (subst_TyVar_Decls d18 S4 d17)))) (fun (k12 : Hvl) (K5 : Kind) (wf0 : (wfKind k12 K5)) =>
    (forall {d17 : (Trace TyVar)} {k13 : Hvl} ,
      (substhvl_TyVar k11 d17 k12 k13) -> (wfKind k13 (subst_TyVar_Kind d17 S4 K5)))) (fun (k12 : Hvl) (S5 : Ty) (wf0 : (wfTy k12 S5)) =>
    (forall {d17 : (Trace TyVar)} {k13 : Hvl} ,
      (substhvl_TyVar k11 d17 k12 k13) -> (wfTy k13 (subst_TyVar_Ty d17 S4 S5)))) (fun (k12 : Hvl) (s4 : Tm) (wf0 : (wfTm k12 s4)) =>
    (forall {d17 : (Trace TyVar)} {k13 : Hvl} ,
      (substhvl_TyVar k11 d17 k12 k13) -> (wfTm k13 (subst_TyVar_Tm d17 S4 s4)))) (fun (k12 : Hvl) {d17 : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d17 k12 k13)) =>
    (wfDecls_DNil k13)) (fun (k12 : Hvl) (t : Tm) (wf0 : (wfTm k12 t)) IHt (d : Decls) (wf1 : (wfDecls (HS TmVar k12) d)) IHd {d17 : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d17 k12 k13)) =>
    (wfDecls_DConsTm k13 (IHt (weakenTrace d17 H0) k13 (weaken_substhvl_TyVar H0 del)) (IHd (weakenTrace d17 (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k12 : Hvl) (K : Kind) (wf0 : (wfKind k12 K)) IHK (d : Decls) (wf1 : (wfDecls (HS TyVar k12) d)) IHd {d17 : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d17 k12 k13)) =>
    (wfDecls_DConsTy k13 (IHK (weakenTrace d17 H0) k13 (weaken_substhvl_TyVar H0 del)) (IHd (weakenTrace d17 (HS TyVar H0)) (HS TyVar k13) (weaken_substhvl_TyVar (HS TyVar H0) del)))) (fun (k12 : Hvl) {d17 : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d17 k12 k13)) =>
    (wfKind_Star k13)) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) IHT (K : Kind) (wf1 : (wfKind (HS TmVar k12) K)) IHK {d17 : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d17 k12 k13)) =>
    (wfKind_KPi k13 (IHT (weakenTrace d17 H0) k13 (weaken_substhvl_TyVar H0 del)) (IHK (weakenTrace d17 (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k12 : Hvl) {X7 : (Index TyVar)} (wfi : (wfindex k12 X7)) {d17 : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d17 k12 k13)) =>
    (substhvl_TyVar_wfindex_TyVar wf del wfi)) (fun (k12 : Hvl) (T1 : Ty) (wf0 : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS TmVar k12) T2)) IHT2 {d17 : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d17 k12 k13)) =>
    (wfTy_TPi k13 (IHT1 (weakenTrace d17 H0) k13 (weaken_substhvl_TyVar H0 del)) (IHT2 (weakenTrace d17 (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) IHT (t : Tm) (wf1 : (wfTm k12 t)) IHt {d17 : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d17 k12 k13)) =>
    (wfTy_TApp k13 (IHT (weakenTrace d17 H0) k13 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d17 H0) k13 (weaken_substhvl_TyVar H0 del)))) (fun (k12 : Hvl) {x11 : (Index TmVar)} (wfi : (wfindex k12 x11)) {d17 : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d17 k12 k13)) =>
    (wfTm_Var k13 _ (substhvl_TyVar_wfindex_TmVar del wfi))) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) IHT (t : Tm) (wf1 : (wfTm (HS TmVar k12) t)) IHt {d17 : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d17 k12 k13)) =>
    (wfTm_Abs k13 (IHT (weakenTrace d17 H0) k13 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d17 (HS TmVar H0)) (HS TmVar k13) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k12 : Hvl) (t1 : Tm) (wf0 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k12 t2)) IHt2 {d17 : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d17 k12 k13)) =>
    (wfTm_App k13 (IHt1 (weakenTrace d17 H0) k13 (weaken_substhvl_TyVar H0 del)) (IHt2 (weakenTrace d17 H0) k13 (weaken_substhvl_TyVar H0 del)))) (fun (k12 : Hvl) (d : Decls) (wf0 : (wfDecls k12 d)) IHd (t : Tm) (wf1 : (wfTm (appendHvl k12 (appendHvl H0 (bind d))) t)) IHt {d17 : (Trace TyVar)} {k13 : Hvl} (del : (substhvl_TyVar k11 d17 k12 k13)) =>
    (wfTm_Let k13 (IHd (weakenTrace d17 H0) k13 (weaken_substhvl_TyVar H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k13) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TyVar__bind _ _ _)) (eq_refl H0)))) eq_refl (IHt (weakenTrace d17 (appendHvl H0 (bind d))) (appendHvl k13 (appendHvl H0 (bind d))) (weaken_substhvl_TyVar (appendHvl H0 (bind d)) del)))))).
  Lemma substhvl_TyVar_wfDecls {k11 : Hvl} {S4 : Ty} (wf : (wfTy k11 S4)) (k12 : Hvl) (d17 : Decls) (wf0 : (wfDecls k12 d17)) :
    (forall {d18 : (Trace TyVar)} {k13 : Hvl} ,
      (substhvl_TyVar k11 d18 k12 k13) -> (wfDecls k13 (subst_TyVar_Decls d18 S4 d17))).
  Proof.
    apply ((substhvl_TyVar_wfDecls_Kind_Ty_Tm wf k12)).
    auto .
  Qed.
  Lemma substhvl_TyVar_wfKind {k11 : Hvl} {S4 : Ty} (wf : (wfTy k11 S4)) (k12 : Hvl) (K5 : Kind) (wf1 : (wfKind k12 K5)) :
    (forall {d19 : (Trace TyVar)} {k14 : Hvl} ,
      (substhvl_TyVar k11 d19 k12 k14) -> (wfKind k14 (subst_TyVar_Kind d19 S4 K5))).
  Proof.
    apply ((substhvl_TyVar_wfDecls_Kind_Ty_Tm wf k12)).
    auto .
  Qed.
  Lemma substhvl_TyVar_wfTy {k11 : Hvl} {S4 : Ty} (wf : (wfTy k11 S4)) (k12 : Hvl) (S5 : Ty) (wf2 : (wfTy k12 S5)) :
    (forall {d20 : (Trace TyVar)} {k15 : Hvl} ,
      (substhvl_TyVar k11 d20 k12 k15) -> (wfTy k15 (subst_TyVar_Ty d20 S4 S5))).
  Proof.
    apply ((substhvl_TyVar_wfDecls_Kind_Ty_Tm wf k12)).
    auto .
  Qed.
  Lemma substhvl_TyVar_wfTm {k11 : Hvl} {S4 : Ty} (wf : (wfTy k11 S4)) (k12 : Hvl) (s4 : Tm) (wf3 : (wfTm k12 s4)) :
    (forall {d21 : (Trace TyVar)} {k16 : Hvl} ,
      (substhvl_TyVar k11 d21 k12 k16) -> (wfTm k16 (subst_TyVar_Tm d21 S4 s4))).
  Proof.
    apply ((substhvl_TyVar_wfDecls_Kind_Ty_Tm wf k12)).
    auto .
  Qed.
End SubstWellFormed.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : infra.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : subst.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : subst_wf.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : wf.
 Hint Resolve substhvl_TmVar_wfDecls substhvl_TmVar_wfKind substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfDecls substhvl_TyVar_wfKind substhvl_TyVar_wfTm substhvl_TyVar_wfTy : infra.
 Hint Resolve substhvl_TmVar_wfDecls substhvl_TmVar_wfKind substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfDecls substhvl_TyVar_wfKind substhvl_TyVar_wfTm substhvl_TyVar_wfTy : subst.
 Hint Resolve substhvl_TmVar_wfDecls substhvl_TmVar_wfKind substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfDecls substhvl_TyVar_wfKind substhvl_TyVar_wfTm substhvl_TyVar_wfTy : subst_wf.
 Hint Resolve substhvl_TmVar_wfDecls substhvl_TmVar_wfKind substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfDecls substhvl_TyVar_wfKind substhvl_TyVar_wfTm substhvl_TyVar_wfTy : wf.
 Hint Constructors substhvl_TmVar substhvl_TyVar : infra.
 Hint Constructors substhvl_TmVar substhvl_TyVar : subst.
 Hint Constructors substhvl_TmVar substhvl_TyVar : subst_wf.
 Hint Constructors substhvl_TmVar substhvl_TyVar : wf.
Fixpoint subhvl_TmVar_TyVar (k11 : Hvl) {struct k11} :
Prop :=
  match k11 with
    | (H0) => True
    | (HS a k11) => match a with
      | (TmVar) => (subhvl_TmVar_TyVar k11)
      | (TyVar) => (subhvl_TmVar_TyVar k11)
    end
  end.
Lemma subhvl_TmVar_TyVar_append  :
  (forall (k11 : Hvl) (k12 : Hvl) ,
    (subhvl_TmVar_TyVar k11) -> (subhvl_TmVar_TyVar k12) -> (subhvl_TmVar_TyVar (appendHvl k11 k12))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_TmVar_TyVar_append : infra.
 Hint Resolve subhvl_TmVar_TyVar_append : wf.
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
  Fixpoint shift_TmVar_Ctx (c1 : (Cutoff TmVar)) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shift_TmVar_Ctx c1 G0) (shift_TmVar_Ty (weakenCutoffTmVar c1 (domainCtx G0)) T))
      | (etvar G0 K) => (etvar (shift_TmVar_Ctx c1 G0) (shift_TmVar_Kind (weakenCutoffTmVar c1 (domainCtx G0)) K))
    end.
  Fixpoint shift_TyVar_Ctx (c1 : (Cutoff TyVar)) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shift_TyVar_Ctx c1 G0) (shift_TyVar_Ty (weakenCutoffTyVar c1 (domainCtx G0)) T))
      | (etvar G0 K) => (etvar (shift_TyVar_Ctx c1 G0) (shift_TyVar_Kind (weakenCutoffTyVar c1 (domainCtx G0)) K))
    end.
  Fixpoint weakenCtx (G : Ctx) (k11 : Hvl) {struct k11} :
  Ctx :=
    match k11 with
      | (H0) => G
      | (HS TmVar k11) => (shift_TmVar_Ctx C0 (weakenCtx G k11))
      | (HS TyVar k11) => (shift_TyVar_Ctx C0 (weakenCtx G k11))
    end.
  Fixpoint subst_TmVar_Ctx (d17 : (Trace TmVar)) (s4 : Tm) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (subst_TmVar_Ctx d17 s4 G0) (subst_TmVar_Ty (weakenTrace d17 (domainCtx G0)) s4 T))
      | (etvar G0 K) => (etvar (subst_TmVar_Ctx d17 s4 G0) (subst_TmVar_Kind (weakenTrace d17 (domainCtx G0)) s4 K))
    end.
  Fixpoint subst_TyVar_Ctx (d17 : (Trace TyVar)) (S4 : Ty) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (subst_TyVar_Ctx d17 S4 G0) (subst_TyVar_Ty (weakenTrace d17 (domainCtx G0)) S4 T))
      | (etvar G0 K) => (etvar (subst_TyVar_Ctx d17 S4 G0) (subst_TyVar_Kind (weakenTrace d17 (domainCtx G0)) S4 K))
    end.
  Lemma domainCtx_shift_TmVar_Ctx  :
    (forall (c1 : (Cutoff TmVar)) (G : Ctx) ,
      ((domainCtx (shift_TmVar_Ctx c1 G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainCtx_shift_TyVar_Ctx  :
    (forall (c1 : (Cutoff TyVar)) (G : Ctx) ,
      ((domainCtx (shift_TyVar_Ctx c1 G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainCtx_subst_TmVar_Ctx  :
    (forall (d17 : (Trace TmVar)) (s4 : Tm) (G : Ctx) ,
      ((domainCtx (subst_TmVar_Ctx d17 s4 G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainCtx_subst_TyVar_Ctx  :
    (forall (d17 : (Trace TyVar)) (S4 : Ty) (G : Ctx) ,
      ((domainCtx (subst_TyVar_Ctx d17 S4 G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainCtx_appendCtx : interaction.
 Hint Rewrite domainCtx_appendCtx : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shift_TmVar_Ctx_appendCtx  :
      (forall (c1 : (Cutoff TmVar)) (G : Ctx) (G0 : Ctx) ,
        ((shift_TmVar_Ctx c1 (appendCtx G G0)) = (appendCtx (shift_TmVar_Ctx c1 G) (shift_TmVar_Ctx (weakenCutoffTmVar c1 (domainCtx G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma shift_TyVar_Ctx_appendCtx  :
      (forall (c1 : (Cutoff TyVar)) (G : Ctx) (G0 : Ctx) ,
        ((shift_TyVar_Ctx c1 (appendCtx G G0)) = (appendCtx (shift_TyVar_Ctx c1 G) (shift_TyVar_Ctx (weakenCutoffTyVar c1 (domainCtx G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma subst_TmVar_Ctx_appendCtx  :
      (forall (d17 : (Trace TmVar)) (s4 : Tm) (G : Ctx) (G0 : Ctx) ,
        ((subst_TmVar_Ctx d17 s4 (appendCtx G G0)) = (appendCtx (subst_TmVar_Ctx d17 s4 G) (subst_TmVar_Ctx (weakenTrace d17 (domainCtx G)) s4 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma subst_TyVar_Ctx_appendCtx  :
      (forall (d17 : (Trace TyVar)) (S4 : Ty) (G : Ctx) (G0 : Ctx) ,
        ((subst_TyVar_Ctx d17 S4 (appendCtx G G0)) = (appendCtx (subst_TyVar_Ctx d17 S4 G) (subst_TyVar_Ctx (weakenTrace d17 (domainCtx G)) S4 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenDecls_append  :
    (forall (d17 : Decls) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenDecls (weakenDecls d17 k11) k12) = (weakenDecls d17 (appendHvl k11 k12)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenKind_append  :
    (forall (K5 : Kind) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenKind (weakenKind K5 k11) k12) = (weakenKind K5 (appendHvl k11 k12)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTy_append  :
    (forall (S4 : Ty) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenTy (weakenTy S4 k11) k12) = (weakenTy S4 (appendHvl k11 k12)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s4 : Tm) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenTm (weakenTm s4 k11) k12) = (weakenTm s4 (appendHvl k11 k12)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Ctx -> (Index TmVar) -> Ty -> Prop :=
      | lookup_evar_here {G : Ctx}
          (T5 : Ty) :
          (wfTy (domainCtx G) T5) -> (lookup_evar (evar G T5) I0 (shift_TmVar_Ty C0 T5))
      | lookup_evar_there_evar
          {G : Ctx} {x11 : (Index TmVar)}
          (T6 : Ty) (T7 : Ty) :
          (lookup_evar G x11 T6) -> (lookup_evar (evar G T7) (IS x11) (shift_TmVar_Ty C0 T6))
      | lookup_evar_there_etvar
          {G : Ctx} {x11 : (Index TmVar)}
          (T6 : Ty) (K5 : Kind) :
          (lookup_evar G x11 T6) -> (lookup_evar (etvar G K5) x11 (shift_TyVar_Ty C0 T6)).
    Inductive lookup_etvar : Ctx -> (Index TyVar) -> Kind -> Prop :=
      | lookup_etvar_here {G : Ctx}
          (K5 : Kind) :
          (wfKind (domainCtx G) K5) -> (lookup_etvar (etvar G K5) I0 (shift_TyVar_Kind C0 K5))
      | lookup_etvar_there_evar
          {G : Ctx} {X7 : (Index TyVar)}
          (K6 : Kind) (T6 : Ty) :
          (lookup_etvar G X7 K6) -> (lookup_etvar (evar G T6) X7 (shift_TmVar_Kind C0 K6))
      | lookup_etvar_there_etvar
          {G : Ctx} {X7 : (Index TyVar)}
          (K6 : Kind) (K7 : Kind) :
          (lookup_etvar G X7 K6) -> (lookup_etvar (etvar G K7) (IS X7) (shift_TyVar_Kind C0 K6)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Ctx) (T6 : Ty) (T7 : Ty) ,
        (lookup_evar (evar G T6) I0 T7) -> ((shift_TmVar_Ty C0 T6) = T7)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Ctx) (K6 : Kind) (K7 : Kind) ,
        (lookup_etvar (etvar G K6) I0 K7) -> ((shift_TyVar_Kind C0 K6) = K7)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Ctx} {x11 : (Index TmVar)} ,
        (forall (T6 : Ty) ,
          (lookup_evar G x11 T6) -> (forall (T7 : Ty) ,
            (lookup_evar G x11 T7) -> (T6 = T7)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G : Ctx} {X7 : (Index TyVar)} ,
        (forall (K6 : Kind) ,
          (lookup_etvar G X7 K6) -> (forall (K7 : Kind) ,
            (lookup_etvar G X7 K7) -> (K6 = K7)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Ctx} {x11 : (Index TmVar)} (T6 : Ty) ,
        (lookup_evar G x11 T6) -> (wfTy (domainCtx G) T6)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G : Ctx} {X7 : (Index TyVar)} (K6 : Kind) ,
        (lookup_etvar G X7 K6) -> (wfKind (domainCtx G) K6)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Ctx} (G0 : Ctx) {x11 : (Index TmVar)} (T6 : Ty) ,
        (lookup_evar G x11 T6) -> (lookup_evar (appendCtx G G0) (weakenIndexTmVar x11 (domainCtx G0)) (weakenTy T6 (domainCtx G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Ctx} (G0 : Ctx) {X7 : (Index TyVar)} (K6 : Kind) ,
        (lookup_etvar G X7 K6) -> (lookup_etvar (appendCtx G G0) (weakenIndexTyVar X7 (domainCtx G0)) (weakenKind K6 (domainCtx G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Ctx} {x11 : (Index TmVar)} (T8 : Ty) ,
        (lookup_evar G x11 T8) -> (wfindex (domainCtx G) x11)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Ctx} {X7 : (Index TyVar)} (K8 : Kind) ,
        (lookup_etvar G X7 K8) -> (wfindex (domainCtx G) X7)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff TmVar) -> Ctx -> Ctx -> Prop :=
    | shift_evar_here {G : Ctx}
        {T6 : Ty} :
        (shift_evar C0 G (evar G T6))
    | shiftevar_there_evar
        {c1 : (Cutoff TmVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_evar c1 G G0) -> (shift_evar (CS c1) (evar G T) (evar G0 (shift_TmVar_Ty c1 T)))
    | shiftevar_there_etvar
        {c1 : (Cutoff TmVar)} {G : Ctx}
        {G0 : Ctx} {K : Kind} :
        (shift_evar c1 G G0) -> (shift_evar c1 (etvar G K) (etvar G0 (shift_TmVar_Kind c1 K))).
  Lemma weaken_shift_evar  :
    (forall (G : Ctx) {c1 : (Cutoff TmVar)} {G0 : Ctx} {G1 : Ctx} ,
      (shift_evar c1 G0 G1) -> (shift_evar (weakenCutoffTmVar c1 (domainCtx G)) (appendCtx G0 G) (appendCtx G1 (shift_TmVar_Ctx c1 G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff TyVar) -> Ctx -> Ctx -> Prop :=
    | shift_etvar_here {G : Ctx}
        {K6 : Kind} :
        (shift_etvar C0 G (etvar G K6))
    | shiftetvar_there_evar
        {c1 : (Cutoff TyVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_etvar c1 G G0) -> (shift_etvar c1 (evar G T) (evar G0 (shift_TyVar_Ty c1 T)))
    | shiftetvar_there_etvar
        {c1 : (Cutoff TyVar)} {G : Ctx}
        {G0 : Ctx} {K : Kind} :
        (shift_etvar c1 G G0) -> (shift_etvar (CS c1) (etvar G K) (etvar G0 (shift_TyVar_Kind c1 K))).
  Lemma weaken_shift_etvar  :
    (forall (G : Ctx) {c1 : (Cutoff TyVar)} {G0 : Ctx} {G1 : Ctx} ,
      (shift_etvar c1 G0 G1) -> (shift_etvar (weakenCutoffTyVar c1 (domainCtx G)) (appendCtx G0 G) (appendCtx G1 (shift_TyVar_Ctx c1 G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_TmVar  :
    (forall {c1 : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} ,
      (shift_evar c1 G G0) -> (shifthvl_TmVar c1 (domainCtx G) (domainCtx G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_etvar_shifthvl_TyVar  :
    (forall {c1 : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} ,
      (shift_etvar c1 G G0) -> (shifthvl_TyVar c1 (domainCtx G) (domainCtx G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Ctx) (T6 : Ty) (s4 : Tm) : (Trace TmVar) -> Ctx -> Ctx -> Prop :=
    | subst_evar_here :
        (subst_evar G T6 s4 X0 (evar G T6) G)
    | subst_evar_there_evar
        {d17 : (Trace TmVar)} {G0 : Ctx}
        {G1 : Ctx} (T7 : Ty) :
        (subst_evar G T6 s4 d17 G0 G1) -> (subst_evar G T6 s4 (XS TmVar d17) (evar G0 T7) (evar G1 (subst_TmVar_Ty d17 s4 T7)))
    | subst_evar_there_etvar
        {d17 : (Trace TmVar)} {G0 : Ctx}
        {G1 : Ctx} (K6 : Kind) :
        (subst_evar G T6 s4 d17 G0 G1) -> (subst_evar G T6 s4 (XS TyVar d17) (etvar G0 K6) (etvar G1 (subst_TmVar_Kind d17 s4 K6))).
  Lemma weaken_subst_evar {G : Ctx} (T6 : Ty) {s4 : Tm} :
    (forall (G0 : Ctx) {d17 : (Trace TmVar)} {G1 : Ctx} {G2 : Ctx} ,
      (subst_evar G T6 s4 d17 G1 G2) -> (subst_evar G T6 s4 (weakenTrace d17 (domainCtx G0)) (appendCtx G1 G0) (appendCtx G2 (subst_TmVar_Ctx d17 s4 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Ctx) (K6 : Kind) (S4 : Ty) : (Trace TyVar) -> Ctx -> Ctx -> Prop :=
    | subst_etvar_here :
        (subst_etvar G K6 S4 X0 (etvar G K6) G)
    | subst_etvar_there_evar
        {d17 : (Trace TyVar)} {G0 : Ctx}
        {G1 : Ctx} (T6 : Ty) :
        (subst_etvar G K6 S4 d17 G0 G1) -> (subst_etvar G K6 S4 (XS TmVar d17) (evar G0 T6) (evar G1 (subst_TyVar_Ty d17 S4 T6)))
    | subst_etvar_there_etvar
        {d17 : (Trace TyVar)} {G0 : Ctx}
        {G1 : Ctx} (K7 : Kind) :
        (subst_etvar G K6 S4 d17 G0 G1) -> (subst_etvar G K6 S4 (XS TyVar d17) (etvar G0 K7) (etvar G1 (subst_TyVar_Kind d17 S4 K7))).
  Lemma weaken_subst_etvar {G : Ctx} (K6 : Kind) {S4 : Ty} :
    (forall (G0 : Ctx) {d17 : (Trace TyVar)} {G1 : Ctx} {G2 : Ctx} ,
      (subst_etvar G K6 S4 d17 G1 G2) -> (subst_etvar G K6 S4 (weakenTrace d17 (domainCtx G0)) (appendCtx G1 G0) (appendCtx G2 (subst_TyVar_Ctx d17 S4 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_TmVar {G : Ctx} {s4 : Tm} (T6 : Ty) :
    (forall {d17 : (Trace TmVar)} {G0 : Ctx} {G1 : Ctx} ,
      (subst_evar G T6 s4 d17 G0 G1) -> (substhvl_TmVar (domainCtx G) d17 (domainCtx G0) (domainCtx G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_TyVar {G : Ctx} {S4 : Ty} (K6 : Kind) :
    (forall {d17 : (Trace TyVar)} {G0 : Ctx} {G1 : Ctx} ,
      (subst_etvar G K6 S4 d17 G0 G1) -> (substhvl_TyVar (domainCtx G) d17 (domainCtx G0) (domainCtx G1))).
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
  (forall {G : Ctx} (G0 : Ctx) {K6 : Kind} (wf : (wfKind (domainCtx G) K6)) ,
    (lookup_etvar (appendCtx (etvar G K6) G0) (weakenIndexTyVar I0 (domainCtx G0)) (weakenKind (shift_TyVar_Kind C0 K6) (domainCtx G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfDecls wfKind wfTm wfTy : infra.
 Hint Constructors wfDecls wfKind wfTm wfTy : wf.
 Hint Extern 10 ((wfDecls _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfKind _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfDecls _ _)) => match goal with
  | H39 : (wfDecls _ (DNil)) |- _ => inversion H39; subst; clear H39
  | H39 : (wfDecls _ (DConsTm _ _)) |- _ => inversion H39; subst; clear H39
  | H39 : (wfDecls _ (DConsTy _ _)) |- _ => inversion H39; subst; clear H39
end : infra wf.
 Hint Extern 2 ((wfKind _ _)) => match goal with
  | H39 : (wfKind _ (Star)) |- _ => inversion H39; subst; clear H39
  | H39 : (wfKind _ (KPi _ _)) |- _ => inversion H39; subst; clear H39
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H39 : (wfTy _ (TVar _)) |- _ => inversion H39; subst; clear H39
  | H39 : (wfTy _ (TPi _ _)) |- _ => inversion H39; subst; clear H39
  | H39 : (wfTy _ (TApp _ _)) |- _ => inversion H39; subst; clear H39
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H39 : (wfTm _ (Var _)) |- _ => inversion H39; subst; clear H39
  | H39 : (wfTm _ (Abs _ _)) |- _ => inversion H39; subst; clear H39
  | H39 : (wfTm _ (App _ _)) |- _ => inversion H39; subst; clear H39
  | H39 : (wfTm _ (Let _ _)) |- _ => inversion H39; subst; clear H39
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
  (forall {c1 : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evar c1 G G0)) {x11 : (Index TmVar)} {T6 : Ty} ,
    (lookup_evar G x11 T6) -> (lookup_evar G0 (shift_TmVar_Index c1 x11) (shift_TmVar_Ty c1 T6))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c1 : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evar c1 G G0)) {X7 : (Index TyVar)} {K6 : Kind} ,
    (lookup_etvar G X7 K6) -> (lookup_etvar G0 X7 (shift_TmVar_Kind c1 K6))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c1 : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_etvar c1 G G0)) {x11 : (Index TmVar)} {T6 : Ty} ,
    (lookup_evar G x11 T6) -> (lookup_evar G0 x11 (shift_TyVar_Ty c1 T6))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c1 : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_etvar c1 G G0)) {X7 : (Index TyVar)} {K6 : Kind} ,
    (lookup_etvar G X7 K6) -> (lookup_etvar G0 (shift_TyVar_Index c1 X7) (shift_TyVar_Kind c1 K6))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Ctx} (T7 : Ty) {s4 : Tm} (wf : (wfTm (domainCtx G) s4)) :
  (forall {d17 : (Trace TmVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_evar G T7 s4 d17 G0 G1)) {X7 : (Index TyVar)} (K7 : Kind) ,
    (lookup_etvar G0 X7 K7) -> (lookup_etvar G1 X7 (subst_TmVar_Kind d17 s4 K7))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Ctx} (K7 : Kind) {S4 : Ty} (wf : (wfTy (domainCtx G) S4)) :
  (forall {d17 : (Trace TyVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_etvar G K7 S4 d17 G0 G1)) {x11 : (Index TmVar)} (T7 : Ty) ,
    (lookup_evar G0 x11 T7) -> (lookup_evar G1 x11 (subst_TyVar_Ty d17 S4 T7))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Decls (d8 : Decls) {struct d8} :
nat :=
  match d8 with
    | (DNil) => 1
    | (DConsTm t6 d9) => (plus 1 (plus (size_Tm t6) (size_Decls d9)))
    | (DConsTy K3 d10) => (plus 1 (plus (size_Kind K3) (size_Decls d10)))
  end
with size_Kind (K3 : Kind) {struct K3} :
nat :=
  match K3 with
    | (Star) => 1
    | (KPi T5 K4) => (plus 1 (plus (size_Ty T5) (size_Kind K4)))
  end
with size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (TVar X7) => 1
    | (TPi T5 T6) => (plus 1 (plus (size_Ty T5) (size_Ty T6)))
    | (TApp T7 t6) => (plus 1 (plus (size_Ty T7) (size_Tm t6)))
  end
with size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (Var x11) => 1
    | (Abs T5 t6) => (plus 1 (plus (size_Ty T5) (size_Tm t6)))
    | (App t7 t8) => (plus 1 (plus (size_Tm t7) (size_Tm t8)))
    | (Let d8 t9) => (plus 1 (plus (size_Decls d8) (size_Tm t9)))
  end.
Fixpoint shift_TmVar__size_Decls (d14 : Decls) (c1 : (Cutoff TmVar)) {struct d14} :
((size_Decls (shift_TmVar_Decls c1 d14)) = (size_Decls d14)) :=
  match d14 return ((size_Decls (shift_TmVar_Decls c1 d14)) = (size_Decls d14)) with
    | (DNil) => eq_refl
    | (DConsTm t d) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t c1) (shift_TmVar__size_Decls d (CS c1))))
    | (DConsTy K d) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Kind K c1) (shift_TmVar__size_Decls d c1)))
  end
with shift_TmVar__size_Kind (K3 : Kind) (c1 : (Cutoff TmVar)) {struct K3} :
((size_Kind (shift_TmVar_Kind c1 K3)) = (size_Kind K3)) :=
  match K3 return ((size_Kind (shift_TmVar_Kind c1 K3)) = (size_Kind K3)) with
    | (Star) => eq_refl
    | (KPi T K) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Ty T c1) (shift_TmVar__size_Kind K (CS c1))))
  end
with shift_TmVar__size_Ty (S1 : Ty) (c1 : (Cutoff TmVar)) {struct S1} :
((size_Ty (shift_TmVar_Ty c1 S1)) = (size_Ty S1)) :=
  match S1 return ((size_Ty (shift_TmVar_Ty c1 S1)) = (size_Ty S1)) with
    | (TVar _) => eq_refl
    | (TPi T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Ty T1 c1) (shift_TmVar__size_Ty T2 (CS c1))))
    | (TApp T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Ty T c1) (shift_TmVar__size_Tm t c1)))
  end
with shift_TmVar__size_Tm (s0 : Tm) (c1 : (Cutoff TmVar)) {struct s0} :
((size_Tm (shift_TmVar_Tm c1 s0)) = (size_Tm s0)) :=
  match s0 return ((size_Tm (shift_TmVar_Tm c1 s0)) = (size_Tm s0)) with
    | (Var _) => eq_refl
    | (Abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Ty T c1) (shift_TmVar__size_Tm t (CS c1))))
    | (App t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t1 c1) (shift_TmVar__size_Tm t2 c1)))
    | (Let d t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Decls d c1) (shift_TmVar__size_Tm t (weakenCutoffTmVar c1 (appendHvl H0 (bind d))))))
  end.
Fixpoint shift_TyVar__size_Decls (d14 : Decls) (c1 : (Cutoff TyVar)) {struct d14} :
((size_Decls (shift_TyVar_Decls c1 d14)) = (size_Decls d14)) :=
  match d14 return ((size_Decls (shift_TyVar_Decls c1 d14)) = (size_Decls d14)) with
    | (DNil) => eq_refl
    | (DConsTm t d) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Tm t c1) (shift_TyVar__size_Decls d c1)))
    | (DConsTy K d) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Kind K c1) (shift_TyVar__size_Decls d (CS c1))))
  end
with shift_TyVar__size_Kind (K3 : Kind) (c1 : (Cutoff TyVar)) {struct K3} :
((size_Kind (shift_TyVar_Kind c1 K3)) = (size_Kind K3)) :=
  match K3 return ((size_Kind (shift_TyVar_Kind c1 K3)) = (size_Kind K3)) with
    | (Star) => eq_refl
    | (KPi T K) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T c1) (shift_TyVar__size_Kind K c1)))
  end
with shift_TyVar__size_Ty (S1 : Ty) (c1 : (Cutoff TyVar)) {struct S1} :
((size_Ty (shift_TyVar_Ty c1 S1)) = (size_Ty S1)) :=
  match S1 return ((size_Ty (shift_TyVar_Ty c1 S1)) = (size_Ty S1)) with
    | (TVar _) => eq_refl
    | (TPi T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T1 c1) (shift_TyVar__size_Ty T2 c1)))
    | (TApp T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T c1) (shift_TyVar__size_Tm t c1)))
  end
with shift_TyVar__size_Tm (s0 : Tm) (c1 : (Cutoff TyVar)) {struct s0} :
((size_Tm (shift_TyVar_Tm c1 s0)) = (size_Tm s0)) :=
  match s0 return ((size_Tm (shift_TyVar_Tm c1 s0)) = (size_Tm s0)) with
    | (Var _) => eq_refl
    | (Abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T c1) (shift_TyVar__size_Tm t c1)))
    | (App t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Tm t1 c1) (shift_TyVar__size_Tm t2 c1)))
    | (Let d t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Decls d c1) (shift_TyVar__size_Tm t (weakenCutoffTyVar c1 (appendHvl H0 (bind d))))))
  end.
 Hint Rewrite shift_TmVar__size_Decls shift_TyVar__size_Decls shift_TmVar__size_Kind shift_TyVar__size_Kind shift_TmVar__size_Tm shift_TyVar__size_Tm shift_TmVar__size_Ty shift_TyVar__size_Ty : interaction.
 Hint Rewrite shift_TmVar__size_Decls shift_TyVar__size_Decls shift_TmVar__size_Kind shift_TyVar__size_Kind shift_TmVar__size_Tm shift_TyVar__size_Tm shift_TmVar__size_Ty shift_TyVar__size_Ty : shift_size.
Lemma weaken_size_Decls  :
  (forall (k : Hvl) (d14 : Decls) ,
    ((size_Decls (weakenDecls d14 k)) = (size_Decls d14))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Kind  :
  (forall (k : Hvl) (K3 : Kind) ,
    ((size_Kind (weakenKind K3 k)) = (size_Kind K3))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Tm  :
  (forall (k : Hvl) (s0 : Tm) ,
    ((size_Tm (weakenTm s0 k)) = (size_Tm s0))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Ty  :
  (forall (k : Hvl) (S1 : Ty) ,
    ((size_Ty (weakenTy S1 k)) = (size_Ty S1))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Decls weaken_size_Kind weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Decls weaken_size_Kind weaken_size_Tm weaken_size_Ty : weaken_size.
 Hint Rewrite appendCtx_assoc : interaction.
 Hint Rewrite <- weakenCutoffTmVar_append weakenCutoffTyVar_append weakenTrace_append weakenDecls_append weakenKind_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.