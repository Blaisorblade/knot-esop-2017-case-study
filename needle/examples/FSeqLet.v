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
    (forall (x7 : (Index TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTmVar (weakenIndexTmVar x7 k) k0) = (weakenIndexTmVar x7 (appendHvl k k0)))).
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
  
  Inductive Decls : Set :=
    | DNil 
    | DCons (t : Tm) (d : Decls)
  with Tm : Set :=
    | Var (x : (Index TmVar))
    | Abs (T : Ty) (t : Tm)
    | App (t1 : Tm) (t2 : Tm)
    | TAbs (t : Tm)
    | TApp (t : Tm) (T : Ty)
    | Let (d : Decls) (t : Tm).
  Scheme ind_Decls := Induction for Decls Sort Prop
  with ind_Tm := Induction for Tm Sort Prop.
  Combined Scheme ind_Decls_Tm from ind_Decls, ind_Tm.
End Terms.

Section Functions.
  Fixpoint bind (d4 : Decls) {struct d4} :
  Hvl :=
    match d4 with
      | (DNil) => H0
      | (DCons t d) => (appendHvl (HS TmVar H0) (bind d))
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
  Fixpoint shift_TmVar_Index (c : (Cutoff TmVar)) (x7 : (Index TmVar)) {struct c} :
  (Index TmVar) :=
    match c with
      | (C0) => (IS x7)
      | (CS c) => match x7 with
        | (I0) => I0
        | (IS x7) => (IS (shift_TmVar_Index c x7))
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
      | (TArr T5 T6) => (TArr (shift_TyVar_Ty c T5) (shift_TyVar_Ty c T6))
      | (TAll T7) => (TAll (shift_TyVar_Ty (CS c) T7))
    end.
  Fixpoint shift_TmVar_Decls (c : (Cutoff TmVar)) (d5 : Decls) {struct d5} :
  Decls :=
    match d5 with
      | (DNil) => (DNil)
      | (DCons t7 d6) => (DCons (shift_TmVar_Tm c t7) (shift_TmVar_Decls (CS c) d6))
    end
  with shift_TmVar_Tm (c : (Cutoff TmVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x7) => (Var (shift_TmVar_Index c x7))
      | (Abs T5 t7) => (Abs T5 (shift_TmVar_Tm (CS c) t7))
      | (App t8 t9) => (App (shift_TmVar_Tm c t8) (shift_TmVar_Tm c t9))
      | (TAbs t10) => (TAbs (shift_TmVar_Tm c t10))
      | (TApp t11 T6) => (TApp (shift_TmVar_Tm c t11) T6)
      | (Let d5 t12) => (Let (shift_TmVar_Decls c d5) (shift_TmVar_Tm (weakenCutoffTmVar c (appendHvl H0 (bind d5))) t12))
    end.
  Fixpoint shift_TyVar_Decls (c : (Cutoff TyVar)) (d5 : Decls) {struct d5} :
  Decls :=
    match d5 with
      | (DNil) => (DNil)
      | (DCons t7 d6) => (DCons (shift_TyVar_Tm c t7) (shift_TyVar_Decls c d6))
    end
  with shift_TyVar_Tm (c : (Cutoff TyVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x7) => (Var x7)
      | (Abs T5 t7) => (Abs (shift_TyVar_Ty c T5) (shift_TyVar_Tm c t7))
      | (App t8 t9) => (App (shift_TyVar_Tm c t8) (shift_TyVar_Tm c t9))
      | (TAbs t10) => (TAbs (shift_TyVar_Tm (CS c) t10))
      | (TApp t11 T6) => (TApp (shift_TyVar_Tm c t11) (shift_TyVar_Ty c T6))
      | (Let d5 t12) => (Let (shift_TyVar_Decls c d5) (shift_TyVar_Tm (weakenCutoffTyVar c (appendHvl H0 (bind d5))) t12))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S0
      | (HS TmVar k) => (weakenTy S0 k)
      | (HS TyVar k) => (shift_TyVar_Ty C0 (weakenTy S0 k))
    end.
  Fixpoint weakenDecls (d5 : Decls) (k : Hvl) {struct k} :
  Decls :=
    match k with
      | (H0) => d5
      | (HS TmVar k) => (shift_TmVar_Decls C0 (weakenDecls d5 k))
      | (HS TyVar k) => (shift_TyVar_Decls C0 (weakenDecls d5 k))
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
  Fixpoint subst_TmVar_Index (d5 : (Trace TmVar)) (s : Tm) (x7 : (Index TmVar)) {struct d5} :
  Tm :=
    match d5 with
      | (X0) => match x7 with
        | (I0) => s
        | (IS x7) => (Var x7)
      end
      | (XS TmVar d5) => match x7 with
        | (I0) => (Var I0)
        | (IS x7) => (shift_TmVar_Tm C0 (subst_TmVar_Index d5 s x7))
      end
      | (XS TyVar d5) => (shift_TyVar_Tm C0 (subst_TmVar_Index d5 s x7))
    end.
  Fixpoint subst_TyVar_Index (d5 : (Trace TyVar)) (S0 : Ty) (X7 : (Index TyVar)) {struct d5} :
  Ty :=
    match d5 with
      | (X0) => match X7 with
        | (I0) => S0
        | (IS X7) => (TVar X7)
      end
      | (XS TmVar d5) => (subst_TyVar_Index d5 S0 X7)
      | (XS TyVar d5) => match X7 with
        | (I0) => (TVar I0)
        | (IS X7) => (shift_TyVar_Ty C0 (subst_TyVar_Index d5 S0 X7))
      end
    end.
  Fixpoint subst_TyVar_Ty (d5 : (Trace TyVar)) (S0 : Ty) (S1 : Ty) {struct S1} :
  Ty :=
    match S1 with
      | (TVar X7) => (subst_TyVar_Index d5 S0 X7)
      | (TArr T5 T6) => (TArr (subst_TyVar_Ty d5 S0 T5) (subst_TyVar_Ty d5 S0 T6))
      | (TAll T7) => (TAll (subst_TyVar_Ty (weakenTrace d5 (HS TyVar H0)) S0 T7))
    end.
  Fixpoint subst_TmVar_Decls (d5 : (Trace TmVar)) (s : Tm) (d6 : Decls) {struct d6} :
  Decls :=
    match d6 with
      | (DNil) => (DNil)
      | (DCons t7 d7) => (DCons (subst_TmVar_Tm d5 s t7) (subst_TmVar_Decls (weakenTrace d5 (HS TmVar H0)) s d7))
    end
  with subst_TmVar_Tm (d5 : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (Var x7) => (subst_TmVar_Index d5 s x7)
      | (Abs T5 t7) => (Abs T5 (subst_TmVar_Tm (weakenTrace d5 (HS TmVar H0)) s t7))
      | (App t8 t9) => (App (subst_TmVar_Tm d5 s t8) (subst_TmVar_Tm d5 s t9))
      | (TAbs t10) => (TAbs (subst_TmVar_Tm (weakenTrace d5 (HS TyVar H0)) s t10))
      | (TApp t11 T6) => (TApp (subst_TmVar_Tm d5 s t11) T6)
      | (Let d6 t12) => (Let (subst_TmVar_Decls d5 s d6) (subst_TmVar_Tm (weakenTrace d5 (appendHvl H0 (bind d6))) s t12))
    end.
  Fixpoint subst_TyVar_Decls (d5 : (Trace TyVar)) (S0 : Ty) (d6 : Decls) {struct d6} :
  Decls :=
    match d6 with
      | (DNil) => (DNil)
      | (DCons t7 d7) => (DCons (subst_TyVar_Tm d5 S0 t7) (subst_TyVar_Decls (weakenTrace d5 (HS TmVar H0)) S0 d7))
    end
  with subst_TyVar_Tm (d5 : (Trace TyVar)) (S0 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x7) => (Var x7)
      | (Abs T5 t7) => (Abs (subst_TyVar_Ty d5 S0 T5) (subst_TyVar_Tm (weakenTrace d5 (HS TmVar H0)) S0 t7))
      | (App t8 t9) => (App (subst_TyVar_Tm d5 S0 t8) (subst_TyVar_Tm d5 S0 t9))
      | (TAbs t10) => (TAbs (subst_TyVar_Tm (weakenTrace d5 (HS TyVar H0)) S0 t10))
      | (TApp t11 T6) => (TApp (subst_TyVar_Tm d5 S0 t11) (subst_TyVar_Ty d5 S0 T6))
      | (Let d6 t12) => (Let (subst_TyVar_Decls d5 S0 d6) (subst_TyVar_Tm (weakenTrace d5 (appendHvl H0 (bind d6))) S0 t12))
    end.
End Subst.

Global Hint Resolve (f_equal (shift_TmVar_Decls C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TyVar_Decls C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TmVar_Tm C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TyVar_Tm C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TyVar_Ty C0)) : cong_shift0.
 Hint Rewrite weakenCutoffTmVar_append weakenCutoffTyVar_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_shift_TmVar__bind  :
  (forall (d5 : Decls) ,
    (forall (c : (Cutoff TmVar)) ,
      ((bind (shift_TmVar_Decls c d5)) = (bind d5)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
Lemma stability_shift_TyVar__bind  :
  (forall (d6 : Decls) ,
    (forall (c0 : (Cutoff TyVar)) ,
      ((bind (shift_TyVar_Decls c0 d6)) = (bind d6)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_shift_TmVar__bind stability_shift_TyVar__bind : interaction.
 Hint Rewrite stability_shift_TmVar__bind stability_shift_TyVar__bind : stability_shift.
Lemma stability_weaken_bind  :
  (forall (k : Hvl) (d7 : Decls) ,
    ((bind (weakenDecls d7 k)) = (bind d7))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bind : interaction.
 Hint Rewrite stability_weaken_bind : stability_weaken.
Lemma stability_subst_TmVar__bind  :
  (forall (d7 : Decls) ,
    (forall (d8 : (Trace TmVar)) (s : Tm) ,
      ((bind (subst_TmVar_Decls d8 s d7)) = (bind d7)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
Lemma stability_subst_TyVar__bind  :
  (forall (d9 : Decls) ,
    (forall (d10 : (Trace TyVar)) (S0 : Ty) ,
      ((bind (subst_TyVar_Decls d10 S0 d9)) = (bind d9)))).
Proof.
  apply_mutual_ind (ind_bind_Decls); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_subst_TmVar__bind stability_subst_TyVar__bind : interaction.
 Hint Rewrite stability_subst_TmVar__bind stability_subst_TyVar__bind : stability_subst.
Section SubstShiftReflection.
  Lemma subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind (s0 : Tm) :
    (forall (k : Hvl) (x7 : (Index TmVar)) ,
      ((subst_TmVar_Index (weakenTrace X0 k) s0 (shift_TmVar_Index (weakenCutoffTmVar C0 k) x7)) = (Var x7))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma subst_TyVar_Index0_shift_TyVar_Index0_reflection_ind (S1 : Ty) :
    (forall (k : Hvl) (X7 : (Index TyVar)) ,
      ((subst_TyVar_Index (weakenTrace X0 k) S1 (shift_TyVar_Index (weakenCutoffTyVar C0 k) X7)) = (TVar X7))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind (S2 : Ty) (k : Hvl) (S1 : Ty) {struct S2} :
  ((subst_TyVar_Ty (weakenTrace X0 k) S1 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S2)) = S2) :=
    match S2 return ((subst_TyVar_Ty (weakenTrace X0 k) S1 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S2)) = S2) with
      | (TVar X7) => (subst_TyVar_Index0_shift_TyVar_Index0_reflection_ind S1 k X7)
      | (TArr T6 T7) => (f_equal2 TArr (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T6 k S1) (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T7 k S1))
      | (TAll T5) => (f_equal TAll (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T5 (HS TyVar k) S1)))
    end.
  Fixpoint subst_TmVar_0_shift_TmVar_0_Decls_reflection_ind (d11 : Decls) (k : Hvl) (s0 : Tm) {struct d11} :
  ((subst_TmVar_Decls (weakenTrace X0 k) s0 (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d11)) = d11) :=
    match d11 return ((subst_TmVar_Decls (weakenTrace X0 k) s0 (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d11)) = d11) with
      | (DNil) => eq_refl
      | (DCons t7 d12) => (f_equal2 DCons (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t7 k s0) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Decls_reflection_ind d12 (HS TmVar k) s0)))
    end
  with subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind (s1 : Tm) (k : Hvl) (s0 : Tm) {struct s1} :
  ((subst_TmVar_Tm (weakenTrace X0 k) s0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s1)) = s1) :=
    match s1 return ((subst_TmVar_Tm (weakenTrace X0 k) s0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s1)) = s1) with
      | (Var x8) => (subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind s0 k x8)
      | (Abs T5 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t8 (HS TmVar k) s0)))
      | (App t9 t10) => (f_equal2 App (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t9 k s0) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t10 k s0))
      | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t8 (HS TyVar k) s0)))
      | (TApp t8 T5) => (f_equal2 TApp (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t8 k s0) eq_refl)
      | (Let d13 t8) => (f_equal2 Let (subst_TmVar_0_shift_TmVar_0_Decls_reflection_ind d13 k s0) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d13)))) eq_refl (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d13))) eq_refl)) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t8 (appendHvl k (appendHvl H0 (bind d13))) s0)))
    end.
  Fixpoint subst_TyVar_0_shift_TyVar_0_Decls_reflection_ind (d11 : Decls) (k : Hvl) (S1 : Ty) {struct d11} :
  ((subst_TyVar_Decls (weakenTrace X0 k) S1 (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d11)) = d11) :=
    match d11 return ((subst_TyVar_Decls (weakenTrace X0 k) S1 (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d11)) = d11) with
      | (DNil) => eq_refl
      | (DCons t7 d12) => (f_equal2 DCons (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t7 k S1) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Decls_reflection_ind d12 (HS TmVar k) S1)))
    end
  with subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (S1 : Ty) {struct s0} :
  ((subst_TyVar_Tm (weakenTrace X0 k) S1 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = s0) :=
    match s0 return ((subst_TyVar_Tm (weakenTrace X0 k) S1 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = s0) with
      | (Var x8) => eq_refl
      | (Abs T5 t8) => (f_equal2 Abs (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T5 k S1) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t8 (HS TmVar k) S1)))
      | (App t9 t10) => (f_equal2 App (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t9 k S1) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t10 k S1))
      | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t8 (HS TyVar k) S1)))
      | (TApp t8 T5) => (f_equal2 TApp (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t8 k S1) (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind T5 k S1))
      | (Let d13 t8) => (f_equal2 Let (subst_TyVar_0_shift_TyVar_0_Decls_reflection_ind d13 k S1) (eq_trans (f_equal3 subst_TyVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TyVar__bind _ _))) (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d13)))) eq_refl (f_equal2 shift_TyVar_Tm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d13))) eq_refl)) (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind t8 (appendHvl k (appendHvl H0 (bind d13))) S1)))
    end.
  Definition subst_TyVar_Ty0_shift_TyVar_Ty0_reflection (S2 : Ty) : (forall (S1 : Ty) ,
    ((subst_TyVar_Ty X0 S1 (shift_TyVar_Ty C0 S2)) = S2)) := (subst_TyVar_0_shift_TyVar_0_Ty_reflection_ind S2 H0).
  Definition subst_TmVar_Decls0_shift_TmVar_Decls0_reflection (d11 : Decls) : (forall (s0 : Tm) ,
    ((subst_TmVar_Decls X0 s0 (shift_TmVar_Decls C0 d11)) = d11)) := (subst_TmVar_0_shift_TmVar_0_Decls_reflection_ind d11 H0).
  Definition subst_TmVar_Tm0_shift_TmVar_Tm0_reflection (s1 : Tm) : (forall (s0 : Tm) ,
    ((subst_TmVar_Tm X0 s0 (shift_TmVar_Tm C0 s1)) = s1)) := (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind s1 H0).
  Definition subst_TyVar_Decls0_shift_TyVar_Decls0_reflection (d11 : Decls) : (forall (S1 : Ty) ,
    ((subst_TyVar_Decls X0 S1 (shift_TyVar_Decls C0 d11)) = d11)) := (subst_TyVar_0_shift_TyVar_0_Decls_reflection_ind d11 H0).
  Definition subst_TyVar_Tm0_shift_TyVar_Tm0_reflection (s0 : Tm) : (forall (S1 : Ty) ,
    ((subst_TyVar_Tm X0 S1 (shift_TyVar_Tm C0 s0)) = s0)) := (subst_TyVar_0_shift_TyVar_0_Tm_reflection_ind s0 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shift_TmVar_Index_shift_TmVar_Index0_comm_ind  :
      (forall (k : Hvl) (c1 : (Cutoff TmVar)) (x7 : (Index TmVar)) ,
        ((shift_TmVar_Index (weakenCutoffTmVar (CS c1) k) (shift_TmVar_Index (weakenCutoffTmVar C0 k) x7)) = (shift_TmVar_Index (weakenCutoffTmVar C0 k) (shift_TmVar_Index (weakenCutoffTmVar c1 k) x7)))).
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
    Fixpoint shift_TyVar__shift_TyVar_0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c1 : (Cutoff TyVar)) {struct S1} :
    ((shift_TyVar_Ty (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c1 k) S1))) :=
      match S1 return ((shift_TyVar_Ty (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S1)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (shift_TyVar_Ty (weakenCutoffTyVar c1 k) S1))) with
        | (TVar X7) => (f_equal TVar (shift_TyVar_Index_shift_TyVar_Index0_comm_ind k c1 X7))
        | (TArr T6 T7) => (f_equal2 TArr (shift_TyVar__shift_TyVar_0_Ty_comm_ind T6 k c1) (shift_TyVar__shift_TyVar_0_Ty_comm_ind T7 k c1))
        | (TAll T5) => (f_equal TAll (shift_TyVar__shift_TyVar_0_Ty_comm_ind T5 (HS TyVar k) c1))
      end.
    Fixpoint shift_TmVar__shift_TmVar_0_Decls_comm_ind (d11 : Decls) (k : Hvl) (c1 : (Cutoff TmVar)) {struct d11} :
    ((shift_TmVar_Decls (weakenCutoffTmVar (CS c1) k) (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d11)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (shift_TmVar_Decls (weakenCutoffTmVar c1 k) d11))) :=
      match d11 return ((shift_TmVar_Decls (weakenCutoffTmVar (CS c1) k) (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d11)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (shift_TmVar_Decls (weakenCutoffTmVar c1 k) d11))) with
        | (DNil) => eq_refl
        | (DCons t7 d12) => (f_equal2 DCons (shift_TmVar__shift_TmVar_0_Tm_comm_ind t7 k c1) (shift_TmVar__shift_TmVar_0_Decls_comm_ind d12 (HS TmVar k) c1))
      end
    with shift_TmVar__shift_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff TmVar)) {struct s0} :
    ((shift_TmVar_Tm (weakenCutoffTmVar (CS c1) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c1 k) s0))) :=
      match s0 return ((shift_TmVar_Tm (weakenCutoffTmVar (CS c1) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c1 k) s0))) with
        | (Var x8) => (f_equal Var (shift_TmVar_Index_shift_TmVar_Index0_comm_ind k c1 x8))
        | (Abs T5 t8) => (f_equal2 Abs eq_refl (shift_TmVar__shift_TmVar_0_Tm_comm_ind t8 (HS TmVar k) c1))
        | (App t9 t10) => (f_equal2 App (shift_TmVar__shift_TmVar_0_Tm_comm_ind t9 k c1) (shift_TmVar__shift_TmVar_0_Tm_comm_ind t10 k c1))
        | (TAbs t8) => (f_equal TAbs (shift_TmVar__shift_TmVar_0_Tm_comm_ind t8 (HS TyVar k) c1))
        | (TApp t8 T5) => (f_equal2 TApp (shift_TmVar__shift_TmVar_0_Tm_comm_ind t8 k c1) eq_refl)
        | (Let d13 t8) => (f_equal2 Let (shift_TmVar__shift_TmVar_0_Decls_comm_ind d13 k c1) (eq_trans (f_equal2 shift_TmVar_Tm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenCutoffTmVar_append (CS c1) k (appendHvl H0 (bind d13)))) (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d13))) eq_refl)) (eq_trans (shift_TmVar__shift_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d13))) c1) (f_equal2 shift_TmVar_Tm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d13)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _))))) (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append c1 k (appendHvl H0 (bind d13)))) eq_refl)))))
      end.
    Fixpoint shift_TmVar__shift_TyVar_0_Decls_comm_ind (d11 : Decls) (k : Hvl) (c1 : (Cutoff TmVar)) {struct d11} :
    ((shift_TmVar_Decls (weakenCutoffTmVar c1 k) (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d11)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (shift_TmVar_Decls (weakenCutoffTmVar c1 k) d11))) :=
      match d11 return ((shift_TmVar_Decls (weakenCutoffTmVar c1 k) (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d11)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (shift_TmVar_Decls (weakenCutoffTmVar c1 k) d11))) with
        | (DNil) => eq_refl
        | (DCons t7 d12) => (f_equal2 DCons (shift_TmVar__shift_TyVar_0_Tm_comm_ind t7 k c1) (shift_TmVar__shift_TyVar_0_Decls_comm_ind d12 (HS TmVar k) c1))
      end
    with shift_TmVar__shift_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff TmVar)) {struct s0} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c1 k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c1 k) s0))) :=
      match s0 return ((shift_TmVar_Tm (weakenCutoffTmVar c1 k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c1 k) s0))) with
        | (Var x8) => eq_refl
        | (Abs T5 t8) => (f_equal2 Abs eq_refl (shift_TmVar__shift_TyVar_0_Tm_comm_ind t8 (HS TmVar k) c1))
        | (App t9 t10) => (f_equal2 App (shift_TmVar__shift_TyVar_0_Tm_comm_ind t9 k c1) (shift_TmVar__shift_TyVar_0_Tm_comm_ind t10 k c1))
        | (TAbs t8) => (f_equal TAbs (shift_TmVar__shift_TyVar_0_Tm_comm_ind t8 (HS TyVar k) c1))
        | (TApp t8 T5) => (f_equal2 TApp (shift_TmVar__shift_TyVar_0_Tm_comm_ind t8 k c1) eq_refl)
        | (Let d13 t8) => (f_equal2 Let (shift_TmVar__shift_TyVar_0_Decls_comm_ind d13 k c1) (eq_trans (f_equal2 shift_TmVar_Tm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TyVar__bind _ _))) (weakenCutoffTmVar_append c1 k (appendHvl H0 (bind d13)))) (f_equal2 shift_TyVar_Tm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d13))) eq_refl)) (eq_trans (shift_TmVar__shift_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d13))) c1) (f_equal2 shift_TyVar_Tm (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d13)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _))))) (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append c1 k (appendHvl H0 (bind d13)))) eq_refl)))))
      end.
    Fixpoint shift_TyVar__shift_TmVar_0_Decls_comm_ind (d11 : Decls) (k : Hvl) (c1 : (Cutoff TyVar)) {struct d11} :
    ((shift_TyVar_Decls (weakenCutoffTyVar c1 k) (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d11)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (shift_TyVar_Decls (weakenCutoffTyVar c1 k) d11))) :=
      match d11 return ((shift_TyVar_Decls (weakenCutoffTyVar c1 k) (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d11)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (shift_TyVar_Decls (weakenCutoffTyVar c1 k) d11))) with
        | (DNil) => eq_refl
        | (DCons t7 d12) => (f_equal2 DCons (shift_TyVar__shift_TmVar_0_Tm_comm_ind t7 k c1) (shift_TyVar__shift_TmVar_0_Decls_comm_ind d12 (HS TmVar k) c1))
      end
    with shift_TyVar__shift_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff TyVar)) {struct s0} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c1 k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c1 k) s0))) :=
      match s0 return ((shift_TyVar_Tm (weakenCutoffTyVar c1 k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c1 k) s0))) with
        | (Var x8) => eq_refl
        | (Abs T5 t8) => (f_equal2 Abs eq_refl (shift_TyVar__shift_TmVar_0_Tm_comm_ind t8 (HS TmVar k) c1))
        | (App t9 t10) => (f_equal2 App (shift_TyVar__shift_TmVar_0_Tm_comm_ind t9 k c1) (shift_TyVar__shift_TmVar_0_Tm_comm_ind t10 k c1))
        | (TAbs t8) => (f_equal TAbs (shift_TyVar__shift_TmVar_0_Tm_comm_ind t8 (HS TyVar k) c1))
        | (TApp t8 T5) => (f_equal2 TApp (shift_TyVar__shift_TmVar_0_Tm_comm_ind t8 k c1) eq_refl)
        | (Let d13 t8) => (f_equal2 Let (shift_TyVar__shift_TmVar_0_Decls_comm_ind d13 k c1) (eq_trans (f_equal2 shift_TyVar_Tm (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenCutoffTyVar_append c1 k (appendHvl H0 (bind d13)))) (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d13))) eq_refl)) (eq_trans (shift_TyVar__shift_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d13))) c1) (f_equal2 shift_TmVar_Tm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d13)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TyVar__bind _ _))))) (f_equal2 shift_TyVar_Tm (eq_sym (weakenCutoffTyVar_append c1 k (appendHvl H0 (bind d13)))) eq_refl)))))
      end.
    Fixpoint shift_TyVar__shift_TyVar_0_Decls_comm_ind (d11 : Decls) (k : Hvl) (c1 : (Cutoff TyVar)) {struct d11} :
    ((shift_TyVar_Decls (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d11)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (shift_TyVar_Decls (weakenCutoffTyVar c1 k) d11))) :=
      match d11 return ((shift_TyVar_Decls (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d11)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (shift_TyVar_Decls (weakenCutoffTyVar c1 k) d11))) with
        | (DNil) => eq_refl
        | (DCons t7 d12) => (f_equal2 DCons (shift_TyVar__shift_TyVar_0_Tm_comm_ind t7 k c1) (shift_TyVar__shift_TyVar_0_Decls_comm_ind d12 (HS TmVar k) c1))
      end
    with shift_TyVar__shift_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff TyVar)) {struct s0} :
    ((shift_TyVar_Tm (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c1 k) s0))) :=
      match s0 return ((shift_TyVar_Tm (weakenCutoffTyVar (CS c1) k) (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (shift_TyVar_Tm (weakenCutoffTyVar c1 k) s0))) with
        | (Var x8) => eq_refl
        | (Abs T5 t8) => (f_equal2 Abs (shift_TyVar__shift_TyVar_0_Ty_comm_ind T5 k c1) (shift_TyVar__shift_TyVar_0_Tm_comm_ind t8 (HS TmVar k) c1))
        | (App t9 t10) => (f_equal2 App (shift_TyVar__shift_TyVar_0_Tm_comm_ind t9 k c1) (shift_TyVar__shift_TyVar_0_Tm_comm_ind t10 k c1))
        | (TAbs t8) => (f_equal TAbs (shift_TyVar__shift_TyVar_0_Tm_comm_ind t8 (HS TyVar k) c1))
        | (TApp t8 T5) => (f_equal2 TApp (shift_TyVar__shift_TyVar_0_Tm_comm_ind t8 k c1) (shift_TyVar__shift_TyVar_0_Ty_comm_ind T5 k c1))
        | (Let d13 t8) => (f_equal2 Let (shift_TyVar__shift_TyVar_0_Decls_comm_ind d13 k c1) (eq_trans (f_equal2 shift_TyVar_Tm (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TyVar__bind _ _))) (weakenCutoffTyVar_append (CS c1) k (appendHvl H0 (bind d13)))) (f_equal2 shift_TyVar_Tm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d13))) eq_refl)) (eq_trans (shift_TyVar__shift_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d13))) c1) (f_equal2 shift_TyVar_Tm (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d13)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TyVar__bind _ _))))) (f_equal2 shift_TyVar_Tm (eq_sym (weakenCutoffTyVar_append c1 k (appendHvl H0 (bind d13)))) eq_refl)))))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition shift_TyVar__shift_TyVar_0_Ty_comm (S1 : Ty) : (forall (c1 : (Cutoff TyVar)) ,
      ((shift_TyVar_Ty (CS c1) (shift_TyVar_Ty C0 S1)) = (shift_TyVar_Ty C0 (shift_TyVar_Ty c1 S1)))) := (shift_TyVar__shift_TyVar_0_Ty_comm_ind S1 H0).
    Definition shift_TmVar__shift_TmVar_0_Decls_comm (d11 : Decls) : (forall (c1 : (Cutoff TmVar)) ,
      ((shift_TmVar_Decls (CS c1) (shift_TmVar_Decls C0 d11)) = (shift_TmVar_Decls C0 (shift_TmVar_Decls c1 d11)))) := (shift_TmVar__shift_TmVar_0_Decls_comm_ind d11 H0).
    Definition shift_TmVar__shift_TmVar_0_Tm_comm (s0 : Tm) : (forall (c1 : (Cutoff TmVar)) ,
      ((shift_TmVar_Tm (CS c1) (shift_TmVar_Tm C0 s0)) = (shift_TmVar_Tm C0 (shift_TmVar_Tm c1 s0)))) := (shift_TmVar__shift_TmVar_0_Tm_comm_ind s0 H0).
    Definition shift_TmVar__shift_TyVar_0_Decls_comm (d11 : Decls) : (forall (c1 : (Cutoff TmVar)) ,
      ((shift_TmVar_Decls c1 (shift_TyVar_Decls C0 d11)) = (shift_TyVar_Decls C0 (shift_TmVar_Decls c1 d11)))) := (shift_TmVar__shift_TyVar_0_Decls_comm_ind d11 H0).
    Definition shift_TmVar__shift_TyVar_0_Tm_comm (s0 : Tm) : (forall (c1 : (Cutoff TmVar)) ,
      ((shift_TmVar_Tm c1 (shift_TyVar_Tm C0 s0)) = (shift_TyVar_Tm C0 (shift_TmVar_Tm c1 s0)))) := (shift_TmVar__shift_TyVar_0_Tm_comm_ind s0 H0).
    Definition shift_TyVar__shift_TmVar_0_Decls_comm (d11 : Decls) : (forall (c1 : (Cutoff TyVar)) ,
      ((shift_TyVar_Decls c1 (shift_TmVar_Decls C0 d11)) = (shift_TmVar_Decls C0 (shift_TyVar_Decls c1 d11)))) := (shift_TyVar__shift_TmVar_0_Decls_comm_ind d11 H0).
    Definition shift_TyVar__shift_TmVar_0_Tm_comm (s0 : Tm) : (forall (c1 : (Cutoff TyVar)) ,
      ((shift_TyVar_Tm c1 (shift_TmVar_Tm C0 s0)) = (shift_TmVar_Tm C0 (shift_TyVar_Tm c1 s0)))) := (shift_TyVar__shift_TmVar_0_Tm_comm_ind s0 H0).
    Definition shift_TyVar__shift_TyVar_0_Decls_comm (d11 : Decls) : (forall (c1 : (Cutoff TyVar)) ,
      ((shift_TyVar_Decls (CS c1) (shift_TyVar_Decls C0 d11)) = (shift_TyVar_Decls C0 (shift_TyVar_Decls c1 d11)))) := (shift_TyVar__shift_TyVar_0_Decls_comm_ind d11 H0).
    Definition shift_TyVar__shift_TyVar_0_Tm_comm (s0 : Tm) : (forall (c1 : (Cutoff TyVar)) ,
      ((shift_TyVar_Tm (CS c1) (shift_TyVar_Tm C0 s0)) = (shift_TyVar_Tm C0 (shift_TyVar_Tm c1 s0)))) := (shift_TyVar__shift_TyVar_0_Tm_comm_ind s0 H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_TmVar__shift_TmVar_0_Decls_comm shift_TmVar__shift_TyVar_0_Decls_comm shift_TyVar__shift_TmVar_0_Decls_comm shift_TyVar__shift_TyVar_0_Decls_comm shift_TmVar__shift_TmVar_0_Tm_comm shift_TmVar__shift_TyVar_0_Tm_comm shift_TyVar__shift_TmVar_0_Tm_comm shift_TyVar__shift_TyVar_0_Tm_comm shift_TyVar__shift_TyVar_0_Ty_comm : interaction.
 Hint Rewrite shift_TmVar__shift_TmVar_0_Decls_comm shift_TmVar__shift_TyVar_0_Decls_comm shift_TyVar__shift_TmVar_0_Decls_comm shift_TyVar__shift_TyVar_0_Decls_comm shift_TmVar__shift_TmVar_0_Tm_comm shift_TmVar__shift_TyVar_0_Tm_comm shift_TyVar__shift_TmVar_0_Tm_comm shift_TyVar__shift_TyVar_0_Tm_comm shift_TyVar__shift_TyVar_0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTy_shift_TyVar_Ty  :
    (forall (k : Hvl) (c1 : (Cutoff TyVar)) (S1 : Ty) ,
      ((weakenTy (shift_TyVar_Ty c1 S1) k) = (shift_TyVar_Ty (weakenCutoffTyVar c1 k) (weakenTy S1 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenDecls_shift_TmVar_Decls  :
    (forall (k : Hvl) (c1 : (Cutoff TmVar)) (d11 : Decls) ,
      ((weakenDecls (shift_TmVar_Decls c1 d11) k) = (shift_TmVar_Decls (weakenCutoffTmVar c1 k) (weakenDecls d11 k)))).
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
    (forall (k : Hvl) (c1 : (Cutoff TyVar)) (d11 : Decls) ,
      ((weakenDecls (shift_TyVar_Decls c1 d11) k) = (shift_TyVar_Decls (weakenCutoffTyVar c1 k) (weakenDecls d11 k)))).
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
      (forall (k : Hvl) (x7 : (Index TmVar)) ,
        ((shift_TmVar_Tm (weakenCutoffTmVar c1 k) (subst_TmVar_Index (weakenTrace X0 k) s0 x7)) = (subst_TmVar_Index (weakenTrace X0 k) (shift_TmVar_Tm c1 s0) (shift_TmVar_Index (weakenCutoffTmVar (CS c1) k) x7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_TyVar_Tm_subst_TmVar_Index0_comm_ind (c1 : (Cutoff TyVar)) (s0 : Tm) :
      (forall (k : Hvl) (x7 : (Index TmVar)) ,
        ((shift_TyVar_Tm (weakenCutoffTyVar c1 k) (subst_TmVar_Index (weakenTrace X0 k) s0 x7)) = (subst_TmVar_Index (weakenTrace X0 k) (shift_TyVar_Tm c1 s0) x7))).
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
    Fixpoint shift_TyVar__subst_TyVar_0_Ty_comm_ind (S2 : Ty) (k : Hvl) (c1 : (Cutoff TyVar)) (S1 : Ty) {struct S2} :
    ((shift_TyVar_Ty (weakenCutoffTyVar c1 k) (subst_TyVar_Ty (weakenTrace X0 k) S1 S2)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Ty (weakenCutoffTyVar (CS c1) k) S2))) :=
      match S2 return ((shift_TyVar_Ty (weakenCutoffTyVar c1 k) (subst_TyVar_Ty (weakenTrace X0 k) S1 S2)) = (subst_TyVar_Ty (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Ty (weakenCutoffTyVar (CS c1) k) S2))) with
        | (TVar X7) => (shift_TyVar_Ty_subst_TyVar_Index0_comm_ind c1 S1 k X7)
        | (TArr T6 T7) => (f_equal2 TArr (shift_TyVar__subst_TyVar_0_Ty_comm_ind T6 k c1 S1) (shift_TyVar__subst_TyVar_0_Ty_comm_ind T7 k c1 S1))
        | (TAll T5) => (f_equal TAll (eq_trans (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Ty_comm_ind T5 (HS TyVar k) c1 S1) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_TmVar__subst_TmVar_0_Decls_comm_ind (d11 : Decls) (k : Hvl) (c1 : (Cutoff TmVar)) (s0 : Tm) {struct d11} :
    ((shift_TmVar_Decls (weakenCutoffTmVar c1 k) (subst_TmVar_Decls (weakenTrace X0 k) s0 d11)) = (subst_TmVar_Decls (weakenTrace X0 k) (shift_TmVar_Tm c1 s0) (shift_TmVar_Decls (weakenCutoffTmVar (CS c1) k) d11))) :=
      match d11 return ((shift_TmVar_Decls (weakenCutoffTmVar c1 k) (subst_TmVar_Decls (weakenTrace X0 k) s0 d11)) = (subst_TmVar_Decls (weakenTrace X0 k) (shift_TmVar_Tm c1 s0) (shift_TmVar_Decls (weakenCutoffTmVar (CS c1) k) d11))) with
        | (DNil) => eq_refl
        | (DCons t7 d12) => (f_equal2 DCons (shift_TmVar__subst_TmVar_0_Tm_comm_ind t7 k c1 s0) (eq_trans (f_equal2 shift_TmVar_Decls eq_refl (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Decls_comm_ind d12 (HS TmVar k) c1 s0) (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end
    with shift_TmVar__subst_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (c1 : (Cutoff TmVar)) (s0 : Tm) {struct s1} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c1 k) (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c1 s0) (shift_TmVar_Tm (weakenCutoffTmVar (CS c1) k) s1))) :=
      match s1 return ((shift_TmVar_Tm (weakenCutoffTmVar c1 k) (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c1 s0) (shift_TmVar_Tm (weakenCutoffTmVar (CS c1) k) s1))) with
        | (Var x8) => (shift_TmVar_Tm_subst_TmVar_Index0_comm_ind c1 s0 k x8)
        | (Abs T5 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind t8 (HS TmVar k) c1 s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t9 t10) => (f_equal2 App (shift_TmVar__subst_TmVar_0_Tm_comm_ind t9 k c1 s0) (shift_TmVar__subst_TmVar_0_Tm_comm_ind t10 k c1 s0))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind t8 (HS TyVar k) c1 s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t8 T5) => (f_equal2 TApp (shift_TmVar__subst_TmVar_0_Tm_comm_ind t8 k c1 s0) eq_refl)
        | (Let d13 t8) => (f_equal2 Let (shift_TmVar__subst_TmVar_0_Decls_comm_ind d13 k c1 s0) (eq_trans (f_equal2 shift_TmVar_Tm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TmVar__bind _ _ _) (eq_refl H0)))) (weakenCutoffTmVar_append c1 k (appendHvl H0 (bind d13)))) (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d13))) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d13))) c1 s0) (f_equal3 subst_TmVar_Tm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d13)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _))))) eq_refl (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append (CS c1) k (appendHvl H0 (bind d13)))) eq_refl)))))
      end.
    Fixpoint shift_TmVar__subst_TyVar_0_Decls_comm_ind (d11 : Decls) (k : Hvl) (c1 : (Cutoff TmVar)) (S1 : Ty) {struct d11} :
    ((shift_TmVar_Decls (weakenCutoffTmVar c1 k) (subst_TyVar_Decls (weakenTrace X0 k) S1 d11)) = (subst_TyVar_Decls (weakenTrace X0 k) S1 (shift_TmVar_Decls (weakenCutoffTmVar c1 k) d11))) :=
      match d11 return ((shift_TmVar_Decls (weakenCutoffTmVar c1 k) (subst_TyVar_Decls (weakenTrace X0 k) S1 d11)) = (subst_TyVar_Decls (weakenTrace X0 k) S1 (shift_TmVar_Decls (weakenCutoffTmVar c1 k) d11))) with
        | (DNil) => eq_refl
        | (DCons t7 d12) => (f_equal2 DCons (shift_TmVar__subst_TyVar_0_Tm_comm_ind t7 k c1 S1) (eq_trans (f_equal2 shift_TmVar_Decls eq_refl (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Decls_comm_ind d12 (HS TmVar k) c1 S1) (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end
    with shift_TmVar__subst_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff TmVar)) (S1 : Ty) {struct s0} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c1 k) (subst_TyVar_Tm (weakenTrace X0 k) S1 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) S1 (shift_TmVar_Tm (weakenCutoffTmVar c1 k) s0))) :=
      match s0 return ((shift_TmVar_Tm (weakenCutoffTmVar c1 k) (subst_TyVar_Tm (weakenTrace X0 k) S1 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) S1 (shift_TmVar_Tm (weakenCutoffTmVar c1 k) s0))) with
        | (Var x8) => eq_refl
        | (Abs T5 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Tm_comm_ind t8 (HS TmVar k) c1 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t9 t10) => (f_equal2 App (shift_TmVar__subst_TyVar_0_Tm_comm_ind t9 k c1 S1) (shift_TmVar__subst_TyVar_0_Tm_comm_ind t10 k c1 S1))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Tm_comm_ind t8 (HS TyVar k) c1 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t8 T5) => (f_equal2 TApp (shift_TmVar__subst_TyVar_0_Tm_comm_ind t8 k c1 S1) eq_refl)
        | (Let d13 t8) => (f_equal2 Let (shift_TmVar__subst_TyVar_0_Decls_comm_ind d13 k c1 S1) (eq_trans (f_equal2 shift_TmVar_Tm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TyVar__bind _ _ _) (eq_refl H0)))) (weakenCutoffTmVar_append c1 k (appendHvl H0 (bind d13)))) (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d13))) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d13))) c1 S1) (f_equal3 subst_TyVar_Tm (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d13)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _))))) eq_refl (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append c1 k (appendHvl H0 (bind d13)))) eq_refl)))))
      end.
    Fixpoint shift_TyVar__subst_TmVar_0_Decls_comm_ind (d11 : Decls) (k : Hvl) (c1 : (Cutoff TyVar)) (s0 : Tm) {struct d11} :
    ((shift_TyVar_Decls (weakenCutoffTyVar c1 k) (subst_TmVar_Decls (weakenTrace X0 k) s0 d11)) = (subst_TmVar_Decls (weakenTrace X0 k) (shift_TyVar_Tm c1 s0) (shift_TyVar_Decls (weakenCutoffTyVar c1 k) d11))) :=
      match d11 return ((shift_TyVar_Decls (weakenCutoffTyVar c1 k) (subst_TmVar_Decls (weakenTrace X0 k) s0 d11)) = (subst_TmVar_Decls (weakenTrace X0 k) (shift_TyVar_Tm c1 s0) (shift_TyVar_Decls (weakenCutoffTyVar c1 k) d11))) with
        | (DNil) => eq_refl
        | (DCons t7 d12) => (f_equal2 DCons (shift_TyVar__subst_TmVar_0_Tm_comm_ind t7 k c1 s0) (eq_trans (f_equal2 shift_TyVar_Decls eq_refl (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Decls_comm_ind d12 (HS TmVar k) c1 s0) (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end
    with shift_TyVar__subst_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (c1 : (Cutoff TyVar)) (s0 : Tm) {struct s1} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c1 k) (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TyVar_Tm c1 s0) (shift_TyVar_Tm (weakenCutoffTyVar c1 k) s1))) :=
      match s1 return ((shift_TyVar_Tm (weakenCutoffTyVar c1 k) (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TyVar_Tm c1 s0) (shift_TyVar_Tm (weakenCutoffTyVar c1 k) s1))) with
        | (Var x8) => (shift_TyVar_Tm_subst_TmVar_Index0_comm_ind c1 s0 k x8)
        | (Abs T5 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Tm_comm_ind t8 (HS TmVar k) c1 s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t9 t10) => (f_equal2 App (shift_TyVar__subst_TmVar_0_Tm_comm_ind t9 k c1 s0) (shift_TyVar__subst_TmVar_0_Tm_comm_ind t10 k c1 s0))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Tm_comm_ind t8 (HS TyVar k) c1 s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t8 T5) => (f_equal2 TApp (shift_TyVar__subst_TmVar_0_Tm_comm_ind t8 k c1 s0) eq_refl)
        | (Let d13 t8) => (f_equal2 Let (shift_TyVar__subst_TmVar_0_Decls_comm_ind d13 k c1 s0) (eq_trans (f_equal2 shift_TyVar_Tm (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TmVar__bind _ _ _) (eq_refl H0)))) (weakenCutoffTyVar_append c1 k (appendHvl H0 (bind d13)))) (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d13))) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d13))) c1 s0) (f_equal3 subst_TmVar_Tm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d13)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TyVar__bind _ _))))) eq_refl (f_equal2 shift_TyVar_Tm (eq_sym (weakenCutoffTyVar_append c1 k (appendHvl H0 (bind d13)))) eq_refl)))))
      end.
    Fixpoint shift_TyVar__subst_TyVar_0_Decls_comm_ind (d11 : Decls) (k : Hvl) (c1 : (Cutoff TyVar)) (S1 : Ty) {struct d11} :
    ((shift_TyVar_Decls (weakenCutoffTyVar c1 k) (subst_TyVar_Decls (weakenTrace X0 k) S1 d11)) = (subst_TyVar_Decls (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Decls (weakenCutoffTyVar (CS c1) k) d11))) :=
      match d11 return ((shift_TyVar_Decls (weakenCutoffTyVar c1 k) (subst_TyVar_Decls (weakenTrace X0 k) S1 d11)) = (subst_TyVar_Decls (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Decls (weakenCutoffTyVar (CS c1) k) d11))) with
        | (DNil) => eq_refl
        | (DCons t7 d12) => (f_equal2 DCons (shift_TyVar__subst_TyVar_0_Tm_comm_ind t7 k c1 S1) (eq_trans (f_equal2 shift_TyVar_Decls eq_refl (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Decls_comm_ind d12 (HS TmVar k) c1 S1) (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end
    with shift_TyVar__subst_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c1 : (Cutoff TyVar)) (S1 : Ty) {struct s0} :
    ((shift_TyVar_Tm (weakenCutoffTyVar c1 k) (subst_TyVar_Tm (weakenTrace X0 k) S1 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Tm (weakenCutoffTyVar (CS c1) k) s0))) :=
      match s0 return ((shift_TyVar_Tm (weakenCutoffTyVar c1 k) (subst_TyVar_Tm (weakenTrace X0 k) S1 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) (shift_TyVar_Ty c1 S1) (shift_TyVar_Tm (weakenCutoffTyVar (CS c1) k) s0))) with
        | (Var x8) => eq_refl
        | (Abs T5 t8) => (f_equal2 Abs (shift_TyVar__subst_TyVar_0_Ty_comm_ind T5 k c1 S1) (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Tm_comm_ind t8 (HS TmVar k) c1 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t9 t10) => (f_equal2 App (shift_TyVar__subst_TyVar_0_Tm_comm_ind t9 k c1 S1) (shift_TyVar__subst_TyVar_0_Tm_comm_ind t10 k c1 S1))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Tm_comm_ind t8 (HS TyVar k) c1 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t8 T5) => (f_equal2 TApp (shift_TyVar__subst_TyVar_0_Tm_comm_ind t8 k c1 S1) (shift_TyVar__subst_TyVar_0_Ty_comm_ind T5 k c1 S1))
        | (Let d13 t8) => (f_equal2 Let (shift_TyVar__subst_TyVar_0_Decls_comm_ind d13 k c1 S1) (eq_trans (f_equal2 shift_TyVar_Tm (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TyVar__bind _ _ _) (eq_refl H0)))) (weakenCutoffTyVar_append c1 k (appendHvl H0 (bind d13)))) (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d13))) eq_refl eq_refl)) (eq_trans (shift_TyVar__subst_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d13))) c1 S1) (f_equal3 subst_TyVar_Tm (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d13)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TyVar__bind _ _))))) eq_refl (f_equal2 shift_TyVar_Tm (eq_sym (weakenCutoffTyVar_append (CS c1) k (appendHvl H0 (bind d13)))) eq_refl)))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shift_TyVar_Ty_subst_TyVar_Ty0_comm (S2 : Ty) : (forall (c1 : (Cutoff TyVar)) (S1 : Ty) ,
      ((shift_TyVar_Ty c1 (subst_TyVar_Ty X0 S1 S2)) = (subst_TyVar_Ty X0 (shift_TyVar_Ty c1 S1) (shift_TyVar_Ty (CS c1) S2)))) := (shift_TyVar__subst_TyVar_0_Ty_comm_ind S2 H0).
    Definition shift_TmVar_Decls_subst_TmVar_Decls0_comm (d11 : Decls) : (forall (c1 : (Cutoff TmVar)) (s0 : Tm) ,
      ((shift_TmVar_Decls c1 (subst_TmVar_Decls X0 s0 d11)) = (subst_TmVar_Decls X0 (shift_TmVar_Tm c1 s0) (shift_TmVar_Decls (CS c1) d11)))) := (shift_TmVar__subst_TmVar_0_Decls_comm_ind d11 H0).
    Definition shift_TmVar_Tm_subst_TmVar_Tm0_comm (s1 : Tm) : (forall (c1 : (Cutoff TmVar)) (s0 : Tm) ,
      ((shift_TmVar_Tm c1 (subst_TmVar_Tm X0 s0 s1)) = (subst_TmVar_Tm X0 (shift_TmVar_Tm c1 s0) (shift_TmVar_Tm (CS c1) s1)))) := (shift_TmVar__subst_TmVar_0_Tm_comm_ind s1 H0).
    Definition shift_TmVar_Decls_subst_TyVar_Decls0_comm (d11 : Decls) : (forall (c1 : (Cutoff TmVar)) (S1 : Ty) ,
      ((shift_TmVar_Decls c1 (subst_TyVar_Decls X0 S1 d11)) = (subst_TyVar_Decls X0 S1 (shift_TmVar_Decls c1 d11)))) := (shift_TmVar__subst_TyVar_0_Decls_comm_ind d11 H0).
    Definition shift_TmVar_Tm_subst_TyVar_Tm0_comm (s0 : Tm) : (forall (c1 : (Cutoff TmVar)) (S1 : Ty) ,
      ((shift_TmVar_Tm c1 (subst_TyVar_Tm X0 S1 s0)) = (subst_TyVar_Tm X0 S1 (shift_TmVar_Tm c1 s0)))) := (shift_TmVar__subst_TyVar_0_Tm_comm_ind s0 H0).
    Definition shift_TyVar_Decls_subst_TmVar_Decls0_comm (d11 : Decls) : (forall (c1 : (Cutoff TyVar)) (s0 : Tm) ,
      ((shift_TyVar_Decls c1 (subst_TmVar_Decls X0 s0 d11)) = (subst_TmVar_Decls X0 (shift_TyVar_Tm c1 s0) (shift_TyVar_Decls c1 d11)))) := (shift_TyVar__subst_TmVar_0_Decls_comm_ind d11 H0).
    Definition shift_TyVar_Tm_subst_TmVar_Tm0_comm (s1 : Tm) : (forall (c1 : (Cutoff TyVar)) (s0 : Tm) ,
      ((shift_TyVar_Tm c1 (subst_TmVar_Tm X0 s0 s1)) = (subst_TmVar_Tm X0 (shift_TyVar_Tm c1 s0) (shift_TyVar_Tm c1 s1)))) := (shift_TyVar__subst_TmVar_0_Tm_comm_ind s1 H0).
    Definition shift_TyVar_Decls_subst_TyVar_Decls0_comm (d11 : Decls) : (forall (c1 : (Cutoff TyVar)) (S1 : Ty) ,
      ((shift_TyVar_Decls c1 (subst_TyVar_Decls X0 S1 d11)) = (subst_TyVar_Decls X0 (shift_TyVar_Ty c1 S1) (shift_TyVar_Decls (CS c1) d11)))) := (shift_TyVar__subst_TyVar_0_Decls_comm_ind d11 H0).
    Definition shift_TyVar_Tm_subst_TyVar_Tm0_comm (s0 : Tm) : (forall (c1 : (Cutoff TyVar)) (S1 : Ty) ,
      ((shift_TyVar_Tm c1 (subst_TyVar_Tm X0 S1 s0)) = (subst_TyVar_Tm X0 (shift_TyVar_Ty c1 S1) (shift_TyVar_Tm (CS c1) s0)))) := (shift_TyVar__subst_TyVar_0_Tm_comm_ind s0 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma subst_TmVar_Index_shift_TmVar_Tm0_comm_ind (d11 : (Trace TmVar)) (s0 : Tm) :
      (forall (k : Hvl) (x7 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TmVar d11) k) s0 (shift_TmVar_Index (weakenCutoffTmVar C0 k) x7)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Index (weakenTrace d11 k) s0 x7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Index_shift_TyVar_Tm0_comm_ind (d11 : (Trace TmVar)) (s0 : Tm) :
      (forall (k : Hvl) (x7 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TyVar d11) k) s0 x7) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Index (weakenTrace d11 k) s0 x7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Index_shift_TmVar_Ty0_comm_ind (d11 : (Trace TyVar)) (S1 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace (XS TmVar d11) k) S1 X7) = (subst_TyVar_Index (weakenTrace d11 k) S1 X7))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Index_shift_TyVar_Ty0_comm_ind (d11 : (Trace TyVar)) (S1 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((subst_TyVar_Index (weakenTrace (XS TyVar d11) k) S1 (shift_TyVar_Index (weakenCutoffTyVar C0 k) X7)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Index (weakenTrace d11 k) S1 X7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_TyVar__shift_TyVar_0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) {struct S2} :
    ((subst_TyVar_Ty (weakenTrace (XS TyVar d11) k) S1 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S2)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Ty (weakenTrace d11 k) S1 S2))) :=
      match S2 return ((subst_TyVar_Ty (weakenTrace (XS TyVar d11) k) S1 (shift_TyVar_Ty (weakenCutoffTyVar C0 k) S2)) = (shift_TyVar_Ty (weakenCutoffTyVar C0 k) (subst_TyVar_Ty (weakenTrace d11 k) S1 S2))) with
        | (TVar X7) => (subst_TyVar_Index_shift_TyVar_Ty0_comm_ind d11 S1 k X7)
        | (TArr T6 T7) => (f_equal2 TArr (subst_TyVar__shift_TyVar_0_Ty_comm_ind T6 k d11 S1) (subst_TyVar__shift_TyVar_0_Ty_comm_ind T7 k d11 S1))
        | (TAll T5) => (f_equal TAll (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TyVar d11) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Ty_comm_ind T5 (HS TyVar k) d11 S1) (f_equal2 shift_TyVar_Ty eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d11 k (HS TyVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__shift_TmVar_0_Decls_comm_ind (d12 : Decls) (k : Hvl) (d11 : (Trace TmVar)) (s0 : Tm) {struct d12} :
    ((subst_TmVar_Decls (weakenTrace (XS TmVar d11) k) s0 (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d12)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (subst_TmVar_Decls (weakenTrace d11 k) s0 d12))) :=
      match d12 return ((subst_TmVar_Decls (weakenTrace (XS TmVar d11) k) s0 (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d12)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (subst_TmVar_Decls (weakenTrace d11 k) s0 d12))) with
        | (DNil) => eq_refl
        | (DCons t7 d13) => (f_equal2 DCons (subst_TmVar__shift_TmVar_0_Tm_comm_ind t7 k d11 s0) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar (XS TmVar d11) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Decls_comm_ind d13 (HS TmVar k) d11 s0) (f_equal2 shift_TmVar_Decls eq_refl (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar d11 k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TmVar__shift_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d11 : (Trace TmVar)) (s0 : Tm) {struct s1} :
    ((subst_TmVar_Tm (weakenTrace (XS TmVar d11) k) s0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s1)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d11 k) s0 s1))) :=
      match s1 return ((subst_TmVar_Tm (weakenTrace (XS TmVar d11) k) s0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s1)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d11 k) s0 s1))) with
        | (Var x8) => (subst_TmVar_Index_shift_TmVar_Tm0_comm_ind d11 s0 k x8)
        | (Abs T5 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TmVar d11) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind t8 (HS TmVar k) d11 s0) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d11 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TmVar__shift_TmVar_0_Tm_comm_ind t9 k d11 s0) (subst_TmVar__shift_TmVar_0_Tm_comm_ind t10 k d11 s0))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TmVar d11) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind t8 (HS TyVar k) d11 s0) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d11 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T5) => (f_equal2 TApp (subst_TmVar__shift_TmVar_0_Tm_comm_ind t8 k d11 s0) eq_refl)
        | (Let d14 t8) => (f_equal2 Let (subst_TmVar__shift_TmVar_0_Decls_comm_ind d14 k d11 s0) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenTrace_append TmVar (XS TmVar d11) k (appendHvl H0 (bind d14)))) eq_refl (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d14))) eq_refl)) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d14))) d11 s0) (f_equal2 shift_TmVar_Tm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d14)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0))))) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d11 k (appendHvl H0 (bind d14)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__shift_TyVar_0_Decls_comm_ind (d12 : Decls) (k : Hvl) (d11 : (Trace TmVar)) (s0 : Tm) {struct d12} :
    ((subst_TmVar_Decls (weakenTrace (XS TyVar d11) k) s0 (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d12)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (subst_TmVar_Decls (weakenTrace d11 k) s0 d12))) :=
      match d12 return ((subst_TmVar_Decls (weakenTrace (XS TyVar d11) k) s0 (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d12)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (subst_TmVar_Decls (weakenTrace d11 k) s0 d12))) with
        | (DNil) => eq_refl
        | (DCons t7 d13) => (f_equal2 DCons (subst_TmVar__shift_TyVar_0_Tm_comm_ind t7 k d11 s0) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar (XS TyVar d11) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Decls_comm_ind d13 (HS TmVar k) d11 s0) (f_equal2 shift_TyVar_Decls eq_refl (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar d11 k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TmVar__shift_TyVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d11 : (Trace TmVar)) (s0 : Tm) {struct s1} :
    ((subst_TmVar_Tm (weakenTrace (XS TyVar d11) k) s0 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s1)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Tm (weakenTrace d11 k) s0 s1))) :=
      match s1 return ((subst_TmVar_Tm (weakenTrace (XS TyVar d11) k) s0 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s1)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TmVar_Tm (weakenTrace d11 k) s0 s1))) with
        | (Var x8) => (subst_TmVar_Index_shift_TyVar_Tm0_comm_ind d11 s0 k x8)
        | (Abs T5 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TyVar d11) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Tm_comm_ind t8 (HS TmVar k) d11 s0) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d11 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TmVar__shift_TyVar_0_Tm_comm_ind t9 k d11 s0) (subst_TmVar__shift_TyVar_0_Tm_comm_ind t10 k d11 s0))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar (XS TyVar d11) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TyVar_0_Tm_comm_ind t8 (HS TyVar k) d11 s0) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d11 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T5) => (f_equal2 TApp (subst_TmVar__shift_TyVar_0_Tm_comm_ind t8 k d11 s0) eq_refl)
        | (Let d14 t8) => (f_equal2 Let (subst_TmVar__shift_TyVar_0_Decls_comm_ind d14 k d11 s0) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TyVar__bind _ _))) (weakenTrace_append TmVar (XS TyVar d11) k (appendHvl H0 (bind d14)))) eq_refl (f_equal2 shift_TyVar_Tm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d14))) eq_refl)) (eq_trans (subst_TmVar__shift_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d14))) d11 s0) (f_equal2 shift_TyVar_Tm (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d14)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0))))) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d11 k (appendHvl H0 (bind d14)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__shift_TmVar_0_Decls_comm_ind (d12 : Decls) (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) {struct d12} :
    ((subst_TyVar_Decls (weakenTrace d11 k) S1 (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d12)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (subst_TyVar_Decls (weakenTrace d11 k) S1 d12))) :=
      match d12 return ((subst_TyVar_Decls (weakenTrace d11 k) S1 (shift_TmVar_Decls (weakenCutoffTmVar C0 k) d12)) = (shift_TmVar_Decls (weakenCutoffTmVar C0 k) (subst_TyVar_Decls (weakenTrace d11 k) S1 d12))) with
        | (DNil) => eq_refl
        | (DCons t7 d13) => (f_equal2 DCons (subst_TyVar__shift_TmVar_0_Tm_comm_ind t7 k d11 S1) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar d11 k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Decls_comm_ind d13 (HS TmVar k) d11 S1) (f_equal2 shift_TmVar_Decls eq_refl (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar d11 k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TyVar__shift_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) {struct s0} :
    ((subst_TyVar_Tm (weakenTrace d11 k) S1 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TyVar_Tm (weakenTrace d11 k) S1 s0))) :=
      match s0 return ((subst_TyVar_Tm (weakenTrace d11 k) S1 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TyVar_Tm (weakenTrace d11 k) S1 s0))) with
        | (Var x8) => eq_refl
        | (Abs T5 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d11 k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Tm_comm_ind t8 (HS TmVar k) d11 S1) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d11 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TyVar__shift_TmVar_0_Tm_comm_ind t9 k d11 S1) (subst_TyVar__shift_TmVar_0_Tm_comm_ind t10 k d11 S1))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d11 k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TmVar_0_Tm_comm_ind t8 (HS TyVar k) d11 S1) (f_equal2 shift_TmVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d11 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T5) => (f_equal2 TApp (subst_TyVar__shift_TmVar_0_Tm_comm_ind t8 k d11 S1) eq_refl)
        | (Let d14 t8) => (f_equal2 Let (subst_TyVar__shift_TmVar_0_Decls_comm_ind d14 k d11 S1) (eq_trans (f_equal3 subst_TyVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenTrace_append TyVar d11 k (appendHvl H0 (bind d14)))) eq_refl (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d14))) eq_refl)) (eq_trans (subst_TyVar__shift_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d14))) d11 S1) (f_equal2 shift_TmVar_Tm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d14)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TyVar__bind _ _ _)) (eq_refl H0))))) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d11 k (appendHvl H0 (bind d14)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__shift_TyVar_0_Decls_comm_ind (d12 : Decls) (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) {struct d12} :
    ((subst_TyVar_Decls (weakenTrace (XS TyVar d11) k) S1 (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d12)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (subst_TyVar_Decls (weakenTrace d11 k) S1 d12))) :=
      match d12 return ((subst_TyVar_Decls (weakenTrace (XS TyVar d11) k) S1 (shift_TyVar_Decls (weakenCutoffTyVar C0 k) d12)) = (shift_TyVar_Decls (weakenCutoffTyVar C0 k) (subst_TyVar_Decls (weakenTrace d11 k) S1 d12))) with
        | (DNil) => eq_refl
        | (DCons t7 d13) => (f_equal2 DCons (subst_TyVar__shift_TyVar_0_Tm_comm_ind t7 k d11 S1) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar (XS TyVar d11) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Decls_comm_ind d13 (HS TmVar k) d11 S1) (f_equal2 shift_TyVar_Decls eq_refl (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar d11 k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TyVar__shift_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) {struct s0} :
    ((subst_TyVar_Tm (weakenTrace (XS TyVar d11) k) S1 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TyVar_Tm (weakenTrace d11 k) S1 s0))) :=
      match s0 return ((subst_TyVar_Tm (weakenTrace (XS TyVar d11) k) S1 (shift_TyVar_Tm (weakenCutoffTyVar C0 k) s0)) = (shift_TyVar_Tm (weakenCutoffTyVar C0 k) (subst_TyVar_Tm (weakenTrace d11 k) S1 s0))) with
        | (Var x8) => eq_refl
        | (Abs T5 t8) => (f_equal2 Abs (subst_TyVar__shift_TyVar_0_Ty_comm_ind T5 k d11 S1) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TyVar d11) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Tm_comm_ind t8 (HS TmVar k) d11 S1) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d11 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TyVar__shift_TyVar_0_Tm_comm_ind t9 k d11 S1) (subst_TyVar__shift_TyVar_0_Tm_comm_ind t10 k d11 S1))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TyVar d11) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__shift_TyVar_0_Tm_comm_ind t8 (HS TyVar k) d11 S1) (f_equal2 shift_TyVar_Tm eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d11 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T5) => (f_equal2 TApp (subst_TyVar__shift_TyVar_0_Tm_comm_ind t8 k d11 S1) (subst_TyVar__shift_TyVar_0_Ty_comm_ind T5 k d11 S1))
        | (Let d14 t8) => (f_equal2 Let (subst_TyVar__shift_TyVar_0_Decls_comm_ind d14 k d11 S1) (eq_trans (f_equal3 subst_TyVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TyVar__bind _ _))) (weakenTrace_append TyVar (XS TyVar d11) k (appendHvl H0 (bind d14)))) eq_refl (f_equal2 shift_TyVar_Tm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d14))) eq_refl)) (eq_trans (subst_TyVar__shift_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d14))) d11 S1) (f_equal2 shift_TyVar_Tm (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind d14)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TyVar__bind _ _ _)) (eq_refl H0))))) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d11 k (appendHvl H0 (bind d14)))) eq_refl eq_refl)))))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition subst_TyVar_Ty_shift_TyVar_Ty0_comm (S2 : Ty) : (forall (d11 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Ty (XS TyVar d11) S1 (shift_TyVar_Ty C0 S2)) = (shift_TyVar_Ty C0 (subst_TyVar_Ty d11 S1 S2)))) := (subst_TyVar__shift_TyVar_0_Ty_comm_ind S2 H0).
    Definition subst_TmVar_Decls_shift_TmVar_Decls0_comm (d12 : Decls) : (forall (d11 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Decls (XS TmVar d11) s0 (shift_TmVar_Decls C0 d12)) = (shift_TmVar_Decls C0 (subst_TmVar_Decls d11 s0 d12)))) := (subst_TmVar__shift_TmVar_0_Decls_comm_ind d12 H0).
    Definition subst_TmVar_Tm_shift_TmVar_Tm0_comm (s1 : Tm) : (forall (d11 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Tm (XS TmVar d11) s0 (shift_TmVar_Tm C0 s1)) = (shift_TmVar_Tm C0 (subst_TmVar_Tm d11 s0 s1)))) := (subst_TmVar__shift_TmVar_0_Tm_comm_ind s1 H0).
    Definition subst_TmVar_Decls_shift_TyVar_Decls0_comm (d12 : Decls) : (forall (d11 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Decls (XS TyVar d11) s0 (shift_TyVar_Decls C0 d12)) = (shift_TyVar_Decls C0 (subst_TmVar_Decls d11 s0 d12)))) := (subst_TmVar__shift_TyVar_0_Decls_comm_ind d12 H0).
    Definition subst_TmVar_Tm_shift_TyVar_Tm0_comm (s1 : Tm) : (forall (d11 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Tm (XS TyVar d11) s0 (shift_TyVar_Tm C0 s1)) = (shift_TyVar_Tm C0 (subst_TmVar_Tm d11 s0 s1)))) := (subst_TmVar__shift_TyVar_0_Tm_comm_ind s1 H0).
    Definition subst_TyVar_Decls_shift_TmVar_Decls0_comm (d12 : Decls) : (forall (d11 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Decls d11 S1 (shift_TmVar_Decls C0 d12)) = (shift_TmVar_Decls C0 (subst_TyVar_Decls d11 S1 d12)))) := (subst_TyVar__shift_TmVar_0_Decls_comm_ind d12 H0).
    Definition subst_TyVar_Tm_shift_TmVar_Tm0_comm (s0 : Tm) : (forall (d11 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Tm d11 S1 (shift_TmVar_Tm C0 s0)) = (shift_TmVar_Tm C0 (subst_TyVar_Tm d11 S1 s0)))) := (subst_TyVar__shift_TmVar_0_Tm_comm_ind s0 H0).
    Definition subst_TyVar_Decls_shift_TyVar_Decls0_comm (d12 : Decls) : (forall (d11 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Decls (XS TyVar d11) S1 (shift_TyVar_Decls C0 d12)) = (shift_TyVar_Decls C0 (subst_TyVar_Decls d11 S1 d12)))) := (subst_TyVar__shift_TyVar_0_Decls_comm_ind d12 H0).
    Definition subst_TyVar_Tm_shift_TyVar_Tm0_comm (s0 : Tm) : (forall (d11 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Tm (XS TyVar d11) S1 (shift_TyVar_Tm C0 s0)) = (shift_TyVar_Tm C0 (subst_TyVar_Tm d11 S1 s0)))) := (subst_TyVar__shift_TyVar_0_Tm_comm_ind s0 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Fixpoint subst_TyVar__TmVar_Ty_ind (S2 : Ty) (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) {struct S2} :
    ((subst_TyVar_Ty (weakenTrace (XS TmVar d11) k) S1 S2) = (subst_TyVar_Ty (weakenTrace d11 k) S1 S2)) :=
      match S2 return ((subst_TyVar_Ty (weakenTrace (XS TmVar d11) k) S1 S2) = (subst_TyVar_Ty (weakenTrace d11 k) S1 S2)) with
        | (TVar X7) => (subst_TyVar_Index_shift_TmVar_Ty0_comm_ind d11 S1 k X7)
        | (TArr T6 T7) => (f_equal2 TArr (subst_TyVar__TmVar_Ty_ind T6 k d11 S1) (subst_TyVar__TmVar_Ty_ind T7 k d11 S1))
        | (TAll T5) => (f_equal TAll (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar (XS TmVar d11) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__TmVar_Ty_ind T5 (HS TyVar k) d11 S1) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar d11 k (HS TyVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint subst_TyVar__TmVar_Decls_ind (d12 : Decls) (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) {struct d12} :
    ((subst_TyVar_Decls (weakenTrace (XS TmVar d11) k) S1 d12) = (subst_TyVar_Decls (weakenTrace d11 k) S1 d12)) :=
      match d12 return ((subst_TyVar_Decls (weakenTrace (XS TmVar d11) k) S1 d12) = (subst_TyVar_Decls (weakenTrace d11 k) S1 d12)) with
        | (DNil) => eq_refl
        | (DCons t7 d13) => (f_equal2 DCons (subst_TyVar__TmVar_Tm_ind t7 k d11 S1) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar (XS TmVar d11) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__TmVar_Decls_ind d13 (HS TmVar k) d11 S1) (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar d11 k (HS TmVar H0))) eq_refl eq_refl))))
      end
    with subst_TyVar__TmVar_Tm_ind (s0 : Tm) (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) {struct s0} :
    ((subst_TyVar_Tm (weakenTrace (XS TmVar d11) k) S1 s0) = (subst_TyVar_Tm (weakenTrace d11 k) S1 s0)) :=
      match s0 return ((subst_TyVar_Tm (weakenTrace (XS TmVar d11) k) S1 s0) = (subst_TyVar_Tm (weakenTrace d11 k) S1 s0)) with
        | (Var x8) => eq_refl
        | (Abs T5 t8) => (f_equal2 Abs (subst_TyVar__TmVar_Ty_ind T5 k d11 S1) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TmVar d11) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__TmVar_Tm_ind t8 (HS TmVar k) d11 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d11 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t9 t10) => (f_equal2 App (subst_TyVar__TmVar_Tm_ind t9 k d11 S1) (subst_TyVar__TmVar_Tm_ind t10 k d11 S1))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TmVar d11) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_TyVar__TmVar_Tm_ind t8 (HS TyVar k) d11 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d11 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t8 T5) => (f_equal2 TApp (subst_TyVar__TmVar_Tm_ind t8 k d11 S1) (subst_TyVar__TmVar_Ty_ind T5 k d11 S1))
        | (Let d14 t8) => (f_equal2 Let (subst_TyVar__TmVar_Decls_ind d14 k d11 S1) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar (XS TmVar d11) k (appendHvl H0 (bind d14))) eq_refl eq_refl) (eq_trans (subst_TyVar__TmVar_Tm_ind t8 (appendHvl k (appendHvl H0 (bind d14))) d11 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d11 k (appendHvl H0 (bind d14)))) eq_refl eq_refl))))
      end.
  End SubstSubordInd.
  Section SubstSubord.
    Definition subst_TyVar_Ty_TmVar (S2 : Ty) : (forall (d11 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Ty (XS TmVar d11) S1 S2) = (subst_TyVar_Ty d11 S1 S2))) := (subst_TyVar__TmVar_Ty_ind S2 H0).
    Definition subst_TyVar_Decls_TmVar (d12 : Decls) : (forall (d11 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Decls (XS TmVar d11) S1 d12) = (subst_TyVar_Decls d11 S1 d12))) := (subst_TyVar__TmVar_Decls_ind d12 H0).
    Definition subst_TyVar_Tm_TmVar (s0 : Tm) : (forall (d11 : (Trace TyVar)) (S1 : Ty) ,
      ((subst_TyVar_Tm (XS TmVar d11) S1 s0) = (subst_TyVar_Tm d11 S1 s0))) := (subst_TyVar__TmVar_Tm_ind s0 H0).
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite subst_TmVar_Decls0_shift_TmVar_Decls0_reflection subst_TyVar_Decls0_shift_TyVar_Decls0_reflection subst_TmVar_Tm0_shift_TmVar_Tm0_reflection subst_TyVar_Tm0_shift_TyVar_Tm0_reflection subst_TyVar_Ty0_shift_TyVar_Ty0_reflection : interaction.
 Hint Rewrite subst_TmVar_Decls0_shift_TmVar_Decls0_reflection subst_TyVar_Decls0_shift_TyVar_Decls0_reflection subst_TmVar_Tm0_shift_TmVar_Tm0_reflection subst_TyVar_Tm0_shift_TyVar_Tm0_reflection subst_TyVar_Ty0_shift_TyVar_Ty0_reflection : reflection.
 Hint Rewrite subst_TmVar_Decls_shift_TmVar_Decls0_comm subst_TmVar_Decls_shift_TyVar_Decls0_comm subst_TyVar_Decls_shift_TmVar_Decls0_comm subst_TyVar_Decls_shift_TyVar_Decls0_comm subst_TmVar_Tm_shift_TmVar_Tm0_comm subst_TmVar_Tm_shift_TyVar_Tm0_comm subst_TyVar_Tm_shift_TmVar_Tm0_comm subst_TyVar_Tm_shift_TyVar_Tm0_comm subst_TyVar_Ty_shift_TyVar_Ty0_comm : interaction.
 Hint Rewrite subst_TmVar_Decls_shift_TmVar_Decls0_comm subst_TmVar_Decls_shift_TyVar_Decls0_comm subst_TyVar_Decls_shift_TmVar_Decls0_comm subst_TyVar_Decls_shift_TyVar_Decls0_comm subst_TmVar_Tm_shift_TmVar_Tm0_comm subst_TmVar_Tm_shift_TyVar_Tm0_comm subst_TyVar_Tm_shift_TmVar_Tm0_comm subst_TyVar_Tm_shift_TyVar_Tm0_comm subst_TyVar_Ty_shift_TyVar_Ty0_comm : subst_shift0.
 Hint Rewrite subst_TyVar_Decls_TmVar subst_TyVar_Tm_TmVar subst_TyVar_Ty_TmVar : interaction.
 Hint Rewrite subst_TyVar_Decls_TmVar subst_TyVar_Tm_TmVar subst_TyVar_Ty_TmVar : subst_shift0.
 Hint Rewrite shift_TmVar_Decls_subst_TmVar_Decls0_comm shift_TmVar_Decls_subst_TyVar_Decls0_comm shift_TyVar_Decls_subst_TmVar_Decls0_comm shift_TyVar_Decls_subst_TyVar_Decls0_comm shift_TmVar_Tm_subst_TmVar_Tm0_comm shift_TmVar_Tm_subst_TyVar_Tm0_comm shift_TyVar_Tm_subst_TmVar_Tm0_comm shift_TyVar_Tm_subst_TyVar_Tm0_comm shift_TyVar_Ty_subst_TyVar_Ty0_comm : interaction.
 Hint Rewrite shift_TmVar_Decls_subst_TmVar_Decls0_comm shift_TmVar_Decls_subst_TyVar_Decls0_comm shift_TyVar_Decls_subst_TmVar_Decls0_comm shift_TyVar_Decls_subst_TyVar_Decls0_comm shift_TmVar_Tm_subst_TmVar_Tm0_comm shift_TmVar_Tm_subst_TyVar_Tm0_comm shift_TyVar_Tm_subst_TmVar_Tm0_comm shift_TyVar_Tm_subst_TyVar_Tm0_comm shift_TyVar_Ty_subst_TyVar_Ty0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma subst_TmVar_Tm_subst_TmVar_Index0_commright_ind (d11 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) :
      (forall (k : Hvl) (x7 : (Index TmVar)) ,
        ((subst_TmVar_Tm (weakenTrace d11 k) s0 (subst_TmVar_Index (weakenTrace X0 k) s1 x7)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d11 s0 s1) (subst_TmVar_Index (weakenTrace (XS TmVar d11) k) s0 x7)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Tm_subst_TmVar_Index0_commright_ind (d11 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) :
      (forall (k : Hvl) (x7 : (Index TmVar)) ,
        ((subst_TyVar_Tm (weakenTrace d11 k) S1 (subst_TmVar_Index (weakenTrace X0 k) s0 x7)) = (subst_TmVar_Index (weakenTrace X0 k) (subst_TyVar_Tm d11 S1 s0) x7))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TyVar_Ty_subst_TyVar_Index0_commright_ind (d11 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((subst_TyVar_Ty (weakenTrace d11 k) S1 (subst_TyVar_Index (weakenTrace X0 k) S2 X7)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d11 S1 S2) (subst_TyVar_Index (weakenTrace (XS TyVar d11) k) S1 X7)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_TmVar_Ty_subst_TyVar_Index0_commleft_ind (d11 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) :
      (forall (k : Hvl) (x7 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace d11 k) s0 x7) = (subst_TyVar_Tm (weakenTrace X0 k) S1 (subst_TmVar_Index (weakenTrace (XS TyVar d11) k) s0 x7)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_TyVar__subst_TyVar_0_Ty_comm_ind (S3 : Ty) (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) {struct S3} :
    ((subst_TyVar_Ty (weakenTrace d11 k) S1 (subst_TyVar_Ty (weakenTrace X0 k) S2 S3)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d11 S1 S2) (subst_TyVar_Ty (weakenTrace (XS TyVar d11) k) S1 S3))) :=
      match S3 return ((subst_TyVar_Ty (weakenTrace d11 k) S1 (subst_TyVar_Ty (weakenTrace X0 k) S2 S3)) = (subst_TyVar_Ty (weakenTrace X0 k) (subst_TyVar_Ty d11 S1 S2) (subst_TyVar_Ty (weakenTrace (XS TyVar d11) k) S1 S3))) with
        | (TVar X7) => (subst_TyVar_Ty_subst_TyVar_Index0_commright_ind d11 S1 S2 k X7)
        | (TArr T6 T7) => (f_equal2 TArr (subst_TyVar__subst_TyVar_0_Ty_comm_ind T6 k d11 S1 S2) (subst_TyVar__subst_TyVar_0_Ty_comm_ind T7 k d11 S1 S2))
        | (TAll T5) => (f_equal TAll (eq_trans (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar d11 k (HS TyVar H0)) eq_refl (f_equal3 subst_TyVar_Ty (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Ty_comm_ind T5 (HS TyVar k) d11 S1 S2) (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TyVar_Ty (eq_sym (weakenTrace_append TyVar (XS TyVar d11) k (HS TyVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__subst_TmVar_0_Decls_comm_ind (d12 : Decls) (k : Hvl) (d11 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) {struct d12} :
    ((subst_TmVar_Decls (weakenTrace d11 k) s0 (subst_TmVar_Decls (weakenTrace X0 k) s1 d12)) = (subst_TmVar_Decls (weakenTrace X0 k) (subst_TmVar_Tm d11 s0 s1) (subst_TmVar_Decls (weakenTrace (XS TmVar d11) k) s0 d12))) :=
      match d12 return ((subst_TmVar_Decls (weakenTrace d11 k) s0 (subst_TmVar_Decls (weakenTrace X0 k) s1 d12)) = (subst_TmVar_Decls (weakenTrace X0 k) (subst_TmVar_Tm d11 s0 s1) (subst_TmVar_Decls (weakenTrace (XS TmVar d11) k) s0 d12))) with
        | (DNil) => eq_refl
        | (DCons t7 d13) => (f_equal2 DCons (subst_TmVar__subst_TmVar_0_Tm_comm_ind t7 k d11 s0 s1) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar d11 k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Decls_comm_ind d13 (HS TmVar k) d11 s0 s1) (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar (XS TmVar d11) k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TmVar__subst_TmVar_0_Tm_comm_ind (s2 : Tm) (k : Hvl) (d11 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) {struct s2} :
    ((subst_TmVar_Tm (weakenTrace d11 k) s0 (subst_TmVar_Tm (weakenTrace X0 k) s1 s2)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d11 s0 s1) (subst_TmVar_Tm (weakenTrace (XS TmVar d11) k) s0 s2))) :=
      match s2 return ((subst_TmVar_Tm (weakenTrace d11 k) s0 (subst_TmVar_Tm (weakenTrace X0 k) s1 s2)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d11 s0 s1) (subst_TmVar_Tm (weakenTrace (XS TmVar d11) k) s0 s2))) with
        | (Var x8) => (subst_TmVar_Tm_subst_TmVar_Index0_commright_ind d11 s0 s1 k x8)
        | (Abs T5 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d11 k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t8 (HS TmVar k) d11 s0 s1) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d11) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TmVar__subst_TmVar_0_Tm_comm_ind t9 k d11 s0 s1) (subst_TmVar__subst_TmVar_0_Tm_comm_ind t10 k d11 s0 s1))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d11 k (HS TyVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t8 (HS TyVar k) d11 s0 s1) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d11) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T5) => (f_equal2 TApp (subst_TmVar__subst_TmVar_0_Tm_comm_ind t8 k d11 s0 s1) eq_refl)
        | (Let d14 t8) => (f_equal2 Let (subst_TmVar__subst_TmVar_0_Decls_comm_ind d14 k d11 s0 s1) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TmVar__bind _ _ _) (eq_refl H0)))) (weakenTrace_append TmVar d11 k (appendHvl H0 (bind d14)))) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d14))) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d14))) d11 s0 s1) (f_equal3 subst_TmVar_Tm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d14)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d11) k (appendHvl H0 (bind d14)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TmVar__subst_TyVar_0_Decls_comm_ind (d12 : Decls) (k : Hvl) (d11 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) {struct d12} :
    ((subst_TmVar_Decls (weakenTrace d11 k) s0 (subst_TyVar_Decls (weakenTrace X0 k) S1 d12)) = (subst_TyVar_Decls (weakenTrace X0 k) S1 (subst_TmVar_Decls (weakenTrace (XS TyVar d11) k) s0 d12))) :=
      match d12 return ((subst_TmVar_Decls (weakenTrace d11 k) s0 (subst_TyVar_Decls (weakenTrace X0 k) S1 d12)) = (subst_TyVar_Decls (weakenTrace X0 k) S1 (subst_TmVar_Decls (weakenTrace (XS TyVar d11) k) s0 d12))) with
        | (DNil) => eq_refl
        | (DCons t7 d13) => (f_equal2 DCons (subst_TmVar__subst_TyVar_0_Tm_comm_ind t7 k d11 s0 S1) (eq_trans (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar d11 k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Decls_comm_ind d13 (HS TmVar k) d11 s0 S1) (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar (XS TyVar d11) k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TmVar__subst_TyVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d11 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) {struct s1} :
    ((subst_TmVar_Tm (weakenTrace d11 k) s0 (subst_TyVar_Tm (weakenTrace X0 k) S1 s1)) = (subst_TyVar_Tm (weakenTrace X0 k) S1 (subst_TmVar_Tm (weakenTrace (XS TyVar d11) k) s0 s1))) :=
      match s1 return ((subst_TmVar_Tm (weakenTrace d11 k) s0 (subst_TyVar_Tm (weakenTrace X0 k) S1 s1)) = (subst_TyVar_Tm (weakenTrace X0 k) S1 (subst_TmVar_Tm (weakenTrace (XS TyVar d11) k) s0 s1))) with
        | (Var x8) => (subst_TmVar_Ty_subst_TyVar_Index0_commleft_ind d11 s0 S1 k x8)
        | (Abs T5 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d11 k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Tm_comm_ind t8 (HS TmVar k) d11 s0 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TyVar d11) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TmVar__subst_TyVar_0_Tm_comm_ind t9 k d11 s0 S1) (subst_TmVar__subst_TyVar_0_Tm_comm_ind t10 k d11 s0 S1))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar d11 k (HS TyVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Tm_comm_ind t8 (HS TyVar k) d11 s0 S1) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TyVar d11) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T5) => (f_equal2 TApp (subst_TmVar__subst_TyVar_0_Tm_comm_ind t8 k d11 s0 S1) eq_refl)
        | (Let d14 t8) => (f_equal2 Let (subst_TmVar__subst_TyVar_0_Decls_comm_ind d14 k d11 s0 S1) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TyVar__bind _ _ _) (eq_refl H0)))) (weakenTrace_append TmVar d11 k (appendHvl H0 (bind d14)))) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d14))) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d14))) d11 s0 S1) (f_equal3 subst_TyVar_Tm (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d14)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TyVar d11) k (appendHvl H0 (bind d14)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__subst_TmVar_0_Decls_comm_ind (d12 : Decls) (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) {struct d12} :
    ((subst_TyVar_Decls (weakenTrace d11 k) S1 (subst_TmVar_Decls (weakenTrace X0 k) s0 d12)) = (subst_TmVar_Decls (weakenTrace X0 k) (subst_TyVar_Tm d11 S1 s0) (subst_TyVar_Decls (weakenTrace d11 k) S1 d12))) :=
      match d12 return ((subst_TyVar_Decls (weakenTrace d11 k) S1 (subst_TmVar_Decls (weakenTrace X0 k) s0 d12)) = (subst_TmVar_Decls (weakenTrace X0 k) (subst_TyVar_Tm d11 S1 s0) (subst_TyVar_Decls (weakenTrace d11 k) S1 d12))) with
        | (DNil) => eq_refl
        | (DCons t7 d13) => (f_equal2 DCons (subst_TyVar__subst_TmVar_0_Tm_comm_ind t7 k d11 S1 s0) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar d11 k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Decls (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Decls_comm_ind d13 (HS TmVar k) d11 S1 s0) (f_equal3 subst_TmVar_Decls (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar d11 k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TyVar__subst_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) {struct s1} :
    ((subst_TyVar_Tm (weakenTrace d11 k) S1 (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TyVar_Tm d11 S1 s0) (subst_TyVar_Tm (weakenTrace d11 k) S1 s1))) :=
      match s1 return ((subst_TyVar_Tm (weakenTrace d11 k) S1 (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TyVar_Tm d11 S1 s0) (subst_TyVar_Tm (weakenTrace d11 k) S1 s1))) with
        | (Var x8) => (subst_TyVar_Tm_subst_TmVar_Index0_commright_ind d11 S1 s0 k x8)
        | (Abs T5 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d11 k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Tm_comm_ind t8 (HS TmVar k) d11 S1 s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d11 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TyVar__subst_TmVar_0_Tm_comm_ind t9 k d11 S1 s0) (subst_TyVar__subst_TmVar_0_Tm_comm_ind t10 k d11 S1 s0))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d11 k (HS TyVar H0)) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Tm_comm_ind t8 (HS TyVar k) d11 S1 s0) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d11 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T5) => (f_equal2 TApp (subst_TyVar__subst_TmVar_0_Tm_comm_ind t8 k d11 S1 s0) eq_refl)
        | (Let d14 t8) => (f_equal2 Let (subst_TyVar__subst_TmVar_0_Decls_comm_ind d14 k d11 S1 s0) (eq_trans (f_equal3 subst_TyVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TmVar__bind _ _ _) (eq_refl H0)))) (weakenTrace_append TyVar d11 k (appendHvl H0 (bind d14)))) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d14))) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TmVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d14))) d11 S1 s0) (f_equal3 subst_TmVar_Tm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d14)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TyVar__bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar d11 k (appendHvl H0 (bind d14)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_TyVar__subst_TyVar_0_Decls_comm_ind (d12 : Decls) (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) {struct d12} :
    ((subst_TyVar_Decls (weakenTrace d11 k) S1 (subst_TyVar_Decls (weakenTrace X0 k) S2 d12)) = (subst_TyVar_Decls (weakenTrace X0 k) (subst_TyVar_Ty d11 S1 S2) (subst_TyVar_Decls (weakenTrace (XS TyVar d11) k) S1 d12))) :=
      match d12 return ((subst_TyVar_Decls (weakenTrace d11 k) S1 (subst_TyVar_Decls (weakenTrace X0 k) S2 d12)) = (subst_TyVar_Decls (weakenTrace X0 k) (subst_TyVar_Ty d11 S1 S2) (subst_TyVar_Decls (weakenTrace (XS TyVar d11) k) S1 d12))) with
        | (DNil) => eq_refl
        | (DCons t7 d13) => (f_equal2 DCons (subst_TyVar__subst_TyVar_0_Tm_comm_ind t7 k d11 S1 S2) (eq_trans (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar d11 k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Decls (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Decls_comm_ind d13 (HS TmVar k) d11 S1 S2) (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Decls (eq_sym (weakenTrace_append TyVar (XS TyVar d11) k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TyVar__subst_TyVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) {struct s0} :
    ((subst_TyVar_Tm (weakenTrace d11 k) S1 (subst_TyVar_Tm (weakenTrace X0 k) S2 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TyVar_Ty d11 S1 S2) (subst_TyVar_Tm (weakenTrace (XS TyVar d11) k) S1 s0))) :=
      match s0 return ((subst_TyVar_Tm (weakenTrace d11 k) S1 (subst_TyVar_Tm (weakenTrace X0 k) S2 s0)) = (subst_TyVar_Tm (weakenTrace X0 k) (subst_TyVar_Ty d11 S1 S2) (subst_TyVar_Tm (weakenTrace (XS TyVar d11) k) S1 s0))) with
        | (Var x8) => eq_refl
        | (Abs T5 t8) => (f_equal2 Abs (subst_TyVar__subst_TyVar_0_Ty_comm_ind T5 k d11 S1 S2) (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d11 k (HS TmVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Tm_comm_ind t8 (HS TmVar k) d11 S1 S2) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TyVar d11) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_TyVar__subst_TyVar_0_Tm_comm_ind t9 k d11 S1 S2) (subst_TyVar__subst_TyVar_0_Tm_comm_ind t10 k d11 S1 S2))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar d11 k (HS TyVar H0)) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Tm_comm_ind t8 (HS TyVar k) d11 S1 S2) (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TyVar d11) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T5) => (f_equal2 TApp (subst_TyVar__subst_TyVar_0_Tm_comm_ind t8 k d11 S1 S2) (subst_TyVar__subst_TyVar_0_Ty_comm_ind T5 k d11 S1 S2))
        | (Let d14 t8) => (f_equal2 Let (subst_TyVar__subst_TyVar_0_Decls_comm_ind d14 k d11 S1 S2) (eq_trans (f_equal3 subst_TyVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TyVar__bind _ _ _) (eq_refl H0)))) (weakenTrace_append TyVar d11 k (appendHvl H0 (bind d14)))) eq_refl (f_equal3 subst_TyVar_Tm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d14))) eq_refl eq_refl)) (eq_trans (subst_TyVar__subst_TyVar_0_Tm_comm_ind t8 (appendHvl k (appendHvl H0 (bind d14))) d11 S1 S2) (f_equal3 subst_TyVar_Tm (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind d14)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TyVar__bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 subst_TyVar_Tm (eq_sym (weakenTrace_append TyVar (XS TyVar d11) k (appendHvl H0 (bind d14)))) eq_refl eq_refl)))))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition subst_TyVar_Ty_subst_TyVar_Ty0_comm (S3 : Ty) : (forall (d11 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) ,
      ((subst_TyVar_Ty d11 S1 (subst_TyVar_Ty X0 S2 S3)) = (subst_TyVar_Ty X0 (subst_TyVar_Ty d11 S1 S2) (subst_TyVar_Ty (XS TyVar d11) S1 S3)))) := (subst_TyVar__subst_TyVar_0_Ty_comm_ind S3 H0).
    Definition subst_TmVar_Decls_subst_TmVar_Decls0_comm (d12 : Decls) : (forall (d11 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) ,
      ((subst_TmVar_Decls d11 s0 (subst_TmVar_Decls X0 s1 d12)) = (subst_TmVar_Decls X0 (subst_TmVar_Tm d11 s0 s1) (subst_TmVar_Decls (XS TmVar d11) s0 d12)))) := (subst_TmVar__subst_TmVar_0_Decls_comm_ind d12 H0).
    Definition subst_TmVar_Tm_subst_TmVar_Tm0_comm (s2 : Tm) : (forall (d11 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) ,
      ((subst_TmVar_Tm d11 s0 (subst_TmVar_Tm X0 s1 s2)) = (subst_TmVar_Tm X0 (subst_TmVar_Tm d11 s0 s1) (subst_TmVar_Tm (XS TmVar d11) s0 s2)))) := (subst_TmVar__subst_TmVar_0_Tm_comm_ind s2 H0).
    Definition subst_TmVar_Decls_subst_TyVar_Decls0_comm (d12 : Decls) : (forall (d11 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) ,
      ((subst_TmVar_Decls d11 s0 (subst_TyVar_Decls X0 S1 d12)) = (subst_TyVar_Decls X0 S1 (subst_TmVar_Decls (XS TyVar d11) s0 d12)))) := (subst_TmVar__subst_TyVar_0_Decls_comm_ind d12 H0).
    Definition subst_TmVar_Tm_subst_TyVar_Tm0_comm (s1 : Tm) : (forall (d11 : (Trace TmVar)) (s0 : Tm) (S1 : Ty) ,
      ((subst_TmVar_Tm d11 s0 (subst_TyVar_Tm X0 S1 s1)) = (subst_TyVar_Tm X0 S1 (subst_TmVar_Tm (XS TyVar d11) s0 s1)))) := (subst_TmVar__subst_TyVar_0_Tm_comm_ind s1 H0).
    Definition subst_TyVar_Decls_subst_TmVar_Decls0_comm (d12 : Decls) : (forall (d11 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) ,
      ((subst_TyVar_Decls d11 S1 (subst_TmVar_Decls X0 s0 d12)) = (subst_TmVar_Decls X0 (subst_TyVar_Tm d11 S1 s0) (subst_TyVar_Decls d11 S1 d12)))) := (subst_TyVar__subst_TmVar_0_Decls_comm_ind d12 H0).
    Definition subst_TyVar_Tm_subst_TmVar_Tm0_comm (s1 : Tm) : (forall (d11 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) ,
      ((subst_TyVar_Tm d11 S1 (subst_TmVar_Tm X0 s0 s1)) = (subst_TmVar_Tm X0 (subst_TyVar_Tm d11 S1 s0) (subst_TyVar_Tm d11 S1 s1)))) := (subst_TyVar__subst_TmVar_0_Tm_comm_ind s1 H0).
    Definition subst_TyVar_Decls_subst_TyVar_Decls0_comm (d12 : Decls) : (forall (d11 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) ,
      ((subst_TyVar_Decls d11 S1 (subst_TyVar_Decls X0 S2 d12)) = (subst_TyVar_Decls X0 (subst_TyVar_Ty d11 S1 S2) (subst_TyVar_Decls (XS TyVar d11) S1 d12)))) := (subst_TyVar__subst_TyVar_0_Decls_comm_ind d12 H0).
    Definition subst_TyVar_Tm_subst_TyVar_Tm0_comm (s0 : Tm) : (forall (d11 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) ,
      ((subst_TyVar_Tm d11 S1 (subst_TyVar_Tm X0 S2 s0)) = (subst_TyVar_Tm X0 (subst_TyVar_Ty d11 S1 S2) (subst_TyVar_Tm (XS TyVar d11) S1 s0)))) := (subst_TyVar__subst_TyVar_0_Tm_comm_ind s0 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_subst_TyVar_Ty  :
      (forall (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) ,
        ((weakenTy (subst_TyVar_Ty d11 S1 S2) k) = (subst_TyVar_Ty (weakenTrace d11 k) S1 (weakenTy S2 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenDecls_subst_TmVar_Decls  :
      (forall (k : Hvl) (d11 : (Trace TmVar)) (s0 : Tm) (d12 : Decls) ,
        ((weakenDecls (subst_TmVar_Decls d11 s0 d12) k) = (subst_TmVar_Decls (weakenTrace d11 k) s0 (weakenDecls d12 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_subst_TmVar_Tm  :
      (forall (k : Hvl) (d11 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) ,
        ((weakenTm (subst_TmVar_Tm d11 s0 s1) k) = (subst_TmVar_Tm (weakenTrace d11 k) s0 (weakenTm s1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenDecls_subst_TyVar_Decls  :
      (forall (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) (d12 : Decls) ,
        ((weakenDecls (subst_TyVar_Decls d11 S1 d12) k) = (subst_TyVar_Decls (weakenTrace d11 k) S1 (weakenDecls d12 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_subst_TyVar_Tm  :
      (forall (k : Hvl) (d11 : (Trace TyVar)) (S1 : Ty) (s0 : Tm) ,
        ((weakenTm (subst_TyVar_Tm d11 S1 s0) k) = (subst_TyVar_Tm (weakenTrace d11 k) S1 (weakenTm s0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite subst_TmVar_Decls_subst_TmVar_Decls0_comm subst_TyVar_Decls_subst_TyVar_Decls0_comm subst_TmVar_Tm_subst_TmVar_Tm0_comm subst_TyVar_Tm_subst_TyVar_Tm0_comm subst_TyVar_Ty_subst_TyVar_Ty0_comm : interaction.
 Hint Rewrite subst_TmVar_Decls_subst_TmVar_Decls0_comm subst_TyVar_Decls_subst_TyVar_Decls0_comm subst_TmVar_Tm_subst_TmVar_Tm0_comm subst_TyVar_Tm_subst_TyVar_Tm0_comm subst_TyVar_Ty_subst_TyVar_Ty0_comm : subst_subst0.
 Hint Rewrite weakenDecls_shift_TmVar_Decls weakenDecls_shift_TyVar_Decls weakenTm_shift_TmVar_Tm weakenTm_shift_TyVar_Tm weakenTy_shift_TyVar_Ty : weaken_shift.
 Hint Rewrite weakenDecls_subst_TmVar_Decls weakenDecls_subst_TyVar_Decls weakenTm_subst_TmVar_Tm weakenTm_subst_TyVar_Tm weakenTy_subst_TyVar_Ty : weaken_subst.
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
        (X7 : (Index TyVar))
        (wfi : (wfindex k X7)) :
        (wfTy k (TVar X7))
    | wfTy_TArr {T5 : Ty}
        (wf : (wfTy k T5)) {T6 : Ty}
        (wf0 : (wfTy k T6)) :
        (wfTy k (TArr T5 T6))
    | wfTy_TAll {T7 : Ty}
        (wf : (wfTy (HS TyVar k) T7)) :
        (wfTy k (TAll T7)).
  Inductive wfDecls (k : Hvl) : Decls -> Prop :=
    | wfDecls_DNil :
        (wfDecls k (DNil))
    | wfDecls_DCons {t7 : Tm}
        (wf : (wfTm k t7)) {d11 : Decls}
        (wf0 : (wfDecls (HS TmVar k) d11))
        : (wfDecls k (DCons t7 d11))
  with wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_Var
        (x7 : (Index TmVar))
        (wfi : (wfindex k x7)) :
        (wfTm k (Var x7))
    | wfTm_Abs {T5 : Ty}
        (wf : (wfTy k T5)) {t7 : Tm}
        (wf0 : (wfTm (HS TmVar k) t7)) :
        (wfTm k (Abs T5 t7))
    | wfTm_App {t8 : Tm}
        (wf : (wfTm k t8)) {t9 : Tm}
        (wf0 : (wfTm k t9)) :
        (wfTm k (App t8 t9))
    | wfTm_TAbs {t10 : Tm}
        (wf : (wfTm (HS TyVar k) t10)) :
        (wfTm k (TAbs t10))
    | wfTm_TApp {t11 : Tm}
        (wf : (wfTm k t11)) {T6 : Ty}
        (wf0 : (wfTy k T6)) :
        (wfTm k (TApp t11 T6))
    | wfTm_Let {d11 : Decls}
        (wf : (wfDecls k d11))
        {t12 : Tm}
        (wf0 : (wfTm (appendHvl k (appendHvl H0 (bind d11))) t12))
        : (wfTm k (Let d11 t12)).
  Definition inversion_wfTy_TVar_1 (k : Hvl) (X : (Index TyVar)) (H18 : (wfTy k (TVar X))) : (wfindex k X) := match H18 in (wfTy _ S1) return match S1 return Prop with
    | (TVar X) => (wfindex k X)
    | _ => True
  end with
    | (wfTy_TVar X H1) => H1
    | _ => I
  end.
  Definition inversion_wfTy_TArr_0 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H19 : (wfTy k0 (TArr T1 T2))) : (wfTy k0 T1) := match H19 in (wfTy _ S2) return match S2 return Prop with
    | (TArr T1 T2) => (wfTy k0 T1)
    | _ => True
  end with
    | (wfTy_TArr T1 H2 T2 H3) => H2
    | _ => I
  end.
  Definition inversion_wfTy_TArr_1 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H19 : (wfTy k0 (TArr T1 T2))) : (wfTy k0 T2) := match H19 in (wfTy _ S2) return match S2 return Prop with
    | (TArr T1 T2) => (wfTy k0 T2)
    | _ => True
  end with
    | (wfTy_TArr T1 H2 T2 H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_TAll_1 (k1 : Hvl) (T : Ty) (H20 : (wfTy k1 (TAll T))) : (wfTy (HS TyVar k1) T) := match H20 in (wfTy _ S3) return match S3 return Prop with
    | (TAll T) => (wfTy (HS TyVar k1) T)
    | _ => True
  end with
    | (wfTy_TAll T H4) => H4
    | _ => I
  end.
  Definition inversion_wfDecls_DCons_1 (k3 : Hvl) (t : Tm) (d : Decls) (H22 : (wfDecls k3 (DCons t d))) : (wfTm k3 t) := match H22 in (wfDecls _ d12) return match d12 return Prop with
    | (DCons t d) => (wfTm k3 t)
    | _ => True
  end with
    | (wfDecls_DCons t H5 d H6) => H5
    | _ => I
  end.
  Definition inversion_wfDecls_DCons_2 (k3 : Hvl) (t : Tm) (d : Decls) (H22 : (wfDecls k3 (DCons t d))) : (wfDecls (HS TmVar k3) d) := match H22 in (wfDecls _ d12) return match d12 return Prop with
    | (DCons t d) => (wfDecls (HS TmVar k3) d)
    | _ => True
  end with
    | (wfDecls_DCons t H5 d H6) => H6
    | _ => I
  end.
  Definition inversion_wfTm_Var_1 (k4 : Hvl) (x : (Index TmVar)) (H23 : (wfTm k4 (Var x))) : (wfindex k4 x) := match H23 in (wfTm _ s0) return match s0 return Prop with
    | (Var x) => (wfindex k4 x)
    | _ => True
  end with
    | (wfTm_Var x H7) => H7
    | _ => I
  end.
  Definition inversion_wfTm_Abs_1 (k5 : Hvl) (T : Ty) (t : Tm) (H24 : (wfTm k5 (Abs T t))) : (wfTy k5 T) := match H24 in (wfTm _ s1) return match s1 return Prop with
    | (Abs T t) => (wfTy k5 T)
    | _ => True
  end with
    | (wfTm_Abs T H8 t H9) => H8
    | _ => I
  end.
  Definition inversion_wfTm_Abs_2 (k5 : Hvl) (T : Ty) (t : Tm) (H24 : (wfTm k5 (Abs T t))) : (wfTm (HS TmVar k5) t) := match H24 in (wfTm _ s1) return match s1 return Prop with
    | (Abs T t) => (wfTm (HS TmVar k5) t)
    | _ => True
  end with
    | (wfTm_Abs T H8 t H9) => H9
    | _ => I
  end.
  Definition inversion_wfTm_App_0 (k6 : Hvl) (t1 : Tm) (t2 : Tm) (H25 : (wfTm k6 (App t1 t2))) : (wfTm k6 t1) := match H25 in (wfTm _ s2) return match s2 return Prop with
    | (App t1 t2) => (wfTm k6 t1)
    | _ => True
  end with
    | (wfTm_App t1 H10 t2 H11) => H10
    | _ => I
  end.
  Definition inversion_wfTm_App_1 (k6 : Hvl) (t1 : Tm) (t2 : Tm) (H25 : (wfTm k6 (App t1 t2))) : (wfTm k6 t2) := match H25 in (wfTm _ s2) return match s2 return Prop with
    | (App t1 t2) => (wfTm k6 t2)
    | _ => True
  end with
    | (wfTm_App t1 H10 t2 H11) => H11
    | _ => I
  end.
  Definition inversion_wfTm_TAbs_1 (k7 : Hvl) (t : Tm) (H26 : (wfTm k7 (TAbs t))) : (wfTm (HS TyVar k7) t) := match H26 in (wfTm _ s3) return match s3 return Prop with
    | (TAbs t) => (wfTm (HS TyVar k7) t)
    | _ => True
  end with
    | (wfTm_TAbs t H12) => H12
    | _ => I
  end.
  Definition inversion_wfTm_TApp_0 (k8 : Hvl) (t : Tm) (T : Ty) (H27 : (wfTm k8 (TApp t T))) : (wfTm k8 t) := match H27 in (wfTm _ s4) return match s4 return Prop with
    | (TApp t T) => (wfTm k8 t)
    | _ => True
  end with
    | (wfTm_TApp t H13 T H14) => H13
    | _ => I
  end.
  Definition inversion_wfTm_TApp_1 (k8 : Hvl) (t : Tm) (T : Ty) (H27 : (wfTm k8 (TApp t T))) : (wfTy k8 T) := match H27 in (wfTm _ s4) return match s4 return Prop with
    | (TApp t T) => (wfTy k8 T)
    | _ => True
  end with
    | (wfTm_TApp t H13 T H14) => H14
    | _ => I
  end.
  Definition inversion_wfTm_Let_0 (k9 : Hvl) (d : Decls) (t : Tm) (H28 : (wfTm k9 (Let d t))) : (wfDecls k9 d) := match H28 in (wfTm _ s5) return match s5 return Prop with
    | (Let d t) => (wfDecls k9 d)
    | _ => True
  end with
    | (wfTm_Let d H15 t H16) => H15
    | _ => I
  end.
  Definition inversion_wfTm_Let_1 (k9 : Hvl) (d : Decls) (t : Tm) (H28 : (wfTm k9 (Let d t))) : (wfTm (appendHvl k9 (appendHvl H0 (bind d))) t) := match H28 in (wfTm _ s5) return match s5 return Prop with
    | (Let d t) => (wfTm (appendHvl k9 (appendHvl H0 (bind d))) t)
    | _ => True
  end with
    | (wfTm_Let d H15 t H16) => H16
    | _ => I
  end.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfDecls := Induction for wfDecls Sort Prop
  with ind_wfTm := Induction for wfTm Sort Prop.
  Combined Scheme ind_wfDecls_Tm from ind_wfDecls, ind_wfTm.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_TmVar : (forall (c1 : (Cutoff TmVar)) (k10 : Hvl) (k11 : Hvl) ,
    Prop) :=
    | shifthvl_TmVar_here
        (k10 : Hvl) :
        (shifthvl_TmVar C0 k10 (HS TmVar k10))
    | shifthvl_TmVar_there_TmVar
        (c1 : (Cutoff TmVar))
        (k10 : Hvl) (k11 : Hvl) :
        (shifthvl_TmVar c1 k10 k11) -> (shifthvl_TmVar (CS c1) (HS TmVar k10) (HS TmVar k11))
    | shifthvl_TmVar_there_TyVar
        (c1 : (Cutoff TmVar))
        (k10 : Hvl) (k11 : Hvl) :
        (shifthvl_TmVar c1 k10 k11) -> (shifthvl_TmVar c1 (HS TyVar k10) (HS TyVar k11)).
  Inductive shifthvl_TyVar : (forall (c1 : (Cutoff TyVar)) (k10 : Hvl) (k11 : Hvl) ,
    Prop) :=
    | shifthvl_TyVar_here
        (k10 : Hvl) :
        (shifthvl_TyVar C0 k10 (HS TyVar k10))
    | shifthvl_TyVar_there_TmVar
        (c1 : (Cutoff TyVar))
        (k10 : Hvl) (k11 : Hvl) :
        (shifthvl_TyVar c1 k10 k11) -> (shifthvl_TyVar c1 (HS TmVar k10) (HS TmVar k11))
    | shifthvl_TyVar_there_TyVar
        (c1 : (Cutoff TyVar))
        (k10 : Hvl) (k11 : Hvl) :
        (shifthvl_TyVar c1 k10 k11) -> (shifthvl_TyVar (CS c1) (HS TyVar k10) (HS TyVar k11)).
  Lemma weaken_shifthvl_TmVar  :
    (forall (k10 : Hvl) {c1 : (Cutoff TmVar)} {k11 : Hvl} {k12 : Hvl} ,
      (shifthvl_TmVar c1 k11 k12) -> (shifthvl_TmVar (weakenCutoffTmVar c1 k10) (appendHvl k11 k10) (appendHvl k12 k10))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_TyVar  :
    (forall (k10 : Hvl) {c1 : (Cutoff TyVar)} {k11 : Hvl} {k12 : Hvl} ,
      (shifthvl_TyVar c1 k11 k12) -> (shifthvl_TyVar (weakenCutoffTyVar c1 k10) (appendHvl k11 k10) (appendHvl k12 k10))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_TmVar__wfindex_TmVar  :
    (forall (c1 : (Cutoff TmVar)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_TmVar c1 k10 k11)) (x7 : (Index TmVar)) ,
      (wfindex k10 x7) -> (wfindex k11 (shift_TmVar_Index c1 x7))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TmVar__wfindex_TyVar  :
    (forall (c1 : (Cutoff TmVar)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_TmVar c1 k10 k11)) (X7 : (Index TyVar)) ,
      (wfindex k10 X7) -> (wfindex k11 X7)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TyVar__wfindex_TmVar  :
    (forall (c1 : (Cutoff TyVar)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_TyVar c1 k10 k11)) (x7 : (Index TmVar)) ,
      (wfindex k10 x7) -> (wfindex k11 x7)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_TyVar__wfindex_TyVar  :
    (forall (c1 : (Cutoff TyVar)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_TyVar c1 k10 k11)) (X7 : (Index TyVar)) ,
      (wfindex k10 X7) -> (wfindex k11 (shift_TyVar_Index c1 X7))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_TmVar__wfTy : (forall (k10 : Hvl) ,
    (forall (S4 : Ty) (wf : (wfTy k10 S4)) ,
      (forall (c1 : (Cutoff TmVar)) (k11 : Hvl) ,
        (shifthvl_TmVar c1 k10 k11) -> (wfTy k11 S4)))) := (ind_wfTy (fun (k10 : Hvl) (S4 : Ty) (wf : (wfTy k10 S4)) =>
    (forall (c1 : (Cutoff TmVar)) (k11 : Hvl) ,
      (shifthvl_TmVar c1 k10 k11) -> (wfTy k11 S4))) (fun (k10 : Hvl) (X7 : (Index TyVar)) (wfi : (wfindex k10 X7)) (c1 : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c1 k10 k11)) =>
    (wfTy_TVar k11 _ (shift_TmVar__wfindex_TyVar c1 k10 k11 ins X7 wfi))) (fun (k10 : Hvl) (T1 : Ty) (wf : (wfTy k10 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k10 T2)) IHT2 (c1 : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c1 k10 k11)) =>
    (wfTy_TArr k11 (IHT1 c1 k11 (weaken_shifthvl_TmVar H0 ins)) (IHT2 c1 k11 (weaken_shifthvl_TmVar H0 ins)))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy (HS TyVar k10) T)) IHT (c1 : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c1 k10 k11)) =>
    (wfTy_TAll k11 (IHT c1 (HS TyVar k11) (weaken_shifthvl_TmVar (HS TyVar H0) ins))))).
  Definition shift_TyVar__wfTy : (forall (k10 : Hvl) ,
    (forall (S4 : Ty) (wf : (wfTy k10 S4)) ,
      (forall (c1 : (Cutoff TyVar)) (k11 : Hvl) ,
        (shifthvl_TyVar c1 k10 k11) -> (wfTy k11 (shift_TyVar_Ty c1 S4))))) := (ind_wfTy (fun (k10 : Hvl) (S4 : Ty) (wf : (wfTy k10 S4)) =>
    (forall (c1 : (Cutoff TyVar)) (k11 : Hvl) ,
      (shifthvl_TyVar c1 k10 k11) -> (wfTy k11 (shift_TyVar_Ty c1 S4)))) (fun (k10 : Hvl) (X7 : (Index TyVar)) (wfi : (wfindex k10 X7)) (c1 : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c1 k10 k11)) =>
    (wfTy_TVar k11 _ (shift_TyVar__wfindex_TyVar c1 k10 k11 ins X7 wfi))) (fun (k10 : Hvl) (T1 : Ty) (wf : (wfTy k10 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k10 T2)) IHT2 (c1 : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c1 k10 k11)) =>
    (wfTy_TArr k11 (IHT1 c1 k11 (weaken_shifthvl_TyVar H0 ins)) (IHT2 c1 k11 (weaken_shifthvl_TyVar H0 ins)))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy (HS TyVar k10) T)) IHT (c1 : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c1 k10 k11)) =>
    (wfTy_TAll k11 (IHT (CS c1) (HS TyVar k11) (weaken_shifthvl_TyVar (HS TyVar H0) ins))))).
  Definition shift_TmVar__wfDecls_Tm : (forall (k10 : Hvl) ,
    (forall (d13 : Decls) (wf : (wfDecls k10 d13)) ,
      (forall (c1 : (Cutoff TmVar)) (k11 : Hvl) ,
        (shifthvl_TmVar c1 k10 k11) -> (wfDecls k11 (shift_TmVar_Decls c1 d13)))) /\
    (forall (s6 : Tm) (wf : (wfTm k10 s6)) ,
      (forall (c1 : (Cutoff TmVar)) (k11 : Hvl) ,
        (shifthvl_TmVar c1 k10 k11) -> (wfTm k11 (shift_TmVar_Tm c1 s6))))) := (ind_wfDecls_Tm (fun (k10 : Hvl) (d13 : Decls) (wf : (wfDecls k10 d13)) =>
    (forall (c1 : (Cutoff TmVar)) (k11 : Hvl) ,
      (shifthvl_TmVar c1 k10 k11) -> (wfDecls k11 (shift_TmVar_Decls c1 d13)))) (fun (k10 : Hvl) (s6 : Tm) (wf : (wfTm k10 s6)) =>
    (forall (c1 : (Cutoff TmVar)) (k11 : Hvl) ,
      (shifthvl_TmVar c1 k10 k11) -> (wfTm k11 (shift_TmVar_Tm c1 s6)))) (fun (k10 : Hvl) (c1 : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c1 k10 k11)) =>
    (wfDecls_DNil k11)) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm k10 t)) IHt (d : Decls) (wf0 : (wfDecls (HS TmVar k10) d)) IHd (c1 : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c1 k10 k11)) =>
    (wfDecls_DCons k11 (IHt c1 k11 (weaken_shifthvl_TmVar H0 ins)) (IHd (CS c1) (HS TmVar k11) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k10 : Hvl) (x7 : (Index TmVar)) (wfi : (wfindex k10 x7)) (c1 : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c1 k10 k11)) =>
    (wfTm_Var k11 _ (shift_TmVar__wfindex_TmVar c1 k10 k11 ins x7 wfi))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) (t : Tm) (wf0 : (wfTm (HS TmVar k10) t)) IHt (c1 : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c1 k10 k11)) =>
    (wfTm_Abs k11 (shift_TmVar__wfTy k10 T wf c1 k11 (weaken_shifthvl_TmVar H0 ins)) (IHt (CS c1) (HS TmVar k11) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k10 t2)) IHt2 (c1 : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c1 k10 k11)) =>
    (wfTm_App k11 (IHt1 c1 k11 (weaken_shifthvl_TmVar H0 ins)) (IHt2 c1 k11 (weaken_shifthvl_TmVar H0 ins)))) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm (HS TyVar k10) t)) IHt (c1 : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c1 k10 k11)) =>
    (wfTm_TAbs k11 (IHt c1 (HS TyVar k11) (weaken_shifthvl_TmVar (HS TyVar H0) ins)))) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm k10 t)) IHt (T : Ty) (wf0 : (wfTy k10 T)) (c1 : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c1 k10 k11)) =>
    (wfTm_TApp k11 (IHt c1 k11 (weaken_shifthvl_TmVar H0 ins)) (shift_TmVar__wfTy k10 T wf0 c1 k11 (weaken_shifthvl_TmVar H0 ins)))) (fun (k10 : Hvl) (d : Decls) (wf : (wfDecls k10 d)) IHd (t : Tm) (wf0 : (wfTm (appendHvl k10 (appendHvl H0 (bind d))) t)) IHt (c1 : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c1 k10 k11)) =>
    (wfTm_Let k11 (IHd c1 k11 (weaken_shifthvl_TmVar H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k11) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _)))) eq_refl (IHt (weakenCutoffTmVar c1 (appendHvl H0 (bind d))) (appendHvl k11 (appendHvl H0 (bind d))) (weaken_shifthvl_TmVar (appendHvl H0 (bind d)) ins)))))).
  Lemma shift_TmVar__wfDecls (k10 : Hvl) :
    (forall (d13 : Decls) (wf : (wfDecls k10 d13)) ,
      (forall (c1 : (Cutoff TmVar)) (k11 : Hvl) ,
        (shifthvl_TmVar c1 k10 k11) -> (wfDecls k11 (shift_TmVar_Decls c1 d13)))).
  Proof.
    pose proof ((shift_TmVar__wfDecls_Tm k10)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_TmVar__wfTm (k10 : Hvl) :
    (forall (s6 : Tm) (wf0 : (wfTm k10 s6)) ,
      (forall (c2 : (Cutoff TmVar)) (k12 : Hvl) ,
        (shifthvl_TmVar c2 k10 k12) -> (wfTm k12 (shift_TmVar_Tm c2 s6)))).
  Proof.
    pose proof ((shift_TmVar__wfDecls_Tm k10)).
    destruct_conjs .
    easy .
  Qed.
  Definition shift_TyVar__wfDecls_Tm : (forall (k10 : Hvl) ,
    (forall (d13 : Decls) (wf : (wfDecls k10 d13)) ,
      (forall (c1 : (Cutoff TyVar)) (k11 : Hvl) ,
        (shifthvl_TyVar c1 k10 k11) -> (wfDecls k11 (shift_TyVar_Decls c1 d13)))) /\
    (forall (s6 : Tm) (wf : (wfTm k10 s6)) ,
      (forall (c1 : (Cutoff TyVar)) (k11 : Hvl) ,
        (shifthvl_TyVar c1 k10 k11) -> (wfTm k11 (shift_TyVar_Tm c1 s6))))) := (ind_wfDecls_Tm (fun (k10 : Hvl) (d13 : Decls) (wf : (wfDecls k10 d13)) =>
    (forall (c1 : (Cutoff TyVar)) (k11 : Hvl) ,
      (shifthvl_TyVar c1 k10 k11) -> (wfDecls k11 (shift_TyVar_Decls c1 d13)))) (fun (k10 : Hvl) (s6 : Tm) (wf : (wfTm k10 s6)) =>
    (forall (c1 : (Cutoff TyVar)) (k11 : Hvl) ,
      (shifthvl_TyVar c1 k10 k11) -> (wfTm k11 (shift_TyVar_Tm c1 s6)))) (fun (k10 : Hvl) (c1 : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c1 k10 k11)) =>
    (wfDecls_DNil k11)) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm k10 t)) IHt (d : Decls) (wf0 : (wfDecls (HS TmVar k10) d)) IHd (c1 : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c1 k10 k11)) =>
    (wfDecls_DCons k11 (IHt c1 k11 (weaken_shifthvl_TyVar H0 ins)) (IHd c1 (HS TmVar k11) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k10 : Hvl) (x7 : (Index TmVar)) (wfi : (wfindex k10 x7)) (c1 : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c1 k10 k11)) =>
    (wfTm_Var k11 _ (shift_TyVar__wfindex_TmVar c1 k10 k11 ins x7 wfi))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) (t : Tm) (wf0 : (wfTm (HS TmVar k10) t)) IHt (c1 : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c1 k10 k11)) =>
    (wfTm_Abs k11 (shift_TyVar__wfTy k10 T wf c1 k11 (weaken_shifthvl_TyVar H0 ins)) (IHt c1 (HS TmVar k11) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k10 t2)) IHt2 (c1 : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c1 k10 k11)) =>
    (wfTm_App k11 (IHt1 c1 k11 (weaken_shifthvl_TyVar H0 ins)) (IHt2 c1 k11 (weaken_shifthvl_TyVar H0 ins)))) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm (HS TyVar k10) t)) IHt (c1 : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c1 k10 k11)) =>
    (wfTm_TAbs k11 (IHt (CS c1) (HS TyVar k11) (weaken_shifthvl_TyVar (HS TyVar H0) ins)))) (fun (k10 : Hvl) (t : Tm) (wf : (wfTm k10 t)) IHt (T : Ty) (wf0 : (wfTy k10 T)) (c1 : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c1 k10 k11)) =>
    (wfTm_TApp k11 (IHt c1 k11 (weaken_shifthvl_TyVar H0 ins)) (shift_TyVar__wfTy k10 T wf0 c1 k11 (weaken_shifthvl_TyVar H0 ins)))) (fun (k10 : Hvl) (d : Decls) (wf : (wfDecls k10 d)) IHd (t : Tm) (wf0 : (wfTm (appendHvl k10 (appendHvl H0 (bind d))) t)) IHt (c1 : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c1 k10 k11)) =>
    (wfTm_Let k11 (IHd c1 k11 (weaken_shifthvl_TyVar H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k11) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TyVar__bind _ _)))) eq_refl (IHt (weakenCutoffTyVar c1 (appendHvl H0 (bind d))) (appendHvl k11 (appendHvl H0 (bind d))) (weaken_shifthvl_TyVar (appendHvl H0 (bind d)) ins)))))).
  Lemma shift_TyVar__wfDecls (k10 : Hvl) :
    (forall (d13 : Decls) (wf : (wfDecls k10 d13)) ,
      (forall (c1 : (Cutoff TyVar)) (k11 : Hvl) ,
        (shifthvl_TyVar c1 k10 k11) -> (wfDecls k11 (shift_TyVar_Decls c1 d13)))).
  Proof.
    pose proof ((shift_TyVar__wfDecls_Tm k10)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_TyVar__wfTm (k10 : Hvl) :
    (forall (s6 : Tm) (wf0 : (wfTm k10 s6)) ,
      (forall (c2 : (Cutoff TyVar)) (k12 : Hvl) ,
        (shifthvl_TyVar c2 k10 k12) -> (wfTm k12 (shift_TyVar_Tm c2 s6)))).
  Proof.
    pose proof ((shift_TyVar__wfDecls_Tm k10)).
    destruct_conjs .
    easy .
  Qed.
  Fixpoint weaken_wfTy (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (S4 : Ty) (wf : (wfTy k11 S4)) ,
    (wfTy (appendHvl k11 k10) (weakenTy S4 k10))) :=
    match k10 return (forall (k11 : Hvl) (S4 : Ty) (wf : (wfTy k11 S4)) ,
      (wfTy (appendHvl k11 k10) (weakenTy S4 k10))) with
      | (H0) => (fun (k11 : Hvl) (S4 : Ty) (wf : (wfTy k11 S4)) =>
        wf)
      | (HS TmVar k10) => (fun (k11 : Hvl) (S4 : Ty) (wf : (wfTy k11 S4)) =>
        (shift_TmVar__wfTy (appendHvl k11 k10) (weakenTy S4 k10) (weaken_wfTy k10 k11 S4 wf) C0 (HS TmVar (appendHvl k11 k10)) (shifthvl_TmVar_here (appendHvl k11 k10))))
      | (HS TyVar k10) => (fun (k11 : Hvl) (S4 : Ty) (wf : (wfTy k11 S4)) =>
        (shift_TyVar__wfTy (appendHvl k11 k10) (weakenTy S4 k10) (weaken_wfTy k10 k11 S4 wf) C0 (HS TyVar (appendHvl k11 k10)) (shifthvl_TyVar_here (appendHvl k11 k10))))
    end.
  Fixpoint weaken_wfDecls (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (d13 : Decls) (wf : (wfDecls k11 d13)) ,
    (wfDecls (appendHvl k11 k10) (weakenDecls d13 k10))) :=
    match k10 return (forall (k11 : Hvl) (d13 : Decls) (wf : (wfDecls k11 d13)) ,
      (wfDecls (appendHvl k11 k10) (weakenDecls d13 k10))) with
      | (H0) => (fun (k11 : Hvl) (d13 : Decls) (wf : (wfDecls k11 d13)) =>
        wf)
      | (HS TmVar k10) => (fun (k11 : Hvl) (d13 : Decls) (wf : (wfDecls k11 d13)) =>
        (shift_TmVar__wfDecls (appendHvl k11 k10) (weakenDecls d13 k10) (weaken_wfDecls k10 k11 d13 wf) C0 (HS TmVar (appendHvl k11 k10)) (shifthvl_TmVar_here (appendHvl k11 k10))))
      | (HS TyVar k10) => (fun (k11 : Hvl) (d13 : Decls) (wf : (wfDecls k11 d13)) =>
        (shift_TyVar__wfDecls (appendHvl k11 k10) (weakenDecls d13 k10) (weaken_wfDecls k10 k11 d13 wf) C0 (HS TyVar (appendHvl k11 k10)) (shifthvl_TyVar_here (appendHvl k11 k10))))
    end.
  Fixpoint weaken_wfTm (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (s6 : Tm) (wf : (wfTm k11 s6)) ,
    (wfTm (appendHvl k11 k10) (weakenTm s6 k10))) :=
    match k10 return (forall (k11 : Hvl) (s6 : Tm) (wf : (wfTm k11 s6)) ,
      (wfTm (appendHvl k11 k10) (weakenTm s6 k10))) with
      | (H0) => (fun (k11 : Hvl) (s6 : Tm) (wf : (wfTm k11 s6)) =>
        wf)
      | (HS TmVar k10) => (fun (k11 : Hvl) (s6 : Tm) (wf : (wfTm k11 s6)) =>
        (shift_TmVar__wfTm (appendHvl k11 k10) (weakenTm s6 k10) (weaken_wfTm k10 k11 s6 wf) C0 (HS TmVar (appendHvl k11 k10)) (shifthvl_TmVar_here (appendHvl k11 k10))))
      | (HS TyVar k10) => (fun (k11 : Hvl) (s6 : Tm) (wf : (wfTm k11 s6)) =>
        (shift_TyVar__wfTm (appendHvl k11 k10) (weakenTm s6 k10) (weaken_wfTm k10 k11 s6 wf) C0 (HS TyVar (appendHvl k11 k10)) (shifthvl_TyVar_here (appendHvl k11 k10))))
    end.
End ShiftWellFormed.
Lemma wfTy_cast  :
  (forall (k12 : Hvl) (S5 : Ty) (k13 : Hvl) (S6 : Ty) ,
    (k12 = k13) -> (S5 = S6) -> (wfTy k12 S5) -> (wfTy k13 S6)).
Proof.
  congruence .
Qed.
Lemma wfDecls_cast  :
  (forall (k12 : Hvl) (d13 : Decls) (k13 : Hvl) (d14 : Decls) ,
    (k12 = k13) -> (d13 = d14) -> (wfDecls k12 d13) -> (wfDecls k13 d14)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k12 : Hvl) (s6 : Tm) (k13 : Hvl) (s7 : Tm) ,
    (k12 = k13) -> (s6 = s7) -> (wfTm k12 s6) -> (wfTm k13 s7)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TyVar : infra.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TyVar : shift.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TyVar : shift_wf.
 Hint Resolve shift_TmVar__wfindex_TmVar shift_TmVar__wfindex_TyVar shift_TyVar__wfindex_TmVar shift_TyVar__wfindex_TyVar : wf.
 Hint Resolve shift_TmVar__wfDecls shift_TmVar__wfTm shift_TmVar__wfTy shift_TyVar__wfDecls shift_TyVar__wfTm shift_TyVar__wfTy : infra.
 Hint Resolve shift_TmVar__wfDecls shift_TmVar__wfTm shift_TmVar__wfTy shift_TyVar__wfDecls shift_TyVar__wfTm shift_TyVar__wfTy : shift.
 Hint Resolve shift_TmVar__wfDecls shift_TmVar__wfTm shift_TmVar__wfTy shift_TyVar__wfDecls shift_TyVar__wfTm shift_TyVar__wfTy : shift_wf.
 Hint Resolve shift_TmVar__wfDecls shift_TmVar__wfTm shift_TmVar__wfTy shift_TyVar__wfDecls shift_TyVar__wfTm shift_TyVar__wfTy : wf.
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
  Inductive substhvl_TmVar (k10 : Hvl) : (forall (d13 : (Trace TmVar)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | substhvl_TmVar_here :
        (substhvl_TmVar k10 X0 (HS TmVar k10) k10)
    | substhvl_TmVar_there_TmVar
        {d13 : (Trace TmVar)}
        {k11 : Hvl} {k12 : Hvl} :
        (substhvl_TmVar k10 d13 k11 k12) -> (substhvl_TmVar k10 (XS TmVar d13) (HS TmVar k11) (HS TmVar k12))
    | substhvl_TmVar_there_TyVar
        {d13 : (Trace TmVar)}
        {k11 : Hvl} {k12 : Hvl} :
        (substhvl_TmVar k10 d13 k11 k12) -> (substhvl_TmVar k10 (XS TyVar d13) (HS TyVar k11) (HS TyVar k12)).
  Inductive substhvl_TyVar (k10 : Hvl) : (forall (d13 : (Trace TyVar)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | substhvl_TyVar_here :
        (substhvl_TyVar k10 X0 (HS TyVar k10) k10)
    | substhvl_TyVar_there_TmVar
        {d13 : (Trace TyVar)}
        {k11 : Hvl} {k12 : Hvl} :
        (substhvl_TyVar k10 d13 k11 k12) -> (substhvl_TyVar k10 (XS TmVar d13) (HS TmVar k11) (HS TmVar k12))
    | substhvl_TyVar_there_TyVar
        {d13 : (Trace TyVar)}
        {k11 : Hvl} {k12 : Hvl} :
        (substhvl_TyVar k10 d13 k11 k12) -> (substhvl_TyVar k10 (XS TyVar d13) (HS TyVar k11) (HS TyVar k12)).
  Lemma weaken_substhvl_TmVar  :
    (forall {k11 : Hvl} (k10 : Hvl) {d13 : (Trace TmVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TmVar k11 d13 k12 k13) -> (substhvl_TmVar k11 (weakenTrace d13 k10) (appendHvl k12 k10) (appendHvl k13 k10))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_TyVar  :
    (forall {k11 : Hvl} (k10 : Hvl) {d13 : (Trace TyVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TyVar k11 d13 k12 k13) -> (substhvl_TyVar k11 (weakenTrace d13 k10) (appendHvl k12 k10) (appendHvl k13 k10))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_TmVar_wfindex_TmVar {k12 : Hvl} {s6 : Tm} (wft : (wfTm k12 s6)) :
    (forall {d13 : (Trace TmVar)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_TmVar k12 d13 k13 k14) -> (forall {x7 : (Index TmVar)} ,
        (wfindex k13 x7) -> (wfTm k14 (subst_TmVar_Index d13 s6 x7)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TyVar_wfindex_TyVar {k12 : Hvl} {S5 : Ty} (wft : (wfTy k12 S5)) :
    (forall {d13 : (Trace TyVar)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_TyVar k12 d13 k13 k14) -> (forall {X7 : (Index TyVar)} ,
        (wfindex k13 X7) -> (wfTy k14 (subst_TyVar_Index d13 S5 X7)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TmVar_wfindex_TyVar {k12 : Hvl} :
    (forall {d13 : (Trace TmVar)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_TmVar k12 d13 k13 k14) -> (forall {X7 : (Index TyVar)} ,
        (wfindex k13 X7) -> (wfindex k14 X7))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_TyVar_wfindex_TmVar {k12 : Hvl} :
    (forall {d13 : (Trace TyVar)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_TyVar k12 d13 k13 k14) -> (forall {x7 : (Index TmVar)} ,
        (wfindex k13 x7) -> (wfindex k14 x7))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_TmVar_wfTy {k12 : Hvl} : (forall (k13 : Hvl) ,
    (forall (S5 : Ty) (wf0 : (wfTy k13 S5)) ,
      (forall {d13 : (Trace TmVar)} {k14 : Hvl} ,
        (substhvl_TmVar k12 d13 k13 k14) -> (wfTy k14 S5)))) := (ind_wfTy (fun (k13 : Hvl) (S5 : Ty) (wf0 : (wfTy k13 S5)) =>
    (forall {d13 : (Trace TmVar)} {k14 : Hvl} ,
      (substhvl_TmVar k12 d13 k13 k14) -> (wfTy k14 S5))) (fun (k13 : Hvl) {X7 : (Index TyVar)} (wfi : (wfindex k13 X7)) {d13 : (Trace TmVar)} {k14 : Hvl} (del : (substhvl_TmVar k12 d13 k13 k14)) =>
    (wfTy_TVar k14 _ (substhvl_TmVar_wfindex_TyVar del wfi))) (fun (k13 : Hvl) (T1 : Ty) (wf0 : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k13 T2)) IHT2 {d13 : (Trace TmVar)} {k14 : Hvl} (del : (substhvl_TmVar k12 d13 k13 k14)) =>
    (wfTy_TArr k14 (IHT1 (weakenTrace d13 H0) k14 (weaken_substhvl_TmVar H0 del)) (IHT2 (weakenTrace d13 H0) k14 (weaken_substhvl_TmVar H0 del)))) (fun (k13 : Hvl) (T : Ty) (wf0 : (wfTy (HS TyVar k13) T)) IHT {d13 : (Trace TmVar)} {k14 : Hvl} (del : (substhvl_TmVar k12 d13 k13 k14)) =>
    (wfTy_TAll k14 (IHT (weakenTrace d13 (HS TyVar H0)) (HS TyVar k14) (weaken_substhvl_TmVar (HS TyVar H0) del))))).
  Definition substhvl_TyVar_wfTy {k12 : Hvl} {S5 : Ty} (wf : (wfTy k12 S5)) : (forall (k13 : Hvl) ,
    (forall (S6 : Ty) (wf0 : (wfTy k13 S6)) ,
      (forall {d13 : (Trace TyVar)} {k14 : Hvl} ,
        (substhvl_TyVar k12 d13 k13 k14) -> (wfTy k14 (subst_TyVar_Ty d13 S5 S6))))) := (ind_wfTy (fun (k13 : Hvl) (S6 : Ty) (wf0 : (wfTy k13 S6)) =>
    (forall {d13 : (Trace TyVar)} {k14 : Hvl} ,
      (substhvl_TyVar k12 d13 k13 k14) -> (wfTy k14 (subst_TyVar_Ty d13 S5 S6)))) (fun (k13 : Hvl) {X7 : (Index TyVar)} (wfi : (wfindex k13 X7)) {d13 : (Trace TyVar)} {k14 : Hvl} (del : (substhvl_TyVar k12 d13 k13 k14)) =>
    (substhvl_TyVar_wfindex_TyVar wf del wfi)) (fun (k13 : Hvl) (T1 : Ty) (wf0 : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k13 T2)) IHT2 {d13 : (Trace TyVar)} {k14 : Hvl} (del : (substhvl_TyVar k12 d13 k13 k14)) =>
    (wfTy_TArr k14 (IHT1 (weakenTrace d13 H0) k14 (weaken_substhvl_TyVar H0 del)) (IHT2 (weakenTrace d13 H0) k14 (weaken_substhvl_TyVar H0 del)))) (fun (k13 : Hvl) (T : Ty) (wf0 : (wfTy (HS TyVar k13) T)) IHT {d13 : (Trace TyVar)} {k14 : Hvl} (del : (substhvl_TyVar k12 d13 k13 k14)) =>
    (wfTy_TAll k14 (IHT (weakenTrace d13 (HS TyVar H0)) (HS TyVar k14) (weaken_substhvl_TyVar (HS TyVar H0) del))))).
  Definition substhvl_TmVar_wfDecls_Tm {k12 : Hvl} {s6 : Tm} (wf : (wfTm k12 s6)) : (forall (k13 : Hvl) ,
    (forall (d13 : Decls) (wf0 : (wfDecls k13 d13)) ,
      (forall {d14 : (Trace TmVar)} {k14 : Hvl} ,
        (substhvl_TmVar k12 d14 k13 k14) -> (wfDecls k14 (subst_TmVar_Decls d14 s6 d13)))) /\
    (forall (s7 : Tm) (wf0 : (wfTm k13 s7)) ,
      (forall {d13 : (Trace TmVar)} {k14 : Hvl} ,
        (substhvl_TmVar k12 d13 k13 k14) -> (wfTm k14 (subst_TmVar_Tm d13 s6 s7))))) := (ind_wfDecls_Tm (fun (k13 : Hvl) (d13 : Decls) (wf0 : (wfDecls k13 d13)) =>
    (forall {d14 : (Trace TmVar)} {k14 : Hvl} ,
      (substhvl_TmVar k12 d14 k13 k14) -> (wfDecls k14 (subst_TmVar_Decls d14 s6 d13)))) (fun (k13 : Hvl) (s7 : Tm) (wf0 : (wfTm k13 s7)) =>
    (forall {d13 : (Trace TmVar)} {k14 : Hvl} ,
      (substhvl_TmVar k12 d13 k13 k14) -> (wfTm k14 (subst_TmVar_Tm d13 s6 s7)))) (fun (k13 : Hvl) {d13 : (Trace TmVar)} {k14 : Hvl} (del : (substhvl_TmVar k12 d13 k13 k14)) =>
    (wfDecls_DNil k14)) (fun (k13 : Hvl) (t : Tm) (wf0 : (wfTm k13 t)) IHt (d : Decls) (wf1 : (wfDecls (HS TmVar k13) d)) IHd {d13 : (Trace TmVar)} {k14 : Hvl} (del : (substhvl_TmVar k12 d13 k13 k14)) =>
    (wfDecls_DCons k14 (IHt (weakenTrace d13 H0) k14 (weaken_substhvl_TmVar H0 del)) (IHd (weakenTrace d13 (HS TmVar H0)) (HS TmVar k14) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k13 : Hvl) {x7 : (Index TmVar)} (wfi : (wfindex k13 x7)) {d13 : (Trace TmVar)} {k14 : Hvl} (del : (substhvl_TmVar k12 d13 k13 k14)) =>
    (substhvl_TmVar_wfindex_TmVar wf del wfi)) (fun (k13 : Hvl) (T : Ty) (wf0 : (wfTy k13 T)) (t : Tm) (wf1 : (wfTm (HS TmVar k13) t)) IHt {d13 : (Trace TmVar)} {k14 : Hvl} (del : (substhvl_TmVar k12 d13 k13 k14)) =>
    (wfTm_Abs k14 (substhvl_TmVar_wfTy k13 T wf0 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d13 (HS TmVar H0)) (HS TmVar k14) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k13 : Hvl) (t1 : Tm) (wf0 : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k13 t2)) IHt2 {d13 : (Trace TmVar)} {k14 : Hvl} (del : (substhvl_TmVar k12 d13 k13 k14)) =>
    (wfTm_App k14 (IHt1 (weakenTrace d13 H0) k14 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d13 H0) k14 (weaken_substhvl_TmVar H0 del)))) (fun (k13 : Hvl) (t : Tm) (wf0 : (wfTm (HS TyVar k13) t)) IHt {d13 : (Trace TmVar)} {k14 : Hvl} (del : (substhvl_TmVar k12 d13 k13 k14)) =>
    (wfTm_TAbs k14 (IHt (weakenTrace d13 (HS TyVar H0)) (HS TyVar k14) (weaken_substhvl_TmVar (HS TyVar H0) del)))) (fun (k13 : Hvl) (t : Tm) (wf0 : (wfTm k13 t)) IHt (T : Ty) (wf1 : (wfTy k13 T)) {d13 : (Trace TmVar)} {k14 : Hvl} (del : (substhvl_TmVar k12 d13 k13 k14)) =>
    (wfTm_TApp k14 (IHt (weakenTrace d13 H0) k14 (weaken_substhvl_TmVar H0 del)) (substhvl_TmVar_wfTy k13 T wf1 (weaken_substhvl_TmVar H0 del)))) (fun (k13 : Hvl) (d : Decls) (wf0 : (wfDecls k13 d)) IHd (t : Tm) (wf1 : (wfTm (appendHvl k13 (appendHvl H0 (bind d))) t)) IHt {d13 : (Trace TmVar)} {k14 : Hvl} (del : (substhvl_TmVar k12 d13 k13 k14)) =>
    (wfTm_Let k14 (IHd (weakenTrace d13 H0) k14 (weaken_substhvl_TmVar H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k14) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0)))) eq_refl (IHt (weakenTrace d13 (appendHvl H0 (bind d))) (appendHvl k14 (appendHvl H0 (bind d))) (weaken_substhvl_TmVar (appendHvl H0 (bind d)) del)))))).
  Lemma substhvl_TmVar_wfDecls {k12 : Hvl} {s6 : Tm} (wf : (wfTm k12 s6)) (k13 : Hvl) (d13 : Decls) (wf0 : (wfDecls k13 d13)) :
    (forall {d14 : (Trace TmVar)} {k14 : Hvl} ,
      (substhvl_TmVar k12 d14 k13 k14) -> (wfDecls k14 (subst_TmVar_Decls d14 s6 d13))).
  Proof.
    apply ((substhvl_TmVar_wfDecls_Tm wf k13)).
    auto .
  Qed.
  Lemma substhvl_TmVar_wfTm {k12 : Hvl} {s6 : Tm} (wf : (wfTm k12 s6)) (k13 : Hvl) (s7 : Tm) (wf1 : (wfTm k13 s7)) :
    (forall {d15 : (Trace TmVar)} {k15 : Hvl} ,
      (substhvl_TmVar k12 d15 k13 k15) -> (wfTm k15 (subst_TmVar_Tm d15 s6 s7))).
  Proof.
    apply ((substhvl_TmVar_wfDecls_Tm wf k13)).
    auto .
  Qed.
  Definition substhvl_TyVar_wfDecls_Tm {k12 : Hvl} {S5 : Ty} (wf : (wfTy k12 S5)) : (forall (k13 : Hvl) ,
    (forall (d13 : Decls) (wf0 : (wfDecls k13 d13)) ,
      (forall {d14 : (Trace TyVar)} {k14 : Hvl} ,
        (substhvl_TyVar k12 d14 k13 k14) -> (wfDecls k14 (subst_TyVar_Decls d14 S5 d13)))) /\
    (forall (s6 : Tm) (wf0 : (wfTm k13 s6)) ,
      (forall {d13 : (Trace TyVar)} {k14 : Hvl} ,
        (substhvl_TyVar k12 d13 k13 k14) -> (wfTm k14 (subst_TyVar_Tm d13 S5 s6))))) := (ind_wfDecls_Tm (fun (k13 : Hvl) (d13 : Decls) (wf0 : (wfDecls k13 d13)) =>
    (forall {d14 : (Trace TyVar)} {k14 : Hvl} ,
      (substhvl_TyVar k12 d14 k13 k14) -> (wfDecls k14 (subst_TyVar_Decls d14 S5 d13)))) (fun (k13 : Hvl) (s6 : Tm) (wf0 : (wfTm k13 s6)) =>
    (forall {d13 : (Trace TyVar)} {k14 : Hvl} ,
      (substhvl_TyVar k12 d13 k13 k14) -> (wfTm k14 (subst_TyVar_Tm d13 S5 s6)))) (fun (k13 : Hvl) {d13 : (Trace TyVar)} {k14 : Hvl} (del : (substhvl_TyVar k12 d13 k13 k14)) =>
    (wfDecls_DNil k14)) (fun (k13 : Hvl) (t : Tm) (wf0 : (wfTm k13 t)) IHt (d : Decls) (wf1 : (wfDecls (HS TmVar k13) d)) IHd {d13 : (Trace TyVar)} {k14 : Hvl} (del : (substhvl_TyVar k12 d13 k13 k14)) =>
    (wfDecls_DCons k14 (IHt (weakenTrace d13 H0) k14 (weaken_substhvl_TyVar H0 del)) (IHd (weakenTrace d13 (HS TmVar H0)) (HS TmVar k14) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k13 : Hvl) {x7 : (Index TmVar)} (wfi : (wfindex k13 x7)) {d13 : (Trace TyVar)} {k14 : Hvl} (del : (substhvl_TyVar k12 d13 k13 k14)) =>
    (wfTm_Var k14 _ (substhvl_TyVar_wfindex_TmVar del wfi))) (fun (k13 : Hvl) (T : Ty) (wf0 : (wfTy k13 T)) (t : Tm) (wf1 : (wfTm (HS TmVar k13) t)) IHt {d13 : (Trace TyVar)} {k14 : Hvl} (del : (substhvl_TyVar k12 d13 k13 k14)) =>
    (wfTm_Abs k14 (substhvl_TyVar_wfTy wf k13 T wf0 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d13 (HS TmVar H0)) (HS TmVar k14) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k13 : Hvl) (t1 : Tm) (wf0 : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k13 t2)) IHt2 {d13 : (Trace TyVar)} {k14 : Hvl} (del : (substhvl_TyVar k12 d13 k13 k14)) =>
    (wfTm_App k14 (IHt1 (weakenTrace d13 H0) k14 (weaken_substhvl_TyVar H0 del)) (IHt2 (weakenTrace d13 H0) k14 (weaken_substhvl_TyVar H0 del)))) (fun (k13 : Hvl) (t : Tm) (wf0 : (wfTm (HS TyVar k13) t)) IHt {d13 : (Trace TyVar)} {k14 : Hvl} (del : (substhvl_TyVar k12 d13 k13 k14)) =>
    (wfTm_TAbs k14 (IHt (weakenTrace d13 (HS TyVar H0)) (HS TyVar k14) (weaken_substhvl_TyVar (HS TyVar H0) del)))) (fun (k13 : Hvl) (t : Tm) (wf0 : (wfTm k13 t)) IHt (T : Ty) (wf1 : (wfTy k13 T)) {d13 : (Trace TyVar)} {k14 : Hvl} (del : (substhvl_TyVar k12 d13 k13 k14)) =>
    (wfTm_TApp k14 (IHt (weakenTrace d13 H0) k14 (weaken_substhvl_TyVar H0 del)) (substhvl_TyVar_wfTy wf k13 T wf1 (weaken_substhvl_TyVar H0 del)))) (fun (k13 : Hvl) (d : Decls) (wf0 : (wfDecls k13 d)) IHd (t : Tm) (wf1 : (wfTm (appendHvl k13 (appendHvl H0 (bind d))) t)) IHt {d13 : (Trace TyVar)} {k14 : Hvl} (del : (substhvl_TyVar k12 d13 k13 k14)) =>
    (wfTm_Let k14 (IHd (weakenTrace d13 H0) k14 (weaken_substhvl_TyVar H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k14) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TyVar__bind _ _ _)) (eq_refl H0)))) eq_refl (IHt (weakenTrace d13 (appendHvl H0 (bind d))) (appendHvl k14 (appendHvl H0 (bind d))) (weaken_substhvl_TyVar (appendHvl H0 (bind d)) del)))))).
  Lemma substhvl_TyVar_wfDecls {k12 : Hvl} {S5 : Ty} (wf : (wfTy k12 S5)) (k13 : Hvl) (d13 : Decls) (wf0 : (wfDecls k13 d13)) :
    (forall {d14 : (Trace TyVar)} {k14 : Hvl} ,
      (substhvl_TyVar k12 d14 k13 k14) -> (wfDecls k14 (subst_TyVar_Decls d14 S5 d13))).
  Proof.
    apply ((substhvl_TyVar_wfDecls_Tm wf k13)).
    auto .
  Qed.
  Lemma substhvl_TyVar_wfTm {k12 : Hvl} {S5 : Ty} (wf : (wfTy k12 S5)) (k13 : Hvl) (s6 : Tm) (wf1 : (wfTm k13 s6)) :
    (forall {d15 : (Trace TyVar)} {k15 : Hvl} ,
      (substhvl_TyVar k12 d15 k13 k15) -> (wfTm k15 (subst_TyVar_Tm d15 S5 s6))).
  Proof.
    apply ((substhvl_TyVar_wfDecls_Tm wf k13)).
    auto .
  Qed.
End SubstWellFormed.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : infra.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : subst.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : subst_wf.
 Hint Resolve substhvl_TmVar_wfindex_TmVar substhvl_TmVar_wfindex_TyVar substhvl_TyVar_wfindex_TmVar substhvl_TyVar_wfindex_TyVar : wf.
 Hint Resolve substhvl_TmVar_wfDecls substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfDecls substhvl_TyVar_wfTm substhvl_TyVar_wfTy : infra.
 Hint Resolve substhvl_TmVar_wfDecls substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfDecls substhvl_TyVar_wfTm substhvl_TyVar_wfTy : subst.
 Hint Resolve substhvl_TmVar_wfDecls substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfDecls substhvl_TyVar_wfTm substhvl_TyVar_wfTy : subst_wf.
 Hint Resolve substhvl_TmVar_wfDecls substhvl_TmVar_wfTm substhvl_TmVar_wfTy substhvl_TyVar_wfDecls substhvl_TyVar_wfTm substhvl_TyVar_wfTy : wf.
 Hint Constructors substhvl_TmVar substhvl_TyVar : infra.
 Hint Constructors substhvl_TmVar substhvl_TyVar : subst.
 Hint Constructors substhvl_TmVar substhvl_TyVar : subst_wf.
 Hint Constructors substhvl_TmVar substhvl_TyVar : wf.
Fixpoint subhvl_TmVar (k12 : Hvl) {struct k12} :
Prop :=
  match k12 with
    | (H0) => True
    | (HS a k12) => match a with
      | (TmVar) => (subhvl_TmVar k12)
      | _ => False
    end
  end.
Lemma subhvl_TmVar_append  :
  (forall (k12 : Hvl) (k13 : Hvl) ,
    (subhvl_TmVar k12) -> (subhvl_TmVar k13) -> (subhvl_TmVar (appendHvl k12 k13))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_TmVar_append : infra.
 Hint Resolve subhvl_TmVar_append : wf.
Lemma wfTy_strengthen_subhvl_TmVar  :
  (forall (k11 : Hvl) (k10 : Hvl) (S4 : Ty) ,
    (subhvl_TmVar k11) -> (wfTy (appendHvl k10 k11) (weakenTy S4 k11)) -> (wfTy k10 S4)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H32 : (wfTy (appendHvl _ _) (weakenTy _ _)) |- _ => apply (wfTy_strengthen_subhvl_TmVar) in H32
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
  Fixpoint shift_TmVar_Ctx (c1 : (Cutoff TmVar)) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shift_TmVar_Ctx c1 G0) T)
      | (etvar G0) => (etvar (shift_TmVar_Ctx c1 G0))
    end.
  Fixpoint shift_TyVar_Ctx (c1 : (Cutoff TyVar)) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shift_TyVar_Ctx c1 G0) (shift_TyVar_Ty (weakenCutoffTyVar c1 (domainCtx G0)) T))
      | (etvar G0) => (etvar (shift_TyVar_Ctx c1 G0))
    end.
  Fixpoint weakenCtx (G : Ctx) (k12 : Hvl) {struct k12} :
  Ctx :=
    match k12 with
      | (H0) => G
      | (HS TmVar k12) => (weakenCtx G k12)
      | (HS TyVar k12) => (shift_TyVar_Ctx C0 (weakenCtx G k12))
    end.
  Fixpoint subst_TmVar_Ctx (d13 : (Trace TmVar)) (s6 : Tm) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (subst_TmVar_Ctx d13 s6 G0) T)
      | (etvar G0) => (etvar (subst_TmVar_Ctx d13 s6 G0))
    end.
  Fixpoint subst_TyVar_Ctx (d13 : (Trace TyVar)) (S5 : Ty) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (subst_TyVar_Ctx d13 S5 G0) (subst_TyVar_Ty (weakenTrace d13 (domainCtx G0)) S5 T))
      | (etvar G0) => (etvar (subst_TyVar_Ctx d13 S5 G0))
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
    (forall (d13 : (Trace TmVar)) (s6 : Tm) (G : Ctx) ,
      ((domainCtx (subst_TmVar_Ctx d13 s6 G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainCtx_subst_TyVar_Ctx  :
    (forall (d13 : (Trace TyVar)) (S5 : Ty) (G : Ctx) ,
      ((domainCtx (subst_TyVar_Ctx d13 S5 G)) = (domainCtx G))).
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
      (forall (d13 : (Trace TmVar)) (s6 : Tm) (G : Ctx) (G0 : Ctx) ,
        ((subst_TmVar_Ctx d13 s6 (appendCtx G G0)) = (appendCtx (subst_TmVar_Ctx d13 s6 G) (subst_TmVar_Ctx (weakenTrace d13 (domainCtx G)) s6 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma subst_TyVar_Ctx_appendCtx  :
      (forall (d13 : (Trace TyVar)) (S5 : Ty) (G : Ctx) (G0 : Ctx) ,
        ((subst_TyVar_Ctx d13 S5 (appendCtx G G0)) = (appendCtx (subst_TyVar_Ctx d13 S5 G) (subst_TyVar_Ctx (weakenTrace d13 (domainCtx G)) S5 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S5 : Ty) (k12 : Hvl) (k13 : Hvl) ,
      ((weakenTy (weakenTy S5 k12) k13) = (weakenTy S5 (appendHvl k12 k13)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenDecls_append  :
    (forall (d13 : Decls) (k12 : Hvl) (k13 : Hvl) ,
      ((weakenDecls (weakenDecls d13 k12) k13) = (weakenDecls d13 (appendHvl k12 k13)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s6 : Tm) (k12 : Hvl) (k13 : Hvl) ,
      ((weakenTm (weakenTm s6 k12) k13) = (weakenTm s6 (appendHvl k12 k13)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Ctx -> (Index TmVar) -> Ty -> Prop :=
      | lookup_evar_here {G : Ctx}
          (T5 : Ty) :
          (wfTy (domainCtx G) T5) -> (lookup_evar (evar G T5) I0 T5)
      | lookup_evar_there_evar
          {G : Ctx} {x7 : (Index TmVar)}
          (T6 : Ty) (T7 : Ty) :
          (lookup_evar G x7 T6) -> (lookup_evar (evar G T7) (IS x7) T6)
      | lookup_evar_there_etvar
          {G : Ctx} {x7 : (Index TmVar)}
          (T6 : Ty) :
          (lookup_evar G x7 T6) -> (lookup_evar (etvar G) x7 (shift_TyVar_Ty C0 T6)).
    Inductive lookup_etvar : Ctx -> (Index TyVar) -> Prop :=
      | lookup_etvar_here {G : Ctx}
          : (lookup_etvar (etvar G) I0)
      | lookup_etvar_there_evar
          {G : Ctx} {X7 : (Index TyVar)}
          (T6 : Ty) :
          (lookup_etvar G X7) -> (lookup_etvar (evar G T6) X7)
      | lookup_etvar_there_etvar
          {G : Ctx} {X7 : (Index TyVar)} :
          (lookup_etvar G X7) -> (lookup_etvar (etvar G) (IS X7)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Ctx) (T6 : Ty) (T7 : Ty) ,
        (lookup_evar (evar G T6) I0 T7) -> (T6 = T7)).
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
    Lemma lookup_evar_wf  :
      (forall {G : Ctx} {x7 : (Index TmVar)} (T6 : Ty) ,
        (lookup_evar G x7 T6) -> (wfTy (domainCtx G) T6)).
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
      (forall {G : Ctx} (G0 : Ctx) {X7 : (Index TyVar)} ,
        (lookup_etvar G X7) -> (lookup_etvar (appendCtx G G0) (weakenIndexTyVar X7 (domainCtx G0)))).
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
      (forall {G : Ctx} {X7 : (Index TyVar)} ,
        (lookup_etvar G X7) -> (wfindex (domainCtx G) X7)).
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
        (shift_evar c1 G G0) -> (shift_evar (CS c1) (evar G T) (evar G0 T))
    | shiftevar_there_etvar
        {c1 : (Cutoff TmVar)} {G : Ctx}
        {G0 : Ctx} :
        (shift_evar c1 G G0) -> (shift_evar c1 (etvar G) (etvar G0)).
  Lemma weaken_shift_evar  :
    (forall (G : Ctx) {c1 : (Cutoff TmVar)} {G0 : Ctx} {G1 : Ctx} ,
      (shift_evar c1 G0 G1) -> (shift_evar (weakenCutoffTmVar c1 (domainCtx G)) (appendCtx G0 G) (appendCtx G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff TyVar) -> Ctx -> Ctx -> Prop :=
    | shift_etvar_here {G : Ctx} :
        (shift_etvar C0 G (etvar G))
    | shiftetvar_there_evar
        {c1 : (Cutoff TyVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_etvar c1 G G0) -> (shift_etvar c1 (evar G T) (evar G0 (shift_TyVar_Ty c1 T)))
    | shiftetvar_there_etvar
        {c1 : (Cutoff TyVar)} {G : Ctx}
        {G0 : Ctx} :
        (shift_etvar c1 G G0) -> (shift_etvar (CS c1) (etvar G) (etvar G0)).
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
  Inductive subst_evar (G : Ctx) (T6 : Ty) (s6 : Tm) : (Trace TmVar) -> Ctx -> Ctx -> Prop :=
    | subst_evar_here :
        (subst_evar G T6 s6 X0 (evar G T6) G)
    | subst_evar_there_evar
        {d13 : (Trace TmVar)} {G0 : Ctx}
        {G1 : Ctx} (T7 : Ty) :
        (subst_evar G T6 s6 d13 G0 G1) -> (subst_evar G T6 s6 (XS TmVar d13) (evar G0 T7) (evar G1 T7))
    | subst_evar_there_etvar
        {d13 : (Trace TmVar)} {G0 : Ctx}
        {G1 : Ctx} :
        (subst_evar G T6 s6 d13 G0 G1) -> (subst_evar G T6 s6 (XS TyVar d13) (etvar G0) (etvar G1)).
  Lemma weaken_subst_evar {G : Ctx} (T6 : Ty) {s6 : Tm} :
    (forall (G0 : Ctx) {d13 : (Trace TmVar)} {G1 : Ctx} {G2 : Ctx} ,
      (subst_evar G T6 s6 d13 G1 G2) -> (subst_evar G T6 s6 (weakenTrace d13 (domainCtx G0)) (appendCtx G1 G0) (appendCtx G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Ctx) (S5 : Ty) : (Trace TyVar) -> Ctx -> Ctx -> Prop :=
    | subst_etvar_here :
        (subst_etvar G S5 X0 (etvar G) G)
    | subst_etvar_there_evar
        {d13 : (Trace TyVar)} {G0 : Ctx}
        {G1 : Ctx} (T6 : Ty) :
        (subst_etvar G S5 d13 G0 G1) -> (subst_etvar G S5 (XS TmVar d13) (evar G0 T6) (evar G1 (subst_TyVar_Ty d13 S5 T6)))
    | subst_etvar_there_etvar
        {d13 : (Trace TyVar)} {G0 : Ctx}
        {G1 : Ctx} :
        (subst_etvar G S5 d13 G0 G1) -> (subst_etvar G S5 (XS TyVar d13) (etvar G0) (etvar G1)).
  Lemma weaken_subst_etvar {G : Ctx} {S5 : Ty} :
    (forall (G0 : Ctx) {d13 : (Trace TyVar)} {G1 : Ctx} {G2 : Ctx} ,
      (subst_etvar G S5 d13 G1 G2) -> (subst_etvar G S5 (weakenTrace d13 (domainCtx G0)) (appendCtx G1 G0) (appendCtx G2 (subst_TyVar_Ctx d13 S5 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_TmVar {G : Ctx} {s6 : Tm} (T6 : Ty) :
    (forall {d13 : (Trace TmVar)} {G0 : Ctx} {G1 : Ctx} ,
      (subst_evar G T6 s6 d13 G0 G1) -> (substhvl_TmVar (domainCtx G) d13 (domainCtx G0) (domainCtx G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_TyVar {G : Ctx} {S5 : Ty} :
    (forall {d13 : (Trace TyVar)} {G0 : Ctx} {G1 : Ctx} ,
      (subst_etvar G S5 d13 G0 G1) -> (substhvl_TyVar (domainCtx G) d13 (domainCtx G0) (domainCtx G1))).
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
    (lookup_evar (appendCtx (evar G T6) G0) (weakenIndexTmVar I0 (domainCtx G0)) (weakenTy T6 (domainCtx G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Ctx} (G0 : Ctx) ,
    (lookup_etvar (appendCtx (etvar G) G0) (weakenIndexTyVar I0 (domainCtx G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfDecls wfTm wfTy : infra.
 Hint Constructors wfDecls wfTm wfTy : wf.
 Hint Extern 10 ((wfDecls _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H32 : (wfTy _ (TVar _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTy _ (TArr _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTy _ (TAll _)) |- _ => inversion H32; subst; clear H32
end : infra wf.
 Hint Extern 2 ((wfDecls _ _)) => match goal with
  | H32 : (wfDecls _ (DNil)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfDecls _ (DCons _ _)) |- _ => inversion H32; subst; clear H32
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H32 : (wfTm _ (Var _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (Abs _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (App _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (TAbs _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (TApp _ _)) |- _ => inversion H32; subst; clear H32
  | H32 : (wfTm _ (Let _ _)) |- _ => inversion H32; subst; clear H32
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
  (forall {c1 : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evar c1 G G0)) {x7 : (Index TmVar)} {T6 : Ty} ,
    (lookup_evar G x7 T6) -> (lookup_evar G0 (shift_TmVar_Index c1 x7) T6)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c1 : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evar c1 G G0)) {X7 : (Index TyVar)} ,
    (lookup_etvar G X7) -> (lookup_etvar G0 X7)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c1 : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_etvar c1 G G0)) {x7 : (Index TmVar)} {T6 : Ty} ,
    (lookup_evar G x7 T6) -> (lookup_evar G0 x7 (shift_TyVar_Ty c1 T6))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c1 : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_etvar c1 G G0)) {X7 : (Index TyVar)} ,
    (lookup_etvar G X7) -> (lookup_etvar G0 (shift_TyVar_Index c1 X7))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Ctx} (T7 : Ty) {s6 : Tm} :
  (forall {d13 : (Trace TmVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_evar G T7 s6 d13 G0 G1)) {X7 : (Index TyVar)} ,
    (lookup_etvar G0 X7) -> (lookup_etvar G1 X7)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Ctx} {S5 : Ty} (wf : (wfTy (domainCtx G) S5)) :
  (forall {d13 : (Trace TyVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_etvar G S5 d13 G0 G1)) {x7 : (Index TmVar)} (T7 : Ty) ,
    (lookup_evar G0 x7 T7) -> (lookup_evar G1 x7 (subst_TyVar_Ty d13 S5 T7))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (TVar X7) => 1
    | (TArr T5 T6) => (plus 1 (plus (size_Ty T5) (size_Ty T6)))
    | (TAll T7) => (plus 1 (size_Ty T7))
  end.
Fixpoint size_Decls (d5 : Decls) {struct d5} :
nat :=
  match d5 with
    | (DNil) => 1
    | (DCons t7 d6) => (plus 1 (plus (size_Tm t7) (size_Decls d6)))
  end
with size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (Var x7) => 1
    | (Abs T5 t7) => (plus 1 (plus (size_Ty T5) (size_Tm t7)))
    | (App t8 t9) => (plus 1 (plus (size_Tm t8) (size_Tm t9)))
    | (TAbs t10) => (plus 1 (size_Tm t10))
    | (TApp t11 T6) => (plus 1 (plus (size_Tm t11) (size_Ty T6)))
    | (Let d5 t12) => (plus 1 (plus (size_Decls d5) (size_Tm t12)))
  end.
Fixpoint shift_TyVar__size_Ty (S1 : Ty) (c1 : (Cutoff TyVar)) {struct S1} :
((size_Ty (shift_TyVar_Ty c1 S1)) = (size_Ty S1)) :=
  match S1 return ((size_Ty (shift_TyVar_Ty c1 S1)) = (size_Ty S1)) with
    | (TVar _) => eq_refl
    | (TArr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T1 c1) (shift_TyVar__size_Ty T2 c1)))
    | (TAll T) => (f_equal2 plus eq_refl (shift_TyVar__size_Ty T (CS c1)))
  end.
Fixpoint shift_TmVar__size_Decls (d11 : Decls) (c1 : (Cutoff TmVar)) {struct d11} :
((size_Decls (shift_TmVar_Decls c1 d11)) = (size_Decls d11)) :=
  match d11 return ((size_Decls (shift_TmVar_Decls c1 d11)) = (size_Decls d11)) with
    | (DNil) => eq_refl
    | (DCons t d) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t c1) (shift_TmVar__size_Decls d (CS c1))))
  end
with shift_TmVar__size_Tm (s0 : Tm) (c1 : (Cutoff TmVar)) {struct s0} :
((size_Tm (shift_TmVar_Tm c1 s0)) = (size_Tm s0)) :=
  match s0 return ((size_Tm (shift_TmVar_Tm c1 s0)) = (size_Tm s0)) with
    | (Var _) => eq_refl
    | (Abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_TmVar__size_Tm t (CS c1))))
    | (App t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t1 c1) (shift_TmVar__size_Tm t2 c1)))
    | (TAbs t) => (f_equal2 plus eq_refl (shift_TmVar__size_Tm t c1))
    | (TApp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t c1) eq_refl))
    | (Let d t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Decls d c1) (shift_TmVar__size_Tm t (weakenCutoffTmVar c1 (appendHvl H0 (bind d))))))
  end.
Fixpoint shift_TyVar__size_Decls (d11 : Decls) (c1 : (Cutoff TyVar)) {struct d11} :
((size_Decls (shift_TyVar_Decls c1 d11)) = (size_Decls d11)) :=
  match d11 return ((size_Decls (shift_TyVar_Decls c1 d11)) = (size_Decls d11)) with
    | (DNil) => eq_refl
    | (DCons t d) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Tm t c1) (shift_TyVar__size_Decls d c1)))
  end
with shift_TyVar__size_Tm (s0 : Tm) (c1 : (Cutoff TyVar)) {struct s0} :
((size_Tm (shift_TyVar_Tm c1 s0)) = (size_Tm s0)) :=
  match s0 return ((size_Tm (shift_TyVar_Tm c1 s0)) = (size_Tm s0)) with
    | (Var _) => eq_refl
    | (Abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Ty T c1) (shift_TyVar__size_Tm t c1)))
    | (App t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Tm t1 c1) (shift_TyVar__size_Tm t2 c1)))
    | (TAbs t) => (f_equal2 plus eq_refl (shift_TyVar__size_Tm t (CS c1)))
    | (TApp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Tm t c1) (shift_TyVar__size_Ty T c1)))
    | (Let d t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TyVar__size_Decls d c1) (shift_TyVar__size_Tm t (weakenCutoffTyVar c1 (appendHvl H0 (bind d))))))
  end.
 Hint Rewrite shift_TmVar__size_Decls shift_TyVar__size_Decls shift_TmVar__size_Tm shift_TyVar__size_Tm shift_TyVar__size_Ty : interaction.
 Hint Rewrite shift_TmVar__size_Decls shift_TyVar__size_Decls shift_TmVar__size_Tm shift_TyVar__size_Tm shift_TyVar__size_Ty : shift_size.
Lemma weaken_size_Decls  :
  (forall (k : Hvl) (d11 : Decls) ,
    ((size_Decls (weakenDecls d11 k)) = (size_Decls d11))).
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
 Hint Rewrite weaken_size_Decls weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Decls weaken_size_Tm weaken_size_Ty : weaken_size.
 Hint Rewrite appendCtx_assoc : interaction.
 Hint Rewrite <- weakenCutoffTmVar_append weakenCutoffTyVar_append weakenTrace_append weakenDecls_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.