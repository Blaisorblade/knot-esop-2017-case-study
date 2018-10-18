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
  
  Fixpoint weakenIndexTmVar (x51 : (Index TmVar)) (k : Hvl) {struct k} :
  (Index TmVar) :=
    match k with
      | (H0) => x51
      | (HS a k) => match a with
        | (TmVar) => (IS (weakenIndexTmVar x51 k))
        | _ => (weakenIndexTmVar x51 k)
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
    (forall (x51 : (Index TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTmVar (weakenIndexTmVar x51 k) k0) = (weakenIndexTmVar x51 (appendHvl k k0)))).
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
    | all (T : Ty) (t : Tm)
  with Ty : Set :=
    | tvar (X : (Index TyVar))
    | tpi (T1 : Ty) (T2 : Ty)
    | tapp (T : Ty) (t : Tm)
    | prop 
    | prf .
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
  Fixpoint shiftIndex (c : (Cutoff TmVar)) (x51 : (Index TmVar)) {struct c} :
  (Index TmVar) :=
    match c with
      | (C0) => (IS x51)
      | (CS c) => match x51 with
        | (I0) => I0
        | (IS x51) => (IS (shiftIndex c x51))
      end
    end.
  Fixpoint tshiftIndex (c : (Cutoff TyVar)) (X5 : (Index TyVar)) {struct c} :
  (Index TyVar) :=
    match c with
      | (C0) => (IS X5)
      | (CS c) => match X5 with
        | (I0) => I0
        | (IS X5) => (IS (tshiftIndex c X5))
      end
    end.
  Fixpoint shiftTm (c : (Cutoff TmVar)) (s11 : Tm) {struct s11} :
  Tm :=
    match s11 with
      | (var x51) => (var (shiftIndex c x51))
      | (abs T73 t51) => (abs (shiftTy c T73) (shiftTm (CS c) t51))
      | (app t52 t53) => (app (shiftTm c t52) (shiftTm c t53))
      | (all T74 t54) => (all (shiftTy c T74) (shiftTm (CS c) t54))
    end
  with shiftTy (c : (Cutoff TmVar)) (S34 : Ty) {struct S34} :
  Ty :=
    match S34 with
      | (tvar X5) => (tvar X5)
      | (tpi T73 T74) => (tpi (shiftTy c T73) (shiftTy (CS c) T74))
      | (tapp T75 t51) => (tapp (shiftTy c T75) (shiftTm c t51))
      | (prop) => (prop)
      | (prf) => (prf)
    end.
  Fixpoint tshiftTm (c : (Cutoff TyVar)) (s11 : Tm) {struct s11} :
  Tm :=
    match s11 with
      | (var x51) => (var x51)
      | (abs T73 t51) => (abs (tshiftTy c T73) (tshiftTm c t51))
      | (app t52 t53) => (app (tshiftTm c t52) (tshiftTm c t53))
      | (all T74 t54) => (all (tshiftTy c T74) (tshiftTm c t54))
    end
  with tshiftTy (c : (Cutoff TyVar)) (S34 : Ty) {struct S34} :
  Ty :=
    match S34 with
      | (tvar X5) => (tvar (tshiftIndex c X5))
      | (tpi T73 T74) => (tpi (tshiftTy c T73) (tshiftTy c T74))
      | (tapp T75 t51) => (tapp (tshiftTy c T75) (tshiftTm c t51))
      | (prop) => (prop)
      | (prf) => (prf)
    end.
  Fixpoint shiftKind (c : (Cutoff TmVar)) (K42 : Kind) {struct K42} :
  Kind :=
    match K42 with
      | (star) => (star)
      | (kpi T73 K43) => (kpi (shiftTy c T73) (shiftKind (CS c) K43))
    end.
  Fixpoint tshiftKind (c : (Cutoff TyVar)) (K42 : Kind) {struct K42} :
  Kind :=
    match K42 with
      | (star) => (star)
      | (kpi T73 K43) => (kpi (tshiftTy c T73) (tshiftKind c K43))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTm (s11 : Tm) (k : Hvl) {struct k} :
  Tm :=
    match k with
      | (H0) => s11
      | (HS TmVar k) => (shiftTm C0 (weakenTm s11 k))
      | (HS TyVar k) => (tshiftTm C0 (weakenTm s11 k))
    end.
  Fixpoint weakenTy (S34 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S34
      | (HS TmVar k) => (shiftTy C0 (weakenTy S34 k))
      | (HS TyVar k) => (tshiftTy C0 (weakenTy S34 k))
    end.
  Fixpoint weakenKind (K42 : Kind) (k : Hvl) {struct k} :
  Kind :=
    match k with
      | (H0) => K42
      | (HS TmVar k) => (shiftKind C0 (weakenKind K42 k))
      | (HS TyVar k) => (tshiftKind C0 (weakenKind K42 k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T73 : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x51 : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x51
      | (HS b k) => (XS b (weakenTrace x51 k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x51 : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x51 k) k0) = (weakenTrace x51 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint substIndex (d : (Trace TmVar)) (s11 : Tm) (x51 : (Index TmVar)) {struct d} :
  Tm :=
    match d with
      | (X0) => match x51 with
        | (I0) => s11
        | (IS x51) => (var x51)
      end
      | (XS TmVar d) => match x51 with
        | (I0) => (var I0)
        | (IS x51) => (shiftTm C0 (substIndex d s11 x51))
      end
      | (XS TyVar d) => (tshiftTm C0 (substIndex d s11 x51))
    end.
  Fixpoint tsubstIndex (d : (Trace TyVar)) (S34 : Ty) (X5 : (Index TyVar)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X5 with
        | (I0) => S34
        | (IS X5) => (tvar X5)
      end
      | (XS TmVar d) => (shiftTy C0 (tsubstIndex d S34 X5))
      | (XS TyVar d) => match X5 with
        | (I0) => (tvar I0)
        | (IS X5) => (tshiftTy C0 (tsubstIndex d S34 X5))
      end
    end.
  Fixpoint substTm (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) {struct s12} :
  Tm :=
    match s12 with
      | (var x51) => (substIndex d s11 x51)
      | (abs T73 t51) => (abs (substTy d s11 T73) (substTm (weakenTrace d (HS TmVar H0)) s11 t51))
      | (app t52 t53) => (app (substTm d s11 t52) (substTm d s11 t53))
      | (all T74 t54) => (all (substTy d s11 T74) (substTm (weakenTrace d (HS TmVar H0)) s11 t54))
    end
  with substTy (d : (Trace TmVar)) (s11 : Tm) (S34 : Ty) {struct S34} :
  Ty :=
    match S34 with
      | (tvar X5) => (tvar X5)
      | (tpi T73 T74) => (tpi (substTy d s11 T73) (substTy (weakenTrace d (HS TmVar H0)) s11 T74))
      | (tapp T75 t51) => (tapp (substTy d s11 T75) (substTm d s11 t51))
      | (prop) => (prop)
      | (prf) => (prf)
    end.
  Fixpoint tsubstTm (d : (Trace TyVar)) (S34 : Ty) (s11 : Tm) {struct s11} :
  Tm :=
    match s11 with
      | (var x51) => (var x51)
      | (abs T73 t51) => (abs (tsubstTy d S34 T73) (tsubstTm (weakenTrace d (HS TmVar H0)) S34 t51))
      | (app t52 t53) => (app (tsubstTm d S34 t52) (tsubstTm d S34 t53))
      | (all T74 t54) => (all (tsubstTy d S34 T74) (tsubstTm (weakenTrace d (HS TmVar H0)) S34 t54))
    end
  with tsubstTy (d : (Trace TyVar)) (S34 : Ty) (S35 : Ty) {struct S35} :
  Ty :=
    match S35 with
      | (tvar X5) => (tsubstIndex d S34 X5)
      | (tpi T73 T74) => (tpi (tsubstTy d S34 T73) (tsubstTy (weakenTrace d (HS TmVar H0)) S34 T74))
      | (tapp T75 t51) => (tapp (tsubstTy d S34 T75) (tsubstTm d S34 t51))
      | (prop) => (prop)
      | (prf) => (prf)
    end.
  Fixpoint substKind (d : (Trace TmVar)) (s11 : Tm) (K42 : Kind) {struct K42} :
  Kind :=
    match K42 with
      | (star) => (star)
      | (kpi T73 K43) => (kpi (substTy d s11 T73) (substKind (weakenTrace d (HS TmVar H0)) s11 K43))
    end.
  Fixpoint tsubstKind (d : (Trace TyVar)) (S34 : Ty) (K42 : Kind) {struct K42} :
  Kind :=
    match K42 with
      | (star) => (star)
      | (kpi T73 K43) => (kpi (tsubstTy d S34 T73) (tsubstKind (weakenTrace d (HS TmVar H0)) S34 K43))
    end.
End Subst.

Global Hint Resolve (f_equal (shiftKind C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftKind C0)) : cong_shift0.
Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (shiftTy C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutoffTmVar_append weakenCutoffTyVar_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s11 : Tm) :
    (forall (k : Hvl) (x51 : (Index TmVar)) ,
      ((substIndex (weakenTrace X0 k) s11 (shiftIndex (weakenCutoffTmVar C0 k) x51)) = (var x51))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S34 : Ty) :
    (forall (k : Hvl) (X5 : (Index TyVar)) ,
      ((tsubstIndex (weakenTrace X0 k) S34 (tshiftIndex (weakenCutoffTyVar C0 k) X5)) = (tvar X5))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst0_shift0_Tm_reflection_ind (s12 : Tm) (k : Hvl) (s11 : Tm) {struct s12} :
  ((substTm (weakenTrace X0 k) s11 (shiftTm (weakenCutoffTmVar C0 k) s12)) = s12) :=
    match s12 return ((substTm (weakenTrace X0 k) s11 (shiftTm (weakenCutoffTmVar C0 k) s12)) = s12) with
      | (var x51) => (substIndex0_shiftIndex0_reflection_ind s11 k x51)
      | (abs T73 t51) => (f_equal2 abs (subst0_shift0_Ty_reflection_ind T73 k s11) (eq_trans (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t51 (HS TmVar k) s11)))
      | (app t52 t53) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t52 k s11) (subst0_shift0_Tm_reflection_ind t53 k s11))
      | (all T73 t51) => (f_equal2 all (subst0_shift0_Ty_reflection_ind T73 k s11) (eq_trans (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t51 (HS TmVar k) s11)))
    end
  with subst0_shift0_Ty_reflection_ind (S34 : Ty) (k : Hvl) (s11 : Tm) {struct S34} :
  ((substTy (weakenTrace X0 k) s11 (shiftTy (weakenCutoffTmVar C0 k) S34)) = S34) :=
    match S34 return ((substTy (weakenTrace X0 k) s11 (shiftTy (weakenCutoffTmVar C0 k) S34)) = S34) with
      | (tvar X5) => eq_refl
      | (tpi T75 T76) => (f_equal2 tpi (subst0_shift0_Ty_reflection_ind T75 k s11) (eq_trans (f_equal3 substTy (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst0_shift0_Ty_reflection_ind T76 (HS TmVar k) s11)))
      | (tapp T74 t54) => (f_equal2 tapp (subst0_shift0_Ty_reflection_ind T74 k s11) (subst0_shift0_Tm_reflection_ind t54 k s11))
      | (prop) => eq_refl
      | (prf) => eq_refl
    end.
  Fixpoint tsubst0_tshift0_Tm_reflection_ind (s11 : Tm) (k : Hvl) (S34 : Ty) {struct s11} :
  ((tsubstTm (weakenTrace X0 k) S34 (tshiftTm (weakenCutoffTyVar C0 k) s11)) = s11) :=
    match s11 return ((tsubstTm (weakenTrace X0 k) S34 (tshiftTm (weakenCutoffTyVar C0 k) s11)) = s11) with
      | (var x51) => eq_refl
      | (abs T73 t51) => (f_equal2 abs (tsubst0_tshift0_Ty_reflection_ind T73 k S34) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t51 (HS TmVar k) S34)))
      | (app t52 t53) => (f_equal2 app (tsubst0_tshift0_Tm_reflection_ind t52 k S34) (tsubst0_tshift0_Tm_reflection_ind t53 k S34))
      | (all T73 t51) => (f_equal2 all (tsubst0_tshift0_Ty_reflection_ind T73 k S34) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t51 (HS TmVar k) S34)))
    end
  with tsubst0_tshift0_Ty_reflection_ind (S35 : Ty) (k : Hvl) (S34 : Ty) {struct S35} :
  ((tsubstTy (weakenTrace X0 k) S34 (tshiftTy (weakenCutoffTyVar C0 k) S35)) = S35) :=
    match S35 return ((tsubstTy (weakenTrace X0 k) S34 (tshiftTy (weakenCutoffTyVar C0 k) S35)) = S35) with
      | (tvar X5) => (tsubstIndex0_tshiftIndex0_reflection_ind S34 k X5)
      | (tpi T75 T76) => (f_equal2 tpi (tsubst0_tshift0_Ty_reflection_ind T75 k S34) (eq_trans (f_equal3 tsubstTy (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T76 (HS TmVar k) S34)))
      | (tapp T74 t54) => (f_equal2 tapp (tsubst0_tshift0_Ty_reflection_ind T74 k S34) (tsubst0_tshift0_Tm_reflection_ind t54 k S34))
      | (prop) => eq_refl
      | (prf) => eq_refl
    end.
  Fixpoint subst0_shift0_Kind_reflection_ind (K42 : Kind) (k : Hvl) (s11 : Tm) {struct K42} :
  ((substKind (weakenTrace X0 k) s11 (shiftKind (weakenCutoffTmVar C0 k) K42)) = K42) :=
    match K42 return ((substKind (weakenTrace X0 k) s11 (shiftKind (weakenCutoffTmVar C0 k) K42)) = K42) with
      | (star) => eq_refl
      | (kpi T73 K43) => (f_equal2 kpi (subst0_shift0_Ty_reflection_ind T73 k s11) (eq_trans (f_equal3 substKind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst0_shift0_Kind_reflection_ind K43 (HS TmVar k) s11)))
    end.
  Fixpoint tsubst0_tshift0_Kind_reflection_ind (K42 : Kind) (k : Hvl) (S34 : Ty) {struct K42} :
  ((tsubstKind (weakenTrace X0 k) S34 (tshiftKind (weakenCutoffTyVar C0 k) K42)) = K42) :=
    match K42 return ((tsubstKind (weakenTrace X0 k) S34 (tshiftKind (weakenCutoffTyVar C0 k) K42)) = K42) with
      | (star) => eq_refl
      | (kpi T73 K43) => (f_equal2 kpi (tsubst0_tshift0_Ty_reflection_ind T73 k S34) (eq_trans (f_equal3 tsubstKind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (tsubst0_tshift0_Kind_reflection_ind K43 (HS TmVar k) S34)))
    end.
  Definition substTm0_shiftTm0_reflection (s12 : Tm) : (forall (s11 : Tm) ,
    ((substTm X0 s11 (shiftTm C0 s12)) = s12)) := (subst0_shift0_Tm_reflection_ind s12 H0).
  Definition substTy0_shiftTy0_reflection (S34 : Ty) : (forall (s11 : Tm) ,
    ((substTy X0 s11 (shiftTy C0 S34)) = S34)) := (subst0_shift0_Ty_reflection_ind S34 H0).
  Definition tsubstTm0_tshiftTm0_reflection (s11 : Tm) : (forall (S34 : Ty) ,
    ((tsubstTm X0 S34 (tshiftTm C0 s11)) = s11)) := (tsubst0_tshift0_Tm_reflection_ind s11 H0).
  Definition tsubstTy0_tshiftTy0_reflection (S35 : Ty) : (forall (S34 : Ty) ,
    ((tsubstTy X0 S34 (tshiftTy C0 S35)) = S35)) := (tsubst0_tshift0_Ty_reflection_ind S35 H0).
  Definition substKind0_shiftKind0_reflection (K42 : Kind) : (forall (s11 : Tm) ,
    ((substKind X0 s11 (shiftKind C0 K42)) = K42)) := (subst0_shift0_Kind_reflection_ind K42 H0).
  Definition tsubstKind0_tshiftKind0_reflection (K42 : Kind) : (forall (S34 : Ty) ,
    ((tsubstKind X0 S34 (tshiftKind C0 K42)) = K42)) := (tsubst0_tshift0_Kind_reflection_ind K42 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff TmVar)) (x51 : (Index TmVar)) ,
        ((shiftIndex (weakenCutoffTmVar (CS c) k) (shiftIndex (weakenCutoffTmVar C0 k) x51)) = (shiftIndex (weakenCutoffTmVar C0 k) (shiftIndex (weakenCutoffTmVar c k) x51)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff TyVar)) (X5 : (Index TyVar)) ,
        ((tshiftIndex (weakenCutoffTyVar (CS c) k) (tshiftIndex (weakenCutoffTyVar C0 k) X5)) = (tshiftIndex (weakenCutoffTyVar C0 k) (tshiftIndex (weakenCutoffTyVar c k) X5)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint shift_shift0_Tm_comm_ind (s11 : Tm) (k : Hvl) (c : (Cutoff TmVar)) {struct s11} :
    ((shiftTm (weakenCutoffTmVar (CS c) k) (shiftTm (weakenCutoffTmVar C0 k) s11)) = (shiftTm (weakenCutoffTmVar C0 k) (shiftTm (weakenCutoffTmVar c k) s11))) :=
      match s11 return ((shiftTm (weakenCutoffTmVar (CS c) k) (shiftTm (weakenCutoffTmVar C0 k) s11)) = (shiftTm (weakenCutoffTmVar C0 k) (shiftTm (weakenCutoffTmVar c k) s11))) with
        | (var x51) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c x51))
        | (abs T73 t51) => (f_equal2 abs (shift_shift0_Ty_comm_ind T73 k c) (shift_shift0_Tm_comm_ind t51 (HS TmVar k) c))
        | (app t52 t53) => (f_equal2 app (shift_shift0_Tm_comm_ind t52 k c) (shift_shift0_Tm_comm_ind t53 k c))
        | (all T73 t51) => (f_equal2 all (shift_shift0_Ty_comm_ind T73 k c) (shift_shift0_Tm_comm_ind t51 (HS TmVar k) c))
      end
    with shift_shift0_Ty_comm_ind (S34 : Ty) (k : Hvl) (c : (Cutoff TmVar)) {struct S34} :
    ((shiftTy (weakenCutoffTmVar (CS c) k) (shiftTy (weakenCutoffTmVar C0 k) S34)) = (shiftTy (weakenCutoffTmVar C0 k) (shiftTy (weakenCutoffTmVar c k) S34))) :=
      match S34 return ((shiftTy (weakenCutoffTmVar (CS c) k) (shiftTy (weakenCutoffTmVar C0 k) S34)) = (shiftTy (weakenCutoffTmVar C0 k) (shiftTy (weakenCutoffTmVar c k) S34))) with
        | (tvar X5) => eq_refl
        | (tpi T75 T76) => (f_equal2 tpi (shift_shift0_Ty_comm_ind T75 k c) (shift_shift0_Ty_comm_ind T76 (HS TmVar k) c))
        | (tapp T74 t54) => (f_equal2 tapp (shift_shift0_Ty_comm_ind T74 k c) (shift_shift0_Tm_comm_ind t54 k c))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint shift_tshift0_Tm_comm_ind (s11 : Tm) (k : Hvl) (c : (Cutoff TmVar)) {struct s11} :
    ((shiftTm (weakenCutoffTmVar c k) (tshiftTm (weakenCutoffTyVar C0 k) s11)) = (tshiftTm (weakenCutoffTyVar C0 k) (shiftTm (weakenCutoffTmVar c k) s11))) :=
      match s11 return ((shiftTm (weakenCutoffTmVar c k) (tshiftTm (weakenCutoffTyVar C0 k) s11)) = (tshiftTm (weakenCutoffTyVar C0 k) (shiftTm (weakenCutoffTmVar c k) s11))) with
        | (var x51) => eq_refl
        | (abs T73 t51) => (f_equal2 abs (shift_tshift0_Ty_comm_ind T73 k c) (shift_tshift0_Tm_comm_ind t51 (HS TmVar k) c))
        | (app t52 t53) => (f_equal2 app (shift_tshift0_Tm_comm_ind t52 k c) (shift_tshift0_Tm_comm_ind t53 k c))
        | (all T73 t51) => (f_equal2 all (shift_tshift0_Ty_comm_ind T73 k c) (shift_tshift0_Tm_comm_ind t51 (HS TmVar k) c))
      end
    with shift_tshift0_Ty_comm_ind (S34 : Ty) (k : Hvl) (c : (Cutoff TmVar)) {struct S34} :
    ((shiftTy (weakenCutoffTmVar c k) (tshiftTy (weakenCutoffTyVar C0 k) S34)) = (tshiftTy (weakenCutoffTyVar C0 k) (shiftTy (weakenCutoffTmVar c k) S34))) :=
      match S34 return ((shiftTy (weakenCutoffTmVar c k) (tshiftTy (weakenCutoffTyVar C0 k) S34)) = (tshiftTy (weakenCutoffTyVar C0 k) (shiftTy (weakenCutoffTmVar c k) S34))) with
        | (tvar X5) => eq_refl
        | (tpi T75 T76) => (f_equal2 tpi (shift_tshift0_Ty_comm_ind T75 k c) (shift_tshift0_Ty_comm_ind T76 (HS TmVar k) c))
        | (tapp T74 t54) => (f_equal2 tapp (shift_tshift0_Ty_comm_ind T74 k c) (shift_tshift0_Tm_comm_ind t54 k c))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint tshift_shift0_Tm_comm_ind (s11 : Tm) (k : Hvl) (c : (Cutoff TyVar)) {struct s11} :
    ((tshiftTm (weakenCutoffTyVar c k) (shiftTm (weakenCutoffTmVar C0 k) s11)) = (shiftTm (weakenCutoffTmVar C0 k) (tshiftTm (weakenCutoffTyVar c k) s11))) :=
      match s11 return ((tshiftTm (weakenCutoffTyVar c k) (shiftTm (weakenCutoffTmVar C0 k) s11)) = (shiftTm (weakenCutoffTmVar C0 k) (tshiftTm (weakenCutoffTyVar c k) s11))) with
        | (var x51) => eq_refl
        | (abs T73 t51) => (f_equal2 abs (tshift_shift0_Ty_comm_ind T73 k c) (tshift_shift0_Tm_comm_ind t51 (HS TmVar k) c))
        | (app t52 t53) => (f_equal2 app (tshift_shift0_Tm_comm_ind t52 k c) (tshift_shift0_Tm_comm_ind t53 k c))
        | (all T73 t51) => (f_equal2 all (tshift_shift0_Ty_comm_ind T73 k c) (tshift_shift0_Tm_comm_ind t51 (HS TmVar k) c))
      end
    with tshift_shift0_Ty_comm_ind (S34 : Ty) (k : Hvl) (c : (Cutoff TyVar)) {struct S34} :
    ((tshiftTy (weakenCutoffTyVar c k) (shiftTy (weakenCutoffTmVar C0 k) S34)) = (shiftTy (weakenCutoffTmVar C0 k) (tshiftTy (weakenCutoffTyVar c k) S34))) :=
      match S34 return ((tshiftTy (weakenCutoffTyVar c k) (shiftTy (weakenCutoffTmVar C0 k) S34)) = (shiftTy (weakenCutoffTmVar C0 k) (tshiftTy (weakenCutoffTyVar c k) S34))) with
        | (tvar X5) => eq_refl
        | (tpi T75 T76) => (f_equal2 tpi (tshift_shift0_Ty_comm_ind T75 k c) (tshift_shift0_Ty_comm_ind T76 (HS TmVar k) c))
        | (tapp T74 t54) => (f_equal2 tapp (tshift_shift0_Ty_comm_ind T74 k c) (tshift_shift0_Tm_comm_ind t54 k c))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint tshift_tshift0_Tm_comm_ind (s11 : Tm) (k : Hvl) (c : (Cutoff TyVar)) {struct s11} :
    ((tshiftTm (weakenCutoffTyVar (CS c) k) (tshiftTm (weakenCutoffTyVar C0 k) s11)) = (tshiftTm (weakenCutoffTyVar C0 k) (tshiftTm (weakenCutoffTyVar c k) s11))) :=
      match s11 return ((tshiftTm (weakenCutoffTyVar (CS c) k) (tshiftTm (weakenCutoffTyVar C0 k) s11)) = (tshiftTm (weakenCutoffTyVar C0 k) (tshiftTm (weakenCutoffTyVar c k) s11))) with
        | (var x51) => eq_refl
        | (abs T73 t51) => (f_equal2 abs (tshift_tshift0_Ty_comm_ind T73 k c) (tshift_tshift0_Tm_comm_ind t51 (HS TmVar k) c))
        | (app t52 t53) => (f_equal2 app (tshift_tshift0_Tm_comm_ind t52 k c) (tshift_tshift0_Tm_comm_ind t53 k c))
        | (all T73 t51) => (f_equal2 all (tshift_tshift0_Ty_comm_ind T73 k c) (tshift_tshift0_Tm_comm_ind t51 (HS TmVar k) c))
      end
    with tshift_tshift0_Ty_comm_ind (S34 : Ty) (k : Hvl) (c : (Cutoff TyVar)) {struct S34} :
    ((tshiftTy (weakenCutoffTyVar (CS c) k) (tshiftTy (weakenCutoffTyVar C0 k) S34)) = (tshiftTy (weakenCutoffTyVar C0 k) (tshiftTy (weakenCutoffTyVar c k) S34))) :=
      match S34 return ((tshiftTy (weakenCutoffTyVar (CS c) k) (tshiftTy (weakenCutoffTyVar C0 k) S34)) = (tshiftTy (weakenCutoffTyVar C0 k) (tshiftTy (weakenCutoffTyVar c k) S34))) with
        | (tvar X5) => (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k c X5))
        | (tpi T75 T76) => (f_equal2 tpi (tshift_tshift0_Ty_comm_ind T75 k c) (tshift_tshift0_Ty_comm_ind T76 (HS TmVar k) c))
        | (tapp T74 t54) => (f_equal2 tapp (tshift_tshift0_Ty_comm_ind T74 k c) (tshift_tshift0_Tm_comm_ind t54 k c))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint shift_shift0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TmVar)) {struct K42} :
    ((shiftKind (weakenCutoffTmVar (CS c) k) (shiftKind (weakenCutoffTmVar C0 k) K42)) = (shiftKind (weakenCutoffTmVar C0 k) (shiftKind (weakenCutoffTmVar c k) K42))) :=
      match K42 return ((shiftKind (weakenCutoffTmVar (CS c) k) (shiftKind (weakenCutoffTmVar C0 k) K42)) = (shiftKind (weakenCutoffTmVar C0 k) (shiftKind (weakenCutoffTmVar c k) K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (shift_shift0_Ty_comm_ind T73 k c) (shift_shift0_Kind_comm_ind K43 (HS TmVar k) c))
      end.
    Fixpoint shift_tshift0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TmVar)) {struct K42} :
    ((shiftKind (weakenCutoffTmVar c k) (tshiftKind (weakenCutoffTyVar C0 k) K42)) = (tshiftKind (weakenCutoffTyVar C0 k) (shiftKind (weakenCutoffTmVar c k) K42))) :=
      match K42 return ((shiftKind (weakenCutoffTmVar c k) (tshiftKind (weakenCutoffTyVar C0 k) K42)) = (tshiftKind (weakenCutoffTyVar C0 k) (shiftKind (weakenCutoffTmVar c k) K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (shift_tshift0_Ty_comm_ind T73 k c) (shift_tshift0_Kind_comm_ind K43 (HS TmVar k) c))
      end.
    Fixpoint tshift_shift0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TyVar)) {struct K42} :
    ((tshiftKind (weakenCutoffTyVar c k) (shiftKind (weakenCutoffTmVar C0 k) K42)) = (shiftKind (weakenCutoffTmVar C0 k) (tshiftKind (weakenCutoffTyVar c k) K42))) :=
      match K42 return ((tshiftKind (weakenCutoffTyVar c k) (shiftKind (weakenCutoffTmVar C0 k) K42)) = (shiftKind (weakenCutoffTmVar C0 k) (tshiftKind (weakenCutoffTyVar c k) K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (tshift_shift0_Ty_comm_ind T73 k c) (tshift_shift0_Kind_comm_ind K43 (HS TmVar k) c))
      end.
    Fixpoint tshift_tshift0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TyVar)) {struct K42} :
    ((tshiftKind (weakenCutoffTyVar (CS c) k) (tshiftKind (weakenCutoffTyVar C0 k) K42)) = (tshiftKind (weakenCutoffTyVar C0 k) (tshiftKind (weakenCutoffTyVar c k) K42))) :=
      match K42 return ((tshiftKind (weakenCutoffTyVar (CS c) k) (tshiftKind (weakenCutoffTyVar C0 k) K42)) = (tshiftKind (weakenCutoffTyVar C0 k) (tshiftKind (weakenCutoffTyVar c k) K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (tshift_tshift0_Ty_comm_ind T73 k c) (tshift_tshift0_Kind_comm_ind K43 (HS TmVar k) c))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition shift_shift0_Tm_comm (s11 : Tm) : (forall (c : (Cutoff TmVar)) ,
      ((shiftTm (CS c) (shiftTm C0 s11)) = (shiftTm C0 (shiftTm c s11)))) := (shift_shift0_Tm_comm_ind s11 H0).
    Definition shift_shift0_Ty_comm (S34 : Ty) : (forall (c : (Cutoff TmVar)) ,
      ((shiftTy (CS c) (shiftTy C0 S34)) = (shiftTy C0 (shiftTy c S34)))) := (shift_shift0_Ty_comm_ind S34 H0).
    Definition shift_tshift0_Tm_comm (s11 : Tm) : (forall (c : (Cutoff TmVar)) ,
      ((shiftTm c (tshiftTm C0 s11)) = (tshiftTm C0 (shiftTm c s11)))) := (shift_tshift0_Tm_comm_ind s11 H0).
    Definition shift_tshift0_Ty_comm (S34 : Ty) : (forall (c : (Cutoff TmVar)) ,
      ((shiftTy c (tshiftTy C0 S34)) = (tshiftTy C0 (shiftTy c S34)))) := (shift_tshift0_Ty_comm_ind S34 H0).
    Definition tshift_shift0_Tm_comm (s11 : Tm) : (forall (c : (Cutoff TyVar)) ,
      ((tshiftTm c (shiftTm C0 s11)) = (shiftTm C0 (tshiftTm c s11)))) := (tshift_shift0_Tm_comm_ind s11 H0).
    Definition tshift_shift0_Ty_comm (S34 : Ty) : (forall (c : (Cutoff TyVar)) ,
      ((tshiftTy c (shiftTy C0 S34)) = (shiftTy C0 (tshiftTy c S34)))) := (tshift_shift0_Ty_comm_ind S34 H0).
    Definition tshift_tshift0_Tm_comm (s11 : Tm) : (forall (c : (Cutoff TyVar)) ,
      ((tshiftTm (CS c) (tshiftTm C0 s11)) = (tshiftTm C0 (tshiftTm c s11)))) := (tshift_tshift0_Tm_comm_ind s11 H0).
    Definition tshift_tshift0_Ty_comm (S34 : Ty) : (forall (c : (Cutoff TyVar)) ,
      ((tshiftTy (CS c) (tshiftTy C0 S34)) = (tshiftTy C0 (tshiftTy c S34)))) := (tshift_tshift0_Ty_comm_ind S34 H0).
    Definition shift_shift0_Kind_comm (K42 : Kind) : (forall (c : (Cutoff TmVar)) ,
      ((shiftKind (CS c) (shiftKind C0 K42)) = (shiftKind C0 (shiftKind c K42)))) := (shift_shift0_Kind_comm_ind K42 H0).
    Definition shift_tshift0_Kind_comm (K42 : Kind) : (forall (c : (Cutoff TmVar)) ,
      ((shiftKind c (tshiftKind C0 K42)) = (tshiftKind C0 (shiftKind c K42)))) := (shift_tshift0_Kind_comm_ind K42 H0).
    Definition tshift_shift0_Kind_comm (K42 : Kind) : (forall (c : (Cutoff TyVar)) ,
      ((tshiftKind c (shiftKind C0 K42)) = (shiftKind C0 (tshiftKind c K42)))) := (tshift_shift0_Kind_comm_ind K42 H0).
    Definition tshift_tshift0_Kind_comm (K42 : Kind) : (forall (c : (Cutoff TyVar)) ,
      ((tshiftKind (CS c) (tshiftKind C0 K42)) = (tshiftKind C0 (tshiftKind c K42)))) := (tshift_tshift0_Kind_comm_ind K42 H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_shift0_Kind_comm shift_tshift0_Kind_comm tshift_shift0_Kind_comm tshift_tshift0_Kind_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm shift_shift0_Ty_comm shift_tshift0_Ty_comm tshift_shift0_Ty_comm tshift_tshift0_Ty_comm : interaction.
 Hint Rewrite shift_shift0_Kind_comm shift_tshift0_Kind_comm tshift_shift0_Kind_comm tshift_tshift0_Kind_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm shift_shift0_Ty_comm shift_tshift0_Ty_comm tshift_shift0_Ty_comm tshift_tshift0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTm_shiftTm  :
    (forall (k : Hvl) (c : (Cutoff TmVar)) (s11 : Tm) ,
      ((weakenTm (shiftTm c s11) k) = (shiftTm (weakenCutoffTmVar c k) (weakenTm s11 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTy_shiftTy  :
    (forall (k : Hvl) (c : (Cutoff TmVar)) (S34 : Ty) ,
      ((weakenTy (shiftTy c S34) k) = (shiftTy (weakenCutoffTmVar c k) (weakenTy S34 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k : Hvl) (c : (Cutoff TyVar)) (s11 : Tm) ,
      ((weakenTm (tshiftTm c s11) k) = (tshiftTm (weakenCutoffTyVar c k) (weakenTm s11 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTy_tshiftTy  :
    (forall (k : Hvl) (c : (Cutoff TyVar)) (S34 : Ty) ,
      ((weakenTy (tshiftTy c S34) k) = (tshiftTy (weakenCutoffTyVar c k) (weakenTy S34 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenKind_shiftKind  :
    (forall (k : Hvl) (c : (Cutoff TmVar)) (K42 : Kind) ,
      ((weakenKind (shiftKind c K42) k) = (shiftKind (weakenCutoffTmVar c k) (weakenKind K42 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenKind_tshiftKind  :
    (forall (k : Hvl) (c : (Cutoff TyVar)) (K42 : Kind) ,
      ((weakenKind (tshiftKind c K42) k) = (tshiftKind (weakenCutoffTyVar c k) (weakenKind K42 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTm_substIndex0_comm_ind (c : (Cutoff TmVar)) (s11 : Tm) :
      (forall (k : Hvl) (x51 : (Index TmVar)) ,
        ((shiftTm (weakenCutoffTmVar c k) (substIndex (weakenTrace X0 k) s11 x51)) = (substIndex (weakenTrace X0 k) (shiftTm c s11) (shiftIndex (weakenCutoffTmVar (CS c) k) x51)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_substIndex0_comm_ind (c : (Cutoff TyVar)) (s11 : Tm) :
      (forall (k : Hvl) (x51 : (Index TmVar)) ,
        ((tshiftTm (weakenCutoffTyVar c k) (substIndex (weakenTrace X0 k) s11 x51)) = (substIndex (weakenTrace X0 k) (tshiftTm c s11) x51))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shiftTy_tsubstIndex0_comm_ind (c : (Cutoff TmVar)) (S34 : Ty) :
      (forall (k : Hvl) (X5 : (Index TyVar)) ,
        ((shiftTy (weakenCutoffTmVar c k) (tsubstIndex (weakenTrace X0 k) S34 X5)) = (tsubstIndex (weakenTrace X0 k) (shiftTy c S34) X5))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTy_tsubstIndex0_comm_ind (c : (Cutoff TyVar)) (S34 : Ty) :
      (forall (k : Hvl) (X5 : (Index TyVar)) ,
        ((tshiftTy (weakenCutoffTyVar c k) (tsubstIndex (weakenTrace X0 k) S34 X5)) = (tsubstIndex (weakenTrace X0 k) (tshiftTy c S34) (tshiftIndex (weakenCutoffTyVar (CS c) k) X5)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint shift_subst0_Tm_comm_ind (s12 : Tm) (k : Hvl) (c : (Cutoff TmVar)) (s11 : Tm) {struct s12} :
    ((shiftTm (weakenCutoffTmVar c k) (substTm (weakenTrace X0 k) s11 s12)) = (substTm (weakenTrace X0 k) (shiftTm c s11) (shiftTm (weakenCutoffTmVar (CS c) k) s12))) :=
      match s12 return ((shiftTm (weakenCutoffTmVar c k) (substTm (weakenTrace X0 k) s11 s12)) = (substTm (weakenTrace X0 k) (shiftTm c s11) (shiftTm (weakenCutoffTmVar (CS c) k) s12))) with
        | (var x51) => (shiftTm_substIndex0_comm_ind c s11 k x51)
        | (abs T73 t51) => (f_equal2 abs (shift_subst0_Ty_comm_ind T73 k c s11) (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t51 (HS TmVar k) c s11) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (app t52 t53) => (f_equal2 app (shift_subst0_Tm_comm_ind t52 k c s11) (shift_subst0_Tm_comm_ind t53 k c s11))
        | (all T73 t51) => (f_equal2 all (shift_subst0_Ty_comm_ind T73 k c s11) (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t51 (HS TmVar k) c s11) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end
    with shift_subst0_Ty_comm_ind (S34 : Ty) (k : Hvl) (c : (Cutoff TmVar)) (s11 : Tm) {struct S34} :
    ((shiftTy (weakenCutoffTmVar c k) (substTy (weakenTrace X0 k) s11 S34)) = (substTy (weakenTrace X0 k) (shiftTm c s11) (shiftTy (weakenCutoffTmVar (CS c) k) S34))) :=
      match S34 return ((shiftTy (weakenCutoffTmVar c k) (substTy (weakenTrace X0 k) s11 S34)) = (substTy (weakenTrace X0 k) (shiftTm c s11) (shiftTy (weakenCutoffTmVar (CS c) k) S34))) with
        | (tvar X5) => eq_refl
        | (tpi T75 T76) => (f_equal2 tpi (shift_subst0_Ty_comm_ind T75 k c s11) (eq_trans (f_equal2 shiftTy eq_refl (f_equal3 substTy (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Ty_comm_ind T76 (HS TmVar k) c s11) (f_equal3 substTy (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (tapp T74 t54) => (f_equal2 tapp (shift_subst0_Ty_comm_ind T74 k c s11) (shift_subst0_Tm_comm_ind t54 k c s11))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint shift_tsubst0_Tm_comm_ind (s11 : Tm) (k : Hvl) (c : (Cutoff TmVar)) (S34 : Ty) {struct s11} :
    ((shiftTm (weakenCutoffTmVar c k) (tsubstTm (weakenTrace X0 k) S34 s11)) = (tsubstTm (weakenTrace X0 k) (shiftTy c S34) (shiftTm (weakenCutoffTmVar c k) s11))) :=
      match s11 return ((shiftTm (weakenCutoffTmVar c k) (tsubstTm (weakenTrace X0 k) S34 s11)) = (tsubstTm (weakenTrace X0 k) (shiftTy c S34) (shiftTm (weakenCutoffTmVar c k) s11))) with
        | (var x51) => eq_refl
        | (abs T73 t51) => (f_equal2 abs (shift_tsubst0_Ty_comm_ind T73 k c S34) (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t51 (HS TmVar k) c S34) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (app t52 t53) => (f_equal2 app (shift_tsubst0_Tm_comm_ind t52 k c S34) (shift_tsubst0_Tm_comm_ind t53 k c S34))
        | (all T73 t51) => (f_equal2 all (shift_tsubst0_Ty_comm_ind T73 k c S34) (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t51 (HS TmVar k) c S34) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end
    with shift_tsubst0_Ty_comm_ind (S35 : Ty) (k : Hvl) (c : (Cutoff TmVar)) (S34 : Ty) {struct S35} :
    ((shiftTy (weakenCutoffTmVar c k) (tsubstTy (weakenTrace X0 k) S34 S35)) = (tsubstTy (weakenTrace X0 k) (shiftTy c S34) (shiftTy (weakenCutoffTmVar c k) S35))) :=
      match S35 return ((shiftTy (weakenCutoffTmVar c k) (tsubstTy (weakenTrace X0 k) S34 S35)) = (tsubstTy (weakenTrace X0 k) (shiftTy c S34) (shiftTy (weakenCutoffTmVar c k) S35))) with
        | (tvar X5) => (shiftTy_tsubstIndex0_comm_ind c S34 k X5)
        | (tpi T75 T76) => (f_equal2 tpi (shift_tsubst0_Ty_comm_ind T75 k c S34) (eq_trans (f_equal2 shiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Ty_comm_ind T76 (HS TmVar k) c S34) (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (tapp T74 t54) => (f_equal2 tapp (shift_tsubst0_Ty_comm_ind T74 k c S34) (shift_tsubst0_Tm_comm_ind t54 k c S34))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint tshift_subst0_Tm_comm_ind (s12 : Tm) (k : Hvl) (c : (Cutoff TyVar)) (s11 : Tm) {struct s12} :
    ((tshiftTm (weakenCutoffTyVar c k) (substTm (weakenTrace X0 k) s11 s12)) = (substTm (weakenTrace X0 k) (tshiftTm c s11) (tshiftTm (weakenCutoffTyVar c k) s12))) :=
      match s12 return ((tshiftTm (weakenCutoffTyVar c k) (substTm (weakenTrace X0 k) s11 s12)) = (substTm (weakenTrace X0 k) (tshiftTm c s11) (tshiftTm (weakenCutoffTyVar c k) s12))) with
        | (var x51) => (tshiftTm_substIndex0_comm_ind c s11 k x51)
        | (abs T73 t51) => (f_equal2 abs (tshift_subst0_Ty_comm_ind T73 k c s11) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t51 (HS TmVar k) c s11) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (app t52 t53) => (f_equal2 app (tshift_subst0_Tm_comm_ind t52 k c s11) (tshift_subst0_Tm_comm_ind t53 k c s11))
        | (all T73 t51) => (f_equal2 all (tshift_subst0_Ty_comm_ind T73 k c s11) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t51 (HS TmVar k) c s11) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end
    with tshift_subst0_Ty_comm_ind (S34 : Ty) (k : Hvl) (c : (Cutoff TyVar)) (s11 : Tm) {struct S34} :
    ((tshiftTy (weakenCutoffTyVar c k) (substTy (weakenTrace X0 k) s11 S34)) = (substTy (weakenTrace X0 k) (tshiftTm c s11) (tshiftTy (weakenCutoffTyVar c k) S34))) :=
      match S34 return ((tshiftTy (weakenCutoffTyVar c k) (substTy (weakenTrace X0 k) s11 S34)) = (substTy (weakenTrace X0 k) (tshiftTm c s11) (tshiftTy (weakenCutoffTyVar c k) S34))) with
        | (tvar X5) => eq_refl
        | (tpi T75 T76) => (f_equal2 tpi (tshift_subst0_Ty_comm_ind T75 k c s11) (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 substTy (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Ty_comm_ind T76 (HS TmVar k) c s11) (f_equal3 substTy (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (tapp T74 t54) => (f_equal2 tapp (tshift_subst0_Ty_comm_ind T74 k c s11) (tshift_subst0_Tm_comm_ind t54 k c s11))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint tshift_tsubst0_Tm_comm_ind (s11 : Tm) (k : Hvl) (c : (Cutoff TyVar)) (S34 : Ty) {struct s11} :
    ((tshiftTm (weakenCutoffTyVar c k) (tsubstTm (weakenTrace X0 k) S34 s11)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c S34) (tshiftTm (weakenCutoffTyVar (CS c) k) s11))) :=
      match s11 return ((tshiftTm (weakenCutoffTyVar c k) (tsubstTm (weakenTrace X0 k) S34 s11)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c S34) (tshiftTm (weakenCutoffTyVar (CS c) k) s11))) with
        | (var x51) => eq_refl
        | (abs T73 t51) => (f_equal2 abs (tshift_tsubst0_Ty_comm_ind T73 k c S34) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t51 (HS TmVar k) c S34) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (app t52 t53) => (f_equal2 app (tshift_tsubst0_Tm_comm_ind t52 k c S34) (tshift_tsubst0_Tm_comm_ind t53 k c S34))
        | (all T73 t51) => (f_equal2 all (tshift_tsubst0_Ty_comm_ind T73 k c S34) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t51 (HS TmVar k) c S34) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end
    with tshift_tsubst0_Ty_comm_ind (S35 : Ty) (k : Hvl) (c : (Cutoff TyVar)) (S34 : Ty) {struct S35} :
    ((tshiftTy (weakenCutoffTyVar c k) (tsubstTy (weakenTrace X0 k) S34 S35)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c S34) (tshiftTy (weakenCutoffTyVar (CS c) k) S35))) :=
      match S35 return ((tshiftTy (weakenCutoffTyVar c k) (tsubstTy (weakenTrace X0 k) S34 S35)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c S34) (tshiftTy (weakenCutoffTyVar (CS c) k) S35))) with
        | (tvar X5) => (tshiftTy_tsubstIndex0_comm_ind c S34 k X5)
        | (tpi T75 T76) => (f_equal2 tpi (tshift_tsubst0_Ty_comm_ind T75 k c S34) (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T76 (HS TmVar k) c S34) (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (tapp T74 t54) => (f_equal2 tapp (tshift_tsubst0_Ty_comm_ind T74 k c S34) (tshift_tsubst0_Tm_comm_ind t54 k c S34))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint shift_subst0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TmVar)) (s11 : Tm) {struct K42} :
    ((shiftKind (weakenCutoffTmVar c k) (substKind (weakenTrace X0 k) s11 K42)) = (substKind (weakenTrace X0 k) (shiftTm c s11) (shiftKind (weakenCutoffTmVar (CS c) k) K42))) :=
      match K42 return ((shiftKind (weakenCutoffTmVar c k) (substKind (weakenTrace X0 k) s11 K42)) = (substKind (weakenTrace X0 k) (shiftTm c s11) (shiftKind (weakenCutoffTmVar (CS c) k) K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (shift_subst0_Ty_comm_ind T73 k c s11) (eq_trans (f_equal2 shiftKind eq_refl (f_equal3 substKind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Kind_comm_ind K43 (HS TmVar k) c s11) (f_equal3 substKind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_tsubst0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TmVar)) (S34 : Ty) {struct K42} :
    ((shiftKind (weakenCutoffTmVar c k) (tsubstKind (weakenTrace X0 k) S34 K42)) = (tsubstKind (weakenTrace X0 k) (shiftTy c S34) (shiftKind (weakenCutoffTmVar c k) K42))) :=
      match K42 return ((shiftKind (weakenCutoffTmVar c k) (tsubstKind (weakenTrace X0 k) S34 K42)) = (tsubstKind (weakenTrace X0 k) (shiftTy c S34) (shiftKind (weakenCutoffTmVar c k) K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (shift_tsubst0_Ty_comm_ind T73 k c S34) (eq_trans (f_equal2 shiftKind eq_refl (f_equal3 tsubstKind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Kind_comm_ind K43 (HS TmVar k) c S34) (f_equal3 tsubstKind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint tshift_subst0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TyVar)) (s11 : Tm) {struct K42} :
    ((tshiftKind (weakenCutoffTyVar c k) (substKind (weakenTrace X0 k) s11 K42)) = (substKind (weakenTrace X0 k) (tshiftTm c s11) (tshiftKind (weakenCutoffTyVar c k) K42))) :=
      match K42 return ((tshiftKind (weakenCutoffTyVar c k) (substKind (weakenTrace X0 k) s11 K42)) = (substKind (weakenTrace X0 k) (tshiftTm c s11) (tshiftKind (weakenCutoffTyVar c k) K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (tshift_subst0_Ty_comm_ind T73 k c s11) (eq_trans (f_equal2 tshiftKind eq_refl (f_equal3 substKind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Kind_comm_ind K43 (HS TmVar k) c s11) (f_equal3 substKind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
    Fixpoint tshift_tsubst0_Kind_comm_ind (K42 : Kind) (k : Hvl) (c : (Cutoff TyVar)) (S34 : Ty) {struct K42} :
    ((tshiftKind (weakenCutoffTyVar c k) (tsubstKind (weakenTrace X0 k) S34 K42)) = (tsubstKind (weakenTrace X0 k) (tshiftTy c S34) (tshiftKind (weakenCutoffTyVar (CS c) k) K42))) :=
      match K42 return ((tshiftKind (weakenCutoffTyVar c k) (tsubstKind (weakenTrace X0 k) S34 K42)) = (tsubstKind (weakenTrace X0 k) (tshiftTy c S34) (tshiftKind (weakenCutoffTyVar (CS c) k) K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (tshift_tsubst0_Ty_comm_ind T73 k c S34) (eq_trans (f_equal2 tshiftKind eq_refl (f_equal3 tsubstKind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Kind_comm_ind K43 (HS TmVar k) c S34) (f_equal3 tsubstKind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shiftTm_substTm0_comm (s12 : Tm) : (forall (c : (Cutoff TmVar)) (s11 : Tm) ,
      ((shiftTm c (substTm X0 s11 s12)) = (substTm X0 (shiftTm c s11) (shiftTm (CS c) s12)))) := (shift_subst0_Tm_comm_ind s12 H0).
    Definition shiftTy_substTy0_comm (S34 : Ty) : (forall (c : (Cutoff TmVar)) (s11 : Tm) ,
      ((shiftTy c (substTy X0 s11 S34)) = (substTy X0 (shiftTm c s11) (shiftTy (CS c) S34)))) := (shift_subst0_Ty_comm_ind S34 H0).
    Definition shiftTm_tsubstTm0_comm (s11 : Tm) : (forall (c : (Cutoff TmVar)) (S34 : Ty) ,
      ((shiftTm c (tsubstTm X0 S34 s11)) = (tsubstTm X0 (shiftTy c S34) (shiftTm c s11)))) := (shift_tsubst0_Tm_comm_ind s11 H0).
    Definition shiftTy_tsubstTy0_comm (S35 : Ty) : (forall (c : (Cutoff TmVar)) (S34 : Ty) ,
      ((shiftTy c (tsubstTy X0 S34 S35)) = (tsubstTy X0 (shiftTy c S34) (shiftTy c S35)))) := (shift_tsubst0_Ty_comm_ind S35 H0).
    Definition tshiftTm_substTm0_comm (s12 : Tm) : (forall (c : (Cutoff TyVar)) (s11 : Tm) ,
      ((tshiftTm c (substTm X0 s11 s12)) = (substTm X0 (tshiftTm c s11) (tshiftTm c s12)))) := (tshift_subst0_Tm_comm_ind s12 H0).
    Definition tshiftTy_substTy0_comm (S34 : Ty) : (forall (c : (Cutoff TyVar)) (s11 : Tm) ,
      ((tshiftTy c (substTy X0 s11 S34)) = (substTy X0 (tshiftTm c s11) (tshiftTy c S34)))) := (tshift_subst0_Ty_comm_ind S34 H0).
    Definition tshiftTm_tsubstTm0_comm (s11 : Tm) : (forall (c : (Cutoff TyVar)) (S34 : Ty) ,
      ((tshiftTm c (tsubstTm X0 S34 s11)) = (tsubstTm X0 (tshiftTy c S34) (tshiftTm (CS c) s11)))) := (tshift_tsubst0_Tm_comm_ind s11 H0).
    Definition tshiftTy_tsubstTy0_comm (S35 : Ty) : (forall (c : (Cutoff TyVar)) (S34 : Ty) ,
      ((tshiftTy c (tsubstTy X0 S34 S35)) = (tsubstTy X0 (tshiftTy c S34) (tshiftTy (CS c) S35)))) := (tshift_tsubst0_Ty_comm_ind S35 H0).
    Definition shiftKind_substKind0_comm (K42 : Kind) : (forall (c : (Cutoff TmVar)) (s11 : Tm) ,
      ((shiftKind c (substKind X0 s11 K42)) = (substKind X0 (shiftTm c s11) (shiftKind (CS c) K42)))) := (shift_subst0_Kind_comm_ind K42 H0).
    Definition shiftKind_tsubstKind0_comm (K42 : Kind) : (forall (c : (Cutoff TmVar)) (S34 : Ty) ,
      ((shiftKind c (tsubstKind X0 S34 K42)) = (tsubstKind X0 (shiftTy c S34) (shiftKind c K42)))) := (shift_tsubst0_Kind_comm_ind K42 H0).
    Definition tshiftKind_substKind0_comm (K42 : Kind) : (forall (c : (Cutoff TyVar)) (s11 : Tm) ,
      ((tshiftKind c (substKind X0 s11 K42)) = (substKind X0 (tshiftTm c s11) (tshiftKind c K42)))) := (tshift_subst0_Kind_comm_ind K42 H0).
    Definition tshiftKind_tsubstKind0_comm (K42 : Kind) : (forall (c : (Cutoff TyVar)) (S34 : Ty) ,
      ((tshiftKind c (tsubstKind X0 S34 K42)) = (tsubstKind X0 (tshiftTy c S34) (tshiftKind (CS c) K42)))) := (tshift_tsubst0_Kind_comm_ind K42 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d : (Trace TmVar)) (s11 : Tm) :
      (forall (k : Hvl) (x51 : (Index TmVar)) ,
        ((substIndex (weakenTrace (XS TmVar d) k) s11 (shiftIndex (weakenCutoffTmVar C0 k) x51)) = (shiftTm (weakenCutoffTmVar C0 k) (substIndex (weakenTrace d k) s11 x51)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d : (Trace TmVar)) (s11 : Tm) :
      (forall (k : Hvl) (x51 : (Index TmVar)) ,
        ((substIndex (weakenTrace (XS TyVar d) k) s11 x51) = (tshiftTm (weakenCutoffTyVar C0 k) (substIndex (weakenTrace d k) s11 x51)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d : (Trace TyVar)) (S34 : Ty) :
      (forall (k : Hvl) (X5 : (Index TyVar)) ,
        ((tsubstIndex (weakenTrace (XS TmVar d) k) S34 X5) = (shiftTy (weakenCutoffTmVar C0 k) (tsubstIndex (weakenTrace d k) S34 X5)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d : (Trace TyVar)) (S34 : Ty) :
      (forall (k : Hvl) (X5 : (Index TyVar)) ,
        ((tsubstIndex (weakenTrace (XS TyVar d) k) S34 (tshiftIndex (weakenCutoffTyVar C0 k) X5)) = (tshiftTy (weakenCutoffTyVar C0 k) (tsubstIndex (weakenTrace d k) S34 X5)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_shift0_Tm_comm_ind (s12 : Tm) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) {struct s12} :
    ((substTm (weakenTrace (XS TmVar d) k) s11 (shiftTm (weakenCutoffTmVar C0 k) s12)) = (shiftTm (weakenCutoffTmVar C0 k) (substTm (weakenTrace d k) s11 s12))) :=
      match s12 return ((substTm (weakenTrace (XS TmVar d) k) s11 (shiftTm (weakenCutoffTmVar C0 k) s12)) = (shiftTm (weakenCutoffTmVar C0 k) (substTm (weakenTrace d k) s11 s12))) with
        | (var x51) => (substIndex_shiftTm0_comm_ind d s11 k x51)
        | (abs T73 t51) => (f_equal2 abs (subst_shift0_Ty_comm_ind T73 k d s11) (eq_trans (f_equal3 substTm (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t51 (HS TmVar k) d s11) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t52 t53) => (f_equal2 app (subst_shift0_Tm_comm_ind t52 k d s11) (subst_shift0_Tm_comm_ind t53 k d s11))
        | (all T73 t51) => (f_equal2 all (subst_shift0_Ty_comm_ind T73 k d s11) (eq_trans (f_equal3 substTm (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t51 (HS TmVar k) d s11) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_shift0_Ty_comm_ind (S34 : Ty) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) {struct S34} :
    ((substTy (weakenTrace (XS TmVar d) k) s11 (shiftTy (weakenCutoffTmVar C0 k) S34)) = (shiftTy (weakenCutoffTmVar C0 k) (substTy (weakenTrace d k) s11 S34))) :=
      match S34 return ((substTy (weakenTrace (XS TmVar d) k) s11 (shiftTy (weakenCutoffTmVar C0 k) S34)) = (shiftTy (weakenCutoffTmVar C0 k) (substTy (weakenTrace d k) s11 S34))) with
        | (tvar X5) => eq_refl
        | (tpi T75 T76) => (f_equal2 tpi (subst_shift0_Ty_comm_ind T75 k d s11) (eq_trans (f_equal3 substTy (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Ty_comm_ind T76 (HS TmVar k) d s11) (f_equal2 shiftTy eq_refl (f_equal3 substTy (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T74 t54) => (f_equal2 tapp (subst_shift0_Ty_comm_ind T74 k d s11) (subst_shift0_Tm_comm_ind t54 k d s11))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint subst_tshift0_Tm_comm_ind (s12 : Tm) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) {struct s12} :
    ((substTm (weakenTrace (XS TyVar d) k) s11 (tshiftTm (weakenCutoffTyVar C0 k) s12)) = (tshiftTm (weakenCutoffTyVar C0 k) (substTm (weakenTrace d k) s11 s12))) :=
      match s12 return ((substTm (weakenTrace (XS TyVar d) k) s11 (tshiftTm (weakenCutoffTyVar C0 k) s12)) = (tshiftTm (weakenCutoffTyVar C0 k) (substTm (weakenTrace d k) s11 s12))) with
        | (var x51) => (substIndex_tshiftTm0_comm_ind d s11 k x51)
        | (abs T73 t51) => (f_equal2 abs (subst_tshift0_Ty_comm_ind T73 k d s11) (eq_trans (f_equal3 substTm (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t51 (HS TmVar k) d s11) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t52 t53) => (f_equal2 app (subst_tshift0_Tm_comm_ind t52 k d s11) (subst_tshift0_Tm_comm_ind t53 k d s11))
        | (all T73 t51) => (f_equal2 all (subst_tshift0_Ty_comm_ind T73 k d s11) (eq_trans (f_equal3 substTm (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t51 (HS TmVar k) d s11) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_tshift0_Ty_comm_ind (S34 : Ty) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) {struct S34} :
    ((substTy (weakenTrace (XS TyVar d) k) s11 (tshiftTy (weakenCutoffTyVar C0 k) S34)) = (tshiftTy (weakenCutoffTyVar C0 k) (substTy (weakenTrace d k) s11 S34))) :=
      match S34 return ((substTy (weakenTrace (XS TyVar d) k) s11 (tshiftTy (weakenCutoffTyVar C0 k) S34)) = (tshiftTy (weakenCutoffTyVar C0 k) (substTy (weakenTrace d k) s11 S34))) with
        | (tvar X5) => eq_refl
        | (tpi T75 T76) => (f_equal2 tpi (subst_tshift0_Ty_comm_ind T75 k d s11) (eq_trans (f_equal3 substTy (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Ty_comm_ind T76 (HS TmVar k) d s11) (f_equal2 tshiftTy eq_refl (f_equal3 substTy (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T74 t54) => (f_equal2 tapp (subst_tshift0_Ty_comm_ind T74 k d s11) (subst_tshift0_Tm_comm_ind t54 k d s11))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint tsubst_shift0_Tm_comm_ind (s11 : Tm) (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) {struct s11} :
    ((tsubstTm (weakenTrace (XS TmVar d) k) S34 (shiftTm (weakenCutoffTmVar C0 k) s11)) = (shiftTm (weakenCutoffTmVar C0 k) (tsubstTm (weakenTrace d k) S34 s11))) :=
      match s11 return ((tsubstTm (weakenTrace (XS TmVar d) k) S34 (shiftTm (weakenCutoffTmVar C0 k) s11)) = (shiftTm (weakenCutoffTmVar C0 k) (tsubstTm (weakenTrace d k) S34 s11))) with
        | (var x51) => eq_refl
        | (abs T73 t51) => (f_equal2 abs (tsubst_shift0_Ty_comm_ind T73 k d S34) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t51 (HS TmVar k) d S34) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t52 t53) => (f_equal2 app (tsubst_shift0_Tm_comm_ind t52 k d S34) (tsubst_shift0_Tm_comm_ind t53 k d S34))
        | (all T73 t51) => (f_equal2 all (tsubst_shift0_Ty_comm_ind T73 k d S34) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t51 (HS TmVar k) d S34) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with tsubst_shift0_Ty_comm_ind (S35 : Ty) (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) {struct S35} :
    ((tsubstTy (weakenTrace (XS TmVar d) k) S34 (shiftTy (weakenCutoffTmVar C0 k) S35)) = (shiftTy (weakenCutoffTmVar C0 k) (tsubstTy (weakenTrace d k) S34 S35))) :=
      match S35 return ((tsubstTy (weakenTrace (XS TmVar d) k) S34 (shiftTy (weakenCutoffTmVar C0 k) S35)) = (shiftTy (weakenCutoffTmVar C0 k) (tsubstTy (weakenTrace d k) S34 S35))) with
        | (tvar X5) => (tsubstIndex_shiftTy0_comm_ind d S34 k X5)
        | (tpi T75 T76) => (f_equal2 tpi (tsubst_shift0_Ty_comm_ind T75 k d S34) (eq_trans (f_equal3 tsubstTy (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Ty_comm_ind T76 (HS TmVar k) d S34) (f_equal2 shiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T74 t54) => (f_equal2 tapp (tsubst_shift0_Ty_comm_ind T74 k d S34) (tsubst_shift0_Tm_comm_ind t54 k d S34))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint tsubst_tshift0_Tm_comm_ind (s11 : Tm) (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) {struct s11} :
    ((tsubstTm (weakenTrace (XS TyVar d) k) S34 (tshiftTm (weakenCutoffTyVar C0 k) s11)) = (tshiftTm (weakenCutoffTyVar C0 k) (tsubstTm (weakenTrace d k) S34 s11))) :=
      match s11 return ((tsubstTm (weakenTrace (XS TyVar d) k) S34 (tshiftTm (weakenCutoffTyVar C0 k) s11)) = (tshiftTm (weakenCutoffTyVar C0 k) (tsubstTm (weakenTrace d k) S34 s11))) with
        | (var x51) => eq_refl
        | (abs T73 t51) => (f_equal2 abs (tsubst_tshift0_Ty_comm_ind T73 k d S34) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t51 (HS TmVar k) d S34) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t52 t53) => (f_equal2 app (tsubst_tshift0_Tm_comm_ind t52 k d S34) (tsubst_tshift0_Tm_comm_ind t53 k d S34))
        | (all T73 t51) => (f_equal2 all (tsubst_tshift0_Ty_comm_ind T73 k d S34) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t51 (HS TmVar k) d S34) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with tsubst_tshift0_Ty_comm_ind (S35 : Ty) (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) {struct S35} :
    ((tsubstTy (weakenTrace (XS TyVar d) k) S34 (tshiftTy (weakenCutoffTyVar C0 k) S35)) = (tshiftTy (weakenCutoffTyVar C0 k) (tsubstTy (weakenTrace d k) S34 S35))) :=
      match S35 return ((tsubstTy (weakenTrace (XS TyVar d) k) S34 (tshiftTy (weakenCutoffTyVar C0 k) S35)) = (tshiftTy (weakenCutoffTyVar C0 k) (tsubstTy (weakenTrace d k) S34 S35))) with
        | (tvar X5) => (tsubstIndex_tshiftTy0_comm_ind d S34 k X5)
        | (tpi T75 T76) => (f_equal2 tpi (tsubst_tshift0_Ty_comm_ind T75 k d S34) (eq_trans (f_equal3 tsubstTy (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T76 (HS TmVar k) d S34) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T74 t54) => (f_equal2 tapp (tsubst_tshift0_Ty_comm_ind T74 k d S34) (tsubst_tshift0_Tm_comm_ind t54 k d S34))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint subst_shift0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) {struct K42} :
    ((substKind (weakenTrace (XS TmVar d) k) s11 (shiftKind (weakenCutoffTmVar C0 k) K42)) = (shiftKind (weakenCutoffTmVar C0 k) (substKind (weakenTrace d k) s11 K42))) :=
      match K42 return ((substKind (weakenTrace (XS TmVar d) k) s11 (shiftKind (weakenCutoffTmVar C0 k) K42)) = (shiftKind (weakenCutoffTmVar C0 k) (substKind (weakenTrace d k) s11 K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (subst_shift0_Ty_comm_ind T73 k d s11) (eq_trans (f_equal3 substKind (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Kind_comm_ind K43 (HS TmVar k) d s11) (f_equal2 shiftKind eq_refl (f_equal3 substKind (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tshift0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) {struct K42} :
    ((substKind (weakenTrace (XS TyVar d) k) s11 (tshiftKind (weakenCutoffTyVar C0 k) K42)) = (tshiftKind (weakenCutoffTyVar C0 k) (substKind (weakenTrace d k) s11 K42))) :=
      match K42 return ((substKind (weakenTrace (XS TyVar d) k) s11 (tshiftKind (weakenCutoffTyVar C0 k) K42)) = (tshiftKind (weakenCutoffTyVar C0 k) (substKind (weakenTrace d k) s11 K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (subst_tshift0_Ty_comm_ind T73 k d s11) (eq_trans (f_equal3 substKind (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Kind_comm_ind K43 (HS TmVar k) d s11) (f_equal2 tshiftKind eq_refl (f_equal3 substKind (eq_sym (weakenTrace_append TmVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_shift0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) {struct K42} :
    ((tsubstKind (weakenTrace (XS TmVar d) k) S34 (shiftKind (weakenCutoffTmVar C0 k) K42)) = (shiftKind (weakenCutoffTmVar C0 k) (tsubstKind (weakenTrace d k) S34 K42))) :=
      match K42 return ((tsubstKind (weakenTrace (XS TmVar d) k) S34 (shiftKind (weakenCutoffTmVar C0 k) K42)) = (shiftKind (weakenCutoffTmVar C0 k) (tsubstKind (weakenTrace d k) S34 K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (tsubst_shift0_Ty_comm_ind T73 k d S34) (eq_trans (f_equal3 tsubstKind (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Kind_comm_ind K43 (HS TmVar k) d S34) (f_equal2 shiftKind eq_refl (f_equal3 tsubstKind (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tshift0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) {struct K42} :
    ((tsubstKind (weakenTrace (XS TyVar d) k) S34 (tshiftKind (weakenCutoffTyVar C0 k) K42)) = (tshiftKind (weakenCutoffTyVar C0 k) (tsubstKind (weakenTrace d k) S34 K42))) :=
      match K42 return ((tsubstKind (weakenTrace (XS TyVar d) k) S34 (tshiftKind (weakenCutoffTyVar C0 k) K42)) = (tshiftKind (weakenCutoffTyVar C0 k) (tsubstKind (weakenTrace d k) S34 K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (tsubst_tshift0_Ty_comm_ind T73 k d S34) (eq_trans (f_equal3 tsubstKind (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Kind_comm_ind K43 (HS TmVar k) d S34) (f_equal2 tshiftKind eq_refl (f_equal3 tsubstKind (eq_sym (weakenTrace_append TyVar d k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition substTm_shiftTm0_comm (s12 : Tm) : (forall (d : (Trace TmVar)) (s11 : Tm) ,
      ((substTm (XS TmVar d) s11 (shiftTm C0 s12)) = (shiftTm C0 (substTm d s11 s12)))) := (subst_shift0_Tm_comm_ind s12 H0).
    Definition substTy_shiftTy0_comm (S34 : Ty) : (forall (d : (Trace TmVar)) (s11 : Tm) ,
      ((substTy (XS TmVar d) s11 (shiftTy C0 S34)) = (shiftTy C0 (substTy d s11 S34)))) := (subst_shift0_Ty_comm_ind S34 H0).
    Definition substTm_tshiftTm0_comm (s12 : Tm) : (forall (d : (Trace TmVar)) (s11 : Tm) ,
      ((substTm (XS TyVar d) s11 (tshiftTm C0 s12)) = (tshiftTm C0 (substTm d s11 s12)))) := (subst_tshift0_Tm_comm_ind s12 H0).
    Definition substTy_tshiftTy0_comm (S34 : Ty) : (forall (d : (Trace TmVar)) (s11 : Tm) ,
      ((substTy (XS TyVar d) s11 (tshiftTy C0 S34)) = (tshiftTy C0 (substTy d s11 S34)))) := (subst_tshift0_Ty_comm_ind S34 H0).
    Definition tsubstTm_shiftTm0_comm (s11 : Tm) : (forall (d : (Trace TyVar)) (S34 : Ty) ,
      ((tsubstTm (XS TmVar d) S34 (shiftTm C0 s11)) = (shiftTm C0 (tsubstTm d S34 s11)))) := (tsubst_shift0_Tm_comm_ind s11 H0).
    Definition tsubstTy_shiftTy0_comm (S35 : Ty) : (forall (d : (Trace TyVar)) (S34 : Ty) ,
      ((tsubstTy (XS TmVar d) S34 (shiftTy C0 S35)) = (shiftTy C0 (tsubstTy d S34 S35)))) := (tsubst_shift0_Ty_comm_ind S35 H0).
    Definition tsubstTm_tshiftTm0_comm (s11 : Tm) : (forall (d : (Trace TyVar)) (S34 : Ty) ,
      ((tsubstTm (XS TyVar d) S34 (tshiftTm C0 s11)) = (tshiftTm C0 (tsubstTm d S34 s11)))) := (tsubst_tshift0_Tm_comm_ind s11 H0).
    Definition tsubstTy_tshiftTy0_comm (S35 : Ty) : (forall (d : (Trace TyVar)) (S34 : Ty) ,
      ((tsubstTy (XS TyVar d) S34 (tshiftTy C0 S35)) = (tshiftTy C0 (tsubstTy d S34 S35)))) := (tsubst_tshift0_Ty_comm_ind S35 H0).
    Definition substKind_shiftKind0_comm (K42 : Kind) : (forall (d : (Trace TmVar)) (s11 : Tm) ,
      ((substKind (XS TmVar d) s11 (shiftKind C0 K42)) = (shiftKind C0 (substKind d s11 K42)))) := (subst_shift0_Kind_comm_ind K42 H0).
    Definition substKind_tshiftKind0_comm (K42 : Kind) : (forall (d : (Trace TmVar)) (s11 : Tm) ,
      ((substKind (XS TyVar d) s11 (tshiftKind C0 K42)) = (tshiftKind C0 (substKind d s11 K42)))) := (subst_tshift0_Kind_comm_ind K42 H0).
    Definition tsubstKind_shiftKind0_comm (K42 : Kind) : (forall (d : (Trace TyVar)) (S34 : Ty) ,
      ((tsubstKind (XS TmVar d) S34 (shiftKind C0 K42)) = (shiftKind C0 (tsubstKind d S34 K42)))) := (tsubst_shift0_Kind_comm_ind K42 H0).
    Definition tsubstKind_tshiftKind0_comm (K42 : Kind) : (forall (d : (Trace TyVar)) (S34 : Ty) ,
      ((tsubstKind (XS TyVar d) S34 (tshiftKind C0 K42)) = (tshiftKind C0 (tsubstKind d S34 K42)))) := (tsubst_tshift0_Kind_comm_ind K42 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    
  End SubstSubordInd.
  Section SubstSubord.
    
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite substKind0_shiftKind0_reflection tsubstKind0_tshiftKind0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection substTy0_shiftTy0_reflection tsubstTy0_tshiftTy0_reflection : interaction.
 Hint Rewrite substKind0_shiftKind0_reflection tsubstKind0_tshiftKind0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection substTy0_shiftTy0_reflection tsubstTy0_tshiftTy0_reflection : reflection.
 Hint Rewrite substKind_shiftKind0_comm substKind_tshiftKind0_comm tsubstKind_shiftKind0_comm tsubstKind_tshiftKind0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm substTy_shiftTy0_comm substTy_tshiftTy0_comm tsubstTy_shiftTy0_comm tsubstTy_tshiftTy0_comm : interaction.
 Hint Rewrite substKind_shiftKind0_comm substKind_tshiftKind0_comm tsubstKind_shiftKind0_comm tsubstKind_tshiftKind0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm substTy_shiftTy0_comm substTy_tshiftTy0_comm tsubstTy_shiftTy0_comm tsubstTy_tshiftTy0_comm : subst_shift0.
 Hint Rewrite shiftKind_substKind0_comm shiftKind_tsubstKind0_comm tshiftKind_substKind0_comm tshiftKind_tsubstKind0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm shiftTy_substTy0_comm shiftTy_tsubstTy0_comm tshiftTy_substTy0_comm tshiftTy_tsubstTy0_comm : interaction.
 Hint Rewrite shiftKind_substKind0_comm shiftKind_tsubstKind0_comm tshiftKind_substKind0_comm tshiftKind_tsubstKind0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm shiftTy_substTy0_comm shiftTy_tsubstTy0_comm tshiftTy_substTy0_comm tshiftTy_tsubstTy0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) :
      (forall (k : Hvl) (x51 : (Index TmVar)) ,
        ((substTm (weakenTrace d k) s11 (substIndex (weakenTrace X0 k) s12 x51)) = (substTm (weakenTrace X0 k) (substTm d s11 s12) (substIndex (weakenTrace (XS TmVar d) k) s11 x51)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d : (Trace TyVar)) (S34 : Ty) (s11 : Tm) :
      (forall (k : Hvl) (x51 : (Index TmVar)) ,
        ((tsubstTm (weakenTrace d k) S34 (substIndex (weakenTrace X0 k) s11 x51)) = (substIndex (weakenTrace X0 k) (tsubstTm d S34 s11) x51))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commright_ind (d : (Trace TmVar)) (s11 : Tm) (S34 : Ty) :
      (forall (k : Hvl) (X5 : (Index TyVar)) ,
        ((substTy (weakenTrace d k) s11 (tsubstIndex (weakenTrace X0 k) S34 X5)) = (tsubstIndex (weakenTrace X0 k) (substTy d s11 S34) X5))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d : (Trace TyVar)) (S34 : Ty) (S35 : Ty) :
      (forall (k : Hvl) (X5 : (Index TyVar)) ,
        ((tsubstTy (weakenTrace d k) S34 (tsubstIndex (weakenTrace X0 k) S35 X5)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S34 S35) (tsubstIndex (weakenTrace (XS TyVar d) k) S34 X5)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d : (Trace TmVar)) (s11 : Tm) (S34 : Ty) :
      (forall (k : Hvl) (x51 : (Index TmVar)) ,
        ((substIndex (weakenTrace d k) s11 x51) = (tsubstTm (weakenTrace X0 k) (substTy d s11 S34) (substIndex (weakenTrace (XS TyVar d) k) s11 x51)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commleft_ind (d : (Trace TyVar)) (S34 : Ty) (s11 : Tm) :
      (forall (k : Hvl) (X5 : (Index TyVar)) ,
        ((tsubstIndex (weakenTrace d k) S34 X5) = (substTy (weakenTrace X0 k) (tsubstTm d S34 s11) (tsubstIndex (weakenTrace (XS TmVar d) k) S34 X5)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_subst0_Tm_comm_ind (s13 : Tm) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) {struct s13} :
    ((substTm (weakenTrace d k) s11 (substTm (weakenTrace X0 k) s12 s13)) = (substTm (weakenTrace X0 k) (substTm d s11 s12) (substTm (weakenTrace (XS TmVar d) k) s11 s13))) :=
      match s13 return ((substTm (weakenTrace d k) s11 (substTm (weakenTrace X0 k) s12 s13)) = (substTm (weakenTrace X0 k) (substTm d s11 s12) (substTm (weakenTrace (XS TmVar d) k) s11 s13))) with
        | (var x51) => (substTm_substIndex0_commright_ind d s11 s12 k x51)
        | (abs T73 t51) => (f_equal2 abs (subst_subst0_Ty_comm_ind T73 k d s11 s12) (eq_trans (f_equal3 substTm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t51 (HS TmVar k) d s11 s12) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t52 t53) => (f_equal2 app (subst_subst0_Tm_comm_ind t52 k d s11 s12) (subst_subst0_Tm_comm_ind t53 k d s11 s12))
        | (all T73 t51) => (f_equal2 all (subst_subst0_Ty_comm_ind T73 k d s11 s12) (eq_trans (f_equal3 substTm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t51 (HS TmVar k) d s11 s12) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_subst0_Ty_comm_ind (S34 : Ty) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) {struct S34} :
    ((substTy (weakenTrace d k) s11 (substTy (weakenTrace X0 k) s12 S34)) = (substTy (weakenTrace X0 k) (substTm d s11 s12) (substTy (weakenTrace (XS TmVar d) k) s11 S34))) :=
      match S34 return ((substTy (weakenTrace d k) s11 (substTy (weakenTrace X0 k) s12 S34)) = (substTy (weakenTrace X0 k) (substTm d s11 s12) (substTy (weakenTrace (XS TmVar d) k) s11 S34))) with
        | (tvar X5) => eq_refl
        | (tpi T75 T76) => (f_equal2 tpi (subst_subst0_Ty_comm_ind T75 k d s11 s12) (eq_trans (f_equal3 substTy (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 substTy (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Ty_comm_ind T76 (HS TmVar k) d s11 s12) (f_equal3 substTy (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 substTy (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T74 t54) => (f_equal2 tapp (subst_subst0_Ty_comm_ind T74 k d s11 s12) (subst_subst0_Tm_comm_ind t54 k d s11 s12))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint subst_tsubst0_Tm_comm_ind (s12 : Tm) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (S34 : Ty) {struct s12} :
    ((substTm (weakenTrace d k) s11 (tsubstTm (weakenTrace X0 k) S34 s12)) = (tsubstTm (weakenTrace X0 k) (substTy d s11 S34) (substTm (weakenTrace (XS TyVar d) k) s11 s12))) :=
      match s12 return ((substTm (weakenTrace d k) s11 (tsubstTm (weakenTrace X0 k) S34 s12)) = (tsubstTm (weakenTrace X0 k) (substTy d s11 S34) (substTm (weakenTrace (XS TyVar d) k) s11 s12))) with
        | (var x51) => (substTy_tsubstIndex0_commleft_ind d s11 S34 k x51)
        | (abs T73 t51) => (f_equal2 abs (subst_tsubst0_Ty_comm_ind T73 k d s11 S34) (eq_trans (f_equal3 substTm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t51 (HS TmVar k) d s11 S34) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t52 t53) => (f_equal2 app (subst_tsubst0_Tm_comm_ind t52 k d s11 S34) (subst_tsubst0_Tm_comm_ind t53 k d s11 S34))
        | (all T73 t51) => (f_equal2 all (subst_tsubst0_Ty_comm_ind T73 k d s11 S34) (eq_trans (f_equal3 substTm (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t51 (HS TmVar k) d s11 S34) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_tsubst0_Ty_comm_ind (S35 : Ty) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (S34 : Ty) {struct S35} :
    ((substTy (weakenTrace d k) s11 (tsubstTy (weakenTrace X0 k) S34 S35)) = (tsubstTy (weakenTrace X0 k) (substTy d s11 S34) (substTy (weakenTrace (XS TyVar d) k) s11 S35))) :=
      match S35 return ((substTy (weakenTrace d k) s11 (tsubstTy (weakenTrace X0 k) S34 S35)) = (tsubstTy (weakenTrace X0 k) (substTy d s11 S34) (substTy (weakenTrace (XS TyVar d) k) s11 S35))) with
        | (tvar X5) => (substTy_tsubstIndex0_commright_ind d s11 S34 k X5)
        | (tpi T75 T76) => (f_equal2 tpi (subst_tsubst0_Ty_comm_ind T75 k d s11 S34) (eq_trans (f_equal3 substTy (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Ty_comm_ind T76 (HS TmVar k) d s11 S34) (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 substTy (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T74 t54) => (f_equal2 tapp (subst_tsubst0_Ty_comm_ind T74 k d s11 S34) (subst_tsubst0_Tm_comm_ind t54 k d s11 S34))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint tsubst_subst0_Tm_comm_ind (s12 : Tm) (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) (s11 : Tm) {struct s12} :
    ((tsubstTm (weakenTrace d k) S34 (substTm (weakenTrace X0 k) s11 s12)) = (substTm (weakenTrace X0 k) (tsubstTm d S34 s11) (tsubstTm (weakenTrace (XS TmVar d) k) S34 s12))) :=
      match s12 return ((tsubstTm (weakenTrace d k) S34 (substTm (weakenTrace X0 k) s11 s12)) = (substTm (weakenTrace X0 k) (tsubstTm d S34 s11) (tsubstTm (weakenTrace (XS TmVar d) k) S34 s12))) with
        | (var x51) => (tsubstTm_substIndex0_commright_ind d S34 s11 k x51)
        | (abs T73 t51) => (f_equal2 abs (tsubst_subst0_Ty_comm_ind T73 k d S34 s11) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t51 (HS TmVar k) d S34 s11) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t52 t53) => (f_equal2 app (tsubst_subst0_Tm_comm_ind t52 k d S34 s11) (tsubst_subst0_Tm_comm_ind t53 k d S34 s11))
        | (all T73 t51) => (f_equal2 all (tsubst_subst0_Ty_comm_ind T73 k d S34 s11) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t51 (HS TmVar k) d S34 s11) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with tsubst_subst0_Ty_comm_ind (S35 : Ty) (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) (s11 : Tm) {struct S35} :
    ((tsubstTy (weakenTrace d k) S34 (substTy (weakenTrace X0 k) s11 S35)) = (substTy (weakenTrace X0 k) (tsubstTm d S34 s11) (tsubstTy (weakenTrace (XS TmVar d) k) S34 S35))) :=
      match S35 return ((tsubstTy (weakenTrace d k) S34 (substTy (weakenTrace X0 k) s11 S35)) = (substTy (weakenTrace X0 k) (tsubstTm d S34 s11) (tsubstTy (weakenTrace (XS TmVar d) k) S34 S35))) with
        | (tvar X5) => (tsubstTm_substIndex0_commleft_ind d S34 s11 k X5)
        | (tpi T75 T76) => (f_equal2 tpi (tsubst_subst0_Ty_comm_ind T75 k d S34 s11) (eq_trans (f_equal3 tsubstTy (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 substTy (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Ty_comm_ind T76 (HS TmVar k) d S34 s11) (f_equal3 substTy (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T74 t54) => (f_equal2 tapp (tsubst_subst0_Ty_comm_ind T74 k d S34 s11) (tsubst_subst0_Tm_comm_ind t54 k d S34 s11))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint tsubst_tsubst0_Tm_comm_ind (s11 : Tm) (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) (S35 : Ty) {struct s11} :
    ((tsubstTm (weakenTrace d k) S34 (tsubstTm (weakenTrace X0 k) S35 s11)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d S34 S35) (tsubstTm (weakenTrace (XS TyVar d) k) S34 s11))) :=
      match s11 return ((tsubstTm (weakenTrace d k) S34 (tsubstTm (weakenTrace X0 k) S35 s11)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d S34 S35) (tsubstTm (weakenTrace (XS TyVar d) k) S34 s11))) with
        | (var x51) => eq_refl
        | (abs T73 t51) => (f_equal2 abs (tsubst_tsubst0_Ty_comm_ind T73 k d S34 S35) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t51 (HS TmVar k) d S34 S35) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t52 t53) => (f_equal2 app (tsubst_tsubst0_Tm_comm_ind t52 k d S34 S35) (tsubst_tsubst0_Tm_comm_ind t53 k d S34 S35))
        | (all T73 t51) => (f_equal2 all (tsubst_tsubst0_Ty_comm_ind T73 k d S34 S35) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t51 (HS TmVar k) d S34 S35) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with tsubst_tsubst0_Ty_comm_ind (S36 : Ty) (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) (S35 : Ty) {struct S36} :
    ((tsubstTy (weakenTrace d k) S34 (tsubstTy (weakenTrace X0 k) S35 S36)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S34 S35) (tsubstTy (weakenTrace (XS TyVar d) k) S34 S36))) :=
      match S36 return ((tsubstTy (weakenTrace d k) S34 (tsubstTy (weakenTrace X0 k) S35 S36)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S34 S35) (tsubstTy (weakenTrace (XS TyVar d) k) S34 S36))) with
        | (tvar X5) => (tsubstTy_tsubstIndex0_commright_ind d S34 S35 k X5)
        | (tpi T75 T76) => (f_equal2 tpi (tsubst_tsubst0_Ty_comm_ind T75 k d S34 S35) (eq_trans (f_equal3 tsubstTy (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T76 (HS TmVar k) d S34 S35) (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (tapp T74 t54) => (f_equal2 tapp (tsubst_tsubst0_Ty_comm_ind T74 k d S34 S35) (tsubst_tsubst0_Tm_comm_ind t54 k d S34 S35))
        | (prop) => eq_refl
        | (prf) => eq_refl
      end.
    Fixpoint subst_subst0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) {struct K42} :
    ((substKind (weakenTrace d k) s11 (substKind (weakenTrace X0 k) s12 K42)) = (substKind (weakenTrace X0 k) (substTm d s11 s12) (substKind (weakenTrace (XS TmVar d) k) s11 K42))) :=
      match K42 return ((substKind (weakenTrace d k) s11 (substKind (weakenTrace X0 k) s12 K42)) = (substKind (weakenTrace X0 k) (substTm d s11 s12) (substKind (weakenTrace (XS TmVar d) k) s11 K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (subst_subst0_Ty_comm_ind T73 k d s11 s12) (eq_trans (f_equal3 substKind (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 substKind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Kind_comm_ind K43 (HS TmVar k) d s11 s12) (f_equal3 substKind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 substKind (eq_sym (weakenTrace_append TmVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tsubst0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (S34 : Ty) {struct K42} :
    ((substKind (weakenTrace d k) s11 (tsubstKind (weakenTrace X0 k) S34 K42)) = (tsubstKind (weakenTrace X0 k) (substTy d s11 S34) (substKind (weakenTrace (XS TyVar d) k) s11 K42))) :=
      match K42 return ((substKind (weakenTrace d k) s11 (tsubstKind (weakenTrace X0 k) S34 K42)) = (tsubstKind (weakenTrace X0 k) (substTy d s11 S34) (substKind (weakenTrace (XS TyVar d) k) s11 K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (subst_tsubst0_Ty_comm_ind T73 k d s11 S34) (eq_trans (f_equal3 substKind (weakenTrace_append TmVar d k (HS TmVar H0)) eq_refl (f_equal3 tsubstKind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Kind_comm_ind K43 (HS TmVar k) d s11 S34) (f_equal3 tsubstKind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 substKind (eq_sym (weakenTrace_append TmVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_subst0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) (s11 : Tm) {struct K42} :
    ((tsubstKind (weakenTrace d k) S34 (substKind (weakenTrace X0 k) s11 K42)) = (substKind (weakenTrace X0 k) (tsubstTm d S34 s11) (tsubstKind (weakenTrace (XS TmVar d) k) S34 K42))) :=
      match K42 return ((tsubstKind (weakenTrace d k) S34 (substKind (weakenTrace X0 k) s11 K42)) = (substKind (weakenTrace X0 k) (tsubstTm d S34 s11) (tsubstKind (weakenTrace (XS TmVar d) k) S34 K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (tsubst_subst0_Ty_comm_ind T73 k d S34 s11) (eq_trans (f_equal3 tsubstKind (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 substKind (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Kind_comm_ind K43 (HS TmVar k) d S34 s11) (f_equal3 substKind (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 tsubstKind (eq_sym (weakenTrace_append TyVar (XS TmVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tsubst0_Kind_comm_ind (K42 : Kind) (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) (S35 : Ty) {struct K42} :
    ((tsubstKind (weakenTrace d k) S34 (tsubstKind (weakenTrace X0 k) S35 K42)) = (tsubstKind (weakenTrace X0 k) (tsubstTy d S34 S35) (tsubstKind (weakenTrace (XS TyVar d) k) S34 K42))) :=
      match K42 return ((tsubstKind (weakenTrace d k) S34 (tsubstKind (weakenTrace X0 k) S35 K42)) = (tsubstKind (weakenTrace X0 k) (tsubstTy d S34 S35) (tsubstKind (weakenTrace (XS TyVar d) k) S34 K42))) with
        | (star) => eq_refl
        | (kpi T73 K43) => (f_equal2 kpi (tsubst_tsubst0_Ty_comm_ind T73 k d S34 S35) (eq_trans (f_equal3 tsubstKind (weakenTrace_append TyVar d k (HS TmVar H0)) eq_refl (f_equal3 tsubstKind (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Kind_comm_ind K43 (HS TmVar k) d S34 S35) (f_equal3 tsubstKind (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 tsubstKind (eq_sym (weakenTrace_append TyVar (XS TyVar d) k (HS TmVar H0))) eq_refl eq_refl)))))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition substTm_substTm0_comm (s13 : Tm) : (forall (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) ,
      ((substTm d s11 (substTm X0 s12 s13)) = (substTm X0 (substTm d s11 s12) (substTm (XS TmVar d) s11 s13)))) := (subst_subst0_Tm_comm_ind s13 H0).
    Definition substTy_substTy0_comm (S34 : Ty) : (forall (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) ,
      ((substTy d s11 (substTy X0 s12 S34)) = (substTy X0 (substTm d s11 s12) (substTy (XS TmVar d) s11 S34)))) := (subst_subst0_Ty_comm_ind S34 H0).
    Definition substTm_tsubstTm0_comm (s12 : Tm) : (forall (d : (Trace TmVar)) (s11 : Tm) (S34 : Ty) ,
      ((substTm d s11 (tsubstTm X0 S34 s12)) = (tsubstTm X0 (substTy d s11 S34) (substTm (XS TyVar d) s11 s12)))) := (subst_tsubst0_Tm_comm_ind s12 H0).
    Definition substTy_tsubstTy0_comm (S35 : Ty) : (forall (d : (Trace TmVar)) (s11 : Tm) (S34 : Ty) ,
      ((substTy d s11 (tsubstTy X0 S34 S35)) = (tsubstTy X0 (substTy d s11 S34) (substTy (XS TyVar d) s11 S35)))) := (subst_tsubst0_Ty_comm_ind S35 H0).
    Definition tsubstTm_substTm0_comm (s12 : Tm) : (forall (d : (Trace TyVar)) (S34 : Ty) (s11 : Tm) ,
      ((tsubstTm d S34 (substTm X0 s11 s12)) = (substTm X0 (tsubstTm d S34 s11) (tsubstTm (XS TmVar d) S34 s12)))) := (tsubst_subst0_Tm_comm_ind s12 H0).
    Definition tsubstTy_substTy0_comm (S35 : Ty) : (forall (d : (Trace TyVar)) (S34 : Ty) (s11 : Tm) ,
      ((tsubstTy d S34 (substTy X0 s11 S35)) = (substTy X0 (tsubstTm d S34 s11) (tsubstTy (XS TmVar d) S34 S35)))) := (tsubst_subst0_Ty_comm_ind S35 H0).
    Definition tsubstTm_tsubstTm0_comm (s11 : Tm) : (forall (d : (Trace TyVar)) (S34 : Ty) (S35 : Ty) ,
      ((tsubstTm d S34 (tsubstTm X0 S35 s11)) = (tsubstTm X0 (tsubstTy d S34 S35) (tsubstTm (XS TyVar d) S34 s11)))) := (tsubst_tsubst0_Tm_comm_ind s11 H0).
    Definition tsubstTy_tsubstTy0_comm (S36 : Ty) : (forall (d : (Trace TyVar)) (S34 : Ty) (S35 : Ty) ,
      ((tsubstTy d S34 (tsubstTy X0 S35 S36)) = (tsubstTy X0 (tsubstTy d S34 S35) (tsubstTy (XS TyVar d) S34 S36)))) := (tsubst_tsubst0_Ty_comm_ind S36 H0).
    Definition substKind_substKind0_comm (K42 : Kind) : (forall (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) ,
      ((substKind d s11 (substKind X0 s12 K42)) = (substKind X0 (substTm d s11 s12) (substKind (XS TmVar d) s11 K42)))) := (subst_subst0_Kind_comm_ind K42 H0).
    Definition substKind_tsubstKind0_comm (K42 : Kind) : (forall (d : (Trace TmVar)) (s11 : Tm) (S34 : Ty) ,
      ((substKind d s11 (tsubstKind X0 S34 K42)) = (tsubstKind X0 (substTy d s11 S34) (substKind (XS TyVar d) s11 K42)))) := (subst_tsubst0_Kind_comm_ind K42 H0).
    Definition tsubstKind_substKind0_comm (K42 : Kind) : (forall (d : (Trace TyVar)) (S34 : Ty) (s11 : Tm) ,
      ((tsubstKind d S34 (substKind X0 s11 K42)) = (substKind X0 (tsubstTm d S34 s11) (tsubstKind (XS TmVar d) S34 K42)))) := (tsubst_subst0_Kind_comm_ind K42 H0).
    Definition tsubstKind_tsubstKind0_comm (K42 : Kind) : (forall (d : (Trace TyVar)) (S34 : Ty) (S35 : Ty) ,
      ((tsubstKind d S34 (tsubstKind X0 S35 K42)) = (tsubstKind X0 (tsubstTy d S34 S35) (tsubstKind (XS TyVar d) S34 K42)))) := (tsubst_tsubst0_Kind_comm_ind K42 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTm_substTm  :
      (forall (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (s12 : Tm) ,
        ((weakenTm (substTm d s11 s12) k) = (substTm (weakenTrace d k) s11 (weakenTm s12 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTy_substTy  :
      (forall (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (S34 : Ty) ,
        ((weakenTy (substTy d s11 S34) k) = (substTy (weakenTrace d k) s11 (weakenTy S34 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) (s11 : Tm) ,
        ((weakenTm (tsubstTm d S34 s11) k) = (tsubstTm (weakenTrace d k) S34 (weakenTm s11 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTy_tsubstTy  :
      (forall (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) (S35 : Ty) ,
        ((weakenTy (tsubstTy d S34 S35) k) = (tsubstTy (weakenTrace d k) S34 (weakenTy S35 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenKind_substKind  :
      (forall (k : Hvl) (d : (Trace TmVar)) (s11 : Tm) (K42 : Kind) ,
        ((weakenKind (substKind d s11 K42) k) = (substKind (weakenTrace d k) s11 (weakenKind K42 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenKind_tsubstKind  :
      (forall (k : Hvl) (d : (Trace TyVar)) (S34 : Ty) (K42 : Kind) ,
        ((weakenKind (tsubstKind d S34 K42) k) = (tsubstKind (weakenTrace d k) S34 (weakenKind K42 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite substKind_substKind0_comm tsubstKind_tsubstKind0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm substTy_substTy0_comm tsubstTy_tsubstTy0_comm : interaction.
 Hint Rewrite substKind_substKind0_comm tsubstKind_tsubstKind0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm substTy_substTy0_comm tsubstTy_tsubstTy0_comm : subst_subst0.
 Hint Rewrite weakenKind_shiftKind weakenKind_tshiftKind weakenTm_shiftTm weakenTm_tshiftTm weakenTy_shiftTy weakenTy_tshiftTy : weaken_shift.
 Hint Rewrite weakenKind_substKind weakenKind_tsubstKind weakenTm_substTm weakenTm_tsubstTm weakenTy_substTy weakenTy_tsubstTy : weaken_subst.
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
        (x51 : (Index TmVar))
        (wfi : (wfindex k x51)) :
        (wfTm k (var x51))
    | wfTm_abs {T73 : Ty}
        (wf : (wfTy k T73)) {t51 : Tm}
        (wf0 : (wfTm (HS TmVar k) t51))
        : (wfTm k (abs T73 t51))
    | wfTm_app {t52 : Tm}
        (wf : (wfTm k t52)) {t53 : Tm}
        (wf0 : (wfTm k t53)) :
        (wfTm k (app t52 t53))
    | wfTm_all {T74 : Ty}
        (wf : (wfTy k T74)) {t54 : Tm}
        (wf0 : (wfTm (HS TmVar k) t54))
        : (wfTm k (all T74 t54))
  with wfTy (k : Hvl) : Ty -> Prop :=
    | wfTy_tvar
        (X5 : (Index TyVar))
        (wfi : (wfindex k X5)) :
        (wfTy k (tvar X5))
    | wfTy_tpi {T73 : Ty}
        (wf : (wfTy k T73)) {T74 : Ty}
        (wf0 : (wfTy (HS TmVar k) T74))
        : (wfTy k (tpi T73 T74))
    | wfTy_tapp {T75 : Ty}
        (wf : (wfTy k T75)) {t51 : Tm}
        (wf0 : (wfTm k t51)) :
        (wfTy k (tapp T75 t51))
    | wfTy_prop : (wfTy k (prop))
    | wfTy_prf : (wfTy k (prf)).
  Inductive wfKind (k : Hvl) : Kind -> Prop :=
    | wfKind_star :
        (wfKind k (star))
    | wfKind_kpi {T73 : Ty}
        (wf : (wfTy k T73)) {K42 : Kind}
        (wf0 : (wfKind (HS TmVar k) K42))
        : (wfKind k (kpi T73 K42)).
  Definition inversion_wfTm_var_1 (k : Hvl) (x : (Index TmVar)) (H17 : (wfTm k (var x))) : (wfindex k x) := match H17 in (wfTm _ s11) return match s11 return Prop with
    | (var x) => (wfindex k x)
    | _ => True
  end with
    | (wfTm_var x H1) => H1
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k0 : Hvl) (T : Ty) (t : Tm) (H18 : (wfTm k0 (abs T t))) : (wfTy k0 T) := match H18 in (wfTm _ s12) return match s12 return Prop with
    | (abs T t) => (wfTy k0 T)
    | _ => True
  end with
    | (wfTm_abs T H2 t H3) => H2
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k0 : Hvl) (T : Ty) (t : Tm) (H18 : (wfTm k0 (abs T t))) : (wfTm (HS TmVar k0) t) := match H18 in (wfTm _ s12) return match s12 return Prop with
    | (abs T t) => (wfTm (HS TmVar k0) t)
    | _ => True
  end with
    | (wfTm_abs T H2 t H3) => H3
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k1 : Hvl) (t1 : Tm) (t2 : Tm) (H19 : (wfTm k1 (app t1 t2))) : (wfTm k1 t1) := match H19 in (wfTm _ s13) return match s13 return Prop with
    | (app t1 t2) => (wfTm k1 t1)
    | _ => True
  end with
    | (wfTm_app t1 H4 t2 H5) => H4
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k1 : Hvl) (t1 : Tm) (t2 : Tm) (H19 : (wfTm k1 (app t1 t2))) : (wfTm k1 t2) := match H19 in (wfTm _ s13) return match s13 return Prop with
    | (app t1 t2) => (wfTm k1 t2)
    | _ => True
  end with
    | (wfTm_app t1 H4 t2 H5) => H5
    | _ => I
  end.
  Definition inversion_wfTm_all_1 (k2 : Hvl) (T : Ty) (t : Tm) (H20 : (wfTm k2 (all T t))) : (wfTy k2 T) := match H20 in (wfTm _ s14) return match s14 return Prop with
    | (all T t) => (wfTy k2 T)
    | _ => True
  end with
    | (wfTm_all T H6 t H7) => H6
    | _ => I
  end.
  Definition inversion_wfTm_all_2 (k2 : Hvl) (T : Ty) (t : Tm) (H20 : (wfTm k2 (all T t))) : (wfTm (HS TmVar k2) t) := match H20 in (wfTm _ s14) return match s14 return Prop with
    | (all T t) => (wfTm (HS TmVar k2) t)
    | _ => True
  end with
    | (wfTm_all T H6 t H7) => H7
    | _ => I
  end.
  Definition inversion_wfTy_tvar_1 (k3 : Hvl) (X : (Index TyVar)) (H21 : (wfTy k3 (tvar X))) : (wfindex k3 X) := match H21 in (wfTy _ S34) return match S34 return Prop with
    | (tvar X) => (wfindex k3 X)
    | _ => True
  end with
    | (wfTy_tvar X H8) => H8
    | _ => I
  end.
  Definition inversion_wfTy_tpi_1 (k4 : Hvl) (T1 : Ty) (T2 : Ty) (H22 : (wfTy k4 (tpi T1 T2))) : (wfTy k4 T1) := match H22 in (wfTy _ S35) return match S35 return Prop with
    | (tpi T1 T2) => (wfTy k4 T1)
    | _ => True
  end with
    | (wfTy_tpi T1 H9 T2 H10) => H9
    | _ => I
  end.
  Definition inversion_wfTy_tpi_2 (k4 : Hvl) (T1 : Ty) (T2 : Ty) (H22 : (wfTy k4 (tpi T1 T2))) : (wfTy (HS TmVar k4) T2) := match H22 in (wfTy _ S35) return match S35 return Prop with
    | (tpi T1 T2) => (wfTy (HS TmVar k4) T2)
    | _ => True
  end with
    | (wfTy_tpi T1 H9 T2 H10) => H10
    | _ => I
  end.
  Definition inversion_wfTy_tapp_0 (k5 : Hvl) (T : Ty) (t : Tm) (H23 : (wfTy k5 (tapp T t))) : (wfTy k5 T) := match H23 in (wfTy _ S36) return match S36 return Prop with
    | (tapp T t) => (wfTy k5 T)
    | _ => True
  end with
    | (wfTy_tapp T H11 t H12) => H11
    | _ => I
  end.
  Definition inversion_wfTy_tapp_1 (k5 : Hvl) (T : Ty) (t : Tm) (H23 : (wfTy k5 (tapp T t))) : (wfTm k5 t) := match H23 in (wfTy _ S36) return match S36 return Prop with
    | (tapp T t) => (wfTm k5 t)
    | _ => True
  end with
    | (wfTy_tapp T H11 t H12) => H12
    | _ => I
  end.
  Definition inversion_wfKind_kpi_1 (k9 : Hvl) (T : Ty) (K : Kind) (H27 : (wfKind k9 (kpi T K))) : (wfTy k9 T) := match H27 in (wfKind _ K43) return match K43 return Prop with
    | (kpi T K) => (wfTy k9 T)
    | _ => True
  end with
    | (wfKind_kpi T H13 K H14) => H13
    | _ => I
  end.
  Definition inversion_wfKind_kpi_2 (k9 : Hvl) (T : Ty) (K : Kind) (H27 : (wfKind k9 (kpi T K))) : (wfKind (HS TmVar k9) K) := match H27 in (wfKind _ K43) return match K43 return Prop with
    | (kpi T K) => (wfKind (HS TmVar k9) K)
    | _ => True
  end with
    | (wfKind_kpi T H13 K H14) => H14
    | _ => I
  end.
  Scheme ind_wfTm := Induction for wfTm Sort Prop
  with ind_wfTy := Induction for wfTy Sort Prop.
  Combined Scheme ind_wfTm_Ty from ind_wfTm, ind_wfTy.
  Scheme ind_wfKind := Induction for wfKind Sort Prop.
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
        (shifthvl_TmVar c k10 k11) -> (shifthvl_TmVar (CS c) (HS TmVar k10) (HS TmVar k11))
    | shifthvl_TmVar_there_TyVar
        (c : (Cutoff TmVar)) (k10 : Hvl)
        (k11 : Hvl) :
        (shifthvl_TmVar c k10 k11) -> (shifthvl_TmVar c (HS TyVar k10) (HS TyVar k11)).
  Inductive shifthvl_TyVar : (forall (c : (Cutoff TyVar)) (k10 : Hvl) (k11 : Hvl) ,
    Prop) :=
    | shifthvl_TyVar_here
        (k10 : Hvl) :
        (shifthvl_TyVar C0 k10 (HS TyVar k10))
    | shifthvl_TyVar_there_TmVar
        (c : (Cutoff TyVar)) (k10 : Hvl)
        (k11 : Hvl) :
        (shifthvl_TyVar c k10 k11) -> (shifthvl_TyVar c (HS TmVar k10) (HS TmVar k11))
    | shifthvl_TyVar_there_TyVar
        (c : (Cutoff TyVar)) (k10 : Hvl)
        (k11 : Hvl) :
        (shifthvl_TyVar c k10 k11) -> (shifthvl_TyVar (CS c) (HS TyVar k10) (HS TyVar k11)).
  Lemma weaken_shifthvl_TmVar  :
    (forall (k10 : Hvl) {c : (Cutoff TmVar)} {k11 : Hvl} {k12 : Hvl} ,
      (shifthvl_TmVar c k11 k12) -> (shifthvl_TmVar (weakenCutoffTmVar c k10) (appendHvl k11 k10) (appendHvl k12 k10))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_TyVar  :
    (forall (k10 : Hvl) {c : (Cutoff TyVar)} {k11 : Hvl} {k12 : Hvl} ,
      (shifthvl_TyVar c k11 k12) -> (shifthvl_TyVar (weakenCutoffTyVar c k10) (appendHvl k11 k10) (appendHvl k12 k10))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_TmVar  :
    (forall (c : (Cutoff TmVar)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) (x51 : (Index TmVar)) ,
      (wfindex k10 x51) -> (wfindex k11 (shiftIndex c x51))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_TyVar  :
    (forall (c : (Cutoff TmVar)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) (X5 : (Index TyVar)) ,
      (wfindex k10 X5) -> (wfindex k11 X5)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_TmVar  :
    (forall (c : (Cutoff TyVar)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_TyVar c k10 k11)) (x51 : (Index TmVar)) ,
      (wfindex k10 x51) -> (wfindex k11 x51)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_TyVar  :
    (forall (c : (Cutoff TyVar)) (k10 : Hvl) (k11 : Hvl) (ins : (shifthvl_TyVar c k10 k11)) (X5 : (Index TyVar)) ,
      (wfindex k10 X5) -> (wfindex k11 (tshiftIndex c X5))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTm_Ty : (forall (k10 : Hvl) ,
    (forall (s15 : Tm) (wf : (wfTm k10 s15)) ,
      (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
        (shifthvl_TmVar c k10 k11) -> (wfTm k11 (shiftTm c s15)))) /\
    (forall (S39 : Ty) (wf : (wfTy k10 S39)) ,
      (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
        (shifthvl_TmVar c k10 k11) -> (wfTy k11 (shiftTy c S39))))) := (ind_wfTm_Ty (fun (k10 : Hvl) (s15 : Tm) (wf : (wfTm k10 s15)) =>
    (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
      (shifthvl_TmVar c k10 k11) -> (wfTm k11 (shiftTm c s15)))) (fun (k10 : Hvl) (S39 : Ty) (wf : (wfTy k10 S39)) =>
    (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
      (shifthvl_TmVar c k10 k11) -> (wfTy k11 (shiftTy c S39)))) (fun (k10 : Hvl) (x51 : (Index TmVar)) (wfi : (wfindex k10 x51)) (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTm_var k11 _ (shift_wfindex_TmVar c k10 k11 ins x51 wfi))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) IHT (t : Tm) (wf0 : (wfTm (HS TmVar k10) t)) IHt (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTm_abs k11 (IHT c k11 (weaken_shifthvl_TmVar H0 ins)) (IHt (CS c) (HS TmVar k11) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k10 t2)) IHt2 (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTm_app k11 (IHt1 c k11 (weaken_shifthvl_TmVar H0 ins)) (IHt2 c k11 (weaken_shifthvl_TmVar H0 ins)))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) IHT (t : Tm) (wf0 : (wfTm (HS TmVar k10) t)) IHt (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTm_all k11 (IHT c k11 (weaken_shifthvl_TmVar H0 ins)) (IHt (CS c) (HS TmVar k11) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k10 : Hvl) (X5 : (Index TyVar)) (wfi : (wfindex k10 X5)) (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTy_tvar k11 _ (shift_wfindex_TyVar c k10 k11 ins X5 wfi))) (fun (k10 : Hvl) (T1 : Ty) (wf : (wfTy k10 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS TmVar k10) T2)) IHT2 (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTy_tpi k11 (IHT1 c k11 (weaken_shifthvl_TmVar H0 ins)) (IHT2 (CS c) (HS TmVar k11) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) IHT (t : Tm) (wf0 : (wfTm k10 t)) IHt (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTy_tapp k11 (IHT c k11 (weaken_shifthvl_TmVar H0 ins)) (IHt c k11 (weaken_shifthvl_TmVar H0 ins)))) (fun (k10 : Hvl) (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTy_prop k11)) (fun (k10 : Hvl) (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfTy_prf k11))).
  Lemma shift_wfTm (k10 : Hvl) :
    (forall (s15 : Tm) (wf : (wfTm k10 s15)) ,
      (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
        (shifthvl_TmVar c k10 k11) -> (wfTm k11 (shiftTm c s15)))).
  Proof.
    pose proof ((shift_wfTm_Ty k10)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_wfTy (k10 : Hvl) :
    (forall (S39 : Ty) (wf0 : (wfTy k10 S39)) ,
      (forall (c0 : (Cutoff TmVar)) (k12 : Hvl) ,
        (shifthvl_TmVar c0 k10 k12) -> (wfTy k12 (shiftTy c0 S39)))).
  Proof.
    pose proof ((shift_wfTm_Ty k10)).
    destruct_conjs .
    easy .
  Qed.
  Definition tshift_wfTm_Ty : (forall (k10 : Hvl) ,
    (forall (s15 : Tm) (wf : (wfTm k10 s15)) ,
      (forall (c : (Cutoff TyVar)) (k11 : Hvl) ,
        (shifthvl_TyVar c k10 k11) -> (wfTm k11 (tshiftTm c s15)))) /\
    (forall (S39 : Ty) (wf : (wfTy k10 S39)) ,
      (forall (c : (Cutoff TyVar)) (k11 : Hvl) ,
        (shifthvl_TyVar c k10 k11) -> (wfTy k11 (tshiftTy c S39))))) := (ind_wfTm_Ty (fun (k10 : Hvl) (s15 : Tm) (wf : (wfTm k10 s15)) =>
    (forall (c : (Cutoff TyVar)) (k11 : Hvl) ,
      (shifthvl_TyVar c k10 k11) -> (wfTm k11 (tshiftTm c s15)))) (fun (k10 : Hvl) (S39 : Ty) (wf : (wfTy k10 S39)) =>
    (forall (c : (Cutoff TyVar)) (k11 : Hvl) ,
      (shifthvl_TyVar c k10 k11) -> (wfTy k11 (tshiftTy c S39)))) (fun (k10 : Hvl) (x51 : (Index TmVar)) (wfi : (wfindex k10 x51)) (c : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c k10 k11)) =>
    (wfTm_var k11 _ (tshift_wfindex_TmVar c k10 k11 ins x51 wfi))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) IHT (t : Tm) (wf0 : (wfTm (HS TmVar k10) t)) IHt (c : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c k10 k11)) =>
    (wfTm_abs k11 (IHT c k11 (weaken_shifthvl_TyVar H0 ins)) (IHt c (HS TmVar k11) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k10 : Hvl) (t1 : Tm) (wf : (wfTm k10 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k10 t2)) IHt2 (c : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c k10 k11)) =>
    (wfTm_app k11 (IHt1 c k11 (weaken_shifthvl_TyVar H0 ins)) (IHt2 c k11 (weaken_shifthvl_TyVar H0 ins)))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) IHT (t : Tm) (wf0 : (wfTm (HS TmVar k10) t)) IHt (c : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c k10 k11)) =>
    (wfTm_all k11 (IHT c k11 (weaken_shifthvl_TyVar H0 ins)) (IHt c (HS TmVar k11) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k10 : Hvl) (X5 : (Index TyVar)) (wfi : (wfindex k10 X5)) (c : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c k10 k11)) =>
    (wfTy_tvar k11 _ (tshift_wfindex_TyVar c k10 k11 ins X5 wfi))) (fun (k10 : Hvl) (T1 : Ty) (wf : (wfTy k10 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS TmVar k10) T2)) IHT2 (c : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c k10 k11)) =>
    (wfTy_tpi k11 (IHT1 c k11 (weaken_shifthvl_TyVar H0 ins)) (IHT2 c (HS TmVar k11) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) IHT (t : Tm) (wf0 : (wfTm k10 t)) IHt (c : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c k10 k11)) =>
    (wfTy_tapp k11 (IHT c k11 (weaken_shifthvl_TyVar H0 ins)) (IHt c k11 (weaken_shifthvl_TyVar H0 ins)))) (fun (k10 : Hvl) (c : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c k10 k11)) =>
    (wfTy_prop k11)) (fun (k10 : Hvl) (c : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c k10 k11)) =>
    (wfTy_prf k11))).
  Lemma tshift_wfTm (k10 : Hvl) :
    (forall (s15 : Tm) (wf : (wfTm k10 s15)) ,
      (forall (c : (Cutoff TyVar)) (k11 : Hvl) ,
        (shifthvl_TyVar c k10 k11) -> (wfTm k11 (tshiftTm c s15)))).
  Proof.
    pose proof ((tshift_wfTm_Ty k10)).
    destruct_conjs .
    easy .
  Qed.
  Lemma tshift_wfTy (k10 : Hvl) :
    (forall (S39 : Ty) (wf0 : (wfTy k10 S39)) ,
      (forall (c0 : (Cutoff TyVar)) (k12 : Hvl) ,
        (shifthvl_TyVar c0 k10 k12) -> (wfTy k12 (tshiftTy c0 S39)))).
  Proof.
    pose proof ((tshift_wfTm_Ty k10)).
    destruct_conjs .
    easy .
  Qed.
  Definition shift_wfKind : (forall (k10 : Hvl) ,
    (forall (K44 : Kind) (wf : (wfKind k10 K44)) ,
      (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
        (shifthvl_TmVar c k10 k11) -> (wfKind k11 (shiftKind c K44))))) := (ind_wfKind (fun (k10 : Hvl) (K44 : Kind) (wf : (wfKind k10 K44)) =>
    (forall (c : (Cutoff TmVar)) (k11 : Hvl) ,
      (shifthvl_TmVar c k10 k11) -> (wfKind k11 (shiftKind c K44)))) (fun (k10 : Hvl) (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfKind_star k11)) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) (K : Kind) (wf0 : (wfKind (HS TmVar k10) K)) IHK (c : (Cutoff TmVar)) (k11 : Hvl) (ins : (shifthvl_TmVar c k10 k11)) =>
    (wfKind_kpi k11 (shift_wfTy k10 T wf c k11 (weaken_shifthvl_TmVar H0 ins)) (IHK (CS c) (HS TmVar k11) (weaken_shifthvl_TmVar (HS TmVar H0) ins))))).
  Definition tshift_wfKind : (forall (k10 : Hvl) ,
    (forall (K44 : Kind) (wf : (wfKind k10 K44)) ,
      (forall (c : (Cutoff TyVar)) (k11 : Hvl) ,
        (shifthvl_TyVar c k10 k11) -> (wfKind k11 (tshiftKind c K44))))) := (ind_wfKind (fun (k10 : Hvl) (K44 : Kind) (wf : (wfKind k10 K44)) =>
    (forall (c : (Cutoff TyVar)) (k11 : Hvl) ,
      (shifthvl_TyVar c k10 k11) -> (wfKind k11 (tshiftKind c K44)))) (fun (k10 : Hvl) (c : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c k10 k11)) =>
    (wfKind_star k11)) (fun (k10 : Hvl) (T : Ty) (wf : (wfTy k10 T)) (K : Kind) (wf0 : (wfKind (HS TmVar k10) K)) IHK (c : (Cutoff TyVar)) (k11 : Hvl) (ins : (shifthvl_TyVar c k10 k11)) =>
    (wfKind_kpi k11 (tshift_wfTy k10 T wf c k11 (weaken_shifthvl_TyVar H0 ins)) (IHK c (HS TmVar k11) (weaken_shifthvl_TyVar (HS TmVar H0) ins))))).
  Fixpoint weaken_wfTm (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (s15 : Tm) (wf : (wfTm k11 s15)) ,
    (wfTm (appendHvl k11 k10) (weakenTm s15 k10))) :=
    match k10 return (forall (k11 : Hvl) (s15 : Tm) (wf : (wfTm k11 s15)) ,
      (wfTm (appendHvl k11 k10) (weakenTm s15 k10))) with
      | (H0) => (fun (k11 : Hvl) (s15 : Tm) (wf : (wfTm k11 s15)) =>
        wf)
      | (HS TmVar k10) => (fun (k11 : Hvl) (s15 : Tm) (wf : (wfTm k11 s15)) =>
        (shift_wfTm (appendHvl k11 k10) (weakenTm s15 k10) (weaken_wfTm k10 k11 s15 wf) C0 (HS TmVar (appendHvl k11 k10)) (shifthvl_TmVar_here (appendHvl k11 k10))))
      | (HS TyVar k10) => (fun (k11 : Hvl) (s15 : Tm) (wf : (wfTm k11 s15)) =>
        (tshift_wfTm (appendHvl k11 k10) (weakenTm s15 k10) (weaken_wfTm k10 k11 s15 wf) C0 (HS TyVar (appendHvl k11 k10)) (shifthvl_TyVar_here (appendHvl k11 k10))))
    end.
  Fixpoint weaken_wfTy (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (S39 : Ty) (wf : (wfTy k11 S39)) ,
    (wfTy (appendHvl k11 k10) (weakenTy S39 k10))) :=
    match k10 return (forall (k11 : Hvl) (S39 : Ty) (wf : (wfTy k11 S39)) ,
      (wfTy (appendHvl k11 k10) (weakenTy S39 k10))) with
      | (H0) => (fun (k11 : Hvl) (S39 : Ty) (wf : (wfTy k11 S39)) =>
        wf)
      | (HS TmVar k10) => (fun (k11 : Hvl) (S39 : Ty) (wf : (wfTy k11 S39)) =>
        (shift_wfTy (appendHvl k11 k10) (weakenTy S39 k10) (weaken_wfTy k10 k11 S39 wf) C0 (HS TmVar (appendHvl k11 k10)) (shifthvl_TmVar_here (appendHvl k11 k10))))
      | (HS TyVar k10) => (fun (k11 : Hvl) (S39 : Ty) (wf : (wfTy k11 S39)) =>
        (tshift_wfTy (appendHvl k11 k10) (weakenTy S39 k10) (weaken_wfTy k10 k11 S39 wf) C0 (HS TyVar (appendHvl k11 k10)) (shifthvl_TyVar_here (appendHvl k11 k10))))
    end.
  Fixpoint weaken_wfKind (k10 : Hvl) {struct k10} :
  (forall (k11 : Hvl) (K44 : Kind) (wf : (wfKind k11 K44)) ,
    (wfKind (appendHvl k11 k10) (weakenKind K44 k10))) :=
    match k10 return (forall (k11 : Hvl) (K44 : Kind) (wf : (wfKind k11 K44)) ,
      (wfKind (appendHvl k11 k10) (weakenKind K44 k10))) with
      | (H0) => (fun (k11 : Hvl) (K44 : Kind) (wf : (wfKind k11 K44)) =>
        wf)
      | (HS TmVar k10) => (fun (k11 : Hvl) (K44 : Kind) (wf : (wfKind k11 K44)) =>
        (shift_wfKind (appendHvl k11 k10) (weakenKind K44 k10) (weaken_wfKind k10 k11 K44 wf) C0 (HS TmVar (appendHvl k11 k10)) (shifthvl_TmVar_here (appendHvl k11 k10))))
      | (HS TyVar k10) => (fun (k11 : Hvl) (K44 : Kind) (wf : (wfKind k11 K44)) =>
        (tshift_wfKind (appendHvl k11 k10) (weakenKind K44 k10) (weaken_wfKind k10 k11 K44 wf) C0 (HS TyVar (appendHvl k11 k10)) (shifthvl_TyVar_here (appendHvl k11 k10))))
    end.
End ShiftWellFormed.
Lemma wfTm_cast  :
  (forall (k10 : Hvl) (s15 : Tm) (k11 : Hvl) (s16 : Tm) ,
    (k10 = k11) -> (s15 = s16) -> (wfTm k10 s15) -> (wfTm k11 s16)).
Proof.
  congruence .
Qed.
Lemma wfTy_cast  :
  (forall (k10 : Hvl) (S39 : Ty) (k11 : Hvl) (S40 : Ty) ,
    (k10 = k11) -> (S39 = S40) -> (wfTy k10 S39) -> (wfTy k11 S40)).
Proof.
  congruence .
Qed.
Lemma wfKind_cast  :
  (forall (k10 : Hvl) (K44 : Kind) (k11 : Hvl) (K45 : Kind) ,
    (k10 = k11) -> (K44 = K45) -> (wfKind k10 K44) -> (wfKind k11 K45)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_wfindex_TmVar shift_wfindex_TyVar tshift_wfindex_TmVar tshift_wfindex_TyVar : infra.
 Hint Resolve shift_wfindex_TmVar shift_wfindex_TyVar tshift_wfindex_TmVar tshift_wfindex_TyVar : shift.
 Hint Resolve shift_wfindex_TmVar shift_wfindex_TyVar tshift_wfindex_TmVar tshift_wfindex_TyVar : shift_wf.
 Hint Resolve shift_wfindex_TmVar shift_wfindex_TyVar tshift_wfindex_TmVar tshift_wfindex_TyVar : wf.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : infra.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : shift.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : shift_wf.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : wf.
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
  Inductive substhvl_TmVar (k10 : Hvl) : (forall (d : (Trace TmVar)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | substhvl_TmVar_here :
        (substhvl_TmVar k10 X0 (HS TmVar k10) k10)
    | substhvl_TmVar_there_TmVar
        {d : (Trace TmVar)} {k11 : Hvl}
        {k12 : Hvl} :
        (substhvl_TmVar k10 d k11 k12) -> (substhvl_TmVar k10 (XS TmVar d) (HS TmVar k11) (HS TmVar k12))
    | substhvl_TmVar_there_TyVar
        {d : (Trace TmVar)} {k11 : Hvl}
        {k12 : Hvl} :
        (substhvl_TmVar k10 d k11 k12) -> (substhvl_TmVar k10 (XS TyVar d) (HS TyVar k11) (HS TyVar k12)).
  Inductive substhvl_TyVar (k10 : Hvl) : (forall (d : (Trace TyVar)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | substhvl_TyVar_here :
        (substhvl_TyVar k10 X0 (HS TyVar k10) k10)
    | substhvl_TyVar_there_TmVar
        {d : (Trace TyVar)} {k11 : Hvl}
        {k12 : Hvl} :
        (substhvl_TyVar k10 d k11 k12) -> (substhvl_TyVar k10 (XS TmVar d) (HS TmVar k11) (HS TmVar k12))
    | substhvl_TyVar_there_TyVar
        {d : (Trace TyVar)} {k11 : Hvl}
        {k12 : Hvl} :
        (substhvl_TyVar k10 d k11 k12) -> (substhvl_TyVar k10 (XS TyVar d) (HS TyVar k11) (HS TyVar k12)).
  Lemma weaken_substhvl_TmVar  :
    (forall {k11 : Hvl} (k10 : Hvl) {d : (Trace TmVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TmVar k11 d k12 k13) -> (substhvl_TmVar k11 (weakenTrace d k10) (appendHvl k12 k10) (appendHvl k13 k10))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_TyVar  :
    (forall {k11 : Hvl} (k10 : Hvl) {d : (Trace TyVar)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_TyVar k11 d k12 k13) -> (substhvl_TyVar k11 (weakenTrace d k10) (appendHvl k12 k10) (appendHvl k13 k10))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_TmVar_wfindex_TmVar {k10 : Hvl} {s15 : Tm} (wft : (wfTm k10 s15)) :
    (forall {d : (Trace TmVar)} {k11 : Hvl} {k12 : Hvl} ,
      (substhvl_TmVar k10 d k11 k12) -> (forall {x51 : (Index TmVar)} ,
        (wfindex k11 x51) -> (wfTm k12 (substIndex d s15 x51)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TyVar_wfindex_TyVar {k10 : Hvl} {S39 : Ty} (wft : (wfTy k10 S39)) :
    (forall {d : (Trace TyVar)} {k11 : Hvl} {k12 : Hvl} ,
      (substhvl_TyVar k10 d k11 k12) -> (forall {X5 : (Index TyVar)} ,
        (wfindex k11 X5) -> (wfTy k12 (tsubstIndex d S39 X5)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TmVar_wfindex_TyVar {k10 : Hvl} :
    (forall {d : (Trace TmVar)} {k11 : Hvl} {k12 : Hvl} ,
      (substhvl_TmVar k10 d k11 k12) -> (forall {X5 : (Index TyVar)} ,
        (wfindex k11 X5) -> (wfindex k12 X5))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_TyVar_wfindex_TmVar {k10 : Hvl} :
    (forall {d : (Trace TyVar)} {k11 : Hvl} {k12 : Hvl} ,
      (substhvl_TyVar k10 d k11 k12) -> (forall {x51 : (Index TmVar)} ,
        (wfindex k11 x51) -> (wfindex k12 x51))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_TmVar_wfTm_Ty {k10 : Hvl} {s15 : Tm} (wf : (wfTm k10 s15)) : (forall (k11 : Hvl) ,
    (forall (s16 : Tm) (wf0 : (wfTm k11 s16)) ,
      (forall {d : (Trace TmVar)} {k12 : Hvl} ,
        (substhvl_TmVar k10 d k11 k12) -> (wfTm k12 (substTm d s15 s16)))) /\
    (forall (S39 : Ty) (wf0 : (wfTy k11 S39)) ,
      (forall {d : (Trace TmVar)} {k12 : Hvl} ,
        (substhvl_TmVar k10 d k11 k12) -> (wfTy k12 (substTy d s15 S39))))) := (ind_wfTm_Ty (fun (k11 : Hvl) (s16 : Tm) (wf0 : (wfTm k11 s16)) =>
    (forall {d : (Trace TmVar)} {k12 : Hvl} ,
      (substhvl_TmVar k10 d k11 k12) -> (wfTm k12 (substTm d s15 s16)))) (fun (k11 : Hvl) (S39 : Ty) (wf0 : (wfTy k11 S39)) =>
    (forall {d : (Trace TmVar)} {k12 : Hvl} ,
      (substhvl_TmVar k10 d k11 k12) -> (wfTy k12 (substTy d s15 S39)))) (fun (k11 : Hvl) {x51 : (Index TmVar)} (wfi : (wfindex k11 x51)) {d : (Trace TmVar)} {k12 : Hvl} (del : (substhvl_TmVar k10 d k11 k12)) =>
    (substhvl_TmVar_wfindex_TmVar wf del wfi)) (fun (k11 : Hvl) (T : Ty) (wf0 : (wfTy k11 T)) IHT (t : Tm) (wf1 : (wfTm (HS TmVar k11) t)) IHt {d : (Trace TmVar)} {k12 : Hvl} (del : (substhvl_TmVar k10 d k11 k12)) =>
    (wfTm_abs k12 (IHT (weakenTrace d H0) k12 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d (HS TmVar H0)) (HS TmVar k12) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k11 : Hvl) (t1 : Tm) (wf0 : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k11 t2)) IHt2 {d : (Trace TmVar)} {k12 : Hvl} (del : (substhvl_TmVar k10 d k11 k12)) =>
    (wfTm_app k12 (IHt1 (weakenTrace d H0) k12 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d H0) k12 (weaken_substhvl_TmVar H0 del)))) (fun (k11 : Hvl) (T : Ty) (wf0 : (wfTy k11 T)) IHT (t : Tm) (wf1 : (wfTm (HS TmVar k11) t)) IHt {d : (Trace TmVar)} {k12 : Hvl} (del : (substhvl_TmVar k10 d k11 k12)) =>
    (wfTm_all k12 (IHT (weakenTrace d H0) k12 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d (HS TmVar H0)) (HS TmVar k12) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k11 : Hvl) {X5 : (Index TyVar)} (wfi : (wfindex k11 X5)) {d : (Trace TmVar)} {k12 : Hvl} (del : (substhvl_TmVar k10 d k11 k12)) =>
    (wfTy_tvar k12 _ (substhvl_TmVar_wfindex_TyVar del wfi))) (fun (k11 : Hvl) (T1 : Ty) (wf0 : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS TmVar k11) T2)) IHT2 {d : (Trace TmVar)} {k12 : Hvl} (del : (substhvl_TmVar k10 d k11 k12)) =>
    (wfTy_tpi k12 (IHT1 (weakenTrace d H0) k12 (weaken_substhvl_TmVar H0 del)) (IHT2 (weakenTrace d (HS TmVar H0)) (HS TmVar k12) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k11 : Hvl) (T : Ty) (wf0 : (wfTy k11 T)) IHT (t : Tm) (wf1 : (wfTm k11 t)) IHt {d : (Trace TmVar)} {k12 : Hvl} (del : (substhvl_TmVar k10 d k11 k12)) =>
    (wfTy_tapp k12 (IHT (weakenTrace d H0) k12 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d H0) k12 (weaken_substhvl_TmVar H0 del)))) (fun (k11 : Hvl) {d : (Trace TmVar)} {k12 : Hvl} (del : (substhvl_TmVar k10 d k11 k12)) =>
    (wfTy_prop k12)) (fun (k11 : Hvl) {d : (Trace TmVar)} {k12 : Hvl} (del : (substhvl_TmVar k10 d k11 k12)) =>
    (wfTy_prf k12))).
  Lemma substhvl_TmVar_wfTm {k10 : Hvl} {s15 : Tm} (wf : (wfTm k10 s15)) (k11 : Hvl) (s16 : Tm) (wf0 : (wfTm k11 s16)) :
    (forall {d : (Trace TmVar)} {k12 : Hvl} ,
      (substhvl_TmVar k10 d k11 k12) -> (wfTm k12 (substTm d s15 s16))).
  Proof.
    apply ((substhvl_TmVar_wfTm_Ty wf k11)).
    auto .
  Qed.
  Lemma substhvl_TmVar_wfTy {k10 : Hvl} {s15 : Tm} (wf : (wfTm k10 s15)) (k11 : Hvl) (S39 : Ty) (wf1 : (wfTy k11 S39)) :
    (forall {d0 : (Trace TmVar)} {k13 : Hvl} ,
      (substhvl_TmVar k10 d0 k11 k13) -> (wfTy k13 (substTy d0 s15 S39))).
  Proof.
    apply ((substhvl_TmVar_wfTm_Ty wf k11)).
    auto .
  Qed.
  Definition substhvl_TyVar_wfTm_Ty {k10 : Hvl} {S39 : Ty} (wf : (wfTy k10 S39)) : (forall (k11 : Hvl) ,
    (forall (s15 : Tm) (wf0 : (wfTm k11 s15)) ,
      (forall {d : (Trace TyVar)} {k12 : Hvl} ,
        (substhvl_TyVar k10 d k11 k12) -> (wfTm k12 (tsubstTm d S39 s15)))) /\
    (forall (S40 : Ty) (wf0 : (wfTy k11 S40)) ,
      (forall {d : (Trace TyVar)} {k12 : Hvl} ,
        (substhvl_TyVar k10 d k11 k12) -> (wfTy k12 (tsubstTy d S39 S40))))) := (ind_wfTm_Ty (fun (k11 : Hvl) (s15 : Tm) (wf0 : (wfTm k11 s15)) =>
    (forall {d : (Trace TyVar)} {k12 : Hvl} ,
      (substhvl_TyVar k10 d k11 k12) -> (wfTm k12 (tsubstTm d S39 s15)))) (fun (k11 : Hvl) (S40 : Ty) (wf0 : (wfTy k11 S40)) =>
    (forall {d : (Trace TyVar)} {k12 : Hvl} ,
      (substhvl_TyVar k10 d k11 k12) -> (wfTy k12 (tsubstTy d S39 S40)))) (fun (k11 : Hvl) {x51 : (Index TmVar)} (wfi : (wfindex k11 x51)) {d : (Trace TyVar)} {k12 : Hvl} (del : (substhvl_TyVar k10 d k11 k12)) =>
    (wfTm_var k12 _ (substhvl_TyVar_wfindex_TmVar del wfi))) (fun (k11 : Hvl) (T : Ty) (wf0 : (wfTy k11 T)) IHT (t : Tm) (wf1 : (wfTm (HS TmVar k11) t)) IHt {d : (Trace TyVar)} {k12 : Hvl} (del : (substhvl_TyVar k10 d k11 k12)) =>
    (wfTm_abs k12 (IHT (weakenTrace d H0) k12 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d (HS TmVar H0)) (HS TmVar k12) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k11 : Hvl) (t1 : Tm) (wf0 : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k11 t2)) IHt2 {d : (Trace TyVar)} {k12 : Hvl} (del : (substhvl_TyVar k10 d k11 k12)) =>
    (wfTm_app k12 (IHt1 (weakenTrace d H0) k12 (weaken_substhvl_TyVar H0 del)) (IHt2 (weakenTrace d H0) k12 (weaken_substhvl_TyVar H0 del)))) (fun (k11 : Hvl) (T : Ty) (wf0 : (wfTy k11 T)) IHT (t : Tm) (wf1 : (wfTm (HS TmVar k11) t)) IHt {d : (Trace TyVar)} {k12 : Hvl} (del : (substhvl_TyVar k10 d k11 k12)) =>
    (wfTm_all k12 (IHT (weakenTrace d H0) k12 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d (HS TmVar H0)) (HS TmVar k12) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k11 : Hvl) {X5 : (Index TyVar)} (wfi : (wfindex k11 X5)) {d : (Trace TyVar)} {k12 : Hvl} (del : (substhvl_TyVar k10 d k11 k12)) =>
    (substhvl_TyVar_wfindex_TyVar wf del wfi)) (fun (k11 : Hvl) (T1 : Ty) (wf0 : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS TmVar k11) T2)) IHT2 {d : (Trace TyVar)} {k12 : Hvl} (del : (substhvl_TyVar k10 d k11 k12)) =>
    (wfTy_tpi k12 (IHT1 (weakenTrace d H0) k12 (weaken_substhvl_TyVar H0 del)) (IHT2 (weakenTrace d (HS TmVar H0)) (HS TmVar k12) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k11 : Hvl) (T : Ty) (wf0 : (wfTy k11 T)) IHT (t : Tm) (wf1 : (wfTm k11 t)) IHt {d : (Trace TyVar)} {k12 : Hvl} (del : (substhvl_TyVar k10 d k11 k12)) =>
    (wfTy_tapp k12 (IHT (weakenTrace d H0) k12 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d H0) k12 (weaken_substhvl_TyVar H0 del)))) (fun (k11 : Hvl) {d : (Trace TyVar)} {k12 : Hvl} (del : (substhvl_TyVar k10 d k11 k12)) =>
    (wfTy_prop k12)) (fun (k11 : Hvl) {d : (Trace TyVar)} {k12 : Hvl} (del : (substhvl_TyVar k10 d k11 k12)) =>
    (wfTy_prf k12))).
  Lemma substhvl_TyVar_wfTm {k10 : Hvl} {S39 : Ty} (wf : (wfTy k10 S39)) (k11 : Hvl) (s15 : Tm) (wf0 : (wfTm k11 s15)) :
    (forall {d : (Trace TyVar)} {k12 : Hvl} ,
      (substhvl_TyVar k10 d k11 k12) -> (wfTm k12 (tsubstTm d S39 s15))).
  Proof.
    apply ((substhvl_TyVar_wfTm_Ty wf k11)).
    auto .
  Qed.
  Lemma substhvl_TyVar_wfTy {k10 : Hvl} {S39 : Ty} (wf : (wfTy k10 S39)) (k11 : Hvl) (S40 : Ty) (wf1 : (wfTy k11 S40)) :
    (forall {d0 : (Trace TyVar)} {k13 : Hvl} ,
      (substhvl_TyVar k10 d0 k11 k13) -> (wfTy k13 (tsubstTy d0 S39 S40))).
  Proof.
    apply ((substhvl_TyVar_wfTm_Ty wf k11)).
    auto .
  Qed.
  Definition substhvl_TmVar_wfKind {k10 : Hvl} {s15 : Tm} (wf : (wfTm k10 s15)) : (forall (k11 : Hvl) ,
    (forall (K44 : Kind) (wf0 : (wfKind k11 K44)) ,
      (forall {d : (Trace TmVar)} {k12 : Hvl} ,
        (substhvl_TmVar k10 d k11 k12) -> (wfKind k12 (substKind d s15 K44))))) := (ind_wfKind (fun (k11 : Hvl) (K44 : Kind) (wf0 : (wfKind k11 K44)) =>
    (forall {d : (Trace TmVar)} {k12 : Hvl} ,
      (substhvl_TmVar k10 d k11 k12) -> (wfKind k12 (substKind d s15 K44)))) (fun (k11 : Hvl) {d : (Trace TmVar)} {k12 : Hvl} (del : (substhvl_TmVar k10 d k11 k12)) =>
    (wfKind_star k12)) (fun (k11 : Hvl) (T : Ty) (wf0 : (wfTy k11 T)) (K : Kind) (wf1 : (wfKind (HS TmVar k11) K)) IHK {d : (Trace TmVar)} {k12 : Hvl} (del : (substhvl_TmVar k10 d k11 k12)) =>
    (wfKind_kpi k12 (substhvl_TmVar_wfTy wf k11 T wf0 (weaken_substhvl_TmVar H0 del)) (IHK (weakenTrace d (HS TmVar H0)) (HS TmVar k12) (weaken_substhvl_TmVar (HS TmVar H0) del))))).
  Definition substhvl_TyVar_wfKind {k10 : Hvl} {S39 : Ty} (wf : (wfTy k10 S39)) : (forall (k11 : Hvl) ,
    (forall (K44 : Kind) (wf0 : (wfKind k11 K44)) ,
      (forall {d : (Trace TyVar)} {k12 : Hvl} ,
        (substhvl_TyVar k10 d k11 k12) -> (wfKind k12 (tsubstKind d S39 K44))))) := (ind_wfKind (fun (k11 : Hvl) (K44 : Kind) (wf0 : (wfKind k11 K44)) =>
    (forall {d : (Trace TyVar)} {k12 : Hvl} ,
      (substhvl_TyVar k10 d k11 k12) -> (wfKind k12 (tsubstKind d S39 K44)))) (fun (k11 : Hvl) {d : (Trace TyVar)} {k12 : Hvl} (del : (substhvl_TyVar k10 d k11 k12)) =>
    (wfKind_star k12)) (fun (k11 : Hvl) (T : Ty) (wf0 : (wfTy k11 T)) (K : Kind) (wf1 : (wfKind (HS TmVar k11) K)) IHK {d : (Trace TyVar)} {k12 : Hvl} (del : (substhvl_TyVar k10 d k11 k12)) =>
    (wfKind_kpi k12 (substhvl_TyVar_wfTy wf k11 T wf0 (weaken_substhvl_TyVar H0 del)) (IHK (weakenTrace d (HS TmVar H0)) (HS TmVar k12) (weaken_substhvl_TyVar (HS TmVar H0) del))))).
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
  Fixpoint shiftEnv (c : (Cutoff TmVar)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shiftEnv c G0) (shiftTy (weakenCutoffTmVar c (domainEnv G0)) T))
      | (etvar G0 K) => (etvar (shiftEnv c G0) (shiftKind (weakenCutoffTmVar c (domainEnv G0)) K))
    end.
  Fixpoint tshiftEnv (c : (Cutoff TyVar)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tshiftEnv c G0) (tshiftTy (weakenCutoffTyVar c (domainEnv G0)) T))
      | (etvar G0 K) => (etvar (tshiftEnv c G0) (tshiftKind (weakenCutoffTyVar c (domainEnv G0)) K))
    end.
  Fixpoint weakenEnv (G : Env) (k10 : Hvl) {struct k10} :
  Env :=
    match k10 with
      | (H0) => G
      | (HS TmVar k10) => (shiftEnv C0 (weakenEnv G k10))
      | (HS TyVar k10) => (tshiftEnv C0 (weakenEnv G k10))
    end.
  Fixpoint substEnv (d : (Trace TmVar)) (s15 : Tm) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d s15 G0) (substTy (weakenTrace d (domainEnv G0)) s15 T))
      | (etvar G0 K) => (etvar (substEnv d s15 G0) (substKind (weakenTrace d (domainEnv G0)) s15 K))
    end.
  Fixpoint tsubstEnv (d : (Trace TyVar)) (S39 : Ty) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d S39 G0) (tsubstTy (weakenTrace d (domainEnv G0)) S39 T))
      | (etvar G0 K) => (etvar (tsubstEnv d S39 G0) (tsubstKind (weakenTrace d (domainEnv G0)) S39 K))
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c : (Cutoff TmVar)) (G : Env) ,
      ((domainEnv (shiftEnv c G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_tshiftEnv  :
    (forall (c : (Cutoff TyVar)) (G : Env) ,
      ((domainEnv (tshiftEnv c G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d : (Trace TmVar)) (s15 : Tm) (G : Env) ,
      ((domainEnv (substEnv d s15 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d : (Trace TyVar)) (S39 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d S39 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shiftEnv_appendEnv  :
      (forall (c : (Cutoff TmVar)) (G : Env) (G0 : Env) ,
        ((shiftEnv c (appendEnv G G0)) = (appendEnv (shiftEnv c G) (shiftEnv (weakenCutoffTmVar c (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma tshiftEnv_appendEnv  :
      (forall (c : (Cutoff TyVar)) (G : Env) (G0 : Env) ,
        ((tshiftEnv c (appendEnv G G0)) = (appendEnv (tshiftEnv c G) (tshiftEnv (weakenCutoffTyVar c (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d : (Trace TmVar)) (s15 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d s15 (appendEnv G G0)) = (appendEnv (substEnv d s15 G) (substEnv (weakenTrace d (domainEnv G)) s15 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d : (Trace TyVar)) (S39 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d S39 (appendEnv G G0)) = (appendEnv (tsubstEnv d S39 G) (tsubstEnv (weakenTrace d (domainEnv G)) S39 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTm_append  :
    (forall (s15 : Tm) (k10 : Hvl) (k11 : Hvl) ,
      ((weakenTm (weakenTm s15 k10) k11) = (weakenTm s15 (appendHvl k10 k11)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTy_append  :
    (forall (S39 : Ty) (k10 : Hvl) (k11 : Hvl) ,
      ((weakenTy (weakenTy S39 k10) k11) = (weakenTy S39 (appendHvl k10 k11)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenKind_append  :
    (forall (K44 : Kind) (k10 : Hvl) (k11 : Hvl) ,
      ((weakenKind (weakenKind K44 k10) k11) = (weakenKind K44 (appendHvl k10 k11)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index TmVar) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          (T73 : Ty) :
          (wfTy (domainEnv G) T73) -> (lookup_evar (evar G T73) I0 (shiftTy C0 T73))
      | lookup_evar_there_evar
          {G : Env} {x51 : (Index TmVar)}
          (T74 : Ty) (T75 : Ty) :
          (lookup_evar G x51 T74) -> (lookup_evar (evar G T75) (IS x51) (shiftTy C0 T74))
      | lookup_evar_there_etvar
          {G : Env} {x51 : (Index TmVar)}
          (T74 : Ty) (K44 : Kind) :
          (lookup_evar G x51 T74) -> (lookup_evar (etvar G K44) x51 (tshiftTy C0 T74)).
    Inductive lookup_etvar : Env -> (Index TyVar) -> Kind -> Prop :=
      | lookup_etvar_here {G : Env}
          (K44 : Kind) :
          (wfKind (domainEnv G) K44) -> (lookup_etvar (etvar G K44) I0 (tshiftKind C0 K44))
      | lookup_etvar_there_evar
          {G : Env} {X5 : (Index TyVar)}
          (K45 : Kind) (T74 : Ty) :
          (lookup_etvar G X5 K45) -> (lookup_etvar (evar G T74) X5 (shiftKind C0 K45))
      | lookup_etvar_there_etvar
          {G : Env} {X5 : (Index TyVar)}
          (K45 : Kind) (K46 : Kind) :
          (lookup_etvar G X5 K45) -> (lookup_etvar (etvar G K46) (IS X5) (tshiftKind C0 K45)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (T74 : Ty) (T75 : Ty) ,
        (lookup_evar (evar G T74) I0 T75) -> ((shiftTy C0 T74) = T75)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Env) (K45 : Kind) (K46 : Kind) ,
        (lookup_etvar (etvar G K45) I0 K46) -> ((tshiftKind C0 K45) = K46)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x51 : (Index TmVar)} ,
        (forall (T74 : Ty) ,
          (lookup_evar G x51 T74) -> (forall (T75 : Ty) ,
            (lookup_evar G x51 T75) -> (T74 = T75)))).
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
      (forall {G : Env} {x51 : (Index TmVar)} (T74 : Ty) ,
        (lookup_evar G x51 T74) -> (wfTy (domainEnv G) T74)).
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
      (forall {G : Env} (G0 : Env) {x51 : (Index TmVar)} (T74 : Ty) ,
        (lookup_evar G x51 T74) -> (lookup_evar (appendEnv G G0) (weakenIndexTmVar x51 (domainEnv G0)) (weakenTy T74 (domainEnv G0)))).
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
      (forall {G : Env} {x51 : (Index TmVar)} (T76 : Ty) ,
        (lookup_evar G x51 T76) -> (wfindex (domainEnv G) x51)).
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
        {T74 : Ty} :
        (shift_evar C0 G (evar G T74))
    | shiftevar_there_evar
        {c : (Cutoff TmVar)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c G G0) -> (shift_evar (CS c) (evar G T) (evar G0 (shiftTy c T)))
    | shiftevar_there_etvar
        {c : (Cutoff TmVar)} {G : Env}
        {G0 : Env} {K : Kind} :
        (shift_evar c G G0) -> (shift_evar c (etvar G K) (etvar G0 (shiftKind c K))).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c : (Cutoff TmVar)} {G0 : Env} {G1 : Env} ,
      (shift_evar c G0 G1) -> (shift_evar (weakenCutoffTmVar c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 (shiftEnv c G)))).
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
        (shift_etvar c G G0) -> (shift_etvar c (evar G T) (evar G0 (tshiftTy c T)))
    | shiftetvar_there_etvar
        {c : (Cutoff TyVar)} {G : Env}
        {G0 : Env} {K : Kind} :
        (shift_etvar c G G0) -> (shift_etvar (CS c) (etvar G K) (etvar G0 (tshiftKind c K))).
  Lemma weaken_shift_etvar  :
    (forall (G : Env) {c : (Cutoff TyVar)} {G0 : Env} {G1 : Env} ,
      (shift_etvar c G0 G1) -> (shift_etvar (weakenCutoffTyVar c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 (tshiftEnv c G)))).
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
  Inductive subst_evar (G : Env) (T74 : Ty) (s15 : Tm) : (Trace TmVar) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T74 s15 X0 (evar G T74) G)
    | subst_evar_there_evar
        {d : (Trace TmVar)} {G0 : Env}
        {G1 : Env} (T75 : Ty) :
        (subst_evar G T74 s15 d G0 G1) -> (subst_evar G T74 s15 (XS TmVar d) (evar G0 T75) (evar G1 (substTy d s15 T75)))
    | subst_evar_there_etvar
        {d : (Trace TmVar)} {G0 : Env}
        {G1 : Env} (K45 : Kind) :
        (subst_evar G T74 s15 d G0 G1) -> (subst_evar G T74 s15 (XS TyVar d) (etvar G0 K45) (etvar G1 (substKind d s15 K45))).
  Lemma weaken_subst_evar {G : Env} (T74 : Ty) {s15 : Tm} :
    (forall (G0 : Env) {d : (Trace TmVar)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T74 s15 d G1 G2) -> (subst_evar G T74 s15 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (substEnv d s15 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (K45 : Kind) (S39 : Ty) : (Trace TyVar) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G K45 S39 X0 (etvar G K45) G)
    | subst_etvar_there_evar
        {d : (Trace TyVar)} {G0 : Env}
        {G1 : Env} (T74 : Ty) :
        (subst_etvar G K45 S39 d G0 G1) -> (subst_etvar G K45 S39 (XS TmVar d) (evar G0 T74) (evar G1 (tsubstTy d S39 T74)))
    | subst_etvar_there_etvar
        {d : (Trace TyVar)} {G0 : Env}
        {G1 : Env} (K46 : Kind) :
        (subst_etvar G K45 S39 d G0 G1) -> (subst_etvar G K45 S39 (XS TyVar d) (etvar G0 K46) (etvar G1 (tsubstKind d S39 K46))).
  Lemma weaken_subst_etvar {G : Env} (K45 : Kind) {S39 : Ty} :
    (forall (G0 : Env) {d : (Trace TyVar)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G K45 S39 d G1 G2) -> (subst_etvar G K45 S39 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d S39 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_TmVar {G : Env} {s15 : Tm} (T74 : Ty) :
    (forall {d : (Trace TmVar)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T74 s15 d G0 G1) -> (substhvl_TmVar (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_TyVar {G : Env} {S39 : Ty} (K45 : Kind) :
    (forall {d : (Trace TyVar)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G K45 S39 d G0 G1) -> (substhvl_TyVar (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
End ContextStuff.
 Hint Rewrite domainEnv_shiftEnv domainEnv_tshiftEnv : interaction.
 Hint Rewrite domainEnv_shiftEnv domainEnv_tshiftEnv : env_domain_shift.
 Hint Rewrite domainEnv_substEnv domainEnv_tsubstEnv : interaction.
 Hint Rewrite domainEnv_substEnv domainEnv_tsubstEnv : env_domain_subst.
 Hint Rewrite shiftEnv_appendEnv tshiftEnv_appendEnv : interaction.
 Hint Rewrite shiftEnv_appendEnv tshiftEnv_appendEnv : env_shift_append.
 Hint Rewrite substEnv_appendEnv tsubstEnv_appendEnv : interaction.
 Hint Rewrite substEnv_appendEnv tsubstEnv_appendEnv : env_shift_append.
 Hint Constructors lookup_evar lookup_etvar : infra.
 Hint Constructors lookup_evar lookup_etvar : lookup.
 Hint Constructors lookup_evar lookup_etvar : shift.
 Hint Constructors lookup_evar lookup_etvar : subst.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : infra.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : lookup.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : shift.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : weaken.
Lemma weaken_lookup_evar_here  :
  (forall {G : Env} (G0 : Env) {T74 : Ty} (wf : (wfTy (domainEnv G) T74)) ,
    (lookup_evar (appendEnv (evar G T74) G0) (weakenIndexTmVar I0 (domainEnv G0)) (weakenTy (shiftTy C0 T74) (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) {K45 : Kind} (wf : (wfKind (domainEnv G) K45)) ,
    (lookup_etvar (appendEnv (etvar G K45) G0) (weakenIndexTyVar I0 (domainEnv G0)) (weakenKind (tshiftKind C0 K45) (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfKind wfTm wfTy : infra.
 Hint Constructors wfKind wfTm wfTy : wf.
 Hint Extern 10 ((wfKind _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H34 : (wfTm _ (var _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTm _ (abs _ _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTm _ (app _ _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTm _ (all _ _)) |- _ => inversion H34; subst; clear H34
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H34 : (wfTy _ (tvar _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTy _ (tpi _ _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTy _ (tapp _ _)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTy _ (prop)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfTy _ (prf)) |- _ => inversion H34; subst; clear H34
end : infra wf.
 Hint Extern 2 ((wfKind _ _)) => match goal with
  | H34 : (wfKind _ (star)) |- _ => inversion H34; subst; clear H34
  | H34 : (wfKind _ (kpi _ _)) |- _ => inversion H34; subst; clear H34
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
  (forall {c : (Cutoff TmVar)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {x51 : (Index TmVar)} {T74 : Ty} ,
    (lookup_evar G x51 T74) -> (lookup_evar G0 (shiftIndex c x51) (shiftTy c T74))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c : (Cutoff TmVar)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {X5 : (Index TyVar)} {K45 : Kind} ,
    (lookup_etvar G X5 K45) -> (lookup_etvar G0 X5 (shiftKind c K45))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c : (Cutoff TyVar)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {x51 : (Index TmVar)} {T74 : Ty} ,
    (lookup_evar G x51 T74) -> (lookup_evar G0 x51 (tshiftTy c T74))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c : (Cutoff TyVar)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {X5 : (Index TyVar)} {K45 : Kind} ,
    (lookup_etvar G X5 K45) -> (lookup_etvar G0 (tshiftIndex c X5) (tshiftKind c K45))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} (T75 : Ty) {s15 : Tm} (wf : (wfTm (domainEnv G) s15)) :
  (forall {d : (Trace TmVar)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T75 s15 d G0 G1)) {X5 : (Index TyVar)} (K46 : Kind) ,
    (lookup_etvar G0 X5 K46) -> (lookup_etvar G1 X5 (substKind d s15 K46))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} (K46 : Kind) {S39 : Ty} (wf : (wfTy (domainEnv G) S39)) :
  (forall {d : (Trace TyVar)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G K46 S39 d G0 G1)) {x51 : (Index TmVar)} (T75 : Ty) ,
    (lookup_evar G0 x51 T75) -> (lookup_evar G1 x51 (tsubstTy d S39 T75))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Tm (s11 : Tm) {struct s11} :
nat :=
  match s11 with
    | (var x51) => 1
    | (abs T73 t51) => (plus 1 (plus (size_Ty T73) (size_Tm t51)))
    | (app t52 t53) => (plus 1 (plus (size_Tm t52) (size_Tm t53)))
    | (all T74 t54) => (plus 1 (plus (size_Ty T74) (size_Tm t54)))
  end
with size_Ty (S34 : Ty) {struct S34} :
nat :=
  match S34 with
    | (tvar X5) => 1
    | (tpi T73 T74) => (plus 1 (plus (size_Ty T73) (size_Ty T74)))
    | (tapp T75 t51) => (plus 1 (plus (size_Ty T75) (size_Tm t51)))
    | (prop) => 1
    | (prf) => 1
  end.
Fixpoint size_Kind (K42 : Kind) {struct K42} :
nat :=
  match K42 with
    | (star) => 1
    | (kpi T73 K43) => (plus 1 (plus (size_Ty T73) (size_Kind K43)))
  end.
Fixpoint shift_size_Tm (s11 : Tm) (c : (Cutoff TmVar)) {struct s11} :
((size_Tm (shiftTm c s11)) = (size_Tm s11)) :=
  match s11 return ((size_Tm (shiftTm c s11)) = (size_Tm s11)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Ty T c) (shift_size_Tm t (CS c))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 c)))
    | (all T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Ty T c) (shift_size_Tm t (CS c))))
  end
with shift_size_Ty (S34 : Ty) (c : (Cutoff TmVar)) {struct S34} :
((size_Ty (shiftTy c S34)) = (size_Ty S34)) :=
  match S34 return ((size_Ty (shiftTy c S34)) = (size_Ty S34)) with
    | (tvar _) => eq_refl
    | (tpi T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Ty T1 c) (shift_size_Ty T2 (CS c))))
    | (tapp T t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Ty T c) (shift_size_Tm t c)))
    | (prop) => eq_refl
    | (prf) => eq_refl
  end.
Fixpoint tshift_size_Tm (s11 : Tm) (c : (Cutoff TyVar)) {struct s11} :
((size_Tm (tshiftTm c s11)) = (size_Tm s11)) :=
  match s11 return ((size_Tm (tshiftTm c s11)) = (size_Tm s11)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c) (tshift_size_Tm t c)))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c) (tshift_size_Tm t2 c)))
    | (all T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c) (tshift_size_Tm t c)))
  end
with tshift_size_Ty (S34 : Ty) (c : (Cutoff TyVar)) {struct S34} :
((size_Ty (tshiftTy c S34)) = (size_Ty S34)) :=
  match S34 return ((size_Ty (tshiftTy c S34)) = (size_Ty S34)) with
    | (tvar _) => eq_refl
    | (tpi T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c) (tshift_size_Ty T2 c)))
    | (tapp T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c) (tshift_size_Tm t c)))
    | (prop) => eq_refl
    | (prf) => eq_refl
  end.
Fixpoint shift_size_Kind (K42 : Kind) (c : (Cutoff TmVar)) {struct K42} :
((size_Kind (shiftKind c K42)) = (size_Kind K42)) :=
  match K42 return ((size_Kind (shiftKind c K42)) = (size_Kind K42)) with
    | (star) => eq_refl
    | (kpi T K) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Ty T c) (shift_size_Kind K (CS c))))
  end.
Fixpoint tshift_size_Kind (K42 : Kind) (c : (Cutoff TyVar)) {struct K42} :
((size_Kind (tshiftKind c K42)) = (size_Kind K42)) :=
  match K42 return ((size_Kind (tshiftKind c K42)) = (size_Kind K42)) with
    | (star) => eq_refl
    | (kpi T K) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c) (tshift_size_Kind K c)))
  end.
 Hint Rewrite shift_size_Kind tshift_size_Kind shift_size_Tm tshift_size_Tm shift_size_Ty tshift_size_Ty : interaction.
 Hint Rewrite shift_size_Kind tshift_size_Kind shift_size_Tm tshift_size_Tm shift_size_Ty tshift_size_Ty : shift_size.
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
  (forall (k : Hvl) (S34 : Ty) ,
    ((size_Ty (weakenTy S34 k)) = (size_Ty S34))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Kind weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Kind weaken_size_Tm weaken_size_Ty : weaken_size.
Inductive KindEq (G : Env) : Kind -> Kind -> Prop :=
  | QK_Pi (K1 : Kind)
      (K2 : Kind) (T1 : Ty) (T2 : Ty)
      (jm15 : (TyEq G T1 T2 (star)))
      (jm16 : (KindEq (evar G T1) K1 K2))
      :
      (KindEq G (kpi T1 K1) (kpi T2 K2))
  | QK_Refl (K : Kind)
      (jm17 : (WfKind G K)) :
      (KindEq G K K)
  | QK_Sym (K1 : Kind) (K2 : Kind)
      (jm18 : (KindEq G K1 K2)) :
      (KindEq G K2 K1)
  | QK_Trans (K1 : Kind)
      (K2 : Kind) (K3 : Kind)
      (jm19 : (KindEq G K1 K2))
      (jm20 : (KindEq G K2 K3)) :
      (KindEq G K1 K3)
with TyEq (G : Env) : Ty -> Ty -> Kind -> Prop :=
  | QT_Pi (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm21 : (TyEq G S1 T1 (star)))
      (jm22 : (TyEq (evar G T1) S2 T2 (star)))
      :
      (TyEq G (tpi S1 S2) (tpi T1 T2) (star))
  | QT_App (K : Kind) (S1 : Ty)
      (S2 : Ty) (T : Ty) (t1 : Tm)
      (t2 : Tm)
      (jm23 : (TyEq G S1 S2 (kpi T K)))
      (jm24 : (TermEq G t1 t2 T)) :
      (TyEq G (tapp S1 t1) (tapp S2 t2) (substKind X0 t1 K))
  | QT_All (T : Ty) (t : Tm)
      (jm25 : (Kinding G T (star)))
      (jm26 : (Typing (evar G T) t (prop)))
      :
      (TyEq G (tapp (prf) (all T t)) (tpi T (tapp (prf) t)) (star))
  | QT_Refl (K : Kind) (T : Ty)
      (jm27 : (Kinding G T K)) :
      (TyEq G T T K)
  | QT_Symm (K : Kind) (S1 : Ty)
      (T : Ty)
      (jm28 : (TyEq G T S1 K)) :
      (TyEq G S1 T K)
  | QT_Trans (K : Kind) (S1 : Ty)
      (T : Ty) (U : Ty)
      (jm29 : (TyEq G S1 U K))
      (jm30 : (TyEq G U T K)) :
      (TyEq G S1 T K)
with TermEq (G : Env) : Tm -> Tm -> Ty -> Prop :=
  | Q_Abs (S1 : Ty) (S2 : Ty)
      (T : Ty) (t1 : Tm) (t2 : Tm)
      (jm31 : (TyEq G S1 S2 (star)))
      (jm32 : (TermEq (evar G S1) t1 t2 T))
      :
      (TermEq G (abs S1 t1) (abs S2 t2) (tpi S1 T))
  | Q_App (S1 : Ty) (T : Ty)
      (s1 : Tm) (s2 : Tm) (t1 : Tm)
      (t2 : Tm)
      (jm33 : (TermEq G t1 s1 (tpi S1 T)))
      (jm34 : (TermEq G t2 s2 S1)) :
      (TermEq G (app t1 t2) (app s1 s2) (substTy X0 t2 T))
  | Q_Beta (S1 : Ty) (T : Ty)
      (s : Tm) (t : Tm)
      (jm35 : (Typing (evar G S1) t T))
      (jm36 : (Typing G s S1)) :
      (TermEq G (app (abs S1 t) s) (substTm X0 s t) (substTy X0 s T))
  | Q_Eta (S1 : Ty) (T : Ty)
      (t : Tm)
      (jm37 : (Typing G t (tpi S1 T)))
      :
      (TermEq G (abs S1 (app (weakenTm t (HS TmVar H0)) (var I0))) t (tpi S1 T))
  | Q_Refl (T : Ty) (t : Tm)
      (jm38 : (Typing G t T)) :
      (TermEq G t t T)
  | Q_Symm (T : Ty) (s : Tm)
      (t : Tm)
      (jm39 : (TermEq G t s T)) :
      (TermEq G s t T)
  | Q_Trans (T : Ty) (s : Tm)
      (t : Tm) (u : Tm)
      (jm40 : (TermEq G s u T))
      (jm41 : (TermEq G u t T)) :
      (TermEq G s t T)
with Typing (G : Env) : Tm -> Ty -> Prop :=
  | T_Var (T : Ty)
      (x : (Index TmVar))
      (lk : (lookup_evar G x T))
      (H19 : (wfTy (domainEnv G) T))
      (H20 : (wfindex (domainEnv G) x))
      : (Typing G (var x) T)
  | T_Abs (S1 : Ty) (T : Ty)
      (t : Tm)
      (jm7 : (Kinding G S1 (star)))
      (jm8 : (Typing (evar G S1) t T))
      :
      (Typing G (abs S1 t) (tpi S1 T))
  | T_App (S1 : Ty) (T : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm9 : (Typing G t1 (tpi S1 T)))
      (jm10 : (Typing G t2 S1)) :
      (Typing G (app t1 t2) (substTy X0 t2 T))
  | T_All (T : Ty) (t : Tm)
      (jm11 : (Kinding G T (star)))
      (jm12 : (Typing (evar G T) t (prop)))
      : (Typing G (all T t) (prop))
  | T_Conv (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm13 : (Typing G t T1))
      (jm14 : (TyEq G T1 T2 (star))) :
      (Typing G t T2)
with Kinding (G : Env) : Ty -> Kind -> Prop :=
  | K_TVar (K : Kind)
      (X : (Index TyVar))
      (lk0 : (lookup_etvar G X K))
      (H19 : (wfKind (domainEnv G) K))
      (H20 : (wfindex (domainEnv G) X))
      : (Kinding G (tvar X) K)
  | K_Pi (T1 : Ty) (T2 : Ty)
      (jm1 : (Kinding G T1 (star)))
      (jm2 : (Kinding (evar G T1) T2 (star)))
      : (Kinding G (tpi T1 T2) (star))
  | K_App (K : Kind) (S1 : Ty)
      (T : Ty) (t : Tm)
      (jm3 : (Kinding G S1 (kpi T K)))
      (jm4 : (Typing G t T)) :
      (Kinding G (tapp S1 t) (substKind X0 t K))
  | K_Prop :
      (Kinding G (prop) (star))
  | K_Prf :
      (Kinding G (prf) (kpi (prop) (star)))
  | K_Conv (K1 : Kind) (K2 : Kind)
      (T : Ty)
      (jm5 : (Kinding G T K1))
      (jm6 : (KindEq G K1 K2)) :
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
  (forall (G : Env) (T76 : Ty) (T77 : Ty) (K47 : Kind) (G0 : Env) (T78 : Ty) (T79 : Ty) (K48 : Kind) ,
    (G = G0) -> (T76 = T78) -> (T77 = T79) -> (K47 = K48) -> (TyEq G T76 T77 K47) -> (TyEq G0 T78 T79 K48)).
Proof.
  congruence .
Qed.
Lemma TermEq_cast  :
  (forall (G : Env) (t51 : Tm) (t52 : Tm) (T76 : Ty) (G0 : Env) (t53 : Tm) (t54 : Tm) (T77 : Ty) ,
    (G = G0) -> (t51 = t53) -> (t52 = t54) -> (T76 = T77) -> (TermEq G t51 t52 T76) -> (TermEq G0 t53 t54 T77)).
Proof.
  congruence .
Qed.
Lemma Typing_cast  :
  (forall (G : Env) (t51 : Tm) (T76 : Ty) (G0 : Env) (t52 : Tm) (T77 : Ty) ,
    (G = G0) -> (t51 = t52) -> (T76 = T77) -> (Typing G t51 T76) -> (Typing G0 t52 T77)).
Proof.
  congruence .
Qed.
Lemma Kinding_cast  :
  (forall (G : Env) (T76 : Ty) (K47 : Kind) (G0 : Env) (T77 : Ty) (K48 : Kind) ,
    (G = G0) -> (T76 = T77) -> (K47 = K48) -> (Kinding G T76 K47) -> (Kinding G0 T77 K48)).
Proof.
  congruence .
Qed.
Lemma WfKind_cast  :
  (forall (G : Env) (K47 : Kind) (G0 : Env) (K48 : Kind) ,
    (G = G0) -> (K47 = K48) -> (WfKind G K47) -> (WfKind G0 K48)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_KindEq (G11 : Env) (K62 : Kind) (K63 : Kind) (jm54 : (KindEq G11 K62 K63)) :
(forall (c : (Cutoff TmVar)) (G12 : Env) (H71 : (shift_evar c G11 G12)) ,
  (KindEq G12 (shiftKind c K62) (shiftKind c K63))) :=
  match jm54 in (KindEq _ K62 K63) return (forall (c : (Cutoff TmVar)) (G12 : Env) (H71 : (shift_evar c G11 G12)) ,
    (KindEq G12 (shiftKind c K62) (shiftKind c K63))) with
    | (QK_Pi K59 K60 T87 T88 jm48 jm49) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H71 : (shift_evar c G11 G12)) =>
      (QK_Pi G12 (shiftKind (CS c) K59) (shiftKind (CS c) K60) (shiftTy c T87) (shiftTy c T88) (shift_evar_TyEq G11 T87 T88 (star) jm48 c G12 (weaken_shift_evar empty H71)) (shift_evar_KindEq (evar G11 T87) K59 K60 jm49 (CS c) (evar G12 (shiftTy c T87)) (weaken_shift_evar (evar empty T87) H71))))
    | (QK_Refl K58 jm50) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H71 : (shift_evar c G11 G12)) =>
      (QK_Refl G12 (shiftKind c K58) (shift_evar_WfKind G11 K58 jm50 c G12 (weaken_shift_evar empty H71))))
    | (QK_Sym K59 K60 jm51) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H71 : (shift_evar c G11 G12)) =>
      (QK_Sym G12 (shiftKind c K59) (shiftKind c K60) (shift_evar_KindEq G11 K59 K60 jm51 c G12 (weaken_shift_evar empty H71))))
    | (QK_Trans K59 K60 K61 jm52 jm53) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H71 : (shift_evar c G11 G12)) =>
      (QK_Trans G12 (shiftKind c K59) (shiftKind c K60) (shiftKind c K61) (shift_evar_KindEq G11 K59 K60 jm52 c G12 (weaken_shift_evar empty H71)) (shift_evar_KindEq G11 K60 K61 jm53 c G12 (weaken_shift_evar empty H71))))
  end
with shift_evar_TyEq (G11 : Env) (T90 : Ty) (T91 : Ty) (K59 : Kind) (jm58 : (TyEq G11 T90 T91 K59)) :
(forall (c : (Cutoff TmVar)) (G12 : Env) (H83 : (shift_evar c G11 G12)) ,
  (TyEq G12 (shiftTy c T90) (shiftTy c T91) (shiftKind c K59))) :=
  match jm58 in (TyEq _ T90 T91 K59) return (forall (c : (Cutoff TmVar)) (G12 : Env) (H83 : (shift_evar c G11 G12)) ,
    (TyEq G12 (shiftTy c T90) (shiftTy c T91) (shiftKind c K59))) with
    | (QT_Pi S39 S40 T88 T89 jm48 jm49) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H83 : (shift_evar c G11 G12)) =>
      (QT_Pi G12 (shiftTy c S39) (shiftTy (CS c) S40) (shiftTy c T88) (shiftTy (CS c) T89) (shift_evar_TyEq G11 S39 T88 (star) jm48 c G12 (weaken_shift_evar empty H83)) (shift_evar_TyEq (evar G11 T88) S40 T89 (star) jm49 (CS c) (evar G12 (shiftTy c T88)) (weaken_shift_evar (evar empty T88) H83))))
    | (QT_App K58 S39 S40 T87 t55 t56 jm50 jm51) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H83 : (shift_evar c G11 G12)) =>
      (TyEq_cast G12 _ _ _ G12 (shiftTy c (tapp S39 t55)) (shiftTy c (tapp S40 t56)) (shiftKind c (substKind X0 t55 K58)) eq_refl eq_refl eq_refl (eq_sym (shiftKind_substKind0_comm K58 c t55)) (QT_App G12 (shiftKind (CS c) K58) (shiftTy c S39) (shiftTy c S40) (shiftTy c T87) (shiftTm c t55) (shiftTm c t56) (shift_evar_TyEq G11 S39 S40 (kpi T87 K58) jm50 c G12 (weaken_shift_evar empty H83)) (shift_evar_TermEq G11 t55 t56 T87 jm51 c G12 (weaken_shift_evar empty H83)))))
    | (QT_All T87 t54 jm52 jm53) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H83 : (shift_evar c G11 G12)) =>
      (QT_All G12 (shiftTy c T87) (shiftTm (CS c) t54) (shift_evar_Kinding G11 T87 (star) jm52 c G12 (weaken_shift_evar empty H83)) (shift_evar_Typing (evar G11 T87) t54 (prop) jm53 (CS c) (evar G12 (shiftTy c T87)) (weaken_shift_evar (evar empty T87) H83))))
    | (QT_Refl K58 T87 jm54) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H83 : (shift_evar c G11 G12)) =>
      (QT_Refl G12 (shiftKind c K58) (shiftTy c T87) (shift_evar_Kinding G11 T87 K58 jm54 c G12 (weaken_shift_evar empty H83))))
    | (QT_Symm K58 S39 T87 jm55) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H83 : (shift_evar c G11 G12)) =>
      (QT_Symm G12 (shiftKind c K58) (shiftTy c S39) (shiftTy c T87) (shift_evar_TyEq G11 T87 S39 K58 jm55 c G12 (weaken_shift_evar empty H83))))
    | (QT_Trans K58 S39 T87 U1 jm56 jm57) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H83 : (shift_evar c G11 G12)) =>
      (QT_Trans G12 (shiftKind c K58) (shiftTy c S39) (shiftTy c T87) (shiftTy c U1) (shift_evar_TyEq G11 S39 U1 K58 jm56 c G12 (weaken_shift_evar empty H83)) (shift_evar_TyEq G11 U1 T87 K58 jm57 c G12 (weaken_shift_evar empty H83))))
  end
with shift_evar_TermEq (G11 : Env) (t57 : Tm) (t58 : Tm) (T88 : Ty) (jm59 : (TermEq G11 t57 t58 T88)) :
(forall (c : (Cutoff TmVar)) (G12 : Env) (H89 : (shift_evar c G11 G12)) ,
  (TermEq G12 (shiftTm c t57) (shiftTm c t58) (shiftTy c T88))) :=
  match jm59 in (TermEq _ t57 t58 T88) return (forall (c : (Cutoff TmVar)) (G12 : Env) (H89 : (shift_evar c G11 G12)) ,
    (TermEq G12 (shiftTm c t57) (shiftTm c t58) (shiftTy c T88))) with
    | (Q_Abs S39 S40 T87 t55 t56 jm48 jm49) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H89 : (shift_evar c G11 G12)) =>
      (Q_Abs G12 (shiftTy c S39) (shiftTy c S40) (shiftTy (CS c) T87) (shiftTm (CS c) t55) (shiftTm (CS c) t56) (shift_evar_TyEq G11 S39 S40 (star) jm48 c G12 (weaken_shift_evar empty H89)) (shift_evar_TermEq (evar G11 S39) t55 t56 T87 jm49 (CS c) (evar G12 (shiftTy c S39)) (weaken_shift_evar (evar empty S39) H89))))
    | (Q_App S39 T87 s16 s17 t55 t56 jm50 jm51) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H89 : (shift_evar c G11 G12)) =>
      (TermEq_cast G12 _ _ _ G12 (shiftTm c (app t55 t56)) (shiftTm c (app s16 s17)) (shiftTy c (substTy X0 t56 T87)) eq_refl eq_refl eq_refl (eq_sym (shiftTy_substTy0_comm T87 c t56)) (Q_App G12 (shiftTy c S39) (shiftTy (CS c) T87) (shiftTm c s16) (shiftTm c s17) (shiftTm c t55) (shiftTm c t56) (shift_evar_TermEq G11 t55 s16 (tpi S39 T87) jm50 c G12 (weaken_shift_evar empty H89)) (shift_evar_TermEq G11 t56 s17 S39 jm51 c G12 (weaken_shift_evar empty H89)))))
    | (Q_Beta S39 T87 s15 t54 jm52 jm53) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H89 : (shift_evar c G11 G12)) =>
      (TermEq_cast G12 _ _ _ G12 (shiftTm c (app (abs S39 t54) s15)) (shiftTm c (substTm X0 s15 t54)) (shiftTy c (substTy X0 s15 T87)) eq_refl eq_refl (eq_sym (shiftTm_substTm0_comm t54 c s15)) (eq_sym (shiftTy_substTy0_comm T87 c s15)) (Q_Beta G12 (shiftTy c S39) (shiftTy (CS c) T87) (shiftTm c s15) (shiftTm (CS c) t54) (shift_evar_Typing (evar G11 S39) t54 T87 jm52 (CS c) (evar G12 (shiftTy c S39)) (weaken_shift_evar (evar empty S39) H89)) (shift_evar_Typing G11 s15 S39 jm53 c G12 (weaken_shift_evar empty H89)))))
    | (Q_Eta S39 T87 t54 jm54) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H89 : (shift_evar c G11 G12)) =>
      (TermEq_cast G12 _ _ _ G12 (shiftTm c (abs S39 (app (weakenTm t54 (HS TmVar H0)) (var I0)))) (shiftTm c t54) (shiftTy c (tpi S39 T87)) eq_refl (f_equal2 abs eq_refl (f_equal2 app (weakenTm_shiftTm (HS TmVar H0) c t54) eq_refl)) eq_refl eq_refl (Q_Eta G12 (shiftTy c S39) (shiftTy (CS c) T87) (shiftTm c t54) (shift_evar_Typing G11 t54 (tpi S39 T87) jm54 c G12 (weaken_shift_evar empty H89)))))
    | (Q_Refl T87 t54 jm55) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H89 : (shift_evar c G11 G12)) =>
      (Q_Refl G12 (shiftTy c T87) (shiftTm c t54) (shift_evar_Typing G11 t54 T87 jm55 c G12 (weaken_shift_evar empty H89))))
    | (Q_Symm T87 s15 t54 jm56) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H89 : (shift_evar c G11 G12)) =>
      (Q_Symm G12 (shiftTy c T87) (shiftTm c s15) (shiftTm c t54) (shift_evar_TermEq G11 t54 s15 T87 jm56 c G12 (weaken_shift_evar empty H89))))
    | (Q_Trans T87 s15 t54 u1 jm57 jm58) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H89 : (shift_evar c G11 G12)) =>
      (Q_Trans G12 (shiftTy c T87) (shiftTm c s15) (shiftTm c t54) (shiftTm c u1) (shift_evar_TermEq G11 s15 u1 T87 jm57 c G12 (weaken_shift_evar empty H89)) (shift_evar_TermEq G11 u1 t54 T87 jm58 c G12 (weaken_shift_evar empty H89))))
  end
with shift_evar_Typing (G11 : Env) (t57 : Tm) (T90 : Ty) (jm56 : (Typing G11 t57 T90)) :
(forall (c : (Cutoff TmVar)) (G12 : Env) (H75 : (shift_evar c G11 G12)) ,
  (Typing G12 (shiftTm c t57) (shiftTy c T90))) :=
  match jm56 in (Typing _ t57 T90) return (forall (c : (Cutoff TmVar)) (G12 : Env) (H75 : (shift_evar c G11 G12)) ,
    (Typing G12 (shiftTm c t57) (shiftTy c T90))) with
    | (T_Var T87 x57 lk1 H59 H60) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H75 : (shift_evar c G11 G12)) =>
      (T_Var G12 (shiftTy c T87) (shiftIndex c x57) (shift_evar_lookup_evar H75 lk1) (shift_wfTy _ _ H59 _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H75))) (shift_wfindex_TmVar _ _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H75)) _ H60)))
    | (T_Abs S39 T87 t54 jm53 jm54) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H75 : (shift_evar c G11 G12)) =>
      (T_Abs G12 (shiftTy c S39) (shiftTy (CS c) T87) (shiftTm (CS c) t54) (shift_evar_Kinding G11 S39 (star) jm53 c G12 (weaken_shift_evar empty H75)) (shift_evar_Typing (evar G11 S39) t54 T87 jm54 (CS c) (evar G12 (shiftTy c S39)) (weaken_shift_evar (evar empty S39) H75))))
    | (T_App S39 T87 t55 t56 jm55 jm48) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H75 : (shift_evar c G11 G12)) =>
      (Typing_cast G12 _ _ G12 (shiftTm c (app t55 t56)) (shiftTy c (substTy X0 t56 T87)) eq_refl eq_refl (eq_sym (shiftTy_substTy0_comm T87 c t56)) (T_App G12 (shiftTy c S39) (shiftTy (CS c) T87) (shiftTm c t55) (shiftTm c t56) (shift_evar_Typing G11 t55 (tpi S39 T87) jm55 c G12 (weaken_shift_evar empty H75)) (shift_evar_Typing G11 t56 S39 jm48 c G12 (weaken_shift_evar empty H75)))))
    | (T_All T87 t54 jm49 jm50) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H75 : (shift_evar c G11 G12)) =>
      (T_All G12 (shiftTy c T87) (shiftTm (CS c) t54) (shift_evar_Kinding G11 T87 (star) jm49 c G12 (weaken_shift_evar empty H75)) (shift_evar_Typing (evar G11 T87) t54 (prop) jm50 (CS c) (evar G12 (shiftTy c T87)) (weaken_shift_evar (evar empty T87) H75))))
    | (T_Conv T88 T89 t54 jm51 jm52) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H75 : (shift_evar c G11 G12)) =>
      (T_Conv G12 (shiftTy c T88) (shiftTy c T89) (shiftTm c t54) (shift_evar_Typing G11 t54 T88 jm51 c G12 (weaken_shift_evar empty H75)) (shift_evar_TyEq G11 T88 T89 (star) jm52 c G12 (weaken_shift_evar empty H75))))
  end
with shift_evar_Kinding (G11 : Env) (T90 : Ty) (K61 : Kind) (jm54 : (Kinding G11 T90 K61)) :
(forall (c : (Cutoff TmVar)) (G12 : Env) (H72 : (shift_evar c G11 G12)) ,
  (Kinding G12 (shiftTy c T90) (shiftKind c K61))) :=
  match jm54 in (Kinding _ T90 K61) return (forall (c : (Cutoff TmVar)) (G12 : Env) (H72 : (shift_evar c G11 G12)) ,
    (Kinding G12 (shiftTy c T90) (shiftKind c K61))) with
    | (K_TVar K58 X11 lk1 H59 H60) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H72 : (shift_evar c G11 G12)) =>
      (K_TVar G12 (shiftKind c K58) X11 (shift_evar_lookup_etvar H72 lk1) (shift_wfKind _ _ H59 _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H72))) (shift_wfindex_TyVar _ _ _ (weaken_shifthvl_TmVar H0 (shift_evar_shifthvl_TmVar H72)) _ H60)))
    | (K_Pi T88 T89 jm48 jm49) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H72 : (shift_evar c G11 G12)) =>
      (K_Pi G12 (shiftTy c T88) (shiftTy (CS c) T89) (shift_evar_Kinding G11 T88 (star) jm48 c G12 (weaken_shift_evar empty H72)) (shift_evar_Kinding (evar G11 T88) T89 (star) jm49 (CS c) (evar G12 (shiftTy c T88)) (weaken_shift_evar (evar empty T88) H72))))
    | (K_App K58 S39 T87 t54 jm50 jm51) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H72 : (shift_evar c G11 G12)) =>
      (Kinding_cast G12 _ _ G12 (shiftTy c (tapp S39 t54)) (shiftKind c (substKind X0 t54 K58)) eq_refl eq_refl (eq_sym (shiftKind_substKind0_comm K58 c t54)) (K_App G12 (shiftKind (CS c) K58) (shiftTy c S39) (shiftTy c T87) (shiftTm c t54) (shift_evar_Kinding G11 S39 (kpi T87 K58) jm50 c G12 (weaken_shift_evar empty H72)) (shift_evar_Typing G11 t54 T87 jm51 c G12 (weaken_shift_evar empty H72)))))
    | (K_Prop) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H72 : (shift_evar c G11 G12)) =>
      (K_Prop G12))
    | (K_Prf) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H72 : (shift_evar c G11 G12)) =>
      (K_Prf G12))
    | (K_Conv K59 K60 T87 jm52 jm53) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H72 : (shift_evar c G11 G12)) =>
      (K_Conv G12 (shiftKind c K59) (shiftKind c K60) (shiftTy c T87) (shift_evar_Kinding G11 T87 K59 jm52 c G12 (weaken_shift_evar empty H72)) (shift_evar_KindEq G11 K59 K60 jm53 c G12 (weaken_shift_evar empty H72))))
  end
with shift_evar_WfKind (G11 : Env) (K59 : Kind) (jm50 : (WfKind G11 K59)) :
(forall (c : (Cutoff TmVar)) (G12 : Env) (H62 : (shift_evar c G11 G12)) ,
  (WfKind G12 (shiftKind c K59))) :=
  match jm50 in (WfKind _ K59) return (forall (c : (Cutoff TmVar)) (G12 : Env) (H62 : (shift_evar c G11 G12)) ,
    (WfKind G12 (shiftKind c K59))) with
    | (WfStar) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H62 : (shift_evar c G11 G12)) =>
      (WfStar G12))
    | (WfPi K58 T87 jm48 jm49) => (fun (c : (Cutoff TmVar)) (G12 : Env) (H62 : (shift_evar c G11 G12)) =>
      (WfKind_cast G12 _ G12 (shiftKind c (kpi T87 (weakenKind K58 (HS TmVar H0)))) eq_refl (f_equal2 kpi eq_refl (weakenKind_shiftKind (HS TmVar H0) c K58)) (WfPi G12 (shiftKind c K58) (shiftTy c T87) (shift_evar_Kinding G11 T87 (star) jm48 c G12 (weaken_shift_evar empty H62)) (shift_evar_WfKind G11 K58 jm49 c G12 (weaken_shift_evar empty H62)))))
  end.
Fixpoint shift_etvar_KindEq (G11 : Env) (K62 : Kind) (K63 : Kind) (jm54 : (KindEq G11 K62 K63)) :
(forall (c : (Cutoff TyVar)) (G12 : Env) (H71 : (shift_etvar c G11 G12)) ,
  (KindEq G12 (tshiftKind c K62) (tshiftKind c K63))) :=
  match jm54 in (KindEq _ K62 K63) return (forall (c : (Cutoff TyVar)) (G12 : Env) (H71 : (shift_etvar c G11 G12)) ,
    (KindEq G12 (tshiftKind c K62) (tshiftKind c K63))) with
    | (QK_Pi K59 K60 T87 T88 jm48 jm49) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H71 : (shift_etvar c G11 G12)) =>
      (QK_Pi G12 (tshiftKind c K59) (tshiftKind c K60) (tshiftTy c T87) (tshiftTy c T88) (shift_etvar_TyEq G11 T87 T88 (star) jm48 c G12 (weaken_shift_etvar empty H71)) (shift_etvar_KindEq (evar G11 T87) K59 K60 jm49 c (evar G12 (tshiftTy c T87)) (weaken_shift_etvar (evar empty T87) H71))))
    | (QK_Refl K58 jm50) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H71 : (shift_etvar c G11 G12)) =>
      (QK_Refl G12 (tshiftKind c K58) (shift_etvar_WfKind G11 K58 jm50 c G12 (weaken_shift_etvar empty H71))))
    | (QK_Sym K59 K60 jm51) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H71 : (shift_etvar c G11 G12)) =>
      (QK_Sym G12 (tshiftKind c K59) (tshiftKind c K60) (shift_etvar_KindEq G11 K59 K60 jm51 c G12 (weaken_shift_etvar empty H71))))
    | (QK_Trans K59 K60 K61 jm52 jm53) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H71 : (shift_etvar c G11 G12)) =>
      (QK_Trans G12 (tshiftKind c K59) (tshiftKind c K60) (tshiftKind c K61) (shift_etvar_KindEq G11 K59 K60 jm52 c G12 (weaken_shift_etvar empty H71)) (shift_etvar_KindEq G11 K60 K61 jm53 c G12 (weaken_shift_etvar empty H71))))
  end
with shift_etvar_TyEq (G11 : Env) (T90 : Ty) (T91 : Ty) (K59 : Kind) (jm58 : (TyEq G11 T90 T91 K59)) :
(forall (c : (Cutoff TyVar)) (G12 : Env) (H83 : (shift_etvar c G11 G12)) ,
  (TyEq G12 (tshiftTy c T90) (tshiftTy c T91) (tshiftKind c K59))) :=
  match jm58 in (TyEq _ T90 T91 K59) return (forall (c : (Cutoff TyVar)) (G12 : Env) (H83 : (shift_etvar c G11 G12)) ,
    (TyEq G12 (tshiftTy c T90) (tshiftTy c T91) (tshiftKind c K59))) with
    | (QT_Pi S39 S40 T88 T89 jm48 jm49) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H83 : (shift_etvar c G11 G12)) =>
      (QT_Pi G12 (tshiftTy c S39) (tshiftTy c S40) (tshiftTy c T88) (tshiftTy c T89) (shift_etvar_TyEq G11 S39 T88 (star) jm48 c G12 (weaken_shift_etvar empty H83)) (shift_etvar_TyEq (evar G11 T88) S40 T89 (star) jm49 c (evar G12 (tshiftTy c T88)) (weaken_shift_etvar (evar empty T88) H83))))
    | (QT_App K58 S39 S40 T87 t55 t56 jm50 jm51) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H83 : (shift_etvar c G11 G12)) =>
      (TyEq_cast G12 _ _ _ G12 (tshiftTy c (tapp S39 t55)) (tshiftTy c (tapp S40 t56)) (tshiftKind c (substKind X0 t55 K58)) eq_refl eq_refl eq_refl (eq_sym (tshiftKind_substKind0_comm K58 c t55)) (QT_App G12 (tshiftKind c K58) (tshiftTy c S39) (tshiftTy c S40) (tshiftTy c T87) (tshiftTm c t55) (tshiftTm c t56) (shift_etvar_TyEq G11 S39 S40 (kpi T87 K58) jm50 c G12 (weaken_shift_etvar empty H83)) (shift_etvar_TermEq G11 t55 t56 T87 jm51 c G12 (weaken_shift_etvar empty H83)))))
    | (QT_All T87 t54 jm52 jm53) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H83 : (shift_etvar c G11 G12)) =>
      (QT_All G12 (tshiftTy c T87) (tshiftTm c t54) (shift_etvar_Kinding G11 T87 (star) jm52 c G12 (weaken_shift_etvar empty H83)) (shift_etvar_Typing (evar G11 T87) t54 (prop) jm53 c (evar G12 (tshiftTy c T87)) (weaken_shift_etvar (evar empty T87) H83))))
    | (QT_Refl K58 T87 jm54) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H83 : (shift_etvar c G11 G12)) =>
      (QT_Refl G12 (tshiftKind c K58) (tshiftTy c T87) (shift_etvar_Kinding G11 T87 K58 jm54 c G12 (weaken_shift_etvar empty H83))))
    | (QT_Symm K58 S39 T87 jm55) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H83 : (shift_etvar c G11 G12)) =>
      (QT_Symm G12 (tshiftKind c K58) (tshiftTy c S39) (tshiftTy c T87) (shift_etvar_TyEq G11 T87 S39 K58 jm55 c G12 (weaken_shift_etvar empty H83))))
    | (QT_Trans K58 S39 T87 U1 jm56 jm57) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H83 : (shift_etvar c G11 G12)) =>
      (QT_Trans G12 (tshiftKind c K58) (tshiftTy c S39) (tshiftTy c T87) (tshiftTy c U1) (shift_etvar_TyEq G11 S39 U1 K58 jm56 c G12 (weaken_shift_etvar empty H83)) (shift_etvar_TyEq G11 U1 T87 K58 jm57 c G12 (weaken_shift_etvar empty H83))))
  end
with shift_etvar_TermEq (G11 : Env) (t57 : Tm) (t58 : Tm) (T88 : Ty) (jm59 : (TermEq G11 t57 t58 T88)) :
(forall (c : (Cutoff TyVar)) (G12 : Env) (H89 : (shift_etvar c G11 G12)) ,
  (TermEq G12 (tshiftTm c t57) (tshiftTm c t58) (tshiftTy c T88))) :=
  match jm59 in (TermEq _ t57 t58 T88) return (forall (c : (Cutoff TyVar)) (G12 : Env) (H89 : (shift_etvar c G11 G12)) ,
    (TermEq G12 (tshiftTm c t57) (tshiftTm c t58) (tshiftTy c T88))) with
    | (Q_Abs S39 S40 T87 t55 t56 jm48 jm49) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H89 : (shift_etvar c G11 G12)) =>
      (Q_Abs G12 (tshiftTy c S39) (tshiftTy c S40) (tshiftTy c T87) (tshiftTm c t55) (tshiftTm c t56) (shift_etvar_TyEq G11 S39 S40 (star) jm48 c G12 (weaken_shift_etvar empty H89)) (shift_etvar_TermEq (evar G11 S39) t55 t56 T87 jm49 c (evar G12 (tshiftTy c S39)) (weaken_shift_etvar (evar empty S39) H89))))
    | (Q_App S39 T87 s16 s17 t55 t56 jm50 jm51) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H89 : (shift_etvar c G11 G12)) =>
      (TermEq_cast G12 _ _ _ G12 (tshiftTm c (app t55 t56)) (tshiftTm c (app s16 s17)) (tshiftTy c (substTy X0 t56 T87)) eq_refl eq_refl eq_refl (eq_sym (tshiftTy_substTy0_comm T87 c t56)) (Q_App G12 (tshiftTy c S39) (tshiftTy c T87) (tshiftTm c s16) (tshiftTm c s17) (tshiftTm c t55) (tshiftTm c t56) (shift_etvar_TermEq G11 t55 s16 (tpi S39 T87) jm50 c G12 (weaken_shift_etvar empty H89)) (shift_etvar_TermEq G11 t56 s17 S39 jm51 c G12 (weaken_shift_etvar empty H89)))))
    | (Q_Beta S39 T87 s15 t54 jm52 jm53) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H89 : (shift_etvar c G11 G12)) =>
      (TermEq_cast G12 _ _ _ G12 (tshiftTm c (app (abs S39 t54) s15)) (tshiftTm c (substTm X0 s15 t54)) (tshiftTy c (substTy X0 s15 T87)) eq_refl eq_refl (eq_sym (tshiftTm_substTm0_comm t54 c s15)) (eq_sym (tshiftTy_substTy0_comm T87 c s15)) (Q_Beta G12 (tshiftTy c S39) (tshiftTy c T87) (tshiftTm c s15) (tshiftTm c t54) (shift_etvar_Typing (evar G11 S39) t54 T87 jm52 c (evar G12 (tshiftTy c S39)) (weaken_shift_etvar (evar empty S39) H89)) (shift_etvar_Typing G11 s15 S39 jm53 c G12 (weaken_shift_etvar empty H89)))))
    | (Q_Eta S39 T87 t54 jm54) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H89 : (shift_etvar c G11 G12)) =>
      (TermEq_cast G12 _ _ _ G12 (tshiftTm c (abs S39 (app (weakenTm t54 (HS TmVar H0)) (var I0)))) (tshiftTm c t54) (tshiftTy c (tpi S39 T87)) eq_refl (f_equal2 abs eq_refl (f_equal2 app (weakenTm_tshiftTm (HS TmVar H0) c t54) eq_refl)) eq_refl eq_refl (Q_Eta G12 (tshiftTy c S39) (tshiftTy c T87) (tshiftTm c t54) (shift_etvar_Typing G11 t54 (tpi S39 T87) jm54 c G12 (weaken_shift_etvar empty H89)))))
    | (Q_Refl T87 t54 jm55) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H89 : (shift_etvar c G11 G12)) =>
      (Q_Refl G12 (tshiftTy c T87) (tshiftTm c t54) (shift_etvar_Typing G11 t54 T87 jm55 c G12 (weaken_shift_etvar empty H89))))
    | (Q_Symm T87 s15 t54 jm56) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H89 : (shift_etvar c G11 G12)) =>
      (Q_Symm G12 (tshiftTy c T87) (tshiftTm c s15) (tshiftTm c t54) (shift_etvar_TermEq G11 t54 s15 T87 jm56 c G12 (weaken_shift_etvar empty H89))))
    | (Q_Trans T87 s15 t54 u1 jm57 jm58) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H89 : (shift_etvar c G11 G12)) =>
      (Q_Trans G12 (tshiftTy c T87) (tshiftTm c s15) (tshiftTm c t54) (tshiftTm c u1) (shift_etvar_TermEq G11 s15 u1 T87 jm57 c G12 (weaken_shift_etvar empty H89)) (shift_etvar_TermEq G11 u1 t54 T87 jm58 c G12 (weaken_shift_etvar empty H89))))
  end
with shift_etvar_Typing (G11 : Env) (t57 : Tm) (T90 : Ty) (jm56 : (Typing G11 t57 T90)) :
(forall (c : (Cutoff TyVar)) (G12 : Env) (H75 : (shift_etvar c G11 G12)) ,
  (Typing G12 (tshiftTm c t57) (tshiftTy c T90))) :=
  match jm56 in (Typing _ t57 T90) return (forall (c : (Cutoff TyVar)) (G12 : Env) (H75 : (shift_etvar c G11 G12)) ,
    (Typing G12 (tshiftTm c t57) (tshiftTy c T90))) with
    | (T_Var T87 x57 lk1 H59 H60) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H75 : (shift_etvar c G11 G12)) =>
      (T_Var G12 (tshiftTy c T87) x57 (shift_etvar_lookup_evar H75 lk1) (tshift_wfTy _ _ H59 _ _ (weaken_shifthvl_TyVar H0 (shift_etvar_shifthvl_TyVar H75))) (tshift_wfindex_TmVar _ _ _ (weaken_shifthvl_TyVar H0 (shift_etvar_shifthvl_TyVar H75)) _ H60)))
    | (T_Abs S39 T87 t54 jm53 jm54) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H75 : (shift_etvar c G11 G12)) =>
      (T_Abs G12 (tshiftTy c S39) (tshiftTy c T87) (tshiftTm c t54) (shift_etvar_Kinding G11 S39 (star) jm53 c G12 (weaken_shift_etvar empty H75)) (shift_etvar_Typing (evar G11 S39) t54 T87 jm54 c (evar G12 (tshiftTy c S39)) (weaken_shift_etvar (evar empty S39) H75))))
    | (T_App S39 T87 t55 t56 jm55 jm48) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H75 : (shift_etvar c G11 G12)) =>
      (Typing_cast G12 _ _ G12 (tshiftTm c (app t55 t56)) (tshiftTy c (substTy X0 t56 T87)) eq_refl eq_refl (eq_sym (tshiftTy_substTy0_comm T87 c t56)) (T_App G12 (tshiftTy c S39) (tshiftTy c T87) (tshiftTm c t55) (tshiftTm c t56) (shift_etvar_Typing G11 t55 (tpi S39 T87) jm55 c G12 (weaken_shift_etvar empty H75)) (shift_etvar_Typing G11 t56 S39 jm48 c G12 (weaken_shift_etvar empty H75)))))
    | (T_All T87 t54 jm49 jm50) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H75 : (shift_etvar c G11 G12)) =>
      (T_All G12 (tshiftTy c T87) (tshiftTm c t54) (shift_etvar_Kinding G11 T87 (star) jm49 c G12 (weaken_shift_etvar empty H75)) (shift_etvar_Typing (evar G11 T87) t54 (prop) jm50 c (evar G12 (tshiftTy c T87)) (weaken_shift_etvar (evar empty T87) H75))))
    | (T_Conv T88 T89 t54 jm51 jm52) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H75 : (shift_etvar c G11 G12)) =>
      (T_Conv G12 (tshiftTy c T88) (tshiftTy c T89) (tshiftTm c t54) (shift_etvar_Typing G11 t54 T88 jm51 c G12 (weaken_shift_etvar empty H75)) (shift_etvar_TyEq G11 T88 T89 (star) jm52 c G12 (weaken_shift_etvar empty H75))))
  end
with shift_etvar_Kinding (G11 : Env) (T90 : Ty) (K61 : Kind) (jm54 : (Kinding G11 T90 K61)) :
(forall (c : (Cutoff TyVar)) (G12 : Env) (H72 : (shift_etvar c G11 G12)) ,
  (Kinding G12 (tshiftTy c T90) (tshiftKind c K61))) :=
  match jm54 in (Kinding _ T90 K61) return (forall (c : (Cutoff TyVar)) (G12 : Env) (H72 : (shift_etvar c G11 G12)) ,
    (Kinding G12 (tshiftTy c T90) (tshiftKind c K61))) with
    | (K_TVar K58 X11 lk1 H59 H60) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H72 : (shift_etvar c G11 G12)) =>
      (K_TVar G12 (tshiftKind c K58) (tshiftIndex c X11) (shift_etvar_lookup_etvar H72 lk1) (tshift_wfKind _ _ H59 _ _ (weaken_shifthvl_TyVar H0 (shift_etvar_shifthvl_TyVar H72))) (tshift_wfindex_TyVar _ _ _ (weaken_shifthvl_TyVar H0 (shift_etvar_shifthvl_TyVar H72)) _ H60)))
    | (K_Pi T88 T89 jm48 jm49) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H72 : (shift_etvar c G11 G12)) =>
      (K_Pi G12 (tshiftTy c T88) (tshiftTy c T89) (shift_etvar_Kinding G11 T88 (star) jm48 c G12 (weaken_shift_etvar empty H72)) (shift_etvar_Kinding (evar G11 T88) T89 (star) jm49 c (evar G12 (tshiftTy c T88)) (weaken_shift_etvar (evar empty T88) H72))))
    | (K_App K58 S39 T87 t54 jm50 jm51) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H72 : (shift_etvar c G11 G12)) =>
      (Kinding_cast G12 _ _ G12 (tshiftTy c (tapp S39 t54)) (tshiftKind c (substKind X0 t54 K58)) eq_refl eq_refl (eq_sym (tshiftKind_substKind0_comm K58 c t54)) (K_App G12 (tshiftKind c K58) (tshiftTy c S39) (tshiftTy c T87) (tshiftTm c t54) (shift_etvar_Kinding G11 S39 (kpi T87 K58) jm50 c G12 (weaken_shift_etvar empty H72)) (shift_etvar_Typing G11 t54 T87 jm51 c G12 (weaken_shift_etvar empty H72)))))
    | (K_Prop) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H72 : (shift_etvar c G11 G12)) =>
      (K_Prop G12))
    | (K_Prf) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H72 : (shift_etvar c G11 G12)) =>
      (K_Prf G12))
    | (K_Conv K59 K60 T87 jm52 jm53) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H72 : (shift_etvar c G11 G12)) =>
      (K_Conv G12 (tshiftKind c K59) (tshiftKind c K60) (tshiftTy c T87) (shift_etvar_Kinding G11 T87 K59 jm52 c G12 (weaken_shift_etvar empty H72)) (shift_etvar_KindEq G11 K59 K60 jm53 c G12 (weaken_shift_etvar empty H72))))
  end
with shift_etvar_WfKind (G11 : Env) (K59 : Kind) (jm50 : (WfKind G11 K59)) :
(forall (c : (Cutoff TyVar)) (G12 : Env) (H62 : (shift_etvar c G11 G12)) ,
  (WfKind G12 (tshiftKind c K59))) :=
  match jm50 in (WfKind _ K59) return (forall (c : (Cutoff TyVar)) (G12 : Env) (H62 : (shift_etvar c G11 G12)) ,
    (WfKind G12 (tshiftKind c K59))) with
    | (WfStar) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H62 : (shift_etvar c G11 G12)) =>
      (WfStar G12))
    | (WfPi K58 T87 jm48 jm49) => (fun (c : (Cutoff TyVar)) (G12 : Env) (H62 : (shift_etvar c G11 G12)) =>
      (WfKind_cast G12 _ G12 (tshiftKind c (kpi T87 (weakenKind K58 (HS TmVar H0)))) eq_refl (f_equal2 kpi eq_refl (weakenKind_tshiftKind (HS TmVar H0) c K58)) (WfPi G12 (tshiftKind c K58) (tshiftTy c T87) (shift_etvar_Kinding G11 T87 (star) jm48 c G12 (weaken_shift_etvar empty H62)) (shift_etvar_WfKind G11 K58 jm49 c G12 (weaken_shift_etvar empty H62)))))
  end.
 Hint Resolve shift_evar_KindEq shift_etvar_KindEq shift_evar_Kinding shift_etvar_Kinding shift_evar_TermEq shift_etvar_TermEq shift_evar_TyEq shift_etvar_TyEq shift_evar_Typing shift_etvar_Typing shift_evar_WfKind shift_etvar_WfKind : infra.
 Hint Resolve shift_evar_KindEq shift_etvar_KindEq shift_evar_Kinding shift_etvar_Kinding shift_evar_TermEq shift_etvar_TermEq shift_evar_TyEq shift_etvar_TyEq shift_evar_Typing shift_etvar_Typing shift_evar_WfKind shift_etvar_WfKind : shift.
Fixpoint weaken_KindEq (G : Env) :
(forall (G0 : Env) (K47 : Kind) (K48 : Kind) (jm42 : (KindEq G0 K47 K48)) ,
  (KindEq (appendEnv G0 G) (weakenKind K47 (domainEnv G)) (weakenKind K48 (domainEnv G)))) :=
  match G return (forall (G0 : Env) (K47 : Kind) (K48 : Kind) (jm42 : (KindEq G0 K47 K48)) ,
    (KindEq (appendEnv G0 G) (weakenKind K47 (domainEnv G)) (weakenKind K48 (domainEnv G)))) with
    | (empty) => (fun (G0 : Env) (K47 : Kind) (K48 : Kind) (jm42 : (KindEq G0 K47 K48)) =>
      jm42)
    | (evar G T76) => (fun (G0 : Env) (K47 : Kind) (K48 : Kind) (jm42 : (KindEq G0 K47 K48)) =>
      (shift_evar_KindEq (appendEnv G0 G) (weakenKind K47 (domainEnv G)) (weakenKind K48 (domainEnv G)) (weaken_KindEq G G0 K47 K48 jm42) C0 (evar (appendEnv G0 G) T76) shift_evar_here))
    | (etvar G K49) => (fun (G0 : Env) (K47 : Kind) (K48 : Kind) (jm42 : (KindEq G0 K47 K48)) =>
      (shift_etvar_KindEq (appendEnv G0 G) (weakenKind K47 (domainEnv G)) (weakenKind K48 (domainEnv G)) (weaken_KindEq G G0 K47 K48 jm42) C0 (etvar (appendEnv G0 G) K49) shift_etvar_here))
  end.
Fixpoint weaken_TyEq (G1 : Env) :
(forall (G2 : Env) (T77 : Ty) (T78 : Ty) (K50 : Kind) (jm43 : (TyEq G2 T77 T78 K50)) ,
  (TyEq (appendEnv G2 G1) (weakenTy T77 (domainEnv G1)) (weakenTy T78 (domainEnv G1)) (weakenKind K50 (domainEnv G1)))) :=
  match G1 return (forall (G2 : Env) (T77 : Ty) (T78 : Ty) (K50 : Kind) (jm43 : (TyEq G2 T77 T78 K50)) ,
    (TyEq (appendEnv G2 G1) (weakenTy T77 (domainEnv G1)) (weakenTy T78 (domainEnv G1)) (weakenKind K50 (domainEnv G1)))) with
    | (empty) => (fun (G2 : Env) (T77 : Ty) (T78 : Ty) (K50 : Kind) (jm43 : (TyEq G2 T77 T78 K50)) =>
      jm43)
    | (evar G1 T79) => (fun (G2 : Env) (T77 : Ty) (T78 : Ty) (K50 : Kind) (jm43 : (TyEq G2 T77 T78 K50)) =>
      (shift_evar_TyEq (appendEnv G2 G1) (weakenTy T77 (domainEnv G1)) (weakenTy T78 (domainEnv G1)) (weakenKind K50 (domainEnv G1)) (weaken_TyEq G1 G2 T77 T78 K50 jm43) C0 (evar (appendEnv G2 G1) T79) shift_evar_here))
    | (etvar G1 K51) => (fun (G2 : Env) (T77 : Ty) (T78 : Ty) (K50 : Kind) (jm43 : (TyEq G2 T77 T78 K50)) =>
      (shift_etvar_TyEq (appendEnv G2 G1) (weakenTy T77 (domainEnv G1)) (weakenTy T78 (domainEnv G1)) (weakenKind K50 (domainEnv G1)) (weaken_TyEq G1 G2 T77 T78 K50 jm43) C0 (etvar (appendEnv G2 G1) K51) shift_etvar_here))
  end.
Fixpoint weaken_TermEq (G3 : Env) :
(forall (G4 : Env) (t51 : Tm) (t52 : Tm) (T80 : Ty) (jm44 : (TermEq G4 t51 t52 T80)) ,
  (TermEq (appendEnv G4 G3) (weakenTm t51 (domainEnv G3)) (weakenTm t52 (domainEnv G3)) (weakenTy T80 (domainEnv G3)))) :=
  match G3 return (forall (G4 : Env) (t51 : Tm) (t52 : Tm) (T80 : Ty) (jm44 : (TermEq G4 t51 t52 T80)) ,
    (TermEq (appendEnv G4 G3) (weakenTm t51 (domainEnv G3)) (weakenTm t52 (domainEnv G3)) (weakenTy T80 (domainEnv G3)))) with
    | (empty) => (fun (G4 : Env) (t51 : Tm) (t52 : Tm) (T80 : Ty) (jm44 : (TermEq G4 t51 t52 T80)) =>
      jm44)
    | (evar G3 T81) => (fun (G4 : Env) (t51 : Tm) (t52 : Tm) (T80 : Ty) (jm44 : (TermEq G4 t51 t52 T80)) =>
      (shift_evar_TermEq (appendEnv G4 G3) (weakenTm t51 (domainEnv G3)) (weakenTm t52 (domainEnv G3)) (weakenTy T80 (domainEnv G3)) (weaken_TermEq G3 G4 t51 t52 T80 jm44) C0 (evar (appendEnv G4 G3) T81) shift_evar_here))
    | (etvar G3 K52) => (fun (G4 : Env) (t51 : Tm) (t52 : Tm) (T80 : Ty) (jm44 : (TermEq G4 t51 t52 T80)) =>
      (shift_etvar_TermEq (appendEnv G4 G3) (weakenTm t51 (domainEnv G3)) (weakenTm t52 (domainEnv G3)) (weakenTy T80 (domainEnv G3)) (weaken_TermEq G3 G4 t51 t52 T80 jm44) C0 (etvar (appendEnv G4 G3) K52) shift_etvar_here))
  end.
Fixpoint weaken_Typing (G5 : Env) :
(forall (G6 : Env) (t53 : Tm) (T82 : Ty) (jm45 : (Typing G6 t53 T82)) ,
  (Typing (appendEnv G6 G5) (weakenTm t53 (domainEnv G5)) (weakenTy T82 (domainEnv G5)))) :=
  match G5 return (forall (G6 : Env) (t53 : Tm) (T82 : Ty) (jm45 : (Typing G6 t53 T82)) ,
    (Typing (appendEnv G6 G5) (weakenTm t53 (domainEnv G5)) (weakenTy T82 (domainEnv G5)))) with
    | (empty) => (fun (G6 : Env) (t53 : Tm) (T82 : Ty) (jm45 : (Typing G6 t53 T82)) =>
      jm45)
    | (evar G5 T83) => (fun (G6 : Env) (t53 : Tm) (T82 : Ty) (jm45 : (Typing G6 t53 T82)) =>
      (shift_evar_Typing (appendEnv G6 G5) (weakenTm t53 (domainEnv G5)) (weakenTy T82 (domainEnv G5)) (weaken_Typing G5 G6 t53 T82 jm45) C0 (evar (appendEnv G6 G5) T83) shift_evar_here))
    | (etvar G5 K53) => (fun (G6 : Env) (t53 : Tm) (T82 : Ty) (jm45 : (Typing G6 t53 T82)) =>
      (shift_etvar_Typing (appendEnv G6 G5) (weakenTm t53 (domainEnv G5)) (weakenTy T82 (domainEnv G5)) (weaken_Typing G5 G6 t53 T82 jm45) C0 (etvar (appendEnv G6 G5) K53) shift_etvar_here))
  end.
Fixpoint weaken_Kinding (G7 : Env) :
(forall (G8 : Env) (T84 : Ty) (K54 : Kind) (jm46 : (Kinding G8 T84 K54)) ,
  (Kinding (appendEnv G8 G7) (weakenTy T84 (domainEnv G7)) (weakenKind K54 (domainEnv G7)))) :=
  match G7 return (forall (G8 : Env) (T84 : Ty) (K54 : Kind) (jm46 : (Kinding G8 T84 K54)) ,
    (Kinding (appendEnv G8 G7) (weakenTy T84 (domainEnv G7)) (weakenKind K54 (domainEnv G7)))) with
    | (empty) => (fun (G8 : Env) (T84 : Ty) (K54 : Kind) (jm46 : (Kinding G8 T84 K54)) =>
      jm46)
    | (evar G7 T85) => (fun (G8 : Env) (T84 : Ty) (K54 : Kind) (jm46 : (Kinding G8 T84 K54)) =>
      (shift_evar_Kinding (appendEnv G8 G7) (weakenTy T84 (domainEnv G7)) (weakenKind K54 (domainEnv G7)) (weaken_Kinding G7 G8 T84 K54 jm46) C0 (evar (appendEnv G8 G7) T85) shift_evar_here))
    | (etvar G7 K55) => (fun (G8 : Env) (T84 : Ty) (K54 : Kind) (jm46 : (Kinding G8 T84 K54)) =>
      (shift_etvar_Kinding (appendEnv G8 G7) (weakenTy T84 (domainEnv G7)) (weakenKind K54 (domainEnv G7)) (weaken_Kinding G7 G8 T84 K54 jm46) C0 (etvar (appendEnv G8 G7) K55) shift_etvar_here))
  end.
Fixpoint weaken_WfKind (G9 : Env) :
(forall (G10 : Env) (K56 : Kind) (jm47 : (WfKind G10 K56)) ,
  (WfKind (appendEnv G10 G9) (weakenKind K56 (domainEnv G9)))) :=
  match G9 return (forall (G10 : Env) (K56 : Kind) (jm47 : (WfKind G10 K56)) ,
    (WfKind (appendEnv G10 G9) (weakenKind K56 (domainEnv G9)))) with
    | (empty) => (fun (G10 : Env) (K56 : Kind) (jm47 : (WfKind G10 K56)) =>
      jm47)
    | (evar G9 T86) => (fun (G10 : Env) (K56 : Kind) (jm47 : (WfKind G10 K56)) =>
      (shift_evar_WfKind (appendEnv G10 G9) (weakenKind K56 (domainEnv G9)) (weaken_WfKind G9 G10 K56 jm47) C0 (evar (appendEnv G10 G9) T86) shift_evar_here))
    | (etvar G9 K57) => (fun (G10 : Env) (K56 : Kind) (jm47 : (WfKind G10 K56)) =>
      (shift_etvar_WfKind (appendEnv G10 G9) (weakenKind K56 (domainEnv G9)) (weaken_WfKind G9 G10 K56 jm47) C0 (etvar (appendEnv G10 G9) K57) shift_etvar_here))
  end.
Fixpoint KindEq_wf_0 (G : Env) (K58 : Kind) (K59 : Kind) (jm48 : (KindEq G K58 K59)) {struct jm48} :
(wfKind (domainEnv G) K58) :=
  match jm48 in (KindEq _ K58 K59) return (wfKind (domainEnv G) K58) with
    | (QK_Pi K1 K2 T1 T2 jm15 jm16) => (wfKind_kpi (domainEnv G) (TyEq_wf_0 G T1 T2 (star) jm15) (KindEq_wf_0 (evar G T1) K1 K2 jm16))
    | (QK_Refl K jm17) => (WfKind_wf_0 G K jm17)
    | (QK_Sym K1 K2 jm18) => (KindEq_wf_1 G K1 K2 jm18)
    | (QK_Trans K1 K2 K3 jm19 jm20) => (KindEq_wf_0 G K1 K2 jm19)
  end
with KindEq_wf_1 (G : Env) (K58 : Kind) (K59 : Kind) (jm49 : (KindEq G K58 K59)) {struct jm49} :
(wfKind (domainEnv G) K59) :=
  match jm49 in (KindEq _ K58 K59) return (wfKind (domainEnv G) K59) with
    | (QK_Pi K1 K2 T1 T2 jm15 jm16) => (wfKind_kpi (domainEnv G) (TyEq_wf_1 G T1 T2 (star) jm15) (KindEq_wf_1 (evar G T1) K1 K2 jm16))
    | (QK_Refl K jm17) => (WfKind_wf_0 G K jm17)
    | (QK_Sym K1 K2 jm18) => (KindEq_wf_0 G K1 K2 jm18)
    | (QK_Trans K1 K2 K3 jm19 jm20) => (KindEq_wf_1 G K2 K3 jm20)
  end
with TyEq_wf_0 (G : Env) (T87 : Ty) (T88 : Ty) (K60 : Kind) (jm50 : (TyEq G T87 T88 K60)) {struct jm50} :
(wfTy (domainEnv G) T87) :=
  match jm50 in (TyEq _ T87 T88 K60) return (wfTy (domainEnv G) T87) with
    | (QT_Pi S1 S2 T1 T2 jm21 jm22) => (wfTy_tpi (domainEnv G) (TyEq_wf_0 G S1 T1 (star) jm21) (TyEq_wf_0 (evar G T1) S2 T2 (star) jm22))
    | (QT_App K S1 S2 T t1 t2 jm23 jm24) => (wfTy_tapp (domainEnv G) (TyEq_wf_0 G S1 S2 (kpi T K) jm23) (TermEq_wf_0 G t1 t2 T jm24))
    | (QT_All T t jm25 jm26) => (wfTy_tapp (domainEnv G) (wfTy_prf (domainEnv G)) (wfTm_all (domainEnv G) (Kinding_wf_0 G T (star) jm25) (Typing_wf_0 (evar G T) t (prop) jm26)))
    | (QT_Refl K T jm27) => (Kinding_wf_0 G T K jm27)
    | (QT_Symm K S1 T jm28) => (TyEq_wf_1 G T S1 K jm28)
    | (QT_Trans K S1 T U jm29 jm30) => (TyEq_wf_0 G S1 U K jm29)
  end
with TyEq_wf_1 (G : Env) (T87 : Ty) (T88 : Ty) (K60 : Kind) (jm51 : (TyEq G T87 T88 K60)) {struct jm51} :
(wfTy (domainEnv G) T88) :=
  match jm51 in (TyEq _ T87 T88 K60) return (wfTy (domainEnv G) T88) with
    | (QT_Pi S1 S2 T1 T2 jm21 jm22) => (wfTy_tpi (domainEnv G) (TyEq_wf_1 G S1 T1 (star) jm21) (TyEq_wf_1 (evar G T1) S2 T2 (star) jm22))
    | (QT_App K S1 S2 T t1 t2 jm23 jm24) => (wfTy_tapp (domainEnv G) (TyEq_wf_1 G S1 S2 (kpi T K) jm23) (TermEq_wf_1 G t1 t2 T jm24))
    | (QT_All T t jm25 jm26) => (wfTy_tpi (domainEnv G) (Kinding_wf_0 G T (star) jm25) (wfTy_tapp (HS TmVar (domainEnv G)) (wfTy_prf (HS TmVar (domainEnv G))) (Typing_wf_0 (evar G T) t (prop) jm26)))
    | (QT_Refl K T jm27) => (Kinding_wf_0 G T K jm27)
    | (QT_Symm K S1 T jm28) => (TyEq_wf_0 G T S1 K jm28)
    | (QT_Trans K S1 T U jm29 jm30) => (TyEq_wf_1 G U T K jm30)
  end
with TyEq_wf_2 (G : Env) (T87 : Ty) (T88 : Ty) (K60 : Kind) (jm52 : (TyEq G T87 T88 K60)) {struct jm52} :
(wfKind (domainEnv G) K60) :=
  match jm52 in (TyEq _ T87 T88 K60) return (wfKind (domainEnv G) K60) with
    | (QT_Pi S1 S2 T1 T2 jm21 jm22) => (wfKind_star (domainEnv G))
    | (QT_App K S1 S2 T t1 t2 jm23 jm24) => (substhvl_TmVar_wfKind (TermEq_wf_0 G t1 t2 T jm24) (HS TmVar (domainEnv G)) K (inversion_wfKind_kpi_2 (domainEnv G) T K (TyEq_wf_2 G S1 S2 (kpi T K) jm23)) (substhvl_TmVar_here (domainEnv G)))
    | (QT_All T t jm25 jm26) => (wfKind_star (domainEnv G))
    | (QT_Refl K T jm27) => (Kinding_wf_1 G T K jm27)
    | (QT_Symm K S1 T jm28) => (TyEq_wf_2 G T S1 K jm28)
    | (QT_Trans K S1 T U jm29 jm30) => (TyEq_wf_2 G U T K jm30)
  end
with TermEq_wf_0 (G : Env) (t54 : Tm) (t55 : Tm) (T89 : Ty) (jm53 : (TermEq G t54 t55 T89)) {struct jm53} :
(wfTm (domainEnv G) t54) :=
  match jm53 in (TermEq _ t54 t55 T89) return (wfTm (domainEnv G) t54) with
    | (Q_Abs S1 S2 T t1 t2 jm31 jm32) => (wfTm_abs (domainEnv G) (TyEq_wf_0 G S1 S2 (star) jm31) (TermEq_wf_0 (evar G S1) t1 t2 T jm32))
    | (Q_App S1 T s1 s2 t1 t2 jm33 jm34) => (wfTm_app (domainEnv G) (TermEq_wf_0 G t1 s1 (tpi S1 T) jm33) (TermEq_wf_0 G t2 s2 S1 jm34))
    | (Q_Beta S1 T s t jm35 jm36) => (wfTm_app (domainEnv G) (wfTm_abs (domainEnv G) (Typing_wf_1 G s S1 jm36) (Typing_wf_0 (evar G S1) t T jm35)) (Typing_wf_0 G s S1 jm36))
    | (Q_Eta S1 T t jm37) => (wfTm_abs (domainEnv G) (inversion_wfTy_tpi_1 (domainEnv G) S1 T (Typing_wf_1 G t (tpi S1 T) jm37)) (wfTm_app (HS TmVar (domainEnv G)) (weaken_wfTm (HS TmVar H0) (domainEnv G) t (Typing_wf_0 G t (tpi S1 T) jm37)) (wfTm_var (HS TmVar (domainEnv G)) I0 I)))
    | (Q_Refl T t jm38) => (Typing_wf_0 G t T jm38)
    | (Q_Symm T s t jm39) => (TermEq_wf_1 G t s T jm39)
    | (Q_Trans T s t u jm40 jm41) => (TermEq_wf_0 G s u T jm40)
  end
with TermEq_wf_1 (G : Env) (t54 : Tm) (t55 : Tm) (T89 : Ty) (jm54 : (TermEq G t54 t55 T89)) {struct jm54} :
(wfTm (domainEnv G) t55) :=
  match jm54 in (TermEq _ t54 t55 T89) return (wfTm (domainEnv G) t55) with
    | (Q_Abs S1 S2 T t1 t2 jm31 jm32) => (wfTm_abs (domainEnv G) (TyEq_wf_1 G S1 S2 (star) jm31) (TermEq_wf_1 (evar G S1) t1 t2 T jm32))
    | (Q_App S1 T s1 s2 t1 t2 jm33 jm34) => (wfTm_app (domainEnv G) (TermEq_wf_1 G t1 s1 (tpi S1 T) jm33) (TermEq_wf_1 G t2 s2 S1 jm34))
    | (Q_Beta S1 T s t jm35 jm36) => (substhvl_TmVar_wfTm (Typing_wf_0 G s S1 jm36) (HS TmVar (domainEnv G)) t (Typing_wf_0 (evar G S1) t T jm35) (substhvl_TmVar_here (domainEnv G)))
    | (Q_Eta S1 T t jm37) => (Typing_wf_0 G t (tpi S1 T) jm37)
    | (Q_Refl T t jm38) => (Typing_wf_0 G t T jm38)
    | (Q_Symm T s t jm39) => (TermEq_wf_0 G t s T jm39)
    | (Q_Trans T s t u jm40 jm41) => (TermEq_wf_1 G u t T jm41)
  end
with TermEq_wf_2 (G : Env) (t54 : Tm) (t55 : Tm) (T89 : Ty) (jm55 : (TermEq G t54 t55 T89)) {struct jm55} :
(wfTy (domainEnv G) T89) :=
  match jm55 in (TermEq _ t54 t55 T89) return (wfTy (domainEnv G) T89) with
    | (Q_Abs S1 S2 T t1 t2 jm31 jm32) => (wfTy_tpi (domainEnv G) (TyEq_wf_0 G S1 S2 (star) jm31) (TermEq_wf_2 (evar G S1) t1 t2 T jm32))
    | (Q_App S1 T s1 s2 t1 t2 jm33 jm34) => (substhvl_TmVar_wfTy (TermEq_wf_0 G t2 s2 S1 jm34) (HS TmVar (domainEnv G)) T (inversion_wfTy_tpi_2 (domainEnv G) S1 T (TermEq_wf_2 G t1 s1 (tpi S1 T) jm33)) (substhvl_TmVar_here (domainEnv G)))
    | (Q_Beta S1 T s t jm35 jm36) => (substhvl_TmVar_wfTy (Typing_wf_0 G s S1 jm36) (HS TmVar (domainEnv G)) T (Typing_wf_1 (evar G S1) t T jm35) (substhvl_TmVar_here (domainEnv G)))
    | (Q_Eta S1 T t jm37) => (wfTy_tpi (domainEnv G) (inversion_wfTy_tpi_1 (domainEnv G) S1 T (Typing_wf_1 G t (tpi S1 T) jm37)) (inversion_wfTy_tpi_2 (domainEnv G) S1 T (Typing_wf_1 G t (tpi S1 T) jm37)))
    | (Q_Refl T t jm38) => (Typing_wf_1 G t T jm38)
    | (Q_Symm T s t jm39) => (TermEq_wf_2 G t s T jm39)
    | (Q_Trans T s t u jm40 jm41) => (TermEq_wf_2 G u t T jm41)
  end
with Typing_wf_0 (G : Env) (t56 : Tm) (T90 : Ty) (jm56 : (Typing G t56 T90)) {struct jm56} :
(wfTm (domainEnv G) t56) :=
  match jm56 in (Typing _ t56 T90) return (wfTm (domainEnv G) t56) with
    | (T_Var T x lk1 H19 H20) => (wfTm_var (domainEnv G) _ H20)
    | (T_Abs S1 T t jm7 jm8) => (wfTm_abs (domainEnv G) (Kinding_wf_0 G S1 (star) jm7) (Typing_wf_0 (evar G S1) t T jm8))
    | (T_App S1 T t1 t2 jm9 jm10) => (wfTm_app (domainEnv G) (Typing_wf_0 G t1 (tpi S1 T) jm9) (Typing_wf_0 G t2 S1 jm10))
    | (T_All T t jm11 jm12) => (wfTm_all (domainEnv G) (Kinding_wf_0 G T (star) jm11) (Typing_wf_0 (evar G T) t (prop) jm12))
    | (T_Conv T1 T2 t jm13 jm14) => (Typing_wf_0 G t T1 jm13)
  end
with Typing_wf_1 (G : Env) (t56 : Tm) (T90 : Ty) (jm57 : (Typing G t56 T90)) {struct jm57} :
(wfTy (domainEnv G) T90) :=
  match jm57 in (Typing _ t56 T90) return (wfTy (domainEnv G) T90) with
    | (T_Var T x lk2 H19 H20) => H19
    | (T_Abs S1 T t jm7 jm8) => (wfTy_tpi (domainEnv G) (Kinding_wf_0 G S1 (star) jm7) (Typing_wf_1 (evar G S1) t T jm8))
    | (T_App S1 T t1 t2 jm9 jm10) => (substhvl_TmVar_wfTy (Typing_wf_0 G t2 S1 jm10) (HS TmVar (domainEnv G)) T (inversion_wfTy_tpi_2 (domainEnv G) S1 T (Typing_wf_1 G t1 (tpi S1 T) jm9)) (substhvl_TmVar_here (domainEnv G)))
    | (T_All T t jm11 jm12) => (wfTy_prop (domainEnv G))
    | (T_Conv T1 T2 t jm13 jm14) => (TyEq_wf_1 G T1 T2 (star) jm14)
  end
with Kinding_wf_0 (G : Env) (T91 : Ty) (K61 : Kind) (jm58 : (Kinding G T91 K61)) {struct jm58} :
(wfTy (domainEnv G) T91) :=
  match jm58 in (Kinding _ T91 K61) return (wfTy (domainEnv G) T91) with
    | (K_TVar K X lk3 H19 H20) => (wfTy_tvar (domainEnv G) _ H20)
    | (K_Pi T1 T2 jm1 jm2) => (wfTy_tpi (domainEnv G) (Kinding_wf_0 G T1 (star) jm1) (Kinding_wf_0 (evar G T1) T2 (star) jm2))
    | (K_App K S1 T t jm3 jm4) => (wfTy_tapp (domainEnv G) (Kinding_wf_0 G S1 (kpi T K) jm3) (Typing_wf_0 G t T jm4))
    | (K_Prop) => (wfTy_prop (domainEnv G))
    | (K_Prf) => (wfTy_prf (domainEnv G))
    | (K_Conv K1 K2 T jm5 jm6) => (Kinding_wf_0 G T K1 jm5)
  end
with Kinding_wf_1 (G : Env) (T91 : Ty) (K61 : Kind) (jm59 : (Kinding G T91 K61)) {struct jm59} :
(wfKind (domainEnv G) K61) :=
  match jm59 in (Kinding _ T91 K61) return (wfKind (domainEnv G) K61) with
    | (K_TVar K X lk4 H19 H20) => H19
    | (K_Pi T1 T2 jm1 jm2) => (wfKind_star (domainEnv G))
    | (K_App K S1 T t jm3 jm4) => (substhvl_TmVar_wfKind (Typing_wf_0 G t T jm4) (HS TmVar (domainEnv G)) K (inversion_wfKind_kpi_2 (domainEnv G) T K (Kinding_wf_1 G S1 (kpi T K) jm3)) (substhvl_TmVar_here (domainEnv G)))
    | (K_Prop) => (wfKind_star (domainEnv G))
    | (K_Prf) => (wfKind_kpi (domainEnv G) (wfTy_prop (domainEnv G)) (wfKind_star (HS TmVar (domainEnv G))))
    | (K_Conv K1 K2 T jm5 jm6) => (KindEq_wf_1 G K1 K2 jm6)
  end
with WfKind_wf_0 (G : Env) (K62 : Kind) (jm60 : (WfKind G K62)) {struct jm60} :
(wfKind (domainEnv G) K62) :=
  match jm60 in (WfKind _ K62) return (wfKind (domainEnv G) K62) with
    | (WfStar) => (wfKind_star (domainEnv G))
    | (WfPi K T jm jm0) => (wfKind_kpi (domainEnv G) (Kinding_wf_0 G T (star) jm) (weaken_wfKind (HS TmVar H0) (domainEnv G) K (WfKind_wf_0 G K jm0)))
  end.
 Hint Extern 8 => match goal with
  | H72 : (KindEq _ _ _) |- _ => pose proof ((KindEq_wf_0 _ _ _ H72)); pose proof ((KindEq_wf_1 _ _ _ H72)); clear H72
end : wf.
 Hint Extern 8 => match goal with
  | H73 : (TyEq _ _ _ _) |- _ => pose proof ((TyEq_wf_0 _ _ _ _ H73)); pose proof ((TyEq_wf_1 _ _ _ _ H73)); pose proof ((TyEq_wf_2 _ _ _ _ H73)); clear H73
end : wf.
 Hint Extern 8 => match goal with
  | H74 : (TermEq _ _ _ _) |- _ => pose proof ((TermEq_wf_0 _ _ _ _ H74)); pose proof ((TermEq_wf_1 _ _ _ _ H74)); pose proof ((TermEq_wf_2 _ _ _ _ H74)); clear H74
end : wf.
 Hint Extern 8 => match goal with
  | H75 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H75)); pose proof ((Typing_wf_1 _ _ _ H75)); clear H75
end : wf.
 Hint Extern 8 => match goal with
  | H76 : (Kinding _ _ _) |- _ => pose proof ((Kinding_wf_0 _ _ _ H76)); pose proof ((Kinding_wf_1 _ _ _ H76)); clear H76
end : wf.
 Hint Extern 8 => match goal with
  | H77 : (WfKind _ _) |- _ => pose proof ((WfKind_wf_0 _ _ H77)); clear H77
end : wf.
Lemma subst_evar_lookup_evar (G11 : Env) (s15 : Tm) (T92 : Ty) (jm61 : (Typing G11 s15 T92)) :
  (forall (d : (Trace TmVar)) (G12 : Env) (G14 : Env) (sub : (subst_evar G11 T92 s15 d G12 G14)) (x57 : (Index TmVar)) (T93 : Ty) ,
    (lookup_evar G12 x57 T93) -> (Typing G14 (substIndex d s15 x57) (substTy d s15 T93))).
Proof.
  needleGenericSubstEnvLookupHom (T_Var).
Qed.
Lemma subst_etvar_lookup_etvar (G11 : Env) (S39 : Ty) (K63 : Kind) (jm61 : (Kinding G11 S39 K63)) :
  (forall (d : (Trace TyVar)) (G12 : Env) (G14 : Env) (sub : (subst_etvar G11 K63 S39 d G12 G14)) (X11 : (Index TyVar)) (K64 : Kind) ,
    (lookup_etvar G12 X11 K64) -> (Kinding G14 (tsubstIndex d S39 X11) (tsubstKind d S39 K64))).
Proof.
  needleGenericSubstEnvLookupHom (K_TVar).
Qed.
Fixpoint subst_evar_KindEq (G12 : Env) (s15 : Tm) (T92 : Ty) (jm67 : (Typing G12 s15 T92)) (G11 : Env) (K1 : Kind) (K2 : Kind) (jm68 : (KindEq G11 K1 K2)) :
(forall (G13 : Env) (d : (Trace TmVar)) (H89 : (subst_evar G12 T92 s15 d G11 G13)) ,
  (KindEq G13 (substKind d s15 K1) (substKind d s15 K2))) :=
  match jm68 in (KindEq _ K1 K2) return (forall (G13 : Env) (d : (Trace TmVar)) (H89 : (subst_evar G12 T92 s15 d G11 G13)) ,
    (KindEq G13 (substKind d s15 K1) (substKind d s15 K2))) with
    | (QK_Pi K64 K65 T93 T94 jm61 jm62) => (fun (G13 : Env) (d : (Trace TmVar)) (H89 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (QK_Pi G13 (substKind (weakenTrace d (HS TmVar H0)) s15 K64) (substKind (weakenTrace d (HS TmVar H0)) s15 K65) (substTy (weakenTrace d H0) s15 T93) (substTy (weakenTrace d H0) s15 T94) (subst_evar_TyEq G12 s15 T92 jm67 G11 T93 T94 (star) jm61 G13 d (weaken_subst_evar _ empty H89)) (subst_evar_KindEq G12 s15 T92 jm67 (evar G11 T93) K64 K65 jm62 (appendEnv G13 (substEnv d s15 (evar empty T93))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty T93) H89))))
    | (QK_Refl K63 jm63) => (fun (G13 : Env) (d : (Trace TmVar)) (H89 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (QK_Refl G13 (substKind (weakenTrace d H0) s15 K63) (subst_evar_WfKind G12 s15 T92 jm67 G11 K63 jm63 G13 d (weaken_subst_evar _ empty H89))))
    | (QK_Sym K64 K65 jm64) => (fun (G13 : Env) (d : (Trace TmVar)) (H89 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (QK_Sym G13 (substKind (weakenTrace d H0) s15 K64) (substKind (weakenTrace d H0) s15 K65) (subst_evar_KindEq G12 s15 T92 jm67 G11 K64 K65 jm64 G13 d (weaken_subst_evar _ empty H89))))
    | (QK_Trans K64 K65 K66 jm65 jm66) => (fun (G13 : Env) (d : (Trace TmVar)) (H89 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (QK_Trans G13 (substKind (weakenTrace d H0) s15 K64) (substKind (weakenTrace d H0) s15 K65) (substKind (weakenTrace d H0) s15 K66) (subst_evar_KindEq G12 s15 T92 jm67 G11 K64 K65 jm65 G13 d (weaken_subst_evar _ empty H89)) (subst_evar_KindEq G12 s15 T92 jm67 G11 K65 K66 jm66 G13 d (weaken_subst_evar _ empty H89))))
  end
with subst_evar_TyEq (G12 : Env) (s15 : Tm) (T92 : Ty) (jm71 : (Typing G12 s15 T92)) (G11 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm72 : (TyEq G11 T1 T2 K)) :
(forall (G13 : Env) (d : (Trace TmVar)) (H100 : (subst_evar G12 T92 s15 d G11 G13)) ,
  (TyEq G13 (substTy d s15 T1) (substTy d s15 T2) (substKind d s15 K))) :=
  match jm72 in (TyEq _ T1 T2 K) return (forall (G13 : Env) (d : (Trace TmVar)) (H100 : (subst_evar G12 T92 s15 d G11 G13)) ,
    (TyEq G13 (substTy d s15 T1) (substTy d s15 T2) (substKind d s15 K))) with
    | (QT_Pi S39 S40 T94 T95 jm61 jm62) => (fun (G13 : Env) (d : (Trace TmVar)) (H100 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (QT_Pi G13 (substTy (weakenTrace d H0) s15 S39) (substTy (weakenTrace d (HS TmVar H0)) s15 S40) (substTy (weakenTrace d H0) s15 T94) (substTy (weakenTrace d (HS TmVar H0)) s15 T95) (subst_evar_TyEq G12 s15 T92 jm71 G11 S39 T94 (star) jm61 G13 d (weaken_subst_evar _ empty H100)) (subst_evar_TyEq G12 s15 T92 jm71 (evar G11 T94) S40 T95 (star) jm62 (appendEnv G13 (substEnv d s15 (evar empty T94))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty T94) H100))))
    | (QT_App K63 S39 S40 T93 t58 t59 jm63 jm64) => (fun (G13 : Env) (d : (Trace TmVar)) (H100 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (TyEq_cast G13 _ _ _ G13 (substTy d s15 (tapp S39 t58)) (substTy d s15 (tapp S40 t59)) (substKind d s15 (substKind X0 t58 K63)) eq_refl eq_refl eq_refl (eq_sym (substKind_substKind0_comm K63 d s15 t58)) (QT_App G13 (substKind (weakenTrace d (HS TmVar H0)) s15 K63) (substTy (weakenTrace d H0) s15 S39) (substTy (weakenTrace d H0) s15 S40) (substTy (weakenTrace d H0) s15 T93) (substTm (weakenTrace d H0) s15 t58) (substTm (weakenTrace d H0) s15 t59) (subst_evar_TyEq G12 s15 T92 jm71 G11 S39 S40 (kpi T93 K63) jm63 G13 d (weaken_subst_evar _ empty H100)) (subst_evar_TermEq G12 s15 T92 jm71 G11 t58 t59 T93 jm64 G13 d (weaken_subst_evar _ empty H100)))))
    | (QT_All T93 t57 jm65 jm66) => (fun (G13 : Env) (d : (Trace TmVar)) (H100 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (QT_All G13 (substTy (weakenTrace d H0) s15 T93) (substTm (weakenTrace d (HS TmVar H0)) s15 t57) (subst_evar_Kinding G12 s15 T92 jm71 G11 T93 (star) jm65 G13 d (weaken_subst_evar _ empty H100)) (subst_evar_Typing G12 s15 T92 jm71 (evar G11 T93) t57 (prop) jm66 (appendEnv G13 (substEnv d s15 (evar empty T93))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty T93) H100))))
    | (QT_Refl K63 T93 jm67) => (fun (G13 : Env) (d : (Trace TmVar)) (H100 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (QT_Refl G13 (substKind (weakenTrace d H0) s15 K63) (substTy (weakenTrace d H0) s15 T93) (subst_evar_Kinding G12 s15 T92 jm71 G11 T93 K63 jm67 G13 d (weaken_subst_evar _ empty H100))))
    | (QT_Symm K63 S39 T93 jm68) => (fun (G13 : Env) (d : (Trace TmVar)) (H100 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (QT_Symm G13 (substKind (weakenTrace d H0) s15 K63) (substTy (weakenTrace d H0) s15 S39) (substTy (weakenTrace d H0) s15 T93) (subst_evar_TyEq G12 s15 T92 jm71 G11 T93 S39 K63 jm68 G13 d (weaken_subst_evar _ empty H100))))
    | (QT_Trans K63 S39 T93 U1 jm69 jm70) => (fun (G13 : Env) (d : (Trace TmVar)) (H100 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (QT_Trans G13 (substKind (weakenTrace d H0) s15 K63) (substTy (weakenTrace d H0) s15 S39) (substTy (weakenTrace d H0) s15 T93) (substTy (weakenTrace d H0) s15 U1) (subst_evar_TyEq G12 s15 T92 jm71 G11 S39 U1 K63 jm69 G13 d (weaken_subst_evar _ empty H100)) (subst_evar_TyEq G12 s15 T92 jm71 G11 U1 T93 K63 jm70 G13 d (weaken_subst_evar _ empty H100))))
  end
with subst_evar_TermEq (G12 : Env) (s18 : Tm) (T92 : Ty) (jm72 : (Typing G12 s18 T92)) (G11 : Env) (t1 : Tm) (t2 : Tm) (T : Ty) (jm73 : (TermEq G11 t1 t2 T)) :
(forall (G13 : Env) (d : (Trace TmVar)) (H106 : (subst_evar G12 T92 s18 d G11 G13)) ,
  (TermEq G13 (substTm d s18 t1) (substTm d s18 t2) (substTy d s18 T))) :=
  match jm73 in (TermEq _ t1 t2 T) return (forall (G13 : Env) (d : (Trace TmVar)) (H106 : (subst_evar G12 T92 s18 d G11 G13)) ,
    (TermEq G13 (substTm d s18 t1) (substTm d s18 t2) (substTy d s18 T))) with
    | (Q_Abs S39 S40 T93 t58 t59 jm61 jm62) => (fun (G13 : Env) (d : (Trace TmVar)) (H106 : (subst_evar G12 T92 s18 d G11 G13)) =>
      (Q_Abs G13 (substTy (weakenTrace d H0) s18 S39) (substTy (weakenTrace d H0) s18 S40) (substTy (weakenTrace d (HS TmVar H0)) s18 T93) (substTm (weakenTrace d (HS TmVar H0)) s18 t58) (substTm (weakenTrace d (HS TmVar H0)) s18 t59) (subst_evar_TyEq G12 s18 T92 jm72 G11 S39 S40 (star) jm61 G13 d (weaken_subst_evar _ empty H106)) (subst_evar_TermEq G12 s18 T92 jm72 (evar G11 S39) t58 t59 T93 jm62 (appendEnv G13 (substEnv d s18 (evar empty S39))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty S39) H106))))
    | (Q_App S39 T93 s16 s17 t58 t59 jm63 jm64) => (fun (G13 : Env) (d : (Trace TmVar)) (H106 : (subst_evar G12 T92 s18 d G11 G13)) =>
      (TermEq_cast G13 _ _ _ G13 (substTm d s18 (app t58 t59)) (substTm d s18 (app s16 s17)) (substTy d s18 (substTy X0 t59 T93)) eq_refl eq_refl eq_refl (eq_sym (substTy_substTy0_comm T93 d s18 t59)) (Q_App G13 (substTy (weakenTrace d H0) s18 S39) (substTy (weakenTrace d (HS TmVar H0)) s18 T93) (substTm (weakenTrace d H0) s18 s16) (substTm (weakenTrace d H0) s18 s17) (substTm (weakenTrace d H0) s18 t58) (substTm (weakenTrace d H0) s18 t59) (subst_evar_TermEq G12 s18 T92 jm72 G11 t58 s16 (tpi S39 T93) jm63 G13 d (weaken_subst_evar _ empty H106)) (subst_evar_TermEq G12 s18 T92 jm72 G11 t59 s17 S39 jm64 G13 d (weaken_subst_evar _ empty H106)))))
    | (Q_Beta S39 T93 s15 t57 jm65 jm66) => (fun (G13 : Env) (d : (Trace TmVar)) (H106 : (subst_evar G12 T92 s18 d G11 G13)) =>
      (TermEq_cast G13 _ _ _ G13 (substTm d s18 (app (abs S39 t57) s15)) (substTm d s18 (substTm X0 s15 t57)) (substTy d s18 (substTy X0 s15 T93)) eq_refl eq_refl (eq_sym (substTm_substTm0_comm t57 d s18 s15)) (eq_sym (substTy_substTy0_comm T93 d s18 s15)) (Q_Beta G13 (substTy (weakenTrace d H0) s18 S39) (substTy (weakenTrace d (HS TmVar H0)) s18 T93) (substTm (weakenTrace d H0) s18 s15) (substTm (weakenTrace d (HS TmVar H0)) s18 t57) (subst_evar_Typing G12 s18 T92 jm72 (evar G11 S39) t57 T93 jm65 (appendEnv G13 (substEnv d s18 (evar empty S39))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty S39) H106)) (subst_evar_Typing G12 s18 T92 jm72 G11 s15 S39 jm66 G13 d (weaken_subst_evar _ empty H106)))))
    | (Q_Eta S39 T93 t57 jm67) => (fun (G13 : Env) (d : (Trace TmVar)) (H106 : (subst_evar G12 T92 s18 d G11 G13)) =>
      (TermEq_cast G13 _ _ _ G13 (substTm d s18 (abs S39 (app (weakenTm t57 (HS TmVar H0)) (var I0)))) (substTm d s18 t57) (substTy d s18 (tpi S39 T93)) eq_refl (f_equal2 abs eq_refl (f_equal2 app (weakenTm_substTm (HS TmVar H0) d s18 t57) eq_refl)) eq_refl eq_refl (Q_Eta G13 (substTy (weakenTrace d H0) s18 S39) (substTy (weakenTrace d (HS TmVar H0)) s18 T93) (substTm (weakenTrace d H0) s18 t57) (subst_evar_Typing G12 s18 T92 jm72 G11 t57 (tpi S39 T93) jm67 G13 d (weaken_subst_evar _ empty H106)))))
    | (Q_Refl T93 t57 jm68) => (fun (G13 : Env) (d : (Trace TmVar)) (H106 : (subst_evar G12 T92 s18 d G11 G13)) =>
      (Q_Refl G13 (substTy (weakenTrace d H0) s18 T93) (substTm (weakenTrace d H0) s18 t57) (subst_evar_Typing G12 s18 T92 jm72 G11 t57 T93 jm68 G13 d (weaken_subst_evar _ empty H106))))
    | (Q_Symm T93 s15 t57 jm69) => (fun (G13 : Env) (d : (Trace TmVar)) (H106 : (subst_evar G12 T92 s18 d G11 G13)) =>
      (Q_Symm G13 (substTy (weakenTrace d H0) s18 T93) (substTm (weakenTrace d H0) s18 s15) (substTm (weakenTrace d H0) s18 t57) (subst_evar_TermEq G12 s18 T92 jm72 G11 t57 s15 T93 jm69 G13 d (weaken_subst_evar _ empty H106))))
    | (Q_Trans T93 s15 t57 u1 jm70 jm71) => (fun (G13 : Env) (d : (Trace TmVar)) (H106 : (subst_evar G12 T92 s18 d G11 G13)) =>
      (Q_Trans G13 (substTy (weakenTrace d H0) s18 T93) (substTm (weakenTrace d H0) s18 s15) (substTm (weakenTrace d H0) s18 t57) (substTm (weakenTrace d H0) s18 u1) (subst_evar_TermEq G12 s18 T92 jm72 G11 s15 u1 T93 jm70 G13 d (weaken_subst_evar _ empty H106)) (subst_evar_TermEq G12 s18 T92 jm72 G11 u1 t57 T93 jm71 G13 d (weaken_subst_evar _ empty H106))))
  end
with subst_evar_Typing (G12 : Env) (s15 : Tm) (T92 : Ty) (jm69 : (Typing G12 s15 T92)) (G11 : Env) (t : Tm) (T : Ty) (jm70 : (Typing G11 t T)) :
(forall (G13 : Env) (d : (Trace TmVar)) (H93 : (subst_evar G12 T92 s15 d G11 G13)) ,
  (Typing G13 (substTm d s15 t) (substTy d s15 T))) :=
  match jm70 in (Typing _ t T) return (forall (G13 : Env) (d : (Trace TmVar)) (H93 : (subst_evar G12 T92 s15 d G11 G13)) ,
    (Typing G13 (substTm d s15 t) (substTy d s15 T))) with
    | (T_Var T93 x57 lk5 H79 H80) => (fun (G13 : Env) (d : (Trace TmVar)) (H93 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (subst_evar_lookup_evar G12 s15 T92 jm69 d G11 G13 H93 x57 T93 lk5))
    | (T_Abs S39 T93 t57 jm66 jm67) => (fun (G13 : Env) (d : (Trace TmVar)) (H93 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (T_Abs G13 (substTy (weakenTrace d H0) s15 S39) (substTy (weakenTrace d (HS TmVar H0)) s15 T93) (substTm (weakenTrace d (HS TmVar H0)) s15 t57) (subst_evar_Kinding G12 s15 T92 jm69 G11 S39 (star) jm66 G13 d (weaken_subst_evar _ empty H93)) (subst_evar_Typing G12 s15 T92 jm69 (evar G11 S39) t57 T93 jm67 (appendEnv G13 (substEnv d s15 (evar empty S39))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty S39) H93))))
    | (T_App S39 T93 t58 t59 jm68 jm61) => (fun (G13 : Env) (d : (Trace TmVar)) (H93 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (Typing_cast G13 _ _ G13 (substTm d s15 (app t58 t59)) (substTy d s15 (substTy X0 t59 T93)) eq_refl eq_refl (eq_sym (substTy_substTy0_comm T93 d s15 t59)) (T_App G13 (substTy (weakenTrace d H0) s15 S39) (substTy (weakenTrace d (HS TmVar H0)) s15 T93) (substTm (weakenTrace d H0) s15 t58) (substTm (weakenTrace d H0) s15 t59) (subst_evar_Typing G12 s15 T92 jm69 G11 t58 (tpi S39 T93) jm68 G13 d (weaken_subst_evar _ empty H93)) (subst_evar_Typing G12 s15 T92 jm69 G11 t59 S39 jm61 G13 d (weaken_subst_evar _ empty H93)))))
    | (T_All T93 t57 jm62 jm63) => (fun (G13 : Env) (d : (Trace TmVar)) (H93 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (T_All G13 (substTy (weakenTrace d H0) s15 T93) (substTm (weakenTrace d (HS TmVar H0)) s15 t57) (subst_evar_Kinding G12 s15 T92 jm69 G11 T93 (star) jm62 G13 d (weaken_subst_evar _ empty H93)) (subst_evar_Typing G12 s15 T92 jm69 (evar G11 T93) t57 (prop) jm63 (appendEnv G13 (substEnv d s15 (evar empty T93))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty T93) H93))))
    | (T_Conv T94 T95 t57 jm64 jm65) => (fun (G13 : Env) (d : (Trace TmVar)) (H93 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (T_Conv G13 (substTy (weakenTrace d H0) s15 T94) (substTy (weakenTrace d H0) s15 T95) (substTm (weakenTrace d H0) s15 t57) (subst_evar_Typing G12 s15 T92 jm69 G11 t57 T94 jm64 G13 d (weaken_subst_evar _ empty H93)) (subst_evar_TyEq G12 s15 T92 jm69 G11 T94 T95 (star) jm65 G13 d (weaken_subst_evar _ empty H93))))
  end
with subst_evar_Kinding (G12 : Env) (s15 : Tm) (T92 : Ty) (jm67 : (Typing G12 s15 T92)) (G11 : Env) (T : Ty) (K : Kind) (jm68 : (Kinding G11 T K)) :
(forall (G13 : Env) (d : (Trace TmVar)) (H90 : (subst_evar G12 T92 s15 d G11 G13)) ,
  (Kinding G13 (substTy d s15 T) (substKind d s15 K))) :=
  match jm68 in (Kinding _ T K) return (forall (G13 : Env) (d : (Trace TmVar)) (H90 : (subst_evar G12 T92 s15 d G11 G13)) ,
    (Kinding G13 (substTy d s15 T) (substKind d s15 K))) with
    | (K_TVar K63 X11 lk5 H79 H80) => (fun (G13 : Env) (d : (Trace TmVar)) (H90 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (K_TVar G13 (substKind (weakenTrace d H0) s15 K63) X11 (subst_evar_lookup_etvar T92 (Typing_wf_0 G12 s15 T92 jm67) H90 K63 lk5) (substhvl_TmVar_wfKind (Typing_wf_0 G12 s15 T92 jm67) _ _ H79 (weaken_substhvl_TmVar H0 (subst_evar_substhvl_TmVar _ H90))) (substhvl_TmVar_wfindex_TyVar (weaken_substhvl_TmVar H0 (subst_evar_substhvl_TmVar _ H90)) H80)))
    | (K_Pi T94 T95 jm61 jm62) => (fun (G13 : Env) (d : (Trace TmVar)) (H90 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (K_Pi G13 (substTy (weakenTrace d H0) s15 T94) (substTy (weakenTrace d (HS TmVar H0)) s15 T95) (subst_evar_Kinding G12 s15 T92 jm67 G11 T94 (star) jm61 G13 d (weaken_subst_evar _ empty H90)) (subst_evar_Kinding G12 s15 T92 jm67 (evar G11 T94) T95 (star) jm62 (appendEnv G13 (substEnv d s15 (evar empty T94))) (weakenTrace d (HS TmVar H0)) (weaken_subst_evar _ (evar empty T94) H90))))
    | (K_App K63 S39 T93 t57 jm63 jm64) => (fun (G13 : Env) (d : (Trace TmVar)) (H90 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (Kinding_cast G13 _ _ G13 (substTy d s15 (tapp S39 t57)) (substKind d s15 (substKind X0 t57 K63)) eq_refl eq_refl (eq_sym (substKind_substKind0_comm K63 d s15 t57)) (K_App G13 (substKind (weakenTrace d (HS TmVar H0)) s15 K63) (substTy (weakenTrace d H0) s15 S39) (substTy (weakenTrace d H0) s15 T93) (substTm (weakenTrace d H0) s15 t57) (subst_evar_Kinding G12 s15 T92 jm67 G11 S39 (kpi T93 K63) jm63 G13 d (weaken_subst_evar _ empty H90)) (subst_evar_Typing G12 s15 T92 jm67 G11 t57 T93 jm64 G13 d (weaken_subst_evar _ empty H90)))))
    | (K_Prop) => (fun (G13 : Env) (d : (Trace TmVar)) (H90 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (K_Prop G13))
    | (K_Prf) => (fun (G13 : Env) (d : (Trace TmVar)) (H90 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (K_Prf G13))
    | (K_Conv K64 K65 T93 jm65 jm66) => (fun (G13 : Env) (d : (Trace TmVar)) (H90 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (K_Conv G13 (substKind (weakenTrace d H0) s15 K64) (substKind (weakenTrace d H0) s15 K65) (substTy (weakenTrace d H0) s15 T93) (subst_evar_Kinding G12 s15 T92 jm67 G11 T93 K64 jm65 G13 d (weaken_subst_evar _ empty H90)) (subst_evar_KindEq G12 s15 T92 jm67 G11 K64 K65 jm66 G13 d (weaken_subst_evar _ empty H90))))
  end
with subst_evar_WfKind (G12 : Env) (s15 : Tm) (T92 : Ty) (jm63 : (Typing G12 s15 T92)) (G11 : Env) (K : Kind) (jm64 : (WfKind G11 K)) :
(forall (G13 : Env) (d : (Trace TmVar)) (H81 : (subst_evar G12 T92 s15 d G11 G13)) ,
  (WfKind G13 (substKind d s15 K))) :=
  match jm64 in (WfKind _ K) return (forall (G13 : Env) (d : (Trace TmVar)) (H81 : (subst_evar G12 T92 s15 d G11 G13)) ,
    (WfKind G13 (substKind d s15 K))) with
    | (WfStar) => (fun (G13 : Env) (d : (Trace TmVar)) (H81 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (WfStar G13))
    | (WfPi K63 T93 jm61 jm62) => (fun (G13 : Env) (d : (Trace TmVar)) (H81 : (subst_evar G12 T92 s15 d G11 G13)) =>
      (WfKind_cast G13 _ G13 (substKind d s15 (kpi T93 (weakenKind K63 (HS TmVar H0)))) eq_refl (f_equal2 kpi eq_refl (weakenKind_substKind (HS TmVar H0) d s15 K63)) (WfPi G13 (substKind (weakenTrace d H0) s15 K63) (substTy (weakenTrace d H0) s15 T93) (subst_evar_Kinding G12 s15 T92 jm63 G11 T93 (star) jm61 G13 d (weaken_subst_evar _ empty H81)) (subst_evar_WfKind G12 s15 T92 jm63 G11 K63 jm62 G13 d (weaken_subst_evar _ empty H81)))))
  end.
Fixpoint subst_etvar_KindEq (G12 : Env) (S39 : Ty) (K63 : Kind) (jm67 : (Kinding G12 S39 K63)) (G11 : Env) (K1 : Kind) (K2 : Kind) (jm68 : (KindEq G11 K1 K2)) :
(forall (G13 : Env) (d : (Trace TyVar)) (H90 : (subst_etvar G12 K63 S39 d G11 G13)) ,
  (KindEq G13 (tsubstKind d S39 K1) (tsubstKind d S39 K2))) :=
  match jm68 in (KindEq _ K1 K2) return (forall (G13 : Env) (d : (Trace TyVar)) (H90 : (subst_etvar G12 K63 S39 d G11 G13)) ,
    (KindEq G13 (tsubstKind d S39 K1) (tsubstKind d S39 K2))) with
    | (QK_Pi K65 K66 T93 T94 jm61 jm62) => (fun (G13 : Env) (d : (Trace TyVar)) (H90 : (subst_etvar G12 K63 S39 d G11 G13)) =>
      (QK_Pi G13 (tsubstKind (weakenTrace d (HS TmVar H0)) S39 K65) (tsubstKind (weakenTrace d (HS TmVar H0)) S39 K66) (tsubstTy (weakenTrace d H0) S39 T93) (tsubstTy (weakenTrace d H0) S39 T94) (subst_etvar_TyEq G12 S39 K63 jm67 G11 T93 T94 (star) jm61 G13 d (weaken_subst_etvar _ empty H90)) (subst_etvar_KindEq G12 S39 K63 jm67 (evar G11 T93) K65 K66 jm62 (appendEnv G13 (tsubstEnv d S39 (evar empty T93))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty T93) H90))))
    | (QK_Refl K64 jm63) => (fun (G13 : Env) (d : (Trace TyVar)) (H90 : (subst_etvar G12 K63 S39 d G11 G13)) =>
      (QK_Refl G13 (tsubstKind (weakenTrace d H0) S39 K64) (subst_etvar_WfKind G12 S39 K63 jm67 G11 K64 jm63 G13 d (weaken_subst_etvar _ empty H90))))
    | (QK_Sym K65 K66 jm64) => (fun (G13 : Env) (d : (Trace TyVar)) (H90 : (subst_etvar G12 K63 S39 d G11 G13)) =>
      (QK_Sym G13 (tsubstKind (weakenTrace d H0) S39 K65) (tsubstKind (weakenTrace d H0) S39 K66) (subst_etvar_KindEq G12 S39 K63 jm67 G11 K65 K66 jm64 G13 d (weaken_subst_etvar _ empty H90))))
    | (QK_Trans K65 K66 K67 jm65 jm66) => (fun (G13 : Env) (d : (Trace TyVar)) (H90 : (subst_etvar G12 K63 S39 d G11 G13)) =>
      (QK_Trans G13 (tsubstKind (weakenTrace d H0) S39 K65) (tsubstKind (weakenTrace d H0) S39 K66) (tsubstKind (weakenTrace d H0) S39 K67) (subst_etvar_KindEq G12 S39 K63 jm67 G11 K65 K66 jm65 G13 d (weaken_subst_etvar _ empty H90)) (subst_etvar_KindEq G12 S39 K63 jm67 G11 K66 K67 jm66 G13 d (weaken_subst_etvar _ empty H90))))
  end
with subst_etvar_TyEq (G12 : Env) (S41 : Ty) (K63 : Kind) (jm71 : (Kinding G12 S41 K63)) (G11 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm72 : (TyEq G11 T1 T2 K)) :
(forall (G13 : Env) (d : (Trace TyVar)) (H101 : (subst_etvar G12 K63 S41 d G11 G13)) ,
  (TyEq G13 (tsubstTy d S41 T1) (tsubstTy d S41 T2) (tsubstKind d S41 K))) :=
  match jm72 in (TyEq _ T1 T2 K) return (forall (G13 : Env) (d : (Trace TyVar)) (H101 : (subst_etvar G12 K63 S41 d G11 G13)) ,
    (TyEq G13 (tsubstTy d S41 T1) (tsubstTy d S41 T2) (tsubstKind d S41 K))) with
    | (QT_Pi S39 S40 T94 T95 jm61 jm62) => (fun (G13 : Env) (d : (Trace TyVar)) (H101 : (subst_etvar G12 K63 S41 d G11 G13)) =>
      (QT_Pi G13 (tsubstTy (weakenTrace d H0) S41 S39) (tsubstTy (weakenTrace d (HS TmVar H0)) S41 S40) (tsubstTy (weakenTrace d H0) S41 T94) (tsubstTy (weakenTrace d (HS TmVar H0)) S41 T95) (subst_etvar_TyEq G12 S41 K63 jm71 G11 S39 T94 (star) jm61 G13 d (weaken_subst_etvar _ empty H101)) (subst_etvar_TyEq G12 S41 K63 jm71 (evar G11 T94) S40 T95 (star) jm62 (appendEnv G13 (tsubstEnv d S41 (evar empty T94))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty T94) H101))))
    | (QT_App K64 S39 S40 T93 t58 t59 jm63 jm64) => (fun (G13 : Env) (d : (Trace TyVar)) (H101 : (subst_etvar G12 K63 S41 d G11 G13)) =>
      (TyEq_cast G13 _ _ _ G13 (tsubstTy d S41 (tapp S39 t58)) (tsubstTy d S41 (tapp S40 t59)) (tsubstKind d S41 (substKind X0 t58 K64)) eq_refl eq_refl eq_refl (eq_sym (tsubstKind_substKind0_comm K64 d S41 t58)) (QT_App G13 (tsubstKind (weakenTrace d (HS TmVar H0)) S41 K64) (tsubstTy (weakenTrace d H0) S41 S39) (tsubstTy (weakenTrace d H0) S41 S40) (tsubstTy (weakenTrace d H0) S41 T93) (tsubstTm (weakenTrace d H0) S41 t58) (tsubstTm (weakenTrace d H0) S41 t59) (subst_etvar_TyEq G12 S41 K63 jm71 G11 S39 S40 (kpi T93 K64) jm63 G13 d (weaken_subst_etvar _ empty H101)) (subst_etvar_TermEq G12 S41 K63 jm71 G11 t58 t59 T93 jm64 G13 d (weaken_subst_etvar _ empty H101)))))
    | (QT_All T93 t57 jm65 jm66) => (fun (G13 : Env) (d : (Trace TyVar)) (H101 : (subst_etvar G12 K63 S41 d G11 G13)) =>
      (QT_All G13 (tsubstTy (weakenTrace d H0) S41 T93) (tsubstTm (weakenTrace d (HS TmVar H0)) S41 t57) (subst_etvar_Kinding G12 S41 K63 jm71 G11 T93 (star) jm65 G13 d (weaken_subst_etvar _ empty H101)) (subst_etvar_Typing G12 S41 K63 jm71 (evar G11 T93) t57 (prop) jm66 (appendEnv G13 (tsubstEnv d S41 (evar empty T93))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty T93) H101))))
    | (QT_Refl K64 T93 jm67) => (fun (G13 : Env) (d : (Trace TyVar)) (H101 : (subst_etvar G12 K63 S41 d G11 G13)) =>
      (QT_Refl G13 (tsubstKind (weakenTrace d H0) S41 K64) (tsubstTy (weakenTrace d H0) S41 T93) (subst_etvar_Kinding G12 S41 K63 jm71 G11 T93 K64 jm67 G13 d (weaken_subst_etvar _ empty H101))))
    | (QT_Symm K64 S39 T93 jm68) => (fun (G13 : Env) (d : (Trace TyVar)) (H101 : (subst_etvar G12 K63 S41 d G11 G13)) =>
      (QT_Symm G13 (tsubstKind (weakenTrace d H0) S41 K64) (tsubstTy (weakenTrace d H0) S41 S39) (tsubstTy (weakenTrace d H0) S41 T93) (subst_etvar_TyEq G12 S41 K63 jm71 G11 T93 S39 K64 jm68 G13 d (weaken_subst_etvar _ empty H101))))
    | (QT_Trans K64 S39 T93 U1 jm69 jm70) => (fun (G13 : Env) (d : (Trace TyVar)) (H101 : (subst_etvar G12 K63 S41 d G11 G13)) =>
      (QT_Trans G13 (tsubstKind (weakenTrace d H0) S41 K64) (tsubstTy (weakenTrace d H0) S41 S39) (tsubstTy (weakenTrace d H0) S41 T93) (tsubstTy (weakenTrace d H0) S41 U1) (subst_etvar_TyEq G12 S41 K63 jm71 G11 S39 U1 K64 jm69 G13 d (weaken_subst_etvar _ empty H101)) (subst_etvar_TyEq G12 S41 K63 jm71 G11 U1 T93 K64 jm70 G13 d (weaken_subst_etvar _ empty H101))))
  end
with subst_etvar_TermEq (G12 : Env) (S41 : Ty) (K63 : Kind) (jm72 : (Kinding G12 S41 K63)) (G11 : Env) (t1 : Tm) (t2 : Tm) (T : Ty) (jm73 : (TermEq G11 t1 t2 T)) :
(forall (G13 : Env) (d : (Trace TyVar)) (H107 : (subst_etvar G12 K63 S41 d G11 G13)) ,
  (TermEq G13 (tsubstTm d S41 t1) (tsubstTm d S41 t2) (tsubstTy d S41 T))) :=
  match jm73 in (TermEq _ t1 t2 T) return (forall (G13 : Env) (d : (Trace TyVar)) (H107 : (subst_etvar G12 K63 S41 d G11 G13)) ,
    (TermEq G13 (tsubstTm d S41 t1) (tsubstTm d S41 t2) (tsubstTy d S41 T))) with
    | (Q_Abs S39 S40 T93 t58 t59 jm61 jm62) => (fun (G13 : Env) (d : (Trace TyVar)) (H107 : (subst_etvar G12 K63 S41 d G11 G13)) =>
      (Q_Abs G13 (tsubstTy (weakenTrace d H0) S41 S39) (tsubstTy (weakenTrace d H0) S41 S40) (tsubstTy (weakenTrace d (HS TmVar H0)) S41 T93) (tsubstTm (weakenTrace d (HS TmVar H0)) S41 t58) (tsubstTm (weakenTrace d (HS TmVar H0)) S41 t59) (subst_etvar_TyEq G12 S41 K63 jm72 G11 S39 S40 (star) jm61 G13 d (weaken_subst_etvar _ empty H107)) (subst_etvar_TermEq G12 S41 K63 jm72 (evar G11 S39) t58 t59 T93 jm62 (appendEnv G13 (tsubstEnv d S41 (evar empty S39))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty S39) H107))))
    | (Q_App S39 T93 s16 s17 t58 t59 jm63 jm64) => (fun (G13 : Env) (d : (Trace TyVar)) (H107 : (subst_etvar G12 K63 S41 d G11 G13)) =>
      (TermEq_cast G13 _ _ _ G13 (tsubstTm d S41 (app t58 t59)) (tsubstTm d S41 (app s16 s17)) (tsubstTy d S41 (substTy X0 t59 T93)) eq_refl eq_refl eq_refl (eq_sym (tsubstTy_substTy0_comm T93 d S41 t59)) (Q_App G13 (tsubstTy (weakenTrace d H0) S41 S39) (tsubstTy (weakenTrace d (HS TmVar H0)) S41 T93) (tsubstTm (weakenTrace d H0) S41 s16) (tsubstTm (weakenTrace d H0) S41 s17) (tsubstTm (weakenTrace d H0) S41 t58) (tsubstTm (weakenTrace d H0) S41 t59) (subst_etvar_TermEq G12 S41 K63 jm72 G11 t58 s16 (tpi S39 T93) jm63 G13 d (weaken_subst_etvar _ empty H107)) (subst_etvar_TermEq G12 S41 K63 jm72 G11 t59 s17 S39 jm64 G13 d (weaken_subst_etvar _ empty H107)))))
    | (Q_Beta S39 T93 s15 t57 jm65 jm66) => (fun (G13 : Env) (d : (Trace TyVar)) (H107 : (subst_etvar G12 K63 S41 d G11 G13)) =>
      (TermEq_cast G13 _ _ _ G13 (tsubstTm d S41 (app (abs S39 t57) s15)) (tsubstTm d S41 (substTm X0 s15 t57)) (tsubstTy d S41 (substTy X0 s15 T93)) eq_refl eq_refl (eq_sym (tsubstTm_substTm0_comm t57 d S41 s15)) (eq_sym (tsubstTy_substTy0_comm T93 d S41 s15)) (Q_Beta G13 (tsubstTy (weakenTrace d H0) S41 S39) (tsubstTy (weakenTrace d (HS TmVar H0)) S41 T93) (tsubstTm (weakenTrace d H0) S41 s15) (tsubstTm (weakenTrace d (HS TmVar H0)) S41 t57) (subst_etvar_Typing G12 S41 K63 jm72 (evar G11 S39) t57 T93 jm65 (appendEnv G13 (tsubstEnv d S41 (evar empty S39))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty S39) H107)) (subst_etvar_Typing G12 S41 K63 jm72 G11 s15 S39 jm66 G13 d (weaken_subst_etvar _ empty H107)))))
    | (Q_Eta S39 T93 t57 jm67) => (fun (G13 : Env) (d : (Trace TyVar)) (H107 : (subst_etvar G12 K63 S41 d G11 G13)) =>
      (TermEq_cast G13 _ _ _ G13 (tsubstTm d S41 (abs S39 (app (weakenTm t57 (HS TmVar H0)) (var I0)))) (tsubstTm d S41 t57) (tsubstTy d S41 (tpi S39 T93)) eq_refl (f_equal2 abs eq_refl (f_equal2 app (weakenTm_tsubstTm (HS TmVar H0) d S41 t57) eq_refl)) eq_refl eq_refl (Q_Eta G13 (tsubstTy (weakenTrace d H0) S41 S39) (tsubstTy (weakenTrace d (HS TmVar H0)) S41 T93) (tsubstTm (weakenTrace d H0) S41 t57) (subst_etvar_Typing G12 S41 K63 jm72 G11 t57 (tpi S39 T93) jm67 G13 d (weaken_subst_etvar _ empty H107)))))
    | (Q_Refl T93 t57 jm68) => (fun (G13 : Env) (d : (Trace TyVar)) (H107 : (subst_etvar G12 K63 S41 d G11 G13)) =>
      (Q_Refl G13 (tsubstTy (weakenTrace d H0) S41 T93) (tsubstTm (weakenTrace d H0) S41 t57) (subst_etvar_Typing G12 S41 K63 jm72 G11 t57 T93 jm68 G13 d (weaken_subst_etvar _ empty H107))))
    | (Q_Symm T93 s15 t57 jm69) => (fun (G13 : Env) (d : (Trace TyVar)) (H107 : (subst_etvar G12 K63 S41 d G11 G13)) =>
      (Q_Symm G13 (tsubstTy (weakenTrace d H0) S41 T93) (tsubstTm (weakenTrace d H0) S41 s15) (tsubstTm (weakenTrace d H0) S41 t57) (subst_etvar_TermEq G12 S41 K63 jm72 G11 t57 s15 T93 jm69 G13 d (weaken_subst_etvar _ empty H107))))
    | (Q_Trans T93 s15 t57 u1 jm70 jm71) => (fun (G13 : Env) (d : (Trace TyVar)) (H107 : (subst_etvar G12 K63 S41 d G11 G13)) =>
      (Q_Trans G13 (tsubstTy (weakenTrace d H0) S41 T93) (tsubstTm (weakenTrace d H0) S41 s15) (tsubstTm (weakenTrace d H0) S41 t57) (tsubstTm (weakenTrace d H0) S41 u1) (subst_etvar_TermEq G12 S41 K63 jm72 G11 s15 u1 T93 jm70 G13 d (weaken_subst_etvar _ empty H107)) (subst_etvar_TermEq G12 S41 K63 jm72 G11 u1 t57 T93 jm71 G13 d (weaken_subst_etvar _ empty H107))))
  end
with subst_etvar_Typing (G12 : Env) (S40 : Ty) (K63 : Kind) (jm69 : (Kinding G12 S40 K63)) (G11 : Env) (t : Tm) (T : Ty) (jm70 : (Typing G11 t T)) :
(forall (G13 : Env) (d : (Trace TyVar)) (H94 : (subst_etvar G12 K63 S40 d G11 G13)) ,
  (Typing G13 (tsubstTm d S40 t) (tsubstTy d S40 T))) :=
  match jm70 in (Typing _ t T) return (forall (G13 : Env) (d : (Trace TyVar)) (H94 : (subst_etvar G12 K63 S40 d G11 G13)) ,
    (Typing G13 (tsubstTm d S40 t) (tsubstTy d S40 T))) with
    | (T_Var T93 x57 lk5 H80 H81) => (fun (G13 : Env) (d : (Trace TyVar)) (H94 : (subst_etvar G12 K63 S40 d G11 G13)) =>
      (T_Var G13 (tsubstTy (weakenTrace d H0) S40 T93) x57 (subst_etvar_lookup_evar K63 (Kinding_wf_0 G12 S40 K63 jm69) H94 T93 lk5) (substhvl_TyVar_wfTy (Kinding_wf_0 G12 S40 K63 jm69) _ _ H80 (weaken_substhvl_TyVar H0 (subst_etvar_substhvl_TyVar _ H94))) (substhvl_TyVar_wfindex_TmVar (weaken_substhvl_TyVar H0 (subst_etvar_substhvl_TyVar _ H94)) H81)))
    | (T_Abs S39 T93 t57 jm66 jm67) => (fun (G13 : Env) (d : (Trace TyVar)) (H94 : (subst_etvar G12 K63 S40 d G11 G13)) =>
      (T_Abs G13 (tsubstTy (weakenTrace d H0) S40 S39) (tsubstTy (weakenTrace d (HS TmVar H0)) S40 T93) (tsubstTm (weakenTrace d (HS TmVar H0)) S40 t57) (subst_etvar_Kinding G12 S40 K63 jm69 G11 S39 (star) jm66 G13 d (weaken_subst_etvar _ empty H94)) (subst_etvar_Typing G12 S40 K63 jm69 (evar G11 S39) t57 T93 jm67 (appendEnv G13 (tsubstEnv d S40 (evar empty S39))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty S39) H94))))
    | (T_App S39 T93 t58 t59 jm68 jm61) => (fun (G13 : Env) (d : (Trace TyVar)) (H94 : (subst_etvar G12 K63 S40 d G11 G13)) =>
      (Typing_cast G13 _ _ G13 (tsubstTm d S40 (app t58 t59)) (tsubstTy d S40 (substTy X0 t59 T93)) eq_refl eq_refl (eq_sym (tsubstTy_substTy0_comm T93 d S40 t59)) (T_App G13 (tsubstTy (weakenTrace d H0) S40 S39) (tsubstTy (weakenTrace d (HS TmVar H0)) S40 T93) (tsubstTm (weakenTrace d H0) S40 t58) (tsubstTm (weakenTrace d H0) S40 t59) (subst_etvar_Typing G12 S40 K63 jm69 G11 t58 (tpi S39 T93) jm68 G13 d (weaken_subst_etvar _ empty H94)) (subst_etvar_Typing G12 S40 K63 jm69 G11 t59 S39 jm61 G13 d (weaken_subst_etvar _ empty H94)))))
    | (T_All T93 t57 jm62 jm63) => (fun (G13 : Env) (d : (Trace TyVar)) (H94 : (subst_etvar G12 K63 S40 d G11 G13)) =>
      (T_All G13 (tsubstTy (weakenTrace d H0) S40 T93) (tsubstTm (weakenTrace d (HS TmVar H0)) S40 t57) (subst_etvar_Kinding G12 S40 K63 jm69 G11 T93 (star) jm62 G13 d (weaken_subst_etvar _ empty H94)) (subst_etvar_Typing G12 S40 K63 jm69 (evar G11 T93) t57 (prop) jm63 (appendEnv G13 (tsubstEnv d S40 (evar empty T93))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty T93) H94))))
    | (T_Conv T94 T95 t57 jm64 jm65) => (fun (G13 : Env) (d : (Trace TyVar)) (H94 : (subst_etvar G12 K63 S40 d G11 G13)) =>
      (T_Conv G13 (tsubstTy (weakenTrace d H0) S40 T94) (tsubstTy (weakenTrace d H0) S40 T95) (tsubstTm (weakenTrace d H0) S40 t57) (subst_etvar_Typing G12 S40 K63 jm69 G11 t57 T94 jm64 G13 d (weaken_subst_etvar _ empty H94)) (subst_etvar_TyEq G12 S40 K63 jm69 G11 T94 T95 (star) jm65 G13 d (weaken_subst_etvar _ empty H94))))
  end
with subst_etvar_Kinding (G12 : Env) (S40 : Ty) (K63 : Kind) (jm67 : (Kinding G12 S40 K63)) (G11 : Env) (T : Ty) (K : Kind) (jm68 : (Kinding G11 T K)) :
(forall (G13 : Env) (d : (Trace TyVar)) (H91 : (subst_etvar G12 K63 S40 d G11 G13)) ,
  (Kinding G13 (tsubstTy d S40 T) (tsubstKind d S40 K))) :=
  match jm68 in (Kinding _ T K) return (forall (G13 : Env) (d : (Trace TyVar)) (H91 : (subst_etvar G12 K63 S40 d G11 G13)) ,
    (Kinding G13 (tsubstTy d S40 T) (tsubstKind d S40 K))) with
    | (K_TVar K64 X11 lk5 H80 H81) => (fun (G13 : Env) (d : (Trace TyVar)) (H91 : (subst_etvar G12 K63 S40 d G11 G13)) =>
      (subst_etvar_lookup_etvar G12 S40 K63 jm67 d G11 G13 H91 X11 K64 lk5))
    | (K_Pi T94 T95 jm61 jm62) => (fun (G13 : Env) (d : (Trace TyVar)) (H91 : (subst_etvar G12 K63 S40 d G11 G13)) =>
      (K_Pi G13 (tsubstTy (weakenTrace d H0) S40 T94) (tsubstTy (weakenTrace d (HS TmVar H0)) S40 T95) (subst_etvar_Kinding G12 S40 K63 jm67 G11 T94 (star) jm61 G13 d (weaken_subst_etvar _ empty H91)) (subst_etvar_Kinding G12 S40 K63 jm67 (evar G11 T94) T95 (star) jm62 (appendEnv G13 (tsubstEnv d S40 (evar empty T94))) (weakenTrace d (HS TmVar H0)) (weaken_subst_etvar _ (evar empty T94) H91))))
    | (K_App K64 S39 T93 t57 jm63 jm64) => (fun (G13 : Env) (d : (Trace TyVar)) (H91 : (subst_etvar G12 K63 S40 d G11 G13)) =>
      (Kinding_cast G13 _ _ G13 (tsubstTy d S40 (tapp S39 t57)) (tsubstKind d S40 (substKind X0 t57 K64)) eq_refl eq_refl (eq_sym (tsubstKind_substKind0_comm K64 d S40 t57)) (K_App G13 (tsubstKind (weakenTrace d (HS TmVar H0)) S40 K64) (tsubstTy (weakenTrace d H0) S40 S39) (tsubstTy (weakenTrace d H0) S40 T93) (tsubstTm (weakenTrace d H0) S40 t57) (subst_etvar_Kinding G12 S40 K63 jm67 G11 S39 (kpi T93 K64) jm63 G13 d (weaken_subst_etvar _ empty H91)) (subst_etvar_Typing G12 S40 K63 jm67 G11 t57 T93 jm64 G13 d (weaken_subst_etvar _ empty H91)))))
    | (K_Prop) => (fun (G13 : Env) (d : (Trace TyVar)) (H91 : (subst_etvar G12 K63 S40 d G11 G13)) =>
      (K_Prop G13))
    | (K_Prf) => (fun (G13 : Env) (d : (Trace TyVar)) (H91 : (subst_etvar G12 K63 S40 d G11 G13)) =>
      (K_Prf G13))
    | (K_Conv K65 K66 T93 jm65 jm66) => (fun (G13 : Env) (d : (Trace TyVar)) (H91 : (subst_etvar G12 K63 S40 d G11 G13)) =>
      (K_Conv G13 (tsubstKind (weakenTrace d H0) S40 K65) (tsubstKind (weakenTrace d H0) S40 K66) (tsubstTy (weakenTrace d H0) S40 T93) (subst_etvar_Kinding G12 S40 K63 jm67 G11 T93 K65 jm65 G13 d (weaken_subst_etvar _ empty H91)) (subst_etvar_KindEq G12 S40 K63 jm67 G11 K65 K66 jm66 G13 d (weaken_subst_etvar _ empty H91))))
  end
with subst_etvar_WfKind (G12 : Env) (S39 : Ty) (K63 : Kind) (jm63 : (Kinding G12 S39 K63)) (G11 : Env) (K : Kind) (jm64 : (WfKind G11 K)) :
(forall (G13 : Env) (d : (Trace TyVar)) (H82 : (subst_etvar G12 K63 S39 d G11 G13)) ,
  (WfKind G13 (tsubstKind d S39 K))) :=
  match jm64 in (WfKind _ K) return (forall (G13 : Env) (d : (Trace TyVar)) (H82 : (subst_etvar G12 K63 S39 d G11 G13)) ,
    (WfKind G13 (tsubstKind d S39 K))) with
    | (WfStar) => (fun (G13 : Env) (d : (Trace TyVar)) (H82 : (subst_etvar G12 K63 S39 d G11 G13)) =>
      (WfStar G13))
    | (WfPi K64 T93 jm61 jm62) => (fun (G13 : Env) (d : (Trace TyVar)) (H82 : (subst_etvar G12 K63 S39 d G11 G13)) =>
      (WfKind_cast G13 _ G13 (tsubstKind d S39 (kpi T93 (weakenKind K64 (HS TmVar H0)))) eq_refl (f_equal2 kpi eq_refl (weakenKind_tsubstKind (HS TmVar H0) d S39 K64)) (WfPi G13 (tsubstKind (weakenTrace d H0) S39 K64) (tsubstTy (weakenTrace d H0) S39 T93) (subst_etvar_Kinding G12 S39 K63 jm63 G11 T93 (star) jm61 G13 d (weaken_subst_etvar _ empty H82)) (subst_etvar_WfKind G12 S39 K63 jm63 G11 K64 jm62 G13 d (weaken_subst_etvar _ empty H82)))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutoffTmVar_append weakenCutoffTyVar_append weakenTrace_append weakenKind_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.