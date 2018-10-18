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
  Fixpoint weakenIndexTyVar (X10 : (Index TyVar)) (k : Hvl) {struct k} :
  (Index TyVar) :=
    match k with
      | (H0) => X10
      | (HS a k) => match a with
        | (TyVar) => (IS (weakenIndexTyVar X10 k))
        | _ => (weakenIndexTyVar X10 k)
      end
    end.
  Lemma weakenIndexTmVar_append  :
    (forall (x6 : (Index TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTmVar (weakenIndexTmVar x6 k) k0) = (weakenIndexTmVar x6 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexTyVar_append  :
    (forall (X10 : (Index TyVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTyVar (weakenIndexTyVar X10 k) k0) = (weakenIndexTyVar X10 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Ty : Set :=
    | TVar (X : (Index TyVar))
    | TArr (T1 : Ty) (T2 : Ty)
    | TAll (T : Ty)
    | TProd (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Pat : Set :=
    | PVar (T : Ty)
    | PTVar 
    | PProd (p1 : Pat) (p2 : Pat).
  Scheme ind_Pat := Induction for Pat Sort Prop.
  
  Inductive Tm : Set :=
    | Var (x : (Index TmVar))
    | Abs (T : Ty) (t : Tm)
    | App (t1 : Tm) (t2 : Tm)
    | TAbs (t : Tm)
    | TApp (t : Tm) (T : Ty)
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
      | (PTVar) => (HS TyVar H0)
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
  Fixpoint tshiftIndex (c : (Cutoff TyVar)) (X10 : (Index TyVar)) {struct c} :
  (Index TyVar) :=
    match c with
      | (C0) => (IS X10)
      | (CS c) => match X10 with
        | (I0) => I0
        | (IS X10) => (IS (tshiftIndex c X10))
      end
    end.
  Fixpoint tshiftTy (c : (Cutoff TyVar)) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (TVar X10) => (TVar (tshiftIndex c X10))
      | (TArr T9 T10) => (TArr (tshiftTy c T9) (tshiftTy c T10))
      | (TAll T11) => (TAll (tshiftTy (CS c) T11))
      | (TProd T12 T13) => (TProd (tshiftTy c T12) (tshiftTy c T13))
    end.
  Fixpoint tshiftPat (c : (Cutoff TyVar)) (p9 : Pat) {struct p9} :
  Pat :=
    match p9 with
      | (PVar T9) => (PVar (tshiftTy c T9))
      | (PTVar) => (PTVar)
      | (PProd p10 p11) => (PProd (tshiftPat c p10) (tshiftPat (weakenCutoffTyVar c (appendHvl H0 (bind p10))) p11))
    end.
  Fixpoint shiftTm (c : (Cutoff TmVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x6) => (Var (shiftIndex c x6))
      | (Abs T9 t8) => (Abs T9 (shiftTm (CS c) t8))
      | (App t9 t10) => (App (shiftTm c t9) (shiftTm c t10))
      | (TAbs t11) => (TAbs (shiftTm c t11))
      | (TApp t12 T10) => (TApp (shiftTm c t12) T10)
      | (Prod t13 t14) => (Prod (shiftTm c t13) (shiftTm c t14))
      | (Case t15 p9 t16) => (Case (shiftTm c t15) p9 (shiftTm (weakenCutoffTmVar c (appendHvl H0 (bind p9))) t16))
    end.
  Fixpoint tshiftTm (c : (Cutoff TyVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x6) => (Var x6)
      | (Abs T9 t8) => (Abs (tshiftTy c T9) (tshiftTm c t8))
      | (App t9 t10) => (App (tshiftTm c t9) (tshiftTm c t10))
      | (TAbs t11) => (TAbs (tshiftTm (CS c) t11))
      | (TApp t12 T10) => (TApp (tshiftTm c t12) (tshiftTy c T10))
      | (Prod t13 t14) => (Prod (tshiftTm c t13) (tshiftTm c t14))
      | (Case t15 p9 t16) => (Case (tshiftTm c t15) (tshiftPat c p9) (tshiftTm (weakenCutoffTyVar c (appendHvl H0 (bind p9))) t16))
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
      | (HS TyVar k) => (tshiftPat C0 (weakenPat p9 k))
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
        (T9 : (Trace a)).
  
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
  Fixpoint substIndex (d : (Trace TmVar)) (s : Tm) (x6 : (Index TmVar)) {struct d} :
  Tm :=
    match d with
      | (X0) => match x6 with
        | (I0) => s
        | (IS x6) => (Var x6)
      end
      | (XS TmVar d) => match x6 with
        | (I0) => (Var I0)
        | (IS x6) => (shiftTm C0 (substIndex d s x6))
      end
      | (XS TyVar d) => (tshiftTm C0 (substIndex d s x6))
    end.
  Fixpoint tsubstIndex (d : (Trace TyVar)) (S0 : Ty) (X10 : (Index TyVar)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X10 with
        | (I0) => S0
        | (IS X10) => (TVar X10)
      end
      | (XS TmVar d) => (tsubstIndex d S0 X10)
      | (XS TyVar d) => match X10 with
        | (I0) => (TVar I0)
        | (IS X10) => (tshiftTy C0 (tsubstIndex d S0 X10))
      end
    end.
  Fixpoint tsubstTy (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) {struct S1} :
  Ty :=
    match S1 with
      | (TVar X10) => (tsubstIndex d S0 X10)
      | (TArr T9 T10) => (TArr (tsubstTy d S0 T9) (tsubstTy d S0 T10))
      | (TAll T11) => (TAll (tsubstTy (weakenTrace d (HS TyVar H0)) S0 T11))
      | (TProd T12 T13) => (TProd (tsubstTy d S0 T12) (tsubstTy d S0 T13))
    end.
  Fixpoint tsubstPat (d : (Trace TyVar)) (S0 : Ty) (p9 : Pat) {struct p9} :
  Pat :=
    match p9 with
      | (PVar T9) => (PVar (tsubstTy d S0 T9))
      | (PTVar) => (PTVar)
      | (PProd p10 p11) => (PProd (tsubstPat d S0 p10) (tsubstPat (weakenTrace d (appendHvl H0 (bind p10))) S0 p11))
    end.
  Fixpoint substTm (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (Var x6) => (substIndex d s x6)
      | (Abs T9 t8) => (Abs T9 (substTm (weakenTrace d (HS TmVar H0)) s t8))
      | (App t9 t10) => (App (substTm d s t9) (substTm d s t10))
      | (TAbs t11) => (TAbs (substTm (weakenTrace d (HS TyVar H0)) s t11))
      | (TApp t12 T10) => (TApp (substTm d s t12) T10)
      | (Prod t13 t14) => (Prod (substTm d s t13) (substTm d s t14))
      | (Case t15 p9 t16) => (Case (substTm d s t15) p9 (substTm (weakenTrace d (appendHvl H0 (bind p9))) s t16))
    end.
  Fixpoint tsubstTm (d : (Trace TyVar)) (S0 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x6) => (Var x6)
      | (Abs T9 t8) => (Abs (tsubstTy d S0 T9) (tsubstTm (weakenTrace d (HS TmVar H0)) S0 t8))
      | (App t9 t10) => (App (tsubstTm d S0 t9) (tsubstTm d S0 t10))
      | (TAbs t11) => (TAbs (tsubstTm (weakenTrace d (HS TyVar H0)) S0 t11))
      | (TApp t12 T10) => (TApp (tsubstTm d S0 t12) (tsubstTy d S0 T10))
      | (Prod t13 t14) => (Prod (tsubstTm d S0 t13) (tsubstTm d S0 t14))
      | (Case t15 p9 t16) => (Case (tsubstTm d S0 t15) (tsubstPat d S0 p9) (tsubstTm (weakenTrace d (appendHvl H0 (bind p9))) S0 t16))
    end.
End Subst.

Global Hint Resolve (f_equal (tshiftPat C0)) : cong_shift0.
Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutoffTmVar_append weakenCutoffTyVar_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_tshift_bind  :
  (forall (p9 : Pat) ,
    (forall (c : (Cutoff TyVar)) ,
      ((bind (tshiftPat c p9)) = (bind p9)))).
Proof.
  apply_mutual_ind (ind_bind_Pat); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_tshift_bind : interaction.
 Hint Rewrite stability_tshift_bind : stability_shift.
Lemma stability_weaken_bind  :
  (forall (k : Hvl) (p10 : Pat) ,
    ((bind (weakenPat p10 k)) = (bind p10))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bind : interaction.
 Hint Rewrite stability_weaken_bind : stability_weaken.
Lemma stability_tsubst_bind  :
  (forall (p10 : Pat) ,
    (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((bind (tsubstPat d S0 p10)) = (bind p10)))).
Proof.
  apply_mutual_ind (ind_bind_Pat); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_tsubst_bind : interaction.
 Hint Rewrite stability_tsubst_bind : stability_subst.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x6 : (Index TmVar)) ,
      ((substIndex (weakenTrace X0 k) s (shiftIndex (weakenCutoffTmVar C0 k) x6)) = (Var x6))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S1 : Ty) :
    (forall (k : Hvl) (X10 : (Index TyVar)) ,
      ((tsubstIndex (weakenTrace X0 k) S1 (tshiftIndex (weakenCutoffTyVar C0 k) X10)) = (TVar X10))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint tsubst0_tshift0_Ty_reflection_ind (S2 : Ty) (k : Hvl) (S1 : Ty) {struct S2} :
  ((tsubstTy (weakenTrace X0 k) S1 (tshiftTy (weakenCutoffTyVar C0 k) S2)) = S2) :=
    match S2 return ((tsubstTy (weakenTrace X0 k) S1 (tshiftTy (weakenCutoffTyVar C0 k) S2)) = S2) with
      | (TVar X10) => (tsubstIndex0_tshiftIndex0_reflection_ind S1 k X10)
      | (TArr T10 T11) => (f_equal2 TArr (tsubst0_tshift0_Ty_reflection_ind T10 k S1) (tsubst0_tshift0_Ty_reflection_ind T11 k S1))
      | (TAll T9) => (f_equal TAll (eq_trans (f_equal3 tsubstTy (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T9 (HS TyVar k) S1)))
      | (TProd T10 T11) => (f_equal2 TProd (tsubst0_tshift0_Ty_reflection_ind T10 k S1) (tsubst0_tshift0_Ty_reflection_ind T11 k S1))
    end.
  Fixpoint tsubst0_tshift0_Pat_reflection_ind (p11 : Pat) (k : Hvl) (S1 : Ty) {struct p11} :
  ((tsubstPat (weakenTrace X0 k) S1 (tshiftPat (weakenCutoffTyVar C0 k) p11)) = p11) :=
    match p11 return ((tsubstPat (weakenTrace X0 k) S1 (tshiftPat (weakenCutoffTyVar C0 k) p11)) = p11) with
      | (PVar T9) => (f_equal PVar (tsubst0_tshift0_Ty_reflection_ind T9 k S1))
      | (PTVar) => eq_refl
      | (PProd p12 p13) => (f_equal2 PProd (tsubst0_tshift0_Pat_reflection_ind p12 k S1) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bind _ _))) (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p12)))) eq_refl (f_equal2 tshiftPat (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p12))) eq_refl)) (tsubst0_tshift0_Pat_reflection_ind p13 (appendHvl k (appendHvl H0 (bind p12))) S1)))
    end.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutoffTmVar C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutoffTmVar C0 k) s0)) = s0) with
      | (Var x6) => (substIndex0_shiftIndex0_reflection_ind s k x6)
      | (Abs T9 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t8 (HS TmVar k) s)))
      | (App t9 t10) => (f_equal2 App (subst0_shift0_Tm_reflection_ind t9 k s) (subst0_shift0_Tm_reflection_ind t10 k s))
      | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t8 (HS TyVar k) s)))
      | (TApp t8 T9) => (f_equal2 TApp (subst0_shift0_Tm_reflection_ind t8 k s) eq_refl)
      | (Prod t9 t10) => (f_equal2 Prod (subst0_shift0_Tm_reflection_ind t9 k s) (subst0_shift0_Tm_reflection_ind t10 k s))
      | (Case t9 p11 t10) => (f_equal3 Case (subst0_shift0_Tm_reflection_ind t9 k s) eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p11))) eq_refl (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p11))) eq_refl)) (subst0_shift0_Tm_reflection_ind t10 (appendHvl k (appendHvl H0 (bind p11))) s)))
    end.
  Fixpoint tsubst0_tshift0_Tm_reflection_ind (s : Tm) (k : Hvl) (S1 : Ty) {struct s} :
  ((tsubstTm (weakenTrace X0 k) S1 (tshiftTm (weakenCutoffTyVar C0 k) s)) = s) :=
    match s return ((tsubstTm (weakenTrace X0 k) S1 (tshiftTm (weakenCutoffTyVar C0 k) s)) = s) with
      | (Var x6) => eq_refl
      | (Abs T9 t8) => (f_equal2 Abs (tsubst0_tshift0_Ty_reflection_ind T9 k S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t8 (HS TmVar k) S1)))
      | (App t9 t10) => (f_equal2 App (tsubst0_tshift0_Tm_reflection_ind t9 k S1) (tsubst0_tshift0_Tm_reflection_ind t10 k S1))
      | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t8 (HS TyVar k) S1)))
      | (TApp t8 T9) => (f_equal2 TApp (tsubst0_tshift0_Tm_reflection_ind t8 k S1) (tsubst0_tshift0_Ty_reflection_ind T9 k S1))
      | (Prod t9 t10) => (f_equal2 Prod (tsubst0_tshift0_Tm_reflection_ind t9 k S1) (tsubst0_tshift0_Tm_reflection_ind t10 k S1))
      | (Case t9 p11 t10) => (f_equal3 Case (tsubst0_tshift0_Tm_reflection_ind t9 k S1) (tsubst0_tshift0_Pat_reflection_ind p11 k S1) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bind _ _))) (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p11)))) eq_refl (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p11))) eq_refl)) (tsubst0_tshift0_Tm_reflection_ind t10 (appendHvl k (appendHvl H0 (bind p11))) S1)))
    end.
  Definition tsubstTy0_tshiftTy0_reflection (S2 : Ty) : (forall (S1 : Ty) ,
    ((tsubstTy X0 S1 (tshiftTy C0 S2)) = S2)) := (tsubst0_tshift0_Ty_reflection_ind S2 H0).
  Definition tsubstPat0_tshiftPat0_reflection (p11 : Pat) : (forall (S1 : Ty) ,
    ((tsubstPat X0 S1 (tshiftPat C0 p11)) = p11)) := (tsubst0_tshift0_Pat_reflection_ind p11 H0).
  Definition substTm0_shiftTm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((substTm X0 s (shiftTm C0 s0)) = s0)) := (subst0_shift0_Tm_reflection_ind s0 H0).
  Definition tsubstTm0_tshiftTm0_reflection (s : Tm) : (forall (S1 : Ty) ,
    ((tsubstTm X0 S1 (tshiftTm C0 s)) = s)) := (tsubst0_tshift0_Tm_reflection_ind s H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c0 : (Cutoff TmVar)) (x6 : (Index TmVar)) ,
        ((shiftIndex (weakenCutoffTmVar (CS c0) k) (shiftIndex (weakenCutoffTmVar C0 k) x6)) = (shiftIndex (weakenCutoffTmVar C0 k) (shiftIndex (weakenCutoffTmVar c0 k) x6)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c0 : (Cutoff TyVar)) (X10 : (Index TyVar)) ,
        ((tshiftIndex (weakenCutoffTyVar (CS c0) k) (tshiftIndex (weakenCutoffTyVar C0 k) X10)) = (tshiftIndex (weakenCutoffTyVar C0 k) (tshiftIndex (weakenCutoffTyVar c0 k) X10)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint tshift_tshift0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c0 : (Cutoff TyVar)) {struct S1} :
    ((tshiftTy (weakenCutoffTyVar (CS c0) k) (tshiftTy (weakenCutoffTyVar C0 k) S1)) = (tshiftTy (weakenCutoffTyVar C0 k) (tshiftTy (weakenCutoffTyVar c0 k) S1))) :=
      match S1 return ((tshiftTy (weakenCutoffTyVar (CS c0) k) (tshiftTy (weakenCutoffTyVar C0 k) S1)) = (tshiftTy (weakenCutoffTyVar C0 k) (tshiftTy (weakenCutoffTyVar c0 k) S1))) with
        | (TVar X10) => (f_equal TVar (tshiftIndex_tshiftIndex0_comm_ind k c0 X10))
        | (TArr T10 T11) => (f_equal2 TArr (tshift_tshift0_Ty_comm_ind T10 k c0) (tshift_tshift0_Ty_comm_ind T11 k c0))
        | (TAll T9) => (f_equal TAll (tshift_tshift0_Ty_comm_ind T9 (HS TyVar k) c0))
        | (TProd T10 T11) => (f_equal2 TProd (tshift_tshift0_Ty_comm_ind T10 k c0) (tshift_tshift0_Ty_comm_ind T11 k c0))
      end.
    Fixpoint tshift_tshift0_Pat_comm_ind (p11 : Pat) (k : Hvl) (c0 : (Cutoff TyVar)) {struct p11} :
    ((tshiftPat (weakenCutoffTyVar (CS c0) k) (tshiftPat (weakenCutoffTyVar C0 k) p11)) = (tshiftPat (weakenCutoffTyVar C0 k) (tshiftPat (weakenCutoffTyVar c0 k) p11))) :=
      match p11 return ((tshiftPat (weakenCutoffTyVar (CS c0) k) (tshiftPat (weakenCutoffTyVar C0 k) p11)) = (tshiftPat (weakenCutoffTyVar C0 k) (tshiftPat (weakenCutoffTyVar c0 k) p11))) with
        | (PVar T9) => (f_equal PVar (tshift_tshift0_Ty_comm_ind T9 k c0))
        | (PTVar) => eq_refl
        | (PProd p12 p13) => (f_equal2 PProd (tshift_tshift0_Pat_comm_ind p12 k c0) (eq_trans (f_equal2 tshiftPat (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bind _ _))) (weakenCutoffTyVar_append (CS c0) k (appendHvl H0 (bind p12)))) (f_equal2 tshiftPat (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p12))) eq_refl)) (eq_trans (tshift_tshift0_Pat_comm_ind p13 (appendHvl k (appendHvl H0 (bind p12))) c0) (f_equal2 tshiftPat (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p12)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bind _ _))))) (f_equal2 tshiftPat (eq_sym (weakenCutoffTyVar_append c0 k (appendHvl H0 (bind p12)))) eq_refl)))))
      end.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff TmVar)) {struct s} :
    ((shiftTm (weakenCutoffTmVar (CS c0) k) (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (shiftTm (weakenCutoffTmVar c0 k) s))) :=
      match s return ((shiftTm (weakenCutoffTmVar (CS c0) k) (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (shiftTm (weakenCutoffTmVar c0 k) s))) with
        | (Var x6) => (f_equal Var (shiftIndex_shiftIndex0_comm_ind k c0 x6))
        | (Abs T9 t8) => (f_equal2 Abs eq_refl (shift_shift0_Tm_comm_ind t8 (HS TmVar k) c0))
        | (App t9 t10) => (f_equal2 App (shift_shift0_Tm_comm_ind t9 k c0) (shift_shift0_Tm_comm_ind t10 k c0))
        | (TAbs t8) => (f_equal TAbs (shift_shift0_Tm_comm_ind t8 (HS TyVar k) c0))
        | (TApp t8 T9) => (f_equal2 TApp (shift_shift0_Tm_comm_ind t8 k c0) eq_refl)
        | (Prod t9 t10) => (f_equal2 Prod (shift_shift0_Tm_comm_ind t9 k c0) (shift_shift0_Tm_comm_ind t10 k c0))
        | (Case t9 p11 t10) => (f_equal3 Case (shift_shift0_Tm_comm_ind t9 k c0) eq_refl (eq_trans (f_equal2 shiftTm (weakenCutoffTmVar_append (CS c0) k (appendHvl H0 (bind p11))) (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p11))) eq_refl)) (eq_trans (shift_shift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) c0) (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p11)))) (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append c0 k (appendHvl H0 (bind p11)))) eq_refl)))))
      end.
    Fixpoint shift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff TmVar)) {struct s} :
    ((shiftTm (weakenCutoffTmVar c0 k) (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (shiftTm (weakenCutoffTmVar c0 k) s))) :=
      match s return ((shiftTm (weakenCutoffTmVar c0 k) (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (shiftTm (weakenCutoffTmVar c0 k) s))) with
        | (Var x6) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs eq_refl (shift_tshift0_Tm_comm_ind t8 (HS TmVar k) c0))
        | (App t9 t10) => (f_equal2 App (shift_tshift0_Tm_comm_ind t9 k c0) (shift_tshift0_Tm_comm_ind t10 k c0))
        | (TAbs t8) => (f_equal TAbs (shift_tshift0_Tm_comm_ind t8 (HS TyVar k) c0))
        | (TApp t8 T9) => (f_equal2 TApp (shift_tshift0_Tm_comm_ind t8 k c0) eq_refl)
        | (Prod t9 t10) => (f_equal2 Prod (shift_tshift0_Tm_comm_ind t9 k c0) (shift_tshift0_Tm_comm_ind t10 k c0))
        | (Case t9 p11 t10) => (f_equal3 Case (shift_tshift0_Tm_comm_ind t9 k c0) eq_refl (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bind _ _))) (weakenCutoffTmVar_append c0 k (appendHvl H0 (bind p11)))) (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p11))) eq_refl)) (eq_trans (shift_tshift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) c0) (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p11)))) (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append c0 k (appendHvl H0 (bind p11)))) eq_refl)))))
      end.
    Fixpoint tshift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff TyVar)) {struct s} :
    ((tshiftTm (weakenCutoffTyVar c0 k) (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (tshiftTm (weakenCutoffTyVar c0 k) s))) :=
      match s return ((tshiftTm (weakenCutoffTyVar c0 k) (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (tshiftTm (weakenCutoffTyVar c0 k) s))) with
        | (Var x6) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs eq_refl (tshift_shift0_Tm_comm_ind t8 (HS TmVar k) c0))
        | (App t9 t10) => (f_equal2 App (tshift_shift0_Tm_comm_ind t9 k c0) (tshift_shift0_Tm_comm_ind t10 k c0))
        | (TAbs t8) => (f_equal TAbs (tshift_shift0_Tm_comm_ind t8 (HS TyVar k) c0))
        | (TApp t8 T9) => (f_equal2 TApp (tshift_shift0_Tm_comm_ind t8 k c0) eq_refl)
        | (Prod t9 t10) => (f_equal2 Prod (tshift_shift0_Tm_comm_ind t9 k c0) (tshift_shift0_Tm_comm_ind t10 k c0))
        | (Case t9 p11 t10) => (f_equal3 Case (tshift_shift0_Tm_comm_ind t9 k c0) eq_refl (eq_trans (f_equal2 tshiftTm (weakenCutoffTyVar_append c0 k (appendHvl H0 (bind p11))) (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p11))) eq_refl)) (eq_trans (tshift_shift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) c0) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p11)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bind _ _))))) (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append c0 k (appendHvl H0 (bind p11)))) eq_refl)))))
      end.
    Fixpoint tshift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff TyVar)) {struct s} :
    ((tshiftTm (weakenCutoffTyVar (CS c0) k) (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (tshiftTm (weakenCutoffTyVar c0 k) s))) :=
      match s return ((tshiftTm (weakenCutoffTyVar (CS c0) k) (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (tshiftTm (weakenCutoffTyVar c0 k) s))) with
        | (Var x6) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs (tshift_tshift0_Ty_comm_ind T9 k c0) (tshift_tshift0_Tm_comm_ind t8 (HS TmVar k) c0))
        | (App t9 t10) => (f_equal2 App (tshift_tshift0_Tm_comm_ind t9 k c0) (tshift_tshift0_Tm_comm_ind t10 k c0))
        | (TAbs t8) => (f_equal TAbs (tshift_tshift0_Tm_comm_ind t8 (HS TyVar k) c0))
        | (TApp t8 T9) => (f_equal2 TApp (tshift_tshift0_Tm_comm_ind t8 k c0) (tshift_tshift0_Ty_comm_ind T9 k c0))
        | (Prod t9 t10) => (f_equal2 Prod (tshift_tshift0_Tm_comm_ind t9 k c0) (tshift_tshift0_Tm_comm_ind t10 k c0))
        | (Case t9 p11 t10) => (f_equal3 Case (tshift_tshift0_Tm_comm_ind t9 k c0) (tshift_tshift0_Pat_comm_ind p11 k c0) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bind _ _))) (weakenCutoffTyVar_append (CS c0) k (appendHvl H0 (bind p11)))) (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p11))) eq_refl)) (eq_trans (tshift_tshift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) c0) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p11)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bind _ _))))) (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append c0 k (appendHvl H0 (bind p11)))) eq_refl)))))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_Ty_comm (S1 : Ty) : (forall (c0 : (Cutoff TyVar)) ,
      ((tshiftTy (CS c0) (tshiftTy C0 S1)) = (tshiftTy C0 (tshiftTy c0 S1)))) := (tshift_tshift0_Ty_comm_ind S1 H0).
    Definition tshift_tshift0_Pat_comm (p11 : Pat) : (forall (c0 : (Cutoff TyVar)) ,
      ((tshiftPat (CS c0) (tshiftPat C0 p11)) = (tshiftPat C0 (tshiftPat c0 p11)))) := (tshift_tshift0_Pat_comm_ind p11 H0).
    Definition shift_shift0_Tm_comm (s : Tm) : (forall (c0 : (Cutoff TmVar)) ,
      ((shiftTm (CS c0) (shiftTm C0 s)) = (shiftTm C0 (shiftTm c0 s)))) := (shift_shift0_Tm_comm_ind s H0).
    Definition shift_tshift0_Tm_comm (s : Tm) : (forall (c0 : (Cutoff TmVar)) ,
      ((shiftTm c0 (tshiftTm C0 s)) = (tshiftTm C0 (shiftTm c0 s)))) := (shift_tshift0_Tm_comm_ind s H0).
    Definition tshift_shift0_Tm_comm (s : Tm) : (forall (c0 : (Cutoff TyVar)) ,
      ((tshiftTm c0 (shiftTm C0 s)) = (shiftTm C0 (tshiftTm c0 s)))) := (tshift_shift0_Tm_comm_ind s H0).
    Definition tshift_tshift0_Tm_comm (s : Tm) : (forall (c0 : (Cutoff TyVar)) ,
      ((tshiftTm (CS c0) (tshiftTm C0 s)) = (tshiftTm C0 (tshiftTm c0 s)))) := (tshift_tshift0_Tm_comm_ind s H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite tshift_tshift0_Pat_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : interaction.
 Hint Rewrite tshift_tshift0_Pat_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTy_tshiftTy  :
    (forall (k : Hvl) (c0 : (Cutoff TyVar)) (S1 : Ty) ,
      ((weakenTy (tshiftTy c0 S1) k) = (tshiftTy (weakenCutoffTyVar c0 k) (weakenTy S1 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenPat_tshiftPat  :
    (forall (k : Hvl) (c0 : (Cutoff TyVar)) (p11 : Pat) ,
      ((weakenPat (tshiftPat c0 p11) k) = (tshiftPat (weakenCutoffTyVar c0 k) (weakenPat p11 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k : Hvl) (c0 : (Cutoff TmVar)) (s : Tm) ,
      ((weakenTm (shiftTm c0 s) k) = (shiftTm (weakenCutoffTmVar c0 k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k : Hvl) (c0 : (Cutoff TyVar)) (s : Tm) ,
      ((weakenTm (tshiftTm c0 s) k) = (tshiftTm (weakenCutoffTyVar c0 k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTm_substIndex0_comm_ind (c0 : (Cutoff TmVar)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((shiftTm (weakenCutoffTmVar c0 k) (substIndex (weakenTrace X0 k) s x6)) = (substIndex (weakenTrace X0 k) (shiftTm c0 s) (shiftIndex (weakenCutoffTmVar (CS c0) k) x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_substIndex0_comm_ind (c0 : (Cutoff TyVar)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((tshiftTm (weakenCutoffTyVar c0 k) (substIndex (weakenTrace X0 k) s x6)) = (substIndex (weakenTrace X0 k) (tshiftTm c0 s) x6))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTy_tsubstIndex0_comm_ind (c0 : (Cutoff TyVar)) (S1 : Ty) :
      (forall (k : Hvl) (X10 : (Index TyVar)) ,
        ((tshiftTy (weakenCutoffTyVar c0 k) (tsubstIndex (weakenTrace X0 k) S1 X10)) = (tsubstIndex (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftIndex (weakenCutoffTyVar (CS c0) k) X10)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint tshift_tsubst0_Ty_comm_ind (S2 : Ty) (k : Hvl) (c0 : (Cutoff TyVar)) (S1 : Ty) {struct S2} :
    ((tshiftTy (weakenCutoffTyVar c0 k) (tsubstTy (weakenTrace X0 k) S1 S2)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTy (weakenCutoffTyVar (CS c0) k) S2))) :=
      match S2 return ((tshiftTy (weakenCutoffTyVar c0 k) (tsubstTy (weakenTrace X0 k) S1 S2)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTy (weakenCutoffTyVar (CS c0) k) S2))) with
        | (TVar X10) => (tshiftTy_tsubstIndex0_comm_ind c0 S1 k X10)
        | (TArr T10 T11) => (f_equal2 TArr (tshift_tsubst0_Ty_comm_ind T10 k c0 S1) (tshift_tsubst0_Ty_comm_ind T11 k c0 S1))
        | (TAll T9) => (f_equal TAll (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T9 (HS TyVar k) c0 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TProd T10 T11) => (f_equal2 TProd (tshift_tsubst0_Ty_comm_ind T10 k c0 S1) (tshift_tsubst0_Ty_comm_ind T11 k c0 S1))
      end.
    Fixpoint tshift_tsubst0_Pat_comm_ind (p11 : Pat) (k : Hvl) (c0 : (Cutoff TyVar)) (S1 : Ty) {struct p11} :
    ((tshiftPat (weakenCutoffTyVar c0 k) (tsubstPat (weakenTrace X0 k) S1 p11)) = (tsubstPat (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftPat (weakenCutoffTyVar (CS c0) k) p11))) :=
      match p11 return ((tshiftPat (weakenCutoffTyVar c0 k) (tsubstPat (weakenTrace X0 k) S1 p11)) = (tsubstPat (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftPat (weakenCutoffTyVar (CS c0) k) p11))) with
        | (PVar T9) => (f_equal PVar (tshift_tsubst0_Ty_comm_ind T9 k c0 S1))
        | (PTVar) => eq_refl
        | (PProd p12 p13) => (f_equal2 PProd (tshift_tsubst0_Pat_comm_ind p12 k c0 S1) (eq_trans (f_equal2 tshiftPat (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bind _ _ _) (eq_refl H0)))) (weakenCutoffTyVar_append c0 k (appendHvl H0 (bind p12)))) (f_equal3 tsubstPat (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p12))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Pat_comm_ind p13 (appendHvl k (appendHvl H0 (bind p12))) c0 S1) (f_equal3 tsubstPat (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p12)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bind _ _))))) eq_refl (f_equal2 tshiftPat (eq_sym (weakenCutoffTyVar_append (CS c0) k (appendHvl H0 (bind p12)))) eq_refl)))))
      end.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c0 : (Cutoff TmVar)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutoffTmVar c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c0 s) (shiftTm (weakenCutoffTmVar (CS c0) k) s0))) :=
      match s0 return ((shiftTm (weakenCutoffTmVar c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c0 s) (shiftTm (weakenCutoffTmVar (CS c0) k) s0))) with
        | (Var x6) => (shiftTm_substIndex0_comm_ind c0 s k x6)
        | (Abs T9 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t8 (HS TmVar k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t9 t10) => (f_equal2 App (shift_subst0_Tm_comm_ind t9 k c0 s) (shift_subst0_Tm_comm_ind t10 k c0 s))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t8 (HS TyVar k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t8 T9) => (f_equal2 TApp (shift_subst0_Tm_comm_ind t8 k c0 s) eq_refl)
        | (Prod t9 t10) => (f_equal2 Prod (shift_subst0_Tm_comm_ind t9 k c0 s) (shift_subst0_Tm_comm_ind t10 k c0 s))
        | (Case t9 p11 t10) => (f_equal3 Case (shift_subst0_Tm_comm_ind t9 k c0 s) eq_refl (eq_trans (f_equal2 shiftTm (weakenCutoffTmVar_append c0 k (appendHvl H0 (bind p11))) (f_equal3 substTm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p11))) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p11)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append (CS c0) k (appendHvl H0 (bind p11)))) eq_refl)))))
      end.
    Fixpoint shift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff TmVar)) (S1 : Ty) {struct s} :
    ((shiftTm (weakenCutoffTmVar c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) S1 (shiftTm (weakenCutoffTmVar c0 k) s))) :=
      match s return ((shiftTm (weakenCutoffTmVar c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) S1 (shiftTm (weakenCutoffTmVar c0 k) s))) with
        | (Var x6) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t8 (HS TmVar k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t9 t10) => (f_equal2 App (shift_tsubst0_Tm_comm_ind t9 k c0 S1) (shift_tsubst0_Tm_comm_ind t10 k c0 S1))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t8 (HS TyVar k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t8 T9) => (f_equal2 TApp (shift_tsubst0_Tm_comm_ind t8 k c0 S1) eq_refl)
        | (Prod t9 t10) => (f_equal2 Prod (shift_tsubst0_Tm_comm_ind t9 k c0 S1) (shift_tsubst0_Tm_comm_ind t10 k c0 S1))
        | (Case t9 p11 t10) => (f_equal3 Case (shift_tsubst0_Tm_comm_ind t9 k c0 S1) eq_refl (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bind _ _ _) (eq_refl H0)))) (weakenCutoffTmVar_append c0 k (appendHvl H0 (bind p11)))) (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p11))) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p11)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append c0 k (appendHvl H0 (bind p11)))) eq_refl)))))
      end.
    Fixpoint tshift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c0 : (Cutoff TyVar)) (s : Tm) {struct s0} :
    ((tshiftTm (weakenCutoffTyVar c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c0 s) (tshiftTm (weakenCutoffTyVar c0 k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffTyVar c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c0 s) (tshiftTm (weakenCutoffTyVar c0 k) s0))) with
        | (Var x6) => (tshiftTm_substIndex0_comm_ind c0 s k x6)
        | (Abs T9 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t8 (HS TmVar k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t9 t10) => (f_equal2 App (tshift_subst0_Tm_comm_ind t9 k c0 s) (tshift_subst0_Tm_comm_ind t10 k c0 s))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t8 (HS TyVar k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t8 T9) => (f_equal2 TApp (tshift_subst0_Tm_comm_ind t8 k c0 s) eq_refl)
        | (Prod t9 t10) => (f_equal2 Prod (tshift_subst0_Tm_comm_ind t9 k c0 s) (tshift_subst0_Tm_comm_ind t10 k c0 s))
        | (Case t9 p11 t10) => (f_equal3 Case (tshift_subst0_Tm_comm_ind t9 k c0 s) eq_refl (eq_trans (f_equal2 tshiftTm (weakenCutoffTyVar_append c0 k (appendHvl H0 (bind p11))) (f_equal3 substTm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p11))) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) c0 s) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p11)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bind _ _))))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append c0 k (appendHvl H0 (bind p11)))) eq_refl)))))
      end.
    Fixpoint tshift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff TyVar)) (S1 : Ty) {struct s} :
    ((tshiftTm (weakenCutoffTyVar c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTm (weakenCutoffTyVar (CS c0) k) s))) :=
      match s return ((tshiftTm (weakenCutoffTyVar c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTm (weakenCutoffTyVar (CS c0) k) s))) with
        | (Var x6) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs (tshift_tsubst0_Ty_comm_ind T9 k c0 S1) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t8 (HS TmVar k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t9 t10) => (f_equal2 App (tshift_tsubst0_Tm_comm_ind t9 k c0 S1) (tshift_tsubst0_Tm_comm_ind t10 k c0 S1))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t8 (HS TyVar k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t8 T9) => (f_equal2 TApp (tshift_tsubst0_Tm_comm_ind t8 k c0 S1) (tshift_tsubst0_Ty_comm_ind T9 k c0 S1))
        | (Prod t9 t10) => (f_equal2 Prod (tshift_tsubst0_Tm_comm_ind t9 k c0 S1) (tshift_tsubst0_Tm_comm_ind t10 k c0 S1))
        | (Case t9 p11 t10) => (f_equal3 Case (tshift_tsubst0_Tm_comm_ind t9 k c0 S1) (tshift_tsubst0_Pat_comm_ind p11 k c0 S1) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bind _ _ _) (eq_refl H0)))) (weakenCutoffTyVar_append c0 k (appendHvl H0 (bind p11)))) (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p11))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) c0 S1) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p11)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bind _ _))))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append (CS c0) k (appendHvl H0 (bind p11)))) eq_refl)))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTy_tsubstTy0_comm (S2 : Ty) : (forall (c0 : (Cutoff TyVar)) (S1 : Ty) ,
      ((tshiftTy c0 (tsubstTy X0 S1 S2)) = (tsubstTy X0 (tshiftTy c0 S1) (tshiftTy (CS c0) S2)))) := (tshift_tsubst0_Ty_comm_ind S2 H0).
    Definition tshiftPat_tsubstPat0_comm (p11 : Pat) : (forall (c0 : (Cutoff TyVar)) (S1 : Ty) ,
      ((tshiftPat c0 (tsubstPat X0 S1 p11)) = (tsubstPat X0 (tshiftTy c0 S1) (tshiftPat (CS c0) p11)))) := (tshift_tsubst0_Pat_comm_ind p11 H0).
    Definition shiftTm_substTm0_comm (s0 : Tm) : (forall (c0 : (Cutoff TmVar)) (s : Tm) ,
      ((shiftTm c0 (substTm X0 s s0)) = (substTm X0 (shiftTm c0 s) (shiftTm (CS c0) s0)))) := (shift_subst0_Tm_comm_ind s0 H0).
    Definition shiftTm_tsubstTm0_comm (s : Tm) : (forall (c0 : (Cutoff TmVar)) (S1 : Ty) ,
      ((shiftTm c0 (tsubstTm X0 S1 s)) = (tsubstTm X0 S1 (shiftTm c0 s)))) := (shift_tsubst0_Tm_comm_ind s H0).
    Definition tshiftTm_substTm0_comm (s0 : Tm) : (forall (c0 : (Cutoff TyVar)) (s : Tm) ,
      ((tshiftTm c0 (substTm X0 s s0)) = (substTm X0 (tshiftTm c0 s) (tshiftTm c0 s0)))) := (tshift_subst0_Tm_comm_ind s0 H0).
    Definition tshiftTm_tsubstTm0_comm (s : Tm) : (forall (c0 : (Cutoff TyVar)) (S1 : Ty) ,
      ((tshiftTm c0 (tsubstTm X0 S1 s)) = (tsubstTm X0 (tshiftTy c0 S1) (tshiftTm (CS c0) s)))) := (tshift_tsubst0_Tm_comm_ind s H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d0 : (Trace TmVar)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((substIndex (weakenTrace (XS TmVar d0) k) s (shiftIndex (weakenCutoffTmVar C0 k) x6)) = (shiftTm (weakenCutoffTmVar C0 k) (substIndex (weakenTrace d0 k) s x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d0 : (Trace TmVar)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((substIndex (weakenTrace (XS TyVar d0) k) s x6) = (tshiftTm (weakenCutoffTyVar C0 k) (substIndex (weakenTrace d0 k) s x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d0 : (Trace TyVar)) (S1 : Ty) :
      (forall (k : Hvl) (X10 : (Index TyVar)) ,
        ((tsubstIndex (weakenTrace (XS TmVar d0) k) S1 X10) = (tsubstIndex (weakenTrace d0 k) S1 X10))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d0 : (Trace TyVar)) (S1 : Ty) :
      (forall (k : Hvl) (X10 : (Index TyVar)) ,
        ((tsubstIndex (weakenTrace (XS TyVar d0) k) S1 (tshiftIndex (weakenCutoffTyVar C0 k) X10)) = (tshiftTy (weakenCutoffTyVar C0 k) (tsubstIndex (weakenTrace d0 k) S1 X10)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint tsubst_tshift0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) {struct S2} :
    ((tsubstTy (weakenTrace (XS TyVar d0) k) S1 (tshiftTy (weakenCutoffTyVar C0 k) S2)) = (tshiftTy (weakenCutoffTyVar C0 k) (tsubstTy (weakenTrace d0 k) S1 S2))) :=
      match S2 return ((tsubstTy (weakenTrace (XS TyVar d0) k) S1 (tshiftTy (weakenCutoffTyVar C0 k) S2)) = (tshiftTy (weakenCutoffTyVar C0 k) (tsubstTy (weakenTrace d0 k) S1 S2))) with
        | (TVar X10) => (tsubstIndex_tshiftTy0_comm_ind d0 S1 k X10)
        | (TArr T10 T11) => (f_equal2 TArr (tsubst_tshift0_Ty_comm_ind T10 k d0 S1) (tsubst_tshift0_Ty_comm_ind T11 k d0 S1))
        | (TAll T9) => (f_equal TAll (eq_trans (f_equal3 tsubstTy (weakenTrace_append TyVar (XS TyVar d0) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T9 (HS TyVar k) d0 S1) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar d0 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TProd T10 T11) => (f_equal2 TProd (tsubst_tshift0_Ty_comm_ind T10 k d0 S1) (tsubst_tshift0_Ty_comm_ind T11 k d0 S1))
      end.
    Fixpoint tsubst_tshift0_Pat_comm_ind (p11 : Pat) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) {struct p11} :
    ((tsubstPat (weakenTrace (XS TyVar d0) k) S1 (tshiftPat (weakenCutoffTyVar C0 k) p11)) = (tshiftPat (weakenCutoffTyVar C0 k) (tsubstPat (weakenTrace d0 k) S1 p11))) :=
      match p11 return ((tsubstPat (weakenTrace (XS TyVar d0) k) S1 (tshiftPat (weakenCutoffTyVar C0 k) p11)) = (tshiftPat (weakenCutoffTyVar C0 k) (tsubstPat (weakenTrace d0 k) S1 p11))) with
        | (PVar T9) => (f_equal PVar (tsubst_tshift0_Ty_comm_ind T9 k d0 S1))
        | (PTVar) => eq_refl
        | (PProd p12 p13) => (f_equal2 PProd (tsubst_tshift0_Pat_comm_ind p12 k d0 S1) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bind _ _))) (weakenTrace_append TyVar (XS TyVar d0) k (appendHvl H0 (bind p12)))) eq_refl (f_equal2 tshiftPat (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p12))) eq_refl)) (eq_trans (tsubst_tshift0_Pat_comm_ind p13 (appendHvl k (appendHvl H0 (bind p12))) d0 S1) (f_equal2 tshiftPat (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p12)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0))))) (f_equal3 tsubstPat (eq_sym (weakenTrace_append TyVar d0 k (appendHvl H0 (bind p12)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace TmVar)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS TmVar d0) k) s (shiftTm (weakenCutoffTmVar C0 k) s0)) = (shiftTm (weakenCutoffTmVar C0 k) (substTm (weakenTrace d0 k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS TmVar d0) k) s (shiftTm (weakenCutoffTmVar C0 k) s0)) = (shiftTm (weakenCutoffTmVar C0 k) (substTm (weakenTrace d0 k) s s0))) with
        | (Var x6) => (substIndex_shiftTm0_comm_ind d0 s k x6)
        | (Abs T9 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar (XS TmVar d0) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t8 (HS TmVar k) d0 s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d0 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_shift0_Tm_comm_ind t9 k d0 s) (subst_shift0_Tm_comm_ind t10 k d0 s))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 substTm (weakenTrace_append TmVar (XS TmVar d0) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t8 (HS TyVar k) d0 s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d0 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T9) => (f_equal2 TApp (subst_shift0_Tm_comm_ind t8 k d0 s) eq_refl)
        | (Prod t9 t10) => (f_equal2 Prod (subst_shift0_Tm_comm_ind t9 k d0 s) (subst_shift0_Tm_comm_ind t10 k d0 s))
        | (Case t9 p11 t10) => (f_equal3 Case (subst_shift0_Tm_comm_ind t9 k d0 s) eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar (XS TmVar d0) k (appendHvl H0 (bind p11))) eq_refl (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p11))) eq_refl)) (eq_trans (subst_shift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) d0 s) (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p11)))) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d0 k (appendHvl H0 (bind p11)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace TmVar)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS TyVar d0) k) s (tshiftTm (weakenCutoffTyVar C0 k) s0)) = (tshiftTm (weakenCutoffTyVar C0 k) (substTm (weakenTrace d0 k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS TyVar d0) k) s (tshiftTm (weakenCutoffTyVar C0 k) s0)) = (tshiftTm (weakenCutoffTyVar C0 k) (substTm (weakenTrace d0 k) s s0))) with
        | (Var x6) => (substIndex_tshiftTm0_comm_ind d0 s k x6)
        | (Abs T9 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar (XS TyVar d0) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t8 (HS TmVar k) d0 s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d0 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_tshift0_Tm_comm_ind t9 k d0 s) (subst_tshift0_Tm_comm_ind t10 k d0 s))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 substTm (weakenTrace_append TmVar (XS TyVar d0) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t8 (HS TyVar k) d0 s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d0 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T9) => (f_equal2 TApp (subst_tshift0_Tm_comm_ind t8 k d0 s) eq_refl)
        | (Prod t9 t10) => (f_equal2 Prod (subst_tshift0_Tm_comm_ind t9 k d0 s) (subst_tshift0_Tm_comm_ind t10 k d0 s))
        | (Case t9 p11 t10) => (f_equal3 Case (subst_tshift0_Tm_comm_ind t9 k d0 s) eq_refl (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bind _ _))) (weakenTrace_append TmVar (XS TyVar d0) k (appendHvl H0 (bind p11)))) eq_refl (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p11))) eq_refl)) (eq_trans (subst_tshift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) d0 s) (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p11)))) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d0 k (appendHvl H0 (bind p11)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d0 k) S1 (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) :=
      match s return ((tsubstTm (weakenTrace d0 k) S1 (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) with
        | (Var x6) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t8 (HS TmVar k) d0 S1) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (tsubst_shift0_Tm_comm_ind t9 k d0 S1) (tsubst_shift0_Tm_comm_ind t10 k d0 S1))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t8 (HS TyVar k) d0 S1) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T9) => (f_equal2 TApp (tsubst_shift0_Tm_comm_ind t8 k d0 S1) eq_refl)
        | (Prod t9 t10) => (f_equal2 Prod (tsubst_shift0_Tm_comm_ind t9 k d0 S1) (tsubst_shift0_Tm_comm_ind t10 k d0 S1))
        | (Case t9 p11 t10) => (f_equal3 Case (tsubst_shift0_Tm_comm_ind t9 k d0 S1) eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (appendHvl H0 (bind p11))) eq_refl (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p11))) eq_refl)) (eq_trans (tsubst_shift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) d0 S1) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind p11)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0))))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (appendHvl H0 (bind p11)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS TyVar d0) k) S1 (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) :=
      match s return ((tsubstTm (weakenTrace (XS TyVar d0) k) S1 (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) with
        | (Var x6) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs (tsubst_tshift0_Ty_comm_ind T9 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar (XS TyVar d0) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t8 (HS TmVar k) d0 S1) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (tsubst_tshift0_Tm_comm_ind t9 k d0 S1) (tsubst_tshift0_Tm_comm_ind t10 k d0 S1))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar (XS TyVar d0) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t8 (HS TyVar k) d0 S1) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T9) => (f_equal2 TApp (tsubst_tshift0_Tm_comm_ind t8 k d0 S1) (tsubst_tshift0_Ty_comm_ind T9 k d0 S1))
        | (Prod t9 t10) => (f_equal2 Prod (tsubst_tshift0_Tm_comm_ind t9 k d0 S1) (tsubst_tshift0_Tm_comm_ind t10 k d0 S1))
        | (Case t9 p11 t10) => (f_equal3 Case (tsubst_tshift0_Tm_comm_ind t9 k d0 S1) (tsubst_tshift0_Pat_comm_ind p11 k d0 S1) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bind _ _))) (weakenTrace_append TyVar (XS TyVar d0) k (appendHvl H0 (bind p11)))) eq_refl (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p11))) eq_refl)) (eq_trans (tsubst_tshift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) d0 S1) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bind p11)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0))))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (appendHvl H0 (bind p11)))) eq_refl eq_refl)))))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S2 : Ty) : (forall (d0 : (Trace TyVar)) (S1 : Ty) ,
      ((tsubstTy (XS TyVar d0) S1 (tshiftTy C0 S2)) = (tshiftTy C0 (tsubstTy d0 S1 S2)))) := (tsubst_tshift0_Ty_comm_ind S2 H0).
    Definition tsubstPat_tshiftPat0_comm (p11 : Pat) : (forall (d0 : (Trace TyVar)) (S1 : Ty) ,
      ((tsubstPat (XS TyVar d0) S1 (tshiftPat C0 p11)) = (tshiftPat C0 (tsubstPat d0 S1 p11)))) := (tsubst_tshift0_Pat_comm_ind p11 H0).
    Definition substTm_shiftTm0_comm (s0 : Tm) : (forall (d0 : (Trace TmVar)) (s : Tm) ,
      ((substTm (XS TmVar d0) s (shiftTm C0 s0)) = (shiftTm C0 (substTm d0 s s0)))) := (subst_shift0_Tm_comm_ind s0 H0).
    Definition substTm_tshiftTm0_comm (s0 : Tm) : (forall (d0 : (Trace TmVar)) (s : Tm) ,
      ((substTm (XS TyVar d0) s (tshiftTm C0 s0)) = (tshiftTm C0 (substTm d0 s s0)))) := (subst_tshift0_Tm_comm_ind s0 H0).
    Definition tsubstTm_shiftTm0_comm (s : Tm) : (forall (d0 : (Trace TyVar)) (S1 : Ty) ,
      ((tsubstTm d0 S1 (shiftTm C0 s)) = (shiftTm C0 (tsubstTm d0 S1 s)))) := (tsubst_shift0_Tm_comm_ind s H0).
    Definition tsubstTm_tshiftTm0_comm (s : Tm) : (forall (d0 : (Trace TyVar)) (S1 : Ty) ,
      ((tsubstTm (XS TyVar d0) S1 (tshiftTm C0 s)) = (tshiftTm C0 (tsubstTm d0 S1 s)))) := (tsubst_tshift0_Tm_comm_ind s H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Fixpoint tsubst_TmVar_Ty_ind (S2 : Ty) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) {struct S2} :
    ((tsubstTy (weakenTrace (XS TmVar d0) k) S1 S2) = (tsubstTy (weakenTrace d0 k) S1 S2)) :=
      match S2 return ((tsubstTy (weakenTrace (XS TmVar d0) k) S1 S2) = (tsubstTy (weakenTrace d0 k) S1 S2)) with
        | (TVar X10) => (tsubstIndex_shiftTy0_comm_ind d0 S1 k X10)
        | (TArr T10 T11) => (f_equal2 TArr (tsubst_TmVar_Ty_ind T10 k d0 S1) (tsubst_TmVar_Ty_ind T11 k d0 S1))
        | (TAll T9) => (f_equal TAll (eq_trans (f_equal3 tsubstTy (weakenTrace_append TyVar (XS TmVar d0) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (tsubst_TmVar_Ty_ind T9 (HS TyVar k) d0 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar d0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TProd T10 T11) => (f_equal2 TProd (tsubst_TmVar_Ty_ind T10 k d0 S1) (tsubst_TmVar_Ty_ind T11 k d0 S1))
      end.
    Fixpoint tsubst_TmVar_Pat_ind (p11 : Pat) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) {struct p11} :
    ((tsubstPat (weakenTrace (XS TmVar d0) k) S1 p11) = (tsubstPat (weakenTrace d0 k) S1 p11)) :=
      match p11 return ((tsubstPat (weakenTrace (XS TmVar d0) k) S1 p11) = (tsubstPat (weakenTrace d0 k) S1 p11)) with
        | (PVar T9) => (f_equal PVar (tsubst_TmVar_Ty_ind T9 k d0 S1))
        | (PTVar) => eq_refl
        | (PProd p12 p13) => (f_equal2 PProd (tsubst_TmVar_Pat_ind p12 k d0 S1) (eq_trans (f_equal3 tsubstPat (weakenTrace_append TyVar (XS TmVar d0) k (appendHvl H0 (bind p12))) eq_refl eq_refl) (eq_trans (tsubst_TmVar_Pat_ind p13 (appendHvl k (appendHvl H0 (bind p12))) d0 S1) (f_equal3 tsubstPat (eq_sym (weakenTrace_append TyVar d0 k (appendHvl H0 (bind p12)))) eq_refl eq_refl))))
      end.
    Fixpoint tsubst_TmVar_Tm_ind (s : Tm) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS TmVar d0) k) S1 s) = (tsubstTm (weakenTrace d0 k) S1 s)) :=
      match s return ((tsubstTm (weakenTrace (XS TmVar d0) k) S1 s) = (tsubstTm (weakenTrace d0 k) S1 s)) with
        | (Var x6) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs (tsubst_TmVar_Ty_ind T9 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar (XS TmVar d0) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (tsubst_TmVar_Tm_ind t8 (HS TmVar k) d0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (App t9 t10) => (f_equal2 App (tsubst_TmVar_Tm_ind t9 k d0 S1) (tsubst_TmVar_Tm_ind t10 k d0 S1))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar (XS TmVar d0) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (tsubst_TmVar_Tm_ind t8 (HS TyVar k) d0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (TApp t8 T9) => (f_equal2 TApp (tsubst_TmVar_Tm_ind t8 k d0 S1) (tsubst_TmVar_Ty_ind T9 k d0 S1))
        | (Prod t9 t10) => (f_equal2 Prod (tsubst_TmVar_Tm_ind t9 k d0 S1) (tsubst_TmVar_Tm_ind t10 k d0 S1))
        | (Case t9 p11 t10) => (f_equal3 Case (tsubst_TmVar_Tm_ind t9 k d0 S1) (tsubst_TmVar_Pat_ind p11 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar (XS TmVar d0) k (appendHvl H0 (bind p11))) eq_refl eq_refl) (eq_trans (tsubst_TmVar_Tm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) d0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (appendHvl H0 (bind p11)))) eq_refl eq_refl))))
      end.
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_TmVar (S2 : Ty) : (forall (d0 : (Trace TyVar)) (S1 : Ty) ,
      ((tsubstTy (XS TmVar d0) S1 S2) = (tsubstTy d0 S1 S2))) := (tsubst_TmVar_Ty_ind S2 H0).
    Definition tsubstPat_TmVar (p11 : Pat) : (forall (d0 : (Trace TyVar)) (S1 : Ty) ,
      ((tsubstPat (XS TmVar d0) S1 p11) = (tsubstPat d0 S1 p11))) := (tsubst_TmVar_Pat_ind p11 H0).
    Definition tsubstTm_TmVar (s : Tm) : (forall (d0 : (Trace TyVar)) (S1 : Ty) ,
      ((tsubstTm (XS TmVar d0) S1 s) = (tsubstTm d0 S1 s))) := (tsubst_TmVar_Tm_ind s H0).
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite tsubstPat0_tshiftPat0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : interaction.
 Hint Rewrite tsubstPat0_tshiftPat0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : reflection.
 Hint Rewrite tsubstPat_tshiftPat0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : interaction.
 Hint Rewrite tsubstPat_tshiftPat0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : subst_shift0.
 Hint Rewrite tsubstPat_TmVar tsubstTm_TmVar tsubstTy_TmVar : interaction.
 Hint Rewrite tsubstPat_TmVar tsubstTm_TmVar tsubstTy_TmVar : subst_shift0.
 Hint Rewrite tshiftPat_tsubstPat0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : interaction.
 Hint Rewrite tshiftPat_tsubstPat0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d0 : (Trace TmVar)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((substTm (weakenTrace d0 k) s (substIndex (weakenTrace X0 k) s0 x6)) = (substTm (weakenTrace X0 k) (substTm d0 s s0) (substIndex (weakenTrace (XS TmVar d0) k) s x6)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d0 : (Trace TyVar)) (S1 : Ty) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((tsubstTm (weakenTrace d0 k) S1 (substIndex (weakenTrace X0 k) s x6)) = (substIndex (weakenTrace X0 k) (tsubstTm d0 S1 s) x6))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d0 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) :
      (forall (k : Hvl) (X10 : (Index TyVar)) ,
        ((tsubstTy (weakenTrace d0 k) S1 (tsubstIndex (weakenTrace X0 k) S2 X10)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstIndex (weakenTrace (XS TyVar d0) k) S1 X10)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d0 : (Trace TmVar)) (s : Tm) (S1 : Ty) :
      (forall (k : Hvl) (x6 : (Index TmVar)) ,
        ((substIndex (weakenTrace d0 k) s x6) = (tsubstTm (weakenTrace X0 k) S1 (substIndex (weakenTrace (XS TyVar d0) k) s x6)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint tsubst_tsubst0_Ty_comm_ind (S3 : Ty) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) {struct S3} :
    ((tsubstTy (weakenTrace d0 k) S1 (tsubstTy (weakenTrace X0 k) S2 S3)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstTy (weakenTrace (XS TyVar d0) k) S1 S3))) :=
      match S3 return ((tsubstTy (weakenTrace d0 k) S1 (tsubstTy (weakenTrace X0 k) S2 S3)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstTy (weakenTrace (XS TyVar d0) k) S1 S3))) with
        | (TVar X10) => (tsubstTy_tsubstIndex0_commright_ind d0 S1 S2 k X10)
        | (TArr T10 T11) => (f_equal2 TArr (tsubst_tsubst0_Ty_comm_ind T10 k d0 S1 S2) (tsubst_tsubst0_Ty_comm_ind T11 k d0 S1 S2))
        | (TAll T9) => (f_equal TAll (eq_trans (f_equal3 tsubstTy (weakenTrace_append TyVar d0 k (HS TyVar H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T9 (HS TyVar k) d0 S1 S2) (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar (XS TyVar d0) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TProd T10 T11) => (f_equal2 TProd (tsubst_tsubst0_Ty_comm_ind T10 k d0 S1 S2) (tsubst_tsubst0_Ty_comm_ind T11 k d0 S1 S2))
      end.
    Fixpoint tsubst_tsubst0_Pat_comm_ind (p11 : Pat) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) {struct p11} :
    ((tsubstPat (weakenTrace d0 k) S1 (tsubstPat (weakenTrace X0 k) S2 p11)) = (tsubstPat (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstPat (weakenTrace (XS TyVar d0) k) S1 p11))) :=
      match p11 return ((tsubstPat (weakenTrace d0 k) S1 (tsubstPat (weakenTrace X0 k) S2 p11)) = (tsubstPat (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstPat (weakenTrace (XS TyVar d0) k) S1 p11))) with
        | (PVar T9) => (f_equal PVar (tsubst_tsubst0_Ty_comm_ind T9 k d0 S1 S2))
        | (PTVar) => eq_refl
        | (PProd p12 p13) => (f_equal2 PProd (tsubst_tsubst0_Pat_comm_ind p12 k d0 S1 S2) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bind _ _ _) (eq_refl H0)))) (weakenTrace_append TyVar d0 k (appendHvl H0 (bind p12)))) eq_refl (f_equal3 tsubstPat (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p12))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Pat_comm_ind p13 (appendHvl k (appendHvl H0 (bind p12))) d0 S1 S2) (f_equal3 tsubstPat (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p12)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstPat (eq_sym (weakenTrace_append TyVar (XS TyVar d0) k (appendHvl H0 (bind p12)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d0 : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d0 k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d0 s s0) (substTm (weakenTrace (XS TmVar d0) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d0 k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d0 s s0) (substTm (weakenTrace (XS TmVar d0) k) s s1))) with
        | (Var x6) => (substTm_substIndex0_commright_ind d0 s s0 k x6)
        | (Abs T9 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar d0 k (HS TmVar H0)) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t8 (HS TmVar k) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TmVar d0) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_subst0_Tm_comm_ind t9 k d0 s s0) (subst_subst0_Tm_comm_ind t10 k d0 s s0))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 substTm (weakenTrace_append TmVar d0 k (HS TyVar H0)) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t8 (HS TyVar k) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TmVar d0) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T9) => (f_equal2 TApp (subst_subst0_Tm_comm_ind t8 k d0 s s0) eq_refl)
        | (Prod t9 t10) => (f_equal2 Prod (subst_subst0_Tm_comm_ind t9 k d0 s s0) (subst_subst0_Tm_comm_ind t10 k d0 s s0))
        | (Case t9 p11 t10) => (f_equal3 Case (subst_subst0_Tm_comm_ind t9 k d0 s s0) eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar d0 k (appendHvl H0 (bind p11))) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p11))) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p11)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TmVar d0) k (appendHvl H0 (bind p11)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace TmVar)) (s : Tm) (S1 : Ty) {struct s0} :
    ((substTm (weakenTrace d0 k) s (tsubstTm (weakenTrace X0 k) S1 s0)) = (tsubstTm (weakenTrace X0 k) S1 (substTm (weakenTrace (XS TyVar d0) k) s s0))) :=
      match s0 return ((substTm (weakenTrace d0 k) s (tsubstTm (weakenTrace X0 k) S1 s0)) = (tsubstTm (weakenTrace X0 k) S1 (substTm (weakenTrace (XS TyVar d0) k) s s0))) with
        | (Var x6) => (substTy_tsubstIndex0_commleft_ind d0 s S1 k x6)
        | (Abs T9 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar d0 k (HS TmVar H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t8 (HS TmVar k) d0 s S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TyVar d0) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (subst_tsubst0_Tm_comm_ind t9 k d0 s S1) (subst_tsubst0_Tm_comm_ind t10 k d0 s S1))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 substTm (weakenTrace_append TmVar d0 k (HS TyVar H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t8 (HS TyVar k) d0 s S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TyVar d0) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T9) => (f_equal2 TApp (subst_tsubst0_Tm_comm_ind t8 k d0 s S1) eq_refl)
        | (Prod t9 t10) => (f_equal2 Prod (subst_tsubst0_Tm_comm_ind t9 k d0 s S1) (subst_tsubst0_Tm_comm_ind t10 k d0 s S1))
        | (Case t9 p11 t10) => (f_equal3 Case (subst_tsubst0_Tm_comm_ind t9 k d0 s S1) eq_refl (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bind _ _ _) (eq_refl H0)))) (weakenTrace_append TmVar d0 k (appendHvl H0 (bind p11)))) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p11))) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) d0 s S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p11)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TyVar d0) k (appendHvl H0 (bind p11)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) (s : Tm) {struct s0} :
    ((tsubstTm (weakenTrace d0 k) S1 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d0 S1 s) (tsubstTm (weakenTrace d0 k) S1 s0))) :=
      match s0 return ((tsubstTm (weakenTrace d0 k) S1 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d0 S1 s) (tsubstTm (weakenTrace d0 k) S1 s0))) with
        | (Var x6) => (tsubstTm_substIndex0_commright_ind d0 S1 s k x6)
        | (Abs T9 t8) => (f_equal2 Abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (HS TmVar H0)) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t8 (HS TmVar k) d0 S1 s) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (tsubst_subst0_Tm_comm_ind t9 k d0 S1 s) (tsubst_subst0_Tm_comm_ind t10 k d0 S1 s))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (HS TyVar H0)) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t8 (HS TyVar k) d0 S1 s) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T9) => (f_equal2 TApp (tsubst_subst0_Tm_comm_ind t8 k d0 S1 s) eq_refl)
        | (Prod t9 t10) => (f_equal2 Prod (tsubst_subst0_Tm_comm_ind t9 k d0 S1 s) (tsubst_subst0_Tm_comm_ind t10 k d0 S1 s))
        | (Case t9 p11 t10) => (f_equal3 Case (tsubst_subst0_Tm_comm_ind t9 k d0 S1 s) eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (appendHvl H0 (bind p11))) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p11))) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) d0 S1 s) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind p11)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (appendHvl H0 (bind p11)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d0 k) S1 (tsubstTm (weakenTrace X0 k) S2 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstTm (weakenTrace (XS TyVar d0) k) S1 s))) :=
      match s return ((tsubstTm (weakenTrace d0 k) S1 (tsubstTm (weakenTrace X0 k) S2 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstTm (weakenTrace (XS TyVar d0) k) S1 s))) with
        | (Var x6) => eq_refl
        | (Abs T9 t8) => (f_equal2 Abs (tsubst_tsubst0_Ty_comm_ind T9 k d0 S1 S2) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (HS TmVar H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t8 (HS TmVar k) d0 S1 S2) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar (XS TyVar d0) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (App t9 t10) => (f_equal2 App (tsubst_tsubst0_Tm_comm_ind t9 k d0 S1 S2) (tsubst_tsubst0_Tm_comm_ind t10 k d0 S1 S2))
        | (TAbs t8) => (f_equal TAbs (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (HS TyVar H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t8 (HS TyVar k) d0 S1 S2) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar (XS TyVar d0) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (TApp t8 T9) => (f_equal2 TApp (tsubst_tsubst0_Tm_comm_ind t8 k d0 S1 S2) (tsubst_tsubst0_Ty_comm_ind T9 k d0 S1 S2))
        | (Prod t9 t10) => (f_equal2 Prod (tsubst_tsubst0_Tm_comm_ind t9 k d0 S1 S2) (tsubst_tsubst0_Tm_comm_ind t10 k d0 S1 S2))
        | (Case t9 p11 t10) => (f_equal3 Case (tsubst_tsubst0_Tm_comm_ind t9 k d0 S1 S2) (tsubst_tsubst0_Pat_comm_ind p11 k d0 S1 S2) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bind _ _ _) (eq_refl H0)))) (weakenTrace_append TyVar d0 k (appendHvl H0 (bind p11)))) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p11))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bind p11))) d0 S1 S2) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bind p11)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar (XS TyVar d0) k (appendHvl H0 (bind p11)))) eq_refl eq_refl)))))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S3 : Ty) : (forall (d0 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) ,
      ((tsubstTy d0 S1 (tsubstTy X0 S2 S3)) = (tsubstTy X0 (tsubstTy d0 S1 S2) (tsubstTy (XS TyVar d0) S1 S3)))) := (tsubst_tsubst0_Ty_comm_ind S3 H0).
    Definition tsubstPat_tsubstPat0_comm (p11 : Pat) : (forall (d0 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) ,
      ((tsubstPat d0 S1 (tsubstPat X0 S2 p11)) = (tsubstPat X0 (tsubstTy d0 S1 S2) (tsubstPat (XS TyVar d0) S1 p11)))) := (tsubst_tsubst0_Pat_comm_ind p11 H0).
    Definition substTm_substTm0_comm (s1 : Tm) : (forall (d0 : (Trace TmVar)) (s : Tm) (s0 : Tm) ,
      ((substTm d0 s (substTm X0 s0 s1)) = (substTm X0 (substTm d0 s s0) (substTm (XS TmVar d0) s s1)))) := (subst_subst0_Tm_comm_ind s1 H0).
    Definition substTm_tsubstTm0_comm (s0 : Tm) : (forall (d0 : (Trace TmVar)) (s : Tm) (S1 : Ty) ,
      ((substTm d0 s (tsubstTm X0 S1 s0)) = (tsubstTm X0 S1 (substTm (XS TyVar d0) s s0)))) := (subst_tsubst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_substTm0_comm (s0 : Tm) : (forall (d0 : (Trace TyVar)) (S1 : Ty) (s : Tm) ,
      ((tsubstTm d0 S1 (substTm X0 s s0)) = (substTm X0 (tsubstTm d0 S1 s) (tsubstTm d0 S1 s0)))) := (tsubst_subst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_tsubstTm0_comm (s : Tm) : (forall (d0 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) ,
      ((tsubstTm d0 S1 (tsubstTm X0 S2 s)) = (tsubstTm X0 (tsubstTy d0 S1 S2) (tsubstTm (XS TyVar d0) S1 s)))) := (tsubst_tsubst0_Tm_comm_ind s H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) ,
        ((weakenTy (tsubstTy d0 S1 S2) k) = (tsubstTy (weakenTrace d0 k) S1 (weakenTy S2 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenPat_tsubstPat  :
      (forall (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) (p11 : Pat) ,
        ((weakenPat (tsubstPat d0 S1 p11) k) = (tsubstPat (weakenTrace d0 k) S1 (weakenPat p11 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k : Hvl) (d0 : (Trace TmVar)) (s : Tm) (s0 : Tm) ,
        ((weakenTm (substTm d0 s s0) k) = (substTm (weakenTrace d0 k) s (weakenTm s0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) (s : Tm) ,
        ((weakenTm (tsubstTm d0 S1 s) k) = (tsubstTm (weakenTrace d0 k) S1 (weakenTm s k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite tsubstPat_tsubstPat0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : interaction.
 Hint Rewrite tsubstPat_tsubstPat0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : subst_subst0.
 Hint Rewrite weakenPat_tshiftPat weakenTm_shiftTm weakenTm_tshiftTm weakenTy_tshiftTy : weaken_shift.
 Hint Rewrite weakenPat_tsubstPat weakenTm_substTm weakenTm_tsubstTm weakenTy_tsubstTy : weaken_subst.
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
        (X10 : (Index TyVar))
        (wfi : (wfindex k X10)) :
        (wfTy k (TVar X10))
    | wfTy_TArr {T9 : Ty}
        (wf : (wfTy k T9)) {T10 : Ty}
        (wf0 : (wfTy k T10)) :
        (wfTy k (TArr T9 T10))
    | wfTy_TAll {T11 : Ty}
        (wf : (wfTy (HS TyVar k) T11)) :
        (wfTy k (TAll T11))
    | wfTy_TProd {T12 : Ty}
        (wf : (wfTy k T12)) {T13 : Ty}
        (wf0 : (wfTy k T13)) :
        (wfTy k (TProd T12 T13)).
  Inductive wfPat (k : Hvl) : Pat -> Prop :=
    | wfPat_PVar {T9 : Ty}
        (wf : (wfTy k T9)) :
        (wfPat k (PVar T9))
    | wfPat_PTVar :
        (wfPat k (PTVar))
    | wfPat_PProd {p11 : Pat}
        (wf : (wfPat k p11)) {p12 : Pat}
        (wf0 : (wfPat (appendHvl k (appendHvl H0 (bind p11))) p12))
        : (wfPat k (PProd p11 p12)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_Var
        (x6 : (Index TmVar))
        (wfi : (wfindex k x6)) :
        (wfTm k (Var x6))
    | wfTm_Abs {T9 : Ty}
        (wf : (wfTy k T9)) {t8 : Tm}
        (wf0 : (wfTm (HS TmVar k) t8)) :
        (wfTm k (Abs T9 t8))
    | wfTm_App {t9 : Tm}
        (wf : (wfTm k t9)) {t10 : Tm}
        (wf0 : (wfTm k t10)) :
        (wfTm k (App t9 t10))
    | wfTm_TAbs {t11 : Tm}
        (wf : (wfTm (HS TyVar k) t11)) :
        (wfTm k (TAbs t11))
    | wfTm_TApp {t12 : Tm}
        (wf : (wfTm k t12)) {T10 : Ty}
        (wf0 : (wfTy k T10)) :
        (wfTm k (TApp t12 T10))
    | wfTm_Prod {t13 : Tm}
        (wf : (wfTm k t13)) {t14 : Tm}
        (wf0 : (wfTm k t14)) :
        (wfTm k (Prod t13 t14))
    | wfTm_Case {t15 : Tm}
        (wf : (wfTm k t15)) {p11 : Pat}
        (wf0 : (wfPat k p11)) {t16 : Tm}
        (wf1 : (wfTm (appendHvl k (appendHvl H0 (bind p11))) t16))
        : (wfTm k (Case t15 p11 t16)).
  Definition inversion_wfTy_TVar_1 (k : Hvl) (X : (Index TyVar)) (H24 : (wfTy k (TVar X))) : (wfindex k X) := match H24 in (wfTy _ S1) return match S1 return Prop with
    | (TVar X) => (wfindex k X)
    | _ => True
  end with
    | (wfTy_TVar X H1) => H1
    | _ => I
  end.
  Definition inversion_wfTy_TArr_0 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H25 : (wfTy k0 (TArr T1 T2))) : (wfTy k0 T1) := match H25 in (wfTy _ S2) return match S2 return Prop with
    | (TArr T1 T2) => (wfTy k0 T1)
    | _ => True
  end with
    | (wfTy_TArr T1 H2 T2 H3) => H2
    | _ => I
  end.
  Definition inversion_wfTy_TArr_1 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H25 : (wfTy k0 (TArr T1 T2))) : (wfTy k0 T2) := match H25 in (wfTy _ S2) return match S2 return Prop with
    | (TArr T1 T2) => (wfTy k0 T2)
    | _ => True
  end with
    | (wfTy_TArr T1 H2 T2 H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_TAll_1 (k1 : Hvl) (T : Ty) (H26 : (wfTy k1 (TAll T))) : (wfTy (HS TyVar k1) T) := match H26 in (wfTy _ S3) return match S3 return Prop with
    | (TAll T) => (wfTy (HS TyVar k1) T)
    | _ => True
  end with
    | (wfTy_TAll T H4) => H4
    | _ => I
  end.
  Definition inversion_wfTy_TProd_0 (k2 : Hvl) (T1 : Ty) (T2 : Ty) (H27 : (wfTy k2 (TProd T1 T2))) : (wfTy k2 T1) := match H27 in (wfTy _ S4) return match S4 return Prop with
    | (TProd T1 T2) => (wfTy k2 T1)
    | _ => True
  end with
    | (wfTy_TProd T1 H5 T2 H6) => H5
    | _ => I
  end.
  Definition inversion_wfTy_TProd_1 (k2 : Hvl) (T1 : Ty) (T2 : Ty) (H27 : (wfTy k2 (TProd T1 T2))) : (wfTy k2 T2) := match H27 in (wfTy _ S4) return match S4 return Prop with
    | (TProd T1 T2) => (wfTy k2 T2)
    | _ => True
  end with
    | (wfTy_TProd T1 H5 T2 H6) => H6
    | _ => I
  end.
  Definition inversion_wfPat_PVar_1 (k3 : Hvl) (T : Ty) (H28 : (wfPat k3 (PVar T))) : (wfTy k3 T) := match H28 in (wfPat _ p11) return match p11 return Prop with
    | (PVar T) => (wfTy k3 T)
    | _ => True
  end with
    | (wfPat_PVar T H7) => H7
    | _ => I
  end.
  Definition inversion_wfPat_PProd_0 (k5 : Hvl) (p1 : Pat) (p2 : Pat) (H30 : (wfPat k5 (PProd p1 p2))) : (wfPat k5 p1) := match H30 in (wfPat _ p13) return match p13 return Prop with
    | (PProd p1 p2) => (wfPat k5 p1)
    | _ => True
  end with
    | (wfPat_PProd p1 H8 p2 H9) => H8
    | _ => I
  end.
  Definition inversion_wfPat_PProd_1 (k5 : Hvl) (p1 : Pat) (p2 : Pat) (H30 : (wfPat k5 (PProd p1 p2))) : (wfPat (appendHvl k5 (appendHvl H0 (bind p1))) p2) := match H30 in (wfPat _ p13) return match p13 return Prop with
    | (PProd p1 p2) => (wfPat (appendHvl k5 (appendHvl H0 (bind p1))) p2)
    | _ => True
  end with
    | (wfPat_PProd p1 H8 p2 H9) => H9
    | _ => I
  end.
  Definition inversion_wfTm_Var_1 (k6 : Hvl) (x : (Index TmVar)) (H31 : (wfTm k6 (Var x))) : (wfindex k6 x) := match H31 in (wfTm _ s) return match s return Prop with
    | (Var x) => (wfindex k6 x)
    | _ => True
  end with
    | (wfTm_Var x H10) => H10
    | _ => I
  end.
  Definition inversion_wfTm_Abs_1 (k7 : Hvl) (T : Ty) (t : Tm) (H32 : (wfTm k7 (Abs T t))) : (wfTy k7 T) := match H32 in (wfTm _ s0) return match s0 return Prop with
    | (Abs T t) => (wfTy k7 T)
    | _ => True
  end with
    | (wfTm_Abs T H11 t H12) => H11
    | _ => I
  end.
  Definition inversion_wfTm_Abs_2 (k7 : Hvl) (T : Ty) (t : Tm) (H32 : (wfTm k7 (Abs T t))) : (wfTm (HS TmVar k7) t) := match H32 in (wfTm _ s0) return match s0 return Prop with
    | (Abs T t) => (wfTm (HS TmVar k7) t)
    | _ => True
  end with
    | (wfTm_Abs T H11 t H12) => H12
    | _ => I
  end.
  Definition inversion_wfTm_App_0 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H33 : (wfTm k8 (App t1 t2))) : (wfTm k8 t1) := match H33 in (wfTm _ s1) return match s1 return Prop with
    | (App t1 t2) => (wfTm k8 t1)
    | _ => True
  end with
    | (wfTm_App t1 H13 t2 H14) => H13
    | _ => I
  end.
  Definition inversion_wfTm_App_1 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H33 : (wfTm k8 (App t1 t2))) : (wfTm k8 t2) := match H33 in (wfTm _ s1) return match s1 return Prop with
    | (App t1 t2) => (wfTm k8 t2)
    | _ => True
  end with
    | (wfTm_App t1 H13 t2 H14) => H14
    | _ => I
  end.
  Definition inversion_wfTm_TAbs_1 (k9 : Hvl) (t : Tm) (H34 : (wfTm k9 (TAbs t))) : (wfTm (HS TyVar k9) t) := match H34 in (wfTm _ s2) return match s2 return Prop with
    | (TAbs t) => (wfTm (HS TyVar k9) t)
    | _ => True
  end with
    | (wfTm_TAbs t H15) => H15
    | _ => I
  end.
  Definition inversion_wfTm_TApp_0 (k10 : Hvl) (t : Tm) (T : Ty) (H35 : (wfTm k10 (TApp t T))) : (wfTm k10 t) := match H35 in (wfTm _ s3) return match s3 return Prop with
    | (TApp t T) => (wfTm k10 t)
    | _ => True
  end with
    | (wfTm_TApp t H16 T H17) => H16
    | _ => I
  end.
  Definition inversion_wfTm_TApp_1 (k10 : Hvl) (t : Tm) (T : Ty) (H35 : (wfTm k10 (TApp t T))) : (wfTy k10 T) := match H35 in (wfTm _ s3) return match s3 return Prop with
    | (TApp t T) => (wfTy k10 T)
    | _ => True
  end with
    | (wfTm_TApp t H16 T H17) => H17
    | _ => I
  end.
  Definition inversion_wfTm_Prod_0 (k11 : Hvl) (t1 : Tm) (t2 : Tm) (H36 : (wfTm k11 (Prod t1 t2))) : (wfTm k11 t1) := match H36 in (wfTm _ s4) return match s4 return Prop with
    | (Prod t1 t2) => (wfTm k11 t1)
    | _ => True
  end with
    | (wfTm_Prod t1 H18 t2 H19) => H18
    | _ => I
  end.
  Definition inversion_wfTm_Prod_1 (k11 : Hvl) (t1 : Tm) (t2 : Tm) (H36 : (wfTm k11 (Prod t1 t2))) : (wfTm k11 t2) := match H36 in (wfTm _ s4) return match s4 return Prop with
    | (Prod t1 t2) => (wfTm k11 t2)
    | _ => True
  end with
    | (wfTm_Prod t1 H18 t2 H19) => H19
    | _ => I
  end.
  Definition inversion_wfTm_Case_0 (k12 : Hvl) (t1 : Tm) (p : Pat) (t2 : Tm) (H37 : (wfTm k12 (Case t1 p t2))) : (wfTm k12 t1) := match H37 in (wfTm _ s5) return match s5 return Prop with
    | (Case t1 p t2) => (wfTm k12 t1)
    | _ => True
  end with
    | (wfTm_Case t1 H20 p H21 t2 H22) => H20
    | _ => I
  end.
  Definition inversion_wfTm_Case_1 (k12 : Hvl) (t1 : Tm) (p : Pat) (t2 : Tm) (H37 : (wfTm k12 (Case t1 p t2))) : (wfPat k12 p) := match H37 in (wfTm _ s5) return match s5 return Prop with
    | (Case t1 p t2) => (wfPat k12 p)
    | _ => True
  end with
    | (wfTm_Case t1 H20 p H21 t2 H22) => H21
    | _ => I
  end.
  Definition inversion_wfTm_Case_2 (k12 : Hvl) (t1 : Tm) (p : Pat) (t2 : Tm) (H37 : (wfTm k12 (Case t1 p t2))) : (wfTm (appendHvl k12 (appendHvl H0 (bind p))) t2) := match H37 in (wfTm _ s5) return match s5 return Prop with
    | (Case t1 p t2) => (wfTm (appendHvl k12 (appendHvl H0 (bind p))) t2)
    | _ => True
  end with
    | (wfTm_Case t1 H20 p H21 t2 H22) => H22
    | _ => I
  end.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfPat := Induction for wfPat Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_TmVar : (forall (c0 : (Cutoff TmVar)) (k13 : Hvl) (k14 : Hvl) ,
    Prop) :=
    | shifthvl_TmVar_here
        (k13 : Hvl) :
        (shifthvl_TmVar C0 k13 (HS TmVar k13))
    | shifthvl_TmVar_there_TmVar
        (c0 : (Cutoff TmVar))
        (k13 : Hvl) (k14 : Hvl) :
        (shifthvl_TmVar c0 k13 k14) -> (shifthvl_TmVar (CS c0) (HS TmVar k13) (HS TmVar k14))
    | shifthvl_TmVar_there_TyVar
        (c0 : (Cutoff TmVar))
        (k13 : Hvl) (k14 : Hvl) :
        (shifthvl_TmVar c0 k13 k14) -> (shifthvl_TmVar c0 (HS TyVar k13) (HS TyVar k14)).
  Inductive shifthvl_TyVar : (forall (c0 : (Cutoff TyVar)) (k13 : Hvl) (k14 : Hvl) ,
    Prop) :=
    | shifthvl_TyVar_here
        (k13 : Hvl) :
        (shifthvl_TyVar C0 k13 (HS TyVar k13))
    | shifthvl_TyVar_there_TmVar
        (c0 : (Cutoff TyVar))
        (k13 : Hvl) (k14 : Hvl) :
        (shifthvl_TyVar c0 k13 k14) -> (shifthvl_TyVar c0 (HS TmVar k13) (HS TmVar k14))
    | shifthvl_TyVar_there_TyVar
        (c0 : (Cutoff TyVar))
        (k13 : Hvl) (k14 : Hvl) :
        (shifthvl_TyVar c0 k13 k14) -> (shifthvl_TyVar (CS c0) (HS TyVar k13) (HS TyVar k14)).
  Lemma weaken_shifthvl_TmVar  :
    (forall (k13 : Hvl) {c0 : (Cutoff TmVar)} {k14 : Hvl} {k15 : Hvl} ,
      (shifthvl_TmVar c0 k14 k15) -> (shifthvl_TmVar (weakenCutoffTmVar c0 k13) (appendHvl k14 k13) (appendHvl k15 k13))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_TyVar  :
    (forall (k13 : Hvl) {c0 : (Cutoff TyVar)} {k14 : Hvl} {k15 : Hvl} ,
      (shifthvl_TyVar c0 k14 k15) -> (shifthvl_TyVar (weakenCutoffTyVar c0 k13) (appendHvl k14 k13) (appendHvl k15 k13))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_TmVar  :
    (forall (c0 : (Cutoff TmVar)) (k13 : Hvl) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) (x6 : (Index TmVar)) ,
      (wfindex k13 x6) -> (wfindex k14 (shiftIndex c0 x6))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_TyVar  :
    (forall (c0 : (Cutoff TmVar)) (k13 : Hvl) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) (X10 : (Index TyVar)) ,
      (wfindex k13 X10) -> (wfindex k14 X10)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_TmVar  :
    (forall (c0 : (Cutoff TyVar)) (k13 : Hvl) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) (x6 : (Index TmVar)) ,
      (wfindex k13 x6) -> (wfindex k14 x6)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_TyVar  :
    (forall (c0 : (Cutoff TyVar)) (k13 : Hvl) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) (X10 : (Index TyVar)) ,
      (wfindex k13 X10) -> (wfindex k14 (tshiftIndex c0 X10))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k13 : Hvl) ,
    (forall (S5 : Ty) (wf : (wfTy k13 S5)) ,
      (forall (c0 : (Cutoff TmVar)) (k14 : Hvl) ,
        (shifthvl_TmVar c0 k13 k14) -> (wfTy k14 S5)))) := (ind_wfTy (fun (k13 : Hvl) (S5 : Ty) (wf : (wfTy k13 S5)) =>
    (forall (c0 : (Cutoff TmVar)) (k14 : Hvl) ,
      (shifthvl_TmVar c0 k13 k14) -> (wfTy k14 S5))) (fun (k13 : Hvl) (X10 : (Index TyVar)) (wfi : (wfindex k13 X10)) (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTy_TVar k14 _ (shift_wfindex_TyVar c0 k13 k14 ins X10 wfi))) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k13 T2)) IHT2 (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTy_TArr k14 (IHT1 c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHT2 c0 k14 (weaken_shifthvl_TmVar H0 ins)))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy (HS TyVar k13) T)) IHT (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTy_TAll k14 (IHT c0 (HS TyVar k14) (weaken_shifthvl_TmVar (HS TyVar H0) ins)))) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k13 T2)) IHT2 (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTy_TProd k14 (IHT1 c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHT2 c0 k14 (weaken_shifthvl_TmVar H0 ins))))).
  Definition tshift_wfTy : (forall (k13 : Hvl) ,
    (forall (S5 : Ty) (wf : (wfTy k13 S5)) ,
      (forall (c0 : (Cutoff TyVar)) (k14 : Hvl) ,
        (shifthvl_TyVar c0 k13 k14) -> (wfTy k14 (tshiftTy c0 S5))))) := (ind_wfTy (fun (k13 : Hvl) (S5 : Ty) (wf : (wfTy k13 S5)) =>
    (forall (c0 : (Cutoff TyVar)) (k14 : Hvl) ,
      (shifthvl_TyVar c0 k13 k14) -> (wfTy k14 (tshiftTy c0 S5)))) (fun (k13 : Hvl) (X10 : (Index TyVar)) (wfi : (wfindex k13 X10)) (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTy_TVar k14 _ (tshift_wfindex_TyVar c0 k13 k14 ins X10 wfi))) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k13 T2)) IHT2 (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTy_TArr k14 (IHT1 c0 k14 (weaken_shifthvl_TyVar H0 ins)) (IHT2 c0 k14 (weaken_shifthvl_TyVar H0 ins)))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy (HS TyVar k13) T)) IHT (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTy_TAll k14 (IHT (CS c0) (HS TyVar k14) (weaken_shifthvl_TyVar (HS TyVar H0) ins)))) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k13 T2)) IHT2 (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTy_TProd k14 (IHT1 c0 k14 (weaken_shifthvl_TyVar H0 ins)) (IHT2 c0 k14 (weaken_shifthvl_TyVar H0 ins))))).
  Definition shift_wfPat : (forall (k13 : Hvl) ,
    (forall (p14 : Pat) (wf : (wfPat k13 p14)) ,
      (forall (c0 : (Cutoff TmVar)) (k14 : Hvl) ,
        (shifthvl_TmVar c0 k13 k14) -> (wfPat k14 p14)))) := (ind_wfPat (fun (k13 : Hvl) (p14 : Pat) (wf : (wfPat k13 p14)) =>
    (forall (c0 : (Cutoff TmVar)) (k14 : Hvl) ,
      (shifthvl_TmVar c0 k13 k14) -> (wfPat k14 p14))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfPat_PVar k14 (shift_wfTy k13 T wf c0 k14 (weaken_shifthvl_TmVar H0 ins)))) (fun (k13 : Hvl) (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfPat_PTVar k14)) (fun (k13 : Hvl) (p1 : Pat) (wf : (wfPat k13 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k13 (appendHvl H0 (bind p1))) p2)) IHp2 (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfPat_PProd k14 (IHp1 c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHp2 (weakenCutoffTmVar c0 (appendHvl H0 (bind p1))) (appendHvl k14 (appendHvl H0 (bind p1))) (weaken_shifthvl_TmVar (appendHvl H0 (bind p1)) ins))))).
  Definition tshift_wfPat : (forall (k13 : Hvl) ,
    (forall (p14 : Pat) (wf : (wfPat k13 p14)) ,
      (forall (c0 : (Cutoff TyVar)) (k14 : Hvl) ,
        (shifthvl_TyVar c0 k13 k14) -> (wfPat k14 (tshiftPat c0 p14))))) := (ind_wfPat (fun (k13 : Hvl) (p14 : Pat) (wf : (wfPat k13 p14)) =>
    (forall (c0 : (Cutoff TyVar)) (k14 : Hvl) ,
      (shifthvl_TyVar c0 k13 k14) -> (wfPat k14 (tshiftPat c0 p14)))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfPat_PVar k14 (tshift_wfTy k13 T wf c0 k14 (weaken_shifthvl_TyVar H0 ins)))) (fun (k13 : Hvl) (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfPat_PTVar k14)) (fun (k13 : Hvl) (p1 : Pat) (wf : (wfPat k13 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k13 (appendHvl H0 (bind p1))) p2)) IHp2 (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfPat_PProd k14 (IHp1 c0 k14 (weaken_shifthvl_TyVar H0 ins)) (eq_ind2 wfPat (f_equal2 appendHvl (eq_refl k14) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bind _ _)))) eq_refl (IHp2 (weakenCutoffTyVar c0 (appendHvl H0 (bind p1))) (appendHvl k14 (appendHvl H0 (bind p1))) (weaken_shifthvl_TyVar (appendHvl H0 (bind p1)) ins)))))).
  Definition shift_wfTm : (forall (k13 : Hvl) ,
    (forall (s6 : Tm) (wf : (wfTm k13 s6)) ,
      (forall (c0 : (Cutoff TmVar)) (k14 : Hvl) ,
        (shifthvl_TmVar c0 k13 k14) -> (wfTm k14 (shiftTm c0 s6))))) := (ind_wfTm (fun (k13 : Hvl) (s6 : Tm) (wf : (wfTm k13 s6)) =>
    (forall (c0 : (Cutoff TmVar)) (k14 : Hvl) ,
      (shifthvl_TmVar c0 k13 k14) -> (wfTm k14 (shiftTm c0 s6)))) (fun (k13 : Hvl) (x6 : (Index TmVar)) (wfi : (wfindex k13 x6)) (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTm_Var k14 _ (shift_wfindex_TmVar c0 k13 k14 ins x6 wfi))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (t : Tm) (wf0 : (wfTm (HS TmVar k13) t)) IHt (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTm_Abs k14 (shift_wfTy k13 T wf c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHt (CS c0) (HS TmVar k14) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k13 : Hvl) (t1 : Tm) (wf : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k13 t2)) IHt2 (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTm_App k14 (IHt1 c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHt2 c0 k14 (weaken_shifthvl_TmVar H0 ins)))) (fun (k13 : Hvl) (t : Tm) (wf : (wfTm (HS TyVar k13) t)) IHt (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTm_TAbs k14 (IHt c0 (HS TyVar k14) (weaken_shifthvl_TmVar (HS TyVar H0) ins)))) (fun (k13 : Hvl) (t : Tm) (wf : (wfTm k13 t)) IHt (T : Ty) (wf0 : (wfTy k13 T)) (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTm_TApp k14 (IHt c0 k14 (weaken_shifthvl_TmVar H0 ins)) (shift_wfTy k13 T wf0 c0 k14 (weaken_shifthvl_TmVar H0 ins)))) (fun (k13 : Hvl) (t1 : Tm) (wf : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k13 t2)) IHt2 (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTm_Prod k14 (IHt1 c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHt2 c0 k14 (weaken_shifthvl_TmVar H0 ins)))) (fun (k13 : Hvl) (t1 : Tm) (wf : (wfTm k13 t1)) IHt1 (p : Pat) (wf0 : (wfPat k13 p)) (t2 : Tm) (wf1 : (wfTm (appendHvl k13 (appendHvl H0 (bind p))) t2)) IHt2 (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTm_Case k14 (IHt1 c0 k14 (weaken_shifthvl_TmVar H0 ins)) (shift_wfPat k13 p wf0 c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHt2 (weakenCutoffTmVar c0 (appendHvl H0 (bind p))) (appendHvl k14 (appendHvl H0 (bind p))) (weaken_shifthvl_TmVar (appendHvl H0 (bind p)) ins))))).
  Definition tshift_wfTm : (forall (k13 : Hvl) ,
    (forall (s6 : Tm) (wf : (wfTm k13 s6)) ,
      (forall (c0 : (Cutoff TyVar)) (k14 : Hvl) ,
        (shifthvl_TyVar c0 k13 k14) -> (wfTm k14 (tshiftTm c0 s6))))) := (ind_wfTm (fun (k13 : Hvl) (s6 : Tm) (wf : (wfTm k13 s6)) =>
    (forall (c0 : (Cutoff TyVar)) (k14 : Hvl) ,
      (shifthvl_TyVar c0 k13 k14) -> (wfTm k14 (tshiftTm c0 s6)))) (fun (k13 : Hvl) (x6 : (Index TmVar)) (wfi : (wfindex k13 x6)) (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTm_Var k14 _ (tshift_wfindex_TmVar c0 k13 k14 ins x6 wfi))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (t : Tm) (wf0 : (wfTm (HS TmVar k13) t)) IHt (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTm_Abs k14 (tshift_wfTy k13 T wf c0 k14 (weaken_shifthvl_TyVar H0 ins)) (IHt c0 (HS TmVar k14) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k13 : Hvl) (t1 : Tm) (wf : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k13 t2)) IHt2 (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTm_App k14 (IHt1 c0 k14 (weaken_shifthvl_TyVar H0 ins)) (IHt2 c0 k14 (weaken_shifthvl_TyVar H0 ins)))) (fun (k13 : Hvl) (t : Tm) (wf : (wfTm (HS TyVar k13) t)) IHt (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTm_TAbs k14 (IHt (CS c0) (HS TyVar k14) (weaken_shifthvl_TyVar (HS TyVar H0) ins)))) (fun (k13 : Hvl) (t : Tm) (wf : (wfTm k13 t)) IHt (T : Ty) (wf0 : (wfTy k13 T)) (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTm_TApp k14 (IHt c0 k14 (weaken_shifthvl_TyVar H0 ins)) (tshift_wfTy k13 T wf0 c0 k14 (weaken_shifthvl_TyVar H0 ins)))) (fun (k13 : Hvl) (t1 : Tm) (wf : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k13 t2)) IHt2 (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTm_Prod k14 (IHt1 c0 k14 (weaken_shifthvl_TyVar H0 ins)) (IHt2 c0 k14 (weaken_shifthvl_TyVar H0 ins)))) (fun (k13 : Hvl) (t1 : Tm) (wf : (wfTm k13 t1)) IHt1 (p : Pat) (wf0 : (wfPat k13 p)) (t2 : Tm) (wf1 : (wfTm (appendHvl k13 (appendHvl H0 (bind p))) t2)) IHt2 (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTm_Case k14 (IHt1 c0 k14 (weaken_shifthvl_TyVar H0 ins)) (tshift_wfPat k13 p wf0 c0 k14 (weaken_shifthvl_TyVar H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k14) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bind _ _)))) eq_refl (IHt2 (weakenCutoffTyVar c0 (appendHvl H0 (bind p))) (appendHvl k14 (appendHvl H0 (bind p))) (weaken_shifthvl_TyVar (appendHvl H0 (bind p)) ins)))))).
  Fixpoint weaken_wfTy (k13 : Hvl) {struct k13} :
  (forall (k14 : Hvl) (S5 : Ty) (wf : (wfTy k14 S5)) ,
    (wfTy (appendHvl k14 k13) (weakenTy S5 k13))) :=
    match k13 return (forall (k14 : Hvl) (S5 : Ty) (wf : (wfTy k14 S5)) ,
      (wfTy (appendHvl k14 k13) (weakenTy S5 k13))) with
      | (H0) => (fun (k14 : Hvl) (S5 : Ty) (wf : (wfTy k14 S5)) =>
        wf)
      | (HS TmVar k13) => (fun (k14 : Hvl) (S5 : Ty) (wf : (wfTy k14 S5)) =>
        (shift_wfTy (appendHvl k14 k13) (weakenTy S5 k13) (weaken_wfTy k13 k14 S5 wf) C0 (HS TmVar (appendHvl k14 k13)) (shifthvl_TmVar_here (appendHvl k14 k13))))
      | (HS TyVar k13) => (fun (k14 : Hvl) (S5 : Ty) (wf : (wfTy k14 S5)) =>
        (tshift_wfTy (appendHvl k14 k13) (weakenTy S5 k13) (weaken_wfTy k13 k14 S5 wf) C0 (HS TyVar (appendHvl k14 k13)) (shifthvl_TyVar_here (appendHvl k14 k13))))
    end.
  Fixpoint weaken_wfPat (k13 : Hvl) {struct k13} :
  (forall (k14 : Hvl) (p14 : Pat) (wf : (wfPat k14 p14)) ,
    (wfPat (appendHvl k14 k13) (weakenPat p14 k13))) :=
    match k13 return (forall (k14 : Hvl) (p14 : Pat) (wf : (wfPat k14 p14)) ,
      (wfPat (appendHvl k14 k13) (weakenPat p14 k13))) with
      | (H0) => (fun (k14 : Hvl) (p14 : Pat) (wf : (wfPat k14 p14)) =>
        wf)
      | (HS TmVar k13) => (fun (k14 : Hvl) (p14 : Pat) (wf : (wfPat k14 p14)) =>
        (shift_wfPat (appendHvl k14 k13) (weakenPat p14 k13) (weaken_wfPat k13 k14 p14 wf) C0 (HS TmVar (appendHvl k14 k13)) (shifthvl_TmVar_here (appendHvl k14 k13))))
      | (HS TyVar k13) => (fun (k14 : Hvl) (p14 : Pat) (wf : (wfPat k14 p14)) =>
        (tshift_wfPat (appendHvl k14 k13) (weakenPat p14 k13) (weaken_wfPat k13 k14 p14 wf) C0 (HS TyVar (appendHvl k14 k13)) (shifthvl_TyVar_here (appendHvl k14 k13))))
    end.
  Fixpoint weaken_wfTm (k13 : Hvl) {struct k13} :
  (forall (k14 : Hvl) (s6 : Tm) (wf : (wfTm k14 s6)) ,
    (wfTm (appendHvl k14 k13) (weakenTm s6 k13))) :=
    match k13 return (forall (k14 : Hvl) (s6 : Tm) (wf : (wfTm k14 s6)) ,
      (wfTm (appendHvl k14 k13) (weakenTm s6 k13))) with
      | (H0) => (fun (k14 : Hvl) (s6 : Tm) (wf : (wfTm k14 s6)) =>
        wf)
      | (HS TmVar k13) => (fun (k14 : Hvl) (s6 : Tm) (wf : (wfTm k14 s6)) =>
        (shift_wfTm (appendHvl k14 k13) (weakenTm s6 k13) (weaken_wfTm k13 k14 s6 wf) C0 (HS TmVar (appendHvl k14 k13)) (shifthvl_TmVar_here (appendHvl k14 k13))))
      | (HS TyVar k13) => (fun (k14 : Hvl) (s6 : Tm) (wf : (wfTm k14 s6)) =>
        (tshift_wfTm (appendHvl k14 k13) (weakenTm s6 k13) (weaken_wfTm k13 k14 s6 wf) C0 (HS TyVar (appendHvl k14 k13)) (shifthvl_TyVar_here (appendHvl k14 k13))))
    end.
End ShiftWellFormed.
Lemma wfTy_cast  :
  (forall (k13 : Hvl) (S5 : Ty) (k14 : Hvl) (S6 : Ty) ,
    (k13 = k14) -> (S5 = S6) -> (wfTy k13 S5) -> (wfTy k14 S6)).
Proof.
  congruence .
Qed.
Lemma wfPat_cast  :
  (forall (k13 : Hvl) (p14 : Pat) (k14 : Hvl) (p15 : Pat) ,
    (k13 = k14) -> (p14 = p15) -> (wfPat k13 p14) -> (wfPat k14 p15)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k13 : Hvl) (s6 : Tm) (k14 : Hvl) (s7 : Tm) ,
    (k13 = k14) -> (s6 = s7) -> (wfTm k13 s6) -> (wfTm k14 s7)).
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
  Inductive substhvl_TmVar (k13 : Hvl) : (forall (d0 : (Trace TmVar)) (k14 : Hvl) (k15 : Hvl) ,
    Prop) :=
    | substhvl_TmVar_here :
        (substhvl_TmVar k13 X0 (HS TmVar k13) k13)
    | substhvl_TmVar_there_TmVar
        {d0 : (Trace TmVar)} {k14 : Hvl}
        {k15 : Hvl} :
        (substhvl_TmVar k13 d0 k14 k15) -> (substhvl_TmVar k13 (XS TmVar d0) (HS TmVar k14) (HS TmVar k15))
    | substhvl_TmVar_there_TyVar
        {d0 : (Trace TmVar)} {k14 : Hvl}
        {k15 : Hvl} :
        (substhvl_TmVar k13 d0 k14 k15) -> (substhvl_TmVar k13 (XS TyVar d0) (HS TyVar k14) (HS TyVar k15)).
  Inductive substhvl_TyVar (k13 : Hvl) : (forall (d0 : (Trace TyVar)) (k14 : Hvl) (k15 : Hvl) ,
    Prop) :=
    | substhvl_TyVar_here :
        (substhvl_TyVar k13 X0 (HS TyVar k13) k13)
    | substhvl_TyVar_there_TmVar
        {d0 : (Trace TyVar)} {k14 : Hvl}
        {k15 : Hvl} :
        (substhvl_TyVar k13 d0 k14 k15) -> (substhvl_TyVar k13 (XS TmVar d0) (HS TmVar k14) (HS TmVar k15))
    | substhvl_TyVar_there_TyVar
        {d0 : (Trace TyVar)} {k14 : Hvl}
        {k15 : Hvl} :
        (substhvl_TyVar k13 d0 k14 k15) -> (substhvl_TyVar k13 (XS TyVar d0) (HS TyVar k14) (HS TyVar k15)).
  Lemma weaken_substhvl_TmVar  :
    (forall {k14 : Hvl} (k13 : Hvl) {d0 : (Trace TmVar)} {k15 : Hvl} {k16 : Hvl} ,
      (substhvl_TmVar k14 d0 k15 k16) -> (substhvl_TmVar k14 (weakenTrace d0 k13) (appendHvl k15 k13) (appendHvl k16 k13))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_TyVar  :
    (forall {k14 : Hvl} (k13 : Hvl) {d0 : (Trace TyVar)} {k15 : Hvl} {k16 : Hvl} ,
      (substhvl_TyVar k14 d0 k15 k16) -> (substhvl_TyVar k14 (weakenTrace d0 k13) (appendHvl k15 k13) (appendHvl k16 k13))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_TmVar_wfindex_TmVar {k13 : Hvl} {s6 : Tm} (wft : (wfTm k13 s6)) :
    (forall {d0 : (Trace TmVar)} {k14 : Hvl} {k15 : Hvl} ,
      (substhvl_TmVar k13 d0 k14 k15) -> (forall {x6 : (Index TmVar)} ,
        (wfindex k14 x6) -> (wfTm k15 (substIndex d0 s6 x6)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TyVar_wfindex_TyVar {k13 : Hvl} {S5 : Ty} (wft : (wfTy k13 S5)) :
    (forall {d0 : (Trace TyVar)} {k14 : Hvl} {k15 : Hvl} ,
      (substhvl_TyVar k13 d0 k14 k15) -> (forall {X10 : (Index TyVar)} ,
        (wfindex k14 X10) -> (wfTy k15 (tsubstIndex d0 S5 X10)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TmVar_wfindex_TyVar {k13 : Hvl} :
    (forall {d0 : (Trace TmVar)} {k14 : Hvl} {k15 : Hvl} ,
      (substhvl_TmVar k13 d0 k14 k15) -> (forall {X10 : (Index TyVar)} ,
        (wfindex k14 X10) -> (wfindex k15 X10))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_TyVar_wfindex_TmVar {k13 : Hvl} :
    (forall {d0 : (Trace TyVar)} {k14 : Hvl} {k15 : Hvl} ,
      (substhvl_TyVar k13 d0 k14 k15) -> (forall {x6 : (Index TmVar)} ,
        (wfindex k14 x6) -> (wfindex k15 x6))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_TmVar_wfTy {k13 : Hvl} : (forall (k14 : Hvl) ,
    (forall (S5 : Ty) (wf0 : (wfTy k14 S5)) ,
      (forall {d0 : (Trace TmVar)} {k15 : Hvl} ,
        (substhvl_TmVar k13 d0 k14 k15) -> (wfTy k15 S5)))) := (ind_wfTy (fun (k14 : Hvl) (S5 : Ty) (wf0 : (wfTy k14 S5)) =>
    (forall {d0 : (Trace TmVar)} {k15 : Hvl} ,
      (substhvl_TmVar k13 d0 k14 k15) -> (wfTy k15 S5))) (fun (k14 : Hvl) {X10 : (Index TyVar)} (wfi : (wfindex k14 X10)) {d0 : (Trace TmVar)} {k15 : Hvl} (del : (substhvl_TmVar k13 d0 k14 k15)) =>
    (wfTy_TVar k15 _ (substhvl_TmVar_wfindex_TyVar del wfi))) (fun (k14 : Hvl) (T1 : Ty) (wf0 : (wfTy k14 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k14 T2)) IHT2 {d0 : (Trace TmVar)} {k15 : Hvl} (del : (substhvl_TmVar k13 d0 k14 k15)) =>
    (wfTy_TArr k15 (IHT1 (weakenTrace d0 H0) k15 (weaken_substhvl_TmVar H0 del)) (IHT2 (weakenTrace d0 H0) k15 (weaken_substhvl_TmVar H0 del)))) (fun (k14 : Hvl) (T : Ty) (wf0 : (wfTy (HS TyVar k14) T)) IHT {d0 : (Trace TmVar)} {k15 : Hvl} (del : (substhvl_TmVar k13 d0 k14 k15)) =>
    (wfTy_TAll k15 (IHT (weakenTrace d0 (HS TyVar H0)) (HS TyVar k15) (weaken_substhvl_TmVar (HS TyVar H0) del)))) (fun (k14 : Hvl) (T1 : Ty) (wf0 : (wfTy k14 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k14 T2)) IHT2 {d0 : (Trace TmVar)} {k15 : Hvl} (del : (substhvl_TmVar k13 d0 k14 k15)) =>
    (wfTy_TProd k15 (IHT1 (weakenTrace d0 H0) k15 (weaken_substhvl_TmVar H0 del)) (IHT2 (weakenTrace d0 H0) k15 (weaken_substhvl_TmVar H0 del))))).
  Definition substhvl_TyVar_wfTy {k13 : Hvl} {S5 : Ty} (wf : (wfTy k13 S5)) : (forall (k14 : Hvl) ,
    (forall (S6 : Ty) (wf0 : (wfTy k14 S6)) ,
      (forall {d0 : (Trace TyVar)} {k15 : Hvl} ,
        (substhvl_TyVar k13 d0 k14 k15) -> (wfTy k15 (tsubstTy d0 S5 S6))))) := (ind_wfTy (fun (k14 : Hvl) (S6 : Ty) (wf0 : (wfTy k14 S6)) =>
    (forall {d0 : (Trace TyVar)} {k15 : Hvl} ,
      (substhvl_TyVar k13 d0 k14 k15) -> (wfTy k15 (tsubstTy d0 S5 S6)))) (fun (k14 : Hvl) {X10 : (Index TyVar)} (wfi : (wfindex k14 X10)) {d0 : (Trace TyVar)} {k15 : Hvl} (del : (substhvl_TyVar k13 d0 k14 k15)) =>
    (substhvl_TyVar_wfindex_TyVar wf del wfi)) (fun (k14 : Hvl) (T1 : Ty) (wf0 : (wfTy k14 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k14 T2)) IHT2 {d0 : (Trace TyVar)} {k15 : Hvl} (del : (substhvl_TyVar k13 d0 k14 k15)) =>
    (wfTy_TArr k15 (IHT1 (weakenTrace d0 H0) k15 (weaken_substhvl_TyVar H0 del)) (IHT2 (weakenTrace d0 H0) k15 (weaken_substhvl_TyVar H0 del)))) (fun (k14 : Hvl) (T : Ty) (wf0 : (wfTy (HS TyVar k14) T)) IHT {d0 : (Trace TyVar)} {k15 : Hvl} (del : (substhvl_TyVar k13 d0 k14 k15)) =>
    (wfTy_TAll k15 (IHT (weakenTrace d0 (HS TyVar H0)) (HS TyVar k15) (weaken_substhvl_TyVar (HS TyVar H0) del)))) (fun (k14 : Hvl) (T1 : Ty) (wf0 : (wfTy k14 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k14 T2)) IHT2 {d0 : (Trace TyVar)} {k15 : Hvl} (del : (substhvl_TyVar k13 d0 k14 k15)) =>
    (wfTy_TProd k15 (IHT1 (weakenTrace d0 H0) k15 (weaken_substhvl_TyVar H0 del)) (IHT2 (weakenTrace d0 H0) k15 (weaken_substhvl_TyVar H0 del))))).
  Definition substhvl_TmVar_wfPat {k13 : Hvl} : (forall (k14 : Hvl) ,
    (forall (p14 : Pat) (wf0 : (wfPat k14 p14)) ,
      (forall {d0 : (Trace TmVar)} {k15 : Hvl} ,
        (substhvl_TmVar k13 d0 k14 k15) -> (wfPat k15 p14)))) := (ind_wfPat (fun (k14 : Hvl) (p14 : Pat) (wf0 : (wfPat k14 p14)) =>
    (forall {d0 : (Trace TmVar)} {k15 : Hvl} ,
      (substhvl_TmVar k13 d0 k14 k15) -> (wfPat k15 p14))) (fun (k14 : Hvl) (T : Ty) (wf0 : (wfTy k14 T)) {d0 : (Trace TmVar)} {k15 : Hvl} (del : (substhvl_TmVar k13 d0 k14 k15)) =>
    (wfPat_PVar k15 (substhvl_TmVar_wfTy k14 T wf0 (weaken_substhvl_TmVar H0 del)))) (fun (k14 : Hvl) {d0 : (Trace TmVar)} {k15 : Hvl} (del : (substhvl_TmVar k13 d0 k14 k15)) =>
    (wfPat_PTVar k15)) (fun (k14 : Hvl) (p1 : Pat) (wf0 : (wfPat k14 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k14 (appendHvl H0 (bind p1))) p2)) IHp2 {d0 : (Trace TmVar)} {k15 : Hvl} (del : (substhvl_TmVar k13 d0 k14 k15)) =>
    (wfPat_PProd k15 (IHp1 (weakenTrace d0 H0) k15 (weaken_substhvl_TmVar H0 del)) (IHp2 (weakenTrace d0 (appendHvl H0 (bind p1))) (appendHvl k15 (appendHvl H0 (bind p1))) (weaken_substhvl_TmVar (appendHvl H0 (bind p1)) del))))).
  Definition substhvl_TyVar_wfPat {k13 : Hvl} {S5 : Ty} (wf : (wfTy k13 S5)) : (forall (k14 : Hvl) ,
    (forall (p14 : Pat) (wf0 : (wfPat k14 p14)) ,
      (forall {d0 : (Trace TyVar)} {k15 : Hvl} ,
        (substhvl_TyVar k13 d0 k14 k15) -> (wfPat k15 (tsubstPat d0 S5 p14))))) := (ind_wfPat (fun (k14 : Hvl) (p14 : Pat) (wf0 : (wfPat k14 p14)) =>
    (forall {d0 : (Trace TyVar)} {k15 : Hvl} ,
      (substhvl_TyVar k13 d0 k14 k15) -> (wfPat k15 (tsubstPat d0 S5 p14)))) (fun (k14 : Hvl) (T : Ty) (wf0 : (wfTy k14 T)) {d0 : (Trace TyVar)} {k15 : Hvl} (del : (substhvl_TyVar k13 d0 k14 k15)) =>
    (wfPat_PVar k15 (substhvl_TyVar_wfTy wf k14 T wf0 (weaken_substhvl_TyVar H0 del)))) (fun (k14 : Hvl) {d0 : (Trace TyVar)} {k15 : Hvl} (del : (substhvl_TyVar k13 d0 k14 k15)) =>
    (wfPat_PTVar k15)) (fun (k14 : Hvl) (p1 : Pat) (wf0 : (wfPat k14 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k14 (appendHvl H0 (bind p1))) p2)) IHp2 {d0 : (Trace TyVar)} {k15 : Hvl} (del : (substhvl_TyVar k13 d0 k14 k15)) =>
    (wfPat_PProd k15 (IHp1 (weakenTrace d0 H0) k15 (weaken_substhvl_TyVar H0 del)) (eq_ind2 wfPat (f_equal2 appendHvl (eq_refl k15) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0)))) eq_refl (IHp2 (weakenTrace d0 (appendHvl H0 (bind p1))) (appendHvl k15 (appendHvl H0 (bind p1))) (weaken_substhvl_TyVar (appendHvl H0 (bind p1)) del)))))).
  Definition substhvl_TmVar_wfTm {k13 : Hvl} {s6 : Tm} (wf : (wfTm k13 s6)) : (forall (k14 : Hvl) ,
    (forall (s7 : Tm) (wf0 : (wfTm k14 s7)) ,
      (forall {d0 : (Trace TmVar)} {k15 : Hvl} ,
        (substhvl_TmVar k13 d0 k14 k15) -> (wfTm k15 (substTm d0 s6 s7))))) := (ind_wfTm (fun (k14 : Hvl) (s7 : Tm) (wf0 : (wfTm k14 s7)) =>
    (forall {d0 : (Trace TmVar)} {k15 : Hvl} ,
      (substhvl_TmVar k13 d0 k14 k15) -> (wfTm k15 (substTm d0 s6 s7)))) (fun (k14 : Hvl) {x6 : (Index TmVar)} (wfi : (wfindex k14 x6)) {d0 : (Trace TmVar)} {k15 : Hvl} (del : (substhvl_TmVar k13 d0 k14 k15)) =>
    (substhvl_TmVar_wfindex_TmVar wf del wfi)) (fun (k14 : Hvl) (T : Ty) (wf0 : (wfTy k14 T)) (t : Tm) (wf1 : (wfTm (HS TmVar k14) t)) IHt {d0 : (Trace TmVar)} {k15 : Hvl} (del : (substhvl_TmVar k13 d0 k14 k15)) =>
    (wfTm_Abs k15 (substhvl_TmVar_wfTy k14 T wf0 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d0 (HS TmVar H0)) (HS TmVar k15) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k14 : Hvl) (t1 : Tm) (wf0 : (wfTm k14 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k14 t2)) IHt2 {d0 : (Trace TmVar)} {k15 : Hvl} (del : (substhvl_TmVar k13 d0 k14 k15)) =>
    (wfTm_App k15 (IHt1 (weakenTrace d0 H0) k15 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d0 H0) k15 (weaken_substhvl_TmVar H0 del)))) (fun (k14 : Hvl) (t : Tm) (wf0 : (wfTm (HS TyVar k14) t)) IHt {d0 : (Trace TmVar)} {k15 : Hvl} (del : (substhvl_TmVar k13 d0 k14 k15)) =>
    (wfTm_TAbs k15 (IHt (weakenTrace d0 (HS TyVar H0)) (HS TyVar k15) (weaken_substhvl_TmVar (HS TyVar H0) del)))) (fun (k14 : Hvl) (t : Tm) (wf0 : (wfTm k14 t)) IHt (T : Ty) (wf1 : (wfTy k14 T)) {d0 : (Trace TmVar)} {k15 : Hvl} (del : (substhvl_TmVar k13 d0 k14 k15)) =>
    (wfTm_TApp k15 (IHt (weakenTrace d0 H0) k15 (weaken_substhvl_TmVar H0 del)) (substhvl_TmVar_wfTy k14 T wf1 (weaken_substhvl_TmVar H0 del)))) (fun (k14 : Hvl) (t1 : Tm) (wf0 : (wfTm k14 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k14 t2)) IHt2 {d0 : (Trace TmVar)} {k15 : Hvl} (del : (substhvl_TmVar k13 d0 k14 k15)) =>
    (wfTm_Prod k15 (IHt1 (weakenTrace d0 H0) k15 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d0 H0) k15 (weaken_substhvl_TmVar H0 del)))) (fun (k14 : Hvl) (t1 : Tm) (wf0 : (wfTm k14 t1)) IHt1 (p : Pat) (wf1 : (wfPat k14 p)) (t2 : Tm) (wf2 : (wfTm (appendHvl k14 (appendHvl H0 (bind p))) t2)) IHt2 {d0 : (Trace TmVar)} {k15 : Hvl} (del : (substhvl_TmVar k13 d0 k14 k15)) =>
    (wfTm_Case k15 (IHt1 (weakenTrace d0 H0) k15 (weaken_substhvl_TmVar H0 del)) (substhvl_TmVar_wfPat k14 p wf1 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d0 (appendHvl H0 (bind p))) (appendHvl k15 (appendHvl H0 (bind p))) (weaken_substhvl_TmVar (appendHvl H0 (bind p)) del))))).
  Definition substhvl_TyVar_wfTm {k13 : Hvl} {S5 : Ty} (wf : (wfTy k13 S5)) : (forall (k14 : Hvl) ,
    (forall (s6 : Tm) (wf0 : (wfTm k14 s6)) ,
      (forall {d0 : (Trace TyVar)} {k15 : Hvl} ,
        (substhvl_TyVar k13 d0 k14 k15) -> (wfTm k15 (tsubstTm d0 S5 s6))))) := (ind_wfTm (fun (k14 : Hvl) (s6 : Tm) (wf0 : (wfTm k14 s6)) =>
    (forall {d0 : (Trace TyVar)} {k15 : Hvl} ,
      (substhvl_TyVar k13 d0 k14 k15) -> (wfTm k15 (tsubstTm d0 S5 s6)))) (fun (k14 : Hvl) {x6 : (Index TmVar)} (wfi : (wfindex k14 x6)) {d0 : (Trace TyVar)} {k15 : Hvl} (del : (substhvl_TyVar k13 d0 k14 k15)) =>
    (wfTm_Var k15 _ (substhvl_TyVar_wfindex_TmVar del wfi))) (fun (k14 : Hvl) (T : Ty) (wf0 : (wfTy k14 T)) (t : Tm) (wf1 : (wfTm (HS TmVar k14) t)) IHt {d0 : (Trace TyVar)} {k15 : Hvl} (del : (substhvl_TyVar k13 d0 k14 k15)) =>
    (wfTm_Abs k15 (substhvl_TyVar_wfTy wf k14 T wf0 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d0 (HS TmVar H0)) (HS TmVar k15) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k14 : Hvl) (t1 : Tm) (wf0 : (wfTm k14 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k14 t2)) IHt2 {d0 : (Trace TyVar)} {k15 : Hvl} (del : (substhvl_TyVar k13 d0 k14 k15)) =>
    (wfTm_App k15 (IHt1 (weakenTrace d0 H0) k15 (weaken_substhvl_TyVar H0 del)) (IHt2 (weakenTrace d0 H0) k15 (weaken_substhvl_TyVar H0 del)))) (fun (k14 : Hvl) (t : Tm) (wf0 : (wfTm (HS TyVar k14) t)) IHt {d0 : (Trace TyVar)} {k15 : Hvl} (del : (substhvl_TyVar k13 d0 k14 k15)) =>
    (wfTm_TAbs k15 (IHt (weakenTrace d0 (HS TyVar H0)) (HS TyVar k15) (weaken_substhvl_TyVar (HS TyVar H0) del)))) (fun (k14 : Hvl) (t : Tm) (wf0 : (wfTm k14 t)) IHt (T : Ty) (wf1 : (wfTy k14 T)) {d0 : (Trace TyVar)} {k15 : Hvl} (del : (substhvl_TyVar k13 d0 k14 k15)) =>
    (wfTm_TApp k15 (IHt (weakenTrace d0 H0) k15 (weaken_substhvl_TyVar H0 del)) (substhvl_TyVar_wfTy wf k14 T wf1 (weaken_substhvl_TyVar H0 del)))) (fun (k14 : Hvl) (t1 : Tm) (wf0 : (wfTm k14 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k14 t2)) IHt2 {d0 : (Trace TyVar)} {k15 : Hvl} (del : (substhvl_TyVar k13 d0 k14 k15)) =>
    (wfTm_Prod k15 (IHt1 (weakenTrace d0 H0) k15 (weaken_substhvl_TyVar H0 del)) (IHt2 (weakenTrace d0 H0) k15 (weaken_substhvl_TyVar H0 del)))) (fun (k14 : Hvl) (t1 : Tm) (wf0 : (wfTm k14 t1)) IHt1 (p : Pat) (wf1 : (wfPat k14 p)) (t2 : Tm) (wf2 : (wfTm (appendHvl k14 (appendHvl H0 (bind p))) t2)) IHt2 {d0 : (Trace TyVar)} {k15 : Hvl} (del : (substhvl_TyVar k13 d0 k14 k15)) =>
    (wfTm_Case k15 (IHt1 (weakenTrace d0 H0) k15 (weaken_substhvl_TyVar H0 del)) (substhvl_TyVar_wfPat wf k14 p wf1 (weaken_substhvl_TyVar H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k15) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bind _ _ _)) (eq_refl H0)))) eq_refl (IHt2 (weakenTrace d0 (appendHvl H0 (bind p))) (appendHvl k15 (appendHvl H0 (bind p))) (weaken_substhvl_TyVar (appendHvl H0 (bind p)) del)))))).
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
Fixpoint subhvl_TmVar_TyVar (k13 : Hvl) {struct k13} :
Prop :=
  match k13 with
    | (H0) => True
    | (HS a k13) => match a with
      | (TmVar) => (subhvl_TmVar_TyVar k13)
      | (TyVar) => (subhvl_TmVar_TyVar k13)
    end
  end.
Lemma subhvl_TmVar_TyVar_append  :
  (forall (k13 : Hvl) (k14 : Hvl) ,
    (subhvl_TmVar_TyVar k13) -> (subhvl_TmVar_TyVar k14) -> (subhvl_TmVar_TyVar (appendHvl k13 k14))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_TmVar_TyVar_append : infra.
 Hint Resolve subhvl_TmVar_TyVar_append : wf.
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
  Fixpoint shiftCtx (c0 : (Cutoff TmVar)) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shiftCtx c0 G0) T)
      | (etvar G0) => (etvar (shiftCtx c0 G0))
    end.
  Fixpoint tshiftCtx (c0 : (Cutoff TyVar)) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tshiftCtx c0 G0) (tshiftTy (weakenCutoffTyVar c0 (domainCtx G0)) T))
      | (etvar G0) => (etvar (tshiftCtx c0 G0))
    end.
  Fixpoint weakenCtx (G : Ctx) (k13 : Hvl) {struct k13} :
  Ctx :=
    match k13 with
      | (H0) => G
      | (HS TmVar k13) => (weakenCtx G k13)
      | (HS TyVar k13) => (tshiftCtx C0 (weakenCtx G k13))
    end.
  Fixpoint substCtx (d0 : (Trace TmVar)) (s6 : Tm) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substCtx d0 s6 G0) T)
      | (etvar G0) => (etvar (substCtx d0 s6 G0))
    end.
  Fixpoint tsubstCtx (d0 : (Trace TyVar)) (S5 : Ty) (G : Ctx) :
  Ctx :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstCtx d0 S5 G0) (tsubstTy (weakenTrace d0 (domainCtx G0)) S5 T))
      | (etvar G0) => (etvar (tsubstCtx d0 S5 G0))
    end.
  Lemma domainCtx_shiftCtx  :
    (forall (c0 : (Cutoff TmVar)) (G : Ctx) ,
      ((domainCtx (shiftCtx c0 G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainCtx_tshiftCtx  :
    (forall (c0 : (Cutoff TyVar)) (G : Ctx) ,
      ((domainCtx (tshiftCtx c0 G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainCtx_substCtx  :
    (forall (d0 : (Trace TmVar)) (s6 : Tm) (G : Ctx) ,
      ((domainCtx (substCtx d0 s6 G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainCtx_tsubstCtx  :
    (forall (d0 : (Trace TyVar)) (S5 : Ty) (G : Ctx) ,
      ((domainCtx (tsubstCtx d0 S5 G)) = (domainCtx G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainCtx_appendCtx : interaction.
 Hint Rewrite domainCtx_appendCtx : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shiftCtx_appendCtx  :
      (forall (c0 : (Cutoff TmVar)) (G : Ctx) (G0 : Ctx) ,
        ((shiftCtx c0 (appendCtx G G0)) = (appendCtx (shiftCtx c0 G) (shiftCtx (weakenCutoffTmVar c0 (domainCtx G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma tshiftCtx_appendCtx  :
      (forall (c0 : (Cutoff TyVar)) (G : Ctx) (G0 : Ctx) ,
        ((tshiftCtx c0 (appendCtx G G0)) = (appendCtx (tshiftCtx c0 G) (tshiftCtx (weakenCutoffTyVar c0 (domainCtx G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substCtx_appendCtx  :
      (forall (d0 : (Trace TmVar)) (s6 : Tm) (G : Ctx) (G0 : Ctx) ,
        ((substCtx d0 s6 (appendCtx G G0)) = (appendCtx (substCtx d0 s6 G) (substCtx (weakenTrace d0 (domainCtx G)) s6 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstCtx_appendCtx  :
      (forall (d0 : (Trace TyVar)) (S5 : Ty) (G : Ctx) (G0 : Ctx) ,
        ((tsubstCtx d0 S5 (appendCtx G G0)) = (appendCtx (tsubstCtx d0 S5 G) (tsubstCtx (weakenTrace d0 (domainCtx G)) S5 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S5 : Ty) (k13 : Hvl) (k14 : Hvl) ,
      ((weakenTy (weakenTy S5 k13) k14) = (weakenTy S5 (appendHvl k13 k14)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenPat_append  :
    (forall (p14 : Pat) (k13 : Hvl) (k14 : Hvl) ,
      ((weakenPat (weakenPat p14 k13) k14) = (weakenPat p14 (appendHvl k13 k14)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s6 : Tm) (k13 : Hvl) (k14 : Hvl) ,
      ((weakenTm (weakenTm s6 k13) k14) = (weakenTm s6 (appendHvl k13 k14)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Ctx -> (Index TmVar) -> Ty -> Prop :=
      | lookup_evar_here {G : Ctx}
          (T9 : Ty) :
          (wfTy (domainCtx G) T9) -> (lookup_evar (evar G T9) I0 T9)
      | lookup_evar_there_evar
          {G : Ctx} {x6 : (Index TmVar)}
          (T10 : Ty) (T11 : Ty) :
          (lookup_evar G x6 T10) -> (lookup_evar (evar G T11) (IS x6) T10)
      | lookup_evar_there_etvar
          {G : Ctx} {x6 : (Index TmVar)}
          (T10 : Ty) :
          (lookup_evar G x6 T10) -> (lookup_evar (etvar G) x6 (tshiftTy C0 T10)).
    Inductive lookup_etvar : Ctx -> (Index TyVar) -> Prop :=
      | lookup_etvar_here {G : Ctx}
          : (lookup_etvar (etvar G) I0)
      | lookup_etvar_there_evar
          {G : Ctx} {X10 : (Index TyVar)}
          (T10 : Ty) :
          (lookup_etvar G X10) -> (lookup_etvar (evar G T10) X10)
      | lookup_etvar_there_etvar
          {G : Ctx} {X10 : (Index TyVar)}
          :
          (lookup_etvar G X10) -> (lookup_etvar (etvar G) (IS X10)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Ctx) (T10 : Ty) (T11 : Ty) ,
        (lookup_evar (evar G T10) I0 T11) -> (T10 = T11)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Ctx} {x6 : (Index TmVar)} ,
        (forall (T10 : Ty) ,
          (lookup_evar G x6 T10) -> (forall (T11 : Ty) ,
            (lookup_evar G x6 T11) -> (T10 = T11)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Ctx} {x6 : (Index TmVar)} (T10 : Ty) ,
        (lookup_evar G x6 T10) -> (wfTy (domainCtx G) T10)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Ctx} (G0 : Ctx) {x6 : (Index TmVar)} (T10 : Ty) ,
        (lookup_evar G x6 T10) -> (lookup_evar (appendCtx G G0) (weakenIndexTmVar x6 (domainCtx G0)) (weakenTy T10 (domainCtx G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Ctx} (G0 : Ctx) {X10 : (Index TyVar)} ,
        (lookup_etvar G X10) -> (lookup_etvar (appendCtx G G0) (weakenIndexTyVar X10 (domainCtx G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Ctx} {x6 : (Index TmVar)} (T12 : Ty) ,
        (lookup_evar G x6 T12) -> (wfindex (domainCtx G) x6)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Ctx} {X10 : (Index TyVar)} ,
        (lookup_etvar G X10) -> (wfindex (domainCtx G) X10)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff TmVar) -> Ctx -> Ctx -> Prop :=
    | shift_evar_here {G : Ctx}
        {T10 : Ty} :
        (shift_evar C0 G (evar G T10))
    | shiftevar_there_evar
        {c0 : (Cutoff TmVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_evar c0 G G0) -> (shift_evar (CS c0) (evar G T) (evar G0 T))
    | shiftevar_there_etvar
        {c0 : (Cutoff TmVar)} {G : Ctx}
        {G0 : Ctx} :
        (shift_evar c0 G G0) -> (shift_evar c0 (etvar G) (etvar G0)).
  Lemma weaken_shift_evar  :
    (forall (G : Ctx) {c0 : (Cutoff TmVar)} {G0 : Ctx} {G1 : Ctx} ,
      (shift_evar c0 G0 G1) -> (shift_evar (weakenCutoffTmVar c0 (domainCtx G)) (appendCtx G0 G) (appendCtx G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff TyVar) -> Ctx -> Ctx -> Prop :=
    | shift_etvar_here {G : Ctx} :
        (shift_etvar C0 G (etvar G))
    | shiftetvar_there_evar
        {c0 : (Cutoff TyVar)} {G : Ctx}
        {G0 : Ctx} {T : Ty} :
        (shift_etvar c0 G G0) -> (shift_etvar c0 (evar G T) (evar G0 (tshiftTy c0 T)))
    | shiftetvar_there_etvar
        {c0 : (Cutoff TyVar)} {G : Ctx}
        {G0 : Ctx} :
        (shift_etvar c0 G G0) -> (shift_etvar (CS c0) (etvar G) (etvar G0)).
  Lemma weaken_shift_etvar  :
    (forall (G : Ctx) {c0 : (Cutoff TyVar)} {G0 : Ctx} {G1 : Ctx} ,
      (shift_etvar c0 G0 G1) -> (shift_etvar (weakenCutoffTyVar c0 (domainCtx G)) (appendCtx G0 G) (appendCtx G1 (tshiftCtx c0 G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_TmVar  :
    (forall {c0 : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} ,
      (shift_evar c0 G G0) -> (shifthvl_TmVar c0 (domainCtx G) (domainCtx G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_etvar_shifthvl_TyVar  :
    (forall {c0 : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} ,
      (shift_etvar c0 G G0) -> (shifthvl_TyVar c0 (domainCtx G) (domainCtx G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Ctx) (T10 : Ty) (s6 : Tm) : (Trace TmVar) -> Ctx -> Ctx -> Prop :=
    | subst_evar_here :
        (subst_evar G T10 s6 X0 (evar G T10) G)
    | subst_evar_there_evar
        {d0 : (Trace TmVar)} {G0 : Ctx}
        {G1 : Ctx} (T11 : Ty) :
        (subst_evar G T10 s6 d0 G0 G1) -> (subst_evar G T10 s6 (XS TmVar d0) (evar G0 T11) (evar G1 T11))
    | subst_evar_there_etvar
        {d0 : (Trace TmVar)} {G0 : Ctx}
        {G1 : Ctx} :
        (subst_evar G T10 s6 d0 G0 G1) -> (subst_evar G T10 s6 (XS TyVar d0) (etvar G0) (etvar G1)).
  Lemma weaken_subst_evar {G : Ctx} (T10 : Ty) {s6 : Tm} :
    (forall (G0 : Ctx) {d0 : (Trace TmVar)} {G1 : Ctx} {G2 : Ctx} ,
      (subst_evar G T10 s6 d0 G1 G2) -> (subst_evar G T10 s6 (weakenTrace d0 (domainCtx G0)) (appendCtx G1 G0) (appendCtx G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Ctx) (S5 : Ty) : (Trace TyVar) -> Ctx -> Ctx -> Prop :=
    | subst_etvar_here :
        (subst_etvar G S5 X0 (etvar G) G)
    | subst_etvar_there_evar
        {d0 : (Trace TyVar)} {G0 : Ctx}
        {G1 : Ctx} (T10 : Ty) :
        (subst_etvar G S5 d0 G0 G1) -> (subst_etvar G S5 (XS TmVar d0) (evar G0 T10) (evar G1 (tsubstTy d0 S5 T10)))
    | subst_etvar_there_etvar
        {d0 : (Trace TyVar)} {G0 : Ctx}
        {G1 : Ctx} :
        (subst_etvar G S5 d0 G0 G1) -> (subst_etvar G S5 (XS TyVar d0) (etvar G0) (etvar G1)).
  Lemma weaken_subst_etvar {G : Ctx} {S5 : Ty} :
    (forall (G0 : Ctx) {d0 : (Trace TyVar)} {G1 : Ctx} {G2 : Ctx} ,
      (subst_etvar G S5 d0 G1 G2) -> (subst_etvar G S5 (weakenTrace d0 (domainCtx G0)) (appendCtx G1 G0) (appendCtx G2 (tsubstCtx d0 S5 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_TmVar {G : Ctx} {s6 : Tm} (T10 : Ty) :
    (forall {d0 : (Trace TmVar)} {G0 : Ctx} {G1 : Ctx} ,
      (subst_evar G T10 s6 d0 G0 G1) -> (substhvl_TmVar (domainCtx G) d0 (domainCtx G0) (domainCtx G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_TyVar {G : Ctx} {S5 : Ty} :
    (forall {d0 : (Trace TyVar)} {G0 : Ctx} {G1 : Ctx} ,
      (subst_etvar G S5 d0 G0 G1) -> (substhvl_TyVar (domainCtx G) d0 (domainCtx G0) (domainCtx G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
End ContextStuff.
 Hint Rewrite domainCtx_tshiftCtx : interaction.
 Hint Rewrite domainCtx_tshiftCtx : env_domain_shift.
 Hint Rewrite domainCtx_tsubstCtx : interaction.
 Hint Rewrite domainCtx_tsubstCtx : env_domain_subst.
 Hint Rewrite tshiftCtx_appendCtx : interaction.
 Hint Rewrite tshiftCtx_appendCtx : env_shift_append.
 Hint Rewrite tsubstCtx_appendCtx : interaction.
 Hint Rewrite tsubstCtx_appendCtx : env_shift_append.
 Hint Constructors lookup_evar lookup_etvar : infra.
 Hint Constructors lookup_evar lookup_etvar : lookup.
 Hint Constructors lookup_evar lookup_etvar : shift.
 Hint Constructors lookup_evar lookup_etvar : subst.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : infra.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : lookup.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : shift.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : weaken.
Lemma weaken_lookup_evar_here  :
  (forall {G : Ctx} (G0 : Ctx) {T10 : Ty} (wf : (wfTy (domainCtx G) T10)) ,
    (lookup_evar (appendCtx (evar G T10) G0) (weakenIndexTmVar I0 (domainCtx G0)) (weakenTy T10 (domainCtx G0)))).
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
  | H41 : (wfTy _ (TVar _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTy _ (TArr _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTy _ (TAll _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTy _ (TProd _ _)) |- _ => inversion H41; subst; clear H41
end : infra wf.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H41 : (wfPat _ (PVar _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfPat _ (PTVar)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfPat _ (PProd _ _)) |- _ => inversion H41; subst; clear H41
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H41 : (wfTm _ (Var _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (Abs _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (App _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (TAbs _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (TApp _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (Prod _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (Case _ _ _)) |- _ => inversion H41; subst; clear H41
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
  (forall {c0 : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evar c0 G G0)) {x6 : (Index TmVar)} {T10 : Ty} ,
    (lookup_evar G x6 T10) -> (lookup_evar G0 (shiftIndex c0 x6) T10)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c0 : (Cutoff TmVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_evar c0 G G0)) {X10 : (Index TyVar)} ,
    (lookup_etvar G X10) -> (lookup_etvar G0 X10)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c0 : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_etvar c0 G G0)) {x6 : (Index TmVar)} {T10 : Ty} ,
    (lookup_evar G x6 T10) -> (lookup_evar G0 x6 (tshiftTy c0 T10))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c0 : (Cutoff TyVar)} {G : Ctx} {G0 : Ctx} (ins : (shift_etvar c0 G G0)) {X10 : (Index TyVar)} ,
    (lookup_etvar G X10) -> (lookup_etvar G0 (tshiftIndex c0 X10))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Ctx} (T11 : Ty) {s6 : Tm} :
  (forall {d0 : (Trace TmVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_evar G T11 s6 d0 G0 G1)) {X10 : (Index TyVar)} ,
    (lookup_etvar G0 X10) -> (lookup_etvar G1 X10)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Ctx} {S5 : Ty} (wf : (wfTy (domainCtx G) S5)) :
  (forall {d0 : (Trace TyVar)} {G0 : Ctx} {G1 : Ctx} (sub : (subst_etvar G S5 d0 G0 G1)) {x6 : (Index TmVar)} (T11 : Ty) ,
    (lookup_evar G0 x6 T11) -> (lookup_evar G1 x6 (tsubstTy d0 S5 T11))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (TVar X10) => 1
    | (TArr T9 T10) => (plus 1 (plus (size_Ty T9) (size_Ty T10)))
    | (TAll T11) => (plus 1 (size_Ty T11))
    | (TProd T12 T13) => (plus 1 (plus (size_Ty T12) (size_Ty T13)))
  end.
Fixpoint size_Pat (p9 : Pat) {struct p9} :
nat :=
  match p9 with
    | (PVar T9) => (plus 1 (size_Ty T9))
    | (PTVar) => 1
    | (PProd p10 p11) => (plus 1 (plus (size_Pat p10) (size_Pat p11)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (Var x6) => 1
    | (Abs T9 t8) => (plus 1 (plus (size_Ty T9) (size_Tm t8)))
    | (App t9 t10) => (plus 1 (plus (size_Tm t9) (size_Tm t10)))
    | (TAbs t11) => (plus 1 (size_Tm t11))
    | (TApp t12 T10) => (plus 1 (plus (size_Tm t12) (size_Ty T10)))
    | (Prod t13 t14) => (plus 1 (plus (size_Tm t13) (size_Tm t14)))
    | (Case t15 p9 t16) => (plus 1 (plus (size_Tm t15) (plus (size_Pat p9) (size_Tm t16))))
  end.
Fixpoint tshift_size_Ty (S1 : Ty) (c0 : (Cutoff TyVar)) {struct S1} :
((size_Ty (tshiftTy c0 S1)) = (size_Ty S1)) :=
  match S1 return ((size_Ty (tshiftTy c0 S1)) = (size_Ty S1)) with
    | (TVar _) => eq_refl
    | (TArr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c0) (tshift_size_Ty T2 c0)))
    | (TAll T) => (f_equal2 plus eq_refl (tshift_size_Ty T (CS c0)))
    | (TProd T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c0) (tshift_size_Ty T2 c0)))
  end.
Fixpoint tshift_size_Pat (p11 : Pat) (c0 : (Cutoff TyVar)) {struct p11} :
((size_Pat (tshiftPat c0 p11)) = (size_Pat p11)) :=
  match p11 return ((size_Pat (tshiftPat c0 p11)) = (size_Pat p11)) with
    | (PVar T) => (f_equal2 plus eq_refl (tshift_size_Ty T c0))
    | (PTVar) => eq_refl
    | (PProd p1 p2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Pat p1 c0) (tshift_size_Pat p2 (weakenCutoffTyVar c0 (appendHvl H0 (bind p1))))))
  end.
Fixpoint shift_size_Tm (s : Tm) (c0 : (Cutoff TmVar)) {struct s} :
((size_Tm (shiftTm c0 s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c0 s)) = (size_Tm s)) with
    | (Var _) => eq_refl
    | (Abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c0))))
    | (App t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c0) (shift_size_Tm t2 c0)))
    | (TAbs t) => (f_equal2 plus eq_refl (shift_size_Tm t c0))
    | (TApp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c0) eq_refl))
    | (Prod t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c0) (shift_size_Tm t2 c0)))
    | (Case t1 p t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c0) (f_equal2 plus eq_refl (shift_size_Tm t2 (weakenCutoffTmVar c0 (appendHvl H0 (bind p)))))))
  end.
Fixpoint tshift_size_Tm (s : Tm) (c0 : (Cutoff TyVar)) {struct s} :
((size_Tm (tshiftTm c0 s)) = (size_Tm s)) :=
  match s return ((size_Tm (tshiftTm c0 s)) = (size_Tm s)) with
    | (Var _) => eq_refl
    | (Abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c0) (tshift_size_Tm t c0)))
    | (App t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c0) (tshift_size_Tm t2 c0)))
    | (TAbs t) => (f_equal2 plus eq_refl (tshift_size_Tm t (CS c0)))
    | (TApp t T) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t c0) (tshift_size_Ty T c0)))
    | (Prod t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c0) (tshift_size_Tm t2 c0)))
    | (Case t1 p t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c0) (f_equal2 plus (tshift_size_Pat p c0) (tshift_size_Tm t2 (weakenCutoffTyVar c0 (appendHvl H0 (bind p)))))))
  end.
 Hint Rewrite tshift_size_Pat shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite tshift_size_Pat shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Pat  :
  (forall (k : Hvl) (p11 : Pat) ,
    ((size_Pat (weakenPat p11 k)) = (size_Pat p11))).
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
  (forall (k : Hvl) (S1 : Ty) ,
    ((size_Ty (weakenTy S1 k)) = (size_Ty S1))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Pat weaken_size_Tm weaken_size_Ty : weaken_size.
 Hint Rewrite appendCtx_assoc : interaction.
 Hint Rewrite <- weakenCutoffTmVar_append weakenCutoffTyVar_append weakenTrace_append weakenPat_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.