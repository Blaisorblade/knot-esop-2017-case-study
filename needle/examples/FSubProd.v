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
    (forall (x6 : (Index TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTmVar (weakenIndexTmVar x6 k) k0) = (weakenIndexTmVar x6 (appendHvl k k0)))).
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
    | tvar (X : (Index TyVar))
    | top 
    | tarrow (T1 : Ty) (T2 : Ty)
    | tall (T1 : Ty) (T2 : Ty)
    | tprod (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Pat : Set :=
    | pvar (T : Ty)
    | pprod (p1 : Pat) (p2 : Pat).
  Scheme ind_Pat := Induction for Pat Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index TmVar))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tabs (T : Ty) (t : Tm)
    | tapp (t : Tm) (T : Ty)
    | prod (t1 : Tm) (t2 : Tm)
    | lett (p : Pat) (t1 : Tm)
        (t2 : Tm).
  Scheme ind_Tm := Induction for Tm Sort Prop.
End Terms.

Section Functions.
  Fixpoint bindPat (p8 : Pat) {struct p8} :
  Hvl :=
    match p8 with
      | (pvar T) => (HS TmVar H0)
      | (pprod p1 p2) => (appendHvl (appendHvl H0 (bindPat p1)) (bindPat p2))
    end.
  Scheme ind_bindPat_Pat := Induction for Pat Sort Prop.
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
  Fixpoint tshiftIndex (c : (Cutoff TyVar)) (X7 : (Index TyVar)) {struct c} :
  (Index TyVar) :=
    match c with
      | (C0) => (IS X7)
      | (CS c) => match X7 with
        | (I0) => I0
        | (IS X7) => (IS (tshiftIndex c X7))
      end
    end.
  Fixpoint tshiftTy (c : (Cutoff TyVar)) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (tvar X7) => (tvar (tshiftIndex c X7))
      | (top) => (top)
      | (tarrow T12 T13) => (tarrow (tshiftTy c T12) (tshiftTy c T13))
      | (tall T14 T15) => (tall (tshiftTy c T14) (tshiftTy (CS c) T15))
      | (tprod T16 T17) => (tprod (tshiftTy c T16) (tshiftTy c T17))
    end.
  Fixpoint tshiftPat (c : (Cutoff TyVar)) (p9 : Pat) {struct p9} :
  Pat :=
    match p9 with
      | (pvar T12) => (pvar (tshiftTy c T12))
      | (pprod p10 p11) => (pprod (tshiftPat c p10) (tshiftPat (weakenCutoffTyVar c (appendHvl H0 (bindPat p10))) p11))
    end.
  Fixpoint shiftTm (c : (Cutoff TmVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var (shiftIndex c x6))
      | (abs T12 t8) => (abs T12 (shiftTm (CS c) t8))
      | (app t9 t10) => (app (shiftTm c t9) (shiftTm c t10))
      | (tabs T13 t11) => (tabs T13 (shiftTm c t11))
      | (tapp t12 T14) => (tapp (shiftTm c t12) T14)
      | (prod t13 t14) => (prod (shiftTm c t13) (shiftTm c t14))
      | (lett p9 t15 t16) => (lett p9 (shiftTm c t15) (shiftTm (weakenCutoffTmVar c (appendHvl H0 (bindPat p9))) t16))
    end.
  Fixpoint tshiftTm (c : (Cutoff TyVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var x6)
      | (abs T12 t8) => (abs (tshiftTy c T12) (tshiftTm c t8))
      | (app t9 t10) => (app (tshiftTm c t9) (tshiftTm c t10))
      | (tabs T13 t11) => (tabs (tshiftTy c T13) (tshiftTm (CS c) t11))
      | (tapp t12 T14) => (tapp (tshiftTm c t12) (tshiftTy c T14))
      | (prod t13 t14) => (prod (tshiftTm c t13) (tshiftTm c t14))
      | (lett p9 t15 t16) => (lett (tshiftPat c p9) (tshiftTm c t15) (tshiftTm (weakenCutoffTyVar c (appendHvl H0 (bindPat p9))) t16))
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
        (T12 : (Trace a)).
  
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
        | (IS x6) => (var x6)
      end
      | (XS TmVar d) => match x6 with
        | (I0) => (var I0)
        | (IS x6) => (shiftTm C0 (substIndex d s x6))
      end
      | (XS TyVar d) => (tshiftTm C0 (substIndex d s x6))
    end.
  Fixpoint tsubstIndex (d : (Trace TyVar)) (S0 : Ty) (X7 : (Index TyVar)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X7 with
        | (I0) => S0
        | (IS X7) => (tvar X7)
      end
      | (XS TmVar d) => (tsubstIndex d S0 X7)
      | (XS TyVar d) => match X7 with
        | (I0) => (tvar I0)
        | (IS X7) => (tshiftTy C0 (tsubstIndex d S0 X7))
      end
    end.
  Fixpoint tsubstTy (d : (Trace TyVar)) (S0 : Ty) (S1 : Ty) {struct S1} :
  Ty :=
    match S1 with
      | (tvar X7) => (tsubstIndex d S0 X7)
      | (top) => (top)
      | (tarrow T12 T13) => (tarrow (tsubstTy d S0 T12) (tsubstTy d S0 T13))
      | (tall T14 T15) => (tall (tsubstTy d S0 T14) (tsubstTy (weakenTrace d (HS TyVar H0)) S0 T15))
      | (tprod T16 T17) => (tprod (tsubstTy d S0 T16) (tsubstTy d S0 T17))
    end.
  Fixpoint tsubstPat (d : (Trace TyVar)) (S0 : Ty) (p9 : Pat) {struct p9} :
  Pat :=
    match p9 with
      | (pvar T12) => (pvar (tsubstTy d S0 T12))
      | (pprod p10 p11) => (pprod (tsubstPat d S0 p10) (tsubstPat (weakenTrace d (appendHvl H0 (bindPat p10))) S0 p11))
    end.
  Fixpoint substTm (d : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x6) => (substIndex d s x6)
      | (abs T12 t8) => (abs T12 (substTm (weakenTrace d (HS TmVar H0)) s t8))
      | (app t9 t10) => (app (substTm d s t9) (substTm d s t10))
      | (tabs T13 t11) => (tabs T13 (substTm (weakenTrace d (HS TyVar H0)) s t11))
      | (tapp t12 T14) => (tapp (substTm d s t12) T14)
      | (prod t13 t14) => (prod (substTm d s t13) (substTm d s t14))
      | (lett p9 t15 t16) => (lett p9 (substTm d s t15) (substTm (weakenTrace d (appendHvl H0 (bindPat p9))) s t16))
    end.
  Fixpoint tsubstTm (d : (Trace TyVar)) (S0 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var x6)
      | (abs T12 t8) => (abs (tsubstTy d S0 T12) (tsubstTm (weakenTrace d (HS TmVar H0)) S0 t8))
      | (app t9 t10) => (app (tsubstTm d S0 t9) (tsubstTm d S0 t10))
      | (tabs T13 t11) => (tabs (tsubstTy d S0 T13) (tsubstTm (weakenTrace d (HS TyVar H0)) S0 t11))
      | (tapp t12 T14) => (tapp (tsubstTm d S0 t12) (tsubstTy d S0 T14))
      | (prod t13 t14) => (prod (tsubstTm d S0 t13) (tsubstTm d S0 t14))
      | (lett p9 t15 t16) => (lett (tsubstPat d S0 p9) (tsubstTm d S0 t15) (tsubstTm (weakenTrace d (appendHvl H0 (bindPat p9))) S0 t16))
    end.
End Subst.

Global Hint Resolve (f_equal (tshiftPat C0)) : cong_shift0.
Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutoffTmVar_append weakenCutoffTyVar_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_tshift_bindPat  :
  (forall (p9 : Pat) ,
    (forall (c : (Cutoff TyVar)) ,
      ((bindPat (tshiftPat c p9)) = (bindPat p9)))).
Proof.
  apply_mutual_ind (ind_bindPat_Pat); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_tshift_bindPat : interaction.
 Hint Rewrite stability_tshift_bindPat : stability_shift.
Lemma stability_weaken_bindPat  :
  (forall (k : Hvl) (p10 : Pat) ,
    ((bindPat (weakenPat p10 k)) = (bindPat p10))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bindPat : interaction.
 Hint Rewrite stability_weaken_bindPat : stability_weaken.
Lemma stability_tsubst_bindPat  :
  (forall (p10 : Pat) ,
    (forall (d : (Trace TyVar)) (S0 : Ty) ,
      ((bindPat (tsubstPat d S0 p10)) = (bindPat p10)))).
Proof.
  apply_mutual_ind (ind_bindPat_Pat); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_tsubst_bindPat : interaction.
 Hint Rewrite stability_tsubst_bindPat : stability_subst.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x6 : (Index TmVar)) ,
      ((substIndex (weakenTrace X0 k) s (shiftIndex (weakenCutoffTmVar C0 k) x6)) = (var x6))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S1 : Ty) :
    (forall (k : Hvl) (X7 : (Index TyVar)) ,
      ((tsubstIndex (weakenTrace X0 k) S1 (tshiftIndex (weakenCutoffTyVar C0 k) X7)) = (tvar X7))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint tsubst0_tshift0_Ty_reflection_ind (S2 : Ty) (k : Hvl) (S1 : Ty) {struct S2} :
  ((tsubstTy (weakenTrace X0 k) S1 (tshiftTy (weakenCutoffTyVar C0 k) S2)) = S2) :=
    match S2 return ((tsubstTy (weakenTrace X0 k) S1 (tshiftTy (weakenCutoffTyVar C0 k) S2)) = S2) with
      | (tvar X7) => (tsubstIndex0_tshiftIndex0_reflection_ind S1 k X7)
      | (top) => eq_refl
      | (tarrow T12 T13) => (f_equal2 tarrow (tsubst0_tshift0_Ty_reflection_ind T12 k S1) (tsubst0_tshift0_Ty_reflection_ind T13 k S1))
      | (tall T12 T13) => (f_equal2 tall (tsubst0_tshift0_Ty_reflection_ind T12 k S1) (eq_trans (f_equal3 tsubstTy (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T13 (HS TyVar k) S1)))
      | (tprod T12 T13) => (f_equal2 tprod (tsubst0_tshift0_Ty_reflection_ind T12 k S1) (tsubst0_tshift0_Ty_reflection_ind T13 k S1))
    end.
  Fixpoint tsubst0_tshift0_Pat_reflection_ind (p11 : Pat) (k : Hvl) (S1 : Ty) {struct p11} :
  ((tsubstPat (weakenTrace X0 k) S1 (tshiftPat (weakenCutoffTyVar C0 k) p11)) = p11) :=
    match p11 return ((tsubstPat (weakenTrace X0 k) S1 (tshiftPat (weakenCutoffTyVar C0 k) p11)) = p11) with
      | (pvar T12) => (f_equal pvar (tsubst0_tshift0_Ty_reflection_ind T12 k S1))
      | (pprod p12 p13) => (f_equal2 pprod (tsubst0_tshift0_Pat_reflection_ind p12 k S1) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append TyVar X0 k (appendHvl H0 (bindPat p12)))) eq_refl (f_equal2 tshiftPat (weakenCutoffTyVar_append C0 k (appendHvl H0 (bindPat p12))) eq_refl)) (tsubst0_tshift0_Pat_reflection_ind p13 (appendHvl k (appendHvl H0 (bindPat p12))) S1)))
    end.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutoffTmVar C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutoffTmVar C0 k) s0)) = s0) with
      | (var x6) => (substIndex0_shiftIndex0_reflection_ind s k x6)
      | (abs T12 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t8 (HS TmVar k) s)))
      | (app t9 t10) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t9 k s) (subst0_shift0_Tm_reflection_ind t10 k s))
      | (tabs T12 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t8 (HS TyVar k) s)))
      | (tapp t8 T12) => (f_equal2 tapp (subst0_shift0_Tm_reflection_ind t8 k s) eq_refl)
      | (prod t9 t10) => (f_equal2 prod (subst0_shift0_Tm_reflection_ind t9 k s) (subst0_shift0_Tm_reflection_ind t10 k s))
      | (lett p11 t9 t10) => (f_equal3 lett eq_refl (subst0_shift0_Tm_reflection_ind t9 k s) (eq_trans (f_equal3 substTm (weakenTrace_append TmVar X0 k (appendHvl H0 (bindPat p11))) eq_refl (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bindPat p11))) eq_refl)) (subst0_shift0_Tm_reflection_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) s)))
    end.
  Fixpoint tsubst0_tshift0_Tm_reflection_ind (s : Tm) (k : Hvl) (S1 : Ty) {struct s} :
  ((tsubstTm (weakenTrace X0 k) S1 (tshiftTm (weakenCutoffTyVar C0 k) s)) = s) :=
    match s return ((tsubstTm (weakenTrace X0 k) S1 (tshiftTm (weakenCutoffTyVar C0 k) s)) = s) with
      | (var x6) => eq_refl
      | (abs T12 t8) => (f_equal2 abs (tsubst0_tshift0_Ty_reflection_ind T12 k S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t8 (HS TmVar k) S1)))
      | (app t9 t10) => (f_equal2 app (tsubst0_tshift0_Tm_reflection_ind t9 k S1) (tsubst0_tshift0_Tm_reflection_ind t10 k S1))
      | (tabs T12 t8) => (f_equal2 tabs (tsubst0_tshift0_Ty_reflection_ind T12 k S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t8 (HS TyVar k) S1)))
      | (tapp t8 T12) => (f_equal2 tapp (tsubst0_tshift0_Tm_reflection_ind t8 k S1) (tsubst0_tshift0_Ty_reflection_ind T12 k S1))
      | (prod t9 t10) => (f_equal2 prod (tsubst0_tshift0_Tm_reflection_ind t9 k S1) (tsubst0_tshift0_Tm_reflection_ind t10 k S1))
      | (lett p11 t9 t10) => (f_equal3 lett (tsubst0_tshift0_Pat_reflection_ind p11 k S1) (tsubst0_tshift0_Tm_reflection_ind t9 k S1) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append TyVar X0 k (appendHvl H0 (bindPat p11)))) eq_refl (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bindPat p11))) eq_refl)) (tsubst0_tshift0_Tm_reflection_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) S1)))
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
      (forall (k : Hvl) (c0 : (Cutoff TyVar)) (X7 : (Index TyVar)) ,
        ((tshiftIndex (weakenCutoffTyVar (CS c0) k) (tshiftIndex (weakenCutoffTyVar C0 k) X7)) = (tshiftIndex (weakenCutoffTyVar C0 k) (tshiftIndex (weakenCutoffTyVar c0 k) X7)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint tshift_tshift0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c0 : (Cutoff TyVar)) {struct S1} :
    ((tshiftTy (weakenCutoffTyVar (CS c0) k) (tshiftTy (weakenCutoffTyVar C0 k) S1)) = (tshiftTy (weakenCutoffTyVar C0 k) (tshiftTy (weakenCutoffTyVar c0 k) S1))) :=
      match S1 return ((tshiftTy (weakenCutoffTyVar (CS c0) k) (tshiftTy (weakenCutoffTyVar C0 k) S1)) = (tshiftTy (weakenCutoffTyVar C0 k) (tshiftTy (weakenCutoffTyVar c0 k) S1))) with
        | (tvar X7) => (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k c0 X7))
        | (top) => eq_refl
        | (tarrow T12 T13) => (f_equal2 tarrow (tshift_tshift0_Ty_comm_ind T12 k c0) (tshift_tshift0_Ty_comm_ind T13 k c0))
        | (tall T12 T13) => (f_equal2 tall (tshift_tshift0_Ty_comm_ind T12 k c0) (tshift_tshift0_Ty_comm_ind T13 (HS TyVar k) c0))
        | (tprod T12 T13) => (f_equal2 tprod (tshift_tshift0_Ty_comm_ind T12 k c0) (tshift_tshift0_Ty_comm_ind T13 k c0))
      end.
    Fixpoint tshift_tshift0_Pat_comm_ind (p11 : Pat) (k : Hvl) (c0 : (Cutoff TyVar)) {struct p11} :
    ((tshiftPat (weakenCutoffTyVar (CS c0) k) (tshiftPat (weakenCutoffTyVar C0 k) p11)) = (tshiftPat (weakenCutoffTyVar C0 k) (tshiftPat (weakenCutoffTyVar c0 k) p11))) :=
      match p11 return ((tshiftPat (weakenCutoffTyVar (CS c0) k) (tshiftPat (weakenCutoffTyVar C0 k) p11)) = (tshiftPat (weakenCutoffTyVar C0 k) (tshiftPat (weakenCutoffTyVar c0 k) p11))) with
        | (pvar T12) => (f_equal pvar (tshift_tshift0_Ty_comm_ind T12 k c0))
        | (pprod p12 p13) => (f_equal2 pprod (tshift_tshift0_Pat_comm_ind p12 k c0) (eq_trans (f_equal2 tshiftPat (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutoffTyVar_append (CS c0) k (appendHvl H0 (bindPat p12)))) (f_equal2 tshiftPat (weakenCutoffTyVar_append C0 k (appendHvl H0 (bindPat p12))) eq_refl)) (eq_trans (tshift_tshift0_Pat_comm_ind p13 (appendHvl k (appendHvl H0 (bindPat p12))) c0) (f_equal2 tshiftPat (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bindPat p12)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftPat (eq_sym (weakenCutoffTyVar_append c0 k (appendHvl H0 (bindPat p12)))) eq_refl)))))
      end.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff TmVar)) {struct s} :
    ((shiftTm (weakenCutoffTmVar (CS c0) k) (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (shiftTm (weakenCutoffTmVar c0 k) s))) :=
      match s return ((shiftTm (weakenCutoffTmVar (CS c0) k) (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (shiftTm (weakenCutoffTmVar c0 k) s))) with
        | (var x6) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c0 x6))
        | (abs T12 t8) => (f_equal2 abs eq_refl (shift_shift0_Tm_comm_ind t8 (HS TmVar k) c0))
        | (app t9 t10) => (f_equal2 app (shift_shift0_Tm_comm_ind t9 k c0) (shift_shift0_Tm_comm_ind t10 k c0))
        | (tabs T12 t8) => (f_equal2 tabs eq_refl (shift_shift0_Tm_comm_ind t8 (HS TyVar k) c0))
        | (tapp t8 T12) => (f_equal2 tapp (shift_shift0_Tm_comm_ind t8 k c0) eq_refl)
        | (prod t9 t10) => (f_equal2 prod (shift_shift0_Tm_comm_ind t9 k c0) (shift_shift0_Tm_comm_ind t10 k c0))
        | (lett p11 t9 t10) => (f_equal3 lett eq_refl (shift_shift0_Tm_comm_ind t9 k c0) (eq_trans (f_equal2 shiftTm (weakenCutoffTmVar_append (CS c0) k (appendHvl H0 (bindPat p11))) (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bindPat p11))) eq_refl)) (eq_trans (shift_shift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) c0) (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bindPat p11)))) (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append c0 k (appendHvl H0 (bindPat p11)))) eq_refl)))))
      end.
    Fixpoint shift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff TmVar)) {struct s} :
    ((shiftTm (weakenCutoffTmVar c0 k) (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (shiftTm (weakenCutoffTmVar c0 k) s))) :=
      match s return ((shiftTm (weakenCutoffTmVar c0 k) (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (shiftTm (weakenCutoffTmVar c0 k) s))) with
        | (var x6) => eq_refl
        | (abs T12 t8) => (f_equal2 abs eq_refl (shift_tshift0_Tm_comm_ind t8 (HS TmVar k) c0))
        | (app t9 t10) => (f_equal2 app (shift_tshift0_Tm_comm_ind t9 k c0) (shift_tshift0_Tm_comm_ind t10 k c0))
        | (tabs T12 t8) => (f_equal2 tabs eq_refl (shift_tshift0_Tm_comm_ind t8 (HS TyVar k) c0))
        | (tapp t8 T12) => (f_equal2 tapp (shift_tshift0_Tm_comm_ind t8 k c0) eq_refl)
        | (prod t9 t10) => (f_equal2 prod (shift_tshift0_Tm_comm_ind t9 k c0) (shift_tshift0_Tm_comm_ind t10 k c0))
        | (lett p11 t9 t10) => (f_equal3 lett eq_refl (shift_tshift0_Tm_comm_ind t9 k c0) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutoffTmVar_append c0 k (appendHvl H0 (bindPat p11)))) (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bindPat p11))) eq_refl)) (eq_trans (shift_tshift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) c0) (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bindPat p11)))) (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append c0 k (appendHvl H0 (bindPat p11)))) eq_refl)))))
      end.
    Fixpoint tshift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff TyVar)) {struct s} :
    ((tshiftTm (weakenCutoffTyVar c0 k) (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (tshiftTm (weakenCutoffTyVar c0 k) s))) :=
      match s return ((tshiftTm (weakenCutoffTyVar c0 k) (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (tshiftTm (weakenCutoffTyVar c0 k) s))) with
        | (var x6) => eq_refl
        | (abs T12 t8) => (f_equal2 abs eq_refl (tshift_shift0_Tm_comm_ind t8 (HS TmVar k) c0))
        | (app t9 t10) => (f_equal2 app (tshift_shift0_Tm_comm_ind t9 k c0) (tshift_shift0_Tm_comm_ind t10 k c0))
        | (tabs T12 t8) => (f_equal2 tabs eq_refl (tshift_shift0_Tm_comm_ind t8 (HS TyVar k) c0))
        | (tapp t8 T12) => (f_equal2 tapp (tshift_shift0_Tm_comm_ind t8 k c0) eq_refl)
        | (prod t9 t10) => (f_equal2 prod (tshift_shift0_Tm_comm_ind t9 k c0) (tshift_shift0_Tm_comm_ind t10 k c0))
        | (lett p11 t9 t10) => (f_equal3 lett eq_refl (tshift_shift0_Tm_comm_ind t9 k c0) (eq_trans (f_equal2 tshiftTm (weakenCutoffTyVar_append c0 k (appendHvl H0 (bindPat p11))) (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bindPat p11))) eq_refl)) (eq_trans (tshift_shift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) c0) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bindPat p11)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append c0 k (appendHvl H0 (bindPat p11)))) eq_refl)))))
      end.
    Fixpoint tshift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff TyVar)) {struct s} :
    ((tshiftTm (weakenCutoffTyVar (CS c0) k) (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (tshiftTm (weakenCutoffTyVar c0 k) s))) :=
      match s return ((tshiftTm (weakenCutoffTyVar (CS c0) k) (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (tshiftTm (weakenCutoffTyVar c0 k) s))) with
        | (var x6) => eq_refl
        | (abs T12 t8) => (f_equal2 abs (tshift_tshift0_Ty_comm_ind T12 k c0) (tshift_tshift0_Tm_comm_ind t8 (HS TmVar k) c0))
        | (app t9 t10) => (f_equal2 app (tshift_tshift0_Tm_comm_ind t9 k c0) (tshift_tshift0_Tm_comm_ind t10 k c0))
        | (tabs T12 t8) => (f_equal2 tabs (tshift_tshift0_Ty_comm_ind T12 k c0) (tshift_tshift0_Tm_comm_ind t8 (HS TyVar k) c0))
        | (tapp t8 T12) => (f_equal2 tapp (tshift_tshift0_Tm_comm_ind t8 k c0) (tshift_tshift0_Ty_comm_ind T12 k c0))
        | (prod t9 t10) => (f_equal2 prod (tshift_tshift0_Tm_comm_ind t9 k c0) (tshift_tshift0_Tm_comm_ind t10 k c0))
        | (lett p11 t9 t10) => (f_equal3 lett (tshift_tshift0_Pat_comm_ind p11 k c0) (tshift_tshift0_Tm_comm_ind t9 k c0) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutoffTyVar_append (CS c0) k (appendHvl H0 (bindPat p11)))) (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bindPat p11))) eq_refl)) (eq_trans (tshift_tshift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) c0) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bindPat p11)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append c0 k (appendHvl H0 (bindPat p11)))) eq_refl)))))
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
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((tshiftTy (weakenCutoffTyVar c0 k) (tsubstIndex (weakenTrace X0 k) S1 X7)) = (tsubstIndex (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftIndex (weakenCutoffTyVar (CS c0) k) X7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint tshift_tsubst0_Ty_comm_ind (S2 : Ty) (k : Hvl) (c0 : (Cutoff TyVar)) (S1 : Ty) {struct S2} :
    ((tshiftTy (weakenCutoffTyVar c0 k) (tsubstTy (weakenTrace X0 k) S1 S2)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTy (weakenCutoffTyVar (CS c0) k) S2))) :=
      match S2 return ((tshiftTy (weakenCutoffTyVar c0 k) (tsubstTy (weakenTrace X0 k) S1 S2)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTy (weakenCutoffTyVar (CS c0) k) S2))) with
        | (tvar X7) => (tshiftTy_tsubstIndex0_comm_ind c0 S1 k X7)
        | (top) => eq_refl
        | (tarrow T12 T13) => (f_equal2 tarrow (tshift_tsubst0_Ty_comm_ind T12 k c0 S1) (tshift_tsubst0_Ty_comm_ind T13 k c0 S1))
        | (tall T12 T13) => (f_equal2 tall (tshift_tsubst0_Ty_comm_ind T12 k c0 S1) (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T13 (HS TyVar k) c0 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (tprod T12 T13) => (f_equal2 tprod (tshift_tsubst0_Ty_comm_ind T12 k c0 S1) (tshift_tsubst0_Ty_comm_ind T13 k c0 S1))
      end.
    Fixpoint tshift_tsubst0_Pat_comm_ind (p11 : Pat) (k : Hvl) (c0 : (Cutoff TyVar)) (S1 : Ty) {struct p11} :
    ((tshiftPat (weakenCutoffTyVar c0 k) (tsubstPat (weakenTrace X0 k) S1 p11)) = (tsubstPat (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftPat (weakenCutoffTyVar (CS c0) k) p11))) :=
      match p11 return ((tshiftPat (weakenCutoffTyVar c0 k) (tsubstPat (weakenTrace X0 k) S1 p11)) = (tsubstPat (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftPat (weakenCutoffTyVar (CS c0) k) p11))) with
        | (pvar T12) => (f_equal pvar (tshift_tsubst0_Ty_comm_ind T12 k c0 S1))
        | (pprod p12 p13) => (f_equal2 pprod (tshift_tsubst0_Pat_comm_ind p12 k c0 S1) (eq_trans (f_equal2 tshiftPat (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutoffTyVar_append c0 k (appendHvl H0 (bindPat p12)))) (f_equal3 tsubstPat (weakenTrace_append TyVar X0 k (appendHvl H0 (bindPat p12))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Pat_comm_ind p13 (appendHvl k (appendHvl H0 (bindPat p12))) c0 S1) (f_equal3 tsubstPat (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bindPat p12)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftPat (eq_sym (weakenCutoffTyVar_append (CS c0) k (appendHvl H0 (bindPat p12)))) eq_refl)))))
      end.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c0 : (Cutoff TmVar)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutoffTmVar c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c0 s) (shiftTm (weakenCutoffTmVar (CS c0) k) s0))) :=
      match s0 return ((shiftTm (weakenCutoffTmVar c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c0 s) (shiftTm (weakenCutoffTmVar (CS c0) k) s0))) with
        | (var x6) => (shiftTm_substIndex0_comm_ind c0 s k x6)
        | (abs T12 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t8 (HS TmVar k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (app t9 t10) => (f_equal2 app (shift_subst0_Tm_comm_ind t9 k c0 s) (shift_subst0_Tm_comm_ind t10 k c0 s))
        | (tabs T12 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t8 (HS TyVar k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (tapp t8 T12) => (f_equal2 tapp (shift_subst0_Tm_comm_ind t8 k c0 s) eq_refl)
        | (prod t9 t10) => (f_equal2 prod (shift_subst0_Tm_comm_ind t9 k c0 s) (shift_subst0_Tm_comm_ind t10 k c0 s))
        | (lett p11 t9 t10) => (f_equal3 lett eq_refl (shift_subst0_Tm_comm_ind t9 k c0 s) (eq_trans (f_equal2 shiftTm (weakenCutoffTmVar_append c0 k (appendHvl H0 (bindPat p11))) (f_equal3 substTm (weakenTrace_append TmVar X0 k (appendHvl H0 (bindPat p11))) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bindPat p11)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append (CS c0) k (appendHvl H0 (bindPat p11)))) eq_refl)))))
      end.
    Fixpoint shift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff TmVar)) (S1 : Ty) {struct s} :
    ((shiftTm (weakenCutoffTmVar c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) S1 (shiftTm (weakenCutoffTmVar c0 k) s))) :=
      match s return ((shiftTm (weakenCutoffTmVar c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) S1 (shiftTm (weakenCutoffTmVar c0 k) s))) with
        | (var x6) => eq_refl
        | (abs T12 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t8 (HS TmVar k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (app t9 t10) => (f_equal2 app (shift_tsubst0_Tm_comm_ind t9 k c0 S1) (shift_tsubst0_Tm_comm_ind t10 k c0 S1))
        | (tabs T12 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t8 (HS TyVar k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (tapp t8 T12) => (f_equal2 tapp (shift_tsubst0_Tm_comm_ind t8 k c0 S1) eq_refl)
        | (prod t9 t10) => (f_equal2 prod (shift_tsubst0_Tm_comm_ind t9 k c0 S1) (shift_tsubst0_Tm_comm_ind t10 k c0 S1))
        | (lett p11 t9 t10) => (f_equal3 lett eq_refl (shift_tsubst0_Tm_comm_ind t9 k c0 S1) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutoffTmVar_append c0 k (appendHvl H0 (bindPat p11)))) (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (appendHvl H0 (bindPat p11))) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bindPat p11)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append c0 k (appendHvl H0 (bindPat p11)))) eq_refl)))))
      end.
    Fixpoint tshift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c0 : (Cutoff TyVar)) (s : Tm) {struct s0} :
    ((tshiftTm (weakenCutoffTyVar c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c0 s) (tshiftTm (weakenCutoffTyVar c0 k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffTyVar c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c0 s) (tshiftTm (weakenCutoffTyVar c0 k) s0))) with
        | (var x6) => (tshiftTm_substIndex0_comm_ind c0 s k x6)
        | (abs T12 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t8 (HS TmVar k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (app t9 t10) => (f_equal2 app (tshift_subst0_Tm_comm_ind t9 k c0 s) (tshift_subst0_Tm_comm_ind t10 k c0 s))
        | (tabs T12 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t8 (HS TyVar k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (tapp t8 T12) => (f_equal2 tapp (tshift_subst0_Tm_comm_ind t8 k c0 s) eq_refl)
        | (prod t9 t10) => (f_equal2 prod (tshift_subst0_Tm_comm_ind t9 k c0 s) (tshift_subst0_Tm_comm_ind t10 k c0 s))
        | (lett p11 t9 t10) => (f_equal3 lett eq_refl (tshift_subst0_Tm_comm_ind t9 k c0 s) (eq_trans (f_equal2 tshiftTm (weakenCutoffTyVar_append c0 k (appendHvl H0 (bindPat p11))) (f_equal3 substTm (weakenTrace_append TmVar X0 k (appendHvl H0 (bindPat p11))) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) c0 s) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bindPat p11)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append c0 k (appendHvl H0 (bindPat p11)))) eq_refl)))))
      end.
    Fixpoint tshift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff TyVar)) (S1 : Ty) {struct s} :
    ((tshiftTm (weakenCutoffTyVar c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTm (weakenCutoffTyVar (CS c0) k) s))) :=
      match s return ((tshiftTm (weakenCutoffTyVar c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTm (weakenCutoffTyVar (CS c0) k) s))) with
        | (var x6) => eq_refl
        | (abs T12 t8) => (f_equal2 abs (tshift_tsubst0_Ty_comm_ind T12 k c0 S1) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t8 (HS TmVar k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (app t9 t10) => (f_equal2 app (tshift_tsubst0_Tm_comm_ind t9 k c0 S1) (tshift_tsubst0_Tm_comm_ind t10 k c0 S1))
        | (tabs T12 t8) => (f_equal2 tabs (tshift_tsubst0_Ty_comm_ind T12 k c0 S1) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t8 (HS TyVar k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (tapp t8 T12) => (f_equal2 tapp (tshift_tsubst0_Tm_comm_ind t8 k c0 S1) (tshift_tsubst0_Ty_comm_ind T12 k c0 S1))
        | (prod t9 t10) => (f_equal2 prod (tshift_tsubst0_Tm_comm_ind t9 k c0 S1) (tshift_tsubst0_Tm_comm_ind t10 k c0 S1))
        | (lett p11 t9 t10) => (f_equal3 lett (tshift_tsubst0_Pat_comm_ind p11 k c0 S1) (tshift_tsubst0_Tm_comm_ind t9 k c0 S1) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutoffTyVar_append c0 k (appendHvl H0 (bindPat p11)))) (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (appendHvl H0 (bindPat p11))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) c0 S1) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bindPat p11)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append (CS c0) k (appendHvl H0 (bindPat p11)))) eq_refl)))))
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
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((tsubstIndex (weakenTrace (XS TmVar d0) k) S1 X7) = (tsubstIndex (weakenTrace d0 k) S1 X7))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d0 : (Trace TyVar)) (S1 : Ty) :
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((tsubstIndex (weakenTrace (XS TyVar d0) k) S1 (tshiftIndex (weakenCutoffTyVar C0 k) X7)) = (tshiftTy (weakenCutoffTyVar C0 k) (tsubstIndex (weakenTrace d0 k) S1 X7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint tsubst_tshift0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) {struct S2} :
    ((tsubstTy (weakenTrace (XS TyVar d0) k) S1 (tshiftTy (weakenCutoffTyVar C0 k) S2)) = (tshiftTy (weakenCutoffTyVar C0 k) (tsubstTy (weakenTrace d0 k) S1 S2))) :=
      match S2 return ((tsubstTy (weakenTrace (XS TyVar d0) k) S1 (tshiftTy (weakenCutoffTyVar C0 k) S2)) = (tshiftTy (weakenCutoffTyVar C0 k) (tsubstTy (weakenTrace d0 k) S1 S2))) with
        | (tvar X7) => (tsubstIndex_tshiftTy0_comm_ind d0 S1 k X7)
        | (top) => eq_refl
        | (tarrow T12 T13) => (f_equal2 tarrow (tsubst_tshift0_Ty_comm_ind T12 k d0 S1) (tsubst_tshift0_Ty_comm_ind T13 k d0 S1))
        | (tall T12 T13) => (f_equal2 tall (tsubst_tshift0_Ty_comm_ind T12 k d0 S1) (eq_trans (f_equal3 tsubstTy (weakenTrace_append TyVar (XS TyVar d0) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T13 (HS TyVar k) d0 S1) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar d0 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (tprod T12 T13) => (f_equal2 tprod (tsubst_tshift0_Ty_comm_ind T12 k d0 S1) (tsubst_tshift0_Ty_comm_ind T13 k d0 S1))
      end.
    Fixpoint tsubst_tshift0_Pat_comm_ind (p11 : Pat) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) {struct p11} :
    ((tsubstPat (weakenTrace (XS TyVar d0) k) S1 (tshiftPat (weakenCutoffTyVar C0 k) p11)) = (tshiftPat (weakenCutoffTyVar C0 k) (tsubstPat (weakenTrace d0 k) S1 p11))) :=
      match p11 return ((tsubstPat (weakenTrace (XS TyVar d0) k) S1 (tshiftPat (weakenCutoffTyVar C0 k) p11)) = (tshiftPat (weakenCutoffTyVar C0 k) (tsubstPat (weakenTrace d0 k) S1 p11))) with
        | (pvar T12) => (f_equal pvar (tsubst_tshift0_Ty_comm_ind T12 k d0 S1))
        | (pprod p12 p13) => (f_equal2 pprod (tsubst_tshift0_Pat_comm_ind p12 k d0 S1) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append TyVar (XS TyVar d0) k (appendHvl H0 (bindPat p12)))) eq_refl (f_equal2 tshiftPat (weakenCutoffTyVar_append C0 k (appendHvl H0 (bindPat p12))) eq_refl)) (eq_trans (tsubst_tshift0_Pat_comm_ind p13 (appendHvl k (appendHvl H0 (bindPat p12))) d0 S1) (f_equal2 tshiftPat (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bindPat p12)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstPat (eq_sym (weakenTrace_append TyVar d0 k (appendHvl H0 (bindPat p12)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace TmVar)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS TmVar d0) k) s (shiftTm (weakenCutoffTmVar C0 k) s0)) = (shiftTm (weakenCutoffTmVar C0 k) (substTm (weakenTrace d0 k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS TmVar d0) k) s (shiftTm (weakenCutoffTmVar C0 k) s0)) = (shiftTm (weakenCutoffTmVar C0 k) (substTm (weakenTrace d0 k) s s0))) with
        | (var x6) => (substIndex_shiftTm0_comm_ind d0 s k x6)
        | (abs T12 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar (XS TmVar d0) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t8 (HS TmVar k) d0 s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d0 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (subst_shift0_Tm_comm_ind t9 k d0 s) (subst_shift0_Tm_comm_ind t10 k d0 s))
        | (tabs T12 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar (XS TmVar d0) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t8 (HS TyVar k) d0 s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d0 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (tapp t8 T12) => (f_equal2 tapp (subst_shift0_Tm_comm_ind t8 k d0 s) eq_refl)
        | (prod t9 t10) => (f_equal2 prod (subst_shift0_Tm_comm_ind t9 k d0 s) (subst_shift0_Tm_comm_ind t10 k d0 s))
        | (lett p11 t9 t10) => (f_equal3 lett eq_refl (subst_shift0_Tm_comm_ind t9 k d0 s) (eq_trans (f_equal3 substTm (weakenTrace_append TmVar (XS TmVar d0) k (appendHvl H0 (bindPat p11))) eq_refl (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bindPat p11))) eq_refl)) (eq_trans (subst_shift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) d0 s) (f_equal2 shiftTm (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bindPat p11)))) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d0 k (appendHvl H0 (bindPat p11)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace TmVar)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS TyVar d0) k) s (tshiftTm (weakenCutoffTyVar C0 k) s0)) = (tshiftTm (weakenCutoffTyVar C0 k) (substTm (weakenTrace d0 k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS TyVar d0) k) s (tshiftTm (weakenCutoffTyVar C0 k) s0)) = (tshiftTm (weakenCutoffTyVar C0 k) (substTm (weakenTrace d0 k) s s0))) with
        | (var x6) => (substIndex_tshiftTm0_comm_ind d0 s k x6)
        | (abs T12 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar (XS TyVar d0) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t8 (HS TmVar k) d0 s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d0 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (subst_tshift0_Tm_comm_ind t9 k d0 s) (subst_tshift0_Tm_comm_ind t10 k d0 s))
        | (tabs T12 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar (XS TyVar d0) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t8 (HS TyVar k) d0 s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d0 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (tapp t8 T12) => (f_equal2 tapp (subst_tshift0_Tm_comm_ind t8 k d0 s) eq_refl)
        | (prod t9 t10) => (f_equal2 prod (subst_tshift0_Tm_comm_ind t9 k d0 s) (subst_tshift0_Tm_comm_ind t10 k d0 s))
        | (lett p11 t9 t10) => (f_equal3 lett eq_refl (subst_tshift0_Tm_comm_ind t9 k d0 s) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append TmVar (XS TyVar d0) k (appendHvl H0 (bindPat p11)))) eq_refl (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bindPat p11))) eq_refl)) (eq_trans (subst_tshift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) d0 s) (f_equal2 tshiftTm (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bindPat p11)))) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar d0 k (appendHvl H0 (bindPat p11)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d0 k) S1 (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) :=
      match s return ((tsubstTm (weakenTrace d0 k) S1 (shiftTm (weakenCutoffTmVar C0 k) s)) = (shiftTm (weakenCutoffTmVar C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) with
        | (var x6) => eq_refl
        | (abs T12 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t8 (HS TmVar k) d0 S1) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (tsubst_shift0_Tm_comm_ind t9 k d0 S1) (tsubst_shift0_Tm_comm_ind t10 k d0 S1))
        | (tabs T12 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t8 (HS TyVar k) d0 S1) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (tapp t8 T12) => (f_equal2 tapp (tsubst_shift0_Tm_comm_ind t8 k d0 S1) eq_refl)
        | (prod t9 t10) => (f_equal2 prod (tsubst_shift0_Tm_comm_ind t9 k d0 S1) (tsubst_shift0_Tm_comm_ind t10 k d0 S1))
        | (lett p11 t9 t10) => (f_equal3 lett eq_refl (tsubst_shift0_Tm_comm_ind t9 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (appendHvl H0 (bindPat p11))) eq_refl (f_equal2 shiftTm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bindPat p11))) eq_refl)) (eq_trans (tsubst_shift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) d0 S1) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bindPat p11)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (appendHvl H0 (bindPat p11)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS TyVar d0) k) S1 (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) :=
      match s return ((tsubstTm (weakenTrace (XS TyVar d0) k) S1 (tshiftTm (weakenCutoffTyVar C0 k) s)) = (tshiftTm (weakenCutoffTyVar C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) with
        | (var x6) => eq_refl
        | (abs T12 t8) => (f_equal2 abs (tsubst_tshift0_Ty_comm_ind T12 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar (XS TyVar d0) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t8 (HS TmVar k) d0 S1) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (tsubst_tshift0_Tm_comm_ind t9 k d0 S1) (tsubst_tshift0_Tm_comm_ind t10 k d0 S1))
        | (tabs T12 t8) => (f_equal2 tabs (tsubst_tshift0_Ty_comm_ind T12 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar (XS TyVar d0) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t8 (HS TyVar k) d0 S1) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (tapp t8 T12) => (f_equal2 tapp (tsubst_tshift0_Tm_comm_ind t8 k d0 S1) (tsubst_tshift0_Ty_comm_ind T12 k d0 S1))
        | (prod t9 t10) => (f_equal2 prod (tsubst_tshift0_Tm_comm_ind t9 k d0 S1) (tsubst_tshift0_Tm_comm_ind t10 k d0 S1))
        | (lett p11 t9 t10) => (f_equal3 lett (tsubst_tshift0_Pat_comm_ind p11 k d0 S1) (tsubst_tshift0_Tm_comm_ind t9 k d0 S1) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append TyVar (XS TyVar d0) k (appendHvl H0 (bindPat p11)))) eq_refl (f_equal2 tshiftTm (weakenCutoffTyVar_append C0 k (appendHvl H0 (bindPat p11))) eq_refl)) (eq_trans (tsubst_tshift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) d0 S1) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffTyVar_append C0 k (appendHvl H0 (bindPat p11)))) (f_equal2 weakenCutoffTyVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (appendHvl H0 (bindPat p11)))) eq_refl eq_refl)))))
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
        | (tvar X7) => (tsubstIndex_shiftTy0_comm_ind d0 S1 k X7)
        | (top) => eq_refl
        | (tarrow T12 T13) => (f_equal2 tarrow (tsubst_TmVar_Ty_ind T12 k d0 S1) (tsubst_TmVar_Ty_ind T13 k d0 S1))
        | (tall T12 T13) => (f_equal2 tall (tsubst_TmVar_Ty_ind T12 k d0 S1) (eq_trans (f_equal3 tsubstTy (weakenTrace_append TyVar (XS TmVar d0) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (tsubst_TmVar_Ty_ind T13 (HS TyVar k) d0 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar d0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (tprod T12 T13) => (f_equal2 tprod (tsubst_TmVar_Ty_ind T12 k d0 S1) (tsubst_TmVar_Ty_ind T13 k d0 S1))
      end.
    Fixpoint tsubst_TmVar_Pat_ind (p11 : Pat) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) {struct p11} :
    ((tsubstPat (weakenTrace (XS TmVar d0) k) S1 p11) = (tsubstPat (weakenTrace d0 k) S1 p11)) :=
      match p11 return ((tsubstPat (weakenTrace (XS TmVar d0) k) S1 p11) = (tsubstPat (weakenTrace d0 k) S1 p11)) with
        | (pvar T12) => (f_equal pvar (tsubst_TmVar_Ty_ind T12 k d0 S1))
        | (pprod p12 p13) => (f_equal2 pprod (tsubst_TmVar_Pat_ind p12 k d0 S1) (eq_trans (f_equal3 tsubstPat (weakenTrace_append TyVar (XS TmVar d0) k (appendHvl H0 (bindPat p12))) eq_refl eq_refl) (eq_trans (tsubst_TmVar_Pat_ind p13 (appendHvl k (appendHvl H0 (bindPat p12))) d0 S1) (f_equal3 tsubstPat (eq_sym (weakenTrace_append TyVar d0 k (appendHvl H0 (bindPat p12)))) eq_refl eq_refl))))
      end.
    Fixpoint tsubst_TmVar_Tm_ind (s : Tm) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS TmVar d0) k) S1 s) = (tsubstTm (weakenTrace d0 k) S1 s)) :=
      match s return ((tsubstTm (weakenTrace (XS TmVar d0) k) S1 s) = (tsubstTm (weakenTrace d0 k) S1 s)) with
        | (var x6) => eq_refl
        | (abs T12 t8) => (f_equal2 abs (tsubst_TmVar_Ty_ind T12 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar (XS TmVar d0) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (tsubst_TmVar_Tm_ind t8 (HS TmVar k) d0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TmVar H0))) eq_refl eq_refl))))
        | (app t9 t10) => (f_equal2 app (tsubst_TmVar_Tm_ind t9 k d0 S1) (tsubst_TmVar_Tm_ind t10 k d0 S1))
        | (tabs T12 t8) => (f_equal2 tabs (tsubst_TmVar_Ty_ind T12 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar (XS TmVar d0) k (HS TyVar H0)) eq_refl eq_refl) (eq_trans (tsubst_TmVar_Tm_ind t8 (HS TyVar k) d0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TyVar H0))) eq_refl eq_refl))))
        | (tapp t8 T12) => (f_equal2 tapp (tsubst_TmVar_Tm_ind t8 k d0 S1) (tsubst_TmVar_Ty_ind T12 k d0 S1))
        | (prod t9 t10) => (f_equal2 prod (tsubst_TmVar_Tm_ind t9 k d0 S1) (tsubst_TmVar_Tm_ind t10 k d0 S1))
        | (lett p11 t9 t10) => (f_equal3 lett (tsubst_TmVar_Pat_ind p11 k d0 S1) (tsubst_TmVar_Tm_ind t9 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar (XS TmVar d0) k (appendHvl H0 (bindPat p11))) eq_refl eq_refl) (eq_trans (tsubst_TmVar_Tm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) d0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (appendHvl H0 (bindPat p11)))) eq_refl eq_refl))))
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
      (forall (k : Hvl) (X7 : (Index TyVar)) ,
        ((tsubstTy (weakenTrace d0 k) S1 (tsubstIndex (weakenTrace X0 k) S2 X7)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstIndex (weakenTrace (XS TyVar d0) k) S1 X7)))).
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
        | (tvar X7) => (tsubstTy_tsubstIndex0_commright_ind d0 S1 S2 k X7)
        | (top) => eq_refl
        | (tarrow T12 T13) => (f_equal2 tarrow (tsubst_tsubst0_Ty_comm_ind T12 k d0 S1 S2) (tsubst_tsubst0_Ty_comm_ind T13 k d0 S1 S2))
        | (tall T12 T13) => (f_equal2 tall (tsubst_tsubst0_Ty_comm_ind T12 k d0 S1 S2) (eq_trans (f_equal3 tsubstTy (weakenTrace_append TyVar d0 k (HS TyVar H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T13 (HS TyVar k) d0 S1 S2) (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append TyVar (XS TyVar d0) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (tprod T12 T13) => (f_equal2 tprod (tsubst_tsubst0_Ty_comm_ind T12 k d0 S1 S2) (tsubst_tsubst0_Ty_comm_ind T13 k d0 S1 S2))
      end.
    Fixpoint tsubst_tsubst0_Pat_comm_ind (p11 : Pat) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) {struct p11} :
    ((tsubstPat (weakenTrace d0 k) S1 (tsubstPat (weakenTrace X0 k) S2 p11)) = (tsubstPat (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstPat (weakenTrace (XS TyVar d0) k) S1 p11))) :=
      match p11 return ((tsubstPat (weakenTrace d0 k) S1 (tsubstPat (weakenTrace X0 k) S2 p11)) = (tsubstPat (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstPat (weakenTrace (XS TyVar d0) k) S1 p11))) with
        | (pvar T12) => (f_equal pvar (tsubst_tsubst0_Ty_comm_ind T12 k d0 S1 S2))
        | (pprod p12 p13) => (f_equal2 pprod (tsubst_tsubst0_Pat_comm_ind p12 k d0 S1 S2) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append TyVar d0 k (appendHvl H0 (bindPat p12)))) eq_refl (f_equal3 tsubstPat (weakenTrace_append TyVar X0 k (appendHvl H0 (bindPat p12))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Pat_comm_ind p13 (appendHvl k (appendHvl H0 (bindPat p12))) d0 S1 S2) (f_equal3 tsubstPat (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bindPat p12)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstPat (eq_sym (weakenTrace_append TyVar (XS TyVar d0) k (appendHvl H0 (bindPat p12)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d0 : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d0 k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d0 s s0) (substTm (weakenTrace (XS TmVar d0) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d0 k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d0 s s0) (substTm (weakenTrace (XS TmVar d0) k) s s1))) with
        | (var x6) => (substTm_substIndex0_commright_ind d0 s s0 k x6)
        | (abs T12 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar d0 k (HS TmVar H0)) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t8 (HS TmVar k) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TmVar d0) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (subst_subst0_Tm_comm_ind t9 k d0 s s0) (subst_subst0_Tm_comm_ind t10 k d0 s s0))
        | (tabs T12 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar d0 k (HS TyVar H0)) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t8 (HS TyVar k) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TmVar d0) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (tapp t8 T12) => (f_equal2 tapp (subst_subst0_Tm_comm_ind t8 k d0 s s0) eq_refl)
        | (prod t9 t10) => (f_equal2 prod (subst_subst0_Tm_comm_ind t9 k d0 s s0) (subst_subst0_Tm_comm_ind t10 k d0 s s0))
        | (lett p11 t9 t10) => (f_equal3 lett eq_refl (subst_subst0_Tm_comm_ind t9 k d0 s s0) (eq_trans (f_equal3 substTm (weakenTrace_append TmVar d0 k (appendHvl H0 (bindPat p11))) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (appendHvl H0 (bindPat p11))) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bindPat p11)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TmVar d0) k (appendHvl H0 (bindPat p11)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace TmVar)) (s : Tm) (S1 : Ty) {struct s0} :
    ((substTm (weakenTrace d0 k) s (tsubstTm (weakenTrace X0 k) S1 s0)) = (tsubstTm (weakenTrace X0 k) S1 (substTm (weakenTrace (XS TyVar d0) k) s s0))) :=
      match s0 return ((substTm (weakenTrace d0 k) s (tsubstTm (weakenTrace X0 k) S1 s0)) = (tsubstTm (weakenTrace X0 k) S1 (substTm (weakenTrace (XS TyVar d0) k) s s0))) with
        | (var x6) => (substTy_tsubstIndex0_commleft_ind d0 s S1 k x6)
        | (abs T12 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar d0 k (HS TmVar H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t8 (HS TmVar k) d0 s S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TyVar d0) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (subst_tsubst0_Tm_comm_ind t9 k d0 s S1) (subst_tsubst0_Tm_comm_ind t10 k d0 s S1))
        | (tabs T12 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append TmVar d0 k (HS TyVar H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t8 (HS TyVar k) d0 s S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TyVar d0) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (tapp t8 T12) => (f_equal2 tapp (subst_tsubst0_Tm_comm_ind t8 k d0 s S1) eq_refl)
        | (prod t9 t10) => (f_equal2 prod (subst_tsubst0_Tm_comm_ind t9 k d0 s S1) (subst_tsubst0_Tm_comm_ind t10 k d0 s S1))
        | (lett p11 t9 t10) => (f_equal3 lett eq_refl (subst_tsubst0_Tm_comm_ind t9 k d0 s S1) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append TmVar d0 k (appendHvl H0 (bindPat p11)))) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (appendHvl H0 (bindPat p11))) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) d0 s S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bindPat p11)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append TmVar (XS TyVar d0) k (appendHvl H0 (bindPat p11)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) (s : Tm) {struct s0} :
    ((tsubstTm (weakenTrace d0 k) S1 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d0 S1 s) (tsubstTm (weakenTrace d0 k) S1 s0))) :=
      match s0 return ((tsubstTm (weakenTrace d0 k) S1 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d0 S1 s) (tsubstTm (weakenTrace d0 k) S1 s0))) with
        | (var x6) => (tsubstTm_substIndex0_commright_ind d0 S1 s k x6)
        | (abs T12 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (HS TmVar H0)) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t8 (HS TmVar k) d0 S1 s) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (tsubst_subst0_Tm_comm_ind t9 k d0 S1 s) (tsubst_subst0_Tm_comm_ind t10 k d0 S1 s))
        | (tabs T12 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (HS TyVar H0)) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t8 (HS TyVar k) d0 S1 s) (f_equal3 substTm (eq_sym (weakenTrace_append TmVar X0 k (HS TyVar H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (HS TyVar H0))) eq_refl eq_refl)))))
        | (tapp t8 T12) => (f_equal2 tapp (tsubst_subst0_Tm_comm_ind t8 k d0 S1 s) eq_refl)
        | (prod t9 t10) => (f_equal2 prod (tsubst_subst0_Tm_comm_ind t9 k d0 S1 s) (tsubst_subst0_Tm_comm_ind t10 k d0 S1 s))
        | (lett p11 t9 t10) => (f_equal3 lett eq_refl (tsubst_subst0_Tm_comm_ind t9 k d0 S1 s) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (appendHvl H0 (bindPat p11))) eq_refl (f_equal3 substTm (weakenTrace_append TmVar X0 k (appendHvl H0 (bindPat p11))) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) d0 S1 s) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bindPat p11)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar d0 k (appendHvl H0 (bindPat p11)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace TyVar)) (S1 : Ty) (S2 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d0 k) S1 (tsubstTm (weakenTrace X0 k) S2 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstTm (weakenTrace (XS TyVar d0) k) S1 s))) :=
      match s return ((tsubstTm (weakenTrace d0 k) S1 (tsubstTm (weakenTrace X0 k) S2 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstTm (weakenTrace (XS TyVar d0) k) S1 s))) with
        | (var x6) => eq_refl
        | (abs T12 t8) => (f_equal2 abs (tsubst_tsubst0_Ty_comm_ind T12 k d0 S1 S2) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (HS TmVar H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t8 (HS TmVar k) d0 S1 S2) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TmVar H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar (XS TyVar d0) k (HS TmVar H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (tsubst_tsubst0_Tm_comm_ind t9 k d0 S1 S2) (tsubst_tsubst0_Tm_comm_ind t10 k d0 S1 S2))
        | (tabs T12 t8) => (f_equal2 tabs (tsubst_tsubst0_Ty_comm_ind T12 k d0 S1 S2) (eq_trans (f_equal3 tsubstTm (weakenTrace_append TyVar d0 k (HS TyVar H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (HS TyVar H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t8 (HS TyVar k) d0 S1 S2) (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar X0 k (HS TyVar H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar (XS TyVar d0) k (HS TyVar H0))) eq_refl eq_refl)))))
        | (tapp t8 T12) => (f_equal2 tapp (tsubst_tsubst0_Tm_comm_ind t8 k d0 S1 S2) (tsubst_tsubst0_Ty_comm_ind T12 k d0 S1 S2))
        | (prod t9 t10) => (f_equal2 prod (tsubst_tsubst0_Tm_comm_ind t9 k d0 S1 S2) (tsubst_tsubst0_Tm_comm_ind t10 k d0 S1 S2))
        | (lett p11 t9 t10) => (f_equal3 lett (tsubst_tsubst0_Pat_comm_ind p11 k d0 S1 S2) (tsubst_tsubst0_Tm_comm_ind t9 k d0 S1 S2) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append TyVar d0 k (appendHvl H0 (bindPat p11)))) eq_refl (f_equal3 tsubstTm (weakenTrace_append TyVar X0 k (appendHvl H0 (bindPat p11))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p11))) d0 S1 S2) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append TyVar X0 k (appendHvl H0 (bindPat p11)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append TyVar (XS TyVar d0) k (appendHvl H0 (bindPat p11)))) eq_refl eq_refl)))))
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
    | wfTy_tvar
        (X7 : (Index TyVar))
        (wfi : (wfindex k X7)) :
        (wfTy k (tvar X7))
    | wfTy_top : (wfTy k (top))
    | wfTy_tarrow {T12 : Ty}
        (wf : (wfTy k T12)) {T13 : Ty}
        (wf0 : (wfTy k T13)) :
        (wfTy k (tarrow T12 T13))
    | wfTy_tall {T14 : Ty}
        (wf : (wfTy k T14)) {T15 : Ty}
        (wf0 : (wfTy (HS TyVar k) T15))
        : (wfTy k (tall T14 T15))
    | wfTy_tprod {T16 : Ty}
        (wf : (wfTy k T16)) {T17 : Ty}
        (wf0 : (wfTy k T17)) :
        (wfTy k (tprod T16 T17)).
  Inductive wfPat (k : Hvl) : Pat -> Prop :=
    | wfPat_pvar {T12 : Ty}
        (wf : (wfTy k T12)) :
        (wfPat k (pvar T12))
    | wfPat_pprod {p11 : Pat}
        (wf : (wfPat k p11)) {p12 : Pat}
        (wf0 : (wfPat (appendHvl k (appendHvl H0 (bindPat p11))) p12))
        : (wfPat k (pprod p11 p12)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var
        (x6 : (Index TmVar))
        (wfi : (wfindex k x6)) :
        (wfTm k (var x6))
    | wfTm_abs {T12 : Ty}
        (wf : (wfTy k T12)) {t8 : Tm}
        (wf0 : (wfTm (HS TmVar k) t8)) :
        (wfTm k (abs T12 t8))
    | wfTm_app {t9 : Tm}
        (wf : (wfTm k t9)) {t10 : Tm}
        (wf0 : (wfTm k t10)) :
        (wfTm k (app t9 t10))
    | wfTm_tabs {T13 : Ty}
        (wf : (wfTy k T13)) {t11 : Tm}
        (wf0 : (wfTm (HS TyVar k) t11))
        : (wfTm k (tabs T13 t11))
    | wfTm_tapp {t12 : Tm}
        (wf : (wfTm k t12)) {T14 : Ty}
        (wf0 : (wfTy k T14)) :
        (wfTm k (tapp t12 T14))
    | wfTm_prod {t13 : Tm}
        (wf : (wfTm k t13)) {t14 : Tm}
        (wf0 : (wfTm k t14)) :
        (wfTm k (prod t13 t14))
    | wfTm_lett {p11 : Pat}
        (wf : (wfPat k p11)) {t15 : Tm}
        (wf0 : (wfTm k t15)) {t16 : Tm}
        (wf1 : (wfTm (appendHvl k (appendHvl H0 (bindPat p11))) t16))
        : (wfTm k (lett p11 t15 t16)).
  Definition inversion_wfTy_tvar_1 (k : Hvl) (X : (Index TyVar)) (H27 : (wfTy k (tvar X))) : (wfindex k X) := match H27 in (wfTy _ S1) return match S1 return Prop with
    | (tvar X) => (wfindex k X)
    | _ => True
  end with
    | (wfTy_tvar X H1) => H1
    | _ => I
  end.
  Definition inversion_wfTy_tarrow_0 (k1 : Hvl) (T1 : Ty) (T2 : Ty) (H29 : (wfTy k1 (tarrow T1 T2))) : (wfTy k1 T1) := match H29 in (wfTy _ S3) return match S3 return Prop with
    | (tarrow T1 T2) => (wfTy k1 T1)
    | _ => True
  end with
    | (wfTy_tarrow T1 H2 T2 H3) => H2
    | _ => I
  end.
  Definition inversion_wfTy_tarrow_1 (k1 : Hvl) (T1 : Ty) (T2 : Ty) (H29 : (wfTy k1 (tarrow T1 T2))) : (wfTy k1 T2) := match H29 in (wfTy _ S3) return match S3 return Prop with
    | (tarrow T1 T2) => (wfTy k1 T2)
    | _ => True
  end with
    | (wfTy_tarrow T1 H2 T2 H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_tall_1 (k2 : Hvl) (T1 : Ty) (T2 : Ty) (H30 : (wfTy k2 (tall T1 T2))) : (wfTy k2 T1) := match H30 in (wfTy _ S4) return match S4 return Prop with
    | (tall T1 T2) => (wfTy k2 T1)
    | _ => True
  end with
    | (wfTy_tall T1 H4 T2 H5) => H4
    | _ => I
  end.
  Definition inversion_wfTy_tall_2 (k2 : Hvl) (T1 : Ty) (T2 : Ty) (H30 : (wfTy k2 (tall T1 T2))) : (wfTy (HS TyVar k2) T2) := match H30 in (wfTy _ S4) return match S4 return Prop with
    | (tall T1 T2) => (wfTy (HS TyVar k2) T2)
    | _ => True
  end with
    | (wfTy_tall T1 H4 T2 H5) => H5
    | _ => I
  end.
  Definition inversion_wfTy_tprod_0 (k3 : Hvl) (T1 : Ty) (T2 : Ty) (H31 : (wfTy k3 (tprod T1 T2))) : (wfTy k3 T1) := match H31 in (wfTy _ S5) return match S5 return Prop with
    | (tprod T1 T2) => (wfTy k3 T1)
    | _ => True
  end with
    | (wfTy_tprod T1 H6 T2 H7) => H6
    | _ => I
  end.
  Definition inversion_wfTy_tprod_1 (k3 : Hvl) (T1 : Ty) (T2 : Ty) (H31 : (wfTy k3 (tprod T1 T2))) : (wfTy k3 T2) := match H31 in (wfTy _ S5) return match S5 return Prop with
    | (tprod T1 T2) => (wfTy k3 T2)
    | _ => True
  end with
    | (wfTy_tprod T1 H6 T2 H7) => H7
    | _ => I
  end.
  Definition inversion_wfPat_pvar_1 (k4 : Hvl) (T : Ty) (H32 : (wfPat k4 (pvar T))) : (wfTy k4 T) := match H32 in (wfPat _ p11) return match p11 return Prop with
    | (pvar T) => (wfTy k4 T)
    | _ => True
  end with
    | (wfPat_pvar T H8) => H8
    | _ => I
  end.
  Definition inversion_wfPat_pprod_0 (k5 : Hvl) (p1 : Pat) (p2 : Pat) (H33 : (wfPat k5 (pprod p1 p2))) : (wfPat k5 p1) := match H33 in (wfPat _ p12) return match p12 return Prop with
    | (pprod p1 p2) => (wfPat k5 p1)
    | _ => True
  end with
    | (wfPat_pprod p1 H9 p2 H10) => H9
    | _ => I
  end.
  Definition inversion_wfPat_pprod_1 (k5 : Hvl) (p1 : Pat) (p2 : Pat) (H33 : (wfPat k5 (pprod p1 p2))) : (wfPat (appendHvl k5 (appendHvl H0 (bindPat p1))) p2) := match H33 in (wfPat _ p12) return match p12 return Prop with
    | (pprod p1 p2) => (wfPat (appendHvl k5 (appendHvl H0 (bindPat p1))) p2)
    | _ => True
  end with
    | (wfPat_pprod p1 H9 p2 H10) => H10
    | _ => I
  end.
  Definition inversion_wfTm_var_1 (k6 : Hvl) (x : (Index TmVar)) (H34 : (wfTm k6 (var x))) : (wfindex k6 x) := match H34 in (wfTm _ s) return match s return Prop with
    | (var x) => (wfindex k6 x)
    | _ => True
  end with
    | (wfTm_var x H11) => H11
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k7 : Hvl) (T : Ty) (t : Tm) (H35 : (wfTm k7 (abs T t))) : (wfTy k7 T) := match H35 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTy k7 T)
    | _ => True
  end with
    | (wfTm_abs T H12 t H13) => H12
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k7 : Hvl) (T : Ty) (t : Tm) (H35 : (wfTm k7 (abs T t))) : (wfTm (HS TmVar k7) t) := match H35 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTm (HS TmVar k7) t)
    | _ => True
  end with
    | (wfTm_abs T H12 t H13) => H13
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H36 : (wfTm k8 (app t1 t2))) : (wfTm k8 t1) := match H36 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k8 t1)
    | _ => True
  end with
    | (wfTm_app t1 H14 t2 H15) => H14
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H36 : (wfTm k8 (app t1 t2))) : (wfTm k8 t2) := match H36 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k8 t2)
    | _ => True
  end with
    | (wfTm_app t1 H14 t2 H15) => H15
    | _ => I
  end.
  Definition inversion_wfTm_tabs_1 (k9 : Hvl) (T : Ty) (t : Tm) (H37 : (wfTm k9 (tabs T t))) : (wfTy k9 T) := match H37 in (wfTm _ s2) return match s2 return Prop with
    | (tabs T t) => (wfTy k9 T)
    | _ => True
  end with
    | (wfTm_tabs T H16 t H17) => H16
    | _ => I
  end.
  Definition inversion_wfTm_tabs_2 (k9 : Hvl) (T : Ty) (t : Tm) (H37 : (wfTm k9 (tabs T t))) : (wfTm (HS TyVar k9) t) := match H37 in (wfTm _ s2) return match s2 return Prop with
    | (tabs T t) => (wfTm (HS TyVar k9) t)
    | _ => True
  end with
    | (wfTm_tabs T H16 t H17) => H17
    | _ => I
  end.
  Definition inversion_wfTm_tapp_0 (k10 : Hvl) (t : Tm) (T : Ty) (H38 : (wfTm k10 (tapp t T))) : (wfTm k10 t) := match H38 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTm k10 t)
    | _ => True
  end with
    | (wfTm_tapp t H18 T H19) => H18
    | _ => I
  end.
  Definition inversion_wfTm_tapp_1 (k10 : Hvl) (t : Tm) (T : Ty) (H38 : (wfTm k10 (tapp t T))) : (wfTy k10 T) := match H38 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTy k10 T)
    | _ => True
  end with
    | (wfTm_tapp t H18 T H19) => H19
    | _ => I
  end.
  Definition inversion_wfTm_prod_0 (k11 : Hvl) (t1 : Tm) (t2 : Tm) (H39 : (wfTm k11 (prod t1 t2))) : (wfTm k11 t1) := match H39 in (wfTm _ s4) return match s4 return Prop with
    | (prod t1 t2) => (wfTm k11 t1)
    | _ => True
  end with
    | (wfTm_prod t1 H20 t2 H21) => H20
    | _ => I
  end.
  Definition inversion_wfTm_prod_1 (k11 : Hvl) (t1 : Tm) (t2 : Tm) (H39 : (wfTm k11 (prod t1 t2))) : (wfTm k11 t2) := match H39 in (wfTm _ s4) return match s4 return Prop with
    | (prod t1 t2) => (wfTm k11 t2)
    | _ => True
  end with
    | (wfTm_prod t1 H20 t2 H21) => H21
    | _ => I
  end.
  Definition inversion_wfTm_lett_0 (k12 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H40 : (wfTm k12 (lett p t1 t2))) : (wfPat k12 p) := match H40 in (wfTm _ s5) return match s5 return Prop with
    | (lett p t1 t2) => (wfPat k12 p)
    | _ => True
  end with
    | (wfTm_lett p H22 t1 H23 t2 H24) => H22
    | _ => I
  end.
  Definition inversion_wfTm_lett_1 (k12 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H40 : (wfTm k12 (lett p t1 t2))) : (wfTm k12 t1) := match H40 in (wfTm _ s5) return match s5 return Prop with
    | (lett p t1 t2) => (wfTm k12 t1)
    | _ => True
  end with
    | (wfTm_lett p H22 t1 H23 t2 H24) => H23
    | _ => I
  end.
  Definition inversion_wfTm_lett_2 (k12 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H40 : (wfTm k12 (lett p t1 t2))) : (wfTm (appendHvl k12 (appendHvl H0 (bindPat p))) t2) := match H40 in (wfTm _ s5) return match s5 return Prop with
    | (lett p t1 t2) => (wfTm (appendHvl k12 (appendHvl H0 (bindPat p))) t2)
    | _ => True
  end with
    | (wfTm_lett p H22 t1 H23 t2 H24) => H24
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
    (forall (c0 : (Cutoff TmVar)) (k13 : Hvl) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) (X7 : (Index TyVar)) ,
      (wfindex k13 X7) -> (wfindex k14 X7)).
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
    (forall (c0 : (Cutoff TyVar)) (k13 : Hvl) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) (X7 : (Index TyVar)) ,
      (wfindex k13 X7) -> (wfindex k14 (tshiftIndex c0 X7))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k13 : Hvl) ,
    (forall (S6 : Ty) (wf : (wfTy k13 S6)) ,
      (forall (c0 : (Cutoff TmVar)) (k14 : Hvl) ,
        (shifthvl_TmVar c0 k13 k14) -> (wfTy k14 S6)))) := (ind_wfTy (fun (k13 : Hvl) (S6 : Ty) (wf : (wfTy k13 S6)) =>
    (forall (c0 : (Cutoff TmVar)) (k14 : Hvl) ,
      (shifthvl_TmVar c0 k13 k14) -> (wfTy k14 S6))) (fun (k13 : Hvl) (X7 : (Index TyVar)) (wfi : (wfindex k13 X7)) (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTy_tvar k14 _ (shift_wfindex_TyVar c0 k13 k14 ins X7 wfi))) (fun (k13 : Hvl) (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTy_top k14)) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k13 T2)) IHT2 (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTy_tarrow k14 (IHT1 c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHT2 c0 k14 (weaken_shifthvl_TmVar H0 ins)))) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS TyVar k13) T2)) IHT2 (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTy_tall k14 (IHT1 c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHT2 c0 (HS TyVar k14) (weaken_shifthvl_TmVar (HS TyVar H0) ins)))) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k13 T2)) IHT2 (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTy_tprod k14 (IHT1 c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHT2 c0 k14 (weaken_shifthvl_TmVar H0 ins))))).
  Definition tshift_wfTy : (forall (k13 : Hvl) ,
    (forall (S6 : Ty) (wf : (wfTy k13 S6)) ,
      (forall (c0 : (Cutoff TyVar)) (k14 : Hvl) ,
        (shifthvl_TyVar c0 k13 k14) -> (wfTy k14 (tshiftTy c0 S6))))) := (ind_wfTy (fun (k13 : Hvl) (S6 : Ty) (wf : (wfTy k13 S6)) =>
    (forall (c0 : (Cutoff TyVar)) (k14 : Hvl) ,
      (shifthvl_TyVar c0 k13 k14) -> (wfTy k14 (tshiftTy c0 S6)))) (fun (k13 : Hvl) (X7 : (Index TyVar)) (wfi : (wfindex k13 X7)) (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTy_tvar k14 _ (tshift_wfindex_TyVar c0 k13 k14 ins X7 wfi))) (fun (k13 : Hvl) (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTy_top k14)) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k13 T2)) IHT2 (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTy_tarrow k14 (IHT1 c0 k14 (weaken_shifthvl_TyVar H0 ins)) (IHT2 c0 k14 (weaken_shifthvl_TyVar H0 ins)))) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS TyVar k13) T2)) IHT2 (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTy_tall k14 (IHT1 c0 k14 (weaken_shifthvl_TyVar H0 ins)) (IHT2 (CS c0) (HS TyVar k14) (weaken_shifthvl_TyVar (HS TyVar H0) ins)))) (fun (k13 : Hvl) (T1 : Ty) (wf : (wfTy k13 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k13 T2)) IHT2 (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTy_tprod k14 (IHT1 c0 k14 (weaken_shifthvl_TyVar H0 ins)) (IHT2 c0 k14 (weaken_shifthvl_TyVar H0 ins))))).
  Definition shift_wfPat : (forall (k13 : Hvl) ,
    (forall (p13 : Pat) (wf : (wfPat k13 p13)) ,
      (forall (c0 : (Cutoff TmVar)) (k14 : Hvl) ,
        (shifthvl_TmVar c0 k13 k14) -> (wfPat k14 p13)))) := (ind_wfPat (fun (k13 : Hvl) (p13 : Pat) (wf : (wfPat k13 p13)) =>
    (forall (c0 : (Cutoff TmVar)) (k14 : Hvl) ,
      (shifthvl_TmVar c0 k13 k14) -> (wfPat k14 p13))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfPat_pvar k14 (shift_wfTy k13 T wf c0 k14 (weaken_shifthvl_TmVar H0 ins)))) (fun (k13 : Hvl) (p1 : Pat) (wf : (wfPat k13 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k13 (appendHvl H0 (bindPat p1))) p2)) IHp2 (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfPat_pprod k14 (IHp1 c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHp2 (weakenCutoffTmVar c0 (appendHvl H0 (bindPat p1))) (appendHvl k14 (appendHvl H0 (bindPat p1))) (weaken_shifthvl_TmVar (appendHvl H0 (bindPat p1)) ins))))).
  Definition tshift_wfPat : (forall (k13 : Hvl) ,
    (forall (p13 : Pat) (wf : (wfPat k13 p13)) ,
      (forall (c0 : (Cutoff TyVar)) (k14 : Hvl) ,
        (shifthvl_TyVar c0 k13 k14) -> (wfPat k14 (tshiftPat c0 p13))))) := (ind_wfPat (fun (k13 : Hvl) (p13 : Pat) (wf : (wfPat k13 p13)) =>
    (forall (c0 : (Cutoff TyVar)) (k14 : Hvl) ,
      (shifthvl_TyVar c0 k13 k14) -> (wfPat k14 (tshiftPat c0 p13)))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfPat_pvar k14 (tshift_wfTy k13 T wf c0 k14 (weaken_shifthvl_TyVar H0 ins)))) (fun (k13 : Hvl) (p1 : Pat) (wf : (wfPat k13 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k13 (appendHvl H0 (bindPat p1))) p2)) IHp2 (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfPat_pprod k14 (IHp1 c0 k14 (weaken_shifthvl_TyVar H0 ins)) (eq_ind2 wfPat (f_equal2 appendHvl (eq_refl k14) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))) eq_refl (IHp2 (weakenCutoffTyVar c0 (appendHvl H0 (bindPat p1))) (appendHvl k14 (appendHvl H0 (bindPat p1))) (weaken_shifthvl_TyVar (appendHvl H0 (bindPat p1)) ins)))))).
  Definition shift_wfTm : (forall (k13 : Hvl) ,
    (forall (s6 : Tm) (wf : (wfTm k13 s6)) ,
      (forall (c0 : (Cutoff TmVar)) (k14 : Hvl) ,
        (shifthvl_TmVar c0 k13 k14) -> (wfTm k14 (shiftTm c0 s6))))) := (ind_wfTm (fun (k13 : Hvl) (s6 : Tm) (wf : (wfTm k13 s6)) =>
    (forall (c0 : (Cutoff TmVar)) (k14 : Hvl) ,
      (shifthvl_TmVar c0 k13 k14) -> (wfTm k14 (shiftTm c0 s6)))) (fun (k13 : Hvl) (x6 : (Index TmVar)) (wfi : (wfindex k13 x6)) (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTm_var k14 _ (shift_wfindex_TmVar c0 k13 k14 ins x6 wfi))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (t : Tm) (wf0 : (wfTm (HS TmVar k13) t)) IHt (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTm_abs k14 (shift_wfTy k13 T wf c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHt (CS c0) (HS TmVar k14) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k13 : Hvl) (t1 : Tm) (wf : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k13 t2)) IHt2 (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTm_app k14 (IHt1 c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHt2 c0 k14 (weaken_shifthvl_TmVar H0 ins)))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (t : Tm) (wf0 : (wfTm (HS TyVar k13) t)) IHt (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTm_tabs k14 (shift_wfTy k13 T wf c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHt c0 (HS TyVar k14) (weaken_shifthvl_TmVar (HS TyVar H0) ins)))) (fun (k13 : Hvl) (t : Tm) (wf : (wfTm k13 t)) IHt (T : Ty) (wf0 : (wfTy k13 T)) (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTm_tapp k14 (IHt c0 k14 (weaken_shifthvl_TmVar H0 ins)) (shift_wfTy k13 T wf0 c0 k14 (weaken_shifthvl_TmVar H0 ins)))) (fun (k13 : Hvl) (t1 : Tm) (wf : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k13 t2)) IHt2 (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTm_prod k14 (IHt1 c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHt2 c0 k14 (weaken_shifthvl_TmVar H0 ins)))) (fun (k13 : Hvl) (p : Pat) (wf : (wfPat k13 p)) (t1 : Tm) (wf0 : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (appendHvl k13 (appendHvl H0 (bindPat p))) t2)) IHt2 (c0 : (Cutoff TmVar)) (k14 : Hvl) (ins : (shifthvl_TmVar c0 k13 k14)) =>
    (wfTm_lett k14 (shift_wfPat k13 p wf c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHt1 c0 k14 (weaken_shifthvl_TmVar H0 ins)) (IHt2 (weakenCutoffTmVar c0 (appendHvl H0 (bindPat p))) (appendHvl k14 (appendHvl H0 (bindPat p))) (weaken_shifthvl_TmVar (appendHvl H0 (bindPat p)) ins))))).
  Definition tshift_wfTm : (forall (k13 : Hvl) ,
    (forall (s6 : Tm) (wf : (wfTm k13 s6)) ,
      (forall (c0 : (Cutoff TyVar)) (k14 : Hvl) ,
        (shifthvl_TyVar c0 k13 k14) -> (wfTm k14 (tshiftTm c0 s6))))) := (ind_wfTm (fun (k13 : Hvl) (s6 : Tm) (wf : (wfTm k13 s6)) =>
    (forall (c0 : (Cutoff TyVar)) (k14 : Hvl) ,
      (shifthvl_TyVar c0 k13 k14) -> (wfTm k14 (tshiftTm c0 s6)))) (fun (k13 : Hvl) (x6 : (Index TmVar)) (wfi : (wfindex k13 x6)) (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTm_var k14 _ (tshift_wfindex_TmVar c0 k13 k14 ins x6 wfi))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (t : Tm) (wf0 : (wfTm (HS TmVar k13) t)) IHt (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTm_abs k14 (tshift_wfTy k13 T wf c0 k14 (weaken_shifthvl_TyVar H0 ins)) (IHt c0 (HS TmVar k14) (weaken_shifthvl_TyVar (HS TmVar H0) ins)))) (fun (k13 : Hvl) (t1 : Tm) (wf : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k13 t2)) IHt2 (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTm_app k14 (IHt1 c0 k14 (weaken_shifthvl_TyVar H0 ins)) (IHt2 c0 k14 (weaken_shifthvl_TyVar H0 ins)))) (fun (k13 : Hvl) (T : Ty) (wf : (wfTy k13 T)) (t : Tm) (wf0 : (wfTm (HS TyVar k13) t)) IHt (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTm_tabs k14 (tshift_wfTy k13 T wf c0 k14 (weaken_shifthvl_TyVar H0 ins)) (IHt (CS c0) (HS TyVar k14) (weaken_shifthvl_TyVar (HS TyVar H0) ins)))) (fun (k13 : Hvl) (t : Tm) (wf : (wfTm k13 t)) IHt (T : Ty) (wf0 : (wfTy k13 T)) (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTm_tapp k14 (IHt c0 k14 (weaken_shifthvl_TyVar H0 ins)) (tshift_wfTy k13 T wf0 c0 k14 (weaken_shifthvl_TyVar H0 ins)))) (fun (k13 : Hvl) (t1 : Tm) (wf : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k13 t2)) IHt2 (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTm_prod k14 (IHt1 c0 k14 (weaken_shifthvl_TyVar H0 ins)) (IHt2 c0 k14 (weaken_shifthvl_TyVar H0 ins)))) (fun (k13 : Hvl) (p : Pat) (wf : (wfPat k13 p)) (t1 : Tm) (wf0 : (wfTm k13 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (appendHvl k13 (appendHvl H0 (bindPat p))) t2)) IHt2 (c0 : (Cutoff TyVar)) (k14 : Hvl) (ins : (shifthvl_TyVar c0 k13 k14)) =>
    (wfTm_lett k14 (tshift_wfPat k13 p wf c0 k14 (weaken_shifthvl_TyVar H0 ins)) (IHt1 c0 k14 (weaken_shifthvl_TyVar H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k14) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))) eq_refl (IHt2 (weakenCutoffTyVar c0 (appendHvl H0 (bindPat p))) (appendHvl k14 (appendHvl H0 (bindPat p))) (weaken_shifthvl_TyVar (appendHvl H0 (bindPat p)) ins)))))).
  Fixpoint weaken_wfTy (k13 : Hvl) {struct k13} :
  (forall (k14 : Hvl) (S6 : Ty) (wf : (wfTy k14 S6)) ,
    (wfTy (appendHvl k14 k13) (weakenTy S6 k13))) :=
    match k13 return (forall (k14 : Hvl) (S6 : Ty) (wf : (wfTy k14 S6)) ,
      (wfTy (appendHvl k14 k13) (weakenTy S6 k13))) with
      | (H0) => (fun (k14 : Hvl) (S6 : Ty) (wf : (wfTy k14 S6)) =>
        wf)
      | (HS TmVar k13) => (fun (k14 : Hvl) (S6 : Ty) (wf : (wfTy k14 S6)) =>
        (shift_wfTy (appendHvl k14 k13) (weakenTy S6 k13) (weaken_wfTy k13 k14 S6 wf) C0 (HS TmVar (appendHvl k14 k13)) (shifthvl_TmVar_here (appendHvl k14 k13))))
      | (HS TyVar k13) => (fun (k14 : Hvl) (S6 : Ty) (wf : (wfTy k14 S6)) =>
        (tshift_wfTy (appendHvl k14 k13) (weakenTy S6 k13) (weaken_wfTy k13 k14 S6 wf) C0 (HS TyVar (appendHvl k14 k13)) (shifthvl_TyVar_here (appendHvl k14 k13))))
    end.
  Fixpoint weaken_wfPat (k13 : Hvl) {struct k13} :
  (forall (k14 : Hvl) (p13 : Pat) (wf : (wfPat k14 p13)) ,
    (wfPat (appendHvl k14 k13) (weakenPat p13 k13))) :=
    match k13 return (forall (k14 : Hvl) (p13 : Pat) (wf : (wfPat k14 p13)) ,
      (wfPat (appendHvl k14 k13) (weakenPat p13 k13))) with
      | (H0) => (fun (k14 : Hvl) (p13 : Pat) (wf : (wfPat k14 p13)) =>
        wf)
      | (HS TmVar k13) => (fun (k14 : Hvl) (p13 : Pat) (wf : (wfPat k14 p13)) =>
        (shift_wfPat (appendHvl k14 k13) (weakenPat p13 k13) (weaken_wfPat k13 k14 p13 wf) C0 (HS TmVar (appendHvl k14 k13)) (shifthvl_TmVar_here (appendHvl k14 k13))))
      | (HS TyVar k13) => (fun (k14 : Hvl) (p13 : Pat) (wf : (wfPat k14 p13)) =>
        (tshift_wfPat (appendHvl k14 k13) (weakenPat p13 k13) (weaken_wfPat k13 k14 p13 wf) C0 (HS TyVar (appendHvl k14 k13)) (shifthvl_TyVar_here (appendHvl k14 k13))))
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
  (forall (k17 : Hvl) (S7 : Ty) (k18 : Hvl) (S8 : Ty) ,
    (k17 = k18) -> (S7 = S8) -> (wfTy k17 S7) -> (wfTy k18 S8)).
Proof.
  congruence .
Qed.
Lemma wfPat_cast  :
  (forall (k17 : Hvl) (p14 : Pat) (k18 : Hvl) (p15 : Pat) ,
    (k17 = k18) -> (p14 = p15) -> (wfPat k17 p14) -> (wfPat k18 p15)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k17 : Hvl) (s6 : Tm) (k18 : Hvl) (s7 : Tm) ,
    (k17 = k18) -> (s6 = s7) -> (wfTm k17 s6) -> (wfTm k18 s7)).
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
  Lemma substhvl_TmVar_wfindex_TmVar {k17 : Hvl} {s6 : Tm} (wft : (wfTm k17 s6)) :
    (forall {d0 : (Trace TmVar)} {k18 : Hvl} {k19 : Hvl} ,
      (substhvl_TmVar k17 d0 k18 k19) -> (forall {x6 : (Index TmVar)} ,
        (wfindex k18 x6) -> (wfTm k19 (substIndex d0 s6 x6)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TyVar_wfindex_TyVar {k17 : Hvl} {S7 : Ty} (wft : (wfTy k17 S7)) :
    (forall {d0 : (Trace TyVar)} {k18 : Hvl} {k19 : Hvl} ,
      (substhvl_TyVar k17 d0 k18 k19) -> (forall {X7 : (Index TyVar)} ,
        (wfindex k18 X7) -> (wfTy k19 (tsubstIndex d0 S7 X7)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_TmVar_wfindex_TyVar {k17 : Hvl} :
    (forall {d0 : (Trace TmVar)} {k18 : Hvl} {k19 : Hvl} ,
      (substhvl_TmVar k17 d0 k18 k19) -> (forall {X7 : (Index TyVar)} ,
        (wfindex k18 X7) -> (wfindex k19 X7))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_TyVar_wfindex_TmVar {k17 : Hvl} :
    (forall {d0 : (Trace TyVar)} {k18 : Hvl} {k19 : Hvl} ,
      (substhvl_TyVar k17 d0 k18 k19) -> (forall {x6 : (Index TmVar)} ,
        (wfindex k18 x6) -> (wfindex k19 x6))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_TmVar_wfTy {k17 : Hvl} : (forall (k18 : Hvl) ,
    (forall (S7 : Ty) (wf0 : (wfTy k18 S7)) ,
      (forall {d0 : (Trace TmVar)} {k19 : Hvl} ,
        (substhvl_TmVar k17 d0 k18 k19) -> (wfTy k19 S7)))) := (ind_wfTy (fun (k18 : Hvl) (S7 : Ty) (wf0 : (wfTy k18 S7)) =>
    (forall {d0 : (Trace TmVar)} {k19 : Hvl} ,
      (substhvl_TmVar k17 d0 k18 k19) -> (wfTy k19 S7))) (fun (k18 : Hvl) {X7 : (Index TyVar)} (wfi : (wfindex k18 X7)) {d0 : (Trace TmVar)} {k19 : Hvl} (del : (substhvl_TmVar k17 d0 k18 k19)) =>
    (wfTy_tvar k19 _ (substhvl_TmVar_wfindex_TyVar del wfi))) (fun (k18 : Hvl) {d0 : (Trace TmVar)} {k19 : Hvl} (del : (substhvl_TmVar k17 d0 k18 k19)) =>
    (wfTy_top k19)) (fun (k18 : Hvl) (T1 : Ty) (wf0 : (wfTy k18 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k18 T2)) IHT2 {d0 : (Trace TmVar)} {k19 : Hvl} (del : (substhvl_TmVar k17 d0 k18 k19)) =>
    (wfTy_tarrow k19 (IHT1 (weakenTrace d0 H0) k19 (weaken_substhvl_TmVar H0 del)) (IHT2 (weakenTrace d0 H0) k19 (weaken_substhvl_TmVar H0 del)))) (fun (k18 : Hvl) (T1 : Ty) (wf0 : (wfTy k18 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS TyVar k18) T2)) IHT2 {d0 : (Trace TmVar)} {k19 : Hvl} (del : (substhvl_TmVar k17 d0 k18 k19)) =>
    (wfTy_tall k19 (IHT1 (weakenTrace d0 H0) k19 (weaken_substhvl_TmVar H0 del)) (IHT2 (weakenTrace d0 (HS TyVar H0)) (HS TyVar k19) (weaken_substhvl_TmVar (HS TyVar H0) del)))) (fun (k18 : Hvl) (T1 : Ty) (wf0 : (wfTy k18 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k18 T2)) IHT2 {d0 : (Trace TmVar)} {k19 : Hvl} (del : (substhvl_TmVar k17 d0 k18 k19)) =>
    (wfTy_tprod k19 (IHT1 (weakenTrace d0 H0) k19 (weaken_substhvl_TmVar H0 del)) (IHT2 (weakenTrace d0 H0) k19 (weaken_substhvl_TmVar H0 del))))).
  Definition substhvl_TyVar_wfTy {k17 : Hvl} {S7 : Ty} (wf : (wfTy k17 S7)) : (forall (k18 : Hvl) ,
    (forall (S8 : Ty) (wf0 : (wfTy k18 S8)) ,
      (forall {d0 : (Trace TyVar)} {k19 : Hvl} ,
        (substhvl_TyVar k17 d0 k18 k19) -> (wfTy k19 (tsubstTy d0 S7 S8))))) := (ind_wfTy (fun (k18 : Hvl) (S8 : Ty) (wf0 : (wfTy k18 S8)) =>
    (forall {d0 : (Trace TyVar)} {k19 : Hvl} ,
      (substhvl_TyVar k17 d0 k18 k19) -> (wfTy k19 (tsubstTy d0 S7 S8)))) (fun (k18 : Hvl) {X7 : (Index TyVar)} (wfi : (wfindex k18 X7)) {d0 : (Trace TyVar)} {k19 : Hvl} (del : (substhvl_TyVar k17 d0 k18 k19)) =>
    (substhvl_TyVar_wfindex_TyVar wf del wfi)) (fun (k18 : Hvl) {d0 : (Trace TyVar)} {k19 : Hvl} (del : (substhvl_TyVar k17 d0 k18 k19)) =>
    (wfTy_top k19)) (fun (k18 : Hvl) (T1 : Ty) (wf0 : (wfTy k18 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k18 T2)) IHT2 {d0 : (Trace TyVar)} {k19 : Hvl} (del : (substhvl_TyVar k17 d0 k18 k19)) =>
    (wfTy_tarrow k19 (IHT1 (weakenTrace d0 H0) k19 (weaken_substhvl_TyVar H0 del)) (IHT2 (weakenTrace d0 H0) k19 (weaken_substhvl_TyVar H0 del)))) (fun (k18 : Hvl) (T1 : Ty) (wf0 : (wfTy k18 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS TyVar k18) T2)) IHT2 {d0 : (Trace TyVar)} {k19 : Hvl} (del : (substhvl_TyVar k17 d0 k18 k19)) =>
    (wfTy_tall k19 (IHT1 (weakenTrace d0 H0) k19 (weaken_substhvl_TyVar H0 del)) (IHT2 (weakenTrace d0 (HS TyVar H0)) (HS TyVar k19) (weaken_substhvl_TyVar (HS TyVar H0) del)))) (fun (k18 : Hvl) (T1 : Ty) (wf0 : (wfTy k18 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k18 T2)) IHT2 {d0 : (Trace TyVar)} {k19 : Hvl} (del : (substhvl_TyVar k17 d0 k18 k19)) =>
    (wfTy_tprod k19 (IHT1 (weakenTrace d0 H0) k19 (weaken_substhvl_TyVar H0 del)) (IHT2 (weakenTrace d0 H0) k19 (weaken_substhvl_TyVar H0 del))))).
  Definition substhvl_TmVar_wfPat {k17 : Hvl} : (forall (k18 : Hvl) ,
    (forall (p14 : Pat) (wf0 : (wfPat k18 p14)) ,
      (forall {d0 : (Trace TmVar)} {k19 : Hvl} ,
        (substhvl_TmVar k17 d0 k18 k19) -> (wfPat k19 p14)))) := (ind_wfPat (fun (k18 : Hvl) (p14 : Pat) (wf0 : (wfPat k18 p14)) =>
    (forall {d0 : (Trace TmVar)} {k19 : Hvl} ,
      (substhvl_TmVar k17 d0 k18 k19) -> (wfPat k19 p14))) (fun (k18 : Hvl) (T : Ty) (wf0 : (wfTy k18 T)) {d0 : (Trace TmVar)} {k19 : Hvl} (del : (substhvl_TmVar k17 d0 k18 k19)) =>
    (wfPat_pvar k19 (substhvl_TmVar_wfTy k18 T wf0 (weaken_substhvl_TmVar H0 del)))) (fun (k18 : Hvl) (p1 : Pat) (wf0 : (wfPat k18 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k18 (appendHvl H0 (bindPat p1))) p2)) IHp2 {d0 : (Trace TmVar)} {k19 : Hvl} (del : (substhvl_TmVar k17 d0 k18 k19)) =>
    (wfPat_pprod k19 (IHp1 (weakenTrace d0 H0) k19 (weaken_substhvl_TmVar H0 del)) (IHp2 (weakenTrace d0 (appendHvl H0 (bindPat p1))) (appendHvl k19 (appendHvl H0 (bindPat p1))) (weaken_substhvl_TmVar (appendHvl H0 (bindPat p1)) del))))).
  Definition substhvl_TyVar_wfPat {k17 : Hvl} {S7 : Ty} (wf : (wfTy k17 S7)) : (forall (k18 : Hvl) ,
    (forall (p14 : Pat) (wf0 : (wfPat k18 p14)) ,
      (forall {d0 : (Trace TyVar)} {k19 : Hvl} ,
        (substhvl_TyVar k17 d0 k18 k19) -> (wfPat k19 (tsubstPat d0 S7 p14))))) := (ind_wfPat (fun (k18 : Hvl) (p14 : Pat) (wf0 : (wfPat k18 p14)) =>
    (forall {d0 : (Trace TyVar)} {k19 : Hvl} ,
      (substhvl_TyVar k17 d0 k18 k19) -> (wfPat k19 (tsubstPat d0 S7 p14)))) (fun (k18 : Hvl) (T : Ty) (wf0 : (wfTy k18 T)) {d0 : (Trace TyVar)} {k19 : Hvl} (del : (substhvl_TyVar k17 d0 k18 k19)) =>
    (wfPat_pvar k19 (substhvl_TyVar_wfTy wf k18 T wf0 (weaken_substhvl_TyVar H0 del)))) (fun (k18 : Hvl) (p1 : Pat) (wf0 : (wfPat k18 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k18 (appendHvl H0 (bindPat p1))) p2)) IHp2 {d0 : (Trace TyVar)} {k19 : Hvl} (del : (substhvl_TyVar k17 d0 k18 k19)) =>
    (wfPat_pprod k19 (IHp1 (weakenTrace d0 H0) k19 (weaken_substhvl_TyVar H0 del)) (eq_ind2 wfPat (f_equal2 appendHvl (eq_refl k19) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (IHp2 (weakenTrace d0 (appendHvl H0 (bindPat p1))) (appendHvl k19 (appendHvl H0 (bindPat p1))) (weaken_substhvl_TyVar (appendHvl H0 (bindPat p1)) del)))))).
  Definition substhvl_TmVar_wfTm {k17 : Hvl} {s6 : Tm} (wf : (wfTm k17 s6)) : (forall (k18 : Hvl) ,
    (forall (s7 : Tm) (wf0 : (wfTm k18 s7)) ,
      (forall {d0 : (Trace TmVar)} {k19 : Hvl} ,
        (substhvl_TmVar k17 d0 k18 k19) -> (wfTm k19 (substTm d0 s6 s7))))) := (ind_wfTm (fun (k18 : Hvl) (s7 : Tm) (wf0 : (wfTm k18 s7)) =>
    (forall {d0 : (Trace TmVar)} {k19 : Hvl} ,
      (substhvl_TmVar k17 d0 k18 k19) -> (wfTm k19 (substTm d0 s6 s7)))) (fun (k18 : Hvl) {x6 : (Index TmVar)} (wfi : (wfindex k18 x6)) {d0 : (Trace TmVar)} {k19 : Hvl} (del : (substhvl_TmVar k17 d0 k18 k19)) =>
    (substhvl_TmVar_wfindex_TmVar wf del wfi)) (fun (k18 : Hvl) (T : Ty) (wf0 : (wfTy k18 T)) (t : Tm) (wf1 : (wfTm (HS TmVar k18) t)) IHt {d0 : (Trace TmVar)} {k19 : Hvl} (del : (substhvl_TmVar k17 d0 k18 k19)) =>
    (wfTm_abs k19 (substhvl_TmVar_wfTy k18 T wf0 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d0 (HS TmVar H0)) (HS TmVar k19) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k18 : Hvl) (t1 : Tm) (wf0 : (wfTm k18 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k18 t2)) IHt2 {d0 : (Trace TmVar)} {k19 : Hvl} (del : (substhvl_TmVar k17 d0 k18 k19)) =>
    (wfTm_app k19 (IHt1 (weakenTrace d0 H0) k19 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d0 H0) k19 (weaken_substhvl_TmVar H0 del)))) (fun (k18 : Hvl) (T : Ty) (wf0 : (wfTy k18 T)) (t : Tm) (wf1 : (wfTm (HS TyVar k18) t)) IHt {d0 : (Trace TmVar)} {k19 : Hvl} (del : (substhvl_TmVar k17 d0 k18 k19)) =>
    (wfTm_tabs k19 (substhvl_TmVar_wfTy k18 T wf0 (weaken_substhvl_TmVar H0 del)) (IHt (weakenTrace d0 (HS TyVar H0)) (HS TyVar k19) (weaken_substhvl_TmVar (HS TyVar H0) del)))) (fun (k18 : Hvl) (t : Tm) (wf0 : (wfTm k18 t)) IHt (T : Ty) (wf1 : (wfTy k18 T)) {d0 : (Trace TmVar)} {k19 : Hvl} (del : (substhvl_TmVar k17 d0 k18 k19)) =>
    (wfTm_tapp k19 (IHt (weakenTrace d0 H0) k19 (weaken_substhvl_TmVar H0 del)) (substhvl_TmVar_wfTy k18 T wf1 (weaken_substhvl_TmVar H0 del)))) (fun (k18 : Hvl) (t1 : Tm) (wf0 : (wfTm k18 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k18 t2)) IHt2 {d0 : (Trace TmVar)} {k19 : Hvl} (del : (substhvl_TmVar k17 d0 k18 k19)) =>
    (wfTm_prod k19 (IHt1 (weakenTrace d0 H0) k19 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d0 H0) k19 (weaken_substhvl_TmVar H0 del)))) (fun (k18 : Hvl) (p : Pat) (wf0 : (wfPat k18 p)) (t1 : Tm) (wf1 : (wfTm k18 t1)) IHt1 (t2 : Tm) (wf2 : (wfTm (appendHvl k18 (appendHvl H0 (bindPat p))) t2)) IHt2 {d0 : (Trace TmVar)} {k19 : Hvl} (del : (substhvl_TmVar k17 d0 k18 k19)) =>
    (wfTm_lett k19 (substhvl_TmVar_wfPat k18 p wf0 (weaken_substhvl_TmVar H0 del)) (IHt1 (weakenTrace d0 H0) k19 (weaken_substhvl_TmVar H0 del)) (IHt2 (weakenTrace d0 (appendHvl H0 (bindPat p))) (appendHvl k19 (appendHvl H0 (bindPat p))) (weaken_substhvl_TmVar (appendHvl H0 (bindPat p)) del))))).
  Definition substhvl_TyVar_wfTm {k17 : Hvl} {S7 : Ty} (wf : (wfTy k17 S7)) : (forall (k18 : Hvl) ,
    (forall (s6 : Tm) (wf0 : (wfTm k18 s6)) ,
      (forall {d0 : (Trace TyVar)} {k19 : Hvl} ,
        (substhvl_TyVar k17 d0 k18 k19) -> (wfTm k19 (tsubstTm d0 S7 s6))))) := (ind_wfTm (fun (k18 : Hvl) (s6 : Tm) (wf0 : (wfTm k18 s6)) =>
    (forall {d0 : (Trace TyVar)} {k19 : Hvl} ,
      (substhvl_TyVar k17 d0 k18 k19) -> (wfTm k19 (tsubstTm d0 S7 s6)))) (fun (k18 : Hvl) {x6 : (Index TmVar)} (wfi : (wfindex k18 x6)) {d0 : (Trace TyVar)} {k19 : Hvl} (del : (substhvl_TyVar k17 d0 k18 k19)) =>
    (wfTm_var k19 _ (substhvl_TyVar_wfindex_TmVar del wfi))) (fun (k18 : Hvl) (T : Ty) (wf0 : (wfTy k18 T)) (t : Tm) (wf1 : (wfTm (HS TmVar k18) t)) IHt {d0 : (Trace TyVar)} {k19 : Hvl} (del : (substhvl_TyVar k17 d0 k18 k19)) =>
    (wfTm_abs k19 (substhvl_TyVar_wfTy wf k18 T wf0 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d0 (HS TmVar H0)) (HS TmVar k19) (weaken_substhvl_TyVar (HS TmVar H0) del)))) (fun (k18 : Hvl) (t1 : Tm) (wf0 : (wfTm k18 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k18 t2)) IHt2 {d0 : (Trace TyVar)} {k19 : Hvl} (del : (substhvl_TyVar k17 d0 k18 k19)) =>
    (wfTm_app k19 (IHt1 (weakenTrace d0 H0) k19 (weaken_substhvl_TyVar H0 del)) (IHt2 (weakenTrace d0 H0) k19 (weaken_substhvl_TyVar H0 del)))) (fun (k18 : Hvl) (T : Ty) (wf0 : (wfTy k18 T)) (t : Tm) (wf1 : (wfTm (HS TyVar k18) t)) IHt {d0 : (Trace TyVar)} {k19 : Hvl} (del : (substhvl_TyVar k17 d0 k18 k19)) =>
    (wfTm_tabs k19 (substhvl_TyVar_wfTy wf k18 T wf0 (weaken_substhvl_TyVar H0 del)) (IHt (weakenTrace d0 (HS TyVar H0)) (HS TyVar k19) (weaken_substhvl_TyVar (HS TyVar H0) del)))) (fun (k18 : Hvl) (t : Tm) (wf0 : (wfTm k18 t)) IHt (T : Ty) (wf1 : (wfTy k18 T)) {d0 : (Trace TyVar)} {k19 : Hvl} (del : (substhvl_TyVar k17 d0 k18 k19)) =>
    (wfTm_tapp k19 (IHt (weakenTrace d0 H0) k19 (weaken_substhvl_TyVar H0 del)) (substhvl_TyVar_wfTy wf k18 T wf1 (weaken_substhvl_TyVar H0 del)))) (fun (k18 : Hvl) (t1 : Tm) (wf0 : (wfTm k18 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k18 t2)) IHt2 {d0 : (Trace TyVar)} {k19 : Hvl} (del : (substhvl_TyVar k17 d0 k18 k19)) =>
    (wfTm_prod k19 (IHt1 (weakenTrace d0 H0) k19 (weaken_substhvl_TyVar H0 del)) (IHt2 (weakenTrace d0 H0) k19 (weaken_substhvl_TyVar H0 del)))) (fun (k18 : Hvl) (p : Pat) (wf0 : (wfPat k18 p)) (t1 : Tm) (wf1 : (wfTm k18 t1)) IHt1 (t2 : Tm) (wf2 : (wfTm (appendHvl k18 (appendHvl H0 (bindPat p))) t2)) IHt2 {d0 : (Trace TyVar)} {k19 : Hvl} (del : (substhvl_TyVar k17 d0 k18 k19)) =>
    (wfTm_lett k19 (substhvl_TyVar_wfPat wf k18 p wf0 (weaken_substhvl_TyVar H0 del)) (IHt1 (weakenTrace d0 H0) k19 (weaken_substhvl_TyVar H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k19) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (IHt2 (weakenTrace d0 (appendHvl H0 (bindPat p))) (appendHvl k19 (appendHvl H0 (bindPat p))) (weaken_substhvl_TyVar (appendHvl H0 (bindPat p)) del)))))).
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
Fixpoint subhvl_TmVar (k17 : Hvl) {struct k17} :
Prop :=
  match k17 with
    | (H0) => True
    | (HS a k17) => match a with
      | (TmVar) => (subhvl_TmVar k17)
      | _ => False
    end
  end.
Lemma subhvl_TmVar_append  :
  (forall (k17 : Hvl) (k18 : Hvl) ,
    (subhvl_TmVar k17) -> (subhvl_TmVar k18) -> (subhvl_TmVar (appendHvl k17 k18))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_TmVar_append : infra.
 Hint Resolve subhvl_TmVar_append : wf.
Lemma wfPat_strengthen_subhvl_TmVar  :
  (forall (k14 : Hvl) (k13 : Hvl) (p13 : Pat) ,
    (subhvl_TmVar k14) -> (wfPat (appendHvl k13 k14) (weakenPat p13 k14)) -> (wfPat k13 p13)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfTy_strengthen_subhvl_TmVar  :
  (forall (k16 : Hvl) (k15 : Hvl) (S6 : Ty) ,
    (subhvl_TmVar k16) -> (wfTy (appendHvl k15 k16) (weakenTy S6 k16)) -> (wfTy k15 S6)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H47 : (wfPat (appendHvl _ _) (weakenPat _ _)) |- _ => apply (wfPat_strengthen_subhvl_TmVar) in H47
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H48 : (wfTy (appendHvl _ _) (weakenTy _ _)) |- _ => apply (wfTy_strengthen_subhvl_TmVar) in H48
end : infra wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | evar (G : Env) (T : Ty)
    | ebound (G : Env) (T : Ty).
  Fixpoint appendEnv (G : Env) (G0 : Env) :
  Env :=
    match G0 with
      | (empty) => G
      | (evar G1 T) => (evar (appendEnv G G1) T)
      | (ebound G1 T) => (ebound (appendEnv G G1) T)
    end.
  Fixpoint domainEnv (G : Env) :
  Hvl :=
    match G with
      | (empty) => H0
      | (evar G0 T) => (HS TmVar (domainEnv G0))
      | (ebound G0 T) => (HS TyVar (domainEnv G0))
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
  Fixpoint shiftEnv (c0 : (Cutoff TmVar)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shiftEnv c0 G0) T)
      | (ebound G0 T) => (ebound (shiftEnv c0 G0) T)
    end.
  Fixpoint tshiftEnv (c0 : (Cutoff TyVar)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tshiftEnv c0 G0) (tshiftTy (weakenCutoffTyVar c0 (domainEnv G0)) T))
      | (ebound G0 T) => (ebound (tshiftEnv c0 G0) (tshiftTy (weakenCutoffTyVar c0 (domainEnv G0)) T))
    end.
  Fixpoint weakenEnv (G : Env) (k17 : Hvl) {struct k17} :
  Env :=
    match k17 with
      | (H0) => G
      | (HS TmVar k17) => (weakenEnv G k17)
      | (HS TyVar k17) => (tshiftEnv C0 (weakenEnv G k17))
    end.
  Fixpoint substEnv (d0 : (Trace TmVar)) (s6 : Tm) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d0 s6 G0) T)
      | (ebound G0 T) => (ebound (substEnv d0 s6 G0) T)
    end.
  Fixpoint tsubstEnv (d0 : (Trace TyVar)) (S7 : Ty) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d0 S7 G0) (tsubstTy (weakenTrace d0 (domainEnv G0)) S7 T))
      | (ebound G0 T) => (ebound (tsubstEnv d0 S7 G0) (tsubstTy (weakenTrace d0 (domainEnv G0)) S7 T))
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c0 : (Cutoff TmVar)) (G : Env) ,
      ((domainEnv (shiftEnv c0 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_tshiftEnv  :
    (forall (c0 : (Cutoff TyVar)) (G : Env) ,
      ((domainEnv (tshiftEnv c0 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d0 : (Trace TmVar)) (s6 : Tm) (G : Env) ,
      ((domainEnv (substEnv d0 s6 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d0 : (Trace TyVar)) (S7 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d0 S7 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shiftEnv_appendEnv  :
      (forall (c0 : (Cutoff TmVar)) (G : Env) (G0 : Env) ,
        ((shiftEnv c0 (appendEnv G G0)) = (appendEnv (shiftEnv c0 G) (shiftEnv (weakenCutoffTmVar c0 (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma tshiftEnv_appendEnv  :
      (forall (c0 : (Cutoff TyVar)) (G : Env) (G0 : Env) ,
        ((tshiftEnv c0 (appendEnv G G0)) = (appendEnv (tshiftEnv c0 G) (tshiftEnv (weakenCutoffTyVar c0 (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d0 : (Trace TmVar)) (s6 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d0 s6 (appendEnv G G0)) = (appendEnv (substEnv d0 s6 G) (substEnv (weakenTrace d0 (domainEnv G)) s6 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d0 : (Trace TyVar)) (S7 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d0 S7 (appendEnv G G0)) = (appendEnv (tsubstEnv d0 S7 G) (tsubstEnv (weakenTrace d0 (domainEnv G)) S7 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S7 : Ty) (k17 : Hvl) (k18 : Hvl) ,
      ((weakenTy (weakenTy S7 k17) k18) = (weakenTy S7 (appendHvl k17 k18)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenPat_append  :
    (forall (p14 : Pat) (k17 : Hvl) (k18 : Hvl) ,
      ((weakenPat (weakenPat p14 k17) k18) = (weakenPat p14 (appendHvl k17 k18)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s6 : Tm) (k17 : Hvl) (k18 : Hvl) ,
      ((weakenTm (weakenTm s6 k17) k18) = (weakenTm s6 (appendHvl k17 k18)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index TmVar) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          (T12 : Ty) :
          (wfTy (domainEnv G) T12) -> (lookup_evar (evar G T12) I0 T12)
      | lookup_evar_there_evar
          {G : Env} {x6 : (Index TmVar)}
          (T13 : Ty) (T14 : Ty) :
          (lookup_evar G x6 T13) -> (lookup_evar (evar G T14) (IS x6) T13)
      | lookup_evar_there_ebound
          {G : Env} {x6 : (Index TmVar)}
          (T13 : Ty) (T14 : Ty) :
          (lookup_evar G x6 T13) -> (lookup_evar (ebound G T14) x6 (tshiftTy C0 T13)).
    Inductive lookup_ebound : Env -> (Index TyVar) -> Ty -> Prop :=
      | lookup_ebound_here {G : Env}
          (T13 : Ty) :
          (wfTy (domainEnv G) T13) -> (lookup_ebound (ebound G T13) I0 (tshiftTy C0 T13))
      | lookup_ebound_there_evar
          {G : Env} {X7 : (Index TyVar)}
          (T14 : Ty) (T15 : Ty) :
          (lookup_ebound G X7 T14) -> (lookup_ebound (evar G T15) X7 T14)
      | lookup_ebound_there_ebound
          {G : Env} {X7 : (Index TyVar)}
          (T14 : Ty) (T15 : Ty) :
          (lookup_ebound G X7 T14) -> (lookup_ebound (ebound G T15) (IS X7) (tshiftTy C0 T14)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (T14 : Ty) (T15 : Ty) ,
        (lookup_evar (evar G T14) I0 T15) -> (T14 = T15)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_ebound_inversion_here  :
      (forall (G : Env) (T14 : Ty) (T15 : Ty) ,
        (lookup_ebound (ebound G T14) I0 T15) -> ((tshiftTy C0 T14) = T15)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x6 : (Index TmVar)} ,
        (forall (T14 : Ty) ,
          (lookup_evar G x6 T14) -> (forall (T15 : Ty) ,
            (lookup_evar G x6 T15) -> (T14 = T15)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_ebound_functional  :
      (forall {G : Env} {X7 : (Index TyVar)} ,
        (forall (T14 : Ty) ,
          (lookup_ebound G X7 T14) -> (forall (T15 : Ty) ,
            (lookup_ebound G X7 T15) -> (T14 = T15)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x6 : (Index TmVar)} (T14 : Ty) ,
        (lookup_evar G x6 T14) -> (wfTy (domainEnv G) T14)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_ebound_wf  :
      (forall {G : Env} {X7 : (Index TyVar)} (T14 : Ty) ,
        (lookup_ebound G X7 T14) -> (wfTy (domainEnv G) T14)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x6 : (Index TmVar)} (T14 : Ty) ,
        (lookup_evar G x6 T14) -> (lookup_evar (appendEnv G G0) (weakenIndexTmVar x6 (domainEnv G0)) (weakenTy T14 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_ebound  :
      (forall {G : Env} (G0 : Env) {X7 : (Index TyVar)} (T14 : Ty) ,
        (lookup_ebound G X7 T14) -> (lookup_ebound (appendEnv G G0) (weakenIndexTyVar X7 (domainEnv G0)) (weakenTy T14 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x6 : (Index TmVar)} (T18 : Ty) ,
        (lookup_evar G x6 T18) -> (wfindex (domainEnv G) x6)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_ebound_wfindex  :
      (forall {G : Env} {X7 : (Index TyVar)} (T18 : Ty) ,
        (lookup_ebound G X7 T18) -> (wfindex (domainEnv G) X7)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff TmVar) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T14 : Ty} :
        (shift_evar C0 G (evar G T14))
    | shiftevar_there_evar
        {c0 : (Cutoff TmVar)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c0 G G0) -> (shift_evar (CS c0) (evar G T) (evar G0 T))
    | shiftevar_there_ebound
        {c0 : (Cutoff TmVar)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c0 G G0) -> (shift_evar c0 (ebound G T) (ebound G0 T)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c0 : (Cutoff TmVar)} {G0 : Env} {G1 : Env} ,
      (shift_evar c0 G0 G1) -> (shift_evar (weakenCutoffTmVar c0 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_ebound : (Cutoff TyVar) -> Env -> Env -> Prop :=
    | shift_ebound_here {G : Env}
        {T14 : Ty} :
        (shift_ebound C0 G (ebound G T14))
    | shiftebound_there_evar
        {c0 : (Cutoff TyVar)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_ebound c0 G G0) -> (shift_ebound c0 (evar G T) (evar G0 (tshiftTy c0 T)))
    | shiftebound_there_ebound
        {c0 : (Cutoff TyVar)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_ebound c0 G G0) -> (shift_ebound (CS c0) (ebound G T) (ebound G0 (tshiftTy c0 T))).
  Lemma weaken_shift_ebound  :
    (forall (G : Env) {c0 : (Cutoff TyVar)} {G0 : Env} {G1 : Env} ,
      (shift_ebound c0 G0 G1) -> (shift_ebound (weakenCutoffTyVar c0 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 (tshiftEnv c0 G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_TmVar  :
    (forall {c0 : (Cutoff TmVar)} {G : Env} {G0 : Env} ,
      (shift_evar c0 G G0) -> (shifthvl_TmVar c0 (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_ebound_shifthvl_TyVar  :
    (forall {c0 : (Cutoff TyVar)} {G : Env} {G0 : Env} ,
      (shift_ebound c0 G G0) -> (shifthvl_TyVar c0 (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Env) (T14 : Ty) (s6 : Tm) : (Trace TmVar) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T14 s6 X0 (evar G T14) G)
    | subst_evar_there_evar
        {d0 : (Trace TmVar)} {G0 : Env}
        {G1 : Env} (T15 : Ty) :
        (subst_evar G T14 s6 d0 G0 G1) -> (subst_evar G T14 s6 (XS TmVar d0) (evar G0 T15) (evar G1 T15))
    | subst_evar_there_ebound
        {d0 : (Trace TmVar)} {G0 : Env}
        {G1 : Env} (T15 : Ty) :
        (subst_evar G T14 s6 d0 G0 G1) -> (subst_evar G T14 s6 (XS TyVar d0) (ebound G0 T15) (ebound G1 T15)).
  Lemma weaken_subst_evar {G : Env} (T14 : Ty) {s6 : Tm} :
    (forall (G0 : Env) {d0 : (Trace TmVar)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T14 s6 d0 G1 G2) -> (subst_evar G T14 s6 (weakenTrace d0 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_ebound (G : Env) (T14 : Ty) (S7 : Ty) : (Trace TyVar) -> Env -> Env -> Prop :=
    | subst_ebound_here :
        (subst_ebound G T14 S7 X0 (ebound G T14) G)
    | subst_ebound_there_evar
        {d0 : (Trace TyVar)} {G0 : Env}
        {G1 : Env} (T15 : Ty) :
        (subst_ebound G T14 S7 d0 G0 G1) -> (subst_ebound G T14 S7 (XS TmVar d0) (evar G0 T15) (evar G1 (tsubstTy d0 S7 T15)))
    | subst_ebound_there_ebound
        {d0 : (Trace TyVar)} {G0 : Env}
        {G1 : Env} (T15 : Ty) :
        (subst_ebound G T14 S7 d0 G0 G1) -> (subst_ebound G T14 S7 (XS TyVar d0) (ebound G0 T15) (ebound G1 (tsubstTy d0 S7 T15))).
  Lemma weaken_subst_ebound {G : Env} (T14 : Ty) {S7 : Ty} :
    (forall (G0 : Env) {d0 : (Trace TyVar)} {G1 : Env} {G2 : Env} ,
      (subst_ebound G T14 S7 d0 G1 G2) -> (subst_ebound G T14 S7 (weakenTrace d0 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d0 S7 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_TmVar {G : Env} {s6 : Tm} (T14 : Ty) :
    (forall {d0 : (Trace TmVar)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T14 s6 d0 G0 G1) -> (substhvl_TmVar (domainEnv G) d0 (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_ebound_substhvl_TyVar {G : Env} {S7 : Ty} (T15 : Ty) :
    (forall {d0 : (Trace TyVar)} {G0 : Env} {G1 : Env} ,
      (subst_ebound G T15 S7 d0 G0 G1) -> (substhvl_TyVar (domainEnv G) d0 (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
End ContextStuff.
 Hint Rewrite domainEnv_tshiftEnv : interaction.
 Hint Rewrite domainEnv_tshiftEnv : env_domain_shift.
 Hint Rewrite domainEnv_tsubstEnv : interaction.
 Hint Rewrite domainEnv_tsubstEnv : env_domain_subst.
 Hint Rewrite tshiftEnv_appendEnv : interaction.
 Hint Rewrite tshiftEnv_appendEnv : env_shift_append.
 Hint Rewrite tsubstEnv_appendEnv : interaction.
 Hint Rewrite tsubstEnv_appendEnv : env_shift_append.
 Hint Constructors lookup_evar lookup_ebound : infra.
 Hint Constructors lookup_evar lookup_ebound : lookup.
 Hint Constructors lookup_evar lookup_ebound : shift.
 Hint Constructors lookup_evar lookup_ebound : subst.
 Hint Resolve weaken_lookup_evar weaken_lookup_ebound : infra.
 Hint Resolve weaken_lookup_evar weaken_lookup_ebound : lookup.
 Hint Resolve weaken_lookup_evar weaken_lookup_ebound : shift.
 Hint Resolve weaken_lookup_evar weaken_lookup_ebound : weaken.
Lemma weaken_lookup_evar_here  :
  (forall {G : Env} (G0 : Env) {T14 : Ty} (wf : (wfTy (domainEnv G) T14)) ,
    (lookup_evar (appendEnv (evar G T14) G0) (weakenIndexTmVar I0 (domainEnv G0)) (weakenTy T14 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_ebound_here  :
  (forall {G : Env} (G0 : Env) {T14 : Ty} (wf : (wfTy (domainEnv G) T14)) ,
    (lookup_ebound (appendEnv (ebound G T14) G0) (weakenIndexTyVar I0 (domainEnv G0)) (weakenTy (tshiftTy C0 T14) (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfPat wfTm wfTy : infra.
 Hint Constructors wfPat wfTm wfTy : wf.
 Hint Extern 10 ((wfPat _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H47 : (wfTy _ (tvar _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTy _ (top)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTy _ (tarrow _ _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTy _ (tall _ _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTy _ (tprod _ _)) |- _ => inversion H47; subst; clear H47
end : infra wf.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H47 : (wfPat _ (pvar _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfPat _ (pprod _ _)) |- _ => inversion H47; subst; clear H47
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H47 : (wfTm _ (var _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTm _ (abs _ _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTm _ (app _ _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTm _ (tabs _ _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTm _ (tapp _ _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTm _ (prod _ _)) |- _ => inversion H47; subst; clear H47
  | H47 : (wfTm _ (lett _ _ _)) |- _ => inversion H47; subst; clear H47
end : infra wf.
 Hint Resolve lookup_evar_wf lookup_ebound_wf : infra.
 Hint Resolve lookup_evar_wf lookup_ebound_wf : wf.
 Hint Resolve lookup_evar_wfindex lookup_ebound_wfindex : infra.
 Hint Resolve lookup_evar_wfindex lookup_ebound_wfindex : lookup.
 Hint Resolve lookup_evar_wfindex lookup_ebound_wfindex : wf.
 Hint Constructors shift_evar shift_ebound : infra.
 Hint Constructors shift_evar shift_ebound : shift.
 Hint Constructors shift_evar shift_ebound : subst.
 Hint Resolve weaken_shift_evar weaken_shift_ebound : infra.
 Hint Resolve weaken_shift_evar weaken_shift_ebound : shift.
 Hint Resolve shift_evar_shifthvl_TmVar shift_ebound_shifthvl_TyVar : infra.
 Hint Resolve shift_evar_shifthvl_TmVar shift_ebound_shifthvl_TyVar : shift.
 Hint Resolve shift_evar_shifthvl_TmVar shift_ebound_shifthvl_TyVar : shift_wf.
 Hint Resolve shift_evar_shifthvl_TmVar shift_ebound_shifthvl_TyVar : wf.
 Hint Constructors subst_evar subst_ebound : infra.
 Hint Constructors subst_evar subst_ebound : subst.
 Hint Resolve weaken_subst_evar weaken_subst_ebound : infra.
 Hint Resolve weaken_subst_evar weaken_subst_ebound : subst.
 Hint Resolve subst_evar_substhvl_TmVar subst_ebound_substhvl_TyVar : infra.
 Hint Resolve subst_evar_substhvl_TmVar subst_ebound_substhvl_TyVar : subst.
 Hint Resolve subst_evar_substhvl_TmVar subst_ebound_substhvl_TyVar : subst_wf.
 Hint Resolve subst_evar_substhvl_TmVar subst_ebound_substhvl_TyVar : wf.
 Hint Resolve subst_evar_substhvl_TmVar subst_ebound_substhvl_TyVar : substenv_substhvl.
Lemma shift_evar_lookup_evar  :
  (forall {c0 : (Cutoff TmVar)} {G : Env} {G0 : Env} (ins : (shift_evar c0 G G0)) {x6 : (Index TmVar)} {T14 : Ty} ,
    (lookup_evar G x6 T14) -> (lookup_evar G0 (shiftIndex c0 x6) T14)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_ebound  :
  (forall {c0 : (Cutoff TmVar)} {G : Env} {G0 : Env} (ins : (shift_evar c0 G G0)) {X7 : (Index TyVar)} {T14 : Ty} ,
    (lookup_ebound G X7 T14) -> (lookup_ebound G0 X7 T14)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_ebound_lookup_evar  :
  (forall {c0 : (Cutoff TyVar)} {G : Env} {G0 : Env} (ins : (shift_ebound c0 G G0)) {x6 : (Index TmVar)} {T14 : Ty} ,
    (lookup_evar G x6 T14) -> (lookup_evar G0 x6 (tshiftTy c0 T14))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_ebound_lookup_ebound  :
  (forall {c0 : (Cutoff TyVar)} {G : Env} {G0 : Env} (ins : (shift_ebound c0 G G0)) {X7 : (Index TyVar)} {T14 : Ty} ,
    (lookup_ebound G X7 T14) -> (lookup_ebound G0 (tshiftIndex c0 X7) (tshiftTy c0 T14))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_ebound shift_ebound_lookup_evar shift_ebound_lookup_ebound : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_ebound shift_ebound_lookup_evar shift_ebound_lookup_ebound : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_ebound shift_ebound_lookup_evar shift_ebound_lookup_ebound : shift.
Lemma subst_evar_lookup_ebound {G : Env} (T16 : Ty) {s6 : Tm} :
  (forall {d0 : (Trace TmVar)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T16 s6 d0 G0 G1)) {X7 : (Index TyVar)} (T17 : Ty) ,
    (lookup_ebound G0 X7 T17) -> (lookup_ebound G1 X7 T17)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_ebound_lookup_evar {G : Env} (T16 : Ty) {S7 : Ty} (wf : (wfTy (domainEnv G) S7)) :
  (forall {d0 : (Trace TyVar)} {G0 : Env} {G1 : Env} (sub : (subst_ebound G T16 S7 d0 G0 G1)) {x6 : (Index TmVar)} (T17 : Ty) ,
    (lookup_evar G0 x6 T17) -> (lookup_evar G1 x6 (tsubstTy d0 S7 T17))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_ebound subst_ebound_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_ebound subst_ebound_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_ebound subst_ebound_lookup_evar : subst.
Fixpoint size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (tvar X7) => 1
    | (top) => 1
    | (tarrow T12 T13) => (plus 1 (plus (size_Ty T12) (size_Ty T13)))
    | (tall T14 T15) => (plus 1 (plus (size_Ty T14) (size_Ty T15)))
    | (tprod T16 T17) => (plus 1 (plus (size_Ty T16) (size_Ty T17)))
  end.
Fixpoint size_Pat (p9 : Pat) {struct p9} :
nat :=
  match p9 with
    | (pvar T12) => (plus 1 (size_Ty T12))
    | (pprod p10 p11) => (plus 1 (plus (size_Pat p10) (size_Pat p11)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x6) => 1
    | (abs T12 t8) => (plus 1 (plus (size_Ty T12) (size_Tm t8)))
    | (app t9 t10) => (plus 1 (plus (size_Tm t9) (size_Tm t10)))
    | (tabs T13 t11) => (plus 1 (plus (size_Ty T13) (size_Tm t11)))
    | (tapp t12 T14) => (plus 1 (plus (size_Tm t12) (size_Ty T14)))
    | (prod t13 t14) => (plus 1 (plus (size_Tm t13) (size_Tm t14)))
    | (lett p9 t15 t16) => (plus 1 (plus (size_Pat p9) (plus (size_Tm t15) (size_Tm t16))))
  end.
Fixpoint tshift_size_Ty (S1 : Ty) (c0 : (Cutoff TyVar)) {struct S1} :
((size_Ty (tshiftTy c0 S1)) = (size_Ty S1)) :=
  match S1 return ((size_Ty (tshiftTy c0 S1)) = (size_Ty S1)) with
    | (tvar _) => eq_refl
    | (top) => eq_refl
    | (tarrow T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c0) (tshift_size_Ty T2 c0)))
    | (tall T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c0) (tshift_size_Ty T2 (CS c0))))
    | (tprod T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c0) (tshift_size_Ty T2 c0)))
  end.
Fixpoint tshift_size_Pat (p11 : Pat) (c0 : (Cutoff TyVar)) {struct p11} :
((size_Pat (tshiftPat c0 p11)) = (size_Pat p11)) :=
  match p11 return ((size_Pat (tshiftPat c0 p11)) = (size_Pat p11)) with
    | (pvar T) => (f_equal2 plus eq_refl (tshift_size_Ty T c0))
    | (pprod p1 p2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Pat p1 c0) (tshift_size_Pat p2 (weakenCutoffTyVar c0 (appendHvl H0 (bindPat p1))))))
  end.
Fixpoint shift_size_Tm (s : Tm) (c0 : (Cutoff TmVar)) {struct s} :
((size_Tm (shiftTm c0 s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c0 s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c0))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c0) (shift_size_Tm t2 c0)))
    | (tabs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t c0)))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c0) eq_refl))
    | (prod t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c0) (shift_size_Tm t2 c0)))
    | (lett p t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c0) (shift_size_Tm t2 (weakenCutoffTmVar c0 (appendHvl H0 (bindPat p)))))))
  end.
Fixpoint tshift_size_Tm (s : Tm) (c0 : (Cutoff TyVar)) {struct s} :
((size_Tm (tshiftTm c0 s)) = (size_Tm s)) :=
  match s return ((size_Tm (tshiftTm c0 s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c0) (tshift_size_Tm t c0)))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c0) (tshift_size_Tm t2 c0)))
    | (tabs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c0) (tshift_size_Tm t (CS c0))))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t c0) (tshift_size_Ty T c0)))
    | (prod t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c0) (tshift_size_Tm t2 c0)))
    | (lett p t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Pat p c0) (f_equal2 plus (tshift_size_Tm t1 c0) (tshift_size_Tm t2 (weakenCutoffTyVar c0 (appendHvl H0 (bindPat p)))))))
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
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutoffTmVar_append weakenCutoffTyVar_append weakenTrace_append weakenPat_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.