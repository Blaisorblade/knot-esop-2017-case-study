Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export Needle.

Local Set Asymmetric Patterns.

Section Namespace.
  Inductive Namespace : Type :=
    | ty 
    | tm .
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
  
  Fixpoint weakenIndexty (X23 : (Index ty)) (k : Hvl) {struct k} :
  (Index ty) :=
    match k with
      | (H0) => X23
      | (HS a k) => match a with
        | (ty) => (IS (weakenIndexty X23 k))
        | _ => (weakenIndexty X23 k)
      end
    end.
  Fixpoint weakenIndextm (x18 : (Index tm)) (k : Hvl) {struct k} :
  (Index tm) :=
    match k with
      | (H0) => x18
      | (HS a k) => match a with
        | (tm) => (IS (weakenIndextm x18 k))
        | _ => (weakenIndextm x18 k)
      end
    end.
  Lemma weakenIndexty_append  :
    (forall (X23 : (Index ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexty (weakenIndexty X23 k) k0) = (weakenIndexty X23 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndextm_append  :
    (forall (x18 : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x18 k) k0) = (weakenIndextm x18 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Ty : Set :=
    | tvar (X : (Index ty))
    | tarr (T1 : Ty) (T2 : Ty)
    | tall (T : Ty)
    | texist (T : Ty)
    | tprod (T1 : Ty) (T2 : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Pat : Set :=
    | pvar (T : Ty)
    | pprod (p1 : Pat) (p2 : Pat).
  Scheme ind_Pat := Induction for Pat Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tabs (t : Tm)
    | tapp (t : Tm) (T : Ty)
    | pack (T1 : Ty) (t : Tm)
        (T2 : Ty)
    | unpack (t1 : Tm) (t2 : Tm)
    | prod (t1 : Tm) (t2 : Tm)
    | case (t1 : Tm) (p : Pat)
        (t2 : Tm).
  Scheme ind_Tm := Induction for Tm Sort Prop.
End Terms.

Section Functions.
  Fixpoint bindPat (p17 : Pat) {struct p17} :
  Hvl :=
    match p17 with
      | (pvar T) => (HS tm H0)
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
  Fixpoint weakenCutoffty (c : (Cutoff ty)) (k : Hvl) {struct k} :
  (Cutoff ty) :=
    match k with
      | (H0) => c
      | (HS a k) => match a with
        | (ty) => (CS (weakenCutoffty c k))
        | _ => (weakenCutoffty c k)
      end
    end.
  Fixpoint weakenCutofftm (c : (Cutoff tm)) (k : Hvl) {struct k} :
  (Cutoff tm) :=
    match k with
      | (H0) => c
      | (HS a k) => match a with
        | (tm) => (CS (weakenCutofftm c k))
        | _ => (weakenCutofftm c k)
      end
    end.
  
  Lemma weakenCutoffty_append  :
    (forall (c : (Cutoff ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffty (weakenCutoffty c k) k0) = (weakenCutoffty c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenCutofftm_append  :
    (forall (c : (Cutoff tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutofftm (weakenCutofftm c k) k0) = (weakenCutofftm c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint tshiftIndex (c : (Cutoff ty)) (X23 : (Index ty)) {struct c} :
  (Index ty) :=
    match c with
      | (C0) => (IS X23)
      | (CS c) => match X23 with
        | (I0) => I0
        | (IS X23) => (IS (tshiftIndex c X23))
      end
    end.
  Fixpoint shiftIndex (c : (Cutoff tm)) (x18 : (Index tm)) {struct c} :
  (Index tm) :=
    match c with
      | (C0) => (IS x18)
      | (CS c) => match x18 with
        | (I0) => I0
        | (IS x18) => (IS (shiftIndex c x18))
      end
    end.
  Fixpoint tshiftTy (c : (Cutoff ty)) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (tvar X23) => (tvar (tshiftIndex c X23))
      | (tarr T53 T54) => (tarr (tshiftTy c T53) (tshiftTy c T54))
      | (tall T55) => (tall (tshiftTy (CS c) T55))
      | (texist T56) => (texist (tshiftTy (CS c) T56))
      | (tprod T57 T58) => (tprod (tshiftTy c T57) (tshiftTy c T58))
    end.
  Fixpoint tshiftPat (c : (Cutoff ty)) (p18 : Pat) {struct p18} :
  Pat :=
    match p18 with
      | (pvar T53) => (pvar (tshiftTy c T53))
      | (pprod p19 p20) => (pprod (tshiftPat c p19) (tshiftPat (weakenCutoffty c (appendHvl H0 (bindPat p19))) p20))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x18) => (var (shiftIndex c x18))
      | (abs T53 t36) => (abs T53 (shiftTm (CS c) t36))
      | (app t37 t38) => (app (shiftTm c t37) (shiftTm c t38))
      | (tabs t39) => (tabs (shiftTm c t39))
      | (tapp t40 T54) => (tapp (shiftTm c t40) T54)
      | (pack T55 t41 T56) => (pack T55 (shiftTm c t41) T56)
      | (unpack t42 t43) => (unpack (shiftTm c t42) (shiftTm (CS c) t43))
      | (prod t44 t45) => (prod (shiftTm c t44) (shiftTm c t45))
      | (case t46 p18 t47) => (case (shiftTm c t46) p18 (shiftTm (weakenCutofftm c (appendHvl H0 (bindPat p18))) t47))
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x18) => (var x18)
      | (abs T53 t36) => (abs (tshiftTy c T53) (tshiftTm c t36))
      | (app t37 t38) => (app (tshiftTm c t37) (tshiftTm c t38))
      | (tabs t39) => (tabs (tshiftTm (CS c) t39))
      | (tapp t40 T54) => (tapp (tshiftTm c t40) (tshiftTy c T54))
      | (pack T55 t41 T56) => (pack (tshiftTy c T55) (tshiftTm c t41) (tshiftTy c T56))
      | (unpack t42 t43) => (unpack (tshiftTm c t42) (tshiftTm (CS c) t43))
      | (prod t44 t45) => (prod (tshiftTm c t44) (tshiftTm c t45))
      | (case t46 p18 t47) => (case (tshiftTm c t46) (tshiftPat c p18) (tshiftTm (weakenCutoffty c (appendHvl H0 (bindPat p18))) t47))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S0
      | (HS tm k) => (weakenTy S0 k)
      | (HS ty k) => (tshiftTy C0 (weakenTy S0 k))
    end.
  Fixpoint weakenPat (p18 : Pat) (k : Hvl) {struct k} :
  Pat :=
    match k with
      | (H0) => p18
      | (HS tm k) => (weakenPat p18 k)
      | (HS ty k) => (tshiftPat C0 (weakenPat p18 k))
    end.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} :
  Tm :=
    match k with
      | (H0) => s
      | (HS tm k) => (shiftTm C0 (weakenTm s k))
      | (HS ty k) => (tshiftTm C0 (weakenTm s k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T53 : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x18 : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x18
      | (HS b k) => (XS b (weakenTrace x18 k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x18 : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x18 k) k0) = (weakenTrace x18 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint tsubstIndex (d : (Trace ty)) (S0 : Ty) (X23 : (Index ty)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X23 with
        | (I0) => S0
        | (IS X23) => (tvar X23)
      end
      | (XS tm d) => (tsubstIndex d S0 X23)
      | (XS ty d) => match X23 with
        | (I0) => (tvar I0)
        | (IS X23) => (tshiftTy C0 (tsubstIndex d S0 X23))
      end
    end.
  Fixpoint substIndex (d : (Trace tm)) (s : Tm) (x18 : (Index tm)) {struct d} :
  Tm :=
    match d with
      | (X0) => match x18 with
        | (I0) => s
        | (IS x18) => (var x18)
      end
      | (XS tm d) => match x18 with
        | (I0) => (var I0)
        | (IS x18) => (shiftTm C0 (substIndex d s x18))
      end
      | (XS ty d) => (tshiftTm C0 (substIndex d s x18))
    end.
  Fixpoint tsubstTy (d : (Trace ty)) (S0 : Ty) (S1 : Ty) {struct S1} :
  Ty :=
    match S1 with
      | (tvar X23) => (tsubstIndex d S0 X23)
      | (tarr T53 T54) => (tarr (tsubstTy d S0 T53) (tsubstTy d S0 T54))
      | (tall T55) => (tall (tsubstTy (weakenTrace d (HS ty H0)) S0 T55))
      | (texist T56) => (texist (tsubstTy (weakenTrace d (HS ty H0)) S0 T56))
      | (tprod T57 T58) => (tprod (tsubstTy d S0 T57) (tsubstTy d S0 T58))
    end.
  Fixpoint tsubstPat (d : (Trace ty)) (S0 : Ty) (p18 : Pat) {struct p18} :
  Pat :=
    match p18 with
      | (pvar T53) => (pvar (tsubstTy d S0 T53))
      | (pprod p19 p20) => (pprod (tsubstPat d S0 p19) (tsubstPat (weakenTrace d (appendHvl H0 (bindPat p19))) S0 p20))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x18) => (substIndex d s x18)
      | (abs T53 t36) => (abs T53 (substTm (weakenTrace d (HS tm H0)) s t36))
      | (app t37 t38) => (app (substTm d s t37) (substTm d s t38))
      | (tabs t39) => (tabs (substTm (weakenTrace d (HS ty H0)) s t39))
      | (tapp t40 T54) => (tapp (substTm d s t40) T54)
      | (pack T55 t41 T56) => (pack T55 (substTm d s t41) T56)
      | (unpack t42 t43) => (unpack (substTm d s t42) (substTm (weakenTrace d (HS tm (HS ty H0))) s t43))
      | (prod t44 t45) => (prod (substTm d s t44) (substTm d s t45))
      | (case t46 p18 t47) => (case (substTm d s t46) p18 (substTm (weakenTrace d (appendHvl H0 (bindPat p18))) s t47))
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x18) => (var x18)
      | (abs T53 t36) => (abs (tsubstTy d S0 T53) (tsubstTm (weakenTrace d (HS tm H0)) S0 t36))
      | (app t37 t38) => (app (tsubstTm d S0 t37) (tsubstTm d S0 t38))
      | (tabs t39) => (tabs (tsubstTm (weakenTrace d (HS ty H0)) S0 t39))
      | (tapp t40 T54) => (tapp (tsubstTm d S0 t40) (tsubstTy d S0 T54))
      | (pack T55 t41 T56) => (pack (tsubstTy d S0 T55) (tsubstTm d S0 t41) (tsubstTy d S0 T56))
      | (unpack t42 t43) => (unpack (tsubstTm d S0 t42) (tsubstTm (weakenTrace d (HS tm (HS ty H0))) S0 t43))
      | (prod t44 t45) => (prod (tsubstTm d S0 t44) (tsubstTm d S0 t45))
      | (case t46 p18 t47) => (case (tsubstTm d S0 t46) (tsubstPat d S0 p18) (tsubstTm (weakenTrace d (appendHvl H0 (bindPat p18))) S0 t47))
    end.
End Subst.

Global Hint Resolve (f_equal (tshiftPat C0)) : cong_shift0.
Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_tshift_bindPat  :
  (forall (p18 : Pat) ,
    (forall (c : (Cutoff ty)) ,
      ((bindPat (tshiftPat c p18)) = (bindPat p18)))).
Proof.
  apply_mutual_ind (ind_bindPat_Pat); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_tshift_bindPat : interaction.
 Hint Rewrite stability_tshift_bindPat : stability_shift.
Lemma stability_weaken_bindPat  :
  (forall (k : Hvl) (p19 : Pat) ,
    ((bindPat (weakenPat p19 k)) = (bindPat p19))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bindPat : interaction.
 Hint Rewrite stability_weaken_bindPat : stability_weaken.
Lemma stability_tsubst_bindPat  :
  (forall (p19 : Pat) ,
    (forall (d : (Trace ty)) (S0 : Ty) ,
      ((bindPat (tsubstPat d S0 p19)) = (bindPat p19)))).
Proof.
  apply_mutual_ind (ind_bindPat_Pat); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_tsubst_bindPat : interaction.
 Hint Rewrite stability_tsubst_bindPat : stability_subst.
Section SubstShiftReflection.
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S1 : Ty) :
    (forall (k : Hvl) (X23 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k) S1 (tshiftIndex (weakenCutoffty C0 k) X23)) = (tvar X23))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x18 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k) s (shiftIndex (weakenCutofftm C0 k) x18)) = (var x18))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint tsubst0_tshift0_Ty_reflection_ind (S2 : Ty) (k : Hvl) (S1 : Ty) {struct S2} :
  ((tsubstTy (weakenTrace X0 k) S1 (tshiftTy (weakenCutoffty C0 k) S2)) = S2) :=
    match S2 return ((tsubstTy (weakenTrace X0 k) S1 (tshiftTy (weakenCutoffty C0 k) S2)) = S2) with
      | (tvar X23) => (tsubstIndex0_tshiftIndex0_reflection_ind S1 k X23)
      | (tarr T54 T55) => (f_equal2 tarr (tsubst0_tshift0_Ty_reflection_ind T54 k S1) (tsubst0_tshift0_Ty_reflection_ind T55 k S1))
      | (tall T53) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T53 (HS ty k) S1)))
      | (texist T53) => (f_equal texist (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T53 (HS ty k) S1)))
      | (tprod T54 T55) => (f_equal2 tprod (tsubst0_tshift0_Ty_reflection_ind T54 k S1) (tsubst0_tshift0_Ty_reflection_ind T55 k S1))
    end.
  Fixpoint tsubst0_tshift0_Pat_reflection_ind (p20 : Pat) (k : Hvl) (S1 : Ty) {struct p20} :
  ((tsubstPat (weakenTrace X0 k) S1 (tshiftPat (weakenCutoffty C0 k) p20)) = p20) :=
    match p20 return ((tsubstPat (weakenTrace X0 k) S1 (tshiftPat (weakenCutoffty C0 k) p20)) = p20) with
      | (pvar T53) => (f_equal pvar (tsubst0_tshift0_Ty_reflection_ind T53 k S1))
      | (pprod p21 p22) => (f_equal2 pprod (tsubst0_tshift0_Pat_reflection_ind p21 k S1) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21)))) eq_refl (f_equal2 tshiftPat (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21))) eq_refl)) (tsubst0_tshift0_Pat_reflection_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) S1)))
    end.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) with
      | (var x18) => (substIndex0_shiftIndex0_reflection_ind s k x18)
      | (abs T53 t36) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t36 (HS tm k) s)))
      | (app t37 t38) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t37 k s) (subst0_shift0_Tm_reflection_ind t38 k s))
      | (tabs t36) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t36 (HS ty k) s)))
      | (tapp t36 T53) => (f_equal2 tapp (subst0_shift0_Tm_reflection_ind t36 k s) eq_refl)
      | (pack T54 t36 T55) => (f_equal3 pack eq_refl (subst0_shift0_Tm_reflection_ind t36 k s) eq_refl)
      | (unpack t37 t38) => (f_equal2 unpack (subst0_shift0_Tm_reflection_ind t37 k s) (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm (HS ty H0))) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t38 (HS tm (HS ty k)) s)))
      | (prod t37 t38) => (f_equal2 prod (subst0_shift0_Tm_reflection_ind t37 k s) (subst0_shift0_Tm_reflection_ind t38 k s))
      | (case t37 p20 t38) => (f_equal3 case (subst0_shift0_Tm_reflection_ind t37 k s) eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (subst0_shift0_Tm_reflection_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) s)))
    end.
  Fixpoint tsubst0_tshift0_Tm_reflection_ind (s : Tm) (k : Hvl) (S1 : Ty) {struct s} :
  ((tsubstTm (weakenTrace X0 k) S1 (tshiftTm (weakenCutoffty C0 k) s)) = s) :=
    match s return ((tsubstTm (weakenTrace X0 k) S1 (tshiftTm (weakenCutoffty C0 k) s)) = s) with
      | (var x18) => eq_refl
      | (abs T53 t36) => (f_equal2 abs (tsubst0_tshift0_Ty_reflection_ind T53 k S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t36 (HS tm k) S1)))
      | (app t37 t38) => (f_equal2 app (tsubst0_tshift0_Tm_reflection_ind t37 k S1) (tsubst0_tshift0_Tm_reflection_ind t38 k S1))
      | (tabs t36) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t36 (HS ty k) S1)))
      | (tapp t36 T53) => (f_equal2 tapp (tsubst0_tshift0_Tm_reflection_ind t36 k S1) (tsubst0_tshift0_Ty_reflection_ind T53 k S1))
      | (pack T54 t36 T55) => (f_equal3 pack (tsubst0_tshift0_Ty_reflection_ind T54 k S1) (tsubst0_tshift0_Tm_reflection_ind t36 k S1) (tsubst0_tshift0_Ty_reflection_ind T55 k S1))
      | (unpack t37 t38) => (f_equal2 unpack (tsubst0_tshift0_Tm_reflection_ind t37 k S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm (HS ty H0))) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t38 (HS tm (HS ty k)) S1)))
      | (prod t37 t38) => (f_equal2 prod (tsubst0_tshift0_Tm_reflection_ind t37 k S1) (tsubst0_tshift0_Tm_reflection_ind t38 k S1))
      | (case t37 p20 t38) => (f_equal3 case (tsubst0_tshift0_Tm_reflection_ind t37 k S1) (tsubst0_tshift0_Pat_reflection_ind p20 k S1) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (tsubst0_tshift0_Tm_reflection_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) S1)))
    end.
  Definition tsubstTy0_tshiftTy0_reflection (S2 : Ty) : (forall (S1 : Ty) ,
    ((tsubstTy X0 S1 (tshiftTy C0 S2)) = S2)) := (tsubst0_tshift0_Ty_reflection_ind S2 H0).
  Definition tsubstPat0_tshiftPat0_reflection (p20 : Pat) : (forall (S1 : Ty) ,
    ((tsubstPat X0 S1 (tshiftPat C0 p20)) = p20)) := (tsubst0_tshift0_Pat_reflection_ind p20 H0).
  Definition substTm0_shiftTm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((substTm X0 s (shiftTm C0 s0)) = s0)) := (subst0_shift0_Tm_reflection_ind s0 H0).
  Definition tsubstTm0_tshiftTm0_reflection (s : Tm) : (forall (S1 : Ty) ,
    ((tsubstTm X0 S1 (tshiftTm C0 s)) = s)) := (tsubst0_tshift0_Tm_reflection_ind s H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c0 : (Cutoff ty)) (X23 : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c0) k) (tshiftIndex (weakenCutoffty C0 k) X23)) = (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c0 k) X23)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c0 : (Cutoff tm)) (x18 : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c0) k) (shiftIndex (weakenCutofftm C0 k) x18)) = (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c0 k) x18)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint tshift_tshift0_Ty_comm_ind (S1 : Ty) (k : Hvl) (c0 : (Cutoff ty)) {struct S1} :
    ((tshiftTy (weakenCutoffty (CS c0) k) (tshiftTy (weakenCutoffty C0 k) S1)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c0 k) S1))) :=
      match S1 return ((tshiftTy (weakenCutoffty (CS c0) k) (tshiftTy (weakenCutoffty C0 k) S1)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c0 k) S1))) with
        | (tvar X23) => (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k c0 X23))
        | (tarr T54 T55) => (f_equal2 tarr (tshift_tshift0_Ty_comm_ind T54 k c0) (tshift_tshift0_Ty_comm_ind T55 k c0))
        | (tall T53) => (f_equal tall (tshift_tshift0_Ty_comm_ind T53 (HS ty k) c0))
        | (texist T53) => (f_equal texist (tshift_tshift0_Ty_comm_ind T53 (HS ty k) c0))
        | (tprod T54 T55) => (f_equal2 tprod (tshift_tshift0_Ty_comm_ind T54 k c0) (tshift_tshift0_Ty_comm_ind T55 k c0))
      end.
    Fixpoint tshift_tshift0_Pat_comm_ind (p20 : Pat) (k : Hvl) (c0 : (Cutoff ty)) {struct p20} :
    ((tshiftPat (weakenCutoffty (CS c0) k) (tshiftPat (weakenCutoffty C0 k) p20)) = (tshiftPat (weakenCutoffty C0 k) (tshiftPat (weakenCutoffty c0 k) p20))) :=
      match p20 return ((tshiftPat (weakenCutoffty (CS c0) k) (tshiftPat (weakenCutoffty C0 k) p20)) = (tshiftPat (weakenCutoffty C0 k) (tshiftPat (weakenCutoffty c0 k) p20))) with
        | (pvar T53) => (f_equal pvar (tshift_tshift0_Ty_comm_ind T53 k c0))
        | (pprod p21 p22) => (f_equal2 pprod (tshift_tshift0_Pat_comm_ind p21 k c0) (eq_trans (f_equal2 tshiftPat (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutoffty_append (CS c0) k (appendHvl H0 (bindPat p21)))) (f_equal2 tshiftPat (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21))) eq_refl)) (eq_trans (tshift_tshift0_Pat_comm_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) c0) (f_equal2 tshiftPat (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftPat (eq_sym (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p21)))) eq_refl)))))
      end.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm (CS c0) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c0 k) s))) :=
      match s return ((shiftTm (weakenCutofftm (CS c0) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c0 k) s))) with
        | (var x18) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c0 x18))
        | (abs T53 t36) => (f_equal2 abs eq_refl (shift_shift0_Tm_comm_ind t36 (HS tm k) c0))
        | (app t37 t38) => (f_equal2 app (shift_shift0_Tm_comm_ind t37 k c0) (shift_shift0_Tm_comm_ind t38 k c0))
        | (tabs t36) => (f_equal tabs (shift_shift0_Tm_comm_ind t36 (HS ty k) c0))
        | (tapp t36 T53) => (f_equal2 tapp (shift_shift0_Tm_comm_ind t36 k c0) eq_refl)
        | (pack T54 t36 T55) => (f_equal3 pack eq_refl (shift_shift0_Tm_comm_ind t36 k c0) eq_refl)
        | (unpack t37 t38) => (f_equal2 unpack (shift_shift0_Tm_comm_ind t37 k c0) (shift_shift0_Tm_comm_ind t38 (HS tm (HS ty k)) c0))
        | (prod t37 t38) => (f_equal2 prod (shift_shift0_Tm_comm_ind t37 k c0) (shift_shift0_Tm_comm_ind t38 k c0))
        | (case t37 p20 t38) => (f_equal3 case (shift_shift0_Tm_comm_ind t37 k c0) eq_refl (eq_trans (f_equal2 shiftTm (weakenCutofftm_append (CS c0) k (appendHvl H0 (bindPat p20))) (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (shift_shift0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) c0) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint shift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm c0 k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c0 k) s))) :=
      match s return ((shiftTm (weakenCutofftm c0 k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c0 k) s))) with
        | (var x18) => eq_refl
        | (abs T53 t36) => (f_equal2 abs eq_refl (shift_tshift0_Tm_comm_ind t36 (HS tm k) c0))
        | (app t37 t38) => (f_equal2 app (shift_tshift0_Tm_comm_ind t37 k c0) (shift_tshift0_Tm_comm_ind t38 k c0))
        | (tabs t36) => (f_equal tabs (shift_tshift0_Tm_comm_ind t36 (HS ty k) c0))
        | (tapp t36 T53) => (f_equal2 tapp (shift_tshift0_Tm_comm_ind t36 k c0) eq_refl)
        | (pack T54 t36 T55) => (f_equal3 pack eq_refl (shift_tshift0_Tm_comm_ind t36 k c0) eq_refl)
        | (unpack t37 t38) => (f_equal2 unpack (shift_tshift0_Tm_comm_ind t37 k c0) (shift_tshift0_Tm_comm_ind t38 (HS tm (HS ty k)) c0))
        | (prod t37 t38) => (f_equal2 prod (shift_tshift0_Tm_comm_ind t37 k c0) (shift_tshift0_Tm_comm_ind t38 k c0))
        | (case t37 p20 t38) => (f_equal3 case (shift_tshift0_Tm_comm_ind t37 k c0) eq_refl (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (shift_tshift0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) c0) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint tshift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty c0 k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c0 k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c0 k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c0 k) s))) with
        | (var x18) => eq_refl
        | (abs T53 t36) => (f_equal2 abs eq_refl (tshift_shift0_Tm_comm_ind t36 (HS tm k) c0))
        | (app t37 t38) => (f_equal2 app (tshift_shift0_Tm_comm_ind t37 k c0) (tshift_shift0_Tm_comm_ind t38 k c0))
        | (tabs t36) => (f_equal tabs (tshift_shift0_Tm_comm_ind t36 (HS ty k) c0))
        | (tapp t36 T53) => (f_equal2 tapp (tshift_shift0_Tm_comm_ind t36 k c0) eq_refl)
        | (pack T54 t36 T55) => (f_equal3 pack eq_refl (tshift_shift0_Tm_comm_ind t36 k c0) eq_refl)
        | (unpack t37 t38) => (f_equal2 unpack (tshift_shift0_Tm_comm_ind t37 k c0) (tshift_shift0_Tm_comm_ind t38 (HS tm (HS ty k)) c0))
        | (prod t37 t38) => (f_equal2 prod (tshift_shift0_Tm_comm_ind t37 k c0) (tshift_shift0_Tm_comm_ind t38 k c0))
        | (case t37 p20 t38) => (f_equal3 case (tshift_shift0_Tm_comm_ind t37 k c0) eq_refl (eq_trans (f_equal2 tshiftTm (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20))) (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (tshift_shift0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) c0) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint tshift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty (CS c0) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c0 k) s))) :=
      match s return ((tshiftTm (weakenCutoffty (CS c0) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c0 k) s))) with
        | (var x18) => eq_refl
        | (abs T53 t36) => (f_equal2 abs (tshift_tshift0_Ty_comm_ind T53 k c0) (tshift_tshift0_Tm_comm_ind t36 (HS tm k) c0))
        | (app t37 t38) => (f_equal2 app (tshift_tshift0_Tm_comm_ind t37 k c0) (tshift_tshift0_Tm_comm_ind t38 k c0))
        | (tabs t36) => (f_equal tabs (tshift_tshift0_Tm_comm_ind t36 (HS ty k) c0))
        | (tapp t36 T53) => (f_equal2 tapp (tshift_tshift0_Tm_comm_ind t36 k c0) (tshift_tshift0_Ty_comm_ind T53 k c0))
        | (pack T54 t36 T55) => (f_equal3 pack (tshift_tshift0_Ty_comm_ind T54 k c0) (tshift_tshift0_Tm_comm_ind t36 k c0) (tshift_tshift0_Ty_comm_ind T55 k c0))
        | (unpack t37 t38) => (f_equal2 unpack (tshift_tshift0_Tm_comm_ind t37 k c0) (tshift_tshift0_Tm_comm_ind t38 (HS tm (HS ty k)) c0))
        | (prod t37 t38) => (f_equal2 prod (tshift_tshift0_Tm_comm_ind t37 k c0) (tshift_tshift0_Tm_comm_ind t38 k c0))
        | (case t37 p20 t38) => (f_equal3 case (tshift_tshift0_Tm_comm_ind t37 k c0) (tshift_tshift0_Pat_comm_ind p20 k c0) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutoffty_append (CS c0) k (appendHvl H0 (bindPat p20)))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (tshift_tshift0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) c0) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_Ty_comm (S1 : Ty) : (forall (c0 : (Cutoff ty)) ,
      ((tshiftTy (CS c0) (tshiftTy C0 S1)) = (tshiftTy C0 (tshiftTy c0 S1)))) := (tshift_tshift0_Ty_comm_ind S1 H0).
    Definition tshift_tshift0_Pat_comm (p20 : Pat) : (forall (c0 : (Cutoff ty)) ,
      ((tshiftPat (CS c0) (tshiftPat C0 p20)) = (tshiftPat C0 (tshiftPat c0 p20)))) := (tshift_tshift0_Pat_comm_ind p20 H0).
    Definition shift_shift0_Tm_comm (s : Tm) : (forall (c0 : (Cutoff tm)) ,
      ((shiftTm (CS c0) (shiftTm C0 s)) = (shiftTm C0 (shiftTm c0 s)))) := (shift_shift0_Tm_comm_ind s H0).
    Definition shift_tshift0_Tm_comm (s : Tm) : (forall (c0 : (Cutoff tm)) ,
      ((shiftTm c0 (tshiftTm C0 s)) = (tshiftTm C0 (shiftTm c0 s)))) := (shift_tshift0_Tm_comm_ind s H0).
    Definition tshift_shift0_Tm_comm (s : Tm) : (forall (c0 : (Cutoff ty)) ,
      ((tshiftTm c0 (shiftTm C0 s)) = (shiftTm C0 (tshiftTm c0 s)))) := (tshift_shift0_Tm_comm_ind s H0).
    Definition tshift_tshift0_Tm_comm (s : Tm) : (forall (c0 : (Cutoff ty)) ,
      ((tshiftTm (CS c0) (tshiftTm C0 s)) = (tshiftTm C0 (tshiftTm c0 s)))) := (tshift_tshift0_Tm_comm_ind s H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite tshift_tshift0_Pat_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : interaction.
 Hint Rewrite tshift_tshift0_Pat_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTy_tshiftTy  :
    (forall (k : Hvl) (c0 : (Cutoff ty)) (S1 : Ty) ,
      ((weakenTy (tshiftTy c0 S1) k) = (tshiftTy (weakenCutoffty c0 k) (weakenTy S1 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenPat_tshiftPat  :
    (forall (k : Hvl) (c0 : (Cutoff ty)) (p20 : Pat) ,
      ((weakenPat (tshiftPat c0 p20) k) = (tshiftPat (weakenCutoffty c0 k) (weakenPat p20 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k : Hvl) (c0 : (Cutoff tm)) (s : Tm) ,
      ((weakenTm (shiftTm c0 s) k) = (shiftTm (weakenCutofftm c0 k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k : Hvl) (c0 : (Cutoff ty)) (s : Tm) ,
      ((weakenTm (tshiftTm c0 s) k) = (tshiftTm (weakenCutoffty c0 k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma tshiftTy_tsubstIndex0_comm_ind (c0 : (Cutoff ty)) (S1 : Ty) :
      (forall (k : Hvl) (X23 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c0 k) (tsubstIndex (weakenTrace X0 k) S1 X23)) = (tsubstIndex (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftIndex (weakenCutoffty (CS c0) k) X23)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shiftTm_substIndex0_comm_ind (c0 : (Cutoff tm)) (s : Tm) :
      (forall (k : Hvl) (x18 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c0 k) (substIndex (weakenTrace X0 k) s x18)) = (substIndex (weakenTrace X0 k) (shiftTm c0 s) (shiftIndex (weakenCutofftm (CS c0) k) x18)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_substIndex0_comm_ind (c0 : (Cutoff ty)) (s : Tm) :
      (forall (k : Hvl) (x18 : (Index tm)) ,
        ((tshiftTm (weakenCutoffty c0 k) (substIndex (weakenTrace X0 k) s x18)) = (substIndex (weakenTrace X0 k) (tshiftTm c0 s) x18))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint tshift_tsubst0_Ty_comm_ind (S2 : Ty) (k : Hvl) (c0 : (Cutoff ty)) (S1 : Ty) {struct S2} :
    ((tshiftTy (weakenCutoffty c0 k) (tsubstTy (weakenTrace X0 k) S1 S2)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTy (weakenCutoffty (CS c0) k) S2))) :=
      match S2 return ((tshiftTy (weakenCutoffty c0 k) (tsubstTy (weakenTrace X0 k) S1 S2)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTy (weakenCutoffty (CS c0) k) S2))) with
        | (tvar X23) => (tshiftTy_tsubstIndex0_comm_ind c0 S1 k X23)
        | (tarr T54 T55) => (f_equal2 tarr (tshift_tsubst0_Ty_comm_ind T54 k c0 S1) (tshift_tsubst0_Ty_comm_ind T55 k c0 S1))
        | (tall T53) => (f_equal tall (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T53 (HS ty k) c0 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (texist T53) => (f_equal texist (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T53 (HS ty k) c0 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tprod T54 T55) => (f_equal2 tprod (tshift_tsubst0_Ty_comm_ind T54 k c0 S1) (tshift_tsubst0_Ty_comm_ind T55 k c0 S1))
      end.
    Fixpoint tshift_tsubst0_Pat_comm_ind (p20 : Pat) (k : Hvl) (c0 : (Cutoff ty)) (S1 : Ty) {struct p20} :
    ((tshiftPat (weakenCutoffty c0 k) (tsubstPat (weakenTrace X0 k) S1 p20)) = (tsubstPat (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftPat (weakenCutoffty (CS c0) k) p20))) :=
      match p20 return ((tshiftPat (weakenCutoffty c0 k) (tsubstPat (weakenTrace X0 k) S1 p20)) = (tsubstPat (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftPat (weakenCutoffty (CS c0) k) p20))) with
        | (pvar T53) => (f_equal pvar (tshift_tsubst0_Ty_comm_ind T53 k c0 S1))
        | (pprod p21 p22) => (f_equal2 pprod (tshift_tsubst0_Pat_comm_ind p21 k c0 S1) (eq_trans (f_equal2 tshiftPat (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p21)))) (f_equal3 tsubstPat (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Pat_comm_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) c0 S1) (f_equal3 tsubstPat (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftPat (eq_sym (weakenCutoffty_append (CS c0) k (appendHvl H0 (bindPat p21)))) eq_refl)))))
      end.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c0 : (Cutoff tm)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutofftm c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c0 s) (shiftTm (weakenCutofftm (CS c0) k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c0 s) (shiftTm (weakenCutofftm (CS c0) k) s0))) with
        | (var x18) => (shiftTm_substIndex0_comm_ind c0 s k x18)
        | (abs T53 t36) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t36 (HS tm k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t37 t38) => (f_equal2 app (shift_subst0_Tm_comm_ind t37 k c0 s) (shift_subst0_Tm_comm_ind t38 k c0 s))
        | (tabs t36) => (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t36 (HS ty k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t36 T53) => (f_equal2 tapp (shift_subst0_Tm_comm_ind t36 k c0 s) eq_refl)
        | (pack T54 t36 T55) => (f_equal3 pack eq_refl (shift_subst0_Tm_comm_ind t36 k c0 s) eq_refl)
        | (unpack t37 t38) => (f_equal2 unpack (shift_subst0_Tm_comm_ind t37 k c0 s) (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t38 (HS tm (HS ty k)) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm (HS ty H0)))) eq_refl eq_refl))))
        | (prod t37 t38) => (f_equal2 prod (shift_subst0_Tm_comm_ind t37 k c0 s) (shift_subst0_Tm_comm_ind t38 k c0 s))
        | (case t37 p20 t38) => (f_equal3 case (shift_subst0_Tm_comm_ind t37 k c0 s) eq_refl (eq_trans (f_equal2 shiftTm (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20))) (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append (CS c0) k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint shift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff tm)) (S1 : Ty) {struct s} :
    ((shiftTm (weakenCutofftm c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) S1 (shiftTm (weakenCutofftm c0 k) s))) :=
      match s return ((shiftTm (weakenCutofftm c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) S1 (shiftTm (weakenCutofftm c0 k) s))) with
        | (var x18) => eq_refl
        | (abs T53 t36) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t36 (HS tm k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t37 t38) => (f_equal2 app (shift_tsubst0_Tm_comm_ind t37 k c0 S1) (shift_tsubst0_Tm_comm_ind t38 k c0 S1))
        | (tabs t36) => (f_equal tabs (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t36 (HS ty k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t36 T53) => (f_equal2 tapp (shift_tsubst0_Tm_comm_ind t36 k c0 S1) eq_refl)
        | (pack T54 t36 T55) => (f_equal3 pack eq_refl (shift_tsubst0_Tm_comm_ind t36 k c0 S1) eq_refl)
        | (unpack t37 t38) => (f_equal2 unpack (shift_tsubst0_Tm_comm_ind t37 k c0 S1) (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t38 (HS tm (HS ty k)) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm (HS ty H0)))) eq_refl eq_refl))))
        | (prod t37 t38) => (f_equal2 prod (shift_tsubst0_Tm_comm_ind t37 k c0 S1) (shift_tsubst0_Tm_comm_ind t38 k c0 S1))
        | (case t37 p20 t38) => (f_equal3 case (shift_tsubst0_Tm_comm_ind t37 k c0 S1) eq_refl (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint tshift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c0 : (Cutoff ty)) (s : Tm) {struct s0} :
    ((tshiftTm (weakenCutoffty c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c0 s) (tshiftTm (weakenCutoffty c0 k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffty c0 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c0 s) (tshiftTm (weakenCutoffty c0 k) s0))) with
        | (var x18) => (tshiftTm_substIndex0_comm_ind c0 s k x18)
        | (abs T53 t36) => (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t36 (HS tm k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t37 t38) => (f_equal2 app (tshift_subst0_Tm_comm_ind t37 k c0 s) (tshift_subst0_Tm_comm_ind t38 k c0 s))
        | (tabs t36) => (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t36 (HS ty k) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t36 T53) => (f_equal2 tapp (tshift_subst0_Tm_comm_ind t36 k c0 s) eq_refl)
        | (pack T54 t36 T55) => (f_equal3 pack eq_refl (tshift_subst0_Tm_comm_ind t36 k c0 s) eq_refl)
        | (unpack t37 t38) => (f_equal2 unpack (tshift_subst0_Tm_comm_ind t37 k c0 s) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t38 (HS tm (HS ty k)) c0 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm (HS ty H0)))) eq_refl eq_refl))))
        | (prod t37 t38) => (f_equal2 prod (tshift_subst0_Tm_comm_ind t37 k c0 s) (tshift_subst0_Tm_comm_ind t38 k c0 s))
        | (case t37 p20 t38) => (f_equal3 case (tshift_subst0_Tm_comm_ind t37 k c0 s) eq_refl (eq_trans (f_equal2 tshiftTm (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20))) (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) c0 s) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
    Fixpoint tshift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c0 : (Cutoff ty)) (S1 : Ty) {struct s} :
    ((tshiftTm (weakenCutoffty c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTm (weakenCutoffty (CS c0) k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c0 k) (tsubstTm (weakenTrace X0 k) S1 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c0 S1) (tshiftTm (weakenCutoffty (CS c0) k) s))) with
        | (var x18) => eq_refl
        | (abs T53 t36) => (f_equal2 abs (tshift_tsubst0_Ty_comm_ind T53 k c0 S1) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t36 (HS tm k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t37 t38) => (f_equal2 app (tshift_tsubst0_Tm_comm_ind t37 k c0 S1) (tshift_tsubst0_Tm_comm_ind t38 k c0 S1))
        | (tabs t36) => (f_equal tabs (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t36 (HS ty k) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t36 T53) => (f_equal2 tapp (tshift_tsubst0_Tm_comm_ind t36 k c0 S1) (tshift_tsubst0_Ty_comm_ind T53 k c0 S1))
        | (pack T54 t36 T55) => (f_equal3 pack (tshift_tsubst0_Ty_comm_ind T54 k c0 S1) (tshift_tsubst0_Tm_comm_ind t36 k c0 S1) (tshift_tsubst0_Ty_comm_ind T55 k c0 S1))
        | (unpack t37 t38) => (f_equal2 unpack (tshift_tsubst0_Tm_comm_ind t37 k c0 S1) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t38 (HS tm (HS ty k)) c0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm (HS ty H0)))) eq_refl eq_refl))))
        | (prod t37 t38) => (f_equal2 prod (tshift_tsubst0_Tm_comm_ind t37 k c0 S1) (tshift_tsubst0_Tm_comm_ind t38 k c0 S1))
        | (case t37 p20 t38) => (f_equal3 case (tshift_tsubst0_Tm_comm_ind t37 k c0 S1) (tshift_tsubst0_Pat_comm_ind p20 k c0 S1) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutoffty_append c0 k (appendHvl H0 (bindPat p20)))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) c0 S1) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append (CS c0) k (appendHvl H0 (bindPat p20)))) eq_refl)))))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTy_tsubstTy0_comm (S2 : Ty) : (forall (c0 : (Cutoff ty)) (S1 : Ty) ,
      ((tshiftTy c0 (tsubstTy X0 S1 S2)) = (tsubstTy X0 (tshiftTy c0 S1) (tshiftTy (CS c0) S2)))) := (tshift_tsubst0_Ty_comm_ind S2 H0).
    Definition tshiftPat_tsubstPat0_comm (p20 : Pat) : (forall (c0 : (Cutoff ty)) (S1 : Ty) ,
      ((tshiftPat c0 (tsubstPat X0 S1 p20)) = (tsubstPat X0 (tshiftTy c0 S1) (tshiftPat (CS c0) p20)))) := (tshift_tsubst0_Pat_comm_ind p20 H0).
    Definition shiftTm_substTm0_comm (s0 : Tm) : (forall (c0 : (Cutoff tm)) (s : Tm) ,
      ((shiftTm c0 (substTm X0 s s0)) = (substTm X0 (shiftTm c0 s) (shiftTm (CS c0) s0)))) := (shift_subst0_Tm_comm_ind s0 H0).
    Definition shiftTm_tsubstTm0_comm (s : Tm) : (forall (c0 : (Cutoff tm)) (S1 : Ty) ,
      ((shiftTm c0 (tsubstTm X0 S1 s)) = (tsubstTm X0 S1 (shiftTm c0 s)))) := (shift_tsubst0_Tm_comm_ind s H0).
    Definition tshiftTm_substTm0_comm (s0 : Tm) : (forall (c0 : (Cutoff ty)) (s : Tm) ,
      ((tshiftTm c0 (substTm X0 s s0)) = (substTm X0 (tshiftTm c0 s) (tshiftTm c0 s0)))) := (tshift_subst0_Tm_comm_ind s0 H0).
    Definition tshiftTm_tsubstTm0_comm (s : Tm) : (forall (c0 : (Cutoff ty)) (S1 : Ty) ,
      ((tshiftTm c0 (tsubstTm X0 S1 s)) = (tsubstTm X0 (tshiftTy c0 S1) (tshiftTm (CS c0) s)))) := (tshift_tsubst0_Tm_comm_ind s H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d0 : (Trace ty)) (S1 : Ty) :
      (forall (k : Hvl) (X23 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d0) k) S1 (tshiftIndex (weakenCutoffty C0 k) X23)) = (tshiftTy (weakenCutoffty C0 k) (tsubstIndex (weakenTrace d0 k) S1 X23)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d0 : (Trace ty)) (S1 : Ty) :
      (forall (k : Hvl) (X23 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d0) k) S1 X23) = (tsubstIndex (weakenTrace d0 k) S1 X23))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d0 : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x18 : (Index tm)) ,
        ((substIndex (weakenTrace (XS ty d0) k) s x18) = (tshiftTm (weakenCutoffty C0 k) (substIndex (weakenTrace d0 k) s x18)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_shiftTm0_comm_ind (d0 : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x18 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d0) k) s (shiftIndex (weakenCutofftm C0 k) x18)) = (shiftTm (weakenCutofftm C0 k) (substIndex (weakenTrace d0 k) s x18)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint tsubst_tshift0_Ty_comm_ind (S2 : Ty) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) {struct S2} :
    ((tsubstTy (weakenTrace (XS ty d0) k) S1 (tshiftTy (weakenCutoffty C0 k) S2)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d0 k) S1 S2))) :=
      match S2 return ((tsubstTy (weakenTrace (XS ty d0) k) S1 (tshiftTy (weakenCutoffty C0 k) S2)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d0 k) S1 S2))) with
        | (tvar X23) => (tsubstIndex_tshiftTy0_comm_ind d0 S1 k X23)
        | (tarr T54 T55) => (f_equal2 tarr (tsubst_tshift0_Ty_comm_ind T54 k d0 S1) (tsubst_tshift0_Ty_comm_ind T55 k d0 S1))
        | (tall T53) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T53 (HS ty k) d0 S1) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (texist T53) => (f_equal texist (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T53 (HS ty k) d0 S1) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tprod T54 T55) => (f_equal2 tprod (tsubst_tshift0_Ty_comm_ind T54 k d0 S1) (tsubst_tshift0_Ty_comm_ind T55 k d0 S1))
      end.
    Fixpoint tsubst_tshift0_Pat_comm_ind (p20 : Pat) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) {struct p20} :
    ((tsubstPat (weakenTrace (XS ty d0) k) S1 (tshiftPat (weakenCutoffty C0 k) p20)) = (tshiftPat (weakenCutoffty C0 k) (tsubstPat (weakenTrace d0 k) S1 p20))) :=
      match p20 return ((tsubstPat (weakenTrace (XS ty d0) k) S1 (tshiftPat (weakenCutoffty C0 k) p20)) = (tshiftPat (weakenCutoffty C0 k) (tsubstPat (weakenTrace d0 k) S1 p20))) with
        | (pvar T53) => (f_equal pvar (tsubst_tshift0_Ty_comm_ind T53 k d0 S1))
        | (pprod p21 p22) => (f_equal2 pprod (tsubst_tshift0_Pat_comm_ind p21 k d0 S1) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty (XS ty d0) k (appendHvl H0 (bindPat p21)))) eq_refl (f_equal2 tshiftPat (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21))) eq_refl)) (eq_trans (tsubst_tshift0_Pat_comm_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) d0 S1) (f_equal2 tshiftPat (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p21)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstPat (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p21)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS tm d0) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d0 k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS tm d0) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d0 k) s s0))) with
        | (var x18) => (substIndex_shiftTm0_comm_ind d0 s k x18)
        | (abs T53 t36) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d0) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t36 (HS tm k) d0 s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t37 t38) => (f_equal2 app (subst_shift0_Tm_comm_ind t37 k d0 s) (subst_shift0_Tm_comm_ind t38 k d0 s))
        | (tabs t36) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t36 (HS ty k) d0 s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t36 T53) => (f_equal2 tapp (subst_shift0_Tm_comm_ind t36 k d0 s) eq_refl)
        | (pack T54 t36 T55) => (f_equal3 pack eq_refl (subst_shift0_Tm_comm_ind t36 k d0 s) eq_refl)
        | (unpack t37 t38) => (f_equal2 unpack (subst_shift0_Tm_comm_ind t37 k d0 s) (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d0) k (HS tm (HS ty H0))) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t38 (HS tm (HS ty k)) d0 s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
        | (prod t37 t38) => (f_equal2 prod (subst_shift0_Tm_comm_ind t37 k d0 s) (subst_shift0_Tm_comm_ind t38 k d0 s))
        | (case t37 p20 t38) => (f_equal3 case (subst_shift0_Tm_comm_ind t37 k d0 s) eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d0) k (appendHvl H0 (bindPat p20))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (subst_shift0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) d0 s) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS ty d0) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d0 k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS ty d0) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d0 k) s s0))) with
        | (var x18) => (substIndex_tshiftTm0_comm_ind d0 s k x18)
        | (abs T53 t36) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d0) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t36 (HS tm k) d0 s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t37 t38) => (f_equal2 app (subst_tshift0_Tm_comm_ind t37 k d0 s) (subst_tshift0_Tm_comm_ind t38 k d0 s))
        | (tabs t36) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t36 (HS ty k) d0 s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t36 T53) => (f_equal2 tapp (subst_tshift0_Tm_comm_ind t36 k d0 s) eq_refl)
        | (pack T54 t36 T55) => (f_equal3 pack eq_refl (subst_tshift0_Tm_comm_ind t36 k d0 s) eq_refl)
        | (unpack t37 t38) => (f_equal2 unpack (subst_tshift0_Tm_comm_ind t37 k d0 s) (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d0) k (HS tm (HS ty H0))) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t38 (HS tm (HS ty k)) d0 s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
        | (prod t37 t38) => (f_equal2 prod (subst_tshift0_Tm_comm_ind t37 k d0 s) (subst_tshift0_Tm_comm_ind t38 k d0 s))
        | (case t37 p20 t38) => (f_equal3 case (subst_tshift0_Tm_comm_ind t37 k d0 s) eq_refl (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append tm (XS ty d0) k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (subst_tshift0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) d0 s) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d0 k) S1 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) :=
      match s return ((tsubstTm (weakenTrace d0 k) S1 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) with
        | (var x18) => eq_refl
        | (abs T53 t36) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t36 (HS tm k) d0 S1) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t37 t38) => (f_equal2 app (tsubst_shift0_Tm_comm_ind t37 k d0 S1) (tsubst_shift0_Tm_comm_ind t38 k d0 S1))
        | (tabs t36) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t36 (HS ty k) d0 S1) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t36 T53) => (f_equal2 tapp (tsubst_shift0_Tm_comm_ind t36 k d0 S1) eq_refl)
        | (pack T54 t36 T55) => (f_equal3 pack eq_refl (tsubst_shift0_Tm_comm_ind t36 k d0 S1) eq_refl)
        | (unpack t37 t38) => (f_equal2 unpack (tsubst_shift0_Tm_comm_ind t37 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS tm (HS ty H0))) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t38 (HS tm (HS ty k)) d0 S1) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
        | (prod t37 t38) => (f_equal2 prod (tsubst_shift0_Tm_comm_ind t37 k d0 S1) (tsubst_shift0_Tm_comm_ind t38 k d0 S1))
        | (case t37 p20 t38) => (f_equal3 case (tsubst_shift0_Tm_comm_ind t37 k d0 S1) eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (tsubst_shift0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S1) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS ty d0) k) S1 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) :=
      match s return ((tsubstTm (weakenTrace (XS ty d0) k) S1 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d0 k) S1 s))) with
        | (var x18) => eq_refl
        | (abs T53 t36) => (f_equal2 abs (tsubst_tshift0_Ty_comm_ind T53 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d0) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t36 (HS tm k) d0 S1) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t37 t38) => (f_equal2 app (tsubst_tshift0_Tm_comm_ind t37 k d0 S1) (tsubst_tshift0_Tm_comm_ind t38 k d0 S1))
        | (tabs t36) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t36 (HS ty k) d0 S1) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t36 T53) => (f_equal2 tapp (tsubst_tshift0_Tm_comm_ind t36 k d0 S1) (tsubst_tshift0_Ty_comm_ind T53 k d0 S1))
        | (pack T54 t36 T55) => (f_equal3 pack (tsubst_tshift0_Ty_comm_ind T54 k d0 S1) (tsubst_tshift0_Tm_comm_ind t36 k d0 S1) (tsubst_tshift0_Ty_comm_ind T55 k d0 S1))
        | (unpack t37 t38) => (f_equal2 unpack (tsubst_tshift0_Tm_comm_ind t37 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d0) k (HS tm (HS ty H0))) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t38 (HS tm (HS ty k)) d0 S1) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
        | (prod t37 t38) => (f_equal2 prod (tsubst_tshift0_Tm_comm_ind t37 k d0 S1) (tsubst_tshift0_Tm_comm_ind t38 k d0 S1))
        | (case t37 p20 t38) => (f_equal3 case (tsubst_tshift0_Tm_comm_ind t37 k d0 S1) (tsubst_tshift0_Pat_comm_ind p20 k d0 S1) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty (XS ty d0) k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20))) eq_refl)) (eq_trans (tsubst_tshift0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S1) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S2 : Ty) : (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTy (XS ty d0) S1 (tshiftTy C0 S2)) = (tshiftTy C0 (tsubstTy d0 S1 S2)))) := (tsubst_tshift0_Ty_comm_ind S2 H0).
    Definition tsubstPat_tshiftPat0_comm (p20 : Pat) : (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((tsubstPat (XS ty d0) S1 (tshiftPat C0 p20)) = (tshiftPat C0 (tsubstPat d0 S1 p20)))) := (tsubst_tshift0_Pat_comm_ind p20 H0).
    Definition substTm_shiftTm0_comm (s0 : Tm) : (forall (d0 : (Trace tm)) (s : Tm) ,
      ((substTm (XS tm d0) s (shiftTm C0 s0)) = (shiftTm C0 (substTm d0 s s0)))) := (subst_shift0_Tm_comm_ind s0 H0).
    Definition substTm_tshiftTm0_comm (s0 : Tm) : (forall (d0 : (Trace tm)) (s : Tm) ,
      ((substTm (XS ty d0) s (tshiftTm C0 s0)) = (tshiftTm C0 (substTm d0 s s0)))) := (subst_tshift0_Tm_comm_ind s0 H0).
    Definition tsubstTm_shiftTm0_comm (s : Tm) : (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTm d0 S1 (shiftTm C0 s)) = (shiftTm C0 (tsubstTm d0 S1 s)))) := (tsubst_shift0_Tm_comm_ind s H0).
    Definition tsubstTm_tshiftTm0_comm (s : Tm) : (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTm (XS ty d0) S1 (tshiftTm C0 s)) = (tshiftTm C0 (tsubstTm d0 S1 s)))) := (tsubst_tshift0_Tm_comm_ind s H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Fixpoint tsubst_tm_Ty_ind (S2 : Ty) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) {struct S2} :
    ((tsubstTy (weakenTrace (XS tm d0) k) S1 S2) = (tsubstTy (weakenTrace d0 k) S1 S2)) :=
      match S2 return ((tsubstTy (weakenTrace (XS tm d0) k) S1 S2) = (tsubstTy (weakenTrace d0 k) S1 S2)) with
        | (tvar X23) => (tsubstIndex_shiftTy0_comm_ind d0 S1 k X23)
        | (tarr T54 T55) => (f_equal2 tarr (tsubst_tm_Ty_ind T54 k d0 S1) (tsubst_tm_Ty_ind T55 k d0 S1))
        | (tall T53) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T53 (HS ty k) d0 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl))))
        | (texist T53) => (f_equal texist (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T53 (HS ty k) d0 S1) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl))))
        | (tprod T54 T55) => (f_equal2 tprod (tsubst_tm_Ty_ind T54 k d0 S1) (tsubst_tm_Ty_ind T55 k d0 S1))
      end.
    Fixpoint tsubst_tm_Pat_ind (p20 : Pat) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) {struct p20} :
    ((tsubstPat (weakenTrace (XS tm d0) k) S1 p20) = (tsubstPat (weakenTrace d0 k) S1 p20)) :=
      match p20 return ((tsubstPat (weakenTrace (XS tm d0) k) S1 p20) = (tsubstPat (weakenTrace d0 k) S1 p20)) with
        | (pvar T53) => (f_equal pvar (tsubst_tm_Ty_ind T53 k d0 S1))
        | (pprod p21 p22) => (f_equal2 pprod (tsubst_tm_Pat_ind p21 k d0 S1) (eq_trans (f_equal3 tsubstPat (weakenTrace_append ty (XS tm d0) k (appendHvl H0 (bindPat p21))) eq_refl eq_refl) (eq_trans (tsubst_tm_Pat_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) d0 S1) (f_equal3 tsubstPat (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p21)))) eq_refl eq_refl))))
      end.
    Fixpoint tsubst_tm_Tm_ind (s : Tm) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS tm d0) k) S1 s) = (tsubstTm (weakenTrace d0 k) S1 s)) :=
      match s return ((tsubstTm (weakenTrace (XS tm d0) k) S1 s) = (tsubstTm (weakenTrace d0 k) S1 s)) with
        | (var x18) => eq_refl
        | (abs T53 t36) => (f_equal2 abs (tsubst_tm_Ty_ind T53 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d0) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t36 (HS tm k) d0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t37 t38) => (f_equal2 app (tsubst_tm_Tm_ind t37 k d0 S1) (tsubst_tm_Tm_ind t38 k d0 S1))
        | (tabs t36) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d0) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t36 (HS ty k) d0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t36 T53) => (f_equal2 tapp (tsubst_tm_Tm_ind t36 k d0 S1) (tsubst_tm_Ty_ind T53 k d0 S1))
        | (pack T54 t36 T55) => (f_equal3 pack (tsubst_tm_Ty_ind T54 k d0 S1) (tsubst_tm_Tm_ind t36 k d0 S1) (tsubst_tm_Ty_ind T55 k d0 S1))
        | (unpack t37 t38) => (f_equal2 unpack (tsubst_tm_Tm_ind t37 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d0) k (HS tm (HS ty H0))) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t38 (HS tm (HS ty k)) d0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm (HS ty H0)))) eq_refl eq_refl))))
        | (prod t37 t38) => (f_equal2 prod (tsubst_tm_Tm_ind t37 k d0 S1) (tsubst_tm_Tm_ind t38 k d0 S1))
        | (case t37 p20 t38) => (f_equal3 case (tsubst_tm_Tm_ind t37 k d0 S1) (tsubst_tm_Pat_ind p20 k d0 S1) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d0) k (appendHvl H0 (bindPat p20))) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl))))
      end.
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S2 : Ty) : (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTy (XS tm d0) S1 S2) = (tsubstTy d0 S1 S2))) := (tsubst_tm_Ty_ind S2 H0).
    Definition tsubstPat_tm (p20 : Pat) : (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((tsubstPat (XS tm d0) S1 p20) = (tsubstPat d0 S1 p20))) := (tsubst_tm_Pat_ind p20 H0).
    Definition tsubstTm_tm (s : Tm) : (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((tsubstTm (XS tm d0) S1 s) = (tsubstTm d0 S1 s))) := (tsubst_tm_Tm_ind s H0).
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite tsubstPat0_tshiftPat0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : interaction.
 Hint Rewrite tsubstPat0_tshiftPat0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : reflection.
 Hint Rewrite tsubstPat_tshiftPat0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : interaction.
 Hint Rewrite tsubstPat_tshiftPat0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : subst_shift0.
 Hint Rewrite tsubstPat_tm tsubstTm_tm tsubstTy_tm : interaction.
 Hint Rewrite tsubstPat_tm tsubstTm_tm tsubstTy_tm : subst_shift0.
 Hint Rewrite tshiftPat_tsubstPat0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : interaction.
 Hint Rewrite tshiftPat_tsubstPat0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d0 : (Trace tm)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (x18 : (Index tm)) ,
        ((substTm (weakenTrace d0 k) s (substIndex (weakenTrace X0 k) s0 x18)) = (substTm (weakenTrace X0 k) (substTm d0 s s0) (substIndex (weakenTrace (XS tm d0) k) s x18)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d0 : (Trace ty)) (S1 : Ty) (s : Tm) :
      (forall (k : Hvl) (x18 : (Index tm)) ,
        ((tsubstTm (weakenTrace d0 k) S1 (substIndex (weakenTrace X0 k) s x18)) = (substIndex (weakenTrace X0 k) (tsubstTm d0 S1 s) x18))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) :
      (forall (k : Hvl) (X23 : (Index ty)) ,
        ((tsubstTy (weakenTrace d0 k) S1 (tsubstIndex (weakenTrace X0 k) S2 X23)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstIndex (weakenTrace (XS ty d0) k) S1 X23)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d0 : (Trace tm)) (s : Tm) (S1 : Ty) :
      (forall (k : Hvl) (x18 : (Index tm)) ,
        ((substIndex (weakenTrace d0 k) s x18) = (tsubstTm (weakenTrace X0 k) S1 (substIndex (weakenTrace (XS ty d0) k) s x18)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint tsubst_tsubst0_Ty_comm_ind (S3 : Ty) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) {struct S3} :
    ((tsubstTy (weakenTrace d0 k) S1 (tsubstTy (weakenTrace X0 k) S2 S3)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstTy (weakenTrace (XS ty d0) k) S1 S3))) :=
      match S3 return ((tsubstTy (weakenTrace d0 k) S1 (tsubstTy (weakenTrace X0 k) S2 S3)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstTy (weakenTrace (XS ty d0) k) S1 S3))) with
        | (tvar X23) => (tsubstTy_tsubstIndex0_commright_ind d0 S1 S2 k X23)
        | (tarr T54 T55) => (f_equal2 tarr (tsubst_tsubst0_Ty_comm_ind T54 k d0 S1 S2) (tsubst_tsubst0_Ty_comm_ind T55 k d0 S1 S2))
        | (tall T53) => (f_equal tall (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d0 k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T53 (HS ty k) d0 S1 S2) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d0) k (HS ty H0))) eq_refl eq_refl)))))
        | (texist T53) => (f_equal texist (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d0 k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T53 (HS ty k) d0 S1 S2) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d0) k (HS ty H0))) eq_refl eq_refl)))))
        | (tprod T54 T55) => (f_equal2 tprod (tsubst_tsubst0_Ty_comm_ind T54 k d0 S1 S2) (tsubst_tsubst0_Ty_comm_ind T55 k d0 S1 S2))
      end.
    Fixpoint tsubst_tsubst0_Pat_comm_ind (p20 : Pat) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) {struct p20} :
    ((tsubstPat (weakenTrace d0 k) S1 (tsubstPat (weakenTrace X0 k) S2 p20)) = (tsubstPat (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstPat (weakenTrace (XS ty d0) k) S1 p20))) :=
      match p20 return ((tsubstPat (weakenTrace d0 k) S1 (tsubstPat (weakenTrace X0 k) S2 p20)) = (tsubstPat (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstPat (weakenTrace (XS ty d0) k) S1 p20))) with
        | (pvar T53) => (f_equal pvar (tsubst_tsubst0_Ty_comm_ind T53 k d0 S1 S2))
        | (pprod p21 p22) => (f_equal2 pprod (tsubst_tsubst0_Pat_comm_ind p21 k d0 S1 S2) (eq_trans (f_equal3 tsubstPat (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p21)))) eq_refl (f_equal3 tsubstPat (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Pat_comm_ind p22 (appendHvl k (appendHvl H0 (bindPat p21))) d0 S1 S2) (f_equal3 tsubstPat (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p21)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstPat (eq_sym (weakenTrace_append ty (XS ty d0) k (appendHvl H0 (bindPat p21)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d0 : (Trace tm)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d0 k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d0 s s0) (substTm (weakenTrace (XS tm d0) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d0 k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d0 s s0) (substTm (weakenTrace (XS tm d0) k) s s1))) with
        | (var x18) => (substTm_substIndex0_commright_ind d0 s s0 k x18)
        | (abs T53 t36) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t36 (HS tm k) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d0) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t37 t38) => (f_equal2 app (subst_subst0_Tm_comm_ind t37 k d0 s s0) (subst_subst0_Tm_comm_ind t38 k d0 s s0))
        | (tabs t36) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t36 (HS ty k) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d0) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t36 T53) => (f_equal2 tapp (subst_subst0_Tm_comm_ind t36 k d0 s s0) eq_refl)
        | (pack T54 t36 T55) => (f_equal3 pack eq_refl (subst_subst0_Tm_comm_ind t36 k d0 s s0) eq_refl)
        | (unpack t37 t38) => (f_equal2 unpack (subst_subst0_Tm_comm_ind t37 k d0 s s0) (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (HS tm (HS ty H0))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t38 (HS tm (HS ty k)) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm (HS ty H0)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d0) k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
        | (prod t37 t38) => (f_equal2 prod (subst_subst0_Tm_comm_ind t37 k d0 s s0) (subst_subst0_Tm_comm_ind t38 k d0 s s0))
        | (case t37 p20 t38) => (f_equal3 case (subst_subst0_Tm_comm_ind t37 k d0 s s0) eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (appendHvl H0 (bindPat p20))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) d0 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d0) k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace tm)) (s : Tm) (S1 : Ty) {struct s0} :
    ((substTm (weakenTrace d0 k) s (tsubstTm (weakenTrace X0 k) S1 s0)) = (tsubstTm (weakenTrace X0 k) S1 (substTm (weakenTrace (XS ty d0) k) s s0))) :=
      match s0 return ((substTm (weakenTrace d0 k) s (tsubstTm (weakenTrace X0 k) S1 s0)) = (tsubstTm (weakenTrace X0 k) S1 (substTm (weakenTrace (XS ty d0) k) s s0))) with
        | (var x18) => (substTy_tsubstIndex0_commleft_ind d0 s S1 k x18)
        | (abs T53 t36) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t36 (HS tm k) d0 s S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d0) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t37 t38) => (f_equal2 app (subst_tsubst0_Tm_comm_ind t37 k d0 s S1) (subst_tsubst0_Tm_comm_ind t38 k d0 s S1))
        | (tabs t36) => (f_equal tabs (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t36 (HS ty k) d0 s S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d0) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t36 T53) => (f_equal2 tapp (subst_tsubst0_Tm_comm_ind t36 k d0 s S1) eq_refl)
        | (pack T54 t36 T55) => (f_equal3 pack eq_refl (subst_tsubst0_Tm_comm_ind t36 k d0 s S1) eq_refl)
        | (unpack t37 t38) => (f_equal2 unpack (subst_tsubst0_Tm_comm_ind t37 k d0 s S1) (eq_trans (f_equal3 substTm (weakenTrace_append tm d0 k (HS tm (HS ty H0))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t38 (HS tm (HS ty k)) d0 s S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm (HS ty H0)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d0) k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
        | (prod t37 t38) => (f_equal2 prod (subst_tsubst0_Tm_comm_ind t37 k d0 s S1) (subst_tsubst0_Tm_comm_ind t38 k d0 s S1))
        | (case t37 p20 t38) => (f_equal3 case (subst_tsubst0_Tm_comm_ind t37 k d0 s S1) eq_refl (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append tm d0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) d0 s S1) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d0) k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) (s : Tm) {struct s0} :
    ((tsubstTm (weakenTrace d0 k) S1 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d0 S1 s) (tsubstTm (weakenTrace d0 k) S1 s0))) :=
      match s0 return ((tsubstTm (weakenTrace d0 k) S1 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d0 S1 s) (tsubstTm (weakenTrace d0 k) S1 s0))) with
        | (var x18) => (tsubstTm_substIndex0_commright_ind d0 S1 s k x18)
        | (abs T53 t36) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t36 (HS tm k) d0 S1 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t37 t38) => (f_equal2 app (tsubst_subst0_Tm_comm_ind t37 k d0 S1 s) (tsubst_subst0_Tm_comm_ind t38 k d0 S1 s))
        | (tabs t36) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t36 (HS ty k) d0 S1 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t36 T53) => (f_equal2 tapp (tsubst_subst0_Tm_comm_ind t36 k d0 S1 s) eq_refl)
        | (pack T54 t36 T55) => (f_equal3 pack eq_refl (tsubst_subst0_Tm_comm_ind t36 k d0 S1 s) eq_refl)
        | (unpack t37 t38) => (f_equal2 unpack (tsubst_subst0_Tm_comm_ind t37 k d0 S1 s) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS tm (HS ty H0))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t38 (HS tm (HS ty k)) d0 S1 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm (HS ty H0)))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
        | (prod t37 t38) => (f_equal2 prod (tsubst_subst0_Tm_comm_ind t37 k d0 S1 s) (tsubst_subst0_Tm_comm_ind t38 k d0 S1 s))
        | (case t37 p20 t38) => (f_equal3 case (tsubst_subst0_Tm_comm_ind t37 k d0 S1 s) eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S1 s) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
    Fixpoint tsubst_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d0 k) S1 (tsubstTm (weakenTrace X0 k) S2 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstTm (weakenTrace (XS ty d0) k) S1 s))) :=
      match s return ((tsubstTm (weakenTrace d0 k) S1 (tsubstTm (weakenTrace X0 k) S2 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d0 S1 S2) (tsubstTm (weakenTrace (XS ty d0) k) S1 s))) with
        | (var x18) => eq_refl
        | (abs T53 t36) => (f_equal2 abs (tsubst_tsubst0_Ty_comm_ind T53 k d0 S1 S2) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t36 (HS tm k) d0 S1 S2) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d0) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t37 t38) => (f_equal2 app (tsubst_tsubst0_Tm_comm_ind t37 k d0 S1 S2) (tsubst_tsubst0_Tm_comm_ind t38 k d0 S1 S2))
        | (tabs t36) => (f_equal tabs (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t36 (HS ty k) d0 S1 S2) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d0) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t36 T53) => (f_equal2 tapp (tsubst_tsubst0_Tm_comm_ind t36 k d0 S1 S2) (tsubst_tsubst0_Ty_comm_ind T53 k d0 S1 S2))
        | (pack T54 t36 T55) => (f_equal3 pack (tsubst_tsubst0_Ty_comm_ind T54 k d0 S1 S2) (tsubst_tsubst0_Tm_comm_ind t36 k d0 S1 S2) (tsubst_tsubst0_Ty_comm_ind T55 k d0 S1 S2))
        | (unpack t37 t38) => (f_equal2 unpack (tsubst_tsubst0_Tm_comm_ind t37 k d0 S1 S2) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d0 k (HS tm (HS ty H0))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm (HS ty H0))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t38 (HS tm (HS ty k)) d0 S1 S2) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm (HS ty H0)))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d0) k (HS tm (HS ty H0)))) eq_refl eq_refl)))))
        | (prod t37 t38) => (f_equal2 prod (tsubst_tsubst0_Tm_comm_ind t37 k d0 S1 S2) (tsubst_tsubst0_Tm_comm_ind t38 k d0 S1 S2))
        | (case t37 p20 t38) => (f_equal3 case (tsubst_tsubst0_Tm_comm_ind t37 k d0 S1 S2) (tsubst_tsubst0_Pat_comm_ind p20 k d0 S1 S2) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append ty d0 k (appendHvl H0 (bindPat p20)))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t38 (appendHvl k (appendHvl H0 (bindPat p20))) d0 S1 S2) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p20)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d0) k (appendHvl H0 (bindPat p20)))) eq_refl eq_refl)))))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S3 : Ty) : (forall (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) ,
      ((tsubstTy d0 S1 (tsubstTy X0 S2 S3)) = (tsubstTy X0 (tsubstTy d0 S1 S2) (tsubstTy (XS ty d0) S1 S3)))) := (tsubst_tsubst0_Ty_comm_ind S3 H0).
    Definition tsubstPat_tsubstPat0_comm (p20 : Pat) : (forall (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) ,
      ((tsubstPat d0 S1 (tsubstPat X0 S2 p20)) = (tsubstPat X0 (tsubstTy d0 S1 S2) (tsubstPat (XS ty d0) S1 p20)))) := (tsubst_tsubst0_Pat_comm_ind p20 H0).
    Definition substTm_substTm0_comm (s1 : Tm) : (forall (d0 : (Trace tm)) (s : Tm) (s0 : Tm) ,
      ((substTm d0 s (substTm X0 s0 s1)) = (substTm X0 (substTm d0 s s0) (substTm (XS tm d0) s s1)))) := (subst_subst0_Tm_comm_ind s1 H0).
    Definition substTm_tsubstTm0_comm (s0 : Tm) : (forall (d0 : (Trace tm)) (s : Tm) (S1 : Ty) ,
      ((substTm d0 s (tsubstTm X0 S1 s0)) = (tsubstTm X0 S1 (substTm (XS ty d0) s s0)))) := (subst_tsubst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_substTm0_comm (s0 : Tm) : (forall (d0 : (Trace ty)) (S1 : Ty) (s : Tm) ,
      ((tsubstTm d0 S1 (substTm X0 s s0)) = (substTm X0 (tsubstTm d0 S1 s) (tsubstTm d0 S1 s0)))) := (tsubst_subst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_tsubstTm0_comm (s : Tm) : (forall (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) ,
      ((tsubstTm d0 S1 (tsubstTm X0 S2 s)) = (tsubstTm X0 (tsubstTy d0 S1 S2) (tsubstTm (XS ty d0) S1 s)))) := (tsubst_tsubst0_Tm_comm_ind s H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) (S2 : Ty) ,
        ((weakenTy (tsubstTy d0 S1 S2) k) = (tsubstTy (weakenTrace d0 k) S1 (weakenTy S2 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenPat_tsubstPat  :
      (forall (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) (p20 : Pat) ,
        ((weakenPat (tsubstPat d0 S1 p20) k) = (tsubstPat (weakenTrace d0 k) S1 (weakenPat p20 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k : Hvl) (d0 : (Trace tm)) (s : Tm) (s0 : Tm) ,
        ((weakenTm (substTm d0 s s0) k) = (substTm (weakenTrace d0 k) s (weakenTm s0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k : Hvl) (d0 : (Trace ty)) (S1 : Ty) (s : Tm) ,
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
    | wfTy_tvar (X23 : (Index ty))
        (wfi : (wfindex k X23)) :
        (wfTy k (tvar X23))
    | wfTy_tarr {T53 : Ty}
        (wf : (wfTy k T53)) {T54 : Ty}
        (wf0 : (wfTy k T54)) :
        (wfTy k (tarr T53 T54))
    | wfTy_tall {T55 : Ty}
        (wf : (wfTy (HS ty k) T55)) :
        (wfTy k (tall T55))
    | wfTy_texist {T56 : Ty}
        (wf : (wfTy (HS ty k) T56)) :
        (wfTy k (texist T56))
    | wfTy_tprod {T57 : Ty}
        (wf : (wfTy k T57)) {T58 : Ty}
        (wf0 : (wfTy k T58)) :
        (wfTy k (tprod T57 T58)).
  Inductive wfPat (k : Hvl) : Pat -> Prop :=
    | wfPat_pvar {T53 : Ty}
        (wf : (wfTy k T53)) :
        (wfPat k (pvar T53))
    | wfPat_pprod {p20 : Pat}
        (wf : (wfPat k p20)) {p21 : Pat}
        (wf0 : (wfPat (appendHvl k (appendHvl H0 (bindPat p20))) p21))
        : (wfPat k (pprod p20 p21)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var (x18 : (Index tm))
        (wfi : (wfindex k x18)) :
        (wfTm k (var x18))
    | wfTm_abs {T53 : Ty}
        (wf : (wfTy k T53)) {t36 : Tm}
        (wf0 : (wfTm (HS tm k) t36)) :
        (wfTm k (abs T53 t36))
    | wfTm_app {t37 : Tm}
        (wf : (wfTm k t37)) {t38 : Tm}
        (wf0 : (wfTm k t38)) :
        (wfTm k (app t37 t38))
    | wfTm_tabs {t39 : Tm}
        (wf : (wfTm (HS ty k) t39)) :
        (wfTm k (tabs t39))
    | wfTm_tapp {t40 : Tm}
        (wf : (wfTm k t40)) {T54 : Ty}
        (wf0 : (wfTy k T54)) :
        (wfTm k (tapp t40 T54))
    | wfTm_pack {T55 : Ty}
        (wf : (wfTy k T55)) {t41 : Tm}
        (wf0 : (wfTm k t41)) {T56 : Ty}
        (wf1 : (wfTy k T56)) :
        (wfTm k (pack T55 t41 T56))
    | wfTm_unpack {t42 : Tm}
        (wf : (wfTm k t42)) {t43 : Tm}
        (wf0 : (wfTm (HS tm (HS ty k)) t43))
        : (wfTm k (unpack t42 t43))
    | wfTm_prod {t44 : Tm}
        (wf : (wfTm k t44)) {t45 : Tm}
        (wf0 : (wfTm k t45)) :
        (wfTm k (prod t44 t45))
    | wfTm_case {t46 : Tm}
        (wf : (wfTm k t46)) {p20 : Pat}
        (wf0 : (wfPat k p20)) {t47 : Tm}
        (wf1 : (wfTm (appendHvl k (appendHvl H0 (bindPat p20))) t47))
        : (wfTm k (case t46 p20 t47)).
  Definition inversion_wfTy_tvar_1 (k : Hvl) (X : (Index ty)) (H30 : (wfTy k (tvar X))) : (wfindex k X) := match H30 in (wfTy _ S1) return match S1 return Prop with
    | (tvar X) => (wfindex k X)
    | _ => True
  end with
    | (wfTy_tvar X H1) => H1
    | _ => I
  end.
  Definition inversion_wfTy_tarr_0 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H31 : (wfTy k0 (tarr T1 T2))) : (wfTy k0 T1) := match H31 in (wfTy _ S2) return match S2 return Prop with
    | (tarr T1 T2) => (wfTy k0 T1)
    | _ => True
  end with
    | (wfTy_tarr T1 H2 T2 H3) => H2
    | _ => I
  end.
  Definition inversion_wfTy_tarr_1 (k0 : Hvl) (T1 : Ty) (T2 : Ty) (H31 : (wfTy k0 (tarr T1 T2))) : (wfTy k0 T2) := match H31 in (wfTy _ S2) return match S2 return Prop with
    | (tarr T1 T2) => (wfTy k0 T2)
    | _ => True
  end with
    | (wfTy_tarr T1 H2 T2 H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_tall_1 (k1 : Hvl) (T : Ty) (H32 : (wfTy k1 (tall T))) : (wfTy (HS ty k1) T) := match H32 in (wfTy _ S3) return match S3 return Prop with
    | (tall T) => (wfTy (HS ty k1) T)
    | _ => True
  end with
    | (wfTy_tall T H4) => H4
    | _ => I
  end.
  Definition inversion_wfTy_texist_1 (k2 : Hvl) (T : Ty) (H33 : (wfTy k2 (texist T))) : (wfTy (HS ty k2) T) := match H33 in (wfTy _ S4) return match S4 return Prop with
    | (texist T) => (wfTy (HS ty k2) T)
    | _ => True
  end with
    | (wfTy_texist T H5) => H5
    | _ => I
  end.
  Definition inversion_wfTy_tprod_0 (k3 : Hvl) (T1 : Ty) (T2 : Ty) (H34 : (wfTy k3 (tprod T1 T2))) : (wfTy k3 T1) := match H34 in (wfTy _ S5) return match S5 return Prop with
    | (tprod T1 T2) => (wfTy k3 T1)
    | _ => True
  end with
    | (wfTy_tprod T1 H6 T2 H7) => H6
    | _ => I
  end.
  Definition inversion_wfTy_tprod_1 (k3 : Hvl) (T1 : Ty) (T2 : Ty) (H34 : (wfTy k3 (tprod T1 T2))) : (wfTy k3 T2) := match H34 in (wfTy _ S5) return match S5 return Prop with
    | (tprod T1 T2) => (wfTy k3 T2)
    | _ => True
  end with
    | (wfTy_tprod T1 H6 T2 H7) => H7
    | _ => I
  end.
  Definition inversion_wfPat_pvar_1 (k4 : Hvl) (T : Ty) (H35 : (wfPat k4 (pvar T))) : (wfTy k4 T) := match H35 in (wfPat _ p20) return match p20 return Prop with
    | (pvar T) => (wfTy k4 T)
    | _ => True
  end with
    | (wfPat_pvar T H8) => H8
    | _ => I
  end.
  Definition inversion_wfPat_pprod_0 (k5 : Hvl) (p1 : Pat) (p2 : Pat) (H36 : (wfPat k5 (pprod p1 p2))) : (wfPat k5 p1) := match H36 in (wfPat _ p21) return match p21 return Prop with
    | (pprod p1 p2) => (wfPat k5 p1)
    | _ => True
  end with
    | (wfPat_pprod p1 H9 p2 H10) => H9
    | _ => I
  end.
  Definition inversion_wfPat_pprod_1 (k5 : Hvl) (p1 : Pat) (p2 : Pat) (H36 : (wfPat k5 (pprod p1 p2))) : (wfPat (appendHvl k5 (appendHvl H0 (bindPat p1))) p2) := match H36 in (wfPat _ p21) return match p21 return Prop with
    | (pprod p1 p2) => (wfPat (appendHvl k5 (appendHvl H0 (bindPat p1))) p2)
    | _ => True
  end with
    | (wfPat_pprod p1 H9 p2 H10) => H10
    | _ => I
  end.
  Definition inversion_wfTm_var_1 (k6 : Hvl) (x : (Index tm)) (H37 : (wfTm k6 (var x))) : (wfindex k6 x) := match H37 in (wfTm _ s) return match s return Prop with
    | (var x) => (wfindex k6 x)
    | _ => True
  end with
    | (wfTm_var x H11) => H11
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k7 : Hvl) (T : Ty) (t : Tm) (H38 : (wfTm k7 (abs T t))) : (wfTy k7 T) := match H38 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTy k7 T)
    | _ => True
  end with
    | (wfTm_abs T H12 t H13) => H12
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k7 : Hvl) (T : Ty) (t : Tm) (H38 : (wfTm k7 (abs T t))) : (wfTm (HS tm k7) t) := match H38 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTm (HS tm k7) t)
    | _ => True
  end with
    | (wfTm_abs T H12 t H13) => H13
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H39 : (wfTm k8 (app t1 t2))) : (wfTm k8 t1) := match H39 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k8 t1)
    | _ => True
  end with
    | (wfTm_app t1 H14 t2 H15) => H14
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H39 : (wfTm k8 (app t1 t2))) : (wfTm k8 t2) := match H39 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k8 t2)
    | _ => True
  end with
    | (wfTm_app t1 H14 t2 H15) => H15
    | _ => I
  end.
  Definition inversion_wfTm_tabs_1 (k9 : Hvl) (t : Tm) (H40 : (wfTm k9 (tabs t))) : (wfTm (HS ty k9) t) := match H40 in (wfTm _ s2) return match s2 return Prop with
    | (tabs t) => (wfTm (HS ty k9) t)
    | _ => True
  end with
    | (wfTm_tabs t H16) => H16
    | _ => I
  end.
  Definition inversion_wfTm_tapp_0 (k10 : Hvl) (t : Tm) (T : Ty) (H41 : (wfTm k10 (tapp t T))) : (wfTm k10 t) := match H41 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTm k10 t)
    | _ => True
  end with
    | (wfTm_tapp t H17 T H18) => H17
    | _ => I
  end.
  Definition inversion_wfTm_tapp_1 (k10 : Hvl) (t : Tm) (T : Ty) (H41 : (wfTm k10 (tapp t T))) : (wfTy k10 T) := match H41 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTy k10 T)
    | _ => True
  end with
    | (wfTm_tapp t H17 T H18) => H18
    | _ => I
  end.
  Definition inversion_wfTm_pack_0 (k11 : Hvl) (T1 : Ty) (t : Tm) (T2 : Ty) (H42 : (wfTm k11 (pack T1 t T2))) : (wfTy k11 T1) := match H42 in (wfTm _ s4) return match s4 return Prop with
    | (pack T1 t T2) => (wfTy k11 T1)
    | _ => True
  end with
    | (wfTm_pack T1 H19 t H20 T2 H21) => H19
    | _ => I
  end.
  Definition inversion_wfTm_pack_1 (k11 : Hvl) (T1 : Ty) (t : Tm) (T2 : Ty) (H42 : (wfTm k11 (pack T1 t T2))) : (wfTm k11 t) := match H42 in (wfTm _ s4) return match s4 return Prop with
    | (pack T1 t T2) => (wfTm k11 t)
    | _ => True
  end with
    | (wfTm_pack T1 H19 t H20 T2 H21) => H20
    | _ => I
  end.
  Definition inversion_wfTm_pack_2 (k11 : Hvl) (T1 : Ty) (t : Tm) (T2 : Ty) (H42 : (wfTm k11 (pack T1 t T2))) : (wfTy k11 T2) := match H42 in (wfTm _ s4) return match s4 return Prop with
    | (pack T1 t T2) => (wfTy k11 T2)
    | _ => True
  end with
    | (wfTm_pack T1 H19 t H20 T2 H21) => H21
    | _ => I
  end.
  Definition inversion_wfTm_unpack_0 (k12 : Hvl) (t1 : Tm) (t2 : Tm) (H43 : (wfTm k12 (unpack t1 t2))) : (wfTm k12 t1) := match H43 in (wfTm _ s5) return match s5 return Prop with
    | (unpack t1 t2) => (wfTm k12 t1)
    | _ => True
  end with
    | (wfTm_unpack t1 H22 t2 H23) => H22
    | _ => I
  end.
  Definition inversion_wfTm_unpack_3 (k12 : Hvl) (t1 : Tm) (t2 : Tm) (H43 : (wfTm k12 (unpack t1 t2))) : (wfTm (HS tm (HS ty k12)) t2) := match H43 in (wfTm _ s5) return match s5 return Prop with
    | (unpack t1 t2) => (wfTm (HS tm (HS ty k12)) t2)
    | _ => True
  end with
    | (wfTm_unpack t1 H22 t2 H23) => H23
    | _ => I
  end.
  Definition inversion_wfTm_prod_0 (k13 : Hvl) (t1 : Tm) (t2 : Tm) (H44 : (wfTm k13 (prod t1 t2))) : (wfTm k13 t1) := match H44 in (wfTm _ s6) return match s6 return Prop with
    | (prod t1 t2) => (wfTm k13 t1)
    | _ => True
  end with
    | (wfTm_prod t1 H24 t2 H25) => H24
    | _ => I
  end.
  Definition inversion_wfTm_prod_1 (k13 : Hvl) (t1 : Tm) (t2 : Tm) (H44 : (wfTm k13 (prod t1 t2))) : (wfTm k13 t2) := match H44 in (wfTm _ s6) return match s6 return Prop with
    | (prod t1 t2) => (wfTm k13 t2)
    | _ => True
  end with
    | (wfTm_prod t1 H24 t2 H25) => H25
    | _ => I
  end.
  Definition inversion_wfTm_case_0 (k14 : Hvl) (t1 : Tm) (p : Pat) (t2 : Tm) (H45 : (wfTm k14 (case t1 p t2))) : (wfTm k14 t1) := match H45 in (wfTm _ s7) return match s7 return Prop with
    | (case t1 p t2) => (wfTm k14 t1)
    | _ => True
  end with
    | (wfTm_case t1 H26 p H27 t2 H28) => H26
    | _ => I
  end.
  Definition inversion_wfTm_case_1 (k14 : Hvl) (t1 : Tm) (p : Pat) (t2 : Tm) (H45 : (wfTm k14 (case t1 p t2))) : (wfPat k14 p) := match H45 in (wfTm _ s7) return match s7 return Prop with
    | (case t1 p t2) => (wfPat k14 p)
    | _ => True
  end with
    | (wfTm_case t1 H26 p H27 t2 H28) => H27
    | _ => I
  end.
  Definition inversion_wfTm_case_2 (k14 : Hvl) (t1 : Tm) (p : Pat) (t2 : Tm) (H45 : (wfTm k14 (case t1 p t2))) : (wfTm (appendHvl k14 (appendHvl H0 (bindPat p))) t2) := match H45 in (wfTm _ s7) return match s7 return Prop with
    | (case t1 p t2) => (wfTm (appendHvl k14 (appendHvl H0 (bindPat p))) t2)
    | _ => True
  end with
    | (wfTm_case t1 H26 p H27 t2 H28) => H28
    | _ => I
  end.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfPat := Induction for wfPat Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c0 : (Cutoff tm)) (k15 : Hvl) (k16 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k15 : Hvl)
        :
        (shifthvl_tm C0 k15 (HS tm k15))
    | shifthvl_tm_there_tm
        (c0 : (Cutoff tm)) (k15 : Hvl)
        (k16 : Hvl) :
        (shifthvl_tm c0 k15 k16) -> (shifthvl_tm (CS c0) (HS tm k15) (HS tm k16))
    | shifthvl_tm_there_ty
        (c0 : (Cutoff tm)) (k15 : Hvl)
        (k16 : Hvl) :
        (shifthvl_tm c0 k15 k16) -> (shifthvl_tm c0 (HS ty k15) (HS ty k16)).
  Inductive shifthvl_ty : (forall (c0 : (Cutoff ty)) (k15 : Hvl) (k16 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k15 : Hvl)
        :
        (shifthvl_ty C0 k15 (HS ty k15))
    | shifthvl_ty_there_tm
        (c0 : (Cutoff ty)) (k15 : Hvl)
        (k16 : Hvl) :
        (shifthvl_ty c0 k15 k16) -> (shifthvl_ty c0 (HS tm k15) (HS tm k16))
    | shifthvl_ty_there_ty
        (c0 : (Cutoff ty)) (k15 : Hvl)
        (k16 : Hvl) :
        (shifthvl_ty c0 k15 k16) -> (shifthvl_ty (CS c0) (HS ty k15) (HS ty k16)).
  Lemma weaken_shifthvl_tm  :
    (forall (k15 : Hvl) {c0 : (Cutoff tm)} {k16 : Hvl} {k17 : Hvl} ,
      (shifthvl_tm c0 k16 k17) -> (shifthvl_tm (weakenCutofftm c0 k15) (appendHvl k16 k15) (appendHvl k17 k15))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k15 : Hvl) {c0 : (Cutoff ty)} {k16 : Hvl} {k17 : Hvl} ,
      (shifthvl_ty c0 k16 k17) -> (shifthvl_ty (weakenCutoffty c0 k15) (appendHvl k16 k15) (appendHvl k17 k15))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c0 : (Cutoff tm)) (k15 : Hvl) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) (x18 : (Index tm)) ,
      (wfindex k15 x18) -> (wfindex k16 (shiftIndex c0 x18))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c0 : (Cutoff tm)) (k15 : Hvl) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) (X23 : (Index ty)) ,
      (wfindex k15 X23) -> (wfindex k16 X23)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c0 : (Cutoff ty)) (k15 : Hvl) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) (x18 : (Index tm)) ,
      (wfindex k15 x18) -> (wfindex k16 x18)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c0 : (Cutoff ty)) (k15 : Hvl) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) (X23 : (Index ty)) ,
      (wfindex k15 X23) -> (wfindex k16 (tshiftIndex c0 X23))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfTy : (forall (k15 : Hvl) ,
    (forall (S6 : Ty) (wf : (wfTy k15 S6)) ,
      (forall (c0 : (Cutoff tm)) (k16 : Hvl) ,
        (shifthvl_tm c0 k15 k16) -> (wfTy k16 S6)))) := (ind_wfTy (fun (k15 : Hvl) (S6 : Ty) (wf : (wfTy k15 S6)) =>
    (forall (c0 : (Cutoff tm)) (k16 : Hvl) ,
      (shifthvl_tm c0 k15 k16) -> (wfTy k16 S6))) (fun (k15 : Hvl) (X23 : (Index ty)) (wfi : (wfindex k15 X23)) (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfTy_tvar k16 _ (shift_wfindex_ty c0 k15 k16 ins X23 wfi))) (fun (k15 : Hvl) (T1 : Ty) (wf : (wfTy k15 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k15 T2)) IHT2 (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfTy_tarr k16 (IHT1 c0 k16 (weaken_shifthvl_tm H0 ins)) (IHT2 c0 k16 (weaken_shifthvl_tm H0 ins)))) (fun (k15 : Hvl) (T : Ty) (wf : (wfTy (HS ty k15) T)) IHT (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfTy_tall k16 (IHT c0 (HS ty k16) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k15 : Hvl) (T : Ty) (wf : (wfTy (HS ty k15) T)) IHT (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfTy_texist k16 (IHT c0 (HS ty k16) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k15 : Hvl) (T1 : Ty) (wf : (wfTy k15 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k15 T2)) IHT2 (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfTy_tprod k16 (IHT1 c0 k16 (weaken_shifthvl_tm H0 ins)) (IHT2 c0 k16 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTy : (forall (k15 : Hvl) ,
    (forall (S6 : Ty) (wf : (wfTy k15 S6)) ,
      (forall (c0 : (Cutoff ty)) (k16 : Hvl) ,
        (shifthvl_ty c0 k15 k16) -> (wfTy k16 (tshiftTy c0 S6))))) := (ind_wfTy (fun (k15 : Hvl) (S6 : Ty) (wf : (wfTy k15 S6)) =>
    (forall (c0 : (Cutoff ty)) (k16 : Hvl) ,
      (shifthvl_ty c0 k15 k16) -> (wfTy k16 (tshiftTy c0 S6)))) (fun (k15 : Hvl) (X23 : (Index ty)) (wfi : (wfindex k15 X23)) (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfTy_tvar k16 _ (tshift_wfindex_ty c0 k15 k16 ins X23 wfi))) (fun (k15 : Hvl) (T1 : Ty) (wf : (wfTy k15 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k15 T2)) IHT2 (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfTy_tarr k16 (IHT1 c0 k16 (weaken_shifthvl_ty H0 ins)) (IHT2 c0 k16 (weaken_shifthvl_ty H0 ins)))) (fun (k15 : Hvl) (T : Ty) (wf : (wfTy (HS ty k15) T)) IHT (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfTy_tall k16 (IHT (CS c0) (HS ty k16) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k15 : Hvl) (T : Ty) (wf : (wfTy (HS ty k15) T)) IHT (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfTy_texist k16 (IHT (CS c0) (HS ty k16) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k15 : Hvl) (T1 : Ty) (wf : (wfTy k15 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k15 T2)) IHT2 (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfTy_tprod k16 (IHT1 c0 k16 (weaken_shifthvl_ty H0 ins)) (IHT2 c0 k16 (weaken_shifthvl_ty H0 ins))))).
  Definition shift_wfPat : (forall (k15 : Hvl) ,
    (forall (p22 : Pat) (wf : (wfPat k15 p22)) ,
      (forall (c0 : (Cutoff tm)) (k16 : Hvl) ,
        (shifthvl_tm c0 k15 k16) -> (wfPat k16 p22)))) := (ind_wfPat (fun (k15 : Hvl) (p22 : Pat) (wf : (wfPat k15 p22)) =>
    (forall (c0 : (Cutoff tm)) (k16 : Hvl) ,
      (shifthvl_tm c0 k15 k16) -> (wfPat k16 p22))) (fun (k15 : Hvl) (T : Ty) (wf : (wfTy k15 T)) (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfPat_pvar k16 (shift_wfTy k15 T wf c0 k16 (weaken_shifthvl_tm H0 ins)))) (fun (k15 : Hvl) (p1 : Pat) (wf : (wfPat k15 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k15 (appendHvl H0 (bindPat p1))) p2)) IHp2 (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfPat_pprod k16 (IHp1 c0 k16 (weaken_shifthvl_tm H0 ins)) (IHp2 (weakenCutofftm c0 (appendHvl H0 (bindPat p1))) (appendHvl k16 (appendHvl H0 (bindPat p1))) (weaken_shifthvl_tm (appendHvl H0 (bindPat p1)) ins))))).
  Definition tshift_wfPat : (forall (k15 : Hvl) ,
    (forall (p22 : Pat) (wf : (wfPat k15 p22)) ,
      (forall (c0 : (Cutoff ty)) (k16 : Hvl) ,
        (shifthvl_ty c0 k15 k16) -> (wfPat k16 (tshiftPat c0 p22))))) := (ind_wfPat (fun (k15 : Hvl) (p22 : Pat) (wf : (wfPat k15 p22)) =>
    (forall (c0 : (Cutoff ty)) (k16 : Hvl) ,
      (shifthvl_ty c0 k15 k16) -> (wfPat k16 (tshiftPat c0 p22)))) (fun (k15 : Hvl) (T : Ty) (wf : (wfTy k15 T)) (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfPat_pvar k16 (tshift_wfTy k15 T wf c0 k16 (weaken_shifthvl_ty H0 ins)))) (fun (k15 : Hvl) (p1 : Pat) (wf : (wfPat k15 p1)) IHp1 (p2 : Pat) (wf0 : (wfPat (appendHvl k15 (appendHvl H0 (bindPat p1))) p2)) IHp2 (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfPat_pprod k16 (IHp1 c0 k16 (weaken_shifthvl_ty H0 ins)) (eq_ind2 wfPat (f_equal2 appendHvl (eq_refl k16) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))) eq_refl (IHp2 (weakenCutoffty c0 (appendHvl H0 (bindPat p1))) (appendHvl k16 (appendHvl H0 (bindPat p1))) (weaken_shifthvl_ty (appendHvl H0 (bindPat p1)) ins)))))).
  Definition shift_wfTm : (forall (k15 : Hvl) ,
    (forall (s8 : Tm) (wf : (wfTm k15 s8)) ,
      (forall (c0 : (Cutoff tm)) (k16 : Hvl) ,
        (shifthvl_tm c0 k15 k16) -> (wfTm k16 (shiftTm c0 s8))))) := (ind_wfTm (fun (k15 : Hvl) (s8 : Tm) (wf : (wfTm k15 s8)) =>
    (forall (c0 : (Cutoff tm)) (k16 : Hvl) ,
      (shifthvl_tm c0 k15 k16) -> (wfTm k16 (shiftTm c0 s8)))) (fun (k15 : Hvl) (x18 : (Index tm)) (wfi : (wfindex k15 x18)) (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfTm_var k16 _ (shift_wfindex_tm c0 k15 k16 ins x18 wfi))) (fun (k15 : Hvl) (T : Ty) (wf : (wfTy k15 T)) (t : Tm) (wf0 : (wfTm (HS tm k15) t)) IHt (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfTm_abs k16 (shift_wfTy k15 T wf c0 k16 (weaken_shifthvl_tm H0 ins)) (IHt (CS c0) (HS tm k16) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k15 : Hvl) (t1 : Tm) (wf : (wfTm k15 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k15 t2)) IHt2 (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfTm_app k16 (IHt1 c0 k16 (weaken_shifthvl_tm H0 ins)) (IHt2 c0 k16 (weaken_shifthvl_tm H0 ins)))) (fun (k15 : Hvl) (t : Tm) (wf : (wfTm (HS ty k15) t)) IHt (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfTm_tabs k16 (IHt c0 (HS ty k16) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k15 : Hvl) (t : Tm) (wf : (wfTm k15 t)) IHt (T : Ty) (wf0 : (wfTy k15 T)) (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfTm_tapp k16 (IHt c0 k16 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k15 T wf0 c0 k16 (weaken_shifthvl_tm H0 ins)))) (fun (k15 : Hvl) (T1 : Ty) (wf : (wfTy k15 T1)) (t : Tm) (wf0 : (wfTm k15 t)) IHt (T2 : Ty) (wf1 : (wfTy k15 T2)) (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfTm_pack k16 (shift_wfTy k15 T1 wf c0 k16 (weaken_shifthvl_tm H0 ins)) (IHt c0 k16 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k15 T2 wf1 c0 k16 (weaken_shifthvl_tm H0 ins)))) (fun (k15 : Hvl) (t1 : Tm) (wf : (wfTm k15 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm (HS tm (HS ty k15)) t2)) IHt2 (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfTm_unpack k16 (IHt1 c0 k16 (weaken_shifthvl_tm H0 ins)) (IHt2 (CS c0) (HS tm (HS ty k16)) (weaken_shifthvl_tm (HS tm (HS ty H0)) ins)))) (fun (k15 : Hvl) (t1 : Tm) (wf : (wfTm k15 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k15 t2)) IHt2 (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfTm_prod k16 (IHt1 c0 k16 (weaken_shifthvl_tm H0 ins)) (IHt2 c0 k16 (weaken_shifthvl_tm H0 ins)))) (fun (k15 : Hvl) (t1 : Tm) (wf : (wfTm k15 t1)) IHt1 (p : Pat) (wf0 : (wfPat k15 p)) (t2 : Tm) (wf1 : (wfTm (appendHvl k15 (appendHvl H0 (bindPat p))) t2)) IHt2 (c0 : (Cutoff tm)) (k16 : Hvl) (ins : (shifthvl_tm c0 k15 k16)) =>
    (wfTm_case k16 (IHt1 c0 k16 (weaken_shifthvl_tm H0 ins)) (shift_wfPat k15 p wf0 c0 k16 (weaken_shifthvl_tm H0 ins)) (IHt2 (weakenCutofftm c0 (appendHvl H0 (bindPat p))) (appendHvl k16 (appendHvl H0 (bindPat p))) (weaken_shifthvl_tm (appendHvl H0 (bindPat p)) ins))))).
  Definition tshift_wfTm : (forall (k15 : Hvl) ,
    (forall (s8 : Tm) (wf : (wfTm k15 s8)) ,
      (forall (c0 : (Cutoff ty)) (k16 : Hvl) ,
        (shifthvl_ty c0 k15 k16) -> (wfTm k16 (tshiftTm c0 s8))))) := (ind_wfTm (fun (k15 : Hvl) (s8 : Tm) (wf : (wfTm k15 s8)) =>
    (forall (c0 : (Cutoff ty)) (k16 : Hvl) ,
      (shifthvl_ty c0 k15 k16) -> (wfTm k16 (tshiftTm c0 s8)))) (fun (k15 : Hvl) (x18 : (Index tm)) (wfi : (wfindex k15 x18)) (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfTm_var k16 _ (tshift_wfindex_tm c0 k15 k16 ins x18 wfi))) (fun (k15 : Hvl) (T : Ty) (wf : (wfTy k15 T)) (t : Tm) (wf0 : (wfTm (HS tm k15) t)) IHt (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfTm_abs k16 (tshift_wfTy k15 T wf c0 k16 (weaken_shifthvl_ty H0 ins)) (IHt c0 (HS tm k16) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k15 : Hvl) (t1 : Tm) (wf : (wfTm k15 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k15 t2)) IHt2 (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfTm_app k16 (IHt1 c0 k16 (weaken_shifthvl_ty H0 ins)) (IHt2 c0 k16 (weaken_shifthvl_ty H0 ins)))) (fun (k15 : Hvl) (t : Tm) (wf : (wfTm (HS ty k15) t)) IHt (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfTm_tabs k16 (IHt (CS c0) (HS ty k16) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k15 : Hvl) (t : Tm) (wf : (wfTm k15 t)) IHt (T : Ty) (wf0 : (wfTy k15 T)) (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfTm_tapp k16 (IHt c0 k16 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k15 T wf0 c0 k16 (weaken_shifthvl_ty H0 ins)))) (fun (k15 : Hvl) (T1 : Ty) (wf : (wfTy k15 T1)) (t : Tm) (wf0 : (wfTm k15 t)) IHt (T2 : Ty) (wf1 : (wfTy k15 T2)) (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfTm_pack k16 (tshift_wfTy k15 T1 wf c0 k16 (weaken_shifthvl_ty H0 ins)) (IHt c0 k16 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k15 T2 wf1 c0 k16 (weaken_shifthvl_ty H0 ins)))) (fun (k15 : Hvl) (t1 : Tm) (wf : (wfTm k15 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm (HS tm (HS ty k15)) t2)) IHt2 (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfTm_unpack k16 (IHt1 c0 k16 (weaken_shifthvl_ty H0 ins)) (IHt2 (CS c0) (HS tm (HS ty k16)) (weaken_shifthvl_ty (HS tm (HS ty H0)) ins)))) (fun (k15 : Hvl) (t1 : Tm) (wf : (wfTm k15 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k15 t2)) IHt2 (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfTm_prod k16 (IHt1 c0 k16 (weaken_shifthvl_ty H0 ins)) (IHt2 c0 k16 (weaken_shifthvl_ty H0 ins)))) (fun (k15 : Hvl) (t1 : Tm) (wf : (wfTm k15 t1)) IHt1 (p : Pat) (wf0 : (wfPat k15 p)) (t2 : Tm) (wf1 : (wfTm (appendHvl k15 (appendHvl H0 (bindPat p))) t2)) IHt2 (c0 : (Cutoff ty)) (k16 : Hvl) (ins : (shifthvl_ty c0 k15 k16)) =>
    (wfTm_case k16 (IHt1 c0 k16 (weaken_shifthvl_ty H0 ins)) (tshift_wfPat k15 p wf0 c0 k16 (weaken_shifthvl_ty H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k16) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))) eq_refl (IHt2 (weakenCutoffty c0 (appendHvl H0 (bindPat p))) (appendHvl k16 (appendHvl H0 (bindPat p))) (weaken_shifthvl_ty (appendHvl H0 (bindPat p)) ins)))))).
  Fixpoint weaken_wfTy (k15 : Hvl) {struct k15} :
  (forall (k16 : Hvl) (S6 : Ty) (wf : (wfTy k16 S6)) ,
    (wfTy (appendHvl k16 k15) (weakenTy S6 k15))) :=
    match k15 return (forall (k16 : Hvl) (S6 : Ty) (wf : (wfTy k16 S6)) ,
      (wfTy (appendHvl k16 k15) (weakenTy S6 k15))) with
      | (H0) => (fun (k16 : Hvl) (S6 : Ty) (wf : (wfTy k16 S6)) =>
        wf)
      | (HS tm k15) => (fun (k16 : Hvl) (S6 : Ty) (wf : (wfTy k16 S6)) =>
        (shift_wfTy (appendHvl k16 k15) (weakenTy S6 k15) (weaken_wfTy k15 k16 S6 wf) C0 (HS tm (appendHvl k16 k15)) (shifthvl_tm_here (appendHvl k16 k15))))
      | (HS ty k15) => (fun (k16 : Hvl) (S6 : Ty) (wf : (wfTy k16 S6)) =>
        (tshift_wfTy (appendHvl k16 k15) (weakenTy S6 k15) (weaken_wfTy k15 k16 S6 wf) C0 (HS ty (appendHvl k16 k15)) (shifthvl_ty_here (appendHvl k16 k15))))
    end.
  Fixpoint weaken_wfPat (k15 : Hvl) {struct k15} :
  (forall (k16 : Hvl) (p22 : Pat) (wf : (wfPat k16 p22)) ,
    (wfPat (appendHvl k16 k15) (weakenPat p22 k15))) :=
    match k15 return (forall (k16 : Hvl) (p22 : Pat) (wf : (wfPat k16 p22)) ,
      (wfPat (appendHvl k16 k15) (weakenPat p22 k15))) with
      | (H0) => (fun (k16 : Hvl) (p22 : Pat) (wf : (wfPat k16 p22)) =>
        wf)
      | (HS tm k15) => (fun (k16 : Hvl) (p22 : Pat) (wf : (wfPat k16 p22)) =>
        (shift_wfPat (appendHvl k16 k15) (weakenPat p22 k15) (weaken_wfPat k15 k16 p22 wf) C0 (HS tm (appendHvl k16 k15)) (shifthvl_tm_here (appendHvl k16 k15))))
      | (HS ty k15) => (fun (k16 : Hvl) (p22 : Pat) (wf : (wfPat k16 p22)) =>
        (tshift_wfPat (appendHvl k16 k15) (weakenPat p22 k15) (weaken_wfPat k15 k16 p22 wf) C0 (HS ty (appendHvl k16 k15)) (shifthvl_ty_here (appendHvl k16 k15))))
    end.
  Fixpoint weaken_wfTm (k15 : Hvl) {struct k15} :
  (forall (k16 : Hvl) (s8 : Tm) (wf : (wfTm k16 s8)) ,
    (wfTm (appendHvl k16 k15) (weakenTm s8 k15))) :=
    match k15 return (forall (k16 : Hvl) (s8 : Tm) (wf : (wfTm k16 s8)) ,
      (wfTm (appendHvl k16 k15) (weakenTm s8 k15))) with
      | (H0) => (fun (k16 : Hvl) (s8 : Tm) (wf : (wfTm k16 s8)) =>
        wf)
      | (HS tm k15) => (fun (k16 : Hvl) (s8 : Tm) (wf : (wfTm k16 s8)) =>
        (shift_wfTm (appendHvl k16 k15) (weakenTm s8 k15) (weaken_wfTm k15 k16 s8 wf) C0 (HS tm (appendHvl k16 k15)) (shifthvl_tm_here (appendHvl k16 k15))))
      | (HS ty k15) => (fun (k16 : Hvl) (s8 : Tm) (wf : (wfTm k16 s8)) =>
        (tshift_wfTm (appendHvl k16 k15) (weakenTm s8 k15) (weaken_wfTm k15 k16 s8 wf) C0 (HS ty (appendHvl k16 k15)) (shifthvl_ty_here (appendHvl k16 k15))))
    end.
End ShiftWellFormed.
Lemma wfTy_cast  :
  (forall (k19 : Hvl) (S7 : Ty) (k20 : Hvl) (S8 : Ty) ,
    (k19 = k20) -> (S7 = S8) -> (wfTy k19 S7) -> (wfTy k20 S8)).
Proof.
  congruence .
Qed.
Lemma wfPat_cast  :
  (forall (k19 : Hvl) (p23 : Pat) (k20 : Hvl) (p24 : Pat) ,
    (k19 = k20) -> (p23 = p24) -> (wfPat k19 p23) -> (wfPat k20 p24)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k19 : Hvl) (s8 : Tm) (k20 : Hvl) (s9 : Tm) ,
    (k19 = k20) -> (s8 = s9) -> (wfTm k19 s8) -> (wfTm k20 s9)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : infra.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift_wf.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : wf.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : infra.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : shift.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : shift_wf.
 Hint Resolve shift_wfPat shift_wfTm shift_wfTy tshift_wfPat tshift_wfTm tshift_wfTy : wf.
 Hint Constructors shifthvl_tm shifthvl_ty : infra.
 Hint Constructors shifthvl_tm shifthvl_ty : shift.
 Hint Constructors shifthvl_tm shifthvl_ty : shift_wf.
 Hint Constructors shifthvl_tm shifthvl_ty : wf.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : infra.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : shift.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : shift_wf.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : weaken.
 Hint Resolve weaken_shifthvl_tm weaken_shifthvl_ty : wf.
Section SubstWellFormed.
  Inductive substhvl_tm (k15 : Hvl) : (forall (d0 : (Trace tm)) (k16 : Hvl) (k17 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k15 X0 (HS tm k15) k15)
    | substhvl_tm_there_tm
        {d0 : (Trace tm)} {k16 : Hvl}
        {k17 : Hvl} :
        (substhvl_tm k15 d0 k16 k17) -> (substhvl_tm k15 (XS tm d0) (HS tm k16) (HS tm k17))
    | substhvl_tm_there_ty
        {d0 : (Trace tm)} {k16 : Hvl}
        {k17 : Hvl} :
        (substhvl_tm k15 d0 k16 k17) -> (substhvl_tm k15 (XS ty d0) (HS ty k16) (HS ty k17)).
  Inductive substhvl_ty (k15 : Hvl) : (forall (d0 : (Trace ty)) (k16 : Hvl) (k17 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k15 X0 (HS ty k15) k15)
    | substhvl_ty_there_tm
        {d0 : (Trace ty)} {k16 : Hvl}
        {k17 : Hvl} :
        (substhvl_ty k15 d0 k16 k17) -> (substhvl_ty k15 (XS tm d0) (HS tm k16) (HS tm k17))
    | substhvl_ty_there_ty
        {d0 : (Trace ty)} {k16 : Hvl}
        {k17 : Hvl} :
        (substhvl_ty k15 d0 k16 k17) -> (substhvl_ty k15 (XS ty d0) (HS ty k16) (HS ty k17)).
  Lemma weaken_substhvl_tm  :
    (forall {k16 : Hvl} (k15 : Hvl) {d0 : (Trace tm)} {k17 : Hvl} {k18 : Hvl} ,
      (substhvl_tm k16 d0 k17 k18) -> (substhvl_tm k16 (weakenTrace d0 k15) (appendHvl k17 k15) (appendHvl k18 k15))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k16 : Hvl} (k15 : Hvl) {d0 : (Trace ty)} {k17 : Hvl} {k18 : Hvl} ,
      (substhvl_ty k16 d0 k17 k18) -> (substhvl_ty k16 (weakenTrace d0 k15) (appendHvl k17 k15) (appendHvl k18 k15))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k19 : Hvl} {s8 : Tm} (wft : (wfTm k19 s8)) :
    (forall {d0 : (Trace tm)} {k20 : Hvl} {k21 : Hvl} ,
      (substhvl_tm k19 d0 k20 k21) -> (forall {x18 : (Index tm)} ,
        (wfindex k20 x18) -> (wfTm k21 (substIndex d0 s8 x18)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k19 : Hvl} {S7 : Ty} (wft : (wfTy k19 S7)) :
    (forall {d0 : (Trace ty)} {k20 : Hvl} {k21 : Hvl} ,
      (substhvl_ty k19 d0 k20 k21) -> (forall {X23 : (Index ty)} ,
        (wfindex k20 X23) -> (wfTy k21 (tsubstIndex d0 S7 X23)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k19 : Hvl} :
    (forall {d0 : (Trace tm)} {k20 : Hvl} {k21 : Hvl} ,
      (substhvl_tm k19 d0 k20 k21) -> (forall {X23 : (Index ty)} ,
        (wfindex k20 X23) -> (wfindex k21 X23))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k19 : Hvl} :
    (forall {d0 : (Trace ty)} {k20 : Hvl} {k21 : Hvl} ,
      (substhvl_ty k19 d0 k20 k21) -> (forall {x18 : (Index tm)} ,
        (wfindex k20 x18) -> (wfindex k21 x18))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfTy {k19 : Hvl} : (forall (k20 : Hvl) ,
    (forall (S7 : Ty) (wf0 : (wfTy k20 S7)) ,
      (forall {d0 : (Trace tm)} {k21 : Hvl} ,
        (substhvl_tm k19 d0 k20 k21) -> (wfTy k21 S7)))) := (ind_wfTy (fun (k20 : Hvl) (S7 : Ty) (wf0 : (wfTy k20 S7)) =>
    (forall {d0 : (Trace tm)} {k21 : Hvl} ,
      (substhvl_tm k19 d0 k20 k21) -> (wfTy k21 S7))) (fun (k20 : Hvl) {X23 : (Index ty)} (wfi : (wfindex k20 X23)) {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfTy_tvar k21 _ (substhvl_tm_wfindex_ty del wfi))) (fun (k20 : Hvl) (T1 : Ty) (wf0 : (wfTy k20 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k20 T2)) IHT2 {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfTy_tarr k21 (IHT1 (weakenTrace d0 H0) k21 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d0 H0) k21 (weaken_substhvl_tm H0 del)))) (fun (k20 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k20) T)) IHT {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfTy_tall k21 (IHT (weakenTrace d0 (HS ty H0)) (HS ty k21) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k20 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k20) T)) IHT {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfTy_texist k21 (IHT (weakenTrace d0 (HS ty H0)) (HS ty k21) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k20 : Hvl) (T1 : Ty) (wf0 : (wfTy k20 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k20 T2)) IHT2 {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfTy_tprod k21 (IHT1 (weakenTrace d0 H0) k21 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d0 H0) k21 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTy {k19 : Hvl} {S7 : Ty} (wf : (wfTy k19 S7)) : (forall (k20 : Hvl) ,
    (forall (S8 : Ty) (wf0 : (wfTy k20 S8)) ,
      (forall {d0 : (Trace ty)} {k21 : Hvl} ,
        (substhvl_ty k19 d0 k20 k21) -> (wfTy k21 (tsubstTy d0 S7 S8))))) := (ind_wfTy (fun (k20 : Hvl) (S8 : Ty) (wf0 : (wfTy k20 S8)) =>
    (forall {d0 : (Trace ty)} {k21 : Hvl} ,
      (substhvl_ty k19 d0 k20 k21) -> (wfTy k21 (tsubstTy d0 S7 S8)))) (fun (k20 : Hvl) {X23 : (Index ty)} (wfi : (wfindex k20 X23)) {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k20 : Hvl) (T1 : Ty) (wf0 : (wfTy k20 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k20 T2)) IHT2 {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfTy_tarr k21 (IHT1 (weakenTrace d0 H0) k21 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d0 H0) k21 (weaken_substhvl_ty H0 del)))) (fun (k20 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k20) T)) IHT {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfTy_tall k21 (IHT (weakenTrace d0 (HS ty H0)) (HS ty k21) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k20 : Hvl) (T : Ty) (wf0 : (wfTy (HS ty k20) T)) IHT {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfTy_texist k21 (IHT (weakenTrace d0 (HS ty H0)) (HS ty k21) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k20 : Hvl) (T1 : Ty) (wf0 : (wfTy k20 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k20 T2)) IHT2 {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfTy_tprod k21 (IHT1 (weakenTrace d0 H0) k21 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d0 H0) k21 (weaken_substhvl_ty H0 del))))).
  Definition substhvl_tm_wfPat {k19 : Hvl} : (forall (k20 : Hvl) ,
    (forall (p23 : Pat) (wf0 : (wfPat k20 p23)) ,
      (forall {d0 : (Trace tm)} {k21 : Hvl} ,
        (substhvl_tm k19 d0 k20 k21) -> (wfPat k21 p23)))) := (ind_wfPat (fun (k20 : Hvl) (p23 : Pat) (wf0 : (wfPat k20 p23)) =>
    (forall {d0 : (Trace tm)} {k21 : Hvl} ,
      (substhvl_tm k19 d0 k20 k21) -> (wfPat k21 p23))) (fun (k20 : Hvl) (T : Ty) (wf0 : (wfTy k20 T)) {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfPat_pvar k21 (substhvl_tm_wfTy k20 T wf0 (weaken_substhvl_tm H0 del)))) (fun (k20 : Hvl) (p1 : Pat) (wf0 : (wfPat k20 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k20 (appendHvl H0 (bindPat p1))) p2)) IHp2 {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfPat_pprod k21 (IHp1 (weakenTrace d0 H0) k21 (weaken_substhvl_tm H0 del)) (IHp2 (weakenTrace d0 (appendHvl H0 (bindPat p1))) (appendHvl k21 (appendHvl H0 (bindPat p1))) (weaken_substhvl_tm (appendHvl H0 (bindPat p1)) del))))).
  Definition substhvl_ty_wfPat {k19 : Hvl} {S7 : Ty} (wf : (wfTy k19 S7)) : (forall (k20 : Hvl) ,
    (forall (p23 : Pat) (wf0 : (wfPat k20 p23)) ,
      (forall {d0 : (Trace ty)} {k21 : Hvl} ,
        (substhvl_ty k19 d0 k20 k21) -> (wfPat k21 (tsubstPat d0 S7 p23))))) := (ind_wfPat (fun (k20 : Hvl) (p23 : Pat) (wf0 : (wfPat k20 p23)) =>
    (forall {d0 : (Trace ty)} {k21 : Hvl} ,
      (substhvl_ty k19 d0 k20 k21) -> (wfPat k21 (tsubstPat d0 S7 p23)))) (fun (k20 : Hvl) (T : Ty) (wf0 : (wfTy k20 T)) {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfPat_pvar k21 (substhvl_ty_wfTy wf k20 T wf0 (weaken_substhvl_ty H0 del)))) (fun (k20 : Hvl) (p1 : Pat) (wf0 : (wfPat k20 p1)) IHp1 (p2 : Pat) (wf1 : (wfPat (appendHvl k20 (appendHvl H0 (bindPat p1))) p2)) IHp2 {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfPat_pprod k21 (IHp1 (weakenTrace d0 H0) k21 (weaken_substhvl_ty H0 del)) (eq_ind2 wfPat (f_equal2 appendHvl (eq_refl k21) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (IHp2 (weakenTrace d0 (appendHvl H0 (bindPat p1))) (appendHvl k21 (appendHvl H0 (bindPat p1))) (weaken_substhvl_ty (appendHvl H0 (bindPat p1)) del)))))).
  Definition substhvl_tm_wfTm {k19 : Hvl} {s8 : Tm} (wf : (wfTm k19 s8)) : (forall (k20 : Hvl) ,
    (forall (s9 : Tm) (wf0 : (wfTm k20 s9)) ,
      (forall {d0 : (Trace tm)} {k21 : Hvl} ,
        (substhvl_tm k19 d0 k20 k21) -> (wfTm k21 (substTm d0 s8 s9))))) := (ind_wfTm (fun (k20 : Hvl) (s9 : Tm) (wf0 : (wfTm k20 s9)) =>
    (forall {d0 : (Trace tm)} {k21 : Hvl} ,
      (substhvl_tm k19 d0 k20 k21) -> (wfTm k21 (substTm d0 s8 s9)))) (fun (k20 : Hvl) {x18 : (Index tm)} (wfi : (wfindex k20 x18)) {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k20 : Hvl) (T : Ty) (wf0 : (wfTy k20 T)) (t : Tm) (wf1 : (wfTm (HS tm k20) t)) IHt {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfTm_abs k21 (substhvl_tm_wfTy k20 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d0 (HS tm H0)) (HS tm k21) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k20 : Hvl) (t1 : Tm) (wf0 : (wfTm k20 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k20 t2)) IHt2 {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfTm_app k21 (IHt1 (weakenTrace d0 H0) k21 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d0 H0) k21 (weaken_substhvl_tm H0 del)))) (fun (k20 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k20) t)) IHt {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfTm_tabs k21 (IHt (weakenTrace d0 (HS ty H0)) (HS ty k21) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k20 : Hvl) (t : Tm) (wf0 : (wfTm k20 t)) IHt (T : Ty) (wf1 : (wfTy k20 T)) {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfTm_tapp k21 (IHt (weakenTrace d0 H0) k21 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k20 T wf1 (weaken_substhvl_tm H0 del)))) (fun (k20 : Hvl) (T1 : Ty) (wf0 : (wfTy k20 T1)) (t : Tm) (wf1 : (wfTm k20 t)) IHt (T2 : Ty) (wf2 : (wfTy k20 T2)) {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfTm_pack k21 (substhvl_tm_wfTy k20 T1 wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d0 H0) k21 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k20 T2 wf2 (weaken_substhvl_tm H0 del)))) (fun (k20 : Hvl) (t1 : Tm) (wf0 : (wfTm k20 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (HS tm (HS ty k20)) t2)) IHt2 {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfTm_unpack k21 (IHt1 (weakenTrace d0 H0) k21 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d0 (HS tm (HS ty H0))) (HS tm (HS ty k21)) (weaken_substhvl_tm (HS tm (HS ty H0)) del)))) (fun (k20 : Hvl) (t1 : Tm) (wf0 : (wfTm k20 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k20 t2)) IHt2 {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfTm_prod k21 (IHt1 (weakenTrace d0 H0) k21 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d0 H0) k21 (weaken_substhvl_tm H0 del)))) (fun (k20 : Hvl) (t1 : Tm) (wf0 : (wfTm k20 t1)) IHt1 (p : Pat) (wf1 : (wfPat k20 p)) (t2 : Tm) (wf2 : (wfTm (appendHvl k20 (appendHvl H0 (bindPat p))) t2)) IHt2 {d0 : (Trace tm)} {k21 : Hvl} (del : (substhvl_tm k19 d0 k20 k21)) =>
    (wfTm_case k21 (IHt1 (weakenTrace d0 H0) k21 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfPat k20 p wf1 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d0 (appendHvl H0 (bindPat p))) (appendHvl k21 (appendHvl H0 (bindPat p))) (weaken_substhvl_tm (appendHvl H0 (bindPat p)) del))))).
  Definition substhvl_ty_wfTm {k19 : Hvl} {S7 : Ty} (wf : (wfTy k19 S7)) : (forall (k20 : Hvl) ,
    (forall (s8 : Tm) (wf0 : (wfTm k20 s8)) ,
      (forall {d0 : (Trace ty)} {k21 : Hvl} ,
        (substhvl_ty k19 d0 k20 k21) -> (wfTm k21 (tsubstTm d0 S7 s8))))) := (ind_wfTm (fun (k20 : Hvl) (s8 : Tm) (wf0 : (wfTm k20 s8)) =>
    (forall {d0 : (Trace ty)} {k21 : Hvl} ,
      (substhvl_ty k19 d0 k20 k21) -> (wfTm k21 (tsubstTm d0 S7 s8)))) (fun (k20 : Hvl) {x18 : (Index tm)} (wfi : (wfindex k20 x18)) {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfTm_var k21 _ (substhvl_ty_wfindex_tm del wfi))) (fun (k20 : Hvl) (T : Ty) (wf0 : (wfTy k20 T)) (t : Tm) (wf1 : (wfTm (HS tm k20) t)) IHt {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfTm_abs k21 (substhvl_ty_wfTy wf k20 T wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d0 (HS tm H0)) (HS tm k21) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k20 : Hvl) (t1 : Tm) (wf0 : (wfTm k20 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k20 t2)) IHt2 {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfTm_app k21 (IHt1 (weakenTrace d0 H0) k21 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d0 H0) k21 (weaken_substhvl_ty H0 del)))) (fun (k20 : Hvl) (t : Tm) (wf0 : (wfTm (HS ty k20) t)) IHt {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfTm_tabs k21 (IHt (weakenTrace d0 (HS ty H0)) (HS ty k21) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k20 : Hvl) (t : Tm) (wf0 : (wfTm k20 t)) IHt (T : Ty) (wf1 : (wfTy k20 T)) {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfTm_tapp k21 (IHt (weakenTrace d0 H0) k21 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k20 T wf1 (weaken_substhvl_ty H0 del)))) (fun (k20 : Hvl) (T1 : Ty) (wf0 : (wfTy k20 T1)) (t : Tm) (wf1 : (wfTm k20 t)) IHt (T2 : Ty) (wf2 : (wfTy k20 T2)) {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfTm_pack k21 (substhvl_ty_wfTy wf k20 T1 wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d0 H0) k21 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k20 T2 wf2 (weaken_substhvl_ty H0 del)))) (fun (k20 : Hvl) (t1 : Tm) (wf0 : (wfTm k20 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (HS tm (HS ty k20)) t2)) IHt2 {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfTm_unpack k21 (IHt1 (weakenTrace d0 H0) k21 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d0 (HS tm (HS ty H0))) (HS tm (HS ty k21)) (weaken_substhvl_ty (HS tm (HS ty H0)) del)))) (fun (k20 : Hvl) (t1 : Tm) (wf0 : (wfTm k20 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k20 t2)) IHt2 {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfTm_prod k21 (IHt1 (weakenTrace d0 H0) k21 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d0 H0) k21 (weaken_substhvl_ty H0 del)))) (fun (k20 : Hvl) (t1 : Tm) (wf0 : (wfTm k20 t1)) IHt1 (p : Pat) (wf1 : (wfPat k20 p)) (t2 : Tm) (wf2 : (wfTm (appendHvl k20 (appendHvl H0 (bindPat p))) t2)) IHt2 {d0 : (Trace ty)} {k21 : Hvl} (del : (substhvl_ty k19 d0 k20 k21)) =>
    (wfTm_case k21 (IHt1 (weakenTrace d0 H0) k21 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfPat wf k20 p wf1 (weaken_substhvl_ty H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k21) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (IHt2 (weakenTrace d0 (appendHvl H0 (bindPat p))) (appendHvl k21 (appendHvl H0 (bindPat p))) (weaken_substhvl_ty (appendHvl H0 (bindPat p)) del)))))).
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : infra.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : wf.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfPat substhvl_ty_wfTm substhvl_ty_wfTy : infra.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfPat substhvl_ty_wfTm substhvl_ty_wfTy : subst.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfPat substhvl_ty_wfTm substhvl_ty_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfPat substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfPat substhvl_ty_wfTm substhvl_ty_wfTy : wf.
 Hint Constructors substhvl_tm substhvl_ty : infra.
 Hint Constructors substhvl_tm substhvl_ty : subst.
 Hint Constructors substhvl_tm substhvl_ty : subst_wf.
 Hint Constructors substhvl_tm substhvl_ty : wf.
Fixpoint subhvl_tm (k19 : Hvl) {struct k19} :
Prop :=
  match k19 with
    | (H0) => True
    | (HS a k19) => match a with
      | (tm) => (subhvl_tm k19)
      | _ => False
    end
  end.
Lemma subhvl_tm_append  :
  (forall (k19 : Hvl) (k20 : Hvl) ,
    (subhvl_tm k19) -> (subhvl_tm k20) -> (subhvl_tm (appendHvl k19 k20))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_tm_append : infra.
 Hint Resolve subhvl_tm_append : wf.
Lemma wfPat_strengthen_subhvl_tm  :
  (forall (k16 : Hvl) (k15 : Hvl) (p22 : Pat) ,
    (subhvl_tm k16) -> (wfPat (appendHvl k15 k16) (weakenPat p22 k16)) -> (wfPat k15 p22)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfTy_strengthen_subhvl_tm  :
  (forall (k18 : Hvl) (k17 : Hvl) (S6 : Ty) ,
    (subhvl_tm k18) -> (wfTy (appendHvl k17 k18) (weakenTy S6 k18)) -> (wfTy k17 S6)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H49 : (wfPat (appendHvl _ _) (weakenPat _ _)) |- _ => apply (wfPat_strengthen_subhvl_tm) in H49
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H50 : (wfTy (appendHvl _ _) (weakenTy _ _)) |- _ => apply (wfTy_strengthen_subhvl_tm) in H50
end : infra wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | evar (G2 : Env) (T : Ty)
    | etvar (G2 : Env).
  Fixpoint appendEnv (G2 : Env) (G3 : Env) :
  Env :=
    match G3 with
      | (empty) => G2
      | (evar G4 T) => (evar (appendEnv G2 G4) T)
      | (etvar G4) => (etvar (appendEnv G2 G4))
    end.
  Fixpoint domainEnv (G2 : Env) :
  Hvl :=
    match G2 with
      | (empty) => H0
      | (evar G3 T) => (HS tm (domainEnv G3))
      | (etvar G3) => (HS ty (domainEnv G3))
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
  Fixpoint shiftEnv (c0 : (Cutoff tm)) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (shiftEnv c0 G3) T)
      | (etvar G3) => (etvar (shiftEnv c0 G3))
    end.
  Fixpoint tshiftEnv (c0 : (Cutoff ty)) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (tshiftEnv c0 G3) (tshiftTy (weakenCutoffty c0 (domainEnv G3)) T))
      | (etvar G3) => (etvar (tshiftEnv c0 G3))
    end.
  Fixpoint weakenEnv (G2 : Env) (k19 : Hvl) {struct k19} :
  Env :=
    match k19 with
      | (H0) => G2
      | (HS tm k19) => (weakenEnv G2 k19)
      | (HS ty k19) => (tshiftEnv C0 (weakenEnv G2 k19))
    end.
  Fixpoint substEnv (d0 : (Trace tm)) (s8 : Tm) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (substEnv d0 s8 G3) T)
      | (etvar G3) => (etvar (substEnv d0 s8 G3))
    end.
  Fixpoint tsubstEnv (d0 : (Trace ty)) (S7 : Ty) (G2 : Env) :
  Env :=
    match G2 with
      | (empty) => empty
      | (evar G3 T) => (evar (tsubstEnv d0 S7 G3) (tsubstTy (weakenTrace d0 (domainEnv G3)) S7 T))
      | (etvar G3) => (etvar (tsubstEnv d0 S7 G3))
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c0 : (Cutoff tm)) (G2 : Env) ,
      ((domainEnv (shiftEnv c0 G2)) = (domainEnv G2))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_tshiftEnv  :
    (forall (c0 : (Cutoff ty)) (G2 : Env) ,
      ((domainEnv (tshiftEnv c0 G2)) = (domainEnv G2))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d0 : (Trace tm)) (s8 : Tm) (G2 : Env) ,
      ((domainEnv (substEnv d0 s8 G2)) = (domainEnv G2))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d0 : (Trace ty)) (S7 : Ty) (G2 : Env) ,
      ((domainEnv (tsubstEnv d0 S7 G2)) = (domainEnv G2))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shiftEnv_appendEnv  :
      (forall (c0 : (Cutoff tm)) (G2 : Env) (G3 : Env) ,
        ((shiftEnv c0 (appendEnv G2 G3)) = (appendEnv (shiftEnv c0 G2) (shiftEnv (weakenCutofftm c0 (domainEnv G2)) G3)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma tshiftEnv_appendEnv  :
      (forall (c0 : (Cutoff ty)) (G2 : Env) (G3 : Env) ,
        ((tshiftEnv c0 (appendEnv G2 G3)) = (appendEnv (tshiftEnv c0 G2) (tshiftEnv (weakenCutoffty c0 (domainEnv G2)) G3)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d0 : (Trace tm)) (s8 : Tm) (G2 : Env) (G3 : Env) ,
        ((substEnv d0 s8 (appendEnv G2 G3)) = (appendEnv (substEnv d0 s8 G2) (substEnv (weakenTrace d0 (domainEnv G2)) s8 G3)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d0 : (Trace ty)) (S7 : Ty) (G2 : Env) (G3 : Env) ,
        ((tsubstEnv d0 S7 (appendEnv G2 G3)) = (appendEnv (tsubstEnv d0 S7 G2) (tsubstEnv (weakenTrace d0 (domainEnv G2)) S7 G3)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenTy_append  :
    (forall (S7 : Ty) (k19 : Hvl) (k20 : Hvl) ,
      ((weakenTy (weakenTy S7 k19) k20) = (weakenTy S7 (appendHvl k19 k20)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenPat_append  :
    (forall (p23 : Pat) (k19 : Hvl) (k20 : Hvl) ,
      ((weakenPat (weakenPat p23 k19) k20) = (weakenPat p23 (appendHvl k19 k20)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s8 : Tm) (k19 : Hvl) (k20 : Hvl) ,
      ((weakenTm (weakenTm s8 k19) k20) = (weakenTm s8 (appendHvl k19 k20)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G2 : Env}
          (T53 : Ty) :
          (wfTy (domainEnv G2) T53) -> (lookup_evar (evar G2 T53) I0 T53)
      | lookup_evar_there_evar
          {G2 : Env} {x18 : (Index tm)}
          (T54 : Ty) (T55 : Ty) :
          (lookup_evar G2 x18 T54) -> (lookup_evar (evar G2 T55) (IS x18) T54)
      | lookup_evar_there_etvar
          {G2 : Env} {x18 : (Index tm)}
          (T54 : Ty) :
          (lookup_evar G2 x18 T54) -> (lookup_evar (etvar G2) x18 (tshiftTy C0 T54)).
    Inductive lookup_etvar : Env -> (Index ty) -> Prop :=
      | lookup_etvar_here {G2 : Env}
          : (lookup_etvar (etvar G2) I0)
      | lookup_etvar_there_evar
          {G2 : Env} {X23 : (Index ty)}
          (T54 : Ty) :
          (lookup_etvar G2 X23) -> (lookup_etvar (evar G2 T54) X23)
      | lookup_etvar_there_etvar
          {G2 : Env} {X23 : (Index ty)} :
          (lookup_etvar G2 X23) -> (lookup_etvar (etvar G2) (IS X23)).
    Lemma lookup_evar_inversion_here  :
      (forall (G2 : Env) (T54 : Ty) (T55 : Ty) ,
        (lookup_evar (evar G2 T54) I0 T55) -> (T54 = T55)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G2 : Env} {x18 : (Index tm)} ,
        (forall (T54 : Ty) ,
          (lookup_evar G2 x18 T54) -> (forall (T55 : Ty) ,
            (lookup_evar G2 x18 T55) -> (T54 = T55)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G2 : Env} {x18 : (Index tm)} (T54 : Ty) ,
        (lookup_evar G2 x18 T54) -> (wfTy (domainEnv G2) T54)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G2 : Env} (G3 : Env) {x18 : (Index tm)} (T54 : Ty) ,
        (lookup_evar G2 x18 T54) -> (lookup_evar (appendEnv G2 G3) (weakenIndextm x18 (domainEnv G3)) (weakenTy T54 (domainEnv G3)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G2 : Env} (G3 : Env) {X23 : (Index ty)} ,
        (lookup_etvar G2 X23) -> (lookup_etvar (appendEnv G2 G3) (weakenIndexty X23 (domainEnv G3)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G2 : Env} {x18 : (Index tm)} (T56 : Ty) ,
        (lookup_evar G2 x18 T56) -> (wfindex (domainEnv G2) x18)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G2 : Env} {X23 : (Index ty)} ,
        (lookup_etvar G2 X23) -> (wfindex (domainEnv G2) X23)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G2 : Env}
        {T54 : Ty} :
        (shift_evar C0 G2 (evar G2 T54))
    | shiftevar_there_evar
        {c0 : (Cutoff tm)} {G2 : Env}
        {G3 : Env} {T : Ty} :
        (shift_evar c0 G2 G3) -> (shift_evar (CS c0) (evar G2 T) (evar G3 T))
    | shiftevar_there_etvar
        {c0 : (Cutoff tm)} {G2 : Env}
        {G3 : Env} :
        (shift_evar c0 G2 G3) -> (shift_evar c0 (etvar G2) (etvar G3)).
  Lemma weaken_shift_evar  :
    (forall (G2 : Env) {c0 : (Cutoff tm)} {G3 : Env} {G4 : Env} ,
      (shift_evar c0 G3 G4) -> (shift_evar (weakenCutofftm c0 (domainEnv G2)) (appendEnv G3 G2) (appendEnv G4 G2))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G2 : Env}
        : (shift_etvar C0 G2 (etvar G2))
    | shiftetvar_there_evar
        {c0 : (Cutoff ty)} {G2 : Env}
        {G3 : Env} {T : Ty} :
        (shift_etvar c0 G2 G3) -> (shift_etvar c0 (evar G2 T) (evar G3 (tshiftTy c0 T)))
    | shiftetvar_there_etvar
        {c0 : (Cutoff ty)} {G2 : Env}
        {G3 : Env} :
        (shift_etvar c0 G2 G3) -> (shift_etvar (CS c0) (etvar G2) (etvar G3)).
  Lemma weaken_shift_etvar  :
    (forall (G2 : Env) {c0 : (Cutoff ty)} {G3 : Env} {G4 : Env} ,
      (shift_etvar c0 G3 G4) -> (shift_etvar (weakenCutoffty c0 (domainEnv G2)) (appendEnv G3 G2) (appendEnv G4 (tshiftEnv c0 G2)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_tm  :
    (forall {c0 : (Cutoff tm)} {G2 : Env} {G3 : Env} ,
      (shift_evar c0 G2 G3) -> (shifthvl_tm c0 (domainEnv G2) (domainEnv G3))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_etvar_shifthvl_ty  :
    (forall {c0 : (Cutoff ty)} {G2 : Env} {G3 : Env} ,
      (shift_etvar c0 G2 G3) -> (shifthvl_ty c0 (domainEnv G2) (domainEnv G3))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G2 : Env) (T54 : Ty) (s8 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G2 T54 s8 X0 (evar G2 T54) G2)
    | subst_evar_there_evar
        {d0 : (Trace tm)} {G3 : Env}
        {G4 : Env} (T55 : Ty) :
        (subst_evar G2 T54 s8 d0 G3 G4) -> (subst_evar G2 T54 s8 (XS tm d0) (evar G3 T55) (evar G4 T55))
    | subst_evar_there_etvar
        {d0 : (Trace tm)} {G3 : Env}
        {G4 : Env} :
        (subst_evar G2 T54 s8 d0 G3 G4) -> (subst_evar G2 T54 s8 (XS ty d0) (etvar G3) (etvar G4)).
  Lemma weaken_subst_evar {G2 : Env} (T54 : Ty) {s8 : Tm} :
    (forall (G3 : Env) {d0 : (Trace tm)} {G4 : Env} {G5 : Env} ,
      (subst_evar G2 T54 s8 d0 G4 G5) -> (subst_evar G2 T54 s8 (weakenTrace d0 (domainEnv G3)) (appendEnv G4 G3) (appendEnv G5 G3))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G2 : Env) (S7 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G2 S7 X0 (etvar G2) G2)
    | subst_etvar_there_evar
        {d0 : (Trace ty)} {G3 : Env}
        {G4 : Env} (T54 : Ty) :
        (subst_etvar G2 S7 d0 G3 G4) -> (subst_etvar G2 S7 (XS tm d0) (evar G3 T54) (evar G4 (tsubstTy d0 S7 T54)))
    | subst_etvar_there_etvar
        {d0 : (Trace ty)} {G3 : Env}
        {G4 : Env} :
        (subst_etvar G2 S7 d0 G3 G4) -> (subst_etvar G2 S7 (XS ty d0) (etvar G3) (etvar G4)).
  Lemma weaken_subst_etvar {G2 : Env} {S7 : Ty} :
    (forall (G3 : Env) {d0 : (Trace ty)} {G4 : Env} {G5 : Env} ,
      (subst_etvar G2 S7 d0 G4 G5) -> (subst_etvar G2 S7 (weakenTrace d0 (domainEnv G3)) (appendEnv G4 G3) (appendEnv G5 (tsubstEnv d0 S7 G3)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G2 : Env} {s8 : Tm} (T54 : Ty) :
    (forall {d0 : (Trace tm)} {G3 : Env} {G4 : Env} ,
      (subst_evar G2 T54 s8 d0 G3 G4) -> (substhvl_tm (domainEnv G2) d0 (domainEnv G3) (domainEnv G4))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G2 : Env} {S7 : Ty} :
    (forall {d0 : (Trace ty)} {G3 : Env} {G4 : Env} ,
      (subst_etvar G2 S7 d0 G3 G4) -> (substhvl_ty (domainEnv G2) d0 (domainEnv G3) (domainEnv G4))).
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
 Hint Constructors lookup_evar lookup_etvar : infra.
 Hint Constructors lookup_evar lookup_etvar : lookup.
 Hint Constructors lookup_evar lookup_etvar : shift.
 Hint Constructors lookup_evar lookup_etvar : subst.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : infra.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : lookup.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : shift.
 Hint Resolve weaken_lookup_evar weaken_lookup_etvar : weaken.
Lemma weaken_lookup_evar_here  :
  (forall {G2 : Env} (G3 : Env) {T54 : Ty} (wf : (wfTy (domainEnv G2) T54)) ,
    (lookup_evar (appendEnv (evar G2 T54) G3) (weakenIndextm I0 (domainEnv G3)) (weakenTy T54 (domainEnv G3)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G2 : Env} (G3 : Env) ,
    (lookup_etvar (appendEnv (etvar G2) G3) (weakenIndexty I0 (domainEnv G3)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfPat wfTm wfTy : infra.
 Hint Constructors wfPat wfTm wfTy : wf.
 Hint Extern 10 ((wfPat _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H49 : (wfTy _ (tvar _)) |- _ => inversion H49; subst; clear H49
  | H49 : (wfTy _ (tarr _ _)) |- _ => inversion H49; subst; clear H49
  | H49 : (wfTy _ (tall _)) |- _ => inversion H49; subst; clear H49
  | H49 : (wfTy _ (texist _)) |- _ => inversion H49; subst; clear H49
  | H49 : (wfTy _ (tprod _ _)) |- _ => inversion H49; subst; clear H49
end : infra wf.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H49 : (wfPat _ (pvar _)) |- _ => inversion H49; subst; clear H49
  | H49 : (wfPat _ (pprod _ _)) |- _ => inversion H49; subst; clear H49
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H49 : (wfTm _ (var _)) |- _ => inversion H49; subst; clear H49
  | H49 : (wfTm _ (abs _ _)) |- _ => inversion H49; subst; clear H49
  | H49 : (wfTm _ (app _ _)) |- _ => inversion H49; subst; clear H49
  | H49 : (wfTm _ (tabs _)) |- _ => inversion H49; subst; clear H49
  | H49 : (wfTm _ (tapp _ _)) |- _ => inversion H49; subst; clear H49
  | H49 : (wfTm _ (pack _ _ _)) |- _ => inversion H49; subst; clear H49
  | H49 : (wfTm _ (unpack _ _)) |- _ => inversion H49; subst; clear H49
  | H49 : (wfTm _ (prod _ _)) |- _ => inversion H49; subst; clear H49
  | H49 : (wfTm _ (case _ _ _)) |- _ => inversion H49; subst; clear H49
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
 Hint Resolve shift_evar_shifthvl_tm shift_etvar_shifthvl_ty : infra.
 Hint Resolve shift_evar_shifthvl_tm shift_etvar_shifthvl_ty : shift.
 Hint Resolve shift_evar_shifthvl_tm shift_etvar_shifthvl_ty : shift_wf.
 Hint Resolve shift_evar_shifthvl_tm shift_etvar_shifthvl_ty : wf.
 Hint Constructors subst_evar subst_etvar : infra.
 Hint Constructors subst_evar subst_etvar : subst.
 Hint Resolve weaken_subst_evar weaken_subst_etvar : infra.
 Hint Resolve weaken_subst_evar weaken_subst_etvar : subst.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : infra.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : subst.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : subst_wf.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : wf.
 Hint Resolve subst_evar_substhvl_tm subst_etvar_substhvl_ty : substenv_substhvl.
Lemma shift_evar_lookup_evar  :
  (forall {c0 : (Cutoff tm)} {G2 : Env} {G3 : Env} (ins : (shift_evar c0 G2 G3)) {x18 : (Index tm)} {T54 : Ty} ,
    (lookup_evar G2 x18 T54) -> (lookup_evar G3 (shiftIndex c0 x18) T54)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c0 : (Cutoff tm)} {G2 : Env} {G3 : Env} (ins : (shift_evar c0 G2 G3)) {X23 : (Index ty)} ,
    (lookup_etvar G2 X23) -> (lookup_etvar G3 X23)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c0 : (Cutoff ty)} {G2 : Env} {G3 : Env} (ins : (shift_etvar c0 G2 G3)) {x18 : (Index tm)} {T54 : Ty} ,
    (lookup_evar G2 x18 T54) -> (lookup_evar G3 x18 (tshiftTy c0 T54))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c0 : (Cutoff ty)} {G2 : Env} {G3 : Env} (ins : (shift_etvar c0 G2 G3)) {X23 : (Index ty)} ,
    (lookup_etvar G2 X23) -> (lookup_etvar G3 (tshiftIndex c0 X23))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G2 : Env} (T55 : Ty) {s8 : Tm} :
  (forall {d0 : (Trace tm)} {G3 : Env} {G4 : Env} (sub : (subst_evar G2 T55 s8 d0 G3 G4)) {X23 : (Index ty)} ,
    (lookup_etvar G3 X23) -> (lookup_etvar G4 X23)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G2 : Env} {S7 : Ty} (wf : (wfTy (domainEnv G2) S7)) :
  (forall {d0 : (Trace ty)} {G3 : Env} {G4 : Env} (sub : (subst_etvar G2 S7 d0 G3 G4)) {x18 : (Index tm)} (T55 : Ty) ,
    (lookup_evar G3 x18 T55) -> (lookup_evar G4 x18 (tsubstTy d0 S7 T55))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (tvar X23) => 1
    | (tarr T53 T54) => (plus 1 (plus (size_Ty T53) (size_Ty T54)))
    | (tall T55) => (plus 1 (size_Ty T55))
    | (texist T56) => (plus 1 (size_Ty T56))
    | (tprod T57 T58) => (plus 1 (plus (size_Ty T57) (size_Ty T58)))
  end.
Fixpoint size_Pat (p18 : Pat) {struct p18} :
nat :=
  match p18 with
    | (pvar T53) => (plus 1 (size_Ty T53))
    | (pprod p19 p20) => (plus 1 (plus (size_Pat p19) (size_Pat p20)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x18) => 1
    | (abs T53 t36) => (plus 1 (plus (size_Ty T53) (size_Tm t36)))
    | (app t37 t38) => (plus 1 (plus (size_Tm t37) (size_Tm t38)))
    | (tabs t39) => (plus 1 (size_Tm t39))
    | (tapp t40 T54) => (plus 1 (plus (size_Tm t40) (size_Ty T54)))
    | (pack T55 t41 T56) => (plus 1 (plus (size_Ty T55) (plus (size_Tm t41) (size_Ty T56))))
    | (unpack t42 t43) => (plus 1 (plus (size_Tm t42) (size_Tm t43)))
    | (prod t44 t45) => (plus 1 (plus (size_Tm t44) (size_Tm t45)))
    | (case t46 p18 t47) => (plus 1 (plus (size_Tm t46) (plus (size_Pat p18) (size_Tm t47))))
  end.
Fixpoint tshift_size_Ty (S1 : Ty) (c0 : (Cutoff ty)) {struct S1} :
((size_Ty (tshiftTy c0 S1)) = (size_Ty S1)) :=
  match S1 return ((size_Ty (tshiftTy c0 S1)) = (size_Ty S1)) with
    | (tvar _) => eq_refl
    | (tarr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c0) (tshift_size_Ty T2 c0)))
    | (tall T) => (f_equal2 plus eq_refl (tshift_size_Ty T (CS c0)))
    | (texist T) => (f_equal2 plus eq_refl (tshift_size_Ty T (CS c0)))
    | (tprod T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c0) (tshift_size_Ty T2 c0)))
  end.
Fixpoint tshift_size_Pat (p20 : Pat) (c0 : (Cutoff ty)) {struct p20} :
((size_Pat (tshiftPat c0 p20)) = (size_Pat p20)) :=
  match p20 return ((size_Pat (tshiftPat c0 p20)) = (size_Pat p20)) with
    | (pvar T) => (f_equal2 plus eq_refl (tshift_size_Ty T c0))
    | (pprod p1 p2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Pat p1 c0) (tshift_size_Pat p2 (weakenCutoffty c0 (appendHvl H0 (bindPat p1))))))
  end.
Fixpoint shift_size_Tm (s : Tm) (c0 : (Cutoff tm)) {struct s} :
((size_Tm (shiftTm c0 s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c0 s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c0))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c0) (shift_size_Tm t2 c0)))
    | (tabs t) => (f_equal2 plus eq_refl (shift_size_Tm t c0))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c0) eq_refl))
    | (pack T1 t T2) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c0) eq_refl)))
    | (unpack t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c0) (shift_size_Tm t2 (CS c0))))
    | (prod t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c0) (shift_size_Tm t2 c0)))
    | (case t1 p t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c0) (f_equal2 plus eq_refl (shift_size_Tm t2 (weakenCutofftm c0 (appendHvl H0 (bindPat p)))))))
  end.
Fixpoint tshift_size_Tm (s : Tm) (c0 : (Cutoff ty)) {struct s} :
((size_Tm (tshiftTm c0 s)) = (size_Tm s)) :=
  match s return ((size_Tm (tshiftTm c0 s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c0) (tshift_size_Tm t c0)))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c0) (tshift_size_Tm t2 c0)))
    | (tabs t) => (f_equal2 plus eq_refl (tshift_size_Tm t (CS c0)))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t c0) (tshift_size_Ty T c0)))
    | (pack T1 t T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c0) (f_equal2 plus (tshift_size_Tm t c0) (tshift_size_Ty T2 c0))))
    | (unpack t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c0) (tshift_size_Tm t2 (CS c0))))
    | (prod t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c0) (tshift_size_Tm t2 c0)))
    | (case t1 p t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c0) (f_equal2 plus (tshift_size_Pat p c0) (tshift_size_Tm t2 (weakenCutoffty c0 (appendHvl H0 (bindPat p)))))))
  end.
 Hint Rewrite tshift_size_Pat shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite tshift_size_Pat shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Pat  :
  (forall (k : Hvl) (p20 : Pat) ,
    ((size_Pat (weakenPat p20 k)) = (size_Pat p20))).
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
Inductive PTyping (G2 : Env) : Pat -> Ty -> Env -> Prop :=
  | P_Var (T : Ty)
      (H32 : (wfTy (domainEnv G2) T))
      :
      (PTyping G2 (pvar T) T (evar empty T))
  | P_Prod (T1 : Ty) (T2 : Ty)
      (p1 : Pat) (p2 : Pat) (G : Env)
      (G0 : Env)
      (wtp1 : (PTyping G2 p1 T1 G))
      (wtp2 : (PTyping (appendEnv G2 (appendEnv empty G)) p2 (weakenTy T2 (appendHvl H0 (bindPat p1))) G0))
      (H34 : (wfTy (domainEnv G2) T2))
      :
      (PTyping G2 (pprod p1 p2) (tprod T1 T2) (appendEnv (appendEnv empty G) G0)).
Inductive Typing (G2 : Env) : Tm -> Ty -> Prop :=
  | T_Var (T : Ty)
      (x : (Index tm))
      (lk : (lookup_evar G2 x T))
      (H32 : (wfTy (domainEnv G2) T))
      (H33 : (wfindex (domainEnv G2) x))
      : (Typing G2 (var x) T)
  | T_Abs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm : (Typing (evar G2 T1) t (weakenTy T2 (HS tm H0))))
      (H34 : (wfTy (domainEnv G2) T1))
      (H35 : (wfTy (domainEnv G2) T2))
      :
      (Typing G2 (abs T1 t) (tarr T1 T2))
  | T_App (T11 : Ty) (T12 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm0 : (Typing G2 t1 (tarr T11 T12)))
      (jm1 : (Typing G2 t2 T11)) :
      (Typing G2 (app t1 t2) T12)
  | T_Tabs (T : Ty) (t : Tm)
      (jm2 : (Typing (etvar G2) t T))
      : (Typing G2 (tabs t) (tall T))
  | T_Tapp (T12 : Ty) (T2 : Ty)
      (t1 : Tm)
      (jm3 : (Typing G2 t1 (tall T12)))
      (H44 : (wfTy (domainEnv G2) T2))
      :
      (Typing G2 (tapp t1 T2) (tsubstTy X0 T2 T12))
  | T_Pack (T2 : Ty) (U : Ty)
      (t2 : Tm)
      (jm4 : (Typing G2 t2 (tsubstTy X0 U T2)))
      (H46 : (wfTy (HS ty (domainEnv G2)) T2))
      (H47 : (wfTy (domainEnv G2) U))
      :
      (Typing G2 (pack U t2 (texist T2)) (texist T2))
  | T_Unpack (T12 : Ty) (T2 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm5 : (Typing G2 t1 (texist T12)))
      (jm6 : (Typing (evar (etvar G2) T12) t2 (weakenTy T2 (HS tm (HS ty H0)))))
      (H50 : (wfTy (domainEnv G2) T2))
      : (Typing G2 (unpack t1 t2) T2)
  | T_Prod (T1 : Ty) (T2 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm7 : (Typing G2 t1 T1))
      (jm8 : (Typing G2 t2 T2)) :
      (Typing G2 (prod t1 t2) (tprod T1 T2))
  | T_Case (T1 : Ty) (T2 : Ty)
      (p : Pat) (t1 : Tm) (t2 : Tm)
      (G1 : Env)
      (jm9 : (Typing G2 t1 T1))
      (wtp : (PTyping G2 p T1 G1))
      (jm10 : (Typing (appendEnv G2 (appendEnv empty G1)) t2 (weakenTy T2 (appendHvl H0 (bindPat p)))))
      (H58 : (wfTy (domainEnv G2) T2))
      : (Typing G2 (case t1 p t2) T2).
Fixpoint domain_PTyping_bindPat (G4 : Env) (p25 : Pat) (T59 : Ty) (G5 : Env) (wtp8 : (PTyping G4 p25 T59 G5)) :
((domainEnv G5) = (bindPat p25)) :=
  match wtp8 in (PTyping _ p25 T59 G5) return ((domainEnv G5) = (bindPat p25)) with
    | (P_Var T56 H51) => (eq_refl (HS tm H0))
    | (P_Prod T57 T58 p23 p24 G2 G3 wtp6 wtp7 H53) => (eq_trans (domainEnv_appendEnv (appendEnv empty G2) G3) (f_equal2 appendHvl (eq_trans (domainEnv_appendEnv empty G2) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G4 p23 T57 G2 wtp6))) (domain_PTyping_bindPat (appendEnv G4 (appendEnv empty G2)) p24 (weakenTy T58 (appendHvl H0 (bindPat p23))) G3 wtp7)))
  end.
Lemma PTyping_cast  :
  (forall (G2 : Env) (p23 : Pat) (T56 : Ty) (G4 : Env) (G3 : Env) (p24 : Pat) (T57 : Ty) (G5 : Env) ,
    (G2 = G3) -> (p23 = p24) -> (T56 = T57) -> (G4 = G5) -> (PTyping G2 p23 T56 G4) -> (PTyping G3 p24 T57 G5)).
Proof.
  congruence .
Qed.
Lemma Typing_cast  :
  (forall (G2 : Env) (t36 : Tm) (T56 : Ty) (G3 : Env) (t37 : Tm) (T57 : Ty) ,
    (G2 = G3) -> (t36 = t37) -> (T56 = T57) -> (Typing G2 t36 T56) -> (Typing G3 t37 T57)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_PTyping (G9 : Env) (p26 : Pat) (T63 : Ty) (G10 : Env) (wtp9 : (PTyping G9 p26 T63 G10)) :
(forall (c0 : (Cutoff tm)) (G11 : Env) (H64 : (shift_evar c0 G9 G11)) ,
  (PTyping G11 p26 T63 G10)) :=
  match wtp9 in (PTyping _ p26 T63 G10) return (forall (c0 : (Cutoff tm)) (G11 : Env) (H64 : (shift_evar c0 G9 G11)) ,
    (PTyping G11 p26 T63 G10)) with
    | (P_Var T60 H57) => (fun (c0 : (Cutoff tm)) (G11 : Env) (H64 : (shift_evar c0 G9 G11)) =>
      (P_Var G11 T60 (shift_wfTy _ _ H57 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H64)))))
    | (P_Prod T61 T62 p24 p25 G7 G8 wtp7 wtp8 H59) => (fun (c0 : (Cutoff tm)) (G11 : Env) (H64 : (shift_evar c0 G9 G11)) =>
      (PTyping_cast G11 _ _ _ G11 (pprod p24 p25) (tprod T61 T62) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym eq_refl) eq_refl) (eq_sym eq_refl)) (P_Prod G11 T61 T62 p24 p25 G7 G8 (shift_evar_PTyping G9 p24 T61 G7 wtp7 c0 G11 (weaken_shift_evar empty H64)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) eq_refl (eq_trans eq_refl (eq_sym eq_refl)) eq_refl (shift_evar_PTyping (appendEnv G9 (appendEnv empty G7)) p25 (weakenTy T62 (appendHvl H0 (bindPat p24))) G8 wtp8 (weakenCutofftm c0 (domainEnv (appendEnv empty G7))) (appendEnv G11 (appendEnv empty G7)) (weaken_shift_evar (appendEnv empty G7) H64))) (shift_wfTy _ _ H59 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H64))))))
  end.
Fixpoint shift_etvar_PTyping (G9 : Env) (p26 : Pat) (T63 : Ty) (G10 : Env) (wtp9 : (PTyping G9 p26 T63 G10)) :
(forall (c0 : (Cutoff ty)) (G11 : Env) (H64 : (shift_etvar c0 G9 G11)) ,
  (PTyping G11 (tshiftPat c0 p26) (tshiftTy c0 T63) (tshiftEnv c0 G10))) :=
  match wtp9 in (PTyping _ p26 T63 G10) return (forall (c0 : (Cutoff ty)) (G11 : Env) (H64 : (shift_etvar c0 G9 G11)) ,
    (PTyping G11 (tshiftPat c0 p26) (tshiftTy c0 T63) (tshiftEnv c0 G10))) with
    | (P_Var T60 H57) => (fun (c0 : (Cutoff ty)) (G11 : Env) (H64 : (shift_etvar c0 G9 G11)) =>
      (P_Var G11 (tshiftTy c0 T60) (tshift_wfTy _ _ H57 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H64)))))
    | (P_Prod T61 T62 p24 p25 G7 G8 wtp7 wtp8 H59) => (fun (c0 : (Cutoff ty)) (G11 : Env) (H64 : (shift_etvar c0 G9 G11)) =>
      (PTyping_cast G11 _ _ _ G11 (tshiftPat c0 (pprod p24 p25)) (tshiftTy c0 (tprod T61 T62)) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym (tshiftEnv_appendEnv c0 empty G7)) eq_refl) (eq_sym (tshiftEnv_appendEnv c0 (appendEnv empty G7) G8))) (P_Prod G11 (tshiftTy c0 T61) (tshiftTy c0 T62) (tshiftPat c0 p24) (tshiftPat (weakenCutoffty c0 (appendHvl H0 (bindPat p24))) p25) (tshiftEnv c0 G7) (tshiftEnv (weakenCutoffty c0 (domainEnv (appendEnv empty G7))) G8) (shift_etvar_PTyping G9 p24 T61 G7 wtp7 c0 G11 (weaken_shift_etvar empty H64)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl (tshiftEnv_appendEnv c0 empty G7)) (f_equal2 tshiftPat (f_equal2 weakenCutoffty eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G9 p24 T61 G7 wtp7)))) eq_refl) (eq_trans (f_equal2 tshiftTy (f_equal2 weakenCutoffty eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G9 p24 T61 G7 wtp7)))) eq_refl) (eq_trans (eq_sym (weakenTy_tshiftTy (appendHvl H0 (bindPat p24)) c0 T62)) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))))) eq_refl (shift_etvar_PTyping (appendEnv G9 (appendEnv empty G7)) p25 (weakenTy T62 (appendHvl H0 (bindPat p24))) G8 wtp8 (weakenCutoffty c0 (domainEnv (appendEnv empty G7))) (appendEnv G11 (tshiftEnv c0 (appendEnv empty G7))) (weaken_shift_etvar (appendEnv empty G7) H64))) (tshift_wfTy _ _ H59 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H64))))))
  end.
Fixpoint shift_evar_Typing (G8 : Env) (t40 : Tm) (T65 : Ty) (jm24 : (Typing G8 t40 T65)) :
(forall (c0 : (Cutoff tm)) (G9 : Env) (H89 : (shift_evar c0 G8 G9)) ,
  (Typing G9 (shiftTm c0 t40) T65)) :=
  match jm24 in (Typing _ t40 T65) return (forall (c0 : (Cutoff tm)) (G9 : Env) (H89 : (shift_evar c0 G8 G9)) ,
    (Typing G9 (shiftTm c0 t40) T65)) with
    | (T_Var T60 x20 lk0 H57 H58) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H89 : (shift_evar c0 G8 G9)) =>
      (T_Var G9 T60 (shiftIndex c0 x20) (shift_evar_lookup_evar H89 lk0) (shift_wfTy _ _ H57 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H89))) (shift_wfindex_tm _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H89)) _ H58)))
    | (T_Abs T61 T64 t37 jm12 H59 H60) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H89 : (shift_evar c0 G8 G9)) =>
      (T_Abs G9 T61 T64 (shiftTm (CS c0) t37) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar G8 T61) t37 (weakenTy T64 (HS tm H0)) jm12 (CS c0) (evar G9 T61) (weaken_shift_evar (evar empty T61) H89))) (shift_wfTy _ _ H59 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H89))) (shift_wfTy _ _ H60 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H89)))))
    | (T_App T62 T63 t38 t39 jm13 jm14) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H89 : (shift_evar c0 G8 G9)) =>
      (T_App G9 T62 T63 (shiftTm c0 t38) (shiftTm c0 t39) (shift_evar_Typing G8 t38 (tarr T62 T63) jm13 c0 G9 (weaken_shift_evar empty H89)) (shift_evar_Typing G8 t39 T62 jm14 c0 G9 (weaken_shift_evar empty H89))))
    | (T_Tabs T60 t37 jm16) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H89 : (shift_evar c0 G8 G9)) =>
      (T_Tabs G9 T60 (shiftTm c0 t37) (shift_evar_Typing (etvar G8) t37 T60 jm16 c0 (etvar G9) (weaken_shift_evar (etvar empty) H89))))
    | (T_Tapp T63 T64 t38 jm17 H69) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H89 : (shift_evar c0 G8 G9)) =>
      (T_Tapp G9 T63 T64 (shiftTm c0 t38) (shift_evar_Typing G8 t38 (tall T63) jm17 c0 G9 (weaken_shift_evar empty H89)) (shift_wfTy _ _ H69 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H89)))))
    | (T_Pack T64 U1 t39 jm18 H71 H72) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H89 : (shift_evar c0 G8 G9)) =>
      (T_Pack G9 T64 U1 (shiftTm c0 t39) (shift_evar_Typing G8 t39 (tsubstTy X0 U1 T64) jm18 c0 G9 (weaken_shift_evar empty H89)) (shift_wfTy _ _ H71 _ _ (weaken_shifthvl_tm (HS ty H0) (shift_evar_shifthvl_tm H89))) (shift_wfTy _ _ H72 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H89)))))
    | (T_Unpack T63 T64 t38 t39 jm19 jm20 H75) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H89 : (shift_evar c0 G8 G9)) =>
      (T_Unpack G9 T63 T64 (shiftTm c0 t38) (shiftTm (CS c0) t39) (shift_evar_Typing G8 t38 (texist T63) jm19 c0 G9 (weaken_shift_evar empty H89)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar (etvar G8) T63) t39 (weakenTy T64 (HS tm (HS ty H0))) jm20 (CS c0) (evar (etvar G9) T63) (weaken_shift_evar (evar (etvar empty) T63) H89))) (shift_wfTy _ _ H75 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H89)))))
    | (T_Prod T61 T64 t38 t39 jm21 jm22) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H89 : (shift_evar c0 G8 G9)) =>
      (T_Prod G9 T61 T64 (shiftTm c0 t38) (shiftTm c0 t39) (shift_evar_Typing G8 t38 T61 jm21 c0 G9 (weaken_shift_evar empty H89)) (shift_evar_Typing G8 t39 T64 jm22 c0 G9 (weaken_shift_evar empty H89))))
    | (T_Case T61 T64 p24 t38 t39 G7 jm23 wtp7 jm15 H83) => (fun (c0 : (Cutoff tm)) (G9 : Env) (H89 : (shift_evar c0 G8 G9)) =>
      (T_Case G9 T61 T64 p24 (shiftTm c0 t38) (shiftTm (weakenCutofftm c0 (appendHvl H0 (bindPat p24))) t39) G7 (shift_evar_Typing G8 t38 T61 jm23 c0 G9 (weaken_shift_evar empty H89)) (shift_evar_PTyping G8 p24 T61 G7 wtp7 c0 G9 (weaken_shift_evar empty H89)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) (f_equal2 shiftTm (f_equal2 weakenCutofftm eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G8 p24 T61 G7 wtp7)))) eq_refl) (eq_trans eq_refl (eq_sym eq_refl)) (shift_evar_Typing (appendEnv G8 (appendEnv empty G7)) t39 (weakenTy T64 (appendHvl H0 (bindPat p24))) jm15 (weakenCutofftm c0 (domainEnv (appendEnv empty G7))) (appendEnv G9 (appendEnv empty G7)) (weaken_shift_evar (appendEnv empty G7) H89))) (shift_wfTy _ _ H83 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H89)))))
  end.
Fixpoint shift_etvar_Typing (G8 : Env) (t40 : Tm) (T65 : Ty) (jm24 : (Typing G8 t40 T65)) :
(forall (c0 : (Cutoff ty)) (G9 : Env) (H89 : (shift_etvar c0 G8 G9)) ,
  (Typing G9 (tshiftTm c0 t40) (tshiftTy c0 T65))) :=
  match jm24 in (Typing _ t40 T65) return (forall (c0 : (Cutoff ty)) (G9 : Env) (H89 : (shift_etvar c0 G8 G9)) ,
    (Typing G9 (tshiftTm c0 t40) (tshiftTy c0 T65))) with
    | (T_Var T60 x20 lk0 H57 H58) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H89 : (shift_etvar c0 G8 G9)) =>
      (T_Var G9 (tshiftTy c0 T60) x20 (shift_etvar_lookup_evar H89 lk0) (tshift_wfTy _ _ H57 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H89))) (tshift_wfindex_tm _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H89)) _ H58)))
    | (T_Abs T61 T64 t37 jm12 H59 H60) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H89 : (shift_etvar c0 G8 G9)) =>
      (T_Abs G9 (tshiftTy c0 T61) (tshiftTy c0 T64) (tshiftTm c0 t37) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tshiftTy (HS tm H0) c0 T64)) (shift_etvar_Typing (evar G8 T61) t37 (weakenTy T64 (HS tm H0)) jm12 c0 (evar G9 (tshiftTy c0 T61)) (weaken_shift_etvar (evar empty T61) H89))) (tshift_wfTy _ _ H59 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H89))) (tshift_wfTy _ _ H60 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H89)))))
    | (T_App T62 T63 t38 t39 jm13 jm14) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H89 : (shift_etvar c0 G8 G9)) =>
      (T_App G9 (tshiftTy c0 T62) (tshiftTy c0 T63) (tshiftTm c0 t38) (tshiftTm c0 t39) (shift_etvar_Typing G8 t38 (tarr T62 T63) jm13 c0 G9 (weaken_shift_etvar empty H89)) (shift_etvar_Typing G8 t39 T62 jm14 c0 G9 (weaken_shift_etvar empty H89))))
    | (T_Tabs T60 t37 jm16) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H89 : (shift_etvar c0 G8 G9)) =>
      (T_Tabs G9 (tshiftTy (CS c0) T60) (tshiftTm (CS c0) t37) (shift_etvar_Typing (etvar G8) t37 T60 jm16 (CS c0) (etvar G9) (weaken_shift_etvar (etvar empty) H89))))
    | (T_Tapp T63 T64 t38 jm17 H69) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H89 : (shift_etvar c0 G8 G9)) =>
      (Typing_cast G9 _ _ G9 (tshiftTm c0 (tapp t38 T64)) (tshiftTy c0 (tsubstTy X0 T64 T63)) eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T63 c0 T64)) (T_Tapp G9 (tshiftTy (CS c0) T63) (tshiftTy c0 T64) (tshiftTm c0 t38) (shift_etvar_Typing G8 t38 (tall T63) jm17 c0 G9 (weaken_shift_etvar empty H89)) (tshift_wfTy _ _ H69 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H89))))))
    | (T_Pack T64 U1 t39 jm18 H71 H72) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H89 : (shift_etvar c0 G8 G9)) =>
      (T_Pack G9 (tshiftTy (CS c0) T64) (tshiftTy c0 U1) (tshiftTm c0 t39) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (tshiftTy_tsubstTy0_comm T64 c0 U1) (shift_etvar_Typing G8 t39 (tsubstTy X0 U1 T64) jm18 c0 G9 (weaken_shift_etvar empty H89))) (tshift_wfTy _ _ H71 _ _ (weaken_shifthvl_ty (HS ty H0) (shift_etvar_shifthvl_ty H89))) (tshift_wfTy _ _ H72 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H89)))))
    | (T_Unpack T63 T64 t38 t39 jm19 jm20 H75) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H89 : (shift_etvar c0 G8 G9)) =>
      (T_Unpack G9 (tshiftTy (CS c0) T63) (tshiftTy c0 T64) (tshiftTm c0 t38) (tshiftTm (CS c0) t39) (shift_etvar_Typing G8 t38 (texist T63) jm19 c0 G9 (weaken_shift_etvar empty H89)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tshiftTy (HS tm (HS ty H0)) c0 T64)) (shift_etvar_Typing (evar (etvar G8) T63) t39 (weakenTy T64 (HS tm (HS ty H0))) jm20 (CS c0) (evar (etvar G9) (tshiftTy (CS c0) T63)) (weaken_shift_etvar (evar (etvar empty) T63) H89))) (tshift_wfTy _ _ H75 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H89)))))
    | (T_Prod T61 T64 t38 t39 jm21 jm22) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H89 : (shift_etvar c0 G8 G9)) =>
      (T_Prod G9 (tshiftTy c0 T61) (tshiftTy c0 T64) (tshiftTm c0 t38) (tshiftTm c0 t39) (shift_etvar_Typing G8 t38 T61 jm21 c0 G9 (weaken_shift_etvar empty H89)) (shift_etvar_Typing G8 t39 T64 jm22 c0 G9 (weaken_shift_etvar empty H89))))
    | (T_Case T61 T64 p24 t38 t39 G7 jm23 wtp7 jm15 H83) => (fun (c0 : (Cutoff ty)) (G9 : Env) (H89 : (shift_etvar c0 G8 G9)) =>
      (T_Case G9 (tshiftTy c0 T61) (tshiftTy c0 T64) (tshiftPat c0 p24) (tshiftTm c0 t38) (tshiftTm (weakenCutoffty c0 (appendHvl H0 (bindPat p24))) t39) (tshiftEnv c0 G7) (shift_etvar_Typing G8 t38 T61 jm23 c0 G9 (weaken_shift_etvar empty H89)) (shift_etvar_PTyping G8 p24 T61 G7 wtp7 c0 G9 (weaken_shift_etvar empty H89)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl (tshiftEnv_appendEnv c0 empty G7)) (f_equal2 tshiftTm (f_equal2 weakenCutoffty eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G8 p24 T61 G7 wtp7)))) eq_refl) (eq_trans (f_equal2 tshiftTy (f_equal2 weakenCutoffty eq_refl (eq_trans (domainEnv_appendEnv empty G7) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G8 p24 T61 G7 wtp7)))) eq_refl) (eq_trans (eq_sym (weakenTy_tshiftTy (appendHvl H0 (bindPat p24)) c0 T64)) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))))) (shift_etvar_Typing (appendEnv G8 (appendEnv empty G7)) t39 (weakenTy T64 (appendHvl H0 (bindPat p24))) jm15 (weakenCutoffty c0 (domainEnv (appendEnv empty G7))) (appendEnv G9 (tshiftEnv c0 (appendEnv empty G7))) (weaken_shift_etvar (appendEnv empty G7) H89))) (tshift_wfTy _ _ H83 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H89)))))
  end.
 Hint Resolve shift_evar_PTyping shift_etvar_PTyping shift_evar_Typing shift_etvar_Typing : infra.
 Hint Resolve shift_evar_PTyping shift_etvar_PTyping shift_evar_Typing shift_etvar_Typing : shift.
Fixpoint weaken_PTyping (G2 : Env) :
(forall (G3 : Env) (p23 : Pat) (T56 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p23 T56 G4)) ,
  (PTyping (appendEnv G3 G2) (weakenPat p23 (domainEnv G2)) (weakenTy T56 (domainEnv G2)) (weakenEnv G4 (domainEnv G2)))) :=
  match G2 return (forall (G3 : Env) (p23 : Pat) (T56 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p23 T56 G4)) ,
    (PTyping (appendEnv G3 G2) (weakenPat p23 (domainEnv G2)) (weakenTy T56 (domainEnv G2)) (weakenEnv G4 (domainEnv G2)))) with
    | (empty) => (fun (G3 : Env) (p23 : Pat) (T56 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p23 T56 G4)) =>
      wtp6)
    | (evar G2 T57) => (fun (G3 : Env) (p23 : Pat) (T56 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p23 T56 G4)) =>
      (shift_evar_PTyping (appendEnv G3 G2) (weakenPat p23 (domainEnv G2)) (weakenTy T56 (domainEnv G2)) (weakenEnv G4 (domainEnv G2)) (weaken_PTyping G2 G3 p23 T56 G4 wtp6) C0 (evar (appendEnv G3 G2) T57) shift_evar_here))
    | (etvar G2) => (fun (G3 : Env) (p23 : Pat) (T56 : Ty) (G4 : Env) (wtp6 : (PTyping G3 p23 T56 G4)) =>
      (shift_etvar_PTyping (appendEnv G3 G2) (weakenPat p23 (domainEnv G2)) (weakenTy T56 (domainEnv G2)) (weakenEnv G4 (domainEnv G2)) (weaken_PTyping G2 G3 p23 T56 G4 wtp6) C0 (etvar (appendEnv G3 G2)) shift_etvar_here))
  end.
Fixpoint weaken_Typing (G5 : Env) :
(forall (G6 : Env) (t36 : Tm) (T58 : Ty) (jm11 : (Typing G6 t36 T58)) ,
  (Typing (appendEnv G6 G5) (weakenTm t36 (domainEnv G5)) (weakenTy T58 (domainEnv G5)))) :=
  match G5 return (forall (G6 : Env) (t36 : Tm) (T58 : Ty) (jm11 : (Typing G6 t36 T58)) ,
    (Typing (appendEnv G6 G5) (weakenTm t36 (domainEnv G5)) (weakenTy T58 (domainEnv G5)))) with
    | (empty) => (fun (G6 : Env) (t36 : Tm) (T58 : Ty) (jm11 : (Typing G6 t36 T58)) =>
      jm11)
    | (evar G5 T59) => (fun (G6 : Env) (t36 : Tm) (T58 : Ty) (jm11 : (Typing G6 t36 T58)) =>
      (shift_evar_Typing (appendEnv G6 G5) (weakenTm t36 (domainEnv G5)) (weakenTy T58 (domainEnv G5)) (weaken_Typing G5 G6 t36 T58 jm11) C0 (evar (appendEnv G6 G5) T59) shift_evar_here))
    | (etvar G5) => (fun (G6 : Env) (t36 : Tm) (T58 : Ty) (jm11 : (Typing G6 t36 T58)) =>
      (shift_etvar_Typing (appendEnv G6 G5) (weakenTm t36 (domainEnv G5)) (weakenTy T58 (domainEnv G5)) (weaken_Typing G5 G6 t36 T58 jm11) C0 (etvar (appendEnv G6 G5)) shift_etvar_here))
  end.
Fixpoint PTyping_wf_0 (G2 : Env) (p24 : Pat) (T60 : Ty) (G7 : Env) (wtp7 : (PTyping G2 p24 T60 G7)) {struct wtp7} :
(wfPat (domainEnv G2) p24) :=
  match wtp7 in (PTyping _ p24 T60 G7) return (wfPat (domainEnv G2) p24) with
    | (P_Var T H32) => (wfPat_pvar (domainEnv G2) H32)
    | (P_Prod T1 T2 p1 p2 G G0 wtp1 wtp2 H34) => (wfPat_pprod (domainEnv G2) (PTyping_wf_0 G2 p1 T1 G wtp1) (wfPat_cast _ _ _ _ (eq_trans (domainEnv_appendEnv G2 (appendEnv empty G)) (f_equal2 appendHvl (eq_refl (domainEnv G2)) (eq_trans (domainEnv_appendEnv empty G) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G2 p1 T1 G wtp1))))) eq_refl (PTyping_wf_0 (appendEnv G2 (appendEnv empty G)) p2 (weakenTy T2 (appendHvl H0 (bindPat p1))) G0 wtp2)))
  end
with PTyping_wf_1 (G2 : Env) (p24 : Pat) (T60 : Ty) (G8 : Env) (wtp8 : (PTyping G2 p24 T60 G8)) {struct wtp8} :
(wfTy (domainEnv G2) T60) :=
  match wtp8 in (PTyping _ p24 T60 G8) return (wfTy (domainEnv G2) T60) with
    | (P_Var T H32) => H32
    | (P_Prod T1 T2 p1 p2 G G0 wtp1 wtp2 H34) => (wfTy_tprod (domainEnv G2) (PTyping_wf_1 G2 p1 T1 G wtp1) H34)
  end.
Fixpoint Typing_wf_0 (G2 : Env) (t37 : Tm) (T61 : Ty) (jm12 : (Typing G2 t37 T61)) {struct jm12} :
(wfTm (domainEnv G2) t37) :=
  match jm12 in (Typing _ t37 T61) return (wfTm (domainEnv G2) t37) with
    | (T_Var T x lk0 H32 H33) => (wfTm_var (domainEnv G2) _ H33)
    | (T_Abs T1 T2 t jm H34 H35) => (wfTm_abs (domainEnv G2) H34 (Typing_wf_0 (evar G2 T1) t (weakenTy T2 (HS tm H0)) jm))
    | (T_App T11 T12 t1 t2 jm0 jm1) => (wfTm_app (domainEnv G2) (Typing_wf_0 G2 t1 (tarr T11 T12) jm0) (Typing_wf_0 G2 t2 T11 jm1))
    | (T_Tabs T t jm2) => (wfTm_tabs (domainEnv G2) (Typing_wf_0 (etvar G2) t T jm2))
    | (T_Tapp T12 T2 t1 jm3 H44) => (wfTm_tapp (domainEnv G2) (Typing_wf_0 G2 t1 (tall T12) jm3) H44)
    | (T_Pack T2 U t2 jm4 H46 H47) => (wfTm_pack (domainEnv G2) H47 (Typing_wf_0 G2 t2 (tsubstTy X0 U T2) jm4) (wfTy_texist (domainEnv G2) H46))
    | (T_Unpack T12 T2 t1 t2 jm5 jm6 H50) => (wfTm_unpack (domainEnv G2) (Typing_wf_0 G2 t1 (texist T12) jm5) (Typing_wf_0 (evar (etvar G2) T12) t2 (weakenTy T2 (HS tm (HS ty H0))) jm6))
    | (T_Prod T1 T2 t1 t2 jm7 jm8) => (wfTm_prod (domainEnv G2) (Typing_wf_0 G2 t1 T1 jm7) (Typing_wf_0 G2 t2 T2 jm8))
    | (T_Case T1 T2 p t1 t2 G1 jm9 wtp jm10 H58) => (wfTm_case (domainEnv G2) (Typing_wf_0 G2 t1 T1 jm9) (PTyping_wf_0 G2 p T1 G1 wtp) (wfTm_cast _ _ _ _ (eq_trans (domainEnv_appendEnv G2 (appendEnv empty G1)) (f_equal2 appendHvl (eq_refl (domainEnv G2)) (eq_trans (domainEnv_appendEnv empty G1) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G2 p T1 G1 wtp))))) eq_refl (Typing_wf_0 (appendEnv G2 (appendEnv empty G1)) t2 (weakenTy T2 (appendHvl H0 (bindPat p))) jm10)))
  end
with Typing_wf_1 (G2 : Env) (t37 : Tm) (T61 : Ty) (jm13 : (Typing G2 t37 T61)) {struct jm13} :
(wfTy (domainEnv G2) T61) :=
  match jm13 in (Typing _ t37 T61) return (wfTy (domainEnv G2) T61) with
    | (T_Var T x lk1 H32 H33) => H32
    | (T_Abs T1 T2 t jm H34 H35) => (wfTy_tarr (domainEnv G2) H34 H35)
    | (T_App T11 T12 t1 t2 jm0 jm1) => (inversion_wfTy_tarr_1 (domainEnv G2) T11 T12 (Typing_wf_1 G2 t1 (tarr T11 T12) jm0))
    | (T_Tabs T t jm2) => (wfTy_tall (domainEnv G2) (Typing_wf_1 (etvar G2) t T jm2))
    | (T_Tapp T12 T2 t1 jm3 H44) => (substhvl_ty_wfTy H44 (HS ty (domainEnv G2)) T12 (inversion_wfTy_tall_1 (domainEnv G2) T12 (Typing_wf_1 G2 t1 (tall T12) jm3)) (substhvl_ty_here (domainEnv G2)))
    | (T_Pack T2 U t2 jm4 H46 H47) => (wfTy_texist (domainEnv G2) H46)
    | (T_Unpack T12 T2 t1 t2 jm5 jm6 H50) => H50
    | (T_Prod T1 T2 t1 t2 jm7 jm8) => (wfTy_tprod (domainEnv G2) (Typing_wf_1 G2 t1 T1 jm7) (Typing_wf_1 G2 t2 T2 jm8))
    | (T_Case T1 T2 p t1 t2 G1 jm9 wtp jm10 H58) => H58
  end.
 Hint Extern 8 => match goal with
  | H61 : (PTyping _ _ _ _) |- _ => pose proof ((PTyping_wf_0 _ _ _ _ H61)); pose proof ((PTyping_wf_1 _ _ _ _ H61)); clear H61
end : wf.
 Hint Extern 8 => match goal with
  | H62 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H62)); pose proof ((Typing_wf_1 _ _ _ H62)); clear H62
end : wf.
Lemma subst_evar_lookup_evar (G9 : Env) (s8 : Tm) (T62 : Ty) (jm14 : (Typing G9 s8 T62)) :
  (forall (d0 : (Trace tm)) (G10 : Env) (G12 : Env) (sub : (subst_evar G9 T62 s8 d0 G10 G12)) (x20 : (Index tm)) (T63 : Ty) ,
    (lookup_evar G10 x20 T63) -> (Typing G12 (substIndex d0 s8 x20) T63)).
Proof.
  needleGenericSubstEnvLookupHom (T_Var).
Qed.
Fixpoint subst_evar_PTyping (G12 : Env) (s8 : Tm) (T62 : Ty) (jm14 : (Typing G12 s8 T62)) (G11 : Env) (p : Pat) (T : Ty) (G13 : Env) (wtp11 : (PTyping G11 p T G13)) :
(forall (G14 : Env) (d0 : (Trace tm)) (H69 : (subst_evar G12 T62 s8 d0 G11 G14)) ,
  (PTyping G14 p T G13)) :=
  match wtp11 in (PTyping _ p T G13) return (forall (G14 : Env) (d0 : (Trace tm)) (H69 : (subst_evar G12 T62 s8 d0 G11 G14)) ,
    (PTyping G14 p T G13)) with
    | (P_Var T63 H64) => (fun (G14 : Env) (d0 : (Trace tm)) (H69 : (subst_evar G12 T62 s8 d0 G11 G14)) =>
      (P_Var G14 T63 (substhvl_tm_wfTy _ _ H64 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H69)))))
    | (P_Prod T64 T65 p25 p26 G9 G10 wtp9 wtp10 H66) => (fun (G14 : Env) (d0 : (Trace tm)) (H69 : (subst_evar G12 T62 s8 d0 G11 G14)) =>
      (PTyping_cast G14 _ _ _ G14 (pprod p25 p26) (tprod T64 T65) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym eq_refl) eq_refl) (eq_sym eq_refl)) (P_Prod G14 T64 T65 p25 p26 G9 G10 (subst_evar_PTyping G12 s8 T62 jm14 G11 p25 T64 G9 wtp9 G14 d0 (weaken_subst_evar _ empty H69)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) eq_refl (eq_trans eq_refl (eq_sym eq_refl)) eq_refl (subst_evar_PTyping G12 s8 T62 jm14 (appendEnv G11 (appendEnv empty G9)) p26 (weakenTy T65 (appendHvl H0 (bindPat p25))) G10 wtp10 (appendEnv G14 (appendEnv empty G9)) (weakenTrace d0 (domainEnv (appendEnv empty G9))) (weaken_subst_evar _ (appendEnv empty G9) H69))) (substhvl_tm_wfTy _ _ H66 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H69))))))
  end.
Fixpoint subst_etvar_PTyping (G12 : Env) (S7 : Ty) (H69 : (wfTy (domainEnv G12) S7)) (G11 : Env) (p : Pat) (T : Ty) (G13 : Env) (wtp11 : (PTyping G11 p T G13)) :
(forall (G14 : Env) (d0 : (Trace ty)) (H70 : (subst_etvar G12 S7 d0 G11 G14)) ,
  (PTyping G14 (tsubstPat d0 S7 p) (tsubstTy d0 S7 T) (tsubstEnv d0 S7 G13))) :=
  match wtp11 in (PTyping _ p T G13) return (forall (G14 : Env) (d0 : (Trace ty)) (H70 : (subst_etvar G12 S7 d0 G11 G14)) ,
    (PTyping G14 (tsubstPat d0 S7 p) (tsubstTy d0 S7 T) (tsubstEnv d0 S7 G13))) with
    | (P_Var T63 H64) => (fun (G14 : Env) (d0 : (Trace ty)) (H70 : (subst_etvar G12 S7 d0 G11 G14)) =>
      (P_Var G14 (tsubstTy (weakenTrace d0 H0) S7 T63) (substhvl_ty_wfTy H69 _ _ H64 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H70)))))
    | (P_Prod T64 T65 p25 p26 G9 G10 wtp9 wtp10 H66) => (fun (G14 : Env) (d0 : (Trace ty)) (H70 : (subst_etvar G12 S7 d0 G11 G14)) =>
      (PTyping_cast G14 _ _ _ G14 (tsubstPat d0 S7 (pprod p25 p26)) (tsubstTy d0 S7 (tprod T64 T65)) _ eq_refl eq_refl eq_refl (eq_trans (f_equal2 appendEnv (eq_sym (tsubstEnv_appendEnv d0 S7 empty G9)) eq_refl) (eq_sym (tsubstEnv_appendEnv d0 S7 (appendEnv empty G9) G10))) (P_Prod G14 (tsubstTy (weakenTrace d0 H0) S7 T64) (tsubstTy (weakenTrace d0 H0) S7 T65) (tsubstPat (weakenTrace d0 H0) S7 p25) (tsubstPat (weakenTrace d0 (appendHvl H0 (bindPat p25))) S7 p26) (tsubstEnv (weakenTrace d0 H0) S7 G9) (tsubstEnv (weakenTrace d0 (domainEnv (appendEnv empty G9))) S7 G10) (subst_etvar_PTyping G12 S7 H69 G11 p25 T64 G9 wtp9 G14 d0 (weaken_subst_etvar empty H70)) (PTyping_cast _ _ _ _ _ _ _ _ (f_equal2 appendEnv eq_refl (tsubstEnv_appendEnv d0 S7 empty G9)) (f_equal3 tsubstPat (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G11 p25 T64 G9 wtp9)))) eq_refl eq_refl) (eq_trans (f_equal3 tsubstTy (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G11 p25 T64 G9 wtp9)))) eq_refl eq_refl) (eq_trans (eq_sym (weakenTy_tsubstTy (appendHvl H0 (bindPat p25)) d0 S7 T65)) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))))) eq_refl (subst_etvar_PTyping G12 S7 H69 (appendEnv G11 (appendEnv empty G9)) p26 (weakenTy T65 (appendHvl H0 (bindPat p25))) G10 wtp10 (appendEnv G14 (tsubstEnv d0 S7 (appendEnv empty G9))) (weakenTrace d0 (domainEnv (appendEnv empty G9))) (weaken_subst_etvar (appendEnv empty G9) H70))) (substhvl_ty_wfTy H69 _ _ H66 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H70))))))
  end.
Fixpoint subst_evar_Typing (G11 : Env) (s8 : Tm) (T63 : Ty) (jm26 : (Typing G11 s8 T63)) (G10 : Env) (t : Tm) (T : Ty) (jm27 : (Typing G10 t T)) :
(forall (G12 : Env) (d0 : (Trace tm)) (H95 : (subst_evar G11 T63 s8 d0 G10 G12)) ,
  (Typing G12 (substTm d0 s8 t) T)) :=
  match jm27 in (Typing _ t T) return (forall (G12 : Env) (d0 : (Trace tm)) (H95 : (subst_evar G11 T63 s8 d0 G10 G12)) ,
    (Typing G12 (substTm d0 s8 t) T)) with
    | (T_Var T64 x20 lk2 H65 H66) => (fun (G12 : Env) (d0 : (Trace tm)) (H95 : (subst_evar G11 T63 s8 d0 G10 G12)) =>
      (subst_evar_lookup_evar G11 s8 T63 jm26 d0 G10 G12 H95 x20 T64 lk2))
    | (T_Abs T65 T68 t38 jm14 H67 H68) => (fun (G12 : Env) (d0 : (Trace tm)) (H95 : (subst_evar G11 T63 s8 d0 G10 G12)) =>
      (T_Abs G12 T65 T68 (substTm (weakenTrace d0 (HS tm H0)) s8 t38) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G11 s8 T63 jm26 (evar G10 T65) t38 (weakenTy T68 (HS tm H0)) jm14 (appendEnv G12 (evar empty T65)) (weakenTrace d0 (HS tm H0)) (weaken_subst_evar _ (evar empty T65) H95))) (substhvl_tm_wfTy _ _ H67 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H95))) (substhvl_tm_wfTy _ _ H68 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H95)))))
    | (T_App T66 T67 t39 t40 jm15 jm16) => (fun (G12 : Env) (d0 : (Trace tm)) (H95 : (subst_evar G11 T63 s8 d0 G10 G12)) =>
      (T_App G12 T66 T67 (substTm (weakenTrace d0 H0) s8 t39) (substTm (weakenTrace d0 H0) s8 t40) (subst_evar_Typing G11 s8 T63 jm26 G10 t39 (tarr T66 T67) jm15 G12 d0 (weaken_subst_evar _ empty H95)) (subst_evar_Typing G11 s8 T63 jm26 G10 t40 T66 jm16 G12 d0 (weaken_subst_evar _ empty H95))))
    | (T_Tabs T64 t38 jm18) => (fun (G12 : Env) (d0 : (Trace tm)) (H95 : (subst_evar G11 T63 s8 d0 G10 G12)) =>
      (T_Tabs G12 T64 (substTm (weakenTrace d0 (HS ty H0)) s8 t38) (subst_evar_Typing G11 s8 T63 jm26 (etvar G10) t38 T64 jm18 (appendEnv G12 (etvar empty)) (weakenTrace d0 (HS ty H0)) (weaken_subst_evar _ (etvar empty) H95))))
    | (T_Tapp T67 T68 t39 jm19 H77) => (fun (G12 : Env) (d0 : (Trace tm)) (H95 : (subst_evar G11 T63 s8 d0 G10 G12)) =>
      (T_Tapp G12 T67 T68 (substTm (weakenTrace d0 H0) s8 t39) (subst_evar_Typing G11 s8 T63 jm26 G10 t39 (tall T67) jm19 G12 d0 (weaken_subst_evar _ empty H95)) (substhvl_tm_wfTy _ _ H77 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H95)))))
    | (T_Pack T68 U1 t40 jm20 H79 H80) => (fun (G12 : Env) (d0 : (Trace tm)) (H95 : (subst_evar G11 T63 s8 d0 G10 G12)) =>
      (T_Pack G12 T68 U1 (substTm (weakenTrace d0 H0) s8 t40) (subst_evar_Typing G11 s8 T63 jm26 G10 t40 (tsubstTy X0 U1 T68) jm20 G12 d0 (weaken_subst_evar _ empty H95)) (substhvl_tm_wfTy _ _ H79 (weaken_substhvl_tm (HS ty H0) (subst_evar_substhvl_tm _ H95))) (substhvl_tm_wfTy _ _ H80 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H95)))))
    | (T_Unpack T67 T68 t39 t40 jm21 jm22 H83) => (fun (G12 : Env) (d0 : (Trace tm)) (H95 : (subst_evar G11 T63 s8 d0 G10 G12)) =>
      (T_Unpack G12 T67 T68 (substTm (weakenTrace d0 H0) s8 t39) (substTm (weakenTrace d0 (HS tm (HS ty H0))) s8 t40) (subst_evar_Typing G11 s8 T63 jm26 G10 t39 (texist T67) jm21 G12 d0 (weaken_subst_evar _ empty H95)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G11 s8 T63 jm26 (evar (etvar G10) T67) t40 (weakenTy T68 (HS tm (HS ty H0))) jm22 (appendEnv G12 (evar (etvar empty) T67)) (weakenTrace d0 (HS tm (HS ty H0))) (weaken_subst_evar _ (evar (etvar empty) T67) H95))) (substhvl_tm_wfTy _ _ H83 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H95)))))
    | (T_Prod T65 T68 t39 t40 jm23 jm24) => (fun (G12 : Env) (d0 : (Trace tm)) (H95 : (subst_evar G11 T63 s8 d0 G10 G12)) =>
      (T_Prod G12 T65 T68 (substTm (weakenTrace d0 H0) s8 t39) (substTm (weakenTrace d0 H0) s8 t40) (subst_evar_Typing G11 s8 T63 jm26 G10 t39 T65 jm23 G12 d0 (weaken_subst_evar _ empty H95)) (subst_evar_Typing G11 s8 T63 jm26 G10 t40 T68 jm24 G12 d0 (weaken_subst_evar _ empty H95))))
    | (T_Case T65 T68 p25 t39 t40 G9 jm25 wtp9 jm17 H91) => (fun (G12 : Env) (d0 : (Trace tm)) (H95 : (subst_evar G11 T63 s8 d0 G10 G12)) =>
      (T_Case G12 T65 T68 p25 (substTm (weakenTrace d0 H0) s8 t39) (substTm (weakenTrace d0 (appendHvl H0 (bindPat p25))) s8 t40) G9 (subst_evar_Typing G11 s8 T63 jm26 G10 t39 T65 jm25 G12 d0 (weaken_subst_evar _ empty H95)) (subst_evar_PTyping G11 s8 T63 jm26 G10 p25 T65 G9 wtp9 G12 d0 (weaken_subst_evar _ empty H95)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl eq_refl) (f_equal3 substTm (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G10 p25 T65 G9 wtp9)))) eq_refl eq_refl) (eq_trans eq_refl (eq_sym eq_refl)) (subst_evar_Typing G11 s8 T63 jm26 (appendEnv G10 (appendEnv empty G9)) t40 (weakenTy T68 (appendHvl H0 (bindPat p25))) jm17 (appendEnv G12 (appendEnv empty G9)) (weakenTrace d0 (domainEnv (appendEnv empty G9))) (weaken_subst_evar _ (appendEnv empty G9) H95))) (substhvl_tm_wfTy _ _ H91 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H95)))))
  end.
Fixpoint subst_etvar_Typing (G11 : Env) (S7 : Ty) (H95 : (wfTy (domainEnv G11) S7)) (G10 : Env) (t : Tm) (T : Ty) (jm26 : (Typing G10 t T)) :
(forall (G12 : Env) (d0 : (Trace ty)) (H96 : (subst_etvar G11 S7 d0 G10 G12)) ,
  (Typing G12 (tsubstTm d0 S7 t) (tsubstTy d0 S7 T))) :=
  match jm26 in (Typing _ t T) return (forall (G12 : Env) (d0 : (Trace ty)) (H96 : (subst_etvar G11 S7 d0 G10 G12)) ,
    (Typing G12 (tsubstTm d0 S7 t) (tsubstTy d0 S7 T))) with
    | (T_Var T64 x20 lk2 H65 H66) => (fun (G12 : Env) (d0 : (Trace ty)) (H96 : (subst_etvar G11 S7 d0 G10 G12)) =>
      (T_Var G12 (tsubstTy (weakenTrace d0 H0) S7 T64) x20 (subst_etvar_lookup_evar H95 H96 T64 lk2) (substhvl_ty_wfTy H95 _ _ H65 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H96))) (substhvl_ty_wfindex_tm (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H96)) H66)))
    | (T_Abs T65 T68 t38 jm14 H67 H68) => (fun (G12 : Env) (d0 : (Trace ty)) (H96 : (subst_etvar G11 S7 d0 G10 G12)) =>
      (T_Abs G12 (tsubstTy (weakenTrace d0 H0) S7 T65) (tsubstTy (weakenTrace d0 H0) S7 T68) (tsubstTm (weakenTrace d0 (HS tm H0)) S7 t38) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tsubstTy (HS tm H0) d0 S7 T68)) (subst_etvar_Typing G11 S7 H95 (evar G10 T65) t38 (weakenTy T68 (HS tm H0)) jm14 (appendEnv G12 (tsubstEnv d0 S7 (evar empty T65))) (weakenTrace d0 (HS tm H0)) (weaken_subst_etvar (evar empty T65) H96))) (substhvl_ty_wfTy H95 _ _ H67 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H96))) (substhvl_ty_wfTy H95 _ _ H68 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H96)))))
    | (T_App T66 T67 t39 t40 jm15 jm16) => (fun (G12 : Env) (d0 : (Trace ty)) (H96 : (subst_etvar G11 S7 d0 G10 G12)) =>
      (T_App G12 (tsubstTy (weakenTrace d0 H0) S7 T66) (tsubstTy (weakenTrace d0 H0) S7 T67) (tsubstTm (weakenTrace d0 H0) S7 t39) (tsubstTm (weakenTrace d0 H0) S7 t40) (subst_etvar_Typing G11 S7 H95 G10 t39 (tarr T66 T67) jm15 G12 d0 (weaken_subst_etvar empty H96)) (subst_etvar_Typing G11 S7 H95 G10 t40 T66 jm16 G12 d0 (weaken_subst_etvar empty H96))))
    | (T_Tabs T64 t38 jm18) => (fun (G12 : Env) (d0 : (Trace ty)) (H96 : (subst_etvar G11 S7 d0 G10 G12)) =>
      (T_Tabs G12 (tsubstTy (weakenTrace d0 (HS ty H0)) S7 T64) (tsubstTm (weakenTrace d0 (HS ty H0)) S7 t38) (subst_etvar_Typing G11 S7 H95 (etvar G10) t38 T64 jm18 (appendEnv G12 (tsubstEnv d0 S7 (etvar empty))) (weakenTrace d0 (HS ty H0)) (weaken_subst_etvar (etvar empty) H96))))
    | (T_Tapp T67 T68 t39 jm19 H77) => (fun (G12 : Env) (d0 : (Trace ty)) (H96 : (subst_etvar G11 S7 d0 G10 G12)) =>
      (Typing_cast G12 _ _ G12 (tsubstTm d0 S7 (tapp t39 T68)) (tsubstTy d0 S7 (tsubstTy X0 T68 T67)) eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T67 d0 S7 T68)) (T_Tapp G12 (tsubstTy (weakenTrace d0 (HS ty H0)) S7 T67) (tsubstTy (weakenTrace d0 H0) S7 T68) (tsubstTm (weakenTrace d0 H0) S7 t39) (subst_etvar_Typing G11 S7 H95 G10 t39 (tall T67) jm19 G12 d0 (weaken_subst_etvar empty H96)) (substhvl_ty_wfTy H95 _ _ H77 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H96))))))
    | (T_Pack T68 U1 t40 jm20 H79 H80) => (fun (G12 : Env) (d0 : (Trace ty)) (H96 : (subst_etvar G11 S7 d0 G10 G12)) =>
      (T_Pack G12 (tsubstTy (weakenTrace d0 (HS ty H0)) S7 T68) (tsubstTy (weakenTrace d0 H0) S7 U1) (tsubstTm (weakenTrace d0 H0) S7 t40) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (tsubstTy_tsubstTy0_comm T68 d0 S7 U1) (subst_etvar_Typing G11 S7 H95 G10 t40 (tsubstTy X0 U1 T68) jm20 G12 d0 (weaken_subst_etvar empty H96))) (substhvl_ty_wfTy H95 _ _ H79 (weaken_substhvl_ty (HS ty H0) (subst_etvar_substhvl_ty H96))) (substhvl_ty_wfTy H95 _ _ H80 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H96)))))
    | (T_Unpack T67 T68 t39 t40 jm21 jm22 H83) => (fun (G12 : Env) (d0 : (Trace ty)) (H96 : (subst_etvar G11 S7 d0 G10 G12)) =>
      (T_Unpack G12 (tsubstTy (weakenTrace d0 (HS ty H0)) S7 T67) (tsubstTy (weakenTrace d0 H0) S7 T68) (tsubstTm (weakenTrace d0 H0) S7 t39) (tsubstTm (weakenTrace d0 (HS tm (HS ty H0))) S7 t40) (subst_etvar_Typing G11 S7 H95 G10 t39 (texist T67) jm21 G12 d0 (weaken_subst_etvar empty H96)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tsubstTy (HS tm (HS ty H0)) d0 S7 T68)) (subst_etvar_Typing G11 S7 H95 (evar (etvar G10) T67) t40 (weakenTy T68 (HS tm (HS ty H0))) jm22 (appendEnv G12 (tsubstEnv d0 S7 (evar (etvar empty) T67))) (weakenTrace d0 (HS tm (HS ty H0))) (weaken_subst_etvar (evar (etvar empty) T67) H96))) (substhvl_ty_wfTy H95 _ _ H83 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H96)))))
    | (T_Prod T65 T68 t39 t40 jm23 jm24) => (fun (G12 : Env) (d0 : (Trace ty)) (H96 : (subst_etvar G11 S7 d0 G10 G12)) =>
      (T_Prod G12 (tsubstTy (weakenTrace d0 H0) S7 T65) (tsubstTy (weakenTrace d0 H0) S7 T68) (tsubstTm (weakenTrace d0 H0) S7 t39) (tsubstTm (weakenTrace d0 H0) S7 t40) (subst_etvar_Typing G11 S7 H95 G10 t39 T65 jm23 G12 d0 (weaken_subst_etvar empty H96)) (subst_etvar_Typing G11 S7 H95 G10 t40 T68 jm24 G12 d0 (weaken_subst_etvar empty H96))))
    | (T_Case T65 T68 p25 t39 t40 G9 jm25 wtp9 jm17 H91) => (fun (G12 : Env) (d0 : (Trace ty)) (H96 : (subst_etvar G11 S7 d0 G10 G12)) =>
      (T_Case G12 (tsubstTy (weakenTrace d0 H0) S7 T65) (tsubstTy (weakenTrace d0 H0) S7 T68) (tsubstPat (weakenTrace d0 H0) S7 p25) (tsubstTm (weakenTrace d0 H0) S7 t39) (tsubstTm (weakenTrace d0 (appendHvl H0 (bindPat p25))) S7 t40) (tsubstEnv (weakenTrace d0 H0) S7 G9) (subst_etvar_Typing G11 S7 H95 G10 t39 T65 jm25 G12 d0 (weaken_subst_etvar empty H96)) (subst_etvar_PTyping G11 S7 H95 G10 p25 T65 G9 wtp9 G12 d0 (weaken_subst_etvar empty H96)) (Typing_cast _ _ _ _ _ _ (f_equal2 appendEnv eq_refl (tsubstEnv_appendEnv d0 S7 empty G9)) (f_equal3 tsubstTm (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G10 p25 T65 G9 wtp9)))) eq_refl eq_refl) (eq_trans (f_equal3 tsubstTy (f_equal2 weakenTrace eq_refl (eq_trans (domainEnv_appendEnv empty G9) (f_equal2 appendHvl (eq_refl H0) (domain_PTyping_bindPat G10 p25 T65 G9 wtp9)))) eq_refl eq_refl) (eq_trans (eq_sym (weakenTy_tsubstTy (appendHvl H0 (bindPat p25)) d0 S7 T68)) (f_equal2 weakenTy eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))))) (subst_etvar_Typing G11 S7 H95 (appendEnv G10 (appendEnv empty G9)) t40 (weakenTy T68 (appendHvl H0 (bindPat p25))) jm17 (appendEnv G12 (tsubstEnv d0 S7 (appendEnv empty G9))) (weakenTrace d0 (domainEnv (appendEnv empty G9))) (weaken_subst_etvar (appendEnv empty G9) H96))) (substhvl_ty_wfTy H95 _ _ H91 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty H96)))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutofftm_append weakenCutoffty_append weakenTrace_append weakenPat_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.