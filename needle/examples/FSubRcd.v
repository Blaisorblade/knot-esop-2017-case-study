Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export Needle.

Local Set Asymmetric Patterns.

Section Namespace.
  Inductive Namespace : Type :=
    | tm 
    | ty .
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
  
  Fixpoint weakenIndextm (x6 : (Index tm)) (k : Hvl) {struct k} :
  (Index tm) :=
    match k with
      | (H0) => x6
      | (HS a k) => match a with
        | (tm) => (IS (weakenIndextm x6 k))
        | _ => (weakenIndextm x6 k)
      end
    end.
  Fixpoint weakenIndexty (X7 : (Index ty)) (k : Hvl) {struct k} :
  (Index ty) :=
    match k with
      | (H0) => X7
      | (HS a k) => match a with
        | (ty) => (IS (weakenIndexty X7 k))
        | _ => (weakenIndexty X7 k)
      end
    end.
  Lemma weakenIndextm_append  :
    (forall (x6 : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x6 k) k0) = (weakenIndextm x6 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexty_append  :
    (forall (X7 : (Index ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexty (weakenIndexty X7 k) k0) = (weakenIndexty X7 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Lab : Set :=
    | L0 
    | LS (l : Lab).
  Scheme ind_Lab := Induction for Lab Sort Prop.
  
  Inductive TRec : Set :=
    | tnil 
    | tcons (l : Lab) (T : Ty)
        (TS : TRec)
  with Ty : Set :=
    | tvar (X : (Index ty))
    | top 
    | tarr (T1 : Ty) (T2 : Ty)
    | tall (T1 : Ty) (T2 : Ty)
    | trec (TS : TRec).
  Scheme ind_TRec := Induction for TRec Sort Prop
  with ind_Ty := Induction for Ty Sort Prop.
  Combined Scheme ind_TRec_Ty from ind_TRec, ind_Ty.
  
  Inductive Pat : Set :=
    | pvar (T : Ty)
    | prec (ps : PRec)
  with PRec : Set :=
    | pnil 
    | pcons (l : Lab) (p : Pat)
        (ps : PRec).
  Scheme ind_Pat := Induction for Pat Sort Prop
  with ind_PRec := Induction for PRec Sort Prop.
  Combined Scheme ind_Pat_PRec from ind_Pat, ind_PRec.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tabs (T : Ty) (t : Tm)
    | tapp (t : Tm) (T : Ty)
    | rec (ts : Rec)
    | prj (t : Tm) (l : Lab)
    | lett (p : Pat) (t1 : Tm)
        (t2 : Tm)
  with Rec : Set :=
    | rnil 
    | rcons (l : Lab) (t : Tm)
        (ts : Rec).
  Scheme ind_Tm := Induction for Tm Sort Prop
  with ind_Rec := Induction for Rec Sort Prop.
  Combined Scheme ind_Tm_Rec from ind_Tm, ind_Rec.
End Terms.

Section Functions.
  Fixpoint bindPRec (ps5 : PRec) {struct ps5} :
  Hvl :=
    match ps5 with
      | (pnil) => H0
      | (pcons l p ps) => (appendHvl (appendHvl H0 (bindPat p)) (bindPRec ps))
    end
  with bindPat (p5 : Pat) {struct p5} :
  Hvl :=
    match p5 with
      | (pvar T) => (HS tm H0)
      | (prec ps) => (appendHvl H0 (bindPRec ps))
    end.
  Scheme ind_bindPRec_bindPat_PRec := Induction for PRec Sort Prop
  with ind_bindPRec_bindPat_Pat := Induction for Pat Sort Prop.
  Combined Scheme ind_bindPRec_bindPat_PRec_Pat from ind_bindPRec_bindPat_PRec, ind_bindPRec_bindPat_Pat.
End Functions.

Section Shift.
  Inductive Cutoff (a : Namespace) : Type :=
    | C0 
    | CS : (Cutoff a) -> (Cutoff a).
  
  Global Arguments C0 {a} .
  Global Arguments CS {a} _ .
  Fixpoint weakenCutofftm (c : (Cutoff tm)) (k : Hvl) {struct k} :
  (Cutoff tm) :=
    match k with
      | (H0) => c
      | (HS a k) => match a with
        | (tm) => (CS (weakenCutofftm c k))
        | _ => (weakenCutofftm c k)
      end
    end.
  Fixpoint weakenCutoffty (c : (Cutoff ty)) (k : Hvl) {struct k} :
  (Cutoff ty) :=
    match k with
      | (H0) => c
      | (HS a k) => match a with
        | (ty) => (CS (weakenCutoffty c k))
        | _ => (weakenCutoffty c k)
      end
    end.
  
  Lemma weakenCutofftm_append  :
    (forall (c : (Cutoff tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutofftm (weakenCutofftm c k) k0) = (weakenCutofftm c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenCutoffty_append  :
    (forall (c : (Cutoff ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffty (weakenCutoffty c k) k0) = (weakenCutoffty c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint shiftIndex (c : (Cutoff tm)) (x6 : (Index tm)) {struct c} :
  (Index tm) :=
    match c with
      | (C0) => (IS x6)
      | (CS c) => match x6 with
        | (I0) => I0
        | (IS x6) => (IS (shiftIndex c x6))
      end
    end.
  Fixpoint tshiftIndex (c : (Cutoff ty)) (X7 : (Index ty)) {struct c} :
  (Index ty) :=
    match c with
      | (C0) => (IS X7)
      | (CS c) => match X7 with
        | (I0) => I0
        | (IS X7) => (IS (tshiftIndex c X7))
      end
    end.
  Fixpoint tshiftTRec (c : (Cutoff ty)) (SS : TRec) {struct SS} :
  TRec :=
    match SS with
      | (tnil) => (tnil)
      | (tcons l5 T11 TS1) => (tcons l5 (tshiftTy c T11) (tshiftTRec c TS1))
    end
  with tshiftTy (c : (Cutoff ty)) (S0 : Ty) {struct S0} :
  Ty :=
    match S0 with
      | (tvar X7) => (tvar (tshiftIndex c X7))
      | (top) => (top)
      | (tarr T11 T12) => (tarr (tshiftTy c T11) (tshiftTy c T12))
      | (tall T13 T14) => (tall (tshiftTy c T13) (tshiftTy (CS c) T14))
      | (trec TS1) => (trec (tshiftTRec c TS1))
    end.
  Fixpoint tshiftPat (c : (Cutoff ty)) (p6 : Pat) {struct p6} :
  Pat :=
    match p6 with
      | (pvar T11) => (pvar (tshiftTy c T11))
      | (prec ps6) => (prec (tshiftPRec c ps6))
    end
  with tshiftPRec (c : (Cutoff ty)) (ps6 : PRec) {struct ps6} :
  PRec :=
    match ps6 with
      | (pnil) => (pnil)
      | (pcons l5 p6 ps7) => (pcons l5 (tshiftPat c p6) (tshiftPRec (weakenCutoffty c (appendHvl H0 (bindPat p6))) ps7))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var (shiftIndex c x6))
      | (abs T11 t8) => (abs T11 (shiftTm (CS c) t8))
      | (app t9 t10) => (app (shiftTm c t9) (shiftTm c t10))
      | (tabs T12 t11) => (tabs T12 (shiftTm c t11))
      | (tapp t12 T13) => (tapp (shiftTm c t12) T13)
      | (rec ts1) => (rec (shiftRec c ts1))
      | (prj t13 l5) => (prj (shiftTm c t13) l5)
      | (lett p6 t14 t15) => (lett p6 (shiftTm c t14) (shiftTm (weakenCutofftm c (appendHvl H0 (bindPat p6))) t15))
    end
  with shiftRec (c : (Cutoff tm)) (ss : Rec) {struct ss} :
  Rec :=
    match ss with
      | (rnil) => (rnil)
      | (rcons l5 t8 ts1) => (rcons l5 (shiftTm c t8) (shiftRec c ts1))
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var x6)
      | (abs T11 t8) => (abs (tshiftTy c T11) (tshiftTm c t8))
      | (app t9 t10) => (app (tshiftTm c t9) (tshiftTm c t10))
      | (tabs T12 t11) => (tabs (tshiftTy c T12) (tshiftTm (CS c) t11))
      | (tapp t12 T13) => (tapp (tshiftTm c t12) (tshiftTy c T13))
      | (rec ts1) => (rec (tshiftRec c ts1))
      | (prj t13 l5) => (prj (tshiftTm c t13) l5)
      | (lett p6 t14 t15) => (lett (tshiftPat c p6) (tshiftTm c t14) (tshiftTm (weakenCutoffty c (appendHvl H0 (bindPat p6))) t15))
    end
  with tshiftRec (c : (Cutoff ty)) (ss : Rec) {struct ss} :
  Rec :=
    match ss with
      | (rnil) => (rnil)
      | (rcons l5 t8 ts1) => (rcons l5 (tshiftTm c t8) (tshiftRec c ts1))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenLab (l5 : Lab) (k : Hvl) {struct k} :
  Lab :=
    match k with
      | (H0) => l5
      | (HS tm k) => (weakenLab l5 k)
      | (HS ty k) => (weakenLab l5 k)
    end.
  Fixpoint weakenTRec (SS : TRec) (k : Hvl) {struct k} :
  TRec :=
    match k with
      | (H0) => SS
      | (HS tm k) => (weakenTRec SS k)
      | (HS ty k) => (tshiftTRec C0 (weakenTRec SS k))
    end.
  Fixpoint weakenTy (S0 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S0
      | (HS tm k) => (weakenTy S0 k)
      | (HS ty k) => (tshiftTy C0 (weakenTy S0 k))
    end.
  Fixpoint weakenPat (p6 : Pat) (k : Hvl) {struct k} :
  Pat :=
    match k with
      | (H0) => p6
      | (HS tm k) => (weakenPat p6 k)
      | (HS ty k) => (tshiftPat C0 (weakenPat p6 k))
    end.
  Fixpoint weakenPRec (ps6 : PRec) (k : Hvl) {struct k} :
  PRec :=
    match k with
      | (H0) => ps6
      | (HS tm k) => (weakenPRec ps6 k)
      | (HS ty k) => (tshiftPRec C0 (weakenPRec ps6 k))
    end.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} :
  Tm :=
    match k with
      | (H0) => s
      | (HS tm k) => (shiftTm C0 (weakenTm s k))
      | (HS ty k) => (tshiftTm C0 (weakenTm s k))
    end.
  Fixpoint weakenRec (ss : Rec) (k : Hvl) {struct k} :
  Rec :=
    match k with
      | (H0) => ss
      | (HS tm k) => (shiftRec C0 (weakenRec ss k))
      | (HS ty k) => (tshiftRec C0 (weakenRec ss k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T11 : (Trace a)).
  
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
  Fixpoint substIndex (d : (Trace tm)) (s : Tm) (x6 : (Index tm)) {struct d} :
  Tm :=
    match d with
      | (X0) => match x6 with
        | (I0) => s
        | (IS x6) => (var x6)
      end
      | (XS tm d) => match x6 with
        | (I0) => (var I0)
        | (IS x6) => (shiftTm C0 (substIndex d s x6))
      end
      | (XS ty d) => (tshiftTm C0 (substIndex d s x6))
    end.
  Fixpoint tsubstIndex (d : (Trace ty)) (S0 : Ty) (X7 : (Index ty)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X7 with
        | (I0) => S0
        | (IS X7) => (tvar X7)
      end
      | (XS tm d) => (tsubstIndex d S0 X7)
      | (XS ty d) => match X7 with
        | (I0) => (tvar I0)
        | (IS X7) => (tshiftTy C0 (tsubstIndex d S0 X7))
      end
    end.
  Fixpoint tsubstTRec (d : (Trace ty)) (S0 : Ty) (SS : TRec) {struct SS} :
  TRec :=
    match SS with
      | (tnil) => (tnil)
      | (tcons l5 T11 TS1) => (tcons l5 (tsubstTy d S0 T11) (tsubstTRec d S0 TS1))
    end
  with tsubstTy (d : (Trace ty)) (S0 : Ty) (S1 : Ty) {struct S1} :
  Ty :=
    match S1 with
      | (tvar X7) => (tsubstIndex d S0 X7)
      | (top) => (top)
      | (tarr T11 T12) => (tarr (tsubstTy d S0 T11) (tsubstTy d S0 T12))
      | (tall T13 T14) => (tall (tsubstTy d S0 T13) (tsubstTy (weakenTrace d (HS ty H0)) S0 T14))
      | (trec TS1) => (trec (tsubstTRec d S0 TS1))
    end.
  Fixpoint tsubstPat (d : (Trace ty)) (S0 : Ty) (p6 : Pat) {struct p6} :
  Pat :=
    match p6 with
      | (pvar T11) => (pvar (tsubstTy d S0 T11))
      | (prec ps6) => (prec (tsubstPRec d S0 ps6))
    end
  with tsubstPRec (d : (Trace ty)) (S0 : Ty) (ps6 : PRec) {struct ps6} :
  PRec :=
    match ps6 with
      | (pnil) => (pnil)
      | (pcons l5 p6 ps7) => (pcons l5 (tsubstPat d S0 p6) (tsubstPRec (weakenTrace d (appendHvl H0 (bindPat p6))) S0 ps7))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x6) => (substIndex d s x6)
      | (abs T11 t8) => (abs T11 (substTm (weakenTrace d (HS tm H0)) s t8))
      | (app t9 t10) => (app (substTm d s t9) (substTm d s t10))
      | (tabs T12 t11) => (tabs T12 (substTm (weakenTrace d (HS ty H0)) s t11))
      | (tapp t12 T13) => (tapp (substTm d s t12) T13)
      | (rec ts1) => (rec (substRec d s ts1))
      | (prj t13 l5) => (prj (substTm d s t13) l5)
      | (lett p6 t14 t15) => (lett p6 (substTm d s t14) (substTm (weakenTrace d (appendHvl H0 (bindPat p6))) s t15))
    end
  with substRec (d : (Trace tm)) (s : Tm) (ss : Rec) {struct ss} :
  Rec :=
    match ss with
      | (rnil) => (rnil)
      | (rcons l5 t8 ts1) => (rcons l5 (substTm d s t8) (substRec d s ts1))
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S0 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var x6)
      | (abs T11 t8) => (abs (tsubstTy d S0 T11) (tsubstTm (weakenTrace d (HS tm H0)) S0 t8))
      | (app t9 t10) => (app (tsubstTm d S0 t9) (tsubstTm d S0 t10))
      | (tabs T12 t11) => (tabs (tsubstTy d S0 T12) (tsubstTm (weakenTrace d (HS ty H0)) S0 t11))
      | (tapp t12 T13) => (tapp (tsubstTm d S0 t12) (tsubstTy d S0 T13))
      | (rec ts1) => (rec (tsubstRec d S0 ts1))
      | (prj t13 l5) => (prj (tsubstTm d S0 t13) l5)
      | (lett p6 t14 t15) => (lett (tsubstPat d S0 p6) (tsubstTm d S0 t14) (tsubstTm (weakenTrace d (appendHvl H0 (bindPat p6))) S0 t15))
    end
  with tsubstRec (d : (Trace ty)) (S0 : Ty) (ss : Rec) {struct ss} :
  Rec :=
    match ss with
      | (rnil) => (rnil)
      | (rcons l5 t8 ts1) => (rcons l5 (tsubstTm d S0 t8) (tsubstRec d S0 ts1))
    end.
End Subst.

Global Hint Resolve (f_equal (tshiftPRec C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftPat C0)) : cong_shift0.
Global Hint Resolve (f_equal (shiftRec C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftRec C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTRec C0)) : cong_shift0.
Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_tshift_bindPRec_bindPat  :
  (forall (ps6 : PRec) ,
    (forall (c : (Cutoff ty)) ,
      ((bindPRec (tshiftPRec c ps6)) = (bindPRec ps6)))) /\
  (forall (p6 : Pat) ,
    (forall (c0 : (Cutoff ty)) ,
      ((bindPat (tshiftPat c0 p6)) = (bindPat p6)))).
Proof.
  apply_mutual_ind (ind_bindPRec_bindPat_PRec_Pat); simpl; intros; congruence .
Qed.
Lemma stability_tshift_bindPRec (ps7 : PRec) :
  (forall (c1 : (Cutoff ty)) ,
    ((bindPRec (tshiftPRec c1 ps7)) = (bindPRec ps7))).
Proof.
  intros; eapply (stability_tshift_bindPRec_bindPat).
Qed.
Lemma stability_tshift_bindPat (p7 : Pat) :
  (forall (c2 : (Cutoff ty)) ,
    ((bindPat (tshiftPat c2 p7)) = (bindPat p7))).
Proof.
  intros; eapply (stability_tshift_bindPRec_bindPat).
Qed.
 Hint Rewrite stability_tshift_bindPRec stability_tshift_bindPat : interaction.
 Hint Rewrite stability_tshift_bindPRec stability_tshift_bindPat : stability_shift.
Lemma stability_weaken_bindPat  :
  (forall (k : Hvl) (p8 : Pat) ,
    ((bindPat (weakenPat p8 k)) = (bindPat p8))).
Proof.
  needleGenericStabilityWeaken .
Qed.
Lemma stability_weaken_bindPRec  :
  (forall (k : Hvl) (ps8 : PRec) ,
    ((bindPRec (weakenPRec ps8 k)) = (bindPRec ps8))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bindPRec stability_weaken_bindPat : interaction.
 Hint Rewrite stability_weaken_bindPRec stability_weaken_bindPat : stability_weaken.
Lemma stability_tsubst_bindPRec_bindPat  :
  (forall (ps8 : PRec) ,
    (forall (d : (Trace ty)) (S0 : Ty) ,
      ((bindPRec (tsubstPRec d S0 ps8)) = (bindPRec ps8)))) /\
  (forall (p8 : Pat) ,
    (forall (d0 : (Trace ty)) (S1 : Ty) ,
      ((bindPat (tsubstPat d0 S1 p8)) = (bindPat p8)))).
Proof.
  apply_mutual_ind (ind_bindPRec_bindPat_PRec_Pat); simpl; intros; congruence .
Qed.
Lemma stability_tsubst_bindPRec (ps9 : PRec) :
  (forall (d1 : (Trace ty)) (S2 : Ty) ,
    ((bindPRec (tsubstPRec d1 S2 ps9)) = (bindPRec ps9))).
Proof.
  intros; eapply (stability_tsubst_bindPRec_bindPat).
Qed.
Lemma stability_tsubst_bindPat (p9 : Pat) :
  (forall (d2 : (Trace ty)) (S3 : Ty) ,
    ((bindPat (tsubstPat d2 S3 p9)) = (bindPat p9))).
Proof.
  intros; eapply (stability_tsubst_bindPRec_bindPat).
Qed.
 Hint Rewrite stability_tsubst_bindPRec stability_tsubst_bindPat : interaction.
 Hint Rewrite stability_tsubst_bindPRec stability_tsubst_bindPat : stability_subst.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x6 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k) s (shiftIndex (weakenCutofftm C0 k) x6)) = (var x6))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S4 : Ty) :
    (forall (k : Hvl) (X7 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k) S4 (tshiftIndex (weakenCutoffty C0 k) X7)) = (tvar X7))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint tsubst0_tshift0_TRec_reflection_ind (SS : TRec) (k : Hvl) (S4 : Ty) {struct SS} :
  ((tsubstTRec (weakenTrace X0 k) S4 (tshiftTRec (weakenCutoffty C0 k) SS)) = SS) :=
    match SS return ((tsubstTRec (weakenTrace X0 k) S4 (tshiftTRec (weakenCutoffty C0 k) SS)) = SS) with
      | (tnil) => eq_refl
      | (tcons l5 T11 TS1) => (f_equal3 tcons eq_refl (tsubst0_tshift0_Ty_reflection_ind T11 k S4) (tsubst0_tshift0_TRec_reflection_ind TS1 k S4))
    end
  with tsubst0_tshift0_Ty_reflection_ind (S5 : Ty) (k : Hvl) (S4 : Ty) {struct S5} :
  ((tsubstTy (weakenTrace X0 k) S4 (tshiftTy (weakenCutoffty C0 k) S5)) = S5) :=
    match S5 return ((tsubstTy (weakenTrace X0 k) S4 (tshiftTy (weakenCutoffty C0 k) S5)) = S5) with
      | (tvar X7) => (tsubstIndex0_tshiftIndex0_reflection_ind S4 k X7)
      | (top) => eq_refl
      | (tarr T12 T13) => (f_equal2 tarr (tsubst0_tshift0_Ty_reflection_ind T12 k S4) (tsubst0_tshift0_Ty_reflection_ind T13 k S4))
      | (tall T12 T13) => (f_equal2 tall (tsubst0_tshift0_Ty_reflection_ind T12 k S4) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T13 (HS ty k) S4)))
      | (trec TS2) => (f_equal trec (tsubst0_tshift0_TRec_reflection_ind TS2 k S4))
    end.
  Fixpoint tsubst0_tshift0_Pat_reflection_ind (p10 : Pat) (k : Hvl) (S4 : Ty) {struct p10} :
  ((tsubstPat (weakenTrace X0 k) S4 (tshiftPat (weakenCutoffty C0 k) p10)) = p10) :=
    match p10 return ((tsubstPat (weakenTrace X0 k) S4 (tshiftPat (weakenCutoffty C0 k) p10)) = p10) with
      | (pvar T11) => (f_equal pvar (tsubst0_tshift0_Ty_reflection_ind T11 k S4))
      | (prec ps10) => (f_equal prec (tsubst0_tshift0_PRec_reflection_ind ps10 k S4))
    end
  with tsubst0_tshift0_PRec_reflection_ind (ps11 : PRec) (k : Hvl) (S4 : Ty) {struct ps11} :
  ((tsubstPRec (weakenTrace X0 k) S4 (tshiftPRec (weakenCutoffty C0 k) ps11)) = ps11) :=
    match ps11 return ((tsubstPRec (weakenTrace X0 k) S4 (tshiftPRec (weakenCutoffty C0 k) ps11)) = ps11) with
      | (pnil) => eq_refl
      | (pcons l5 p11 ps12) => (f_equal3 pcons eq_refl (tsubst0_tshift0_Pat_reflection_ind p11 k S4) (eq_trans (f_equal3 tsubstPRec (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p11)))) eq_refl (f_equal2 tshiftPRec (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p11))) eq_refl)) (tsubst0_tshift0_PRec_reflection_ind ps12 (appendHvl k (appendHvl H0 (bindPat p11))) S4)))
    end.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) with
      | (var x6) => (substIndex0_shiftIndex0_reflection_ind s k x6)
      | (abs T11 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t8 (HS tm k) s)))
      | (app t9 t10) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t9 k s) (subst0_shift0_Tm_reflection_ind t10 k s))
      | (tabs T11 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t8 (HS ty k) s)))
      | (tapp t8 T11) => (f_equal2 tapp (subst0_shift0_Tm_reflection_ind t8 k s) eq_refl)
      | (rec ts1) => (f_equal rec (subst0_shift0_Rec_reflection_ind ts1 k s))
      | (prj t8 l5) => (f_equal2 prj (subst0_shift0_Tm_reflection_ind t8 k s) eq_refl)
      | (lett p10 t9 t10) => (f_equal3 lett eq_refl (subst0_shift0_Tm_reflection_ind t9 k s) (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p10))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p10))) eq_refl)) (subst0_shift0_Tm_reflection_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) s)))
    end
  with subst0_shift0_Rec_reflection_ind (ss : Rec) (k : Hvl) (s : Tm) {struct ss} :
  ((substRec (weakenTrace X0 k) s (shiftRec (weakenCutofftm C0 k) ss)) = ss) :=
    match ss return ((substRec (weakenTrace X0 k) s (shiftRec (weakenCutofftm C0 k) ss)) = ss) with
      | (rnil) => eq_refl
      | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (subst0_shift0_Tm_reflection_ind t11 k s) (subst0_shift0_Rec_reflection_ind ts2 k s))
    end.
  Fixpoint tsubst0_tshift0_Tm_reflection_ind (s : Tm) (k : Hvl) (S4 : Ty) {struct s} :
  ((tsubstTm (weakenTrace X0 k) S4 (tshiftTm (weakenCutoffty C0 k) s)) = s) :=
    match s return ((tsubstTm (weakenTrace X0 k) S4 (tshiftTm (weakenCutoffty C0 k) s)) = s) with
      | (var x6) => eq_refl
      | (abs T11 t8) => (f_equal2 abs (tsubst0_tshift0_Ty_reflection_ind T11 k S4) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t8 (HS tm k) S4)))
      | (app t9 t10) => (f_equal2 app (tsubst0_tshift0_Tm_reflection_ind t9 k S4) (tsubst0_tshift0_Tm_reflection_ind t10 k S4))
      | (tabs T11 t8) => (f_equal2 tabs (tsubst0_tshift0_Ty_reflection_ind T11 k S4) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t8 (HS ty k) S4)))
      | (tapp t8 T11) => (f_equal2 tapp (tsubst0_tshift0_Tm_reflection_ind t8 k S4) (tsubst0_tshift0_Ty_reflection_ind T11 k S4))
      | (rec ts1) => (f_equal rec (tsubst0_tshift0_Rec_reflection_ind ts1 k S4))
      | (prj t8 l5) => (f_equal2 prj (tsubst0_tshift0_Tm_reflection_ind t8 k S4) eq_refl)
      | (lett p10 t9 t10) => (f_equal3 lett (tsubst0_tshift0_Pat_reflection_ind p10 k S4) (tsubst0_tshift0_Tm_reflection_ind t9 k S4) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p10)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p10))) eq_refl)) (tsubst0_tshift0_Tm_reflection_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) S4)))
    end
  with tsubst0_tshift0_Rec_reflection_ind (ss : Rec) (k : Hvl) (S4 : Ty) {struct ss} :
  ((tsubstRec (weakenTrace X0 k) S4 (tshiftRec (weakenCutoffty C0 k) ss)) = ss) :=
    match ss return ((tsubstRec (weakenTrace X0 k) S4 (tshiftRec (weakenCutoffty C0 k) ss)) = ss) with
      | (rnil) => eq_refl
      | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (tsubst0_tshift0_Tm_reflection_ind t11 k S4) (tsubst0_tshift0_Rec_reflection_ind ts2 k S4))
    end.
  Definition tsubstTRec0_tshiftTRec0_reflection (SS : TRec) : (forall (S4 : Ty) ,
    ((tsubstTRec X0 S4 (tshiftTRec C0 SS)) = SS)) := (tsubst0_tshift0_TRec_reflection_ind SS H0).
  Definition tsubstTy0_tshiftTy0_reflection (S5 : Ty) : (forall (S4 : Ty) ,
    ((tsubstTy X0 S4 (tshiftTy C0 S5)) = S5)) := (tsubst0_tshift0_Ty_reflection_ind S5 H0).
  Definition tsubstPat0_tshiftPat0_reflection (p10 : Pat) : (forall (S4 : Ty) ,
    ((tsubstPat X0 S4 (tshiftPat C0 p10)) = p10)) := (tsubst0_tshift0_Pat_reflection_ind p10 H0).
  Definition tsubstPRec0_tshiftPRec0_reflection (ps10 : PRec) : (forall (S4 : Ty) ,
    ((tsubstPRec X0 S4 (tshiftPRec C0 ps10)) = ps10)) := (tsubst0_tshift0_PRec_reflection_ind ps10 H0).
  Definition substTm0_shiftTm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((substTm X0 s (shiftTm C0 s0)) = s0)) := (subst0_shift0_Tm_reflection_ind s0 H0).
  Definition substRec0_shiftRec0_reflection (ss : Rec) : (forall (s : Tm) ,
    ((substRec X0 s (shiftRec C0 ss)) = ss)) := (subst0_shift0_Rec_reflection_ind ss H0).
  Definition tsubstTm0_tshiftTm0_reflection (s : Tm) : (forall (S4 : Ty) ,
    ((tsubstTm X0 S4 (tshiftTm C0 s)) = s)) := (tsubst0_tshift0_Tm_reflection_ind s H0).
  Definition tsubstRec0_tshiftRec0_reflection (ss : Rec) : (forall (S4 : Ty) ,
    ((tsubstRec X0 S4 (tshiftRec C0 ss)) = ss)) := (tsubst0_tshift0_Rec_reflection_ind ss H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c3 : (Cutoff tm)) (x6 : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c3) k) (shiftIndex (weakenCutofftm C0 k) x6)) = (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c3 k) x6)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c3 : (Cutoff ty)) (X7 : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c3) k) (tshiftIndex (weakenCutoffty C0 k) X7)) = (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c3 k) X7)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint tshift_tshift0_TRec_comm_ind (SS : TRec) (k : Hvl) (c3 : (Cutoff ty)) {struct SS} :
    ((tshiftTRec (weakenCutoffty (CS c3) k) (tshiftTRec (weakenCutoffty C0 k) SS)) = (tshiftTRec (weakenCutoffty C0 k) (tshiftTRec (weakenCutoffty c3 k) SS))) :=
      match SS return ((tshiftTRec (weakenCutoffty (CS c3) k) (tshiftTRec (weakenCutoffty C0 k) SS)) = (tshiftTRec (weakenCutoffty C0 k) (tshiftTRec (weakenCutoffty c3 k) SS))) with
        | (tnil) => eq_refl
        | (tcons l5 T11 TS1) => (f_equal3 tcons eq_refl (tshift_tshift0_Ty_comm_ind T11 k c3) (tshift_tshift0_TRec_comm_ind TS1 k c3))
      end
    with tshift_tshift0_Ty_comm_ind (S4 : Ty) (k : Hvl) (c3 : (Cutoff ty)) {struct S4} :
    ((tshiftTy (weakenCutoffty (CS c3) k) (tshiftTy (weakenCutoffty C0 k) S4)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c3 k) S4))) :=
      match S4 return ((tshiftTy (weakenCutoffty (CS c3) k) (tshiftTy (weakenCutoffty C0 k) S4)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c3 k) S4))) with
        | (tvar X7) => (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k c3 X7))
        | (top) => eq_refl
        | (tarr T12 T13) => (f_equal2 tarr (tshift_tshift0_Ty_comm_ind T12 k c3) (tshift_tshift0_Ty_comm_ind T13 k c3))
        | (tall T12 T13) => (f_equal2 tall (tshift_tshift0_Ty_comm_ind T12 k c3) (tshift_tshift0_Ty_comm_ind T13 (HS ty k) c3))
        | (trec TS2) => (f_equal trec (tshift_tshift0_TRec_comm_ind TS2 k c3))
      end.
    Fixpoint tshift_tshift0_Pat_comm_ind (p10 : Pat) (k : Hvl) (c3 : (Cutoff ty)) {struct p10} :
    ((tshiftPat (weakenCutoffty (CS c3) k) (tshiftPat (weakenCutoffty C0 k) p10)) = (tshiftPat (weakenCutoffty C0 k) (tshiftPat (weakenCutoffty c3 k) p10))) :=
      match p10 return ((tshiftPat (weakenCutoffty (CS c3) k) (tshiftPat (weakenCutoffty C0 k) p10)) = (tshiftPat (weakenCutoffty C0 k) (tshiftPat (weakenCutoffty c3 k) p10))) with
        | (pvar T11) => (f_equal pvar (tshift_tshift0_Ty_comm_ind T11 k c3))
        | (prec ps10) => (f_equal prec (tshift_tshift0_PRec_comm_ind ps10 k c3))
      end
    with tshift_tshift0_PRec_comm_ind (ps11 : PRec) (k : Hvl) (c3 : (Cutoff ty)) {struct ps11} :
    ((tshiftPRec (weakenCutoffty (CS c3) k) (tshiftPRec (weakenCutoffty C0 k) ps11)) = (tshiftPRec (weakenCutoffty C0 k) (tshiftPRec (weakenCutoffty c3 k) ps11))) :=
      match ps11 return ((tshiftPRec (weakenCutoffty (CS c3) k) (tshiftPRec (weakenCutoffty C0 k) ps11)) = (tshiftPRec (weakenCutoffty C0 k) (tshiftPRec (weakenCutoffty c3 k) ps11))) with
        | (pnil) => eq_refl
        | (pcons l5 p11 ps12) => (f_equal3 pcons eq_refl (tshift_tshift0_Pat_comm_ind p11 k c3) (eq_trans (f_equal2 tshiftPRec (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutoffty_append (CS c3) k (appendHvl H0 (bindPat p11)))) (f_equal2 tshiftPRec (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p11))) eq_refl)) (eq_trans (tshift_tshift0_PRec_comm_ind ps12 (appendHvl k (appendHvl H0 (bindPat p11))) c3) (f_equal2 tshiftPRec (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p11)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftPRec (eq_sym (weakenCutoffty_append c3 k (appendHvl H0 (bindPat p11)))) eq_refl)))))
      end.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c3 : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm (CS c3) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c3 k) s))) :=
      match s return ((shiftTm (weakenCutofftm (CS c3) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c3 k) s))) with
        | (var x6) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c3 x6))
        | (abs T11 t8) => (f_equal2 abs eq_refl (shift_shift0_Tm_comm_ind t8 (HS tm k) c3))
        | (app t9 t10) => (f_equal2 app (shift_shift0_Tm_comm_ind t9 k c3) (shift_shift0_Tm_comm_ind t10 k c3))
        | (tabs T11 t8) => (f_equal2 tabs eq_refl (shift_shift0_Tm_comm_ind t8 (HS ty k) c3))
        | (tapp t8 T11) => (f_equal2 tapp (shift_shift0_Tm_comm_ind t8 k c3) eq_refl)
        | (rec ts1) => (f_equal rec (shift_shift0_Rec_comm_ind ts1 k c3))
        | (prj t8 l5) => (f_equal2 prj (shift_shift0_Tm_comm_ind t8 k c3) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett eq_refl (shift_shift0_Tm_comm_ind t9 k c3) (eq_trans (f_equal2 shiftTm (weakenCutofftm_append (CS c3) k (appendHvl H0 (bindPat p10))) (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p10))) eq_refl)) (eq_trans (shift_shift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) c3) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p10)))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c3 k (appendHvl H0 (bindPat p10)))) eq_refl)))))
      end
    with shift_shift0_Rec_comm_ind (ss : Rec) (k : Hvl) (c3 : (Cutoff tm)) {struct ss} :
    ((shiftRec (weakenCutofftm (CS c3) k) (shiftRec (weakenCutofftm C0 k) ss)) = (shiftRec (weakenCutofftm C0 k) (shiftRec (weakenCutofftm c3 k) ss))) :=
      match ss return ((shiftRec (weakenCutofftm (CS c3) k) (shiftRec (weakenCutofftm C0 k) ss)) = (shiftRec (weakenCutofftm C0 k) (shiftRec (weakenCutofftm c3 k) ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (shift_shift0_Tm_comm_ind t11 k c3) (shift_shift0_Rec_comm_ind ts2 k c3))
      end.
    Fixpoint shift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c3 : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm c3 k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c3 k) s))) :=
      match s return ((shiftTm (weakenCutofftm c3 k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c3 k) s))) with
        | (var x6) => eq_refl
        | (abs T11 t8) => (f_equal2 abs eq_refl (shift_tshift0_Tm_comm_ind t8 (HS tm k) c3))
        | (app t9 t10) => (f_equal2 app (shift_tshift0_Tm_comm_ind t9 k c3) (shift_tshift0_Tm_comm_ind t10 k c3))
        | (tabs T11 t8) => (f_equal2 tabs eq_refl (shift_tshift0_Tm_comm_ind t8 (HS ty k) c3))
        | (tapp t8 T11) => (f_equal2 tapp (shift_tshift0_Tm_comm_ind t8 k c3) eq_refl)
        | (rec ts1) => (f_equal rec (shift_tshift0_Rec_comm_ind ts1 k c3))
        | (prj t8 l5) => (f_equal2 prj (shift_tshift0_Tm_comm_ind t8 k c3) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett eq_refl (shift_tshift0_Tm_comm_ind t9 k c3) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutofftm_append c3 k (appendHvl H0 (bindPat p10)))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p10))) eq_refl)) (eq_trans (shift_tshift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) c3) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p10)))) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c3 k (appendHvl H0 (bindPat p10)))) eq_refl)))))
      end
    with shift_tshift0_Rec_comm_ind (ss : Rec) (k : Hvl) (c3 : (Cutoff tm)) {struct ss} :
    ((shiftRec (weakenCutofftm c3 k) (tshiftRec (weakenCutoffty C0 k) ss)) = (tshiftRec (weakenCutoffty C0 k) (shiftRec (weakenCutofftm c3 k) ss))) :=
      match ss return ((shiftRec (weakenCutofftm c3 k) (tshiftRec (weakenCutoffty C0 k) ss)) = (tshiftRec (weakenCutoffty C0 k) (shiftRec (weakenCutofftm c3 k) ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (shift_tshift0_Tm_comm_ind t11 k c3) (shift_tshift0_Rec_comm_ind ts2 k c3))
      end.
    Fixpoint tshift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c3 : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty c3 k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c3 k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c3 k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c3 k) s))) with
        | (var x6) => eq_refl
        | (abs T11 t8) => (f_equal2 abs eq_refl (tshift_shift0_Tm_comm_ind t8 (HS tm k) c3))
        | (app t9 t10) => (f_equal2 app (tshift_shift0_Tm_comm_ind t9 k c3) (tshift_shift0_Tm_comm_ind t10 k c3))
        | (tabs T11 t8) => (f_equal2 tabs eq_refl (tshift_shift0_Tm_comm_ind t8 (HS ty k) c3))
        | (tapp t8 T11) => (f_equal2 tapp (tshift_shift0_Tm_comm_ind t8 k c3) eq_refl)
        | (rec ts1) => (f_equal rec (tshift_shift0_Rec_comm_ind ts1 k c3))
        | (prj t8 l5) => (f_equal2 prj (tshift_shift0_Tm_comm_ind t8 k c3) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett eq_refl (tshift_shift0_Tm_comm_ind t9 k c3) (eq_trans (f_equal2 tshiftTm (weakenCutoffty_append c3 k (appendHvl H0 (bindPat p10))) (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p10))) eq_refl)) (eq_trans (tshift_shift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) c3) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p10)))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c3 k (appendHvl H0 (bindPat p10)))) eq_refl)))))
      end
    with tshift_shift0_Rec_comm_ind (ss : Rec) (k : Hvl) (c3 : (Cutoff ty)) {struct ss} :
    ((tshiftRec (weakenCutoffty c3 k) (shiftRec (weakenCutofftm C0 k) ss)) = (shiftRec (weakenCutofftm C0 k) (tshiftRec (weakenCutoffty c3 k) ss))) :=
      match ss return ((tshiftRec (weakenCutoffty c3 k) (shiftRec (weakenCutofftm C0 k) ss)) = (shiftRec (weakenCutofftm C0 k) (tshiftRec (weakenCutoffty c3 k) ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (tshift_shift0_Tm_comm_ind t11 k c3) (tshift_shift0_Rec_comm_ind ts2 k c3))
      end.
    Fixpoint tshift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c3 : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty (CS c3) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c3 k) s))) :=
      match s return ((tshiftTm (weakenCutoffty (CS c3) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c3 k) s))) with
        | (var x6) => eq_refl
        | (abs T11 t8) => (f_equal2 abs (tshift_tshift0_Ty_comm_ind T11 k c3) (tshift_tshift0_Tm_comm_ind t8 (HS tm k) c3))
        | (app t9 t10) => (f_equal2 app (tshift_tshift0_Tm_comm_ind t9 k c3) (tshift_tshift0_Tm_comm_ind t10 k c3))
        | (tabs T11 t8) => (f_equal2 tabs (tshift_tshift0_Ty_comm_ind T11 k c3) (tshift_tshift0_Tm_comm_ind t8 (HS ty k) c3))
        | (tapp t8 T11) => (f_equal2 tapp (tshift_tshift0_Tm_comm_ind t8 k c3) (tshift_tshift0_Ty_comm_ind T11 k c3))
        | (rec ts1) => (f_equal rec (tshift_tshift0_Rec_comm_ind ts1 k c3))
        | (prj t8 l5) => (f_equal2 prj (tshift_tshift0_Tm_comm_ind t8 k c3) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett (tshift_tshift0_Pat_comm_ind p10 k c3) (tshift_tshift0_Tm_comm_ind t9 k c3) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenCutoffty_append (CS c3) k (appendHvl H0 (bindPat p10)))) (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p10))) eq_refl)) (eq_trans (tshift_tshift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) c3) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p10)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c3 k (appendHvl H0 (bindPat p10)))) eq_refl)))))
      end
    with tshift_tshift0_Rec_comm_ind (ss : Rec) (k : Hvl) (c3 : (Cutoff ty)) {struct ss} :
    ((tshiftRec (weakenCutoffty (CS c3) k) (tshiftRec (weakenCutoffty C0 k) ss)) = (tshiftRec (weakenCutoffty C0 k) (tshiftRec (weakenCutoffty c3 k) ss))) :=
      match ss return ((tshiftRec (weakenCutoffty (CS c3) k) (tshiftRec (weakenCutoffty C0 k) ss)) = (tshiftRec (weakenCutoffty C0 k) (tshiftRec (weakenCutoffty c3 k) ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (tshift_tshift0_Tm_comm_ind t11 k c3) (tshift_tshift0_Rec_comm_ind ts2 k c3))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_TRec_comm (SS : TRec) : (forall (c3 : (Cutoff ty)) ,
      ((tshiftTRec (CS c3) (tshiftTRec C0 SS)) = (tshiftTRec C0 (tshiftTRec c3 SS)))) := (tshift_tshift0_TRec_comm_ind SS H0).
    Definition tshift_tshift0_Ty_comm (S4 : Ty) : (forall (c3 : (Cutoff ty)) ,
      ((tshiftTy (CS c3) (tshiftTy C0 S4)) = (tshiftTy C0 (tshiftTy c3 S4)))) := (tshift_tshift0_Ty_comm_ind S4 H0).
    Definition tshift_tshift0_Pat_comm (p10 : Pat) : (forall (c3 : (Cutoff ty)) ,
      ((tshiftPat (CS c3) (tshiftPat C0 p10)) = (tshiftPat C0 (tshiftPat c3 p10)))) := (tshift_tshift0_Pat_comm_ind p10 H0).
    Definition tshift_tshift0_PRec_comm (ps10 : PRec) : (forall (c3 : (Cutoff ty)) ,
      ((tshiftPRec (CS c3) (tshiftPRec C0 ps10)) = (tshiftPRec C0 (tshiftPRec c3 ps10)))) := (tshift_tshift0_PRec_comm_ind ps10 H0).
    Definition shift_shift0_Tm_comm (s : Tm) : (forall (c3 : (Cutoff tm)) ,
      ((shiftTm (CS c3) (shiftTm C0 s)) = (shiftTm C0 (shiftTm c3 s)))) := (shift_shift0_Tm_comm_ind s H0).
    Definition shift_shift0_Rec_comm (ss : Rec) : (forall (c3 : (Cutoff tm)) ,
      ((shiftRec (CS c3) (shiftRec C0 ss)) = (shiftRec C0 (shiftRec c3 ss)))) := (shift_shift0_Rec_comm_ind ss H0).
    Definition shift_tshift0_Tm_comm (s : Tm) : (forall (c3 : (Cutoff tm)) ,
      ((shiftTm c3 (tshiftTm C0 s)) = (tshiftTm C0 (shiftTm c3 s)))) := (shift_tshift0_Tm_comm_ind s H0).
    Definition shift_tshift0_Rec_comm (ss : Rec) : (forall (c3 : (Cutoff tm)) ,
      ((shiftRec c3 (tshiftRec C0 ss)) = (tshiftRec C0 (shiftRec c3 ss)))) := (shift_tshift0_Rec_comm_ind ss H0).
    Definition tshift_shift0_Tm_comm (s : Tm) : (forall (c3 : (Cutoff ty)) ,
      ((tshiftTm c3 (shiftTm C0 s)) = (shiftTm C0 (tshiftTm c3 s)))) := (tshift_shift0_Tm_comm_ind s H0).
    Definition tshift_shift0_Rec_comm (ss : Rec) : (forall (c3 : (Cutoff ty)) ,
      ((tshiftRec c3 (shiftRec C0 ss)) = (shiftRec C0 (tshiftRec c3 ss)))) := (tshift_shift0_Rec_comm_ind ss H0).
    Definition tshift_tshift0_Tm_comm (s : Tm) : (forall (c3 : (Cutoff ty)) ,
      ((tshiftTm (CS c3) (tshiftTm C0 s)) = (tshiftTm C0 (tshiftTm c3 s)))) := (tshift_tshift0_Tm_comm_ind s H0).
    Definition tshift_tshift0_Rec_comm (ss : Rec) : (forall (c3 : (Cutoff ty)) ,
      ((tshiftRec (CS c3) (tshiftRec C0 ss)) = (tshiftRec C0 (tshiftRec c3 ss)))) := (tshift_tshift0_Rec_comm_ind ss H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite tshift_tshift0_PRec_comm tshift_tshift0_Pat_comm shift_shift0_Rec_comm shift_tshift0_Rec_comm tshift_shift0_Rec_comm tshift_tshift0_Rec_comm tshift_tshift0_TRec_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : interaction.
 Hint Rewrite tshift_tshift0_PRec_comm tshift_tshift0_Pat_comm shift_shift0_Rec_comm shift_tshift0_Rec_comm tshift_shift0_Rec_comm tshift_tshift0_Rec_comm tshift_tshift0_TRec_comm shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTRec_tshiftTRec  :
    (forall (k : Hvl) (c3 : (Cutoff ty)) (SS : TRec) ,
      ((weakenTRec (tshiftTRec c3 SS) k) = (tshiftTRec (weakenCutoffty c3 k) (weakenTRec SS k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTy_tshiftTy  :
    (forall (k : Hvl) (c3 : (Cutoff ty)) (S4 : Ty) ,
      ((weakenTy (tshiftTy c3 S4) k) = (tshiftTy (weakenCutoffty c3 k) (weakenTy S4 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenPat_tshiftPat  :
    (forall (k : Hvl) (c3 : (Cutoff ty)) (p10 : Pat) ,
      ((weakenPat (tshiftPat c3 p10) k) = (tshiftPat (weakenCutoffty c3 k) (weakenPat p10 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenPRec_tshiftPRec  :
    (forall (k : Hvl) (c3 : (Cutoff ty)) (ps10 : PRec) ,
      ((weakenPRec (tshiftPRec c3 ps10) k) = (tshiftPRec (weakenCutoffty c3 k) (weakenPRec ps10 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k : Hvl) (c3 : (Cutoff tm)) (s : Tm) ,
      ((weakenTm (shiftTm c3 s) k) = (shiftTm (weakenCutofftm c3 k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenRec_shiftRec  :
    (forall (k : Hvl) (c3 : (Cutoff tm)) (ss : Rec) ,
      ((weakenRec (shiftRec c3 ss) k) = (shiftRec (weakenCutofftm c3 k) (weakenRec ss k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k : Hvl) (c3 : (Cutoff ty)) (s : Tm) ,
      ((weakenTm (tshiftTm c3 s) k) = (tshiftTm (weakenCutoffty c3 k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenRec_tshiftRec  :
    (forall (k : Hvl) (c3 : (Cutoff ty)) (ss : Rec) ,
      ((weakenRec (tshiftRec c3 ss) k) = (tshiftRec (weakenCutoffty c3 k) (weakenRec ss k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTm_substIndex0_comm_ind (c3 : (Cutoff tm)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c3 k) (substIndex (weakenTrace X0 k) s x6)) = (substIndex (weakenTrace X0 k) (shiftTm c3 s) (shiftIndex (weakenCutofftm (CS c3) k) x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_substIndex0_comm_ind (c3 : (Cutoff ty)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((tshiftTm (weakenCutoffty c3 k) (substIndex (weakenTrace X0 k) s x6)) = (substIndex (weakenTrace X0 k) (tshiftTm c3 s) x6))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTy_tsubstIndex0_comm_ind (c3 : (Cutoff ty)) (S4 : Ty) :
      (forall (k : Hvl) (X7 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c3 k) (tsubstIndex (weakenTrace X0 k) S4 X7)) = (tsubstIndex (weakenTrace X0 k) (tshiftTy c3 S4) (tshiftIndex (weakenCutoffty (CS c3) k) X7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint tshift_tsubst0_TRec_comm_ind (SS : TRec) (k : Hvl) (c3 : (Cutoff ty)) (S4 : Ty) {struct SS} :
    ((tshiftTRec (weakenCutoffty c3 k) (tsubstTRec (weakenTrace X0 k) S4 SS)) = (tsubstTRec (weakenTrace X0 k) (tshiftTy c3 S4) (tshiftTRec (weakenCutoffty (CS c3) k) SS))) :=
      match SS return ((tshiftTRec (weakenCutoffty c3 k) (tsubstTRec (weakenTrace X0 k) S4 SS)) = (tsubstTRec (weakenTrace X0 k) (tshiftTy c3 S4) (tshiftTRec (weakenCutoffty (CS c3) k) SS))) with
        | (tnil) => eq_refl
        | (tcons l5 T11 TS1) => (f_equal3 tcons eq_refl (tshift_tsubst0_Ty_comm_ind T11 k c3 S4) (tshift_tsubst0_TRec_comm_ind TS1 k c3 S4))
      end
    with tshift_tsubst0_Ty_comm_ind (S5 : Ty) (k : Hvl) (c3 : (Cutoff ty)) (S4 : Ty) {struct S5} :
    ((tshiftTy (weakenCutoffty c3 k) (tsubstTy (weakenTrace X0 k) S4 S5)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c3 S4) (tshiftTy (weakenCutoffty (CS c3) k) S5))) :=
      match S5 return ((tshiftTy (weakenCutoffty c3 k) (tsubstTy (weakenTrace X0 k) S4 S5)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c3 S4) (tshiftTy (weakenCutoffty (CS c3) k) S5))) with
        | (tvar X7) => (tshiftTy_tsubstIndex0_comm_ind c3 S4 k X7)
        | (top) => eq_refl
        | (tarr T12 T13) => (f_equal2 tarr (tshift_tsubst0_Ty_comm_ind T12 k c3 S4) (tshift_tsubst0_Ty_comm_ind T13 k c3 S4))
        | (tall T12 T13) => (f_equal2 tall (tshift_tsubst0_Ty_comm_ind T12 k c3 S4) (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T13 (HS ty k) c3 S4) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (trec TS2) => (f_equal trec (tshift_tsubst0_TRec_comm_ind TS2 k c3 S4))
      end.
    Fixpoint tshift_tsubst0_Pat_comm_ind (p10 : Pat) (k : Hvl) (c3 : (Cutoff ty)) (S4 : Ty) {struct p10} :
    ((tshiftPat (weakenCutoffty c3 k) (tsubstPat (weakenTrace X0 k) S4 p10)) = (tsubstPat (weakenTrace X0 k) (tshiftTy c3 S4) (tshiftPat (weakenCutoffty (CS c3) k) p10))) :=
      match p10 return ((tshiftPat (weakenCutoffty c3 k) (tsubstPat (weakenTrace X0 k) S4 p10)) = (tsubstPat (weakenTrace X0 k) (tshiftTy c3 S4) (tshiftPat (weakenCutoffty (CS c3) k) p10))) with
        | (pvar T11) => (f_equal pvar (tshift_tsubst0_Ty_comm_ind T11 k c3 S4))
        | (prec ps10) => (f_equal prec (tshift_tsubst0_PRec_comm_ind ps10 k c3 S4))
      end
    with tshift_tsubst0_PRec_comm_ind (ps11 : PRec) (k : Hvl) (c3 : (Cutoff ty)) (S4 : Ty) {struct ps11} :
    ((tshiftPRec (weakenCutoffty c3 k) (tsubstPRec (weakenTrace X0 k) S4 ps11)) = (tsubstPRec (weakenTrace X0 k) (tshiftTy c3 S4) (tshiftPRec (weakenCutoffty (CS c3) k) ps11))) :=
      match ps11 return ((tshiftPRec (weakenCutoffty c3 k) (tsubstPRec (weakenTrace X0 k) S4 ps11)) = (tsubstPRec (weakenTrace X0 k) (tshiftTy c3 S4) (tshiftPRec (weakenCutoffty (CS c3) k) ps11))) with
        | (pnil) => eq_refl
        | (pcons l5 p11 ps12) => (f_equal3 pcons eq_refl (tshift_tsubst0_Pat_comm_ind p11 k c3 S4) (eq_trans (f_equal2 tshiftPRec (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutoffty_append c3 k (appendHvl H0 (bindPat p11)))) (f_equal3 tsubstPRec (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p11))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_PRec_comm_ind ps12 (appendHvl k (appendHvl H0 (bindPat p11))) c3 S4) (f_equal3 tsubstPRec (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p11)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftPRec (eq_sym (weakenCutoffty_append (CS c3) k (appendHvl H0 (bindPat p11)))) eq_refl)))))
      end.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c3 : (Cutoff tm)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutofftm c3 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c3 s) (shiftTm (weakenCutofftm (CS c3) k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c3 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c3 s) (shiftTm (weakenCutofftm (CS c3) k) s0))) with
        | (var x6) => (shiftTm_substIndex0_comm_ind c3 s k x6)
        | (abs T11 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t8 (HS tm k) c3 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t9 t10) => (f_equal2 app (shift_subst0_Tm_comm_ind t9 k c3 s) (shift_subst0_Tm_comm_ind t10 k c3 s))
        | (tabs T11 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t8 (HS ty k) c3 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t8 T11) => (f_equal2 tapp (shift_subst0_Tm_comm_ind t8 k c3 s) eq_refl)
        | (rec ts1) => (f_equal rec (shift_subst0_Rec_comm_ind ts1 k c3 s))
        | (prj t8 l5) => (f_equal2 prj (shift_subst0_Tm_comm_ind t8 k c3 s) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett eq_refl (shift_subst0_Tm_comm_ind t9 k c3 s) (eq_trans (f_equal2 shiftTm (weakenCutofftm_append c3 k (appendHvl H0 (bindPat p10))) (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p10))) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) c3 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p10)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append (CS c3) k (appendHvl H0 (bindPat p10)))) eq_refl)))))
      end
    with shift_subst0_Rec_comm_ind (ss : Rec) (k : Hvl) (c3 : (Cutoff tm)) (s : Tm) {struct ss} :
    ((shiftRec (weakenCutofftm c3 k) (substRec (weakenTrace X0 k) s ss)) = (substRec (weakenTrace X0 k) (shiftTm c3 s) (shiftRec (weakenCutofftm (CS c3) k) ss))) :=
      match ss return ((shiftRec (weakenCutofftm c3 k) (substRec (weakenTrace X0 k) s ss)) = (substRec (weakenTrace X0 k) (shiftTm c3 s) (shiftRec (weakenCutofftm (CS c3) k) ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (shift_subst0_Tm_comm_ind t11 k c3 s) (shift_subst0_Rec_comm_ind ts2 k c3 s))
      end.
    Fixpoint shift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c3 : (Cutoff tm)) (S4 : Ty) {struct s} :
    ((shiftTm (weakenCutofftm c3 k) (tsubstTm (weakenTrace X0 k) S4 s)) = (tsubstTm (weakenTrace X0 k) S4 (shiftTm (weakenCutofftm c3 k) s))) :=
      match s return ((shiftTm (weakenCutofftm c3 k) (tsubstTm (weakenTrace X0 k) S4 s)) = (tsubstTm (weakenTrace X0 k) S4 (shiftTm (weakenCutofftm c3 k) s))) with
        | (var x6) => eq_refl
        | (abs T11 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t8 (HS tm k) c3 S4) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t9 t10) => (f_equal2 app (shift_tsubst0_Tm_comm_ind t9 k c3 S4) (shift_tsubst0_Tm_comm_ind t10 k c3 S4))
        | (tabs T11 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t8 (HS ty k) c3 S4) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t8 T11) => (f_equal2 tapp (shift_tsubst0_Tm_comm_ind t8 k c3 S4) eq_refl)
        | (rec ts1) => (f_equal rec (shift_tsubst0_Rec_comm_ind ts1 k c3 S4))
        | (prj t8 l5) => (f_equal2 prj (shift_tsubst0_Tm_comm_ind t8 k c3 S4) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett eq_refl (shift_tsubst0_Tm_comm_ind t9 k c3 S4) (eq_trans (f_equal2 shiftTm (eq_trans (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutofftm_append c3 k (appendHvl H0 (bindPat p10)))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p10))) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) c3 S4) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p10)))) eq_refl (f_equal2 shiftTm (eq_sym (weakenCutofftm_append c3 k (appendHvl H0 (bindPat p10)))) eq_refl)))))
      end
    with shift_tsubst0_Rec_comm_ind (ss : Rec) (k : Hvl) (c3 : (Cutoff tm)) (S4 : Ty) {struct ss} :
    ((shiftRec (weakenCutofftm c3 k) (tsubstRec (weakenTrace X0 k) S4 ss)) = (tsubstRec (weakenTrace X0 k) S4 (shiftRec (weakenCutofftm c3 k) ss))) :=
      match ss return ((shiftRec (weakenCutofftm c3 k) (tsubstRec (weakenTrace X0 k) S4 ss)) = (tsubstRec (weakenTrace X0 k) S4 (shiftRec (weakenCutofftm c3 k) ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (shift_tsubst0_Tm_comm_ind t11 k c3 S4) (shift_tsubst0_Rec_comm_ind ts2 k c3 S4))
      end.
    Fixpoint tshift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c3 : (Cutoff ty)) (s : Tm) {struct s0} :
    ((tshiftTm (weakenCutoffty c3 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c3 s) (tshiftTm (weakenCutoffty c3 k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffty c3 k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c3 s) (tshiftTm (weakenCutoffty c3 k) s0))) with
        | (var x6) => (tshiftTm_substIndex0_comm_ind c3 s k x6)
        | (abs T11 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t8 (HS tm k) c3 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t9 t10) => (f_equal2 app (tshift_subst0_Tm_comm_ind t9 k c3 s) (tshift_subst0_Tm_comm_ind t10 k c3 s))
        | (tabs T11 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t8 (HS ty k) c3 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t8 T11) => (f_equal2 tapp (tshift_subst0_Tm_comm_ind t8 k c3 s) eq_refl)
        | (rec ts1) => (f_equal rec (tshift_subst0_Rec_comm_ind ts1 k c3 s))
        | (prj t8 l5) => (f_equal2 prj (tshift_subst0_Tm_comm_ind t8 k c3 s) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett eq_refl (tshift_subst0_Tm_comm_ind t9 k c3 s) (eq_trans (f_equal2 tshiftTm (weakenCutoffty_append c3 k (appendHvl H0 (bindPat p10))) (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p10))) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) c3 s) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p10)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append c3 k (appendHvl H0 (bindPat p10)))) eq_refl)))))
      end
    with tshift_subst0_Rec_comm_ind (ss : Rec) (k : Hvl) (c3 : (Cutoff ty)) (s : Tm) {struct ss} :
    ((tshiftRec (weakenCutoffty c3 k) (substRec (weakenTrace X0 k) s ss)) = (substRec (weakenTrace X0 k) (tshiftTm c3 s) (tshiftRec (weakenCutoffty c3 k) ss))) :=
      match ss return ((tshiftRec (weakenCutoffty c3 k) (substRec (weakenTrace X0 k) s ss)) = (substRec (weakenTrace X0 k) (tshiftTm c3 s) (tshiftRec (weakenCutoffty c3 k) ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (tshift_subst0_Tm_comm_ind t11 k c3 s) (tshift_subst0_Rec_comm_ind ts2 k c3 s))
      end.
    Fixpoint tshift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c3 : (Cutoff ty)) (S4 : Ty) {struct s} :
    ((tshiftTm (weakenCutoffty c3 k) (tsubstTm (weakenTrace X0 k) S4 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c3 S4) (tshiftTm (weakenCutoffty (CS c3) k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c3 k) (tsubstTm (weakenTrace X0 k) S4 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c3 S4) (tshiftTm (weakenCutoffty (CS c3) k) s))) with
        | (var x6) => eq_refl
        | (abs T11 t8) => (f_equal2 abs (tshift_tsubst0_Ty_comm_ind T11 k c3 S4) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t8 (HS tm k) c3 S4) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t9 t10) => (f_equal2 app (tshift_tsubst0_Tm_comm_ind t9 k c3 S4) (tshift_tsubst0_Tm_comm_ind t10 k c3 S4))
        | (tabs T11 t8) => (f_equal2 tabs (tshift_tsubst0_Ty_comm_ind T11 k c3 S4) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t8 (HS ty k) c3 S4) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t8 T11) => (f_equal2 tapp (tshift_tsubst0_Tm_comm_ind t8 k c3 S4) (tshift_tsubst0_Ty_comm_ind T11 k c3 S4))
        | (rec ts1) => (f_equal rec (tshift_tsubst0_Rec_comm_ind ts1 k c3 S4))
        | (prj t8 l5) => (f_equal2 prj (tshift_tsubst0_Tm_comm_ind t8 k c3 S4) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett (tshift_tsubst0_Pat_comm_ind p10 k c3 S4) (tshift_tsubst0_Tm_comm_ind t9 k c3 S4) (eq_trans (f_equal2 tshiftTm (eq_trans (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenCutoffty_append c3 k (appendHvl H0 (bindPat p10)))) (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p10))) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) c3 S4) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p10)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _))))) eq_refl (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append (CS c3) k (appendHvl H0 (bindPat p10)))) eq_refl)))))
      end
    with tshift_tsubst0_Rec_comm_ind (ss : Rec) (k : Hvl) (c3 : (Cutoff ty)) (S4 : Ty) {struct ss} :
    ((tshiftRec (weakenCutoffty c3 k) (tsubstRec (weakenTrace X0 k) S4 ss)) = (tsubstRec (weakenTrace X0 k) (tshiftTy c3 S4) (tshiftRec (weakenCutoffty (CS c3) k) ss))) :=
      match ss return ((tshiftRec (weakenCutoffty c3 k) (tsubstRec (weakenTrace X0 k) S4 ss)) = (tsubstRec (weakenTrace X0 k) (tshiftTy c3 S4) (tshiftRec (weakenCutoffty (CS c3) k) ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (tshift_tsubst0_Tm_comm_ind t11 k c3 S4) (tshift_tsubst0_Rec_comm_ind ts2 k c3 S4))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTRec_tsubstTRec0_comm (SS : TRec) : (forall (c3 : (Cutoff ty)) (S4 : Ty) ,
      ((tshiftTRec c3 (tsubstTRec X0 S4 SS)) = (tsubstTRec X0 (tshiftTy c3 S4) (tshiftTRec (CS c3) SS)))) := (tshift_tsubst0_TRec_comm_ind SS H0).
    Definition tshiftTy_tsubstTy0_comm (S5 : Ty) : (forall (c3 : (Cutoff ty)) (S4 : Ty) ,
      ((tshiftTy c3 (tsubstTy X0 S4 S5)) = (tsubstTy X0 (tshiftTy c3 S4) (tshiftTy (CS c3) S5)))) := (tshift_tsubst0_Ty_comm_ind S5 H0).
    Definition tshiftPat_tsubstPat0_comm (p10 : Pat) : (forall (c3 : (Cutoff ty)) (S4 : Ty) ,
      ((tshiftPat c3 (tsubstPat X0 S4 p10)) = (tsubstPat X0 (tshiftTy c3 S4) (tshiftPat (CS c3) p10)))) := (tshift_tsubst0_Pat_comm_ind p10 H0).
    Definition tshiftPRec_tsubstPRec0_comm (ps10 : PRec) : (forall (c3 : (Cutoff ty)) (S4 : Ty) ,
      ((tshiftPRec c3 (tsubstPRec X0 S4 ps10)) = (tsubstPRec X0 (tshiftTy c3 S4) (tshiftPRec (CS c3) ps10)))) := (tshift_tsubst0_PRec_comm_ind ps10 H0).
    Definition shiftTm_substTm0_comm (s0 : Tm) : (forall (c3 : (Cutoff tm)) (s : Tm) ,
      ((shiftTm c3 (substTm X0 s s0)) = (substTm X0 (shiftTm c3 s) (shiftTm (CS c3) s0)))) := (shift_subst0_Tm_comm_ind s0 H0).
    Definition shiftRec_substRec0_comm (ss : Rec) : (forall (c3 : (Cutoff tm)) (s : Tm) ,
      ((shiftRec c3 (substRec X0 s ss)) = (substRec X0 (shiftTm c3 s) (shiftRec (CS c3) ss)))) := (shift_subst0_Rec_comm_ind ss H0).
    Definition shiftTm_tsubstTm0_comm (s : Tm) : (forall (c3 : (Cutoff tm)) (S4 : Ty) ,
      ((shiftTm c3 (tsubstTm X0 S4 s)) = (tsubstTm X0 S4 (shiftTm c3 s)))) := (shift_tsubst0_Tm_comm_ind s H0).
    Definition shiftRec_tsubstRec0_comm (ss : Rec) : (forall (c3 : (Cutoff tm)) (S4 : Ty) ,
      ((shiftRec c3 (tsubstRec X0 S4 ss)) = (tsubstRec X0 S4 (shiftRec c3 ss)))) := (shift_tsubst0_Rec_comm_ind ss H0).
    Definition tshiftTm_substTm0_comm (s0 : Tm) : (forall (c3 : (Cutoff ty)) (s : Tm) ,
      ((tshiftTm c3 (substTm X0 s s0)) = (substTm X0 (tshiftTm c3 s) (tshiftTm c3 s0)))) := (tshift_subst0_Tm_comm_ind s0 H0).
    Definition tshiftRec_substRec0_comm (ss : Rec) : (forall (c3 : (Cutoff ty)) (s : Tm) ,
      ((tshiftRec c3 (substRec X0 s ss)) = (substRec X0 (tshiftTm c3 s) (tshiftRec c3 ss)))) := (tshift_subst0_Rec_comm_ind ss H0).
    Definition tshiftTm_tsubstTm0_comm (s : Tm) : (forall (c3 : (Cutoff ty)) (S4 : Ty) ,
      ((tshiftTm c3 (tsubstTm X0 S4 s)) = (tsubstTm X0 (tshiftTy c3 S4) (tshiftTm (CS c3) s)))) := (tshift_tsubst0_Tm_comm_ind s H0).
    Definition tshiftRec_tsubstRec0_comm (ss : Rec) : (forall (c3 : (Cutoff ty)) (S4 : Ty) ,
      ((tshiftRec c3 (tsubstRec X0 S4 ss)) = (tsubstRec X0 (tshiftTy c3 S4) (tshiftRec (CS c3) ss)))) := (tshift_tsubst0_Rec_comm_ind ss H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d3 : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d3) k) s (shiftIndex (weakenCutofftm C0 k) x6)) = (shiftTm (weakenCutofftm C0 k) (substIndex (weakenTrace d3 k) s x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d3 : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((substIndex (weakenTrace (XS ty d3) k) s x6) = (tshiftTm (weakenCutoffty C0 k) (substIndex (weakenTrace d3 k) s x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d3 : (Trace ty)) (S4 : Ty) :
      (forall (k : Hvl) (X7 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d3) k) S4 X7) = (tsubstIndex (weakenTrace d3 k) S4 X7))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d3 : (Trace ty)) (S4 : Ty) :
      (forall (k : Hvl) (X7 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d3) k) S4 (tshiftIndex (weakenCutoffty C0 k) X7)) = (tshiftTy (weakenCutoffty C0 k) (tsubstIndex (weakenTrace d3 k) S4 X7)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint tsubst_tshift0_TRec_comm_ind (SS : TRec) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) {struct SS} :
    ((tsubstTRec (weakenTrace (XS ty d3) k) S4 (tshiftTRec (weakenCutoffty C0 k) SS)) = (tshiftTRec (weakenCutoffty C0 k) (tsubstTRec (weakenTrace d3 k) S4 SS))) :=
      match SS return ((tsubstTRec (weakenTrace (XS ty d3) k) S4 (tshiftTRec (weakenCutoffty C0 k) SS)) = (tshiftTRec (weakenCutoffty C0 k) (tsubstTRec (weakenTrace d3 k) S4 SS))) with
        | (tnil) => eq_refl
        | (tcons l5 T11 TS1) => (f_equal3 tcons eq_refl (tsubst_tshift0_Ty_comm_ind T11 k d3 S4) (tsubst_tshift0_TRec_comm_ind TS1 k d3 S4))
      end
    with tsubst_tshift0_Ty_comm_ind (S5 : Ty) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) {struct S5} :
    ((tsubstTy (weakenTrace (XS ty d3) k) S4 (tshiftTy (weakenCutoffty C0 k) S5)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d3 k) S4 S5))) :=
      match S5 return ((tsubstTy (weakenTrace (XS ty d3) k) S4 (tshiftTy (weakenCutoffty C0 k) S5)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d3 k) S4 S5))) with
        | (tvar X7) => (tsubstIndex_tshiftTy0_comm_ind d3 S4 k X7)
        | (top) => eq_refl
        | (tarr T12 T13) => (f_equal2 tarr (tsubst_tshift0_Ty_comm_ind T12 k d3 S4) (tsubst_tshift0_Ty_comm_ind T13 k d3 S4))
        | (tall T12 T13) => (f_equal2 tall (tsubst_tshift0_Ty_comm_ind T12 k d3 S4) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d3) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T13 (HS ty k) d3 S4) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d3 k (HS ty H0))) eq_refl eq_refl)))))
        | (trec TS2) => (f_equal trec (tsubst_tshift0_TRec_comm_ind TS2 k d3 S4))
      end.
    Fixpoint tsubst_tshift0_Pat_comm_ind (p10 : Pat) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) {struct p10} :
    ((tsubstPat (weakenTrace (XS ty d3) k) S4 (tshiftPat (weakenCutoffty C0 k) p10)) = (tshiftPat (weakenCutoffty C0 k) (tsubstPat (weakenTrace d3 k) S4 p10))) :=
      match p10 return ((tsubstPat (weakenTrace (XS ty d3) k) S4 (tshiftPat (weakenCutoffty C0 k) p10)) = (tshiftPat (weakenCutoffty C0 k) (tsubstPat (weakenTrace d3 k) S4 p10))) with
        | (pvar T11) => (f_equal pvar (tsubst_tshift0_Ty_comm_ind T11 k d3 S4))
        | (prec ps10) => (f_equal prec (tsubst_tshift0_PRec_comm_ind ps10 k d3 S4))
      end
    with tsubst_tshift0_PRec_comm_ind (ps11 : PRec) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) {struct ps11} :
    ((tsubstPRec (weakenTrace (XS ty d3) k) S4 (tshiftPRec (weakenCutoffty C0 k) ps11)) = (tshiftPRec (weakenCutoffty C0 k) (tsubstPRec (weakenTrace d3 k) S4 ps11))) :=
      match ps11 return ((tsubstPRec (weakenTrace (XS ty d3) k) S4 (tshiftPRec (weakenCutoffty C0 k) ps11)) = (tshiftPRec (weakenCutoffty C0 k) (tsubstPRec (weakenTrace d3 k) S4 ps11))) with
        | (pnil) => eq_refl
        | (pcons l5 p11 ps12) => (f_equal3 pcons eq_refl (tsubst_tshift0_Pat_comm_ind p11 k d3 S4) (eq_trans (f_equal3 tsubstPRec (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty (XS ty d3) k (appendHvl H0 (bindPat p11)))) eq_refl (f_equal2 tshiftPRec (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p11))) eq_refl)) (eq_trans (tsubst_tshift0_PRec_comm_ind ps12 (appendHvl k (appendHvl H0 (bindPat p11))) d3 S4) (f_equal2 tshiftPRec (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p11)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstPRec (eq_sym (weakenTrace_append ty d3 k (appendHvl H0 (bindPat p11)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d3 : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS tm d3) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d3 k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS tm d3) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d3 k) s s0))) with
        | (var x6) => (substIndex_shiftTm0_comm_ind d3 s k x6)
        | (abs T11 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d3) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t8 (HS tm k) d3 s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d3 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (subst_shift0_Tm_comm_ind t9 k d3 s) (subst_shift0_Tm_comm_ind t10 k d3 s))
        | (tabs T11 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d3) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t8 (HS ty k) d3 s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d3 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t8 T11) => (f_equal2 tapp (subst_shift0_Tm_comm_ind t8 k d3 s) eq_refl)
        | (rec ts1) => (f_equal rec (subst_shift0_Rec_comm_ind ts1 k d3 s))
        | (prj t8 l5) => (f_equal2 prj (subst_shift0_Tm_comm_ind t8 k d3 s) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett eq_refl (subst_shift0_Tm_comm_ind t9 k d3 s) (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d3) k (appendHvl H0 (bindPat p10))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p10))) eq_refl)) (eq_trans (subst_shift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) d3 s) (f_equal2 shiftTm (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p10)))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d3 k (appendHvl H0 (bindPat p10)))) eq_refl eq_refl)))))
      end
    with subst_shift0_Rec_comm_ind (ss : Rec) (k : Hvl) (d3 : (Trace tm)) (s : Tm) {struct ss} :
    ((substRec (weakenTrace (XS tm d3) k) s (shiftRec (weakenCutofftm C0 k) ss)) = (shiftRec (weakenCutofftm C0 k) (substRec (weakenTrace d3 k) s ss))) :=
      match ss return ((substRec (weakenTrace (XS tm d3) k) s (shiftRec (weakenCutofftm C0 k) ss)) = (shiftRec (weakenCutofftm C0 k) (substRec (weakenTrace d3 k) s ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (subst_shift0_Tm_comm_ind t11 k d3 s) (subst_shift0_Rec_comm_ind ts2 k d3 s))
      end.
    Fixpoint subst_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d3 : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS ty d3) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d3 k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS ty d3) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d3 k) s s0))) with
        | (var x6) => (substIndex_tshiftTm0_comm_ind d3 s k x6)
        | (abs T11 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d3) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t8 (HS tm k) d3 s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d3 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (subst_tshift0_Tm_comm_ind t9 k d3 s) (subst_tshift0_Tm_comm_ind t10 k d3 s))
        | (tabs T11 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d3) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t8 (HS ty k) d3 s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d3 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t8 T11) => (f_equal2 tapp (subst_tshift0_Tm_comm_ind t8 k d3 s) eq_refl)
        | (rec ts1) => (f_equal rec (subst_tshift0_Rec_comm_ind ts1 k d3 s))
        | (prj t8 l5) => (f_equal2 prj (subst_tshift0_Tm_comm_ind t8 k d3 s) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett eq_refl (subst_tshift0_Tm_comm_ind t9 k d3 s) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append tm (XS ty d3) k (appendHvl H0 (bindPat p10)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p10))) eq_refl)) (eq_trans (subst_tshift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) d3 s) (f_equal2 tshiftTm (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p10)))) (f_equal3 substTm (eq_sym (weakenTrace_append tm d3 k (appendHvl H0 (bindPat p10)))) eq_refl eq_refl)))))
      end
    with subst_tshift0_Rec_comm_ind (ss : Rec) (k : Hvl) (d3 : (Trace tm)) (s : Tm) {struct ss} :
    ((substRec (weakenTrace (XS ty d3) k) s (tshiftRec (weakenCutoffty C0 k) ss)) = (tshiftRec (weakenCutoffty C0 k) (substRec (weakenTrace d3 k) s ss))) :=
      match ss return ((substRec (weakenTrace (XS ty d3) k) s (tshiftRec (weakenCutoffty C0 k) ss)) = (tshiftRec (weakenCutoffty C0 k) (substRec (weakenTrace d3 k) s ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (subst_tshift0_Tm_comm_ind t11 k d3 s) (subst_tshift0_Rec_comm_ind ts2 k d3 s))
      end.
    Fixpoint tsubst_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d3 k) S4 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d3 k) S4 s))) :=
      match s return ((tsubstTm (weakenTrace d3 k) S4 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d3 k) S4 s))) with
        | (var x6) => eq_refl
        | (abs T11 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d3 k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t8 (HS tm k) d3 S4) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d3 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (tsubst_shift0_Tm_comm_ind t9 k d3 S4) (tsubst_shift0_Tm_comm_ind t10 k d3 S4))
        | (tabs T11 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d3 k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t8 (HS ty k) d3 S4) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d3 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t8 T11) => (f_equal2 tapp (tsubst_shift0_Tm_comm_ind t8 k d3 S4) eq_refl)
        | (rec ts1) => (f_equal rec (tsubst_shift0_Rec_comm_ind ts1 k d3 S4))
        | (prj t8 l5) => (f_equal2 prj (tsubst_shift0_Tm_comm_ind t8 k d3 S4) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett eq_refl (tsubst_shift0_Tm_comm_ind t9 k d3 S4) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d3 k (appendHvl H0 (bindPat p10))) eq_refl (f_equal2 shiftTm (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p10))) eq_refl)) (eq_trans (tsubst_shift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) d3 S4) (f_equal2 shiftTm (eq_trans (eq_sym (weakenCutofftm_append C0 k (appendHvl H0 (bindPat p10)))) (f_equal2 weakenCutofftm eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d3 k (appendHvl H0 (bindPat p10)))) eq_refl eq_refl)))))
      end
    with tsubst_shift0_Rec_comm_ind (ss : Rec) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) {struct ss} :
    ((tsubstRec (weakenTrace d3 k) S4 (shiftRec (weakenCutofftm C0 k) ss)) = (shiftRec (weakenCutofftm C0 k) (tsubstRec (weakenTrace d3 k) S4 ss))) :=
      match ss return ((tsubstRec (weakenTrace d3 k) S4 (shiftRec (weakenCutofftm C0 k) ss)) = (shiftRec (weakenCutofftm C0 k) (tsubstRec (weakenTrace d3 k) S4 ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (tsubst_shift0_Tm_comm_ind t11 k d3 S4) (tsubst_shift0_Rec_comm_ind ts2 k d3 S4))
      end.
    Fixpoint tsubst_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS ty d3) k) S4 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d3 k) S4 s))) :=
      match s return ((tsubstTm (weakenTrace (XS ty d3) k) S4 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d3 k) S4 s))) with
        | (var x6) => eq_refl
        | (abs T11 t8) => (f_equal2 abs (tsubst_tshift0_Ty_comm_ind T11 k d3 S4) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d3) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t8 (HS tm k) d3 S4) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d3 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (tsubst_tshift0_Tm_comm_ind t9 k d3 S4) (tsubst_tshift0_Tm_comm_ind t10 k d3 S4))
        | (tabs T11 t8) => (f_equal2 tabs (tsubst_tshift0_Ty_comm_ind T11 k d3 S4) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d3) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t8 (HS ty k) d3 S4) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d3 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t8 T11) => (f_equal2 tapp (tsubst_tshift0_Tm_comm_ind t8 k d3 S4) (tsubst_tshift0_Ty_comm_ind T11 k d3 S4))
        | (rec ts1) => (f_equal rec (tsubst_tshift0_Rec_comm_ind ts1 k d3 S4))
        | (prj t8 l5) => (f_equal2 prj (tsubst_tshift0_Tm_comm_ind t8 k d3 S4) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett (tsubst_tshift0_Pat_comm_ind p10 k d3 S4) (tsubst_tshift0_Tm_comm_ind t9 k d3 S4) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_tshift_bindPat _ _))) (weakenTrace_append ty (XS ty d3) k (appendHvl H0 (bindPat p10)))) eq_refl (f_equal2 tshiftTm (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p10))) eq_refl)) (eq_trans (tsubst_tshift0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) d3 S4) (f_equal2 tshiftTm (eq_trans (eq_sym (weakenCutoffty_append C0 k (appendHvl H0 (bindPat p10)))) (f_equal2 weakenCutoffty eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d3 k (appendHvl H0 (bindPat p10)))) eq_refl eq_refl)))))
      end
    with tsubst_tshift0_Rec_comm_ind (ss : Rec) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) {struct ss} :
    ((tsubstRec (weakenTrace (XS ty d3) k) S4 (tshiftRec (weakenCutoffty C0 k) ss)) = (tshiftRec (weakenCutoffty C0 k) (tsubstRec (weakenTrace d3 k) S4 ss))) :=
      match ss return ((tsubstRec (weakenTrace (XS ty d3) k) S4 (tshiftRec (weakenCutoffty C0 k) ss)) = (tshiftRec (weakenCutoffty C0 k) (tsubstRec (weakenTrace d3 k) S4 ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (tsubst_tshift0_Tm_comm_ind t11 k d3 S4) (tsubst_tshift0_Rec_comm_ind ts2 k d3 S4))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTRec_tshiftTRec0_comm (SS : TRec) : (forall (d3 : (Trace ty)) (S4 : Ty) ,
      ((tsubstTRec (XS ty d3) S4 (tshiftTRec C0 SS)) = (tshiftTRec C0 (tsubstTRec d3 S4 SS)))) := (tsubst_tshift0_TRec_comm_ind SS H0).
    Definition tsubstTy_tshiftTy0_comm (S5 : Ty) : (forall (d3 : (Trace ty)) (S4 : Ty) ,
      ((tsubstTy (XS ty d3) S4 (tshiftTy C0 S5)) = (tshiftTy C0 (tsubstTy d3 S4 S5)))) := (tsubst_tshift0_Ty_comm_ind S5 H0).
    Definition tsubstPat_tshiftPat0_comm (p10 : Pat) : (forall (d3 : (Trace ty)) (S4 : Ty) ,
      ((tsubstPat (XS ty d3) S4 (tshiftPat C0 p10)) = (tshiftPat C0 (tsubstPat d3 S4 p10)))) := (tsubst_tshift0_Pat_comm_ind p10 H0).
    Definition tsubstPRec_tshiftPRec0_comm (ps10 : PRec) : (forall (d3 : (Trace ty)) (S4 : Ty) ,
      ((tsubstPRec (XS ty d3) S4 (tshiftPRec C0 ps10)) = (tshiftPRec C0 (tsubstPRec d3 S4 ps10)))) := (tsubst_tshift0_PRec_comm_ind ps10 H0).
    Definition substTm_shiftTm0_comm (s0 : Tm) : (forall (d3 : (Trace tm)) (s : Tm) ,
      ((substTm (XS tm d3) s (shiftTm C0 s0)) = (shiftTm C0 (substTm d3 s s0)))) := (subst_shift0_Tm_comm_ind s0 H0).
    Definition substRec_shiftRec0_comm (ss : Rec) : (forall (d3 : (Trace tm)) (s : Tm) ,
      ((substRec (XS tm d3) s (shiftRec C0 ss)) = (shiftRec C0 (substRec d3 s ss)))) := (subst_shift0_Rec_comm_ind ss H0).
    Definition substTm_tshiftTm0_comm (s0 : Tm) : (forall (d3 : (Trace tm)) (s : Tm) ,
      ((substTm (XS ty d3) s (tshiftTm C0 s0)) = (tshiftTm C0 (substTm d3 s s0)))) := (subst_tshift0_Tm_comm_ind s0 H0).
    Definition substRec_tshiftRec0_comm (ss : Rec) : (forall (d3 : (Trace tm)) (s : Tm) ,
      ((substRec (XS ty d3) s (tshiftRec C0 ss)) = (tshiftRec C0 (substRec d3 s ss)))) := (subst_tshift0_Rec_comm_ind ss H0).
    Definition tsubstTm_shiftTm0_comm (s : Tm) : (forall (d3 : (Trace ty)) (S4 : Ty) ,
      ((tsubstTm d3 S4 (shiftTm C0 s)) = (shiftTm C0 (tsubstTm d3 S4 s)))) := (tsubst_shift0_Tm_comm_ind s H0).
    Definition tsubstRec_shiftRec0_comm (ss : Rec) : (forall (d3 : (Trace ty)) (S4 : Ty) ,
      ((tsubstRec d3 S4 (shiftRec C0 ss)) = (shiftRec C0 (tsubstRec d3 S4 ss)))) := (tsubst_shift0_Rec_comm_ind ss H0).
    Definition tsubstTm_tshiftTm0_comm (s : Tm) : (forall (d3 : (Trace ty)) (S4 : Ty) ,
      ((tsubstTm (XS ty d3) S4 (tshiftTm C0 s)) = (tshiftTm C0 (tsubstTm d3 S4 s)))) := (tsubst_tshift0_Tm_comm_ind s H0).
    Definition tsubstRec_tshiftRec0_comm (ss : Rec) : (forall (d3 : (Trace ty)) (S4 : Ty) ,
      ((tsubstRec (XS ty d3) S4 (tshiftRec C0 ss)) = (tshiftRec C0 (tsubstRec d3 S4 ss)))) := (tsubst_tshift0_Rec_comm_ind ss H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Fixpoint tsubst_tm_TRec_ind (SS : TRec) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) {struct SS} :
    ((tsubstTRec (weakenTrace (XS tm d3) k) S4 SS) = (tsubstTRec (weakenTrace d3 k) S4 SS)) :=
      match SS return ((tsubstTRec (weakenTrace (XS tm d3) k) S4 SS) = (tsubstTRec (weakenTrace d3 k) S4 SS)) with
        | (tnil) => eq_refl
        | (tcons l5 T11 TS1) => (f_equal3 tcons eq_refl (tsubst_tm_Ty_ind T11 k d3 S4) (tsubst_tm_TRec_ind TS1 k d3 S4))
      end
    with tsubst_tm_Ty_ind (S5 : Ty) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) {struct S5} :
    ((tsubstTy (weakenTrace (XS tm d3) k) S4 S5) = (tsubstTy (weakenTrace d3 k) S4 S5)) :=
      match S5 return ((tsubstTy (weakenTrace (XS tm d3) k) S4 S5) = (tsubstTy (weakenTrace d3 k) S4 S5)) with
        | (tvar X7) => (tsubstIndex_shiftTy0_comm_ind d3 S4 k X7)
        | (top) => eq_refl
        | (tarr T12 T13) => (f_equal2 tarr (tsubst_tm_Ty_ind T12 k d3 S4) (tsubst_tm_Ty_ind T13 k d3 S4))
        | (tall T12 T13) => (f_equal2 tall (tsubst_tm_Ty_ind T12 k d3 S4) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d3) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T13 (HS ty k) d3 S4) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d3 k (HS ty H0))) eq_refl eq_refl))))
        | (trec TS2) => (f_equal trec (tsubst_tm_TRec_ind TS2 k d3 S4))
      end.
    Fixpoint tsubst_tm_Pat_ind (p10 : Pat) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) {struct p10} :
    ((tsubstPat (weakenTrace (XS tm d3) k) S4 p10) = (tsubstPat (weakenTrace d3 k) S4 p10)) :=
      match p10 return ((tsubstPat (weakenTrace (XS tm d3) k) S4 p10) = (tsubstPat (weakenTrace d3 k) S4 p10)) with
        | (pvar T11) => (f_equal pvar (tsubst_tm_Ty_ind T11 k d3 S4))
        | (prec ps10) => (f_equal prec (tsubst_tm_PRec_ind ps10 k d3 S4))
      end
    with tsubst_tm_PRec_ind (ps11 : PRec) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) {struct ps11} :
    ((tsubstPRec (weakenTrace (XS tm d3) k) S4 ps11) = (tsubstPRec (weakenTrace d3 k) S4 ps11)) :=
      match ps11 return ((tsubstPRec (weakenTrace (XS tm d3) k) S4 ps11) = (tsubstPRec (weakenTrace d3 k) S4 ps11)) with
        | (pnil) => eq_refl
        | (pcons l5 p11 ps12) => (f_equal3 pcons eq_refl (tsubst_tm_Pat_ind p11 k d3 S4) (eq_trans (f_equal3 tsubstPRec (weakenTrace_append ty (XS tm d3) k (appendHvl H0 (bindPat p11))) eq_refl eq_refl) (eq_trans (tsubst_tm_PRec_ind ps12 (appendHvl k (appendHvl H0 (bindPat p11))) d3 S4) (f_equal3 tsubstPRec (eq_sym (weakenTrace_append ty d3 k (appendHvl H0 (bindPat p11)))) eq_refl eq_refl))))
      end.
    Fixpoint tsubst_tm_Tm_ind (s : Tm) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS tm d3) k) S4 s) = (tsubstTm (weakenTrace d3 k) S4 s)) :=
      match s return ((tsubstTm (weakenTrace (XS tm d3) k) S4 s) = (tsubstTm (weakenTrace d3 k) S4 s)) with
        | (var x6) => eq_refl
        | (abs T11 t8) => (f_equal2 abs (tsubst_tm_Ty_ind T11 k d3 S4) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d3) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t8 (HS tm k) d3 S4) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d3 k (HS tm H0))) eq_refl eq_refl))))
        | (app t9 t10) => (f_equal2 app (tsubst_tm_Tm_ind t9 k d3 S4) (tsubst_tm_Tm_ind t10 k d3 S4))
        | (tabs T11 t8) => (f_equal2 tabs (tsubst_tm_Ty_ind T11 k d3 S4) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d3) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t8 (HS ty k) d3 S4) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d3 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp t8 T11) => (f_equal2 tapp (tsubst_tm_Tm_ind t8 k d3 S4) (tsubst_tm_Ty_ind T11 k d3 S4))
        | (rec ts1) => (f_equal rec (tsubst_tm_Rec_ind ts1 k d3 S4))
        | (prj t8 l5) => (f_equal2 prj (tsubst_tm_Tm_ind t8 k d3 S4) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett (tsubst_tm_Pat_ind p10 k d3 S4) (tsubst_tm_Tm_ind t9 k d3 S4) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d3) k (appendHvl H0 (bindPat p10))) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) d3 S4) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d3 k (appendHvl H0 (bindPat p10)))) eq_refl eq_refl))))
      end
    with tsubst_tm_Rec_ind (ss : Rec) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) {struct ss} :
    ((tsubstRec (weakenTrace (XS tm d3) k) S4 ss) = (tsubstRec (weakenTrace d3 k) S4 ss)) :=
      match ss return ((tsubstRec (weakenTrace (XS tm d3) k) S4 ss) = (tsubstRec (weakenTrace d3 k) S4 ss)) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (tsubst_tm_Tm_ind t11 k d3 S4) (tsubst_tm_Rec_ind ts2 k d3 S4))
      end.
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTRec_tm (SS : TRec) : (forall (d3 : (Trace ty)) (S4 : Ty) ,
      ((tsubstTRec (XS tm d3) S4 SS) = (tsubstTRec d3 S4 SS))) := (tsubst_tm_TRec_ind SS H0).
    Definition tsubstTy_tm (S5 : Ty) : (forall (d3 : (Trace ty)) (S4 : Ty) ,
      ((tsubstTy (XS tm d3) S4 S5) = (tsubstTy d3 S4 S5))) := (tsubst_tm_Ty_ind S5 H0).
    Definition tsubstPat_tm (p10 : Pat) : (forall (d3 : (Trace ty)) (S4 : Ty) ,
      ((tsubstPat (XS tm d3) S4 p10) = (tsubstPat d3 S4 p10))) := (tsubst_tm_Pat_ind p10 H0).
    Definition tsubstPRec_tm (ps10 : PRec) : (forall (d3 : (Trace ty)) (S4 : Ty) ,
      ((tsubstPRec (XS tm d3) S4 ps10) = (tsubstPRec d3 S4 ps10))) := (tsubst_tm_PRec_ind ps10 H0).
    Definition tsubstTm_tm (s : Tm) : (forall (d3 : (Trace ty)) (S4 : Ty) ,
      ((tsubstTm (XS tm d3) S4 s) = (tsubstTm d3 S4 s))) := (tsubst_tm_Tm_ind s H0).
    Definition tsubstRec_tm (ss : Rec) : (forall (d3 : (Trace ty)) (S4 : Ty) ,
      ((tsubstRec (XS tm d3) S4 ss) = (tsubstRec d3 S4 ss))) := (tsubst_tm_Rec_ind ss H0).
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite tsubstPRec0_tshiftPRec0_reflection tsubstPat0_tshiftPat0_reflection substRec0_shiftRec0_reflection tsubstRec0_tshiftRec0_reflection tsubstTRec0_tshiftTRec0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : interaction.
 Hint Rewrite tsubstPRec0_tshiftPRec0_reflection tsubstPat0_tshiftPat0_reflection substRec0_shiftRec0_reflection tsubstRec0_tshiftRec0_reflection tsubstTRec0_tshiftTRec0_reflection substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : reflection.
 Hint Rewrite tsubstPRec_tshiftPRec0_comm tsubstPat_tshiftPat0_comm substRec_shiftRec0_comm substRec_tshiftRec0_comm tsubstRec_shiftRec0_comm tsubstRec_tshiftRec0_comm tsubstTRec_tshiftTRec0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : interaction.
 Hint Rewrite tsubstPRec_tshiftPRec0_comm tsubstPat_tshiftPat0_comm substRec_shiftRec0_comm substRec_tshiftRec0_comm tsubstRec_shiftRec0_comm tsubstRec_tshiftRec0_comm tsubstTRec_tshiftTRec0_comm substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : subst_shift0.
 Hint Rewrite tsubstPRec_tm tsubstPat_tm tsubstRec_tm tsubstTRec_tm tsubstTm_tm tsubstTy_tm : interaction.
 Hint Rewrite tsubstPRec_tm tsubstPat_tm tsubstRec_tm tsubstTRec_tm tsubstTm_tm tsubstTy_tm : subst_shift0.
 Hint Rewrite tshiftPRec_tsubstPRec0_comm tshiftPat_tsubstPat0_comm shiftRec_substRec0_comm shiftRec_tsubstRec0_comm tshiftRec_substRec0_comm tshiftRec_tsubstRec0_comm tshiftTRec_tsubstTRec0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : interaction.
 Hint Rewrite tshiftPRec_tsubstPRec0_comm tshiftPat_tsubstPat0_comm shiftRec_substRec0_comm shiftRec_tsubstRec0_comm tshiftRec_substRec0_comm tshiftRec_tsubstRec0_comm tshiftTRec_tsubstTRec0_comm shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d3 : (Trace tm)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((substTm (weakenTrace d3 k) s (substIndex (weakenTrace X0 k) s0 x6)) = (substTm (weakenTrace X0 k) (substTm d3 s s0) (substIndex (weakenTrace (XS tm d3) k) s x6)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d3 : (Trace ty)) (S4 : Ty) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((tsubstTm (weakenTrace d3 k) S4 (substIndex (weakenTrace X0 k) s x6)) = (substIndex (weakenTrace X0 k) (tsubstTm d3 S4 s) x6))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d3 : (Trace ty)) (S4 : Ty) (S5 : Ty) :
      (forall (k : Hvl) (X7 : (Index ty)) ,
        ((tsubstTy (weakenTrace d3 k) S4 (tsubstIndex (weakenTrace X0 k) S5 X7)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d3 S4 S5) (tsubstIndex (weakenTrace (XS ty d3) k) S4 X7)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d3 : (Trace tm)) (s : Tm) (S4 : Ty) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((substIndex (weakenTrace d3 k) s x6) = (tsubstTm (weakenTrace X0 k) S4 (substIndex (weakenTrace (XS ty d3) k) s x6)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint tsubst_tsubst0_TRec_comm_ind (SS : TRec) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) (S5 : Ty) {struct SS} :
    ((tsubstTRec (weakenTrace d3 k) S4 (tsubstTRec (weakenTrace X0 k) S5 SS)) = (tsubstTRec (weakenTrace X0 k) (tsubstTy d3 S4 S5) (tsubstTRec (weakenTrace (XS ty d3) k) S4 SS))) :=
      match SS return ((tsubstTRec (weakenTrace d3 k) S4 (tsubstTRec (weakenTrace X0 k) S5 SS)) = (tsubstTRec (weakenTrace X0 k) (tsubstTy d3 S4 S5) (tsubstTRec (weakenTrace (XS ty d3) k) S4 SS))) with
        | (tnil) => eq_refl
        | (tcons l5 T11 TS1) => (f_equal3 tcons eq_refl (tsubst_tsubst0_Ty_comm_ind T11 k d3 S4 S5) (tsubst_tsubst0_TRec_comm_ind TS1 k d3 S4 S5))
      end
    with tsubst_tsubst0_Ty_comm_ind (S6 : Ty) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) (S5 : Ty) {struct S6} :
    ((tsubstTy (weakenTrace d3 k) S4 (tsubstTy (weakenTrace X0 k) S5 S6)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d3 S4 S5) (tsubstTy (weakenTrace (XS ty d3) k) S4 S6))) :=
      match S6 return ((tsubstTy (weakenTrace d3 k) S4 (tsubstTy (weakenTrace X0 k) S5 S6)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d3 S4 S5) (tsubstTy (weakenTrace (XS ty d3) k) S4 S6))) with
        | (tvar X7) => (tsubstTy_tsubstIndex0_commright_ind d3 S4 S5 k X7)
        | (top) => eq_refl
        | (tarr T12 T13) => (f_equal2 tarr (tsubst_tsubst0_Ty_comm_ind T12 k d3 S4 S5) (tsubst_tsubst0_Ty_comm_ind T13 k d3 S4 S5))
        | (tall T12 T13) => (f_equal2 tall (tsubst_tsubst0_Ty_comm_ind T12 k d3 S4 S5) (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d3 k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T13 (HS ty k) d3 S4 S5) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d3) k (HS ty H0))) eq_refl eq_refl)))))
        | (trec TS2) => (f_equal trec (tsubst_tsubst0_TRec_comm_ind TS2 k d3 S4 S5))
      end.
    Fixpoint tsubst_tsubst0_Pat_comm_ind (p10 : Pat) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) (S5 : Ty) {struct p10} :
    ((tsubstPat (weakenTrace d3 k) S4 (tsubstPat (weakenTrace X0 k) S5 p10)) = (tsubstPat (weakenTrace X0 k) (tsubstTy d3 S4 S5) (tsubstPat (weakenTrace (XS ty d3) k) S4 p10))) :=
      match p10 return ((tsubstPat (weakenTrace d3 k) S4 (tsubstPat (weakenTrace X0 k) S5 p10)) = (tsubstPat (weakenTrace X0 k) (tsubstTy d3 S4 S5) (tsubstPat (weakenTrace (XS ty d3) k) S4 p10))) with
        | (pvar T11) => (f_equal pvar (tsubst_tsubst0_Ty_comm_ind T11 k d3 S4 S5))
        | (prec ps10) => (f_equal prec (tsubst_tsubst0_PRec_comm_ind ps10 k d3 S4 S5))
      end
    with tsubst_tsubst0_PRec_comm_ind (ps11 : PRec) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) (S5 : Ty) {struct ps11} :
    ((tsubstPRec (weakenTrace d3 k) S4 (tsubstPRec (weakenTrace X0 k) S5 ps11)) = (tsubstPRec (weakenTrace X0 k) (tsubstTy d3 S4 S5) (tsubstPRec (weakenTrace (XS ty d3) k) S4 ps11))) :=
      match ps11 return ((tsubstPRec (weakenTrace d3 k) S4 (tsubstPRec (weakenTrace X0 k) S5 ps11)) = (tsubstPRec (weakenTrace X0 k) (tsubstTy d3 S4 S5) (tsubstPRec (weakenTrace (XS ty d3) k) S4 ps11))) with
        | (pnil) => eq_refl
        | (pcons l5 p11 ps12) => (f_equal3 pcons eq_refl (tsubst_tsubst0_Pat_comm_ind p11 k d3 S4 S5) (eq_trans (f_equal3 tsubstPRec (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append ty d3 k (appendHvl H0 (bindPat p11)))) eq_refl (f_equal3 tsubstPRec (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p11))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_PRec_comm_ind ps12 (appendHvl k (appendHvl H0 (bindPat p11))) d3 S4 S5) (f_equal3 tsubstPRec (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p11)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstPRec (eq_sym (weakenTrace_append ty (XS ty d3) k (appendHvl H0 (bindPat p11)))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d3 : (Trace tm)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d3 k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d3 s s0) (substTm (weakenTrace (XS tm d3) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d3 k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d3 s s0) (substTm (weakenTrace (XS tm d3) k) s s1))) with
        | (var x6) => (substTm_substIndex0_commright_ind d3 s s0 k x6)
        | (abs T11 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d3 k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t8 (HS tm k) d3 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d3) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (subst_subst0_Tm_comm_ind t9 k d3 s s0) (subst_subst0_Tm_comm_ind t10 k d3 s s0))
        | (tabs T11 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d3 k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t8 (HS ty k) d3 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d3) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t8 T11) => (f_equal2 tapp (subst_subst0_Tm_comm_ind t8 k d3 s s0) eq_refl)
        | (rec ts1) => (f_equal rec (subst_subst0_Rec_comm_ind ts1 k d3 s s0))
        | (prj t8 l5) => (f_equal2 prj (subst_subst0_Tm_comm_ind t8 k d3 s s0) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett eq_refl (subst_subst0_Tm_comm_ind t9 k d3 s s0) (eq_trans (f_equal3 substTm (weakenTrace_append tm d3 k (appendHvl H0 (bindPat p10))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p10))) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) d3 s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p10)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d3) k (appendHvl H0 (bindPat p10)))) eq_refl eq_refl)))))
      end
    with subst_subst0_Rec_comm_ind (ss : Rec) (k : Hvl) (d3 : (Trace tm)) (s : Tm) (s0 : Tm) {struct ss} :
    ((substRec (weakenTrace d3 k) s (substRec (weakenTrace X0 k) s0 ss)) = (substRec (weakenTrace X0 k) (substTm d3 s s0) (substRec (weakenTrace (XS tm d3) k) s ss))) :=
      match ss return ((substRec (weakenTrace d3 k) s (substRec (weakenTrace X0 k) s0 ss)) = (substRec (weakenTrace X0 k) (substTm d3 s s0) (substRec (weakenTrace (XS tm d3) k) s ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (subst_subst0_Tm_comm_ind t11 k d3 s s0) (subst_subst0_Rec_comm_ind ts2 k d3 s s0))
      end.
    Fixpoint subst_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d3 : (Trace tm)) (s : Tm) (S4 : Ty) {struct s0} :
    ((substTm (weakenTrace d3 k) s (tsubstTm (weakenTrace X0 k) S4 s0)) = (tsubstTm (weakenTrace X0 k) S4 (substTm (weakenTrace (XS ty d3) k) s s0))) :=
      match s0 return ((substTm (weakenTrace d3 k) s (tsubstTm (weakenTrace X0 k) S4 s0)) = (tsubstTm (weakenTrace X0 k) S4 (substTm (weakenTrace (XS ty d3) k) s s0))) with
        | (var x6) => (substTy_tsubstIndex0_commleft_ind d3 s S4 k x6)
        | (abs T11 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d3 k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t8 (HS tm k) d3 s S4) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d3) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (subst_tsubst0_Tm_comm_ind t9 k d3 s S4) (subst_tsubst0_Tm_comm_ind t10 k d3 s S4))
        | (tabs T11 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d3 k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t8 (HS ty k) d3 s S4) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d3) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t8 T11) => (f_equal2 tapp (subst_tsubst0_Tm_comm_ind t8 k d3 s S4) eq_refl)
        | (rec ts1) => (f_equal rec (subst_tsubst0_Rec_comm_ind ts1 k d3 s S4))
        | (prj t8 l5) => (f_equal2 prj (subst_tsubst0_Tm_comm_ind t8 k d3 s S4) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett eq_refl (subst_tsubst0_Tm_comm_ind t9 k d3 s S4) (eq_trans (f_equal3 substTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append tm d3 k (appendHvl H0 (bindPat p10)))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p10))) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) d3 s S4) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p10)))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d3) k (appendHvl H0 (bindPat p10)))) eq_refl eq_refl)))))
      end
    with subst_tsubst0_Rec_comm_ind (ss : Rec) (k : Hvl) (d3 : (Trace tm)) (s : Tm) (S4 : Ty) {struct ss} :
    ((substRec (weakenTrace d3 k) s (tsubstRec (weakenTrace X0 k) S4 ss)) = (tsubstRec (weakenTrace X0 k) S4 (substRec (weakenTrace (XS ty d3) k) s ss))) :=
      match ss return ((substRec (weakenTrace d3 k) s (tsubstRec (weakenTrace X0 k) S4 ss)) = (tsubstRec (weakenTrace X0 k) S4 (substRec (weakenTrace (XS ty d3) k) s ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (subst_tsubst0_Tm_comm_ind t11 k d3 s S4) (subst_tsubst0_Rec_comm_ind ts2 k d3 s S4))
      end.
    Fixpoint tsubst_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) (s : Tm) {struct s0} :
    ((tsubstTm (weakenTrace d3 k) S4 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d3 S4 s) (tsubstTm (weakenTrace d3 k) S4 s0))) :=
      match s0 return ((tsubstTm (weakenTrace d3 k) S4 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d3 S4 s) (tsubstTm (weakenTrace d3 k) S4 s0))) with
        | (var x6) => (tsubstTm_substIndex0_commright_ind d3 S4 s k x6)
        | (abs T11 t8) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d3 k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t8 (HS tm k) d3 S4 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d3 k (HS tm H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (tsubst_subst0_Tm_comm_ind t9 k d3 S4 s) (tsubst_subst0_Tm_comm_ind t10 k d3 S4 s))
        | (tabs T11 t8) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d3 k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t8 (HS ty k) d3 S4 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d3 k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t8 T11) => (f_equal2 tapp (tsubst_subst0_Tm_comm_ind t8 k d3 S4 s) eq_refl)
        | (rec ts1) => (f_equal rec (tsubst_subst0_Rec_comm_ind ts1 k d3 S4 s))
        | (prj t8 l5) => (f_equal2 prj (tsubst_subst0_Tm_comm_ind t8 k d3 S4 s) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett eq_refl (tsubst_subst0_Tm_comm_ind t9 k d3 S4 s) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d3 k (appendHvl H0 (bindPat p10))) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p10))) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) d3 S4 s) (f_equal3 substTm (eq_trans (eq_sym (weakenTrace_append tm X0 k (appendHvl H0 (bindPat p10)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d3 k (appendHvl H0 (bindPat p10)))) eq_refl eq_refl)))))
      end
    with tsubst_subst0_Rec_comm_ind (ss : Rec) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) (s : Tm) {struct ss} :
    ((tsubstRec (weakenTrace d3 k) S4 (substRec (weakenTrace X0 k) s ss)) = (substRec (weakenTrace X0 k) (tsubstTm d3 S4 s) (tsubstRec (weakenTrace d3 k) S4 ss))) :=
      match ss return ((tsubstRec (weakenTrace d3 k) S4 (substRec (weakenTrace X0 k) s ss)) = (substRec (weakenTrace X0 k) (tsubstTm d3 S4 s) (tsubstRec (weakenTrace d3 k) S4 ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (tsubst_subst0_Tm_comm_ind t11 k d3 S4 s) (tsubst_subst0_Rec_comm_ind ts2 k d3 S4 s))
      end.
    Fixpoint tsubst_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) (S5 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d3 k) S4 (tsubstTm (weakenTrace X0 k) S5 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d3 S4 S5) (tsubstTm (weakenTrace (XS ty d3) k) S4 s))) :=
      match s return ((tsubstTm (weakenTrace d3 k) S4 (tsubstTm (weakenTrace X0 k) S5 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d3 S4 S5) (tsubstTm (weakenTrace (XS ty d3) k) S4 s))) with
        | (var x6) => eq_refl
        | (abs T11 t8) => (f_equal2 abs (tsubst_tsubst0_Ty_comm_ind T11 k d3 S4 S5) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d3 k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t8 (HS tm k) d3 S4 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d3) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t9 t10) => (f_equal2 app (tsubst_tsubst0_Tm_comm_ind t9 k d3 S4 S5) (tsubst_tsubst0_Tm_comm_ind t10 k d3 S4 S5))
        | (tabs T11 t8) => (f_equal2 tabs (tsubst_tsubst0_Ty_comm_ind T11 k d3 S4 S5) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d3 k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t8 (HS ty k) d3 S4 S5) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d3) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp t8 T11) => (f_equal2 tapp (tsubst_tsubst0_Tm_comm_ind t8 k d3 S4 S5) (tsubst_tsubst0_Ty_comm_ind T11 k d3 S4 S5))
        | (rec ts1) => (f_equal rec (tsubst_tsubst0_Rec_comm_ind ts1 k d3 S4 S5))
        | (prj t8 l5) => (f_equal2 prj (tsubst_tsubst0_Tm_comm_ind t8 k d3 S4 S5) eq_refl)
        | (lett p10 t9 t10) => (f_equal3 lett (tsubst_tsubst0_Pat_comm_ind p10 k d3 S4 S5) (tsubst_tsubst0_Tm_comm_ind t9 k d3 S4 S5) (eq_trans (f_equal3 tsubstTm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_tsubst_bindPat _ _ _) (eq_refl H0)))) (weakenTrace_append ty d3 k (appendHvl H0 (bindPat p10)))) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p10))) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t10 (appendHvl k (appendHvl H0 (bindPat p10))) d3 S4 S5) (f_equal3 tsubstTm (eq_trans (eq_sym (weakenTrace_append ty X0 k (appendHvl H0 (bindPat p10)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d3) k (appendHvl H0 (bindPat p10)))) eq_refl eq_refl)))))
      end
    with tsubst_tsubst0_Rec_comm_ind (ss : Rec) (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) (S5 : Ty) {struct ss} :
    ((tsubstRec (weakenTrace d3 k) S4 (tsubstRec (weakenTrace X0 k) S5 ss)) = (tsubstRec (weakenTrace X0 k) (tsubstTy d3 S4 S5) (tsubstRec (weakenTrace (XS ty d3) k) S4 ss))) :=
      match ss return ((tsubstRec (weakenTrace d3 k) S4 (tsubstRec (weakenTrace X0 k) S5 ss)) = (tsubstRec (weakenTrace X0 k) (tsubstTy d3 S4 S5) (tsubstRec (weakenTrace (XS ty d3) k) S4 ss))) with
        | (rnil) => eq_refl
        | (rcons l6 t11 ts2) => (f_equal3 rcons eq_refl (tsubst_tsubst0_Tm_comm_ind t11 k d3 S4 S5) (tsubst_tsubst0_Rec_comm_ind ts2 k d3 S4 S5))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTRec_tsubstTRec0_comm (SS : TRec) : (forall (d3 : (Trace ty)) (S4 : Ty) (S5 : Ty) ,
      ((tsubstTRec d3 S4 (tsubstTRec X0 S5 SS)) = (tsubstTRec X0 (tsubstTy d3 S4 S5) (tsubstTRec (XS ty d3) S4 SS)))) := (tsubst_tsubst0_TRec_comm_ind SS H0).
    Definition tsubstTy_tsubstTy0_comm (S6 : Ty) : (forall (d3 : (Trace ty)) (S4 : Ty) (S5 : Ty) ,
      ((tsubstTy d3 S4 (tsubstTy X0 S5 S6)) = (tsubstTy X0 (tsubstTy d3 S4 S5) (tsubstTy (XS ty d3) S4 S6)))) := (tsubst_tsubst0_Ty_comm_ind S6 H0).
    Definition tsubstPat_tsubstPat0_comm (p10 : Pat) : (forall (d3 : (Trace ty)) (S4 : Ty) (S5 : Ty) ,
      ((tsubstPat d3 S4 (tsubstPat X0 S5 p10)) = (tsubstPat X0 (tsubstTy d3 S4 S5) (tsubstPat (XS ty d3) S4 p10)))) := (tsubst_tsubst0_Pat_comm_ind p10 H0).
    Definition tsubstPRec_tsubstPRec0_comm (ps10 : PRec) : (forall (d3 : (Trace ty)) (S4 : Ty) (S5 : Ty) ,
      ((tsubstPRec d3 S4 (tsubstPRec X0 S5 ps10)) = (tsubstPRec X0 (tsubstTy d3 S4 S5) (tsubstPRec (XS ty d3) S4 ps10)))) := (tsubst_tsubst0_PRec_comm_ind ps10 H0).
    Definition substTm_substTm0_comm (s1 : Tm) : (forall (d3 : (Trace tm)) (s : Tm) (s0 : Tm) ,
      ((substTm d3 s (substTm X0 s0 s1)) = (substTm X0 (substTm d3 s s0) (substTm (XS tm d3) s s1)))) := (subst_subst0_Tm_comm_ind s1 H0).
    Definition substRec_substRec0_comm (ss : Rec) : (forall (d3 : (Trace tm)) (s : Tm) (s0 : Tm) ,
      ((substRec d3 s (substRec X0 s0 ss)) = (substRec X0 (substTm d3 s s0) (substRec (XS tm d3) s ss)))) := (subst_subst0_Rec_comm_ind ss H0).
    Definition substTm_tsubstTm0_comm (s0 : Tm) : (forall (d3 : (Trace tm)) (s : Tm) (S4 : Ty) ,
      ((substTm d3 s (tsubstTm X0 S4 s0)) = (tsubstTm X0 S4 (substTm (XS ty d3) s s0)))) := (subst_tsubst0_Tm_comm_ind s0 H0).
    Definition substRec_tsubstRec0_comm (ss : Rec) : (forall (d3 : (Trace tm)) (s : Tm) (S4 : Ty) ,
      ((substRec d3 s (tsubstRec X0 S4 ss)) = (tsubstRec X0 S4 (substRec (XS ty d3) s ss)))) := (subst_tsubst0_Rec_comm_ind ss H0).
    Definition tsubstTm_substTm0_comm (s0 : Tm) : (forall (d3 : (Trace ty)) (S4 : Ty) (s : Tm) ,
      ((tsubstTm d3 S4 (substTm X0 s s0)) = (substTm X0 (tsubstTm d3 S4 s) (tsubstTm d3 S4 s0)))) := (tsubst_subst0_Tm_comm_ind s0 H0).
    Definition tsubstRec_substRec0_comm (ss : Rec) : (forall (d3 : (Trace ty)) (S4 : Ty) (s : Tm) ,
      ((tsubstRec d3 S4 (substRec X0 s ss)) = (substRec X0 (tsubstTm d3 S4 s) (tsubstRec d3 S4 ss)))) := (tsubst_subst0_Rec_comm_ind ss H0).
    Definition tsubstTm_tsubstTm0_comm (s : Tm) : (forall (d3 : (Trace ty)) (S4 : Ty) (S5 : Ty) ,
      ((tsubstTm d3 S4 (tsubstTm X0 S5 s)) = (tsubstTm X0 (tsubstTy d3 S4 S5) (tsubstTm (XS ty d3) S4 s)))) := (tsubst_tsubst0_Tm_comm_ind s H0).
    Definition tsubstRec_tsubstRec0_comm (ss : Rec) : (forall (d3 : (Trace ty)) (S4 : Ty) (S5 : Ty) ,
      ((tsubstRec d3 S4 (tsubstRec X0 S5 ss)) = (tsubstRec X0 (tsubstTy d3 S4 S5) (tsubstRec (XS ty d3) S4 ss)))) := (tsubst_tsubst0_Rec_comm_ind ss H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTRec_tsubstTRec  :
      (forall (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) (SS : TRec) ,
        ((weakenTRec (tsubstTRec d3 S4 SS) k) = (tsubstTRec (weakenTrace d3 k) S4 (weakenTRec SS k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTy_tsubstTy  :
      (forall (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) (S5 : Ty) ,
        ((weakenTy (tsubstTy d3 S4 S5) k) = (tsubstTy (weakenTrace d3 k) S4 (weakenTy S5 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenPat_tsubstPat  :
      (forall (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) (p10 : Pat) ,
        ((weakenPat (tsubstPat d3 S4 p10) k) = (tsubstPat (weakenTrace d3 k) S4 (weakenPat p10 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenPRec_tsubstPRec  :
      (forall (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) (ps10 : PRec) ,
        ((weakenPRec (tsubstPRec d3 S4 ps10) k) = (tsubstPRec (weakenTrace d3 k) S4 (weakenPRec ps10 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k : Hvl) (d3 : (Trace tm)) (s : Tm) (s0 : Tm) ,
        ((weakenTm (substTm d3 s s0) k) = (substTm (weakenTrace d3 k) s (weakenTm s0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenRec_substRec  :
      (forall (k : Hvl) (d3 : (Trace tm)) (s : Tm) (ss : Rec) ,
        ((weakenRec (substRec d3 s ss) k) = (substRec (weakenTrace d3 k) s (weakenRec ss k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) (s : Tm) ,
        ((weakenTm (tsubstTm d3 S4 s) k) = (tsubstTm (weakenTrace d3 k) S4 (weakenTm s k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenRec_tsubstRec  :
      (forall (k : Hvl) (d3 : (Trace ty)) (S4 : Ty) (ss : Rec) ,
        ((weakenRec (tsubstRec d3 S4 ss) k) = (tsubstRec (weakenTrace d3 k) S4 (weakenRec ss k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite tsubstPRec_tsubstPRec0_comm tsubstPat_tsubstPat0_comm substRec_substRec0_comm tsubstRec_tsubstRec0_comm tsubstTRec_tsubstTRec0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : interaction.
 Hint Rewrite tsubstPRec_tsubstPRec0_comm tsubstPat_tsubstPat0_comm substRec_substRec0_comm tsubstRec_tsubstRec0_comm tsubstTRec_tsubstTRec0_comm substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : subst_subst0.
 Hint Rewrite weakenPRec_tshiftPRec weakenPat_tshiftPat weakenRec_shiftRec weakenRec_tshiftRec weakenTRec_tshiftTRec weakenTm_shiftTm weakenTm_tshiftTm weakenTy_tshiftTy : weaken_shift.
 Hint Rewrite weakenPRec_tsubstPRec weakenPat_tsubstPat weakenRec_substRec weakenRec_tsubstRec weakenTRec_tsubstTRec weakenTm_substTm weakenTm_tsubstTm weakenTy_tsubstTy : weaken_subst.
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
  Inductive wfLab (k : Hvl) : Lab -> Prop :=
    | wfLab_L0 : (wfLab k (L0))
    | wfLab_LS {l5 : Lab}
        (wf : (wfLab k l5)) :
        (wfLab k (LS l5)).
  Inductive wfTRec (k : Hvl) : TRec -> Prop :=
    | wfTRec_tnil :
        (wfTRec k (tnil))
    | wfTRec_tcons {l5 : Lab}
        (wf : (wfLab k l5)) {T11 : Ty}
        (wf0 : (wfTy k T11))
        {TS1 : TRec}
        (wf1 : (wfTRec k TS1)) :
        (wfTRec k (tcons l5 T11 TS1))
  with wfTy (k : Hvl) : Ty -> Prop :=
    | wfTy_tvar (X7 : (Index ty))
        (wfi : (wfindex k X7)) :
        (wfTy k (tvar X7))
    | wfTy_top : (wfTy k (top))
    | wfTy_tarr {T11 : Ty}
        (wf : (wfTy k T11)) {T12 : Ty}
        (wf0 : (wfTy k T12)) :
        (wfTy k (tarr T11 T12))
    | wfTy_tall {T13 : Ty}
        (wf : (wfTy k T13)) {T14 : Ty}
        (wf0 : (wfTy (HS ty k) T14)) :
        (wfTy k (tall T13 T14))
    | wfTy_trec {TS1 : TRec}
        (wf : (wfTRec k TS1)) :
        (wfTy k (trec TS1)).
  Inductive wfPat (k : Hvl) : Pat -> Prop :=
    | wfPat_pvar {T11 : Ty}
        (wf : (wfTy k T11)) :
        (wfPat k (pvar T11))
    | wfPat_prec {ps10 : PRec}
        (wf : (wfPRec k ps10)) :
        (wfPat k (prec ps10))
  with wfPRec (k : Hvl) : PRec -> Prop :=
    | wfPRec_pnil :
        (wfPRec k (pnil))
    | wfPRec_pcons {l5 : Lab}
        (wf : (wfLab k l5)) {p10 : Pat}
        (wf0 : (wfPat k p10))
        {ps10 : PRec}
        (wf1 : (wfPRec (appendHvl k (appendHvl H0 (bindPat p10))) ps10))
        :
        (wfPRec k (pcons l5 p10 ps10)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var (x6 : (Index tm))
        (wfi : (wfindex k x6)) :
        (wfTm k (var x6))
    | wfTm_abs {T11 : Ty}
        (wf : (wfTy k T11)) {t8 : Tm}
        (wf0 : (wfTm (HS tm k) t8)) :
        (wfTm k (abs T11 t8))
    | wfTm_app {t9 : Tm}
        (wf : (wfTm k t9)) {t10 : Tm}
        (wf0 : (wfTm k t10)) :
        (wfTm k (app t9 t10))
    | wfTm_tabs {T12 : Ty}
        (wf : (wfTy k T12)) {t11 : Tm}
        (wf0 : (wfTm (HS ty k) t11)) :
        (wfTm k (tabs T12 t11))
    | wfTm_tapp {t12 : Tm}
        (wf : (wfTm k t12)) {T13 : Ty}
        (wf0 : (wfTy k T13)) :
        (wfTm k (tapp t12 T13))
    | wfTm_rec {ts1 : Rec}
        (wf : (wfRec k ts1)) :
        (wfTm k (rec ts1))
    | wfTm_prj {t13 : Tm}
        (wf : (wfTm k t13)) {l5 : Lab}
        (wf0 : (wfLab k l5)) :
        (wfTm k (prj t13 l5))
    | wfTm_lett {p10 : Pat}
        (wf : (wfPat k p10)) {t14 : Tm}
        (wf0 : (wfTm k t14)) {t15 : Tm}
        (wf1 : (wfTm (appendHvl k (appendHvl H0 (bindPat p10))) t15))
        : (wfTm k (lett p10 t14 t15))
  with wfRec (k : Hvl) : Rec -> Prop :=
    | wfRec_rnil :
        (wfRec k (rnil))
    | wfRec_rcons {l5 : Lab}
        (wf : (wfLab k l5)) {t8 : Tm}
        (wf0 : (wfTm k t8)) {ts1 : Rec}
        (wf1 : (wfRec k ts1)) :
        (wfRec k (rcons l5 t8 ts1)).
  Definition inversion_wfLab_LS_0 (k0 : Hvl) (l : Lab) (H37 : (wfLab k0 (LS l))) : (wfLab k0 l) := match H37 in (wfLab _ l6) return match l6 return Prop with
    | (LS l) => (wfLab k0 l)
    | _ => True
  end with
    | (wfLab_LS l H1) => H1
    | _ => I
  end.
  Definition inversion_wfTRec_tcons_0 (k2 : Hvl) (l : Lab) (T : Ty) (TS : TRec) (H39 : (wfTRec k2 (tcons l T TS))) : (wfLab k2 l) := match H39 in (wfTRec _ SS0) return match SS0 return Prop with
    | (tcons l T TS) => (wfLab k2 l)
    | _ => True
  end with
    | (wfTRec_tcons l H2 T H3 TS H4) => H2
    | _ => I
  end.
  Definition inversion_wfTRec_tcons_1 (k2 : Hvl) (l : Lab) (T : Ty) (TS : TRec) (H39 : (wfTRec k2 (tcons l T TS))) : (wfTy k2 T) := match H39 in (wfTRec _ SS0) return match SS0 return Prop with
    | (tcons l T TS) => (wfTy k2 T)
    | _ => True
  end with
    | (wfTRec_tcons l H2 T H3 TS H4) => H3
    | _ => I
  end.
  Definition inversion_wfTRec_tcons_2 (k2 : Hvl) (l : Lab) (T : Ty) (TS : TRec) (H39 : (wfTRec k2 (tcons l T TS))) : (wfTRec k2 TS) := match H39 in (wfTRec _ SS0) return match SS0 return Prop with
    | (tcons l T TS) => (wfTRec k2 TS)
    | _ => True
  end with
    | (wfTRec_tcons l H2 T H3 TS H4) => H4
    | _ => I
  end.
  Definition inversion_wfTy_tvar_1 (k3 : Hvl) (X : (Index ty)) (H40 : (wfTy k3 (tvar X))) : (wfindex k3 X) := match H40 in (wfTy _ S4) return match S4 return Prop with
    | (tvar X) => (wfindex k3 X)
    | _ => True
  end with
    | (wfTy_tvar X H5) => H5
    | _ => I
  end.
  Definition inversion_wfTy_tarr_0 (k5 : Hvl) (T1 : Ty) (T2 : Ty) (H42 : (wfTy k5 (tarr T1 T2))) : (wfTy k5 T1) := match H42 in (wfTy _ S6) return match S6 return Prop with
    | (tarr T1 T2) => (wfTy k5 T1)
    | _ => True
  end with
    | (wfTy_tarr T1 H6 T2 H7) => H6
    | _ => I
  end.
  Definition inversion_wfTy_tarr_1 (k5 : Hvl) (T1 : Ty) (T2 : Ty) (H42 : (wfTy k5 (tarr T1 T2))) : (wfTy k5 T2) := match H42 in (wfTy _ S6) return match S6 return Prop with
    | (tarr T1 T2) => (wfTy k5 T2)
    | _ => True
  end with
    | (wfTy_tarr T1 H6 T2 H7) => H7
    | _ => I
  end.
  Definition inversion_wfTy_tall_1 (k6 : Hvl) (T1 : Ty) (T2 : Ty) (H43 : (wfTy k6 (tall T1 T2))) : (wfTy k6 T1) := match H43 in (wfTy _ S7) return match S7 return Prop with
    | (tall T1 T2) => (wfTy k6 T1)
    | _ => True
  end with
    | (wfTy_tall T1 H8 T2 H9) => H8
    | _ => I
  end.
  Definition inversion_wfTy_tall_2 (k6 : Hvl) (T1 : Ty) (T2 : Ty) (H43 : (wfTy k6 (tall T1 T2))) : (wfTy (HS ty k6) T2) := match H43 in (wfTy _ S7) return match S7 return Prop with
    | (tall T1 T2) => (wfTy (HS ty k6) T2)
    | _ => True
  end with
    | (wfTy_tall T1 H8 T2 H9) => H9
    | _ => I
  end.
  Definition inversion_wfTy_trec_0 (k7 : Hvl) (TS : TRec) (H44 : (wfTy k7 (trec TS))) : (wfTRec k7 TS) := match H44 in (wfTy _ S8) return match S8 return Prop with
    | (trec TS) => (wfTRec k7 TS)
    | _ => True
  end with
    | (wfTy_trec TS H10) => H10
    | _ => I
  end.
  Definition inversion_wfPat_pvar_1 (k8 : Hvl) (T : Ty) (H45 : (wfPat k8 (pvar T))) : (wfTy k8 T) := match H45 in (wfPat _ p10) return match p10 return Prop with
    | (pvar T) => (wfTy k8 T)
    | _ => True
  end with
    | (wfPat_pvar T H11) => H11
    | _ => I
  end.
  Definition inversion_wfPat_prec_0 (k9 : Hvl) (ps : PRec) (H46 : (wfPat k9 (prec ps))) : (wfPRec k9 ps) := match H46 in (wfPat _ p11) return match p11 return Prop with
    | (prec ps) => (wfPRec k9 ps)
    | _ => True
  end with
    | (wfPat_prec ps H12) => H12
    | _ => I
  end.
  Definition inversion_wfPRec_pcons_0 (k11 : Hvl) (l : Lab) (p : Pat) (ps : PRec) (H48 : (wfPRec k11 (pcons l p ps))) : (wfLab k11 l) := match H48 in (wfPRec _ ps11) return match ps11 return Prop with
    | (pcons l p ps) => (wfLab k11 l)
    | _ => True
  end with
    | (wfPRec_pcons l H13 p H14 ps H15) => H13
    | _ => I
  end.
  Definition inversion_wfPRec_pcons_1 (k11 : Hvl) (l : Lab) (p : Pat) (ps : PRec) (H48 : (wfPRec k11 (pcons l p ps))) : (wfPat k11 p) := match H48 in (wfPRec _ ps11) return match ps11 return Prop with
    | (pcons l p ps) => (wfPat k11 p)
    | _ => True
  end with
    | (wfPRec_pcons l H13 p H14 ps H15) => H14
    | _ => I
  end.
  Definition inversion_wfPRec_pcons_2 (k11 : Hvl) (l : Lab) (p : Pat) (ps : PRec) (H48 : (wfPRec k11 (pcons l p ps))) : (wfPRec (appendHvl k11 (appendHvl H0 (bindPat p))) ps) := match H48 in (wfPRec _ ps11) return match ps11 return Prop with
    | (pcons l p ps) => (wfPRec (appendHvl k11 (appendHvl H0 (bindPat p))) ps)
    | _ => True
  end with
    | (wfPRec_pcons l H13 p H14 ps H15) => H15
    | _ => I
  end.
  Definition inversion_wfTm_var_1 (k12 : Hvl) (x : (Index tm)) (H49 : (wfTm k12 (var x))) : (wfindex k12 x) := match H49 in (wfTm _ s) return match s return Prop with
    | (var x) => (wfindex k12 x)
    | _ => True
  end with
    | (wfTm_var x H16) => H16
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k13 : Hvl) (T : Ty) (t : Tm) (H50 : (wfTm k13 (abs T t))) : (wfTy k13 T) := match H50 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTy k13 T)
    | _ => True
  end with
    | (wfTm_abs T H17 t H18) => H17
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k13 : Hvl) (T : Ty) (t : Tm) (H50 : (wfTm k13 (abs T t))) : (wfTm (HS tm k13) t) := match H50 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTm (HS tm k13) t)
    | _ => True
  end with
    | (wfTm_abs T H17 t H18) => H18
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k14 : Hvl) (t1 : Tm) (t2 : Tm) (H51 : (wfTm k14 (app t1 t2))) : (wfTm k14 t1) := match H51 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k14 t1)
    | _ => True
  end with
    | (wfTm_app t1 H19 t2 H20) => H19
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k14 : Hvl) (t1 : Tm) (t2 : Tm) (H51 : (wfTm k14 (app t1 t2))) : (wfTm k14 t2) := match H51 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k14 t2)
    | _ => True
  end with
    | (wfTm_app t1 H19 t2 H20) => H20
    | _ => I
  end.
  Definition inversion_wfTm_tabs_1 (k15 : Hvl) (T : Ty) (t : Tm) (H52 : (wfTm k15 (tabs T t))) : (wfTy k15 T) := match H52 in (wfTm _ s2) return match s2 return Prop with
    | (tabs T t) => (wfTy k15 T)
    | _ => True
  end with
    | (wfTm_tabs T H21 t H22) => H21
    | _ => I
  end.
  Definition inversion_wfTm_tabs_2 (k15 : Hvl) (T : Ty) (t : Tm) (H52 : (wfTm k15 (tabs T t))) : (wfTm (HS ty k15) t) := match H52 in (wfTm _ s2) return match s2 return Prop with
    | (tabs T t) => (wfTm (HS ty k15) t)
    | _ => True
  end with
    | (wfTm_tabs T H21 t H22) => H22
    | _ => I
  end.
  Definition inversion_wfTm_tapp_0 (k16 : Hvl) (t : Tm) (T : Ty) (H53 : (wfTm k16 (tapp t T))) : (wfTm k16 t) := match H53 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTm k16 t)
    | _ => True
  end with
    | (wfTm_tapp t H23 T H24) => H23
    | _ => I
  end.
  Definition inversion_wfTm_tapp_1 (k16 : Hvl) (t : Tm) (T : Ty) (H53 : (wfTm k16 (tapp t T))) : (wfTy k16 T) := match H53 in (wfTm _ s3) return match s3 return Prop with
    | (tapp t T) => (wfTy k16 T)
    | _ => True
  end with
    | (wfTm_tapp t H23 T H24) => H24
    | _ => I
  end.
  Definition inversion_wfTm_rec_0 (k17 : Hvl) (ts : Rec) (H54 : (wfTm k17 (rec ts))) : (wfRec k17 ts) := match H54 in (wfTm _ s4) return match s4 return Prop with
    | (rec ts) => (wfRec k17 ts)
    | _ => True
  end with
    | (wfTm_rec ts H25) => H25
    | _ => I
  end.
  Definition inversion_wfTm_prj_0 (k18 : Hvl) (t : Tm) (l : Lab) (H55 : (wfTm k18 (prj t l))) : (wfTm k18 t) := match H55 in (wfTm _ s5) return match s5 return Prop with
    | (prj t l) => (wfTm k18 t)
    | _ => True
  end with
    | (wfTm_prj t H26 l H27) => H26
    | _ => I
  end.
  Definition inversion_wfTm_prj_1 (k18 : Hvl) (t : Tm) (l : Lab) (H55 : (wfTm k18 (prj t l))) : (wfLab k18 l) := match H55 in (wfTm _ s5) return match s5 return Prop with
    | (prj t l) => (wfLab k18 l)
    | _ => True
  end with
    | (wfTm_prj t H26 l H27) => H27
    | _ => I
  end.
  Definition inversion_wfTm_lett_0 (k19 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H56 : (wfTm k19 (lett p t1 t2))) : (wfPat k19 p) := match H56 in (wfTm _ s6) return match s6 return Prop with
    | (lett p t1 t2) => (wfPat k19 p)
    | _ => True
  end with
    | (wfTm_lett p H28 t1 H29 t2 H30) => H28
    | _ => I
  end.
  Definition inversion_wfTm_lett_1 (k19 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H56 : (wfTm k19 (lett p t1 t2))) : (wfTm k19 t1) := match H56 in (wfTm _ s6) return match s6 return Prop with
    | (lett p t1 t2) => (wfTm k19 t1)
    | _ => True
  end with
    | (wfTm_lett p H28 t1 H29 t2 H30) => H29
    | _ => I
  end.
  Definition inversion_wfTm_lett_2 (k19 : Hvl) (p : Pat) (t1 : Tm) (t2 : Tm) (H56 : (wfTm k19 (lett p t1 t2))) : (wfTm (appendHvl k19 (appendHvl H0 (bindPat p))) t2) := match H56 in (wfTm _ s6) return match s6 return Prop with
    | (lett p t1 t2) => (wfTm (appendHvl k19 (appendHvl H0 (bindPat p))) t2)
    | _ => True
  end with
    | (wfTm_lett p H28 t1 H29 t2 H30) => H30
    | _ => I
  end.
  Definition inversion_wfRec_rcons_0 (k21 : Hvl) (l : Lab) (t : Tm) (ts : Rec) (H58 : (wfRec k21 (rcons l t ts))) : (wfLab k21 l) := match H58 in (wfRec _ ss0) return match ss0 return Prop with
    | (rcons l t ts) => (wfLab k21 l)
    | _ => True
  end with
    | (wfRec_rcons l H31 t H32 ts H33) => H31
    | _ => I
  end.
  Definition inversion_wfRec_rcons_1 (k21 : Hvl) (l : Lab) (t : Tm) (ts : Rec) (H58 : (wfRec k21 (rcons l t ts))) : (wfTm k21 t) := match H58 in (wfRec _ ss0) return match ss0 return Prop with
    | (rcons l t ts) => (wfTm k21 t)
    | _ => True
  end with
    | (wfRec_rcons l H31 t H32 ts H33) => H32
    | _ => I
  end.
  Definition inversion_wfRec_rcons_2 (k21 : Hvl) (l : Lab) (t : Tm) (ts : Rec) (H58 : (wfRec k21 (rcons l t ts))) : (wfRec k21 ts) := match H58 in (wfRec _ ss0) return match ss0 return Prop with
    | (rcons l t ts) => (wfRec k21 ts)
    | _ => True
  end with
    | (wfRec_rcons l H31 t H32 ts H33) => H33
    | _ => I
  end.
  Scheme ind_wfLab := Induction for wfLab Sort Prop.
  Scheme ind_wfTRec := Induction for wfTRec Sort Prop
  with ind_wfTy := Induction for wfTy Sort Prop.
  Combined Scheme ind_wfTRec_Ty from ind_wfTRec, ind_wfTy.
  Scheme ind_wfPat := Induction for wfPat Sort Prop
  with ind_wfPRec := Induction for wfPRec Sort Prop.
  Combined Scheme ind_wfPat_PRec from ind_wfPat, ind_wfPRec.
  Scheme ind_wfTm := Induction for wfTm Sort Prop
  with ind_wfRec := Induction for wfRec Sort Prop.
  Combined Scheme ind_wfTm_Rec from ind_wfTm, ind_wfRec.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c3 : (Cutoff tm)) (k22 : Hvl) (k23 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k22 : Hvl)
        :
        (shifthvl_tm C0 k22 (HS tm k22))
    | shifthvl_tm_there_tm
        (c3 : (Cutoff tm)) (k22 : Hvl)
        (k23 : Hvl) :
        (shifthvl_tm c3 k22 k23) -> (shifthvl_tm (CS c3) (HS tm k22) (HS tm k23))
    | shifthvl_tm_there_ty
        (c3 : (Cutoff tm)) (k22 : Hvl)
        (k23 : Hvl) :
        (shifthvl_tm c3 k22 k23) -> (shifthvl_tm c3 (HS ty k22) (HS ty k23)).
  Inductive shifthvl_ty : (forall (c3 : (Cutoff ty)) (k22 : Hvl) (k23 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k22 : Hvl)
        :
        (shifthvl_ty C0 k22 (HS ty k22))
    | shifthvl_ty_there_tm
        (c3 : (Cutoff ty)) (k22 : Hvl)
        (k23 : Hvl) :
        (shifthvl_ty c3 k22 k23) -> (shifthvl_ty c3 (HS tm k22) (HS tm k23))
    | shifthvl_ty_there_ty
        (c3 : (Cutoff ty)) (k22 : Hvl)
        (k23 : Hvl) :
        (shifthvl_ty c3 k22 k23) -> (shifthvl_ty (CS c3) (HS ty k22) (HS ty k23)).
  Lemma weaken_shifthvl_tm  :
    (forall (k22 : Hvl) {c3 : (Cutoff tm)} {k23 : Hvl} {k24 : Hvl} ,
      (shifthvl_tm c3 k23 k24) -> (shifthvl_tm (weakenCutofftm c3 k22) (appendHvl k23 k22) (appendHvl k24 k22))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k22 : Hvl) {c3 : (Cutoff ty)} {k23 : Hvl} {k24 : Hvl} ,
      (shifthvl_ty c3 k23 k24) -> (shifthvl_ty (weakenCutoffty c3 k22) (appendHvl k23 k22) (appendHvl k24 k22))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c3 : (Cutoff tm)) (k22 : Hvl) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) (x6 : (Index tm)) ,
      (wfindex k22 x6) -> (wfindex k23 (shiftIndex c3 x6))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c3 : (Cutoff tm)) (k22 : Hvl) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) (X7 : (Index ty)) ,
      (wfindex k22 X7) -> (wfindex k23 X7)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c3 : (Cutoff ty)) (k22 : Hvl) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) (x6 : (Index tm)) ,
      (wfindex k22 x6) -> (wfindex k23 x6)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c3 : (Cutoff ty)) (k22 : Hvl) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) (X7 : (Index ty)) ,
      (wfindex k22 X7) -> (wfindex k23 (tshiftIndex c3 X7))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfLab : (forall (k22 : Hvl) ,
    (forall (l7 : Lab) (wf : (wfLab k22 l7)) ,
      (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
        (shifthvl_tm c3 k22 k23) -> (wfLab k23 l7)))) := (fun (k22 : Hvl) =>
    (ind_wfLab k22 (fun (l7 : Lab) (wf : (wfLab k22 l7)) =>
      (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
        (shifthvl_tm c3 k22 k23) -> (wfLab k23 l7))) (fun (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
      (wfLab_L0 k23)) (fun (l : Lab) (wf : (wfLab k22 l)) IHl (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
      (wfLab_LS k23 (IHl c3 k23 (weaken_shifthvl_tm H0 ins)))))).
  Definition tshift_wfLab : (forall (k22 : Hvl) ,
    (forall (l7 : Lab) (wf : (wfLab k22 l7)) ,
      (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
        (shifthvl_ty c3 k22 k23) -> (wfLab k23 l7)))) := (fun (k22 : Hvl) =>
    (ind_wfLab k22 (fun (l7 : Lab) (wf : (wfLab k22 l7)) =>
      (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
        (shifthvl_ty c3 k22 k23) -> (wfLab k23 l7))) (fun (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
      (wfLab_L0 k23)) (fun (l : Lab) (wf : (wfLab k22 l)) IHl (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
      (wfLab_LS k23 (IHl c3 k23 (weaken_shifthvl_ty H0 ins)))))).
  Definition shift_wfTRec_Ty : (forall (k22 : Hvl) ,
    (forall (SS1 : TRec) (wf : (wfTRec k22 SS1)) ,
      (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
        (shifthvl_tm c3 k22 k23) -> (wfTRec k23 SS1))) /\
    (forall (S9 : Ty) (wf : (wfTy k22 S9)) ,
      (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
        (shifthvl_tm c3 k22 k23) -> (wfTy k23 S9)))) := (ind_wfTRec_Ty (fun (k22 : Hvl) (SS1 : TRec) (wf : (wfTRec k22 SS1)) =>
    (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
      (shifthvl_tm c3 k22 k23) -> (wfTRec k23 SS1))) (fun (k22 : Hvl) (S9 : Ty) (wf : (wfTy k22 S9)) =>
    (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
      (shifthvl_tm c3 k22 k23) -> (wfTy k23 S9))) (fun (k22 : Hvl) (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTRec_tnil k23)) (fun (k22 : Hvl) (l : Lab) (wf : (wfLab k22 l)) (T : Ty) (wf0 : (wfTy k22 T)) IHT (TS : TRec) (wf1 : (wfTRec k22 TS)) IHTS (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTRec_tcons k23 (shift_wfLab k22 l wf c3 k23 (weaken_shifthvl_tm H0 ins)) (IHT c3 k23 (weaken_shifthvl_tm H0 ins)) (IHTS c3 k23 (weaken_shifthvl_tm H0 ins)))) (fun (k22 : Hvl) (X7 : (Index ty)) (wfi : (wfindex k22 X7)) (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTy_tvar k23 _ (shift_wfindex_ty c3 k22 k23 ins X7 wfi))) (fun (k22 : Hvl) (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTy_top k23)) (fun (k22 : Hvl) (T1 : Ty) (wf : (wfTy k22 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k22 T2)) IHT2 (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTy_tarr k23 (IHT1 c3 k23 (weaken_shifthvl_tm H0 ins)) (IHT2 c3 k23 (weaken_shifthvl_tm H0 ins)))) (fun (k22 : Hvl) (T1 : Ty) (wf : (wfTy k22 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS ty k22) T2)) IHT2 (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTy_tall k23 (IHT1 c3 k23 (weaken_shifthvl_tm H0 ins)) (IHT2 c3 (HS ty k23) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k22 : Hvl) (TS : TRec) (wf : (wfTRec k22 TS)) IHTS (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTy_trec k23 (IHTS c3 k23 (weaken_shifthvl_tm H0 ins))))).
  Lemma shift_wfTRec (k22 : Hvl) :
    (forall (SS1 : TRec) (wf : (wfTRec k22 SS1)) ,
      (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
        (shifthvl_tm c3 k22 k23) -> (wfTRec k23 SS1))).
  Proof.
    pose proof ((shift_wfTRec_Ty k22)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_wfTy (k22 : Hvl) :
    (forall (S9 : Ty) (wf0 : (wfTy k22 S9)) ,
      (forall (c4 : (Cutoff tm)) (k24 : Hvl) ,
        (shifthvl_tm c4 k22 k24) -> (wfTy k24 S9))).
  Proof.
    pose proof ((shift_wfTRec_Ty k22)).
    destruct_conjs .
    easy .
  Qed.
  Definition tshift_wfTRec_Ty : (forall (k22 : Hvl) ,
    (forall (SS1 : TRec) (wf : (wfTRec k22 SS1)) ,
      (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
        (shifthvl_ty c3 k22 k23) -> (wfTRec k23 (tshiftTRec c3 SS1)))) /\
    (forall (S9 : Ty) (wf : (wfTy k22 S9)) ,
      (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
        (shifthvl_ty c3 k22 k23) -> (wfTy k23 (tshiftTy c3 S9))))) := (ind_wfTRec_Ty (fun (k22 : Hvl) (SS1 : TRec) (wf : (wfTRec k22 SS1)) =>
    (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
      (shifthvl_ty c3 k22 k23) -> (wfTRec k23 (tshiftTRec c3 SS1)))) (fun (k22 : Hvl) (S9 : Ty) (wf : (wfTy k22 S9)) =>
    (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
      (shifthvl_ty c3 k22 k23) -> (wfTy k23 (tshiftTy c3 S9)))) (fun (k22 : Hvl) (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTRec_tnil k23)) (fun (k22 : Hvl) (l : Lab) (wf : (wfLab k22 l)) (T : Ty) (wf0 : (wfTy k22 T)) IHT (TS : TRec) (wf1 : (wfTRec k22 TS)) IHTS (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTRec_tcons k23 (tshift_wfLab k22 l wf c3 k23 (weaken_shifthvl_ty H0 ins)) (IHT c3 k23 (weaken_shifthvl_ty H0 ins)) (IHTS c3 k23 (weaken_shifthvl_ty H0 ins)))) (fun (k22 : Hvl) (X7 : (Index ty)) (wfi : (wfindex k22 X7)) (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTy_tvar k23 _ (tshift_wfindex_ty c3 k22 k23 ins X7 wfi))) (fun (k22 : Hvl) (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTy_top k23)) (fun (k22 : Hvl) (T1 : Ty) (wf : (wfTy k22 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k22 T2)) IHT2 (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTy_tarr k23 (IHT1 c3 k23 (weaken_shifthvl_ty H0 ins)) (IHT2 c3 k23 (weaken_shifthvl_ty H0 ins)))) (fun (k22 : Hvl) (T1 : Ty) (wf : (wfTy k22 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy (HS ty k22) T2)) IHT2 (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTy_tall k23 (IHT1 c3 k23 (weaken_shifthvl_ty H0 ins)) (IHT2 (CS c3) (HS ty k23) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k22 : Hvl) (TS : TRec) (wf : (wfTRec k22 TS)) IHTS (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTy_trec k23 (IHTS c3 k23 (weaken_shifthvl_ty H0 ins))))).
  Lemma tshift_wfTRec (k22 : Hvl) :
    (forall (SS1 : TRec) (wf : (wfTRec k22 SS1)) ,
      (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
        (shifthvl_ty c3 k22 k23) -> (wfTRec k23 (tshiftTRec c3 SS1)))).
  Proof.
    pose proof ((tshift_wfTRec_Ty k22)).
    destruct_conjs .
    easy .
  Qed.
  Lemma tshift_wfTy (k22 : Hvl) :
    (forall (S9 : Ty) (wf0 : (wfTy k22 S9)) ,
      (forall (c4 : (Cutoff ty)) (k24 : Hvl) ,
        (shifthvl_ty c4 k22 k24) -> (wfTy k24 (tshiftTy c4 S9)))).
  Proof.
    pose proof ((tshift_wfTRec_Ty k22)).
    destruct_conjs .
    easy .
  Qed.
  Definition shift_wfPat_PRec : (forall (k22 : Hvl) ,
    (forall (p12 : Pat) (wf : (wfPat k22 p12)) ,
      (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
        (shifthvl_tm c3 k22 k23) -> (wfPat k23 p12))) /\
    (forall (ps12 : PRec) (wf : (wfPRec k22 ps12)) ,
      (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
        (shifthvl_tm c3 k22 k23) -> (wfPRec k23 ps12)))) := (ind_wfPat_PRec (fun (k22 : Hvl) (p12 : Pat) (wf : (wfPat k22 p12)) =>
    (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
      (shifthvl_tm c3 k22 k23) -> (wfPat k23 p12))) (fun (k22 : Hvl) (ps12 : PRec) (wf : (wfPRec k22 ps12)) =>
    (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
      (shifthvl_tm c3 k22 k23) -> (wfPRec k23 ps12))) (fun (k22 : Hvl) (T : Ty) (wf : (wfTy k22 T)) (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfPat_pvar k23 (shift_wfTy k22 T wf c3 k23 (weaken_shifthvl_tm H0 ins)))) (fun (k22 : Hvl) (ps : PRec) (wf : (wfPRec k22 ps)) IHps (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfPat_prec k23 (IHps c3 k23 (weaken_shifthvl_tm H0 ins)))) (fun (k22 : Hvl) (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfPRec_pnil k23)) (fun (k22 : Hvl) (l : Lab) (wf : (wfLab k22 l)) (p : Pat) (wf0 : (wfPat k22 p)) IHp (ps : PRec) (wf1 : (wfPRec (appendHvl k22 (appendHvl H0 (bindPat p))) ps)) IHps (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfPRec_pcons k23 (shift_wfLab k22 l wf c3 k23 (weaken_shifthvl_tm H0 ins)) (IHp c3 k23 (weaken_shifthvl_tm H0 ins)) (IHps (weakenCutofftm c3 (appendHvl H0 (bindPat p))) (appendHvl k23 (appendHvl H0 (bindPat p))) (weaken_shifthvl_tm (appendHvl H0 (bindPat p)) ins))))).
  Lemma shift_wfPat (k22 : Hvl) :
    (forall (p12 : Pat) (wf : (wfPat k22 p12)) ,
      (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
        (shifthvl_tm c3 k22 k23) -> (wfPat k23 p12))).
  Proof.
    pose proof ((shift_wfPat_PRec k22)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_wfPRec (k22 : Hvl) :
    (forall (ps12 : PRec) (wf0 : (wfPRec k22 ps12)) ,
      (forall (c4 : (Cutoff tm)) (k24 : Hvl) ,
        (shifthvl_tm c4 k22 k24) -> (wfPRec k24 ps12))).
  Proof.
    pose proof ((shift_wfPat_PRec k22)).
    destruct_conjs .
    easy .
  Qed.
  Definition tshift_wfPat_PRec : (forall (k22 : Hvl) ,
    (forall (p12 : Pat) (wf : (wfPat k22 p12)) ,
      (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
        (shifthvl_ty c3 k22 k23) -> (wfPat k23 (tshiftPat c3 p12)))) /\
    (forall (ps12 : PRec) (wf : (wfPRec k22 ps12)) ,
      (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
        (shifthvl_ty c3 k22 k23) -> (wfPRec k23 (tshiftPRec c3 ps12))))) := (ind_wfPat_PRec (fun (k22 : Hvl) (p12 : Pat) (wf : (wfPat k22 p12)) =>
    (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
      (shifthvl_ty c3 k22 k23) -> (wfPat k23 (tshiftPat c3 p12)))) (fun (k22 : Hvl) (ps12 : PRec) (wf : (wfPRec k22 ps12)) =>
    (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
      (shifthvl_ty c3 k22 k23) -> (wfPRec k23 (tshiftPRec c3 ps12)))) (fun (k22 : Hvl) (T : Ty) (wf : (wfTy k22 T)) (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfPat_pvar k23 (tshift_wfTy k22 T wf c3 k23 (weaken_shifthvl_ty H0 ins)))) (fun (k22 : Hvl) (ps : PRec) (wf : (wfPRec k22 ps)) IHps (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfPat_prec k23 (IHps c3 k23 (weaken_shifthvl_ty H0 ins)))) (fun (k22 : Hvl) (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfPRec_pnil k23)) (fun (k22 : Hvl) (l : Lab) (wf : (wfLab k22 l)) (p : Pat) (wf0 : (wfPat k22 p)) IHp (ps : PRec) (wf1 : (wfPRec (appendHvl k22 (appendHvl H0 (bindPat p))) ps)) IHps (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfPRec_pcons k23 (tshift_wfLab k22 l wf c3 k23 (weaken_shifthvl_ty H0 ins)) (IHp c3 k23 (weaken_shifthvl_ty H0 ins)) (eq_ind2 wfPRec (f_equal2 appendHvl (eq_refl k23) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))) eq_refl (IHps (weakenCutoffty c3 (appendHvl H0 (bindPat p))) (appendHvl k23 (appendHvl H0 (bindPat p))) (weaken_shifthvl_ty (appendHvl H0 (bindPat p)) ins)))))).
  Lemma tshift_wfPat (k22 : Hvl) :
    (forall (p12 : Pat) (wf : (wfPat k22 p12)) ,
      (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
        (shifthvl_ty c3 k22 k23) -> (wfPat k23 (tshiftPat c3 p12)))).
  Proof.
    pose proof ((tshift_wfPat_PRec k22)).
    destruct_conjs .
    easy .
  Qed.
  Lemma tshift_wfPRec (k22 : Hvl) :
    (forall (ps12 : PRec) (wf0 : (wfPRec k22 ps12)) ,
      (forall (c4 : (Cutoff ty)) (k24 : Hvl) ,
        (shifthvl_ty c4 k22 k24) -> (wfPRec k24 (tshiftPRec c4 ps12)))).
  Proof.
    pose proof ((tshift_wfPat_PRec k22)).
    destruct_conjs .
    easy .
  Qed.
  Definition shift_wfTm_Rec : (forall (k22 : Hvl) ,
    (forall (s7 : Tm) (wf : (wfTm k22 s7)) ,
      (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
        (shifthvl_tm c3 k22 k23) -> (wfTm k23 (shiftTm c3 s7)))) /\
    (forall (ss1 : Rec) (wf : (wfRec k22 ss1)) ,
      (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
        (shifthvl_tm c3 k22 k23) -> (wfRec k23 (shiftRec c3 ss1))))) := (ind_wfTm_Rec (fun (k22 : Hvl) (s7 : Tm) (wf : (wfTm k22 s7)) =>
    (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
      (shifthvl_tm c3 k22 k23) -> (wfTm k23 (shiftTm c3 s7)))) (fun (k22 : Hvl) (ss1 : Rec) (wf : (wfRec k22 ss1)) =>
    (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
      (shifthvl_tm c3 k22 k23) -> (wfRec k23 (shiftRec c3 ss1)))) (fun (k22 : Hvl) (x6 : (Index tm)) (wfi : (wfindex k22 x6)) (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTm_var k23 _ (shift_wfindex_tm c3 k22 k23 ins x6 wfi))) (fun (k22 : Hvl) (T : Ty) (wf : (wfTy k22 T)) (t : Tm) (wf0 : (wfTm (HS tm k22) t)) IHt (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTm_abs k23 (shift_wfTy k22 T wf c3 k23 (weaken_shifthvl_tm H0 ins)) (IHt (CS c3) (HS tm k23) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k22 : Hvl) (t1 : Tm) (wf : (wfTm k22 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k22 t2)) IHt2 (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTm_app k23 (IHt1 c3 k23 (weaken_shifthvl_tm H0 ins)) (IHt2 c3 k23 (weaken_shifthvl_tm H0 ins)))) (fun (k22 : Hvl) (T : Ty) (wf : (wfTy k22 T)) (t : Tm) (wf0 : (wfTm (HS ty k22) t)) IHt (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTm_tabs k23 (shift_wfTy k22 T wf c3 k23 (weaken_shifthvl_tm H0 ins)) (IHt c3 (HS ty k23) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k22 : Hvl) (t : Tm) (wf : (wfTm k22 t)) IHt (T : Ty) (wf0 : (wfTy k22 T)) (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTm_tapp k23 (IHt c3 k23 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k22 T wf0 c3 k23 (weaken_shifthvl_tm H0 ins)))) (fun (k22 : Hvl) (ts : Rec) (wf : (wfRec k22 ts)) IHts (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTm_rec k23 (IHts c3 k23 (weaken_shifthvl_tm H0 ins)))) (fun (k22 : Hvl) (t : Tm) (wf : (wfTm k22 t)) IHt (l : Lab) (wf0 : (wfLab k22 l)) (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTm_prj k23 (IHt c3 k23 (weaken_shifthvl_tm H0 ins)) (shift_wfLab k22 l wf0 c3 k23 (weaken_shifthvl_tm H0 ins)))) (fun (k22 : Hvl) (p : Pat) (wf : (wfPat k22 p)) (t1 : Tm) (wf0 : (wfTm k22 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (appendHvl k22 (appendHvl H0 (bindPat p))) t2)) IHt2 (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfTm_lett k23 (shift_wfPat k22 p wf c3 k23 (weaken_shifthvl_tm H0 ins)) (IHt1 c3 k23 (weaken_shifthvl_tm H0 ins)) (IHt2 (weakenCutofftm c3 (appendHvl H0 (bindPat p))) (appendHvl k23 (appendHvl H0 (bindPat p))) (weaken_shifthvl_tm (appendHvl H0 (bindPat p)) ins)))) (fun (k22 : Hvl) (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfRec_rnil k23)) (fun (k22 : Hvl) (l : Lab) (wf : (wfLab k22 l)) (t : Tm) (wf0 : (wfTm k22 t)) IHt (ts : Rec) (wf1 : (wfRec k22 ts)) IHts (c3 : (Cutoff tm)) (k23 : Hvl) (ins : (shifthvl_tm c3 k22 k23)) =>
    (wfRec_rcons k23 (shift_wfLab k22 l wf c3 k23 (weaken_shifthvl_tm H0 ins)) (IHt c3 k23 (weaken_shifthvl_tm H0 ins)) (IHts c3 k23 (weaken_shifthvl_tm H0 ins))))).
  Lemma shift_wfTm (k22 : Hvl) :
    (forall (s7 : Tm) (wf : (wfTm k22 s7)) ,
      (forall (c3 : (Cutoff tm)) (k23 : Hvl) ,
        (shifthvl_tm c3 k22 k23) -> (wfTm k23 (shiftTm c3 s7)))).
  Proof.
    pose proof ((shift_wfTm_Rec k22)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_wfRec (k22 : Hvl) :
    (forall (ss1 : Rec) (wf0 : (wfRec k22 ss1)) ,
      (forall (c4 : (Cutoff tm)) (k24 : Hvl) ,
        (shifthvl_tm c4 k22 k24) -> (wfRec k24 (shiftRec c4 ss1)))).
  Proof.
    pose proof ((shift_wfTm_Rec k22)).
    destruct_conjs .
    easy .
  Qed.
  Definition tshift_wfTm_Rec : (forall (k22 : Hvl) ,
    (forall (s7 : Tm) (wf : (wfTm k22 s7)) ,
      (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
        (shifthvl_ty c3 k22 k23) -> (wfTm k23 (tshiftTm c3 s7)))) /\
    (forall (ss1 : Rec) (wf : (wfRec k22 ss1)) ,
      (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
        (shifthvl_ty c3 k22 k23) -> (wfRec k23 (tshiftRec c3 ss1))))) := (ind_wfTm_Rec (fun (k22 : Hvl) (s7 : Tm) (wf : (wfTm k22 s7)) =>
    (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
      (shifthvl_ty c3 k22 k23) -> (wfTm k23 (tshiftTm c3 s7)))) (fun (k22 : Hvl) (ss1 : Rec) (wf : (wfRec k22 ss1)) =>
    (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
      (shifthvl_ty c3 k22 k23) -> (wfRec k23 (tshiftRec c3 ss1)))) (fun (k22 : Hvl) (x6 : (Index tm)) (wfi : (wfindex k22 x6)) (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTm_var k23 _ (tshift_wfindex_tm c3 k22 k23 ins x6 wfi))) (fun (k22 : Hvl) (T : Ty) (wf : (wfTy k22 T)) (t : Tm) (wf0 : (wfTm (HS tm k22) t)) IHt (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTm_abs k23 (tshift_wfTy k22 T wf c3 k23 (weaken_shifthvl_ty H0 ins)) (IHt c3 (HS tm k23) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k22 : Hvl) (t1 : Tm) (wf : (wfTm k22 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k22 t2)) IHt2 (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTm_app k23 (IHt1 c3 k23 (weaken_shifthvl_ty H0 ins)) (IHt2 c3 k23 (weaken_shifthvl_ty H0 ins)))) (fun (k22 : Hvl) (T : Ty) (wf : (wfTy k22 T)) (t : Tm) (wf0 : (wfTm (HS ty k22) t)) IHt (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTm_tabs k23 (tshift_wfTy k22 T wf c3 k23 (weaken_shifthvl_ty H0 ins)) (IHt (CS c3) (HS ty k23) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k22 : Hvl) (t : Tm) (wf : (wfTm k22 t)) IHt (T : Ty) (wf0 : (wfTy k22 T)) (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTm_tapp k23 (IHt c3 k23 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k22 T wf0 c3 k23 (weaken_shifthvl_ty H0 ins)))) (fun (k22 : Hvl) (ts : Rec) (wf : (wfRec k22 ts)) IHts (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTm_rec k23 (IHts c3 k23 (weaken_shifthvl_ty H0 ins)))) (fun (k22 : Hvl) (t : Tm) (wf : (wfTm k22 t)) IHt (l : Lab) (wf0 : (wfLab k22 l)) (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTm_prj k23 (IHt c3 k23 (weaken_shifthvl_ty H0 ins)) (tshift_wfLab k22 l wf0 c3 k23 (weaken_shifthvl_ty H0 ins)))) (fun (k22 : Hvl) (p : Pat) (wf : (wfPat k22 p)) (t1 : Tm) (wf0 : (wfTm k22 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm (appendHvl k22 (appendHvl H0 (bindPat p))) t2)) IHt2 (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfTm_lett k23 (tshift_wfPat k22 p wf c3 k23 (weaken_shifthvl_ty H0 ins)) (IHt1 c3 k23 (weaken_shifthvl_ty H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k23) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_tshift_bindPat _ _)))) eq_refl (IHt2 (weakenCutoffty c3 (appendHvl H0 (bindPat p))) (appendHvl k23 (appendHvl H0 (bindPat p))) (weaken_shifthvl_ty (appendHvl H0 (bindPat p)) ins))))) (fun (k22 : Hvl) (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfRec_rnil k23)) (fun (k22 : Hvl) (l : Lab) (wf : (wfLab k22 l)) (t : Tm) (wf0 : (wfTm k22 t)) IHt (ts : Rec) (wf1 : (wfRec k22 ts)) IHts (c3 : (Cutoff ty)) (k23 : Hvl) (ins : (shifthvl_ty c3 k22 k23)) =>
    (wfRec_rcons k23 (tshift_wfLab k22 l wf c3 k23 (weaken_shifthvl_ty H0 ins)) (IHt c3 k23 (weaken_shifthvl_ty H0 ins)) (IHts c3 k23 (weaken_shifthvl_ty H0 ins))))).
  Lemma tshift_wfTm (k22 : Hvl) :
    (forall (s7 : Tm) (wf : (wfTm k22 s7)) ,
      (forall (c3 : (Cutoff ty)) (k23 : Hvl) ,
        (shifthvl_ty c3 k22 k23) -> (wfTm k23 (tshiftTm c3 s7)))).
  Proof.
    pose proof ((tshift_wfTm_Rec k22)).
    destruct_conjs .
    easy .
  Qed.
  Lemma tshift_wfRec (k22 : Hvl) :
    (forall (ss1 : Rec) (wf0 : (wfRec k22 ss1)) ,
      (forall (c4 : (Cutoff ty)) (k24 : Hvl) ,
        (shifthvl_ty c4 k22 k24) -> (wfRec k24 (tshiftRec c4 ss1)))).
  Proof.
    pose proof ((tshift_wfTm_Rec k22)).
    destruct_conjs .
    easy .
  Qed.
  Fixpoint weaken_wfLab (k22 : Hvl) {struct k22} :
  (forall (k23 : Hvl) (l7 : Lab) (wf : (wfLab k23 l7)) ,
    (wfLab (appendHvl k23 k22) (weakenLab l7 k22))) :=
    match k22 return (forall (k23 : Hvl) (l7 : Lab) (wf : (wfLab k23 l7)) ,
      (wfLab (appendHvl k23 k22) (weakenLab l7 k22))) with
      | (H0) => (fun (k23 : Hvl) (l7 : Lab) (wf : (wfLab k23 l7)) =>
        wf)
      | (HS tm k22) => (fun (k23 : Hvl) (l7 : Lab) (wf : (wfLab k23 l7)) =>
        (shift_wfLab (appendHvl k23 k22) (weakenLab l7 k22) (weaken_wfLab k22 k23 l7 wf) C0 (HS tm (appendHvl k23 k22)) (shifthvl_tm_here (appendHvl k23 k22))))
      | (HS ty k22) => (fun (k23 : Hvl) (l7 : Lab) (wf : (wfLab k23 l7)) =>
        (tshift_wfLab (appendHvl k23 k22) (weakenLab l7 k22) (weaken_wfLab k22 k23 l7 wf) C0 (HS ty (appendHvl k23 k22)) (shifthvl_ty_here (appendHvl k23 k22))))
    end.
  Fixpoint weaken_wfTRec (k22 : Hvl) {struct k22} :
  (forall (k23 : Hvl) (SS1 : TRec) (wf : (wfTRec k23 SS1)) ,
    (wfTRec (appendHvl k23 k22) (weakenTRec SS1 k22))) :=
    match k22 return (forall (k23 : Hvl) (SS1 : TRec) (wf : (wfTRec k23 SS1)) ,
      (wfTRec (appendHvl k23 k22) (weakenTRec SS1 k22))) with
      | (H0) => (fun (k23 : Hvl) (SS1 : TRec) (wf : (wfTRec k23 SS1)) =>
        wf)
      | (HS tm k22) => (fun (k23 : Hvl) (SS1 : TRec) (wf : (wfTRec k23 SS1)) =>
        (shift_wfTRec (appendHvl k23 k22) (weakenTRec SS1 k22) (weaken_wfTRec k22 k23 SS1 wf) C0 (HS tm (appendHvl k23 k22)) (shifthvl_tm_here (appendHvl k23 k22))))
      | (HS ty k22) => (fun (k23 : Hvl) (SS1 : TRec) (wf : (wfTRec k23 SS1)) =>
        (tshift_wfTRec (appendHvl k23 k22) (weakenTRec SS1 k22) (weaken_wfTRec k22 k23 SS1 wf) C0 (HS ty (appendHvl k23 k22)) (shifthvl_ty_here (appendHvl k23 k22))))
    end.
  Fixpoint weaken_wfTy (k22 : Hvl) {struct k22} :
  (forall (k23 : Hvl) (S9 : Ty) (wf : (wfTy k23 S9)) ,
    (wfTy (appendHvl k23 k22) (weakenTy S9 k22))) :=
    match k22 return (forall (k23 : Hvl) (S9 : Ty) (wf : (wfTy k23 S9)) ,
      (wfTy (appendHvl k23 k22) (weakenTy S9 k22))) with
      | (H0) => (fun (k23 : Hvl) (S9 : Ty) (wf : (wfTy k23 S9)) =>
        wf)
      | (HS tm k22) => (fun (k23 : Hvl) (S9 : Ty) (wf : (wfTy k23 S9)) =>
        (shift_wfTy (appendHvl k23 k22) (weakenTy S9 k22) (weaken_wfTy k22 k23 S9 wf) C0 (HS tm (appendHvl k23 k22)) (shifthvl_tm_here (appendHvl k23 k22))))
      | (HS ty k22) => (fun (k23 : Hvl) (S9 : Ty) (wf : (wfTy k23 S9)) =>
        (tshift_wfTy (appendHvl k23 k22) (weakenTy S9 k22) (weaken_wfTy k22 k23 S9 wf) C0 (HS ty (appendHvl k23 k22)) (shifthvl_ty_here (appendHvl k23 k22))))
    end.
  Fixpoint weaken_wfPat (k22 : Hvl) {struct k22} :
  (forall (k23 : Hvl) (p12 : Pat) (wf : (wfPat k23 p12)) ,
    (wfPat (appendHvl k23 k22) (weakenPat p12 k22))) :=
    match k22 return (forall (k23 : Hvl) (p12 : Pat) (wf : (wfPat k23 p12)) ,
      (wfPat (appendHvl k23 k22) (weakenPat p12 k22))) with
      | (H0) => (fun (k23 : Hvl) (p12 : Pat) (wf : (wfPat k23 p12)) =>
        wf)
      | (HS tm k22) => (fun (k23 : Hvl) (p12 : Pat) (wf : (wfPat k23 p12)) =>
        (shift_wfPat (appendHvl k23 k22) (weakenPat p12 k22) (weaken_wfPat k22 k23 p12 wf) C0 (HS tm (appendHvl k23 k22)) (shifthvl_tm_here (appendHvl k23 k22))))
      | (HS ty k22) => (fun (k23 : Hvl) (p12 : Pat) (wf : (wfPat k23 p12)) =>
        (tshift_wfPat (appendHvl k23 k22) (weakenPat p12 k22) (weaken_wfPat k22 k23 p12 wf) C0 (HS ty (appendHvl k23 k22)) (shifthvl_ty_here (appendHvl k23 k22))))
    end.
  Fixpoint weaken_wfPRec (k22 : Hvl) {struct k22} :
  (forall (k23 : Hvl) (ps12 : PRec) (wf : (wfPRec k23 ps12)) ,
    (wfPRec (appendHvl k23 k22) (weakenPRec ps12 k22))) :=
    match k22 return (forall (k23 : Hvl) (ps12 : PRec) (wf : (wfPRec k23 ps12)) ,
      (wfPRec (appendHvl k23 k22) (weakenPRec ps12 k22))) with
      | (H0) => (fun (k23 : Hvl) (ps12 : PRec) (wf : (wfPRec k23 ps12)) =>
        wf)
      | (HS tm k22) => (fun (k23 : Hvl) (ps12 : PRec) (wf : (wfPRec k23 ps12)) =>
        (shift_wfPRec (appendHvl k23 k22) (weakenPRec ps12 k22) (weaken_wfPRec k22 k23 ps12 wf) C0 (HS tm (appendHvl k23 k22)) (shifthvl_tm_here (appendHvl k23 k22))))
      | (HS ty k22) => (fun (k23 : Hvl) (ps12 : PRec) (wf : (wfPRec k23 ps12)) =>
        (tshift_wfPRec (appendHvl k23 k22) (weakenPRec ps12 k22) (weaken_wfPRec k22 k23 ps12 wf) C0 (HS ty (appendHvl k23 k22)) (shifthvl_ty_here (appendHvl k23 k22))))
    end.
  Fixpoint weaken_wfTm (k22 : Hvl) {struct k22} :
  (forall (k23 : Hvl) (s7 : Tm) (wf : (wfTm k23 s7)) ,
    (wfTm (appendHvl k23 k22) (weakenTm s7 k22))) :=
    match k22 return (forall (k23 : Hvl) (s7 : Tm) (wf : (wfTm k23 s7)) ,
      (wfTm (appendHvl k23 k22) (weakenTm s7 k22))) with
      | (H0) => (fun (k23 : Hvl) (s7 : Tm) (wf : (wfTm k23 s7)) =>
        wf)
      | (HS tm k22) => (fun (k23 : Hvl) (s7 : Tm) (wf : (wfTm k23 s7)) =>
        (shift_wfTm (appendHvl k23 k22) (weakenTm s7 k22) (weaken_wfTm k22 k23 s7 wf) C0 (HS tm (appendHvl k23 k22)) (shifthvl_tm_here (appendHvl k23 k22))))
      | (HS ty k22) => (fun (k23 : Hvl) (s7 : Tm) (wf : (wfTm k23 s7)) =>
        (tshift_wfTm (appendHvl k23 k22) (weakenTm s7 k22) (weaken_wfTm k22 k23 s7 wf) C0 (HS ty (appendHvl k23 k22)) (shifthvl_ty_here (appendHvl k23 k22))))
    end.
  Fixpoint weaken_wfRec (k22 : Hvl) {struct k22} :
  (forall (k23 : Hvl) (ss1 : Rec) (wf : (wfRec k23 ss1)) ,
    (wfRec (appendHvl k23 k22) (weakenRec ss1 k22))) :=
    match k22 return (forall (k23 : Hvl) (ss1 : Rec) (wf : (wfRec k23 ss1)) ,
      (wfRec (appendHvl k23 k22) (weakenRec ss1 k22))) with
      | (H0) => (fun (k23 : Hvl) (ss1 : Rec) (wf : (wfRec k23 ss1)) =>
        wf)
      | (HS tm k22) => (fun (k23 : Hvl) (ss1 : Rec) (wf : (wfRec k23 ss1)) =>
        (shift_wfRec (appendHvl k23 k22) (weakenRec ss1 k22) (weaken_wfRec k22 k23 ss1 wf) C0 (HS tm (appendHvl k23 k22)) (shifthvl_tm_here (appendHvl k23 k22))))
      | (HS ty k22) => (fun (k23 : Hvl) (ss1 : Rec) (wf : (wfRec k23 ss1)) =>
        (tshift_wfRec (appendHvl k23 k22) (weakenRec ss1 k22) (weaken_wfRec k22 k23 ss1 wf) C0 (HS ty (appendHvl k23 k22)) (shifthvl_ty_here (appendHvl k23 k22))))
    end.
End ShiftWellFormed.
Lemma wfLab_cast  :
  (forall (k32 : Hvl) (l8 : Lab) (k33 : Hvl) (l9 : Lab) ,
    (k32 = k33) -> (l8 = l9) -> (wfLab k32 l8) -> (wfLab k33 l9)).
Proof.
  congruence .
Qed.
Lemma wfTRec_cast  :
  (forall (k32 : Hvl) (SS2 : TRec) (k33 : Hvl) (SS3 : TRec) ,
    (k32 = k33) -> (SS2 = SS3) -> (wfTRec k32 SS2) -> (wfTRec k33 SS3)).
Proof.
  congruence .
Qed.
Lemma wfTy_cast  :
  (forall (k32 : Hvl) (S10 : Ty) (k33 : Hvl) (S11 : Ty) ,
    (k32 = k33) -> (S10 = S11) -> (wfTy k32 S10) -> (wfTy k33 S11)).
Proof.
  congruence .
Qed.
Lemma wfPat_cast  :
  (forall (k32 : Hvl) (p13 : Pat) (k33 : Hvl) (p14 : Pat) ,
    (k32 = k33) -> (p13 = p14) -> (wfPat k32 p13) -> (wfPat k33 p14)).
Proof.
  congruence .
Qed.
Lemma wfPRec_cast  :
  (forall (k32 : Hvl) (ps13 : PRec) (k33 : Hvl) (ps14 : PRec) ,
    (k32 = k33) -> (ps13 = ps14) -> (wfPRec k32 ps13) -> (wfPRec k33 ps14)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k32 : Hvl) (s7 : Tm) (k33 : Hvl) (s8 : Tm) ,
    (k32 = k33) -> (s7 = s8) -> (wfTm k32 s7) -> (wfTm k33 s8)).
Proof.
  congruence .
Qed.
Lemma wfRec_cast  :
  (forall (k32 : Hvl) (ss1 : Rec) (k33 : Hvl) (ss2 : Rec) ,
    (k32 = k33) -> (ss1 = ss2) -> (wfRec k32 ss1) -> (wfRec k33 ss2)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : infra.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift_wf.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : wf.
 Hint Resolve shift_wfLab shift_wfPRec shift_wfPat shift_wfRec shift_wfTRec shift_wfTm shift_wfTy tshift_wfLab tshift_wfPRec tshift_wfPat tshift_wfRec tshift_wfTRec tshift_wfTm tshift_wfTy : infra.
 Hint Resolve shift_wfLab shift_wfPRec shift_wfPat shift_wfRec shift_wfTRec shift_wfTm shift_wfTy tshift_wfLab tshift_wfPRec tshift_wfPat tshift_wfRec tshift_wfTRec tshift_wfTm tshift_wfTy : shift.
 Hint Resolve shift_wfLab shift_wfPRec shift_wfPat shift_wfRec shift_wfTRec shift_wfTm shift_wfTy tshift_wfLab tshift_wfPRec tshift_wfPat tshift_wfRec tshift_wfTRec tshift_wfTm tshift_wfTy : shift_wf.
 Hint Resolve shift_wfLab shift_wfPRec shift_wfPat shift_wfRec shift_wfTRec shift_wfTm shift_wfTy tshift_wfLab tshift_wfPRec tshift_wfPat tshift_wfRec tshift_wfTRec tshift_wfTm tshift_wfTy : wf.
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
  Inductive substhvl_tm (k22 : Hvl) : (forall (d3 : (Trace tm)) (k23 : Hvl) (k24 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k22 X0 (HS tm k22) k22)
    | substhvl_tm_there_tm
        {d3 : (Trace tm)} {k23 : Hvl}
        {k24 : Hvl} :
        (substhvl_tm k22 d3 k23 k24) -> (substhvl_tm k22 (XS tm d3) (HS tm k23) (HS tm k24))
    | substhvl_tm_there_ty
        {d3 : (Trace tm)} {k23 : Hvl}
        {k24 : Hvl} :
        (substhvl_tm k22 d3 k23 k24) -> (substhvl_tm k22 (XS ty d3) (HS ty k23) (HS ty k24)).
  Inductive substhvl_ty (k22 : Hvl) : (forall (d3 : (Trace ty)) (k23 : Hvl) (k24 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k22 X0 (HS ty k22) k22)
    | substhvl_ty_there_tm
        {d3 : (Trace ty)} {k23 : Hvl}
        {k24 : Hvl} :
        (substhvl_ty k22 d3 k23 k24) -> (substhvl_ty k22 (XS tm d3) (HS tm k23) (HS tm k24))
    | substhvl_ty_there_ty
        {d3 : (Trace ty)} {k23 : Hvl}
        {k24 : Hvl} :
        (substhvl_ty k22 d3 k23 k24) -> (substhvl_ty k22 (XS ty d3) (HS ty k23) (HS ty k24)).
  Lemma weaken_substhvl_tm  :
    (forall {k23 : Hvl} (k22 : Hvl) {d3 : (Trace tm)} {k24 : Hvl} {k25 : Hvl} ,
      (substhvl_tm k23 d3 k24 k25) -> (substhvl_tm k23 (weakenTrace d3 k22) (appendHvl k24 k22) (appendHvl k25 k22))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k23 : Hvl} (k22 : Hvl) {d3 : (Trace ty)} {k24 : Hvl} {k25 : Hvl} ,
      (substhvl_ty k23 d3 k24 k25) -> (substhvl_ty k23 (weakenTrace d3 k22) (appendHvl k24 k22) (appendHvl k25 k22))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k32 : Hvl} {s7 : Tm} (wft : (wfTm k32 s7)) :
    (forall {d3 : (Trace tm)} {k33 : Hvl} {k34 : Hvl} ,
      (substhvl_tm k32 d3 k33 k34) -> (forall {x6 : (Index tm)} ,
        (wfindex k33 x6) -> (wfTm k34 (substIndex d3 s7 x6)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k32 : Hvl} {S10 : Ty} (wft : (wfTy k32 S10)) :
    (forall {d3 : (Trace ty)} {k33 : Hvl} {k34 : Hvl} ,
      (substhvl_ty k32 d3 k33 k34) -> (forall {X7 : (Index ty)} ,
        (wfindex k33 X7) -> (wfTy k34 (tsubstIndex d3 S10 X7)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k32 : Hvl} :
    (forall {d3 : (Trace tm)} {k33 : Hvl} {k34 : Hvl} ,
      (substhvl_tm k32 d3 k33 k34) -> (forall {X7 : (Index ty)} ,
        (wfindex k33 X7) -> (wfindex k34 X7))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k32 : Hvl} :
    (forall {d3 : (Trace ty)} {k33 : Hvl} {k34 : Hvl} ,
      (substhvl_ty k32 d3 k33 k34) -> (forall {x6 : (Index tm)} ,
        (wfindex k33 x6) -> (wfindex k34 x6))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfLab {k32 : Hvl} : (forall (k33 : Hvl) ,
    (forall (l8 : Lab) (wf0 : (wfLab k33 l8)) ,
      (forall {d3 : (Trace tm)} {k34 : Hvl} ,
        (substhvl_tm k32 d3 k33 k34) -> (wfLab k34 l8)))) := (fun (k33 : Hvl) =>
    (ind_wfLab k33 (fun (l8 : Lab) (wf0 : (wfLab k33 l8)) =>
      (forall {d3 : (Trace tm)} {k34 : Hvl} ,
        (substhvl_tm k32 d3 k33 k34) -> (wfLab k34 l8))) (fun {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
      (wfLab_L0 k34)) (fun (l : Lab) (wf0 : (wfLab k33 l)) IHl {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
      (wfLab_LS k34 (IHl (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)))))).
  Definition substhvl_ty_wfLab {k32 : Hvl} : (forall (k33 : Hvl) ,
    (forall (l8 : Lab) (wf0 : (wfLab k33 l8)) ,
      (forall {d3 : (Trace ty)} {k34 : Hvl} ,
        (substhvl_ty k32 d3 k33 k34) -> (wfLab k34 l8)))) := (fun (k33 : Hvl) =>
    (ind_wfLab k33 (fun (l8 : Lab) (wf0 : (wfLab k33 l8)) =>
      (forall {d3 : (Trace ty)} {k34 : Hvl} ,
        (substhvl_ty k32 d3 k33 k34) -> (wfLab k34 l8))) (fun {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
      (wfLab_L0 k34)) (fun (l : Lab) (wf0 : (wfLab k33 l)) IHl {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
      (wfLab_LS k34 (IHl (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)))))).
  Definition substhvl_tm_wfTRec_Ty {k32 : Hvl} : (forall (k33 : Hvl) ,
    (forall (SS2 : TRec) (wf0 : (wfTRec k33 SS2)) ,
      (forall {d3 : (Trace tm)} {k34 : Hvl} ,
        (substhvl_tm k32 d3 k33 k34) -> (wfTRec k34 SS2))) /\
    (forall (S10 : Ty) (wf0 : (wfTy k33 S10)) ,
      (forall {d3 : (Trace tm)} {k34 : Hvl} ,
        (substhvl_tm k32 d3 k33 k34) -> (wfTy k34 S10)))) := (ind_wfTRec_Ty (fun (k33 : Hvl) (SS2 : TRec) (wf0 : (wfTRec k33 SS2)) =>
    (forall {d3 : (Trace tm)} {k34 : Hvl} ,
      (substhvl_tm k32 d3 k33 k34) -> (wfTRec k34 SS2))) (fun (k33 : Hvl) (S10 : Ty) (wf0 : (wfTy k33 S10)) =>
    (forall {d3 : (Trace tm)} {k34 : Hvl} ,
      (substhvl_tm k32 d3 k33 k34) -> (wfTy k34 S10))) (fun (k33 : Hvl) {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfTRec_tnil k34)) (fun (k33 : Hvl) (l : Lab) (wf0 : (wfLab k33 l)) (T : Ty) (wf1 : (wfTy k33 T)) IHT (TS : TRec) (wf2 : (wfTRec k33 TS)) IHTS {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfTRec_tcons k34 (substhvl_tm_wfLab k33 l wf0 (weaken_substhvl_tm H0 del)) (IHT (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)) (IHTS (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)))) (fun (k33 : Hvl) {X7 : (Index ty)} (wfi : (wfindex k33 X7)) {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfTy_tvar k34 _ (substhvl_tm_wfindex_ty del wfi))) (fun (k33 : Hvl) {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfTy_top k34)) (fun (k33 : Hvl) (T1 : Ty) (wf0 : (wfTy k33 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k33 T2)) IHT2 {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfTy_tarr k34 (IHT1 (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)))) (fun (k33 : Hvl) (T1 : Ty) (wf0 : (wfTy k33 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS ty k33) T2)) IHT2 {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfTy_tall k34 (IHT1 (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d3 (HS ty H0)) (HS ty k34) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k33 : Hvl) (TS : TRec) (wf0 : (wfTRec k33 TS)) IHTS {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfTy_trec k34 (IHTS (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del))))).
  Lemma substhvl_tm_wfTRec {k32 : Hvl} (k33 : Hvl) (SS2 : TRec) (wf0 : (wfTRec k33 SS2)) :
    (forall {d3 : (Trace tm)} {k34 : Hvl} ,
      (substhvl_tm k32 d3 k33 k34) -> (wfTRec k34 SS2)).
  Proof.
    apply ((substhvl_tm_wfTRec_Ty k33)).
    auto .
  Qed.
  Lemma substhvl_tm_wfTy {k32 : Hvl} (k33 : Hvl) (S10 : Ty) (wf1 : (wfTy k33 S10)) :
    (forall {d4 : (Trace tm)} {k35 : Hvl} ,
      (substhvl_tm k32 d4 k33 k35) -> (wfTy k35 S10)).
  Proof.
    apply ((substhvl_tm_wfTRec_Ty k33)).
    auto .
  Qed.
  Definition substhvl_ty_wfTRec_Ty {k32 : Hvl} {S10 : Ty} (wf : (wfTy k32 S10)) : (forall (k33 : Hvl) ,
    (forall (SS2 : TRec) (wf0 : (wfTRec k33 SS2)) ,
      (forall {d3 : (Trace ty)} {k34 : Hvl} ,
        (substhvl_ty k32 d3 k33 k34) -> (wfTRec k34 (tsubstTRec d3 S10 SS2)))) /\
    (forall (S11 : Ty) (wf0 : (wfTy k33 S11)) ,
      (forall {d3 : (Trace ty)} {k34 : Hvl} ,
        (substhvl_ty k32 d3 k33 k34) -> (wfTy k34 (tsubstTy d3 S10 S11))))) := (ind_wfTRec_Ty (fun (k33 : Hvl) (SS2 : TRec) (wf0 : (wfTRec k33 SS2)) =>
    (forall {d3 : (Trace ty)} {k34 : Hvl} ,
      (substhvl_ty k32 d3 k33 k34) -> (wfTRec k34 (tsubstTRec d3 S10 SS2)))) (fun (k33 : Hvl) (S11 : Ty) (wf0 : (wfTy k33 S11)) =>
    (forall {d3 : (Trace ty)} {k34 : Hvl} ,
      (substhvl_ty k32 d3 k33 k34) -> (wfTy k34 (tsubstTy d3 S10 S11)))) (fun (k33 : Hvl) {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfTRec_tnil k34)) (fun (k33 : Hvl) (l : Lab) (wf0 : (wfLab k33 l)) (T : Ty) (wf1 : (wfTy k33 T)) IHT (TS : TRec) (wf2 : (wfTRec k33 TS)) IHTS {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfTRec_tcons k34 (substhvl_ty_wfLab k33 l wf0 (weaken_substhvl_ty H0 del)) (IHT (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)) (IHTS (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)))) (fun (k33 : Hvl) {X7 : (Index ty)} (wfi : (wfindex k33 X7)) {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k33 : Hvl) {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfTy_top k34)) (fun (k33 : Hvl) (T1 : Ty) (wf0 : (wfTy k33 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k33 T2)) IHT2 {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfTy_tarr k34 (IHT1 (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)))) (fun (k33 : Hvl) (T1 : Ty) (wf0 : (wfTy k33 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy (HS ty k33) T2)) IHT2 {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfTy_tall k34 (IHT1 (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d3 (HS ty H0)) (HS ty k34) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k33 : Hvl) (TS : TRec) (wf0 : (wfTRec k33 TS)) IHTS {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfTy_trec k34 (IHTS (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del))))).
  Lemma substhvl_ty_wfTRec {k32 : Hvl} {S10 : Ty} (wf : (wfTy k32 S10)) (k33 : Hvl) (SS2 : TRec) (wf0 : (wfTRec k33 SS2)) :
    (forall {d3 : (Trace ty)} {k34 : Hvl} ,
      (substhvl_ty k32 d3 k33 k34) -> (wfTRec k34 (tsubstTRec d3 S10 SS2))).
  Proof.
    apply ((substhvl_ty_wfTRec_Ty wf k33)).
    auto .
  Qed.
  Lemma substhvl_ty_wfTy {k32 : Hvl} {S10 : Ty} (wf : (wfTy k32 S10)) (k33 : Hvl) (S11 : Ty) (wf1 : (wfTy k33 S11)) :
    (forall {d4 : (Trace ty)} {k35 : Hvl} ,
      (substhvl_ty k32 d4 k33 k35) -> (wfTy k35 (tsubstTy d4 S10 S11))).
  Proof.
    apply ((substhvl_ty_wfTRec_Ty wf k33)).
    auto .
  Qed.
  Definition substhvl_tm_wfPat_PRec {k32 : Hvl} : (forall (k33 : Hvl) ,
    (forall (p13 : Pat) (wf0 : (wfPat k33 p13)) ,
      (forall {d3 : (Trace tm)} {k34 : Hvl} ,
        (substhvl_tm k32 d3 k33 k34) -> (wfPat k34 p13))) /\
    (forall (ps13 : PRec) (wf0 : (wfPRec k33 ps13)) ,
      (forall {d3 : (Trace tm)} {k34 : Hvl} ,
        (substhvl_tm k32 d3 k33 k34) -> (wfPRec k34 ps13)))) := (ind_wfPat_PRec (fun (k33 : Hvl) (p13 : Pat) (wf0 : (wfPat k33 p13)) =>
    (forall {d3 : (Trace tm)} {k34 : Hvl} ,
      (substhvl_tm k32 d3 k33 k34) -> (wfPat k34 p13))) (fun (k33 : Hvl) (ps13 : PRec) (wf0 : (wfPRec k33 ps13)) =>
    (forall {d3 : (Trace tm)} {k34 : Hvl} ,
      (substhvl_tm k32 d3 k33 k34) -> (wfPRec k34 ps13))) (fun (k33 : Hvl) (T : Ty) (wf0 : (wfTy k33 T)) {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfPat_pvar k34 (substhvl_tm_wfTy k33 T wf0 (weaken_substhvl_tm H0 del)))) (fun (k33 : Hvl) (ps : PRec) (wf0 : (wfPRec k33 ps)) IHps {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfPat_prec k34 (IHps (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)))) (fun (k33 : Hvl) {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfPRec_pnil k34)) (fun (k33 : Hvl) (l : Lab) (wf0 : (wfLab k33 l)) (p : Pat) (wf1 : (wfPat k33 p)) IHp (ps : PRec) (wf2 : (wfPRec (appendHvl k33 (appendHvl H0 (bindPat p))) ps)) IHps {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfPRec_pcons k34 (substhvl_tm_wfLab k33 l wf0 (weaken_substhvl_tm H0 del)) (IHp (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)) (IHps (weakenTrace d3 (appendHvl H0 (bindPat p))) (appendHvl k34 (appendHvl H0 (bindPat p))) (weaken_substhvl_tm (appendHvl H0 (bindPat p)) del))))).
  Lemma substhvl_tm_wfPat {k32 : Hvl} (k33 : Hvl) (p13 : Pat) (wf0 : (wfPat k33 p13)) :
    (forall {d3 : (Trace tm)} {k34 : Hvl} ,
      (substhvl_tm k32 d3 k33 k34) -> (wfPat k34 p13)).
  Proof.
    apply ((substhvl_tm_wfPat_PRec k33)).
    auto .
  Qed.
  Lemma substhvl_tm_wfPRec {k32 : Hvl} (k33 : Hvl) (ps13 : PRec) (wf1 : (wfPRec k33 ps13)) :
    (forall {d4 : (Trace tm)} {k35 : Hvl} ,
      (substhvl_tm k32 d4 k33 k35) -> (wfPRec k35 ps13)).
  Proof.
    apply ((substhvl_tm_wfPat_PRec k33)).
    auto .
  Qed.
  Definition substhvl_ty_wfPat_PRec {k32 : Hvl} {S10 : Ty} (wf : (wfTy k32 S10)) : (forall (k33 : Hvl) ,
    (forall (p13 : Pat) (wf0 : (wfPat k33 p13)) ,
      (forall {d3 : (Trace ty)} {k34 : Hvl} ,
        (substhvl_ty k32 d3 k33 k34) -> (wfPat k34 (tsubstPat d3 S10 p13)))) /\
    (forall (ps13 : PRec) (wf0 : (wfPRec k33 ps13)) ,
      (forall {d3 : (Trace ty)} {k34 : Hvl} ,
        (substhvl_ty k32 d3 k33 k34) -> (wfPRec k34 (tsubstPRec d3 S10 ps13))))) := (ind_wfPat_PRec (fun (k33 : Hvl) (p13 : Pat) (wf0 : (wfPat k33 p13)) =>
    (forall {d3 : (Trace ty)} {k34 : Hvl} ,
      (substhvl_ty k32 d3 k33 k34) -> (wfPat k34 (tsubstPat d3 S10 p13)))) (fun (k33 : Hvl) (ps13 : PRec) (wf0 : (wfPRec k33 ps13)) =>
    (forall {d3 : (Trace ty)} {k34 : Hvl} ,
      (substhvl_ty k32 d3 k33 k34) -> (wfPRec k34 (tsubstPRec d3 S10 ps13)))) (fun (k33 : Hvl) (T : Ty) (wf0 : (wfTy k33 T)) {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfPat_pvar k34 (substhvl_ty_wfTy wf k33 T wf0 (weaken_substhvl_ty H0 del)))) (fun (k33 : Hvl) (ps : PRec) (wf0 : (wfPRec k33 ps)) IHps {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfPat_prec k34 (IHps (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)))) (fun (k33 : Hvl) {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfPRec_pnil k34)) (fun (k33 : Hvl) (l : Lab) (wf0 : (wfLab k33 l)) (p : Pat) (wf1 : (wfPat k33 p)) IHp (ps : PRec) (wf2 : (wfPRec (appendHvl k33 (appendHvl H0 (bindPat p))) ps)) IHps {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfPRec_pcons k34 (substhvl_ty_wfLab k33 l wf0 (weaken_substhvl_ty H0 del)) (IHp (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)) (eq_ind2 wfPRec (f_equal2 appendHvl (eq_refl k34) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (IHps (weakenTrace d3 (appendHvl H0 (bindPat p))) (appendHvl k34 (appendHvl H0 (bindPat p))) (weaken_substhvl_ty (appendHvl H0 (bindPat p)) del)))))).
  Lemma substhvl_ty_wfPat {k32 : Hvl} {S10 : Ty} (wf : (wfTy k32 S10)) (k33 : Hvl) (p13 : Pat) (wf0 : (wfPat k33 p13)) :
    (forall {d3 : (Trace ty)} {k34 : Hvl} ,
      (substhvl_ty k32 d3 k33 k34) -> (wfPat k34 (tsubstPat d3 S10 p13))).
  Proof.
    apply ((substhvl_ty_wfPat_PRec wf k33)).
    auto .
  Qed.
  Lemma substhvl_ty_wfPRec {k32 : Hvl} {S10 : Ty} (wf : (wfTy k32 S10)) (k33 : Hvl) (ps13 : PRec) (wf1 : (wfPRec k33 ps13)) :
    (forall {d4 : (Trace ty)} {k35 : Hvl} ,
      (substhvl_ty k32 d4 k33 k35) -> (wfPRec k35 (tsubstPRec d4 S10 ps13))).
  Proof.
    apply ((substhvl_ty_wfPat_PRec wf k33)).
    auto .
  Qed.
  Definition substhvl_tm_wfTm_Rec {k32 : Hvl} {s7 : Tm} (wf : (wfTm k32 s7)) : (forall (k33 : Hvl) ,
    (forall (s8 : Tm) (wf0 : (wfTm k33 s8)) ,
      (forall {d3 : (Trace tm)} {k34 : Hvl} ,
        (substhvl_tm k32 d3 k33 k34) -> (wfTm k34 (substTm d3 s7 s8)))) /\
    (forall (ss1 : Rec) (wf0 : (wfRec k33 ss1)) ,
      (forall {d3 : (Trace tm)} {k34 : Hvl} ,
        (substhvl_tm k32 d3 k33 k34) -> (wfRec k34 (substRec d3 s7 ss1))))) := (ind_wfTm_Rec (fun (k33 : Hvl) (s8 : Tm) (wf0 : (wfTm k33 s8)) =>
    (forall {d3 : (Trace tm)} {k34 : Hvl} ,
      (substhvl_tm k32 d3 k33 k34) -> (wfTm k34 (substTm d3 s7 s8)))) (fun (k33 : Hvl) (ss1 : Rec) (wf0 : (wfRec k33 ss1)) =>
    (forall {d3 : (Trace tm)} {k34 : Hvl} ,
      (substhvl_tm k32 d3 k33 k34) -> (wfRec k34 (substRec d3 s7 ss1)))) (fun (k33 : Hvl) {x6 : (Index tm)} (wfi : (wfindex k33 x6)) {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k33 : Hvl) (T : Ty) (wf0 : (wfTy k33 T)) (t : Tm) (wf1 : (wfTm (HS tm k33) t)) IHt {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfTm_abs k34 (substhvl_tm_wfTy k33 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d3 (HS tm H0)) (HS tm k34) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k33 : Hvl) (t1 : Tm) (wf0 : (wfTm k33 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k33 t2)) IHt2 {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfTm_app k34 (IHt1 (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)))) (fun (k33 : Hvl) (T : Ty) (wf0 : (wfTy k33 T)) (t : Tm) (wf1 : (wfTm (HS ty k33) t)) IHt {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfTm_tabs k34 (substhvl_tm_wfTy k33 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d3 (HS ty H0)) (HS ty k34) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k33 : Hvl) (t : Tm) (wf0 : (wfTm k33 t)) IHt (T : Ty) (wf1 : (wfTy k33 T)) {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfTm_tapp k34 (IHt (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k33 T wf1 (weaken_substhvl_tm H0 del)))) (fun (k33 : Hvl) (ts : Rec) (wf0 : (wfRec k33 ts)) IHts {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfTm_rec k34 (IHts (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)))) (fun (k33 : Hvl) (t : Tm) (wf0 : (wfTm k33 t)) IHt (l : Lab) (wf1 : (wfLab k33 l)) {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfTm_prj k34 (IHt (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfLab k33 l wf1 (weaken_substhvl_tm H0 del)))) (fun (k33 : Hvl) (p : Pat) (wf0 : (wfPat k33 p)) (t1 : Tm) (wf1 : (wfTm k33 t1)) IHt1 (t2 : Tm) (wf2 : (wfTm (appendHvl k33 (appendHvl H0 (bindPat p))) t2)) IHt2 {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfTm_lett k34 (substhvl_tm_wfPat k33 p wf0 (weaken_substhvl_tm H0 del)) (IHt1 (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d3 (appendHvl H0 (bindPat p))) (appendHvl k34 (appendHvl H0 (bindPat p))) (weaken_substhvl_tm (appendHvl H0 (bindPat p)) del)))) (fun (k33 : Hvl) {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfRec_rnil k34)) (fun (k33 : Hvl) (l : Lab) (wf0 : (wfLab k33 l)) (t : Tm) (wf1 : (wfTm k33 t)) IHt (ts : Rec) (wf2 : (wfRec k33 ts)) IHts {d3 : (Trace tm)} {k34 : Hvl} (del : (substhvl_tm k32 d3 k33 k34)) =>
    (wfRec_rcons k34 (substhvl_tm_wfLab k33 l wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del)) (IHts (weakenTrace d3 H0) k34 (weaken_substhvl_tm H0 del))))).
  Lemma substhvl_tm_wfTm {k32 : Hvl} {s7 : Tm} (wf : (wfTm k32 s7)) (k33 : Hvl) (s8 : Tm) (wf0 : (wfTm k33 s8)) :
    (forall {d3 : (Trace tm)} {k34 : Hvl} ,
      (substhvl_tm k32 d3 k33 k34) -> (wfTm k34 (substTm d3 s7 s8))).
  Proof.
    apply ((substhvl_tm_wfTm_Rec wf k33)).
    auto .
  Qed.
  Lemma substhvl_tm_wfRec {k32 : Hvl} {s7 : Tm} (wf : (wfTm k32 s7)) (k33 : Hvl) (ss1 : Rec) (wf1 : (wfRec k33 ss1)) :
    (forall {d4 : (Trace tm)} {k35 : Hvl} ,
      (substhvl_tm k32 d4 k33 k35) -> (wfRec k35 (substRec d4 s7 ss1))).
  Proof.
    apply ((substhvl_tm_wfTm_Rec wf k33)).
    auto .
  Qed.
  Definition substhvl_ty_wfTm_Rec {k32 : Hvl} {S10 : Ty} (wf : (wfTy k32 S10)) : (forall (k33 : Hvl) ,
    (forall (s7 : Tm) (wf0 : (wfTm k33 s7)) ,
      (forall {d3 : (Trace ty)} {k34 : Hvl} ,
        (substhvl_ty k32 d3 k33 k34) -> (wfTm k34 (tsubstTm d3 S10 s7)))) /\
    (forall (ss1 : Rec) (wf0 : (wfRec k33 ss1)) ,
      (forall {d3 : (Trace ty)} {k34 : Hvl} ,
        (substhvl_ty k32 d3 k33 k34) -> (wfRec k34 (tsubstRec d3 S10 ss1))))) := (ind_wfTm_Rec (fun (k33 : Hvl) (s7 : Tm) (wf0 : (wfTm k33 s7)) =>
    (forall {d3 : (Trace ty)} {k34 : Hvl} ,
      (substhvl_ty k32 d3 k33 k34) -> (wfTm k34 (tsubstTm d3 S10 s7)))) (fun (k33 : Hvl) (ss1 : Rec) (wf0 : (wfRec k33 ss1)) =>
    (forall {d3 : (Trace ty)} {k34 : Hvl} ,
      (substhvl_ty k32 d3 k33 k34) -> (wfRec k34 (tsubstRec d3 S10 ss1)))) (fun (k33 : Hvl) {x6 : (Index tm)} (wfi : (wfindex k33 x6)) {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfTm_var k34 _ (substhvl_ty_wfindex_tm del wfi))) (fun (k33 : Hvl) (T : Ty) (wf0 : (wfTy k33 T)) (t : Tm) (wf1 : (wfTm (HS tm k33) t)) IHt {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfTm_abs k34 (substhvl_ty_wfTy wf k33 T wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d3 (HS tm H0)) (HS tm k34) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k33 : Hvl) (t1 : Tm) (wf0 : (wfTm k33 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k33 t2)) IHt2 {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfTm_app k34 (IHt1 (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)))) (fun (k33 : Hvl) (T : Ty) (wf0 : (wfTy k33 T)) (t : Tm) (wf1 : (wfTm (HS ty k33) t)) IHt {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfTm_tabs k34 (substhvl_ty_wfTy wf k33 T wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d3 (HS ty H0)) (HS ty k34) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k33 : Hvl) (t : Tm) (wf0 : (wfTm k33 t)) IHt (T : Ty) (wf1 : (wfTy k33 T)) {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfTm_tapp k34 (IHt (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k33 T wf1 (weaken_substhvl_ty H0 del)))) (fun (k33 : Hvl) (ts : Rec) (wf0 : (wfRec k33 ts)) IHts {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfTm_rec k34 (IHts (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)))) (fun (k33 : Hvl) (t : Tm) (wf0 : (wfTm k33 t)) IHt (l : Lab) (wf1 : (wfLab k33 l)) {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfTm_prj k34 (IHt (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfLab k33 l wf1 (weaken_substhvl_ty H0 del)))) (fun (k33 : Hvl) (p : Pat) (wf0 : (wfPat k33 p)) (t1 : Tm) (wf1 : (wfTm k33 t1)) IHt1 (t2 : Tm) (wf2 : (wfTm (appendHvl k33 (appendHvl H0 (bindPat p))) t2)) IHt2 {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfTm_lett k34 (substhvl_ty_wfPat wf k33 p wf0 (weaken_substhvl_ty H0 del)) (IHt1 (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k34) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_tsubst_bindPat _ _ _)) (eq_refl H0)))) eq_refl (IHt2 (weakenTrace d3 (appendHvl H0 (bindPat p))) (appendHvl k34 (appendHvl H0 (bindPat p))) (weaken_substhvl_ty (appendHvl H0 (bindPat p)) del))))) (fun (k33 : Hvl) {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfRec_rnil k34)) (fun (k33 : Hvl) (l : Lab) (wf0 : (wfLab k33 l)) (t : Tm) (wf1 : (wfTm k33 t)) IHt (ts : Rec) (wf2 : (wfRec k33 ts)) IHts {d3 : (Trace ty)} {k34 : Hvl} (del : (substhvl_ty k32 d3 k33 k34)) =>
    (wfRec_rcons k34 (substhvl_ty_wfLab k33 l wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del)) (IHts (weakenTrace d3 H0) k34 (weaken_substhvl_ty H0 del))))).
  Lemma substhvl_ty_wfTm {k32 : Hvl} {S10 : Ty} (wf : (wfTy k32 S10)) (k33 : Hvl) (s7 : Tm) (wf0 : (wfTm k33 s7)) :
    (forall {d3 : (Trace ty)} {k34 : Hvl} ,
      (substhvl_ty k32 d3 k33 k34) -> (wfTm k34 (tsubstTm d3 S10 s7))).
  Proof.
    apply ((substhvl_ty_wfTm_Rec wf k33)).
    auto .
  Qed.
  Lemma substhvl_ty_wfRec {k32 : Hvl} {S10 : Ty} (wf : (wfTy k32 S10)) (k33 : Hvl) (ss1 : Rec) (wf1 : (wfRec k33 ss1)) :
    (forall {d4 : (Trace ty)} {k35 : Hvl} ,
      (substhvl_ty k32 d4 k33 k35) -> (wfRec k35 (tsubstRec d4 S10 ss1))).
  Proof.
    apply ((substhvl_ty_wfTm_Rec wf k33)).
    auto .
  Qed.
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : infra.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : wf.
 Hint Resolve substhvl_tm_wfLab substhvl_tm_wfPRec substhvl_tm_wfPat substhvl_tm_wfRec substhvl_tm_wfTRec substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfLab substhvl_ty_wfPRec substhvl_ty_wfPat substhvl_ty_wfRec substhvl_ty_wfTRec substhvl_ty_wfTm substhvl_ty_wfTy : infra.
 Hint Resolve substhvl_tm_wfLab substhvl_tm_wfPRec substhvl_tm_wfPat substhvl_tm_wfRec substhvl_tm_wfTRec substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfLab substhvl_ty_wfPRec substhvl_ty_wfPat substhvl_ty_wfRec substhvl_ty_wfTRec substhvl_ty_wfTm substhvl_ty_wfTy : subst.
 Hint Resolve substhvl_tm_wfLab substhvl_tm_wfPRec substhvl_tm_wfPat substhvl_tm_wfRec substhvl_tm_wfTRec substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfLab substhvl_ty_wfPRec substhvl_ty_wfPat substhvl_ty_wfRec substhvl_ty_wfTRec substhvl_ty_wfTm substhvl_ty_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfLab substhvl_tm_wfPRec substhvl_tm_wfPat substhvl_tm_wfRec substhvl_tm_wfTRec substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfLab substhvl_ty_wfPRec substhvl_ty_wfPat substhvl_ty_wfRec substhvl_ty_wfTRec substhvl_ty_wfTm substhvl_ty_wfTy : wf.
 Hint Constructors substhvl_tm substhvl_ty : infra.
 Hint Constructors substhvl_tm substhvl_ty : subst.
 Hint Constructors substhvl_tm substhvl_ty : subst_wf.
 Hint Constructors substhvl_tm substhvl_ty : wf.
Fixpoint subhvl_tm (k32 : Hvl) {struct k32} :
Prop :=
  match k32 with
    | (H0) => True
    | (HS a k32) => match a with
      | (tm) => (subhvl_tm k32)
      | _ => False
    end
  end.
Lemma subhvl_tm_append  :
  (forall (k32 : Hvl) (k33 : Hvl) ,
    (subhvl_tm k32) -> (subhvl_tm k33) -> (subhvl_tm (appendHvl k32 k33))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_tm_append : infra.
 Hint Resolve subhvl_tm_append : wf.
Lemma wfLab_strengthen_subhvl_tm  :
  (forall (k23 : Hvl) (k22 : Hvl) (l7 : Lab) ,
    (subhvl_tm k23) -> (wfLab (appendHvl k22 k23) (weakenLab l7 k23)) -> (wfLab k22 l7)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfPRec_strengthen_subhvl_tm  :
  (forall (k25 : Hvl) (k24 : Hvl) (ps12 : PRec) ,
    (subhvl_tm k25) -> (wfPRec (appendHvl k24 k25) (weakenPRec ps12 k25)) -> (wfPRec k24 ps12)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfPat_strengthen_subhvl_tm  :
  (forall (k27 : Hvl) (k26 : Hvl) (p12 : Pat) ,
    (subhvl_tm k27) -> (wfPat (appendHvl k26 k27) (weakenPat p12 k27)) -> (wfPat k26 p12)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfTRec_strengthen_subhvl_tm  :
  (forall (k29 : Hvl) (k28 : Hvl) (SS1 : TRec) ,
    (subhvl_tm k29) -> (wfTRec (appendHvl k28 k29) (weakenTRec SS1 k29)) -> (wfTRec k28 SS1)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
Lemma wfTy_strengthen_subhvl_tm  :
  (forall (k31 : Hvl) (k30 : Hvl) (S9 : Ty) ,
    (subhvl_tm k31) -> (wfTy (appendHvl k30 k31) (weakenTy S9 k31)) -> (wfTy k30 S9)).
Proof.
  needleGenericWellformedStrengthen .
Qed.
 Hint Extern 2 ((wfLab _ _)) => match goal with
  | H65 : (wfLab (appendHvl _ _) (weakenLab _ _)) |- _ => apply (wfLab_strengthen_subhvl_tm) in H65
end : infra wf.
 Hint Extern 2 ((wfPRec _ _)) => match goal with
  | H66 : (wfPRec (appendHvl _ _) (weakenPRec _ _)) |- _ => apply (wfPRec_strengthen_subhvl_tm) in H66
end : infra wf.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H67 : (wfPat (appendHvl _ _) (weakenPat _ _)) |- _ => apply (wfPat_strengthen_subhvl_tm) in H67
end : infra wf.
 Hint Extern 2 ((wfTRec _ _)) => match goal with
  | H68 : (wfTRec (appendHvl _ _) (weakenTRec _ _)) |- _ => apply (wfTRec_strengthen_subhvl_tm) in H68
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H69 : (wfTy (appendHvl _ _) (weakenTy _ _)) |- _ => apply (wfTy_strengthen_subhvl_tm) in H69
end : infra wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | evar (G : Env) (T : Ty)
    | etvar (G : Env) (T : Ty).
  Fixpoint appendEnv (G : Env) (G0 : Env) :
  Env :=
    match G0 with
      | (empty) => G
      | (evar G1 T) => (evar (appendEnv G G1) T)
      | (etvar G1 T) => (etvar (appendEnv G G1) T)
    end.
  Fixpoint domainEnv (G : Env) :
  Hvl :=
    match G with
      | (empty) => H0
      | (evar G0 T) => (HS tm (domainEnv G0))
      | (etvar G0 T) => (HS ty (domainEnv G0))
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
  Fixpoint shiftEnv (c3 : (Cutoff tm)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shiftEnv c3 G0) T)
      | (etvar G0 T) => (etvar (shiftEnv c3 G0) T)
    end.
  Fixpoint tshiftEnv (c3 : (Cutoff ty)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tshiftEnv c3 G0) (tshiftTy (weakenCutoffty c3 (domainEnv G0)) T))
      | (etvar G0 T) => (etvar (tshiftEnv c3 G0) (tshiftTy (weakenCutoffty c3 (domainEnv G0)) T))
    end.
  Fixpoint weakenEnv (G : Env) (k32 : Hvl) {struct k32} :
  Env :=
    match k32 with
      | (H0) => G
      | (HS tm k32) => (weakenEnv G k32)
      | (HS ty k32) => (tshiftEnv C0 (weakenEnv G k32))
    end.
  Fixpoint substEnv (d3 : (Trace tm)) (s7 : Tm) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d3 s7 G0) T)
      | (etvar G0 T) => (etvar (substEnv d3 s7 G0) T)
    end.
  Fixpoint tsubstEnv (d3 : (Trace ty)) (S10 : Ty) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d3 S10 G0) (tsubstTy (weakenTrace d3 (domainEnv G0)) S10 T))
      | (etvar G0 T) => (etvar (tsubstEnv d3 S10 G0) (tsubstTy (weakenTrace d3 (domainEnv G0)) S10 T))
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c3 : (Cutoff tm)) (G : Env) ,
      ((domainEnv (shiftEnv c3 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_tshiftEnv  :
    (forall (c3 : (Cutoff ty)) (G : Env) ,
      ((domainEnv (tshiftEnv c3 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d3 : (Trace tm)) (s7 : Tm) (G : Env) ,
      ((domainEnv (substEnv d3 s7 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d3 : (Trace ty)) (S10 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d3 S10 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shiftEnv_appendEnv  :
      (forall (c3 : (Cutoff tm)) (G : Env) (G0 : Env) ,
        ((shiftEnv c3 (appendEnv G G0)) = (appendEnv (shiftEnv c3 G) (shiftEnv (weakenCutofftm c3 (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma tshiftEnv_appendEnv  :
      (forall (c3 : (Cutoff ty)) (G : Env) (G0 : Env) ,
        ((tshiftEnv c3 (appendEnv G G0)) = (appendEnv (tshiftEnv c3 G) (tshiftEnv (weakenCutoffty c3 (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d3 : (Trace tm)) (s7 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d3 s7 (appendEnv G G0)) = (appendEnv (substEnv d3 s7 G) (substEnv (weakenTrace d3 (domainEnv G)) s7 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d3 : (Trace ty)) (S10 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d3 S10 (appendEnv G G0)) = (appendEnv (tsubstEnv d3 S10 G) (tsubstEnv (weakenTrace d3 (domainEnv G)) S10 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenLab_append  :
    (forall (l8 : Lab) (k32 : Hvl) (k33 : Hvl) ,
      ((weakenLab (weakenLab l8 k32) k33) = (weakenLab l8 (appendHvl k32 k33)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTRec_append  :
    (forall (SS2 : TRec) (k32 : Hvl) (k33 : Hvl) ,
      ((weakenTRec (weakenTRec SS2 k32) k33) = (weakenTRec SS2 (appendHvl k32 k33)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTy_append  :
    (forall (S10 : Ty) (k32 : Hvl) (k33 : Hvl) ,
      ((weakenTy (weakenTy S10 k32) k33) = (weakenTy S10 (appendHvl k32 k33)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenPat_append  :
    (forall (p13 : Pat) (k32 : Hvl) (k33 : Hvl) ,
      ((weakenPat (weakenPat p13 k32) k33) = (weakenPat p13 (appendHvl k32 k33)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenPRec_append  :
    (forall (ps13 : PRec) (k32 : Hvl) (k33 : Hvl) ,
      ((weakenPRec (weakenPRec ps13 k32) k33) = (weakenPRec ps13 (appendHvl k32 k33)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s7 : Tm) (k32 : Hvl) (k33 : Hvl) ,
      ((weakenTm (weakenTm s7 k32) k33) = (weakenTm s7 (appendHvl k32 k33)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenRec_append  :
    (forall (ss1 : Rec) (k32 : Hvl) (k33 : Hvl) ,
      ((weakenRec (weakenRec ss1 k32) k33) = (weakenRec ss1 (appendHvl k32 k33)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          (T11 : Ty) :
          (wfTy (domainEnv G) T11) -> (lookup_evar (evar G T11) I0 T11)
      | lookup_evar_there_evar
          {G : Env} {x6 : (Index tm)}
          (T12 : Ty) (T13 : Ty) :
          (lookup_evar G x6 T12) -> (lookup_evar (evar G T13) (IS x6) T12)
      | lookup_evar_there_etvar
          {G : Env} {x6 : (Index tm)}
          (T12 : Ty) (T13 : Ty) :
          (lookup_evar G x6 T12) -> (lookup_evar (etvar G T13) x6 (tshiftTy C0 T12)).
    Inductive lookup_etvar : Env -> (Index ty) -> Ty -> Prop :=
      | lookup_etvar_here {G : Env}
          (T12 : Ty) :
          (wfTy (domainEnv G) T12) -> (lookup_etvar (etvar G T12) I0 (tshiftTy C0 T12))
      | lookup_etvar_there_evar
          {G : Env} {X7 : (Index ty)}
          (T13 : Ty) (T14 : Ty) :
          (lookup_etvar G X7 T13) -> (lookup_etvar (evar G T14) X7 T13)
      | lookup_etvar_there_etvar
          {G : Env} {X7 : (Index ty)}
          (T13 : Ty) (T14 : Ty) :
          (lookup_etvar G X7 T13) -> (lookup_etvar (etvar G T14) (IS X7) (tshiftTy C0 T13)).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (T13 : Ty) (T14 : Ty) ,
        (lookup_evar (evar G T13) I0 T14) -> (T13 = T14)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Env) (T13 : Ty) (T14 : Ty) ,
        (lookup_etvar (etvar G T13) I0 T14) -> ((tshiftTy C0 T13) = T14)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x6 : (Index tm)} ,
        (forall (T13 : Ty) ,
          (lookup_evar G x6 T13) -> (forall (T14 : Ty) ,
            (lookup_evar G x6 T14) -> (T13 = T14)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G : Env} {X7 : (Index ty)} ,
        (forall (T13 : Ty) ,
          (lookup_etvar G X7 T13) -> (forall (T14 : Ty) ,
            (lookup_etvar G X7 T14) -> (T13 = T14)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x6 : (Index tm)} (T13 : Ty) ,
        (lookup_evar G x6 T13) -> (wfTy (domainEnv G) T13)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G : Env} {X7 : (Index ty)} (T13 : Ty) ,
        (lookup_etvar G X7 T13) -> (wfTy (domainEnv G) T13)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x6 : (Index tm)} (T13 : Ty) ,
        (lookup_evar G x6 T13) -> (lookup_evar (appendEnv G G0) (weakenIndextm x6 (domainEnv G0)) (weakenTy T13 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X7 : (Index ty)} (T13 : Ty) ,
        (lookup_etvar G X7 T13) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X7 (domainEnv G0)) (weakenTy T13 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x6 : (Index tm)} (T17 : Ty) ,
        (lookup_evar G x6 T17) -> (wfindex (domainEnv G) x6)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X7 : (Index ty)} (T17 : Ty) ,
        (lookup_etvar G X7 T17) -> (wfindex (domainEnv G) X7)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T13 : Ty} :
        (shift_evar C0 G (evar G T13))
    | shiftevar_there_evar
        {c3 : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c3 G G0) -> (shift_evar (CS c3) (evar G T) (evar G0 T))
    | shiftevar_there_etvar
        {c3 : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c3 G G0) -> (shift_evar c3 (etvar G T) (etvar G0 T)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c3 : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c3 G0 G1) -> (shift_evar (weakenCutofftm c3 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G : Env}
        {T13 : Ty} :
        (shift_etvar C0 G (etvar G T13))
    | shiftetvar_there_evar
        {c3 : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c3 G G0) -> (shift_etvar c3 (evar G T) (evar G0 (tshiftTy c3 T)))
    | shiftetvar_there_etvar
        {c3 : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c3 G G0) -> (shift_etvar (CS c3) (etvar G T) (etvar G0 (tshiftTy c3 T))).
  Lemma weaken_shift_etvar  :
    (forall (G : Env) {c3 : (Cutoff ty)} {G0 : Env} {G1 : Env} ,
      (shift_etvar c3 G0 G1) -> (shift_etvar (weakenCutoffty c3 (domainEnv G)) (appendEnv G0 G) (appendEnv G1 (tshiftEnv c3 G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_tm  :
    (forall {c3 : (Cutoff tm)} {G : Env} {G0 : Env} ,
      (shift_evar c3 G G0) -> (shifthvl_tm c3 (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_etvar_shifthvl_ty  :
    (forall {c3 : (Cutoff ty)} {G : Env} {G0 : Env} ,
      (shift_etvar c3 G G0) -> (shifthvl_ty c3 (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Env) (T13 : Ty) (s7 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T13 s7 X0 (evar G T13) G)
    | subst_evar_there_evar
        {d3 : (Trace tm)} {G0 : Env}
        {G1 : Env} (T14 : Ty) :
        (subst_evar G T13 s7 d3 G0 G1) -> (subst_evar G T13 s7 (XS tm d3) (evar G0 T14) (evar G1 T14))
    | subst_evar_there_etvar
        {d3 : (Trace tm)} {G0 : Env}
        {G1 : Env} (T14 : Ty) :
        (subst_evar G T13 s7 d3 G0 G1) -> (subst_evar G T13 s7 (XS ty d3) (etvar G0 T14) (etvar G1 T14)).
  Lemma weaken_subst_evar {G : Env} (T13 : Ty) {s7 : Tm} :
    (forall (G0 : Env) {d3 : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T13 s7 d3 G1 G2) -> (subst_evar G T13 s7 (weakenTrace d3 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (T13 : Ty) (S10 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G T13 S10 X0 (etvar G T13) G)
    | subst_etvar_there_evar
        {d3 : (Trace ty)} {G0 : Env}
        {G1 : Env} (T14 : Ty) :
        (subst_etvar G T13 S10 d3 G0 G1) -> (subst_etvar G T13 S10 (XS tm d3) (evar G0 T14) (evar G1 (tsubstTy d3 S10 T14)))
    | subst_etvar_there_etvar
        {d3 : (Trace ty)} {G0 : Env}
        {G1 : Env} (T14 : Ty) :
        (subst_etvar G T13 S10 d3 G0 G1) -> (subst_etvar G T13 S10 (XS ty d3) (etvar G0 T14) (etvar G1 (tsubstTy d3 S10 T14))).
  Lemma weaken_subst_etvar {G : Env} (T13 : Ty) {S10 : Ty} :
    (forall (G0 : Env) {d3 : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G T13 S10 d3 G1 G2) -> (subst_etvar G T13 S10 (weakenTrace d3 (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d3 S10 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s7 : Tm} (T13 : Ty) :
    (forall {d3 : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T13 s7 d3 G0 G1) -> (substhvl_tm (domainEnv G) d3 (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S10 : Ty} (T14 : Ty) :
    (forall {d3 : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G T14 S10 d3 G0 G1) -> (substhvl_ty (domainEnv G) d3 (domainEnv G0) (domainEnv G1))).
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
  (forall {G : Env} (G0 : Env) {T13 : Ty} (wf : (wfTy (domainEnv G) T13)) ,
    (lookup_evar (appendEnv (evar G T13) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T13 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) {T13 : Ty} (wf : (wfTy (domainEnv G) T13)) ,
    (lookup_etvar (appendEnv (etvar G T13) G0) (weakenIndexty I0 (domainEnv G0)) (weakenTy (tshiftTy C0 T13) (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfLab wfPRec wfPat wfRec wfTRec wfTm wfTy : infra.
 Hint Constructors wfLab wfPRec wfPat wfRec wfTRec wfTm wfTy : wf.
 Hint Extern 10 ((wfLab _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfPRec _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfPat _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfRec _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTRec _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfLab _ _)) => match goal with
  | H65 : (wfLab _ (L0)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfLab _ (LS _)) |- _ => inversion H65; subst; clear H65
end : infra wf.
 Hint Extern 2 ((wfTRec _ _)) => match goal with
  | H65 : (wfTRec _ (tnil)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfTRec _ (tcons _ _ _)) |- _ => inversion H65; subst; clear H65
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H65 : (wfTy _ (tvar _)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfTy _ (top)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfTy _ (tarr _ _)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfTy _ (tall _ _)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfTy _ (trec _)) |- _ => inversion H65; subst; clear H65
end : infra wf.
 Hint Extern 2 ((wfPat _ _)) => match goal with
  | H65 : (wfPat _ (pvar _)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfPat _ (prec _)) |- _ => inversion H65; subst; clear H65
end : infra wf.
 Hint Extern 2 ((wfPRec _ _)) => match goal with
  | H65 : (wfPRec _ (pnil)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfPRec _ (pcons _ _ _)) |- _ => inversion H65; subst; clear H65
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H65 : (wfTm _ (var _)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfTm _ (abs _ _)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfTm _ (app _ _)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfTm _ (tabs _ _)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfTm _ (tapp _ _)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfTm _ (rec _)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfTm _ (prj _ _)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfTm _ (lett _ _ _)) |- _ => inversion H65; subst; clear H65
end : infra wf.
 Hint Extern 2 ((wfRec _ _)) => match goal with
  | H65 : (wfRec _ (rnil)) |- _ => inversion H65; subst; clear H65
  | H65 : (wfRec _ (rcons _ _ _)) |- _ => inversion H65; subst; clear H65
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
  (forall {c3 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c3 G G0)) {x6 : (Index tm)} {T13 : Ty} ,
    (lookup_evar G x6 T13) -> (lookup_evar G0 (shiftIndex c3 x6) T13)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c3 : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c3 G G0)) {X7 : (Index ty)} {T13 : Ty} ,
    (lookup_etvar G X7 T13) -> (lookup_etvar G0 X7 T13)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c3 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c3 G G0)) {x6 : (Index tm)} {T13 : Ty} ,
    (lookup_evar G x6 T13) -> (lookup_evar G0 x6 (tshiftTy c3 T13))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c3 : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c3 G G0)) {X7 : (Index ty)} {T13 : Ty} ,
    (lookup_etvar G X7 T13) -> (lookup_etvar G0 (tshiftIndex c3 X7) (tshiftTy c3 T13))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} (T15 : Ty) {s7 : Tm} :
  (forall {d3 : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T15 s7 d3 G0 G1)) {X7 : (Index ty)} (T16 : Ty) ,
    (lookup_etvar G0 X7 T16) -> (lookup_etvar G1 X7 T16)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} (T15 : Ty) {S10 : Ty} (wf : (wfTy (domainEnv G) S10)) :
  (forall {d3 : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G T15 S10 d3 G0 G1)) {x6 : (Index tm)} (T16 : Ty) ,
    (lookup_evar G0 x6 T16) -> (lookup_evar G1 x6 (tsubstTy d3 S10 T16))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Lab (l5 : Lab) {struct l5} :
nat :=
  match l5 with
    | (L0) => 1
    | (LS l6) => (plus 1 (size_Lab l6))
  end.
Fixpoint size_TRec (SS : TRec) {struct SS} :
nat :=
  match SS with
    | (tnil) => 1
    | (tcons l5 T11 TS1) => (plus 1 (plus (size_Lab l5) (plus (size_Ty T11) (size_TRec TS1))))
  end
with size_Ty (S0 : Ty) {struct S0} :
nat :=
  match S0 with
    | (tvar X7) => 1
    | (top) => 1
    | (tarr T11 T12) => (plus 1 (plus (size_Ty T11) (size_Ty T12)))
    | (tall T13 T14) => (plus 1 (plus (size_Ty T13) (size_Ty T14)))
    | (trec TS1) => (plus 1 (size_TRec TS1))
  end.
Fixpoint size_Pat (p6 : Pat) {struct p6} :
nat :=
  match p6 with
    | (pvar T11) => (plus 1 (size_Ty T11))
    | (prec ps6) => (plus 1 (size_PRec ps6))
  end
with size_PRec (ps6 : PRec) {struct ps6} :
nat :=
  match ps6 with
    | (pnil) => 1
    | (pcons l5 p6 ps7) => (plus 1 (plus (size_Lab l5) (plus (size_Pat p6) (size_PRec ps7))))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x6) => 1
    | (abs T11 t8) => (plus 1 (plus (size_Ty T11) (size_Tm t8)))
    | (app t9 t10) => (plus 1 (plus (size_Tm t9) (size_Tm t10)))
    | (tabs T12 t11) => (plus 1 (plus (size_Ty T12) (size_Tm t11)))
    | (tapp t12 T13) => (plus 1 (plus (size_Tm t12) (size_Ty T13)))
    | (rec ts1) => (plus 1 (size_Rec ts1))
    | (prj t13 l5) => (plus 1 (plus (size_Tm t13) (size_Lab l5)))
    | (lett p6 t14 t15) => (plus 1 (plus (size_Pat p6) (plus (size_Tm t14) (size_Tm t15))))
  end
with size_Rec (ss : Rec) {struct ss} :
nat :=
  match ss with
    | (rnil) => 1
    | (rcons l5 t8 ts1) => (plus 1 (plus (size_Lab l5) (plus (size_Tm t8) (size_Rec ts1))))
  end.
Fixpoint tshift_size_TRec (SS : TRec) (c3 : (Cutoff ty)) {struct SS} :
((size_TRec (tshiftTRec c3 SS)) = (size_TRec SS)) :=
  match SS return ((size_TRec (tshiftTRec c3 SS)) = (size_TRec SS)) with
    | (tnil) => eq_refl
    | (tcons l T TS) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c3) (tshift_size_TRec TS c3))))
  end
with tshift_size_Ty (S4 : Ty) (c3 : (Cutoff ty)) {struct S4} :
((size_Ty (tshiftTy c3 S4)) = (size_Ty S4)) :=
  match S4 return ((size_Ty (tshiftTy c3 S4)) = (size_Ty S4)) with
    | (tvar _) => eq_refl
    | (top) => eq_refl
    | (tarr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c3) (tshift_size_Ty T2 c3)))
    | (tall T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c3) (tshift_size_Ty T2 (CS c3))))
    | (trec TS) => (f_equal2 plus eq_refl (tshift_size_TRec TS c3))
  end.
Fixpoint tshift_size_Pat (p10 : Pat) (c3 : (Cutoff ty)) {struct p10} :
((size_Pat (tshiftPat c3 p10)) = (size_Pat p10)) :=
  match p10 return ((size_Pat (tshiftPat c3 p10)) = (size_Pat p10)) with
    | (pvar T) => (f_equal2 plus eq_refl (tshift_size_Ty T c3))
    | (prec ps) => (f_equal2 plus eq_refl (tshift_size_PRec ps c3))
  end
with tshift_size_PRec (ps10 : PRec) (c3 : (Cutoff ty)) {struct ps10} :
((size_PRec (tshiftPRec c3 ps10)) = (size_PRec ps10)) :=
  match ps10 return ((size_PRec (tshiftPRec c3 ps10)) = (size_PRec ps10)) with
    | (pnil) => eq_refl
    | (pcons l p ps) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Pat p c3) (tshift_size_PRec ps (weakenCutoffty c3 (appendHvl H0 (bindPat p)))))))
  end.
Fixpoint shift_size_Tm (s : Tm) (c3 : (Cutoff tm)) {struct s} :
((size_Tm (shiftTm c3 s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c3 s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c3))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c3) (shift_size_Tm t2 c3)))
    | (tabs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t c3)))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c3) eq_refl))
    | (rec ts) => (f_equal2 plus eq_refl (shift_size_Rec ts c3))
    | (prj t l) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c3) eq_refl))
    | (lett p t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c3) (shift_size_Tm t2 (weakenCutofftm c3 (appendHvl H0 (bindPat p)))))))
  end
with shift_size_Rec (ss : Rec) (c3 : (Cutoff tm)) {struct ss} :
((size_Rec (shiftRec c3 ss)) = (size_Rec ss)) :=
  match ss return ((size_Rec (shiftRec c3 ss)) = (size_Rec ss)) with
    | (rnil) => eq_refl
    | (rcons l t ts) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c3) (shift_size_Rec ts c3))))
  end.
Fixpoint tshift_size_Tm (s : Tm) (c3 : (Cutoff ty)) {struct s} :
((size_Tm (tshiftTm c3 s)) = (size_Tm s)) :=
  match s return ((size_Tm (tshiftTm c3 s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c3) (tshift_size_Tm t c3)))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c3) (tshift_size_Tm t2 c3)))
    | (tabs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c3) (tshift_size_Tm t (CS c3))))
    | (tapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t c3) (tshift_size_Ty T c3)))
    | (rec ts) => (f_equal2 plus eq_refl (tshift_size_Rec ts c3))
    | (prj t l) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t c3) eq_refl))
    | (lett p t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Pat p c3) (f_equal2 plus (tshift_size_Tm t1 c3) (tshift_size_Tm t2 (weakenCutoffty c3 (appendHvl H0 (bindPat p)))))))
  end
with tshift_size_Rec (ss : Rec) (c3 : (Cutoff ty)) {struct ss} :
((size_Rec (tshiftRec c3 ss)) = (size_Rec ss)) :=
  match ss return ((size_Rec (tshiftRec c3 ss)) = (size_Rec ss)) with
    | (rnil) => eq_refl
    | (rcons l t ts) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t c3) (tshift_size_Rec ts c3))))
  end.
 Hint Rewrite tshift_size_PRec tshift_size_Pat shift_size_Rec tshift_size_Rec tshift_size_TRec shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite tshift_size_PRec tshift_size_Pat shift_size_Rec tshift_size_Rec tshift_size_TRec shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Lab  :
  (forall (k : Hvl) (l5 : Lab) ,
    ((size_Lab (weakenLab l5 k)) = (size_Lab l5))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_PRec  :
  (forall (k : Hvl) (ps10 : PRec) ,
    ((size_PRec (weakenPRec ps10 k)) = (size_PRec ps10))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Pat  :
  (forall (k : Hvl) (p10 : Pat) ,
    ((size_Pat (weakenPat p10 k)) = (size_Pat p10))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Rec  :
  (forall (k : Hvl) (ss : Rec) ,
    ((size_Rec (weakenRec ss k)) = (size_Rec ss))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_TRec  :
  (forall (k : Hvl) (SS : TRec) ,
    ((size_TRec (weakenTRec SS k)) = (size_TRec SS))).
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
  (forall (k : Hvl) (S4 : Ty) ,
    ((size_Ty (weakenTy S4 k)) = (size_Ty S4))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Lab weaken_size_PRec weaken_size_Pat weaken_size_Rec weaken_size_TRec weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Lab weaken_size_PRec weaken_size_Pat weaken_size_Rec weaken_size_TRec weaken_size_Tm weaken_size_Ty : weaken_size.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutofftm_append weakenCutoffty_append weakenTrace_append weakenLab_append weakenPRec_append weakenPat_append weakenRec_append weakenTRec_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.