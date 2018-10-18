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
  Fixpoint weakenIndexty (X49 : (Index ty)) (k : Hvl) {struct k} :
  (Index ty) :=
    match k with
      | (H0) => X49
      | (HS a k) => match a with
        | (ty) => (IS (weakenIndexty X49 k))
        | _ => (weakenIndexty X49 k)
      end
    end.
  Lemma weakenIndextm_append  :
    (forall (x6 : (Index tm)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndextm (weakenIndextm x6 k) k0) = (weakenIndextm x6 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexty_append  :
    (forall (X49 : (Index ty)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexty (weakenIndexty X49 k) k0) = (weakenIndexty X49 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Kind : Set :=
    | star 
    | karr (K1 : Kind) (K2 : Kind).
  Scheme ind_Kind := Induction for Kind Sort Prop.
  
  Inductive Ty : Set :=
    | tvar (X : (Index ty))
    | tabs (K : Kind) (T : Ty)
    | tapp (T1 : Ty) (T2 : Ty)
    | tarr (T1 : Ty) (T2 : Ty)
    | tall (K : Kind) (T : Ty).
  Scheme ind_Ty := Induction for Ty Sort Prop.
  
  Inductive Tm : Set :=
    | var (x : (Index tm))
    | abs (T : Ty) (t : Tm)
    | app (t1 : Tm) (t2 : Tm)
    | tyabs (K : Kind) (t : Tm)
    | tyapp (t : Tm) (T : Ty).
  Scheme ind_Tm := Induction for Tm Sort Prop.
End Terms.

Section Functions.
  
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
  Fixpoint tshiftIndex (c : (Cutoff ty)) (X49 : (Index ty)) {struct c} :
  (Index ty) :=
    match c with
      | (C0) => (IS X49)
      | (CS c) => match X49 with
        | (I0) => I0
        | (IS X49) => (IS (tshiftIndex c X49))
      end
    end.
  Fixpoint tshiftTy (c : (Cutoff ty)) (S32 : Ty) {struct S32} :
  Ty :=
    match S32 with
      | (tvar X49) => (tvar (tshiftIndex c X49))
      | (tabs K82 T98) => (tabs K82 (tshiftTy (CS c) T98))
      | (tapp T99 T100) => (tapp (tshiftTy c T99) (tshiftTy c T100))
      | (tarr T101 T102) => (tarr (tshiftTy c T101) (tshiftTy c T102))
      | (tall K83 T103) => (tall K83 (tshiftTy (CS c) T103))
    end.
  Fixpoint shiftTm (c : (Cutoff tm)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var (shiftIndex c x6))
      | (abs T98 t17) => (abs T98 (shiftTm (CS c) t17))
      | (app t18 t19) => (app (shiftTm c t18) (shiftTm c t19))
      | (tyabs K82 t20) => (tyabs K82 (shiftTm c t20))
      | (tyapp t21 T99) => (tyapp (shiftTm c t21) T99)
    end.
  Fixpoint tshiftTm (c : (Cutoff ty)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var x6)
      | (abs T98 t17) => (abs (tshiftTy c T98) (tshiftTm c t17))
      | (app t18 t19) => (app (tshiftTm c t18) (tshiftTm c t19))
      | (tyabs K82 t20) => (tyabs K82 (tshiftTm (CS c) t20))
      | (tyapp t21 T99) => (tyapp (tshiftTm c t21) (tshiftTy c T99))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenKind (K82 : Kind) (k : Hvl) {struct k} :
  Kind :=
    match k with
      | (H0) => K82
      | (HS tm k) => (weakenKind K82 k)
      | (HS ty k) => (weakenKind K82 k)
    end.
  Fixpoint weakenTy (S32 : Ty) (k : Hvl) {struct k} :
  Ty :=
    match k with
      | (H0) => S32
      | (HS tm k) => (weakenTy S32 k)
      | (HS ty k) => (tshiftTy C0 (weakenTy S32 k))
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
        (T98 : (Trace a)).
  
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
  Fixpoint tsubstIndex (d : (Trace ty)) (S32 : Ty) (X49 : (Index ty)) {struct d} :
  Ty :=
    match d with
      | (X0) => match X49 with
        | (I0) => S32
        | (IS X49) => (tvar X49)
      end
      | (XS tm d) => (tsubstIndex d S32 X49)
      | (XS ty d) => match X49 with
        | (I0) => (tvar I0)
        | (IS X49) => (tshiftTy C0 (tsubstIndex d S32 X49))
      end
    end.
  Fixpoint tsubstTy (d : (Trace ty)) (S32 : Ty) (S33 : Ty) {struct S33} :
  Ty :=
    match S33 with
      | (tvar X49) => (tsubstIndex d S32 X49)
      | (tabs K82 T98) => (tabs K82 (tsubstTy (weakenTrace d (HS ty H0)) S32 T98))
      | (tapp T99 T100) => (tapp (tsubstTy d S32 T99) (tsubstTy d S32 T100))
      | (tarr T101 T102) => (tarr (tsubstTy d S32 T101) (tsubstTy d S32 T102))
      | (tall K83 T103) => (tall K83 (tsubstTy (weakenTrace d (HS ty H0)) S32 T103))
    end.
  Fixpoint substTm (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (var x6) => (substIndex d s x6)
      | (abs T98 t17) => (abs T98 (substTm (weakenTrace d (HS tm H0)) s t17))
      | (app t18 t19) => (app (substTm d s t18) (substTm d s t19))
      | (tyabs K82 t20) => (tyabs K82 (substTm (weakenTrace d (HS ty H0)) s t20))
      | (tyapp t21 T99) => (tyapp (substTm d s t21) T99)
    end.
  Fixpoint tsubstTm (d : (Trace ty)) (S32 : Ty) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (var x6) => (var x6)
      | (abs T98 t17) => (abs (tsubstTy d S32 T98) (tsubstTm (weakenTrace d (HS tm H0)) S32 t17))
      | (app t18 t19) => (app (tsubstTm d S32 t18) (tsubstTm d S32 t19))
      | (tyabs K82 t20) => (tyabs K82 (tsubstTm (weakenTrace d (HS ty H0)) S32 t20))
      | (tyapp t21 T99) => (tyapp (tsubstTm d S32 t21) (tsubstTy d S32 T99))
    end.
End Subst.

Global Hint Resolve (f_equal (shiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTm C0)) : cong_shift0.
Global Hint Resolve (f_equal (tshiftTy C0)) : cong_shift0.
 Hint Rewrite weakenCutofftm_append weakenCutoffty_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Section SubstShiftReflection.
  Lemma substIndex0_shiftIndex0_reflection_ind (s : Tm) :
    (forall (k : Hvl) (x6 : (Index tm)) ,
      ((substIndex (weakenTrace X0 k) s (shiftIndex (weakenCutofftm C0 k) x6)) = (var x6))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma tsubstIndex0_tshiftIndex0_reflection_ind (S32 : Ty) :
    (forall (k : Hvl) (X49 : (Index ty)) ,
      ((tsubstIndex (weakenTrace X0 k) S32 (tshiftIndex (weakenCutoffty C0 k) X49)) = (tvar X49))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint tsubst0_tshift0_Ty_reflection_ind (S33 : Ty) (k : Hvl) (S32 : Ty) {struct S33} :
  ((tsubstTy (weakenTrace X0 k) S32 (tshiftTy (weakenCutoffty C0 k) S33)) = S33) :=
    match S33 return ((tsubstTy (weakenTrace X0 k) S32 (tshiftTy (weakenCutoffty C0 k) S33)) = S33) with
      | (tvar X49) => (tsubstIndex0_tshiftIndex0_reflection_ind S32 k X49)
      | (tabs K82 T98) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T98 (HS ty k) S32)))
      | (tapp T99 T100) => (f_equal2 tapp (tsubst0_tshift0_Ty_reflection_ind T99 k S32) (tsubst0_tshift0_Ty_reflection_ind T100 k S32))
      | (tarr T99 T100) => (f_equal2 tarr (tsubst0_tshift0_Ty_reflection_ind T99 k S32) (tsubst0_tshift0_Ty_reflection_ind T100 k S32))
      | (tall K82 T98) => (f_equal2 tall eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Ty_reflection_ind T98 (HS ty k) S32)))
    end.
  Fixpoint subst0_shift0_Tm_reflection_ind (s0 : Tm) (k : Hvl) (s : Tm) {struct s0} :
  ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) :=
    match s0 return ((substTm (weakenTrace X0 k) s (shiftTm (weakenCutofftm C0 k) s0)) = s0) with
      | (var x6) => (substIndex0_shiftIndex0_reflection_ind s k x6)
      | (abs T98 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t17 (HS tm k) s)))
      | (app t18 t19) => (f_equal2 app (subst0_shift0_Tm_reflection_ind t18 k s) (subst0_shift0_Tm_reflection_ind t19 k s))
      | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl) (subst0_shift0_Tm_reflection_ind t17 (HS ty k) s)))
      | (tyapp t17 T98) => (f_equal2 tyapp (subst0_shift0_Tm_reflection_ind t17 k s) eq_refl)
    end.
  Fixpoint tsubst0_tshift0_Tm_reflection_ind (s : Tm) (k : Hvl) (S32 : Ty) {struct s} :
  ((tsubstTm (weakenTrace X0 k) S32 (tshiftTm (weakenCutoffty C0 k) s)) = s) :=
    match s return ((tsubstTm (weakenTrace X0 k) S32 (tshiftTm (weakenCutoffty C0 k) s)) = s) with
      | (var x6) => eq_refl
      | (abs T98 t17) => (f_equal2 abs (tsubst0_tshift0_Ty_reflection_ind T98 k S32) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t17 (HS tm k) S32)))
      | (app t18 t19) => (f_equal2 app (tsubst0_tshift0_Tm_reflection_ind t18 k S32) (tsubst0_tshift0_Tm_reflection_ind t19 k S32))
      | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl) (tsubst0_tshift0_Tm_reflection_ind t17 (HS ty k) S32)))
      | (tyapp t17 T98) => (f_equal2 tyapp (tsubst0_tshift0_Tm_reflection_ind t17 k S32) (tsubst0_tshift0_Ty_reflection_ind T98 k S32))
    end.
  Definition tsubstTy0_tshiftTy0_reflection (S33 : Ty) : (forall (S32 : Ty) ,
    ((tsubstTy X0 S32 (tshiftTy C0 S33)) = S33)) := (tsubst0_tshift0_Ty_reflection_ind S33 H0).
  Definition substTm0_shiftTm0_reflection (s0 : Tm) : (forall (s : Tm) ,
    ((substTm X0 s (shiftTm C0 s0)) = s0)) := (subst0_shift0_Tm_reflection_ind s0 H0).
  Definition tsubstTm0_tshiftTm0_reflection (s : Tm) : (forall (S32 : Ty) ,
    ((tsubstTm X0 S32 (tshiftTm C0 s)) = s)) := (tsubst0_tshift0_Tm_reflection_ind s H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shiftIndex_shiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff tm)) (x6 : (Index tm)) ,
        ((shiftIndex (weakenCutofftm (CS c) k) (shiftIndex (weakenCutofftm C0 k) x6)) = (shiftIndex (weakenCutofftm C0 k) (shiftIndex (weakenCutofftm c k) x6)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma tshiftIndex_tshiftIndex0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff ty)) (X49 : (Index ty)) ,
        ((tshiftIndex (weakenCutoffty (CS c) k) (tshiftIndex (weakenCutoffty C0 k) X49)) = (tshiftIndex (weakenCutoffty C0 k) (tshiftIndex (weakenCutoffty c k) X49)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint tshift_tshift0_Ty_comm_ind (S32 : Ty) (k : Hvl) (c : (Cutoff ty)) {struct S32} :
    ((tshiftTy (weakenCutoffty (CS c) k) (tshiftTy (weakenCutoffty C0 k) S32)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c k) S32))) :=
      match S32 return ((tshiftTy (weakenCutoffty (CS c) k) (tshiftTy (weakenCutoffty C0 k) S32)) = (tshiftTy (weakenCutoffty C0 k) (tshiftTy (weakenCutoffty c k) S32))) with
        | (tvar X49) => (f_equal tvar (tshiftIndex_tshiftIndex0_comm_ind k c X49))
        | (tabs K82 T98) => (f_equal2 tabs eq_refl (tshift_tshift0_Ty_comm_ind T98 (HS ty k) c))
        | (tapp T99 T100) => (f_equal2 tapp (tshift_tshift0_Ty_comm_ind T99 k c) (tshift_tshift0_Ty_comm_ind T100 k c))
        | (tarr T99 T100) => (f_equal2 tarr (tshift_tshift0_Ty_comm_ind T99 k c) (tshift_tshift0_Ty_comm_ind T100 k c))
        | (tall K82 T98) => (f_equal2 tall eq_refl (tshift_tshift0_Ty_comm_ind T98 (HS ty k) c))
      end.
    Fixpoint shift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm (CS c) k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x6) => (f_equal var (shiftIndex_shiftIndex0_comm_ind k c x6))
        | (abs T98 t17) => (f_equal2 abs eq_refl (shift_shift0_Tm_comm_ind t17 (HS tm k) c))
        | (app t18 t19) => (f_equal2 app (shift_shift0_Tm_comm_ind t18 k c) (shift_shift0_Tm_comm_ind t19 k c))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (shift_shift0_Tm_comm_ind t17 (HS ty k) c))
        | (tyapp t17 T98) => (f_equal2 tyapp (shift_shift0_Tm_comm_ind t17 k c) eq_refl)
      end.
    Fixpoint shift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) {struct s} :
    ((shiftTm (weakenCutofftm c k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm c k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (shiftTm (weakenCutofftm c k) s))) with
        | (var x6) => eq_refl
        | (abs T98 t17) => (f_equal2 abs eq_refl (shift_tshift0_Tm_comm_ind t17 (HS tm k) c))
        | (app t18 t19) => (f_equal2 app (shift_tshift0_Tm_comm_ind t18 k c) (shift_tshift0_Tm_comm_ind t19 k c))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (shift_tshift0_Tm_comm_ind t17 (HS ty k) c))
        | (tyapp t17 T98) => (f_equal2 tyapp (shift_tshift0_Tm_comm_ind t17 k c) eq_refl)
      end.
    Fixpoint tshift_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty c k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c k) (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tshiftTm (weakenCutoffty c k) s))) with
        | (var x6) => eq_refl
        | (abs T98 t17) => (f_equal2 abs eq_refl (tshift_shift0_Tm_comm_ind t17 (HS tm k) c))
        | (app t18 t19) => (f_equal2 app (tshift_shift0_Tm_comm_ind t18 k c) (tshift_shift0_Tm_comm_ind t19 k c))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (tshift_shift0_Tm_comm_ind t17 (HS ty k) c))
        | (tyapp t17 T98) => (f_equal2 tyapp (tshift_shift0_Tm_comm_ind t17 k c) eq_refl)
      end.
    Fixpoint tshift_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) {struct s} :
    ((tshiftTm (weakenCutoffty (CS c) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c k) s))) :=
      match s return ((tshiftTm (weakenCutoffty (CS c) k) (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tshiftTm (weakenCutoffty c k) s))) with
        | (var x6) => eq_refl
        | (abs T98 t17) => (f_equal2 abs (tshift_tshift0_Ty_comm_ind T98 k c) (tshift_tshift0_Tm_comm_ind t17 (HS tm k) c))
        | (app t18 t19) => (f_equal2 app (tshift_tshift0_Tm_comm_ind t18 k c) (tshift_tshift0_Tm_comm_ind t19 k c))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (tshift_tshift0_Tm_comm_ind t17 (HS ty k) c))
        | (tyapp t17 T98) => (f_equal2 tyapp (tshift_tshift0_Tm_comm_ind t17 k c) (tshift_tshift0_Ty_comm_ind T98 k c))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition tshift_tshift0_Ty_comm (S32 : Ty) : (forall (c : (Cutoff ty)) ,
      ((tshiftTy (CS c) (tshiftTy C0 S32)) = (tshiftTy C0 (tshiftTy c S32)))) := (tshift_tshift0_Ty_comm_ind S32 H0).
    Definition shift_shift0_Tm_comm (s : Tm) : (forall (c : (Cutoff tm)) ,
      ((shiftTm (CS c) (shiftTm C0 s)) = (shiftTm C0 (shiftTm c s)))) := (shift_shift0_Tm_comm_ind s H0).
    Definition shift_tshift0_Tm_comm (s : Tm) : (forall (c : (Cutoff tm)) ,
      ((shiftTm c (tshiftTm C0 s)) = (tshiftTm C0 (shiftTm c s)))) := (shift_tshift0_Tm_comm_ind s H0).
    Definition tshift_shift0_Tm_comm (s : Tm) : (forall (c : (Cutoff ty)) ,
      ((tshiftTm c (shiftTm C0 s)) = (shiftTm C0 (tshiftTm c s)))) := (tshift_shift0_Tm_comm_ind s H0).
    Definition tshift_tshift0_Tm_comm (s : Tm) : (forall (c : (Cutoff ty)) ,
      ((tshiftTm (CS c) (tshiftTm C0 s)) = (tshiftTm C0 (tshiftTm c s)))) := (tshift_tshift0_Tm_comm_ind s H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : interaction.
 Hint Rewrite shift_shift0_Tm_comm shift_tshift0_Tm_comm tshift_shift0_Tm_comm tshift_tshift0_Tm_comm tshift_tshift0_Ty_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTy_tshiftTy  :
    (forall (k : Hvl) (c : (Cutoff ty)) (S32 : Ty) ,
      ((weakenTy (tshiftTy c S32) k) = (tshiftTy (weakenCutoffty c k) (weakenTy S32 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shiftTm  :
    (forall (k : Hvl) (c : (Cutoff tm)) (s : Tm) ,
      ((weakenTm (shiftTm c s) k) = (shiftTm (weakenCutofftm c k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_tshiftTm  :
    (forall (k : Hvl) (c : (Cutoff ty)) (s : Tm) ,
      ((weakenTm (tshiftTm c s) k) = (tshiftTm (weakenCutoffty c k) (weakenTm s k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shiftTm_substIndex0_comm_ind (c : (Cutoff tm)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((shiftTm (weakenCutofftm c k) (substIndex (weakenTrace X0 k) s x6)) = (substIndex (weakenTrace X0 k) (shiftTm c s) (shiftIndex (weakenCutofftm (CS c) k) x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTm_substIndex0_comm_ind (c : (Cutoff ty)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((tshiftTm (weakenCutoffty c k) (substIndex (weakenTrace X0 k) s x6)) = (substIndex (weakenTrace X0 k) (tshiftTm c s) x6))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tshiftTy_tsubstIndex0_comm_ind (c : (Cutoff ty)) (S32 : Ty) :
      (forall (k : Hvl) (X49 : (Index ty)) ,
        ((tshiftTy (weakenCutoffty c k) (tsubstIndex (weakenTrace X0 k) S32 X49)) = (tsubstIndex (weakenTrace X0 k) (tshiftTy c S32) (tshiftIndex (weakenCutoffty (CS c) k) X49)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint tshift_tsubst0_Ty_comm_ind (S33 : Ty) (k : Hvl) (c : (Cutoff ty)) (S32 : Ty) {struct S33} :
    ((tshiftTy (weakenCutoffty c k) (tsubstTy (weakenTrace X0 k) S32 S33)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c S32) (tshiftTy (weakenCutoffty (CS c) k) S33))) :=
      match S33 return ((tshiftTy (weakenCutoffty c k) (tsubstTy (weakenTrace X0 k) S32 S33)) = (tsubstTy (weakenTrace X0 k) (tshiftTy c S32) (tshiftTy (weakenCutoffty (CS c) k) S33))) with
        | (tvar X49) => (tshiftTy_tsubstIndex0_comm_ind c S32 k X49)
        | (tabs K82 T98) => (f_equal2 tabs eq_refl (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T98 (HS ty k) c S32) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tapp T99 T100) => (f_equal2 tapp (tshift_tsubst0_Ty_comm_ind T99 k c S32) (tshift_tsubst0_Ty_comm_ind T100 k c S32))
        | (tarr T99 T100) => (f_equal2 tarr (tshift_tsubst0_Ty_comm_ind T99 k c S32) (tshift_tsubst0_Ty_comm_ind T100 k c S32))
        | (tall K82 T98) => (f_equal2 tall eq_refl (eq_trans (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Ty_comm_ind T98 (HS ty k) c S32) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
      end.
    Fixpoint shift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff tm)) (s : Tm) {struct s0} :
    ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) :=
      match s0 return ((shiftTm (weakenCutofftm c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (shiftTm c s) (shiftTm (weakenCutofftm (CS c) k) s0))) with
        | (var x6) => (shiftTm_substIndex0_comm_ind c s k x6)
        | (abs T98 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t17 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (shift_subst0_Tm_comm_ind t18 k c s) (shift_subst0_Tm_comm_ind t19 k c s))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_subst0_Tm_comm_ind t17 (HS ty k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tyapp t17 T98) => (f_equal2 tyapp (shift_subst0_Tm_comm_ind t17 k c s) eq_refl)
      end.
    Fixpoint shift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff tm)) (S32 : Ty) {struct s} :
    ((shiftTm (weakenCutofftm c k) (tsubstTm (weakenTrace X0 k) S32 s)) = (tsubstTm (weakenTrace X0 k) S32 (shiftTm (weakenCutofftm c k) s))) :=
      match s return ((shiftTm (weakenCutofftm c k) (tsubstTm (weakenTrace X0 k) S32 s)) = (tsubstTm (weakenTrace X0 k) S32 (shiftTm (weakenCutofftm c k) s))) with
        | (var x6) => eq_refl
        | (abs T98 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t17 (HS tm k) c S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (shift_tsubst0_Tm_comm_ind t18 k c S32) (shift_tsubst0_Tm_comm_ind t19 k c S32))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (shift_tsubst0_Tm_comm_ind t17 (HS ty k) c S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tyapp t17 T98) => (f_equal2 tyapp (shift_tsubst0_Tm_comm_ind t17 k c S32) eq_refl)
      end.
    Fixpoint tshift_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c : (Cutoff ty)) (s : Tm) {struct s0} :
    ((tshiftTm (weakenCutoffty c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c s) (tshiftTm (weakenCutoffty c k) s0))) :=
      match s0 return ((tshiftTm (weakenCutoffty c k) (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tshiftTm c s) (tshiftTm (weakenCutoffty c k) s0))) with
        | (var x6) => (tshiftTm_substIndex0_comm_ind c s k x6)
        | (abs T98 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t17 (HS tm k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (tshift_subst0_Tm_comm_ind t18 k c s) (tshift_subst0_Tm_comm_ind t19 k c s))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_subst0_Tm_comm_ind t17 (HS ty k) c s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tyapp t17 T98) => (f_equal2 tyapp (tshift_subst0_Tm_comm_ind t17 k c s) eq_refl)
      end.
    Fixpoint tshift_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (c : (Cutoff ty)) (S32 : Ty) {struct s} :
    ((tshiftTm (weakenCutoffty c k) (tsubstTm (weakenTrace X0 k) S32 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c S32) (tshiftTm (weakenCutoffty (CS c) k) s))) :=
      match s return ((tshiftTm (weakenCutoffty c k) (tsubstTm (weakenTrace X0 k) S32 s)) = (tsubstTm (weakenTrace X0 k) (tshiftTy c S32) (tshiftTm (weakenCutoffty (CS c) k) s))) with
        | (var x6) => eq_refl
        | (abs T98 t17) => (f_equal2 abs (tshift_tsubst0_Ty_comm_ind T98 k c S32) (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t17 (HS tm k) c S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (tshift_tsubst0_Tm_comm_ind t18 k c S32) (tshift_tsubst0_Tm_comm_ind t19 k c S32))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tshift_tsubst0_Tm_comm_ind t17 (HS ty k) c S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl eq_refl))))
        | (tyapp t17 T98) => (f_equal2 tyapp (tshift_tsubst0_Tm_comm_ind t17 k c S32) (tshift_tsubst0_Ty_comm_ind T98 k c S32))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition tshiftTy_tsubstTy0_comm (S33 : Ty) : (forall (c : (Cutoff ty)) (S32 : Ty) ,
      ((tshiftTy c (tsubstTy X0 S32 S33)) = (tsubstTy X0 (tshiftTy c S32) (tshiftTy (CS c) S33)))) := (tshift_tsubst0_Ty_comm_ind S33 H0).
    Definition shiftTm_substTm0_comm (s0 : Tm) : (forall (c : (Cutoff tm)) (s : Tm) ,
      ((shiftTm c (substTm X0 s s0)) = (substTm X0 (shiftTm c s) (shiftTm (CS c) s0)))) := (shift_subst0_Tm_comm_ind s0 H0).
    Definition shiftTm_tsubstTm0_comm (s : Tm) : (forall (c : (Cutoff tm)) (S32 : Ty) ,
      ((shiftTm c (tsubstTm X0 S32 s)) = (tsubstTm X0 S32 (shiftTm c s)))) := (shift_tsubst0_Tm_comm_ind s H0).
    Definition tshiftTm_substTm0_comm (s0 : Tm) : (forall (c : (Cutoff ty)) (s : Tm) ,
      ((tshiftTm c (substTm X0 s s0)) = (substTm X0 (tshiftTm c s) (tshiftTm c s0)))) := (tshift_subst0_Tm_comm_ind s0 H0).
    Definition tshiftTm_tsubstTm0_comm (s : Tm) : (forall (c : (Cutoff ty)) (S32 : Ty) ,
      ((tshiftTm c (tsubstTm X0 S32 s)) = (tsubstTm X0 (tshiftTy c S32) (tshiftTm (CS c) s)))) := (tshift_tsubst0_Tm_comm_ind s H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma substIndex_shiftTm0_comm_ind (d : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((substIndex (weakenTrace (XS tm d) k) s (shiftIndex (weakenCutofftm C0 k) x6)) = (shiftTm (weakenCutofftm C0 k) (substIndex (weakenTrace d k) s x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma substIndex_tshiftTm0_comm_ind (d : (Trace tm)) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((substIndex (weakenTrace (XS ty d) k) s x6) = (tshiftTm (weakenCutoffty C0 k) (substIndex (weakenTrace d k) s x6)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_shiftTy0_comm_ind (d : (Trace ty)) (S32 : Ty) :
      (forall (k : Hvl) (X49 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS tm d) k) S32 X49) = (tsubstIndex (weakenTrace d k) S32 X49))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma tsubstIndex_tshiftTy0_comm_ind (d : (Trace ty)) (S32 : Ty) :
      (forall (k : Hvl) (X49 : (Index ty)) ,
        ((tsubstIndex (weakenTrace (XS ty d) k) S32 (tshiftIndex (weakenCutoffty C0 k) X49)) = (tshiftTy (weakenCutoffty C0 k) (tsubstIndex (weakenTrace d k) S32 X49)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint tsubst_tshift0_Ty_comm_ind (S33 : Ty) (k : Hvl) (d : (Trace ty)) (S32 : Ty) {struct S33} :
    ((tsubstTy (weakenTrace (XS ty d) k) S32 (tshiftTy (weakenCutoffty C0 k) S33)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d k) S32 S33))) :=
      match S33 return ((tsubstTy (weakenTrace (XS ty d) k) S32 (tshiftTy (weakenCutoffty C0 k) S33)) = (tshiftTy (weakenCutoffty C0 k) (tsubstTy (weakenTrace d k) S32 S33))) with
        | (tvar X49) => (tsubstIndex_tshiftTy0_comm_ind d S32 k X49)
        | (tabs K82 T98) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T98 (HS ty k) d S32) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp T99 T100) => (f_equal2 tapp (tsubst_tshift0_Ty_comm_ind T99 k d S32) (tsubst_tshift0_Ty_comm_ind T100 k d S32))
        | (tarr T99 T100) => (f_equal2 tarr (tsubst_tshift0_Ty_comm_ind T99 k d S32) (tsubst_tshift0_Ty_comm_ind T100 k d S32))
        | (tall K82 T98) => (f_equal2 tall eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Ty_comm_ind T98 (HS ty k) d S32) (f_equal2 tshiftTy eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_shift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS tm d) k) s (shiftTm (weakenCutofftm C0 k) s0)) = (shiftTm (weakenCutofftm C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x6) => (substIndex_shiftTm0_comm_ind d s k x6)
        | (abs T98 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t17 (HS tm k) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (subst_shift0_Tm_comm_ind t18 k d s) (subst_shift0_Tm_comm_ind t19 k d s))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_shift0_Tm_comm_ind t17 (HS ty k) d s) (f_equal2 shiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T98) => (f_equal2 tyapp (subst_shift0_Tm_comm_ind t17 k d s) eq_refl)
      end.
    Fixpoint subst_tshift0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) {struct s0} :
    ((substTm (weakenTrace (XS ty d) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d k) s s0))) :=
      match s0 return ((substTm (weakenTrace (XS ty d) k) s (tshiftTm (weakenCutoffty C0 k) s0)) = (tshiftTm (weakenCutoffty C0 k) (substTm (weakenTrace d k) s s0))) with
        | (var x6) => (substIndex_tshiftTm0_comm_ind d s k x6)
        | (abs T98 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t17 (HS tm k) d s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (subst_tshift0_Tm_comm_ind t18 k d s) (subst_tshift0_Tm_comm_ind t19 k d s))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (subst_tshift0_Tm_comm_ind t17 (HS ty k) d s) (f_equal2 tshiftTm eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm d k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T98) => (f_equal2 tyapp (subst_tshift0_Tm_comm_ind t17 k d s) eq_refl)
      end.
    Fixpoint tsubst_shift0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d k) S32 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d k) S32 s))) :=
      match s return ((tsubstTm (weakenTrace d k) S32 (shiftTm (weakenCutofftm C0 k) s)) = (shiftTm (weakenCutofftm C0 k) (tsubstTm (weakenTrace d k) S32 s))) with
        | (var x6) => eq_refl
        | (abs T98 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t17 (HS tm k) d S32) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (tsubst_shift0_Tm_comm_ind t18 k d S32) (tsubst_shift0_Tm_comm_ind t19 k d S32))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_shift0_Tm_comm_ind t17 (HS ty k) d S32) (f_equal2 shiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T98) => (f_equal2 tyapp (tsubst_shift0_Tm_comm_ind t17 k d S32) eq_refl)
      end.
    Fixpoint tsubst_tshift0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS ty d) k) S32 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d k) S32 s))) :=
      match s return ((tsubstTm (weakenTrace (XS ty d) k) S32 (tshiftTm (weakenCutoffty C0 k) s)) = (tshiftTm (weakenCutoffty C0 k) (tsubstTm (weakenTrace d k) S32 s))) with
        | (var x6) => eq_refl
        | (abs T98 t17) => (f_equal2 abs (tsubst_tshift0_Ty_comm_ind T98 k d S32) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t17 (HS tm k) d S32) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (tsubst_tshift0_Tm_comm_ind t18 k d S32) (tsubst_tshift0_Tm_comm_ind t19 k d S32))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS ty d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tshift0_Tm_comm_ind t17 (HS ty k) d S32) (f_equal2 tshiftTm eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T98) => (f_equal2 tyapp (tsubst_tshift0_Tm_comm_ind t17 k d S32) (tsubst_tshift0_Ty_comm_ind T98 k d S32))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition tsubstTy_tshiftTy0_comm (S33 : Ty) : (forall (d : (Trace ty)) (S32 : Ty) ,
      ((tsubstTy (XS ty d) S32 (tshiftTy C0 S33)) = (tshiftTy C0 (tsubstTy d S32 S33)))) := (tsubst_tshift0_Ty_comm_ind S33 H0).
    Definition substTm_shiftTm0_comm (s0 : Tm) : (forall (d : (Trace tm)) (s : Tm) ,
      ((substTm (XS tm d) s (shiftTm C0 s0)) = (shiftTm C0 (substTm d s s0)))) := (subst_shift0_Tm_comm_ind s0 H0).
    Definition substTm_tshiftTm0_comm (s0 : Tm) : (forall (d : (Trace tm)) (s : Tm) ,
      ((substTm (XS ty d) s (tshiftTm C0 s0)) = (tshiftTm C0 (substTm d s s0)))) := (subst_tshift0_Tm_comm_ind s0 H0).
    Definition tsubstTm_shiftTm0_comm (s : Tm) : (forall (d : (Trace ty)) (S32 : Ty) ,
      ((tsubstTm d S32 (shiftTm C0 s)) = (shiftTm C0 (tsubstTm d S32 s)))) := (tsubst_shift0_Tm_comm_ind s H0).
    Definition tsubstTm_tshiftTm0_comm (s : Tm) : (forall (d : (Trace ty)) (S32 : Ty) ,
      ((tsubstTm (XS ty d) S32 (tshiftTm C0 s)) = (tshiftTm C0 (tsubstTm d S32 s)))) := (tsubst_tshift0_Tm_comm_ind s H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    Fixpoint tsubst_tm_Ty_ind (S33 : Ty) (k : Hvl) (d : (Trace ty)) (S32 : Ty) {struct S33} :
    ((tsubstTy (weakenTrace (XS tm d) k) S32 S33) = (tsubstTy (weakenTrace d k) S32 S33)) :=
      match S33 return ((tsubstTy (weakenTrace (XS tm d) k) S32 S33) = (tsubstTy (weakenTrace d k) S32 S33)) with
        | (tvar X49) => (tsubstIndex_shiftTy0_comm_ind d S32 k X49)
        | (tabs K82 T98) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T98 (HS ty k) d S32) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl))))
        | (tapp T99 T100) => (f_equal2 tapp (tsubst_tm_Ty_ind T99 k d S32) (tsubst_tm_Ty_ind T100 k d S32))
        | (tarr T99 T100) => (f_equal2 tarr (tsubst_tm_Ty_ind T99 k d S32) (tsubst_tm_Ty_ind T100 k d S32))
        | (tall K82 T98) => (f_equal2 tall eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Ty_ind T98 (HS ty k) d S32) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl))))
      end.
    Fixpoint tsubst_tm_Tm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) {struct s} :
    ((tsubstTm (weakenTrace (XS tm d) k) S32 s) = (tsubstTm (weakenTrace d k) S32 s)) :=
      match s return ((tsubstTm (weakenTrace (XS tm d) k) S32 s) = (tsubstTm (weakenTrace d k) S32 s)) with
        | (var x6) => eq_refl
        | (abs T98 t17) => (f_equal2 abs (tsubst_tm_Ty_ind T98 k d S32) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d) k (HS tm H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t17 (HS tm k) d S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl))))
        | (app t18 t19) => (f_equal2 app (tsubst_tm_Tm_ind t18 k d S32) (tsubst_tm_Tm_ind t19 k d S32))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty (XS tm d) k (HS ty H0)) eq_refl eq_refl) (eq_trans (tsubst_tm_Tm_ind t17 (HS ty k) d S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl))))
        | (tyapp t17 T98) => (f_equal2 tyapp (tsubst_tm_Tm_ind t17 k d S32) (tsubst_tm_Ty_ind T98 k d S32))
      end.
  End SubstSubordInd.
  Section SubstSubord.
    Definition tsubstTy_tm (S33 : Ty) : (forall (d : (Trace ty)) (S32 : Ty) ,
      ((tsubstTy (XS tm d) S32 S33) = (tsubstTy d S32 S33))) := (tsubst_tm_Ty_ind S33 H0).
    Definition tsubstTm_tm (s : Tm) : (forall (d : (Trace ty)) (S32 : Ty) ,
      ((tsubstTm (XS tm d) S32 s) = (tsubstTm d S32 s))) := (tsubst_tm_Tm_ind s H0).
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : interaction.
 Hint Rewrite substTm0_shiftTm0_reflection tsubstTm0_tshiftTm0_reflection tsubstTy0_tshiftTy0_reflection : reflection.
 Hint Rewrite substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : interaction.
 Hint Rewrite substTm_shiftTm0_comm substTm_tshiftTm0_comm tsubstTm_shiftTm0_comm tsubstTm_tshiftTm0_comm tsubstTy_tshiftTy0_comm : subst_shift0.
 Hint Rewrite tsubstTm_tm tsubstTy_tm : interaction.
 Hint Rewrite tsubstTm_tm tsubstTy_tm : subst_shift0.
 Hint Rewrite shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : interaction.
 Hint Rewrite shiftTm_substTm0_comm shiftTm_tsubstTm0_comm tshiftTm_substTm0_comm tshiftTm_tsubstTm0_comm tshiftTy_tsubstTy0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma substTm_substIndex0_commright_ind (d : (Trace tm)) (s : Tm) (s0 : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((substTm (weakenTrace d k) s (substIndex (weakenTrace X0 k) s0 x6)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substIndex (weakenTrace (XS tm d) k) s x6)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTm_substIndex0_commright_ind (d : (Trace ty)) (S32 : Ty) (s : Tm) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((tsubstTm (weakenTrace d k) S32 (substIndex (weakenTrace X0 k) s x6)) = (substIndex (weakenTrace X0 k) (tsubstTm d S32 s) x6))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma tsubstTy_tsubstIndex0_commright_ind (d : (Trace ty)) (S32 : Ty) (S33 : Ty) :
      (forall (k : Hvl) (X49 : (Index ty)) ,
        ((tsubstTy (weakenTrace d k) S32 (tsubstIndex (weakenTrace X0 k) S33 X49)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S32 S33) (tsubstIndex (weakenTrace (XS ty d) k) S32 X49)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma substTy_tsubstIndex0_commleft_ind (d : (Trace tm)) (s : Tm) (S32 : Ty) :
      (forall (k : Hvl) (x6 : (Index tm)) ,
        ((substIndex (weakenTrace d k) s x6) = (tsubstTm (weakenTrace X0 k) S32 (substIndex (weakenTrace (XS ty d) k) s x6)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint tsubst_tsubst0_Ty_comm_ind (S34 : Ty) (k : Hvl) (d : (Trace ty)) (S32 : Ty) (S33 : Ty) {struct S34} :
    ((tsubstTy (weakenTrace d k) S32 (tsubstTy (weakenTrace X0 k) S33 S34)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S32 S33) (tsubstTy (weakenTrace (XS ty d) k) S32 S34))) :=
      match S34 return ((tsubstTy (weakenTrace d k) S32 (tsubstTy (weakenTrace X0 k) S33 S34)) = (tsubstTy (weakenTrace X0 k) (tsubstTy d S32 S33) (tsubstTy (weakenTrace (XS ty d) k) S32 S34))) with
        | (tvar X49) => (tsubstTy_tsubstIndex0_commright_ind d S32 S33 k X49)
        | (tabs K82 T98) => (f_equal2 tabs eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T98 (HS ty k) d S32 S33) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tapp T99 T100) => (f_equal2 tapp (tsubst_tsubst0_Ty_comm_ind T99 k d S32 S33) (tsubst_tsubst0_Ty_comm_ind T100 k d S32 S33))
        | (tarr T99 T100) => (f_equal2 tarr (tsubst_tsubst0_Ty_comm_ind T99 k d S32 S33) (tsubst_tsubst0_Ty_comm_ind T100 k d S32 S33))
        | (tall K82 T98) => (f_equal2 tall eq_refl (eq_trans (f_equal3 tsubstTy (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 tsubstTy (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Ty_comm_ind T98 (HS ty k) d S32 S33) (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTy (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
      end.
    Fixpoint subst_subst0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (s0 : Tm) {struct s1} :
    ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) :=
      match s1 return ((substTm (weakenTrace d k) s (substTm (weakenTrace X0 k) s0 s1)) = (substTm (weakenTrace X0 k) (substTm d s s0) (substTm (weakenTrace (XS tm d) k) s s1))) with
        | (var x6) => (substTm_substIndex0_commright_ind d s s0 k x6)
        | (abs T98 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t17 (HS tm k) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (subst_subst0_Tm_comm_ind t18 k d s s0) (subst_subst0_Tm_comm_ind t19 k d s s0))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_subst0_Tm_comm_ind t17 (HS ty k) d s s0) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS tm d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T98) => (f_equal2 tyapp (subst_subst0_Tm_comm_ind t17 k d s s0) eq_refl)
      end.
    Fixpoint subst_tsubst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace tm)) (s : Tm) (S32 : Ty) {struct s0} :
    ((substTm (weakenTrace d k) s (tsubstTm (weakenTrace X0 k) S32 s0)) = (tsubstTm (weakenTrace X0 k) S32 (substTm (weakenTrace (XS ty d) k) s s0))) :=
      match s0 return ((substTm (weakenTrace d k) s (tsubstTm (weakenTrace X0 k) S32 s0)) = (tsubstTm (weakenTrace X0 k) S32 (substTm (weakenTrace (XS ty d) k) s s0))) with
        | (var x6) => (substTy_tsubstIndex0_commleft_ind d s S32 k x6)
        | (abs T98 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t17 (HS tm k) d s S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (subst_tsubst0_Tm_comm_ind t18 k d s S32) (subst_tsubst0_Tm_comm_ind t19 k d s S32))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 substTm (weakenTrace_append tm d k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (subst_tsubst0_Tm_comm_ind t17 (HS ty k) d s S32) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 substTm (eq_sym (weakenTrace_append tm (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T98) => (f_equal2 tyapp (subst_tsubst0_Tm_comm_ind t17 k d s S32) eq_refl)
      end.
    Fixpoint tsubst_subst0_Tm_comm_ind (s0 : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) (s : Tm) {struct s0} :
    ((tsubstTm (weakenTrace d k) S32 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d S32 s) (tsubstTm (weakenTrace d k) S32 s0))) :=
      match s0 return ((tsubstTm (weakenTrace d k) S32 (substTm (weakenTrace X0 k) s s0)) = (substTm (weakenTrace X0 k) (tsubstTm d S32 s) (tsubstTm (weakenTrace d k) S32 s0))) with
        | (var x6) => (tsubstTm_substIndex0_commright_ind d S32 s k x6)
        | (abs T98 t17) => (f_equal2 abs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t17 (HS tm k) d S32 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (tsubst_subst0_Tm_comm_ind t18 k d S32 s) (tsubst_subst0_Tm_comm_ind t19 k d S32 s))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 substTm (weakenTrace_append tm X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_subst0_Tm_comm_ind t17 (HS ty k) d S32 s) (f_equal3 substTm (eq_sym (weakenTrace_append tm X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty d k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T98) => (f_equal2 tyapp (tsubst_subst0_Tm_comm_ind t17 k d S32 s) eq_refl)
      end.
    Fixpoint tsubst_tsubst0_Tm_comm_ind (s : Tm) (k : Hvl) (d : (Trace ty)) (S32 : Ty) (S33 : Ty) {struct s} :
    ((tsubstTm (weakenTrace d k) S32 (tsubstTm (weakenTrace X0 k) S33 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d S32 S33) (tsubstTm (weakenTrace (XS ty d) k) S32 s))) :=
      match s return ((tsubstTm (weakenTrace d k) S32 (tsubstTm (weakenTrace X0 k) S33 s)) = (tsubstTm (weakenTrace X0 k) (tsubstTy d S32 S33) (tsubstTm (weakenTrace (XS ty d) k) S32 s))) with
        | (var x6) => eq_refl
        | (abs T98 t17) => (f_equal2 abs (tsubst_tsubst0_Ty_comm_ind T98 k d S32 S33) (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS tm H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS tm H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t17 (HS tm k) d S32 S33) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS tm H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d) k (HS tm H0))) eq_refl eq_refl)))))
        | (app t18 t19) => (f_equal2 app (tsubst_tsubst0_Tm_comm_ind t18 k d S32 S33) (tsubst_tsubst0_Tm_comm_ind t19 k d S32 S33))
        | (tyabs K82 t17) => (f_equal2 tyabs eq_refl (eq_trans (f_equal3 tsubstTm (weakenTrace_append ty d k (HS ty H0)) eq_refl (f_equal3 tsubstTm (weakenTrace_append ty X0 k (HS ty H0)) eq_refl eq_refl)) (eq_trans (tsubst_tsubst0_Tm_comm_ind t17 (HS ty k) d S32 S33) (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty X0 k (HS ty H0))) eq_refl (f_equal3 tsubstTm (eq_sym (weakenTrace_append ty (XS ty d) k (HS ty H0))) eq_refl eq_refl)))))
        | (tyapp t17 T98) => (f_equal2 tyapp (tsubst_tsubst0_Tm_comm_ind t17 k d S32 S33) (tsubst_tsubst0_Ty_comm_ind T98 k d S32 S33))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition tsubstTy_tsubstTy0_comm (S34 : Ty) : (forall (d : (Trace ty)) (S32 : Ty) (S33 : Ty) ,
      ((tsubstTy d S32 (tsubstTy X0 S33 S34)) = (tsubstTy X0 (tsubstTy d S32 S33) (tsubstTy (XS ty d) S32 S34)))) := (tsubst_tsubst0_Ty_comm_ind S34 H0).
    Definition substTm_substTm0_comm (s1 : Tm) : (forall (d : (Trace tm)) (s : Tm) (s0 : Tm) ,
      ((substTm d s (substTm X0 s0 s1)) = (substTm X0 (substTm d s s0) (substTm (XS tm d) s s1)))) := (subst_subst0_Tm_comm_ind s1 H0).
    Definition substTm_tsubstTm0_comm (s0 : Tm) : (forall (d : (Trace tm)) (s : Tm) (S32 : Ty) ,
      ((substTm d s (tsubstTm X0 S32 s0)) = (tsubstTm X0 S32 (substTm (XS ty d) s s0)))) := (subst_tsubst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_substTm0_comm (s0 : Tm) : (forall (d : (Trace ty)) (S32 : Ty) (s : Tm) ,
      ((tsubstTm d S32 (substTm X0 s s0)) = (substTm X0 (tsubstTm d S32 s) (tsubstTm d S32 s0)))) := (tsubst_subst0_Tm_comm_ind s0 H0).
    Definition tsubstTm_tsubstTm0_comm (s : Tm) : (forall (d : (Trace ty)) (S32 : Ty) (S33 : Ty) ,
      ((tsubstTm d S32 (tsubstTm X0 S33 s)) = (tsubstTm X0 (tsubstTy d S32 S33) (tsubstTm (XS ty d) S32 s)))) := (tsubst_tsubst0_Tm_comm_ind s H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTy_tsubstTy  :
      (forall (k : Hvl) (d : (Trace ty)) (S32 : Ty) (S33 : Ty) ,
        ((weakenTy (tsubstTy d S32 S33) k) = (tsubstTy (weakenTrace d k) S32 (weakenTy S33 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_substTm  :
      (forall (k : Hvl) (d : (Trace tm)) (s : Tm) (s0 : Tm) ,
        ((weakenTm (substTm d s s0) k) = (substTm (weakenTrace d k) s (weakenTm s0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_tsubstTm  :
      (forall (k : Hvl) (d : (Trace ty)) (S32 : Ty) (s : Tm) ,
        ((weakenTm (tsubstTm d S32 s) k) = (tsubstTm (weakenTrace d k) S32 (weakenTm s k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : interaction.
 Hint Rewrite substTm_substTm0_comm tsubstTm_tsubstTm0_comm tsubstTy_tsubstTy0_comm : subst_subst0.
 Hint Rewrite weakenTm_shiftTm weakenTm_tshiftTm weakenTy_tshiftTy : weaken_shift.
 Hint Rewrite weakenTm_substTm weakenTm_tsubstTm weakenTy_tsubstTy : weaken_subst.
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
  Inductive wfKind (k : Hvl) : Kind -> Prop :=
    | wfKind_star :
        (wfKind k (star))
    | wfKind_karr {K82 : Kind}
        (wf : (wfKind k K82))
        {K83 : Kind}
        (wf0 : (wfKind k K83)) :
        (wfKind k (karr K82 K83)).
  Inductive wfTy (k : Hvl) : Ty -> Prop :=
    | wfTy_tvar (X49 : (Index ty))
        (wfi : (wfindex k X49)) :
        (wfTy k (tvar X49))
    | wfTy_tabs {K82 : Kind}
        (wf : (wfKind k K82)) {T98 : Ty}
        (wf0 : (wfTy (HS ty k) T98)) :
        (wfTy k (tabs K82 T98))
    | wfTy_tapp {T99 : Ty}
        (wf : (wfTy k T99)) {T100 : Ty}
        (wf0 : (wfTy k T100)) :
        (wfTy k (tapp T99 T100))
    | wfTy_tarr {T101 : Ty}
        (wf : (wfTy k T101)) {T102 : Ty}
        (wf0 : (wfTy k T102)) :
        (wfTy k (tarr T101 T102))
    | wfTy_tall {K83 : Kind}
        (wf : (wfKind k K83))
        {T103 : Ty}
        (wf0 : (wfTy (HS ty k) T103)) :
        (wfTy k (tall K83 T103)).
  Inductive wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_var (x6 : (Index tm))
        (wfi : (wfindex k x6)) :
        (wfTm k (var x6))
    | wfTm_abs {T98 : Ty}
        (wf : (wfTy k T98)) {t17 : Tm}
        (wf0 : (wfTm (HS tm k) t17)) :
        (wfTm k (abs T98 t17))
    | wfTm_app {t18 : Tm}
        (wf : (wfTm k t18)) {t19 : Tm}
        (wf0 : (wfTm k t19)) :
        (wfTm k (app t18 t19))
    | wfTm_tyabs {K82 : Kind}
        (wf : (wfKind k K82)) {t20 : Tm}
        (wf0 : (wfTm (HS ty k) t20)) :
        (wfTm k (tyabs K82 t20))
    | wfTm_tyapp {t21 : Tm}
        (wf : (wfTm k t21)) {T99 : Ty}
        (wf0 : (wfTy k T99)) :
        (wfTm k (tyapp t21 T99)).
  Definition inversion_wfKind_karr_0 (k0 : Hvl) (K1 : Kind) (K2 : Kind) (H24 : (wfKind k0 (karr K1 K2))) : (wfKind k0 K1) := match H24 in (wfKind _ K83) return match K83 return Prop with
    | (karr K1 K2) => (wfKind k0 K1)
    | _ => True
  end with
    | (wfKind_karr K1 H1 K2 H2) => H1
    | _ => I
  end.
  Definition inversion_wfKind_karr_1 (k0 : Hvl) (K1 : Kind) (K2 : Kind) (H24 : (wfKind k0 (karr K1 K2))) : (wfKind k0 K2) := match H24 in (wfKind _ K83) return match K83 return Prop with
    | (karr K1 K2) => (wfKind k0 K2)
    | _ => True
  end with
    | (wfKind_karr K1 H1 K2 H2) => H2
    | _ => I
  end.
  Definition inversion_wfTy_tvar_1 (k1 : Hvl) (X : (Index ty)) (H25 : (wfTy k1 (tvar X))) : (wfindex k1 X) := match H25 in (wfTy _ S32) return match S32 return Prop with
    | (tvar X) => (wfindex k1 X)
    | _ => True
  end with
    | (wfTy_tvar X H3) => H3
    | _ => I
  end.
  Definition inversion_wfTy_tabs_1 (k2 : Hvl) (K : Kind) (T : Ty) (H26 : (wfTy k2 (tabs K T))) : (wfKind k2 K) := match H26 in (wfTy _ S33) return match S33 return Prop with
    | (tabs K T) => (wfKind k2 K)
    | _ => True
  end with
    | (wfTy_tabs K H4 T H5) => H4
    | _ => I
  end.
  Definition inversion_wfTy_tabs_2 (k2 : Hvl) (K : Kind) (T : Ty) (H26 : (wfTy k2 (tabs K T))) : (wfTy (HS ty k2) T) := match H26 in (wfTy _ S33) return match S33 return Prop with
    | (tabs K T) => (wfTy (HS ty k2) T)
    | _ => True
  end with
    | (wfTy_tabs K H4 T H5) => H5
    | _ => I
  end.
  Definition inversion_wfTy_tapp_0 (k3 : Hvl) (T1 : Ty) (T2 : Ty) (H27 : (wfTy k3 (tapp T1 T2))) : (wfTy k3 T1) := match H27 in (wfTy _ S34) return match S34 return Prop with
    | (tapp T1 T2) => (wfTy k3 T1)
    | _ => True
  end with
    | (wfTy_tapp T1 H6 T2 H7) => H6
    | _ => I
  end.
  Definition inversion_wfTy_tapp_1 (k3 : Hvl) (T1 : Ty) (T2 : Ty) (H27 : (wfTy k3 (tapp T1 T2))) : (wfTy k3 T2) := match H27 in (wfTy _ S34) return match S34 return Prop with
    | (tapp T1 T2) => (wfTy k3 T2)
    | _ => True
  end with
    | (wfTy_tapp T1 H6 T2 H7) => H7
    | _ => I
  end.
  Definition inversion_wfTy_tarr_0 (k4 : Hvl) (T1 : Ty) (T2 : Ty) (H28 : (wfTy k4 (tarr T1 T2))) : (wfTy k4 T1) := match H28 in (wfTy _ S35) return match S35 return Prop with
    | (tarr T1 T2) => (wfTy k4 T1)
    | _ => True
  end with
    | (wfTy_tarr T1 H8 T2 H9) => H8
    | _ => I
  end.
  Definition inversion_wfTy_tarr_1 (k4 : Hvl) (T1 : Ty) (T2 : Ty) (H28 : (wfTy k4 (tarr T1 T2))) : (wfTy k4 T2) := match H28 in (wfTy _ S35) return match S35 return Prop with
    | (tarr T1 T2) => (wfTy k4 T2)
    | _ => True
  end with
    | (wfTy_tarr T1 H8 T2 H9) => H9
    | _ => I
  end.
  Definition inversion_wfTy_tall_1 (k5 : Hvl) (K : Kind) (T : Ty) (H29 : (wfTy k5 (tall K T))) : (wfKind k5 K) := match H29 in (wfTy _ S36) return match S36 return Prop with
    | (tall K T) => (wfKind k5 K)
    | _ => True
  end with
    | (wfTy_tall K H10 T H11) => H10
    | _ => I
  end.
  Definition inversion_wfTy_tall_2 (k5 : Hvl) (K : Kind) (T : Ty) (H29 : (wfTy k5 (tall K T))) : (wfTy (HS ty k5) T) := match H29 in (wfTy _ S36) return match S36 return Prop with
    | (tall K T) => (wfTy (HS ty k5) T)
    | _ => True
  end with
    | (wfTy_tall K H10 T H11) => H11
    | _ => I
  end.
  Definition inversion_wfTm_var_1 (k6 : Hvl) (x : (Index tm)) (H30 : (wfTm k6 (var x))) : (wfindex k6 x) := match H30 in (wfTm _ s) return match s return Prop with
    | (var x) => (wfindex k6 x)
    | _ => True
  end with
    | (wfTm_var x H12) => H12
    | _ => I
  end.
  Definition inversion_wfTm_abs_1 (k7 : Hvl) (T : Ty) (t : Tm) (H31 : (wfTm k7 (abs T t))) : (wfTy k7 T) := match H31 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTy k7 T)
    | _ => True
  end with
    | (wfTm_abs T H13 t H14) => H13
    | _ => I
  end.
  Definition inversion_wfTm_abs_2 (k7 : Hvl) (T : Ty) (t : Tm) (H31 : (wfTm k7 (abs T t))) : (wfTm (HS tm k7) t) := match H31 in (wfTm _ s0) return match s0 return Prop with
    | (abs T t) => (wfTm (HS tm k7) t)
    | _ => True
  end with
    | (wfTm_abs T H13 t H14) => H14
    | _ => I
  end.
  Definition inversion_wfTm_app_0 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H32 : (wfTm k8 (app t1 t2))) : (wfTm k8 t1) := match H32 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k8 t1)
    | _ => True
  end with
    | (wfTm_app t1 H15 t2 H16) => H15
    | _ => I
  end.
  Definition inversion_wfTm_app_1 (k8 : Hvl) (t1 : Tm) (t2 : Tm) (H32 : (wfTm k8 (app t1 t2))) : (wfTm k8 t2) := match H32 in (wfTm _ s1) return match s1 return Prop with
    | (app t1 t2) => (wfTm k8 t2)
    | _ => True
  end with
    | (wfTm_app t1 H15 t2 H16) => H16
    | _ => I
  end.
  Definition inversion_wfTm_tyabs_1 (k9 : Hvl) (K : Kind) (t : Tm) (H33 : (wfTm k9 (tyabs K t))) : (wfKind k9 K) := match H33 in (wfTm _ s2) return match s2 return Prop with
    | (tyabs K t) => (wfKind k9 K)
    | _ => True
  end with
    | (wfTm_tyabs K H17 t H18) => H17
    | _ => I
  end.
  Definition inversion_wfTm_tyabs_2 (k9 : Hvl) (K : Kind) (t : Tm) (H33 : (wfTm k9 (tyabs K t))) : (wfTm (HS ty k9) t) := match H33 in (wfTm _ s2) return match s2 return Prop with
    | (tyabs K t) => (wfTm (HS ty k9) t)
    | _ => True
  end with
    | (wfTm_tyabs K H17 t H18) => H18
    | _ => I
  end.
  Definition inversion_wfTm_tyapp_0 (k10 : Hvl) (t : Tm) (T : Ty) (H34 : (wfTm k10 (tyapp t T))) : (wfTm k10 t) := match H34 in (wfTm _ s3) return match s3 return Prop with
    | (tyapp t T) => (wfTm k10 t)
    | _ => True
  end with
    | (wfTm_tyapp t H19 T H20) => H19
    | _ => I
  end.
  Definition inversion_wfTm_tyapp_1 (k10 : Hvl) (t : Tm) (T : Ty) (H34 : (wfTm k10 (tyapp t T))) : (wfTy k10 T) := match H34 in (wfTm _ s3) return match s3 return Prop with
    | (tyapp t T) => (wfTy k10 T)
    | _ => True
  end with
    | (wfTm_tyapp t H19 T H20) => H20
    | _ => I
  end.
  Scheme ind_wfKind := Induction for wfKind Sort Prop.
  Scheme ind_wfTy := Induction for wfTy Sort Prop.
  Scheme ind_wfTm := Induction for wfTm Sort Prop.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_tm : (forall (c : (Cutoff tm)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | shifthvl_tm_here (k11 : Hvl)
        :
        (shifthvl_tm C0 k11 (HS tm k11))
    | shifthvl_tm_there_tm
        (c : (Cutoff tm)) (k11 : Hvl)
        (k12 : Hvl) :
        (shifthvl_tm c k11 k12) -> (shifthvl_tm (CS c) (HS tm k11) (HS tm k12))
    | shifthvl_tm_there_ty
        (c : (Cutoff tm)) (k11 : Hvl)
        (k12 : Hvl) :
        (shifthvl_tm c k11 k12) -> (shifthvl_tm c (HS ty k11) (HS ty k12)).
  Inductive shifthvl_ty : (forall (c : (Cutoff ty)) (k11 : Hvl) (k12 : Hvl) ,
    Prop) :=
    | shifthvl_ty_here (k11 : Hvl)
        :
        (shifthvl_ty C0 k11 (HS ty k11))
    | shifthvl_ty_there_tm
        (c : (Cutoff ty)) (k11 : Hvl)
        (k12 : Hvl) :
        (shifthvl_ty c k11 k12) -> (shifthvl_ty c (HS tm k11) (HS tm k12))
    | shifthvl_ty_there_ty
        (c : (Cutoff ty)) (k11 : Hvl)
        (k12 : Hvl) :
        (shifthvl_ty c k11 k12) -> (shifthvl_ty (CS c) (HS ty k11) (HS ty k12)).
  Lemma weaken_shifthvl_tm  :
    (forall (k11 : Hvl) {c : (Cutoff tm)} {k12 : Hvl} {k13 : Hvl} ,
      (shifthvl_tm c k12 k13) -> (shifthvl_tm (weakenCutofftm c k11) (appendHvl k12 k11) (appendHvl k13 k11))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_ty  :
    (forall (k11 : Hvl) {c : (Cutoff ty)} {k12 : Hvl} {k13 : Hvl} ,
      (shifthvl_ty c k12 k13) -> (shifthvl_ty (weakenCutoffty c k11) (appendHvl k12 k11) (appendHvl k13 k11))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_wfindex_tm  :
    (forall (c : (Cutoff tm)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) (x6 : (Index tm)) ,
      (wfindex k11 x6) -> (wfindex k12 (shiftIndex c x6))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_wfindex_ty  :
    (forall (c : (Cutoff tm)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) (X49 : (Index ty)) ,
      (wfindex k11 X49) -> (wfindex k12 X49)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_tm  :
    (forall (c : (Cutoff ty)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) (x6 : (Index tm)) ,
      (wfindex k11 x6) -> (wfindex k12 x6)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma tshift_wfindex_ty  :
    (forall (c : (Cutoff ty)) (k11 : Hvl) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) (X49 : (Index ty)) ,
      (wfindex k11 X49) -> (wfindex k12 (tshiftIndex c X49))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_wfKind : (forall (k11 : Hvl) ,
    (forall (K84 : Kind) (wf : (wfKind k11 K84)) ,
      (forall (c : (Cutoff tm)) (k12 : Hvl) ,
        (shifthvl_tm c k11 k12) -> (wfKind k12 K84)))) := (fun (k11 : Hvl) =>
    (ind_wfKind k11 (fun (K84 : Kind) (wf : (wfKind k11 K84)) =>
      (forall (c : (Cutoff tm)) (k12 : Hvl) ,
        (shifthvl_tm c k11 k12) -> (wfKind k12 K84))) (fun (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
      (wfKind_star k12)) (fun (K1 : Kind) (wf : (wfKind k11 K1)) IHK1 (K2 : Kind) (wf0 : (wfKind k11 K2)) IHK2 (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
      (wfKind_karr k12 (IHK1 c k12 (weaken_shifthvl_tm H0 ins)) (IHK2 c k12 (weaken_shifthvl_tm H0 ins)))))).
  Definition tshift_wfKind : (forall (k11 : Hvl) ,
    (forall (K84 : Kind) (wf : (wfKind k11 K84)) ,
      (forall (c : (Cutoff ty)) (k12 : Hvl) ,
        (shifthvl_ty c k11 k12) -> (wfKind k12 K84)))) := (fun (k11 : Hvl) =>
    (ind_wfKind k11 (fun (K84 : Kind) (wf : (wfKind k11 K84)) =>
      (forall (c : (Cutoff ty)) (k12 : Hvl) ,
        (shifthvl_ty c k11 k12) -> (wfKind k12 K84))) (fun (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
      (wfKind_star k12)) (fun (K1 : Kind) (wf : (wfKind k11 K1)) IHK1 (K2 : Kind) (wf0 : (wfKind k11 K2)) IHK2 (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
      (wfKind_karr k12 (IHK1 c k12 (weaken_shifthvl_ty H0 ins)) (IHK2 c k12 (weaken_shifthvl_ty H0 ins)))))).
  Definition shift_wfTy : (forall (k11 : Hvl) ,
    (forall (S37 : Ty) (wf : (wfTy k11 S37)) ,
      (forall (c : (Cutoff tm)) (k12 : Hvl) ,
        (shifthvl_tm c k11 k12) -> (wfTy k12 S37)))) := (ind_wfTy (fun (k11 : Hvl) (S37 : Ty) (wf : (wfTy k11 S37)) =>
    (forall (c : (Cutoff tm)) (k12 : Hvl) ,
      (shifthvl_tm c k11 k12) -> (wfTy k12 S37))) (fun (k11 : Hvl) (X49 : (Index ty)) (wfi : (wfindex k11 X49)) (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTy_tvar k12 _ (shift_wfindex_ty c k11 k12 ins X49 wfi))) (fun (k11 : Hvl) (K : Kind) (wf : (wfKind k11 K)) (T : Ty) (wf0 : (wfTy (HS ty k11) T)) IHT (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTy_tabs k12 (shift_wfKind k11 K wf c k12 (weaken_shifthvl_tm H0 ins)) (IHT c (HS ty k12) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k11 : Hvl) (T1 : Ty) (wf : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k11 T2)) IHT2 (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTy_tapp k12 (IHT1 c k12 (weaken_shifthvl_tm H0 ins)) (IHT2 c k12 (weaken_shifthvl_tm H0 ins)))) (fun (k11 : Hvl) (T1 : Ty) (wf : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k11 T2)) IHT2 (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTy_tarr k12 (IHT1 c k12 (weaken_shifthvl_tm H0 ins)) (IHT2 c k12 (weaken_shifthvl_tm H0 ins)))) (fun (k11 : Hvl) (K : Kind) (wf : (wfKind k11 K)) (T : Ty) (wf0 : (wfTy (HS ty k11) T)) IHT (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTy_tall k12 (shift_wfKind k11 K wf c k12 (weaken_shifthvl_tm H0 ins)) (IHT c (HS ty k12) (weaken_shifthvl_tm (HS ty H0) ins))))).
  Definition tshift_wfTy : (forall (k11 : Hvl) ,
    (forall (S37 : Ty) (wf : (wfTy k11 S37)) ,
      (forall (c : (Cutoff ty)) (k12 : Hvl) ,
        (shifthvl_ty c k11 k12) -> (wfTy k12 (tshiftTy c S37))))) := (ind_wfTy (fun (k11 : Hvl) (S37 : Ty) (wf : (wfTy k11 S37)) =>
    (forall (c : (Cutoff ty)) (k12 : Hvl) ,
      (shifthvl_ty c k11 k12) -> (wfTy k12 (tshiftTy c S37)))) (fun (k11 : Hvl) (X49 : (Index ty)) (wfi : (wfindex k11 X49)) (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTy_tvar k12 _ (tshift_wfindex_ty c k11 k12 ins X49 wfi))) (fun (k11 : Hvl) (K : Kind) (wf : (wfKind k11 K)) (T : Ty) (wf0 : (wfTy (HS ty k11) T)) IHT (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTy_tabs k12 (tshift_wfKind k11 K wf c k12 (weaken_shifthvl_ty H0 ins)) (IHT (CS c) (HS ty k12) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k11 : Hvl) (T1 : Ty) (wf : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k11 T2)) IHT2 (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTy_tapp k12 (IHT1 c k12 (weaken_shifthvl_ty H0 ins)) (IHT2 c k12 (weaken_shifthvl_ty H0 ins)))) (fun (k11 : Hvl) (T1 : Ty) (wf : (wfTy k11 T1)) IHT1 (T2 : Ty) (wf0 : (wfTy k11 T2)) IHT2 (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTy_tarr k12 (IHT1 c k12 (weaken_shifthvl_ty H0 ins)) (IHT2 c k12 (weaken_shifthvl_ty H0 ins)))) (fun (k11 : Hvl) (K : Kind) (wf : (wfKind k11 K)) (T : Ty) (wf0 : (wfTy (HS ty k11) T)) IHT (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTy_tall k12 (tshift_wfKind k11 K wf c k12 (weaken_shifthvl_ty H0 ins)) (IHT (CS c) (HS ty k12) (weaken_shifthvl_ty (HS ty H0) ins))))).
  Definition shift_wfTm : (forall (k11 : Hvl) ,
    (forall (s4 : Tm) (wf : (wfTm k11 s4)) ,
      (forall (c : (Cutoff tm)) (k12 : Hvl) ,
        (shifthvl_tm c k11 k12) -> (wfTm k12 (shiftTm c s4))))) := (ind_wfTm (fun (k11 : Hvl) (s4 : Tm) (wf : (wfTm k11 s4)) =>
    (forall (c : (Cutoff tm)) (k12 : Hvl) ,
      (shifthvl_tm c k11 k12) -> (wfTm k12 (shiftTm c s4)))) (fun (k11 : Hvl) (x6 : (Index tm)) (wfi : (wfindex k11 x6)) (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTm_var k12 _ (shift_wfindex_tm c k11 k12 ins x6 wfi))) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) (t : Tm) (wf0 : (wfTm (HS tm k11) t)) IHt (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTm_abs k12 (shift_wfTy k11 T wf c k12 (weaken_shifthvl_tm H0 ins)) (IHt (CS c) (HS tm k12) (weaken_shifthvl_tm (HS tm H0) ins)))) (fun (k11 : Hvl) (t1 : Tm) (wf : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k11 t2)) IHt2 (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTm_app k12 (IHt1 c k12 (weaken_shifthvl_tm H0 ins)) (IHt2 c k12 (weaken_shifthvl_tm H0 ins)))) (fun (k11 : Hvl) (K : Kind) (wf : (wfKind k11 K)) (t : Tm) (wf0 : (wfTm (HS ty k11) t)) IHt (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTm_tyabs k12 (shift_wfKind k11 K wf c k12 (weaken_shifthvl_tm H0 ins)) (IHt c (HS ty k12) (weaken_shifthvl_tm (HS ty H0) ins)))) (fun (k11 : Hvl) (t : Tm) (wf : (wfTm k11 t)) IHt (T : Ty) (wf0 : (wfTy k11 T)) (c : (Cutoff tm)) (k12 : Hvl) (ins : (shifthvl_tm c k11 k12)) =>
    (wfTm_tyapp k12 (IHt c k12 (weaken_shifthvl_tm H0 ins)) (shift_wfTy k11 T wf0 c k12 (weaken_shifthvl_tm H0 ins))))).
  Definition tshift_wfTm : (forall (k11 : Hvl) ,
    (forall (s4 : Tm) (wf : (wfTm k11 s4)) ,
      (forall (c : (Cutoff ty)) (k12 : Hvl) ,
        (shifthvl_ty c k11 k12) -> (wfTm k12 (tshiftTm c s4))))) := (ind_wfTm (fun (k11 : Hvl) (s4 : Tm) (wf : (wfTm k11 s4)) =>
    (forall (c : (Cutoff ty)) (k12 : Hvl) ,
      (shifthvl_ty c k11 k12) -> (wfTm k12 (tshiftTm c s4)))) (fun (k11 : Hvl) (x6 : (Index tm)) (wfi : (wfindex k11 x6)) (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTm_var k12 _ (tshift_wfindex_tm c k11 k12 ins x6 wfi))) (fun (k11 : Hvl) (T : Ty) (wf : (wfTy k11 T)) (t : Tm) (wf0 : (wfTm (HS tm k11) t)) IHt (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTm_abs k12 (tshift_wfTy k11 T wf c k12 (weaken_shifthvl_ty H0 ins)) (IHt c (HS tm k12) (weaken_shifthvl_ty (HS tm H0) ins)))) (fun (k11 : Hvl) (t1 : Tm) (wf : (wfTm k11 t1)) IHt1 (t2 : Tm) (wf0 : (wfTm k11 t2)) IHt2 (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTm_app k12 (IHt1 c k12 (weaken_shifthvl_ty H0 ins)) (IHt2 c k12 (weaken_shifthvl_ty H0 ins)))) (fun (k11 : Hvl) (K : Kind) (wf : (wfKind k11 K)) (t : Tm) (wf0 : (wfTm (HS ty k11) t)) IHt (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTm_tyabs k12 (tshift_wfKind k11 K wf c k12 (weaken_shifthvl_ty H0 ins)) (IHt (CS c) (HS ty k12) (weaken_shifthvl_ty (HS ty H0) ins)))) (fun (k11 : Hvl) (t : Tm) (wf : (wfTm k11 t)) IHt (T : Ty) (wf0 : (wfTy k11 T)) (c : (Cutoff ty)) (k12 : Hvl) (ins : (shifthvl_ty c k11 k12)) =>
    (wfTm_tyapp k12 (IHt c k12 (weaken_shifthvl_ty H0 ins)) (tshift_wfTy k11 T wf0 c k12 (weaken_shifthvl_ty H0 ins))))).
  Fixpoint weaken_wfKind (k11 : Hvl) {struct k11} :
  (forall (k12 : Hvl) (K84 : Kind) (wf : (wfKind k12 K84)) ,
    (wfKind (appendHvl k12 k11) (weakenKind K84 k11))) :=
    match k11 return (forall (k12 : Hvl) (K84 : Kind) (wf : (wfKind k12 K84)) ,
      (wfKind (appendHvl k12 k11) (weakenKind K84 k11))) with
      | (H0) => (fun (k12 : Hvl) (K84 : Kind) (wf : (wfKind k12 K84)) =>
        wf)
      | (HS tm k11) => (fun (k12 : Hvl) (K84 : Kind) (wf : (wfKind k12 K84)) =>
        (shift_wfKind (appendHvl k12 k11) (weakenKind K84 k11) (weaken_wfKind k11 k12 K84 wf) C0 (HS tm (appendHvl k12 k11)) (shifthvl_tm_here (appendHvl k12 k11))))
      | (HS ty k11) => (fun (k12 : Hvl) (K84 : Kind) (wf : (wfKind k12 K84)) =>
        (tshift_wfKind (appendHvl k12 k11) (weakenKind K84 k11) (weaken_wfKind k11 k12 K84 wf) C0 (HS ty (appendHvl k12 k11)) (shifthvl_ty_here (appendHvl k12 k11))))
    end.
  Fixpoint weaken_wfTy (k11 : Hvl) {struct k11} :
  (forall (k12 : Hvl) (S37 : Ty) (wf : (wfTy k12 S37)) ,
    (wfTy (appendHvl k12 k11) (weakenTy S37 k11))) :=
    match k11 return (forall (k12 : Hvl) (S37 : Ty) (wf : (wfTy k12 S37)) ,
      (wfTy (appendHvl k12 k11) (weakenTy S37 k11))) with
      | (H0) => (fun (k12 : Hvl) (S37 : Ty) (wf : (wfTy k12 S37)) =>
        wf)
      | (HS tm k11) => (fun (k12 : Hvl) (S37 : Ty) (wf : (wfTy k12 S37)) =>
        (shift_wfTy (appendHvl k12 k11) (weakenTy S37 k11) (weaken_wfTy k11 k12 S37 wf) C0 (HS tm (appendHvl k12 k11)) (shifthvl_tm_here (appendHvl k12 k11))))
      | (HS ty k11) => (fun (k12 : Hvl) (S37 : Ty) (wf : (wfTy k12 S37)) =>
        (tshift_wfTy (appendHvl k12 k11) (weakenTy S37 k11) (weaken_wfTy k11 k12 S37 wf) C0 (HS ty (appendHvl k12 k11)) (shifthvl_ty_here (appendHvl k12 k11))))
    end.
  Fixpoint weaken_wfTm (k11 : Hvl) {struct k11} :
  (forall (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) ,
    (wfTm (appendHvl k12 k11) (weakenTm s4 k11))) :=
    match k11 return (forall (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) ,
      (wfTm (appendHvl k12 k11) (weakenTm s4 k11))) with
      | (H0) => (fun (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) =>
        wf)
      | (HS tm k11) => (fun (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) =>
        (shift_wfTm (appendHvl k12 k11) (weakenTm s4 k11) (weaken_wfTm k11 k12 s4 wf) C0 (HS tm (appendHvl k12 k11)) (shifthvl_tm_here (appendHvl k12 k11))))
      | (HS ty k11) => (fun (k12 : Hvl) (s4 : Tm) (wf : (wfTm k12 s4)) =>
        (tshift_wfTm (appendHvl k12 k11) (weakenTm s4 k11) (weaken_wfTm k11 k12 s4 wf) C0 (HS ty (appendHvl k12 k11)) (shifthvl_ty_here (appendHvl k12 k11))))
    end.
End ShiftWellFormed.
Lemma wfKind_cast  :
  (forall (k11 : Hvl) (K84 : Kind) (k12 : Hvl) (K85 : Kind) ,
    (k11 = k12) -> (K84 = K85) -> (wfKind k11 K84) -> (wfKind k12 K85)).
Proof.
  congruence .
Qed.
Lemma wfTy_cast  :
  (forall (k11 : Hvl) (S37 : Ty) (k12 : Hvl) (S38 : Ty) ,
    (k11 = k12) -> (S37 = S38) -> (wfTy k11 S37) -> (wfTy k12 S38)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k11 : Hvl) (s4 : Tm) (k12 : Hvl) (s5 : Tm) ,
    (k11 = k12) -> (s4 = s5) -> (wfTm k11 s4) -> (wfTm k12 s5)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : infra.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : shift_wf.
 Hint Resolve shift_wfindex_tm shift_wfindex_ty tshift_wfindex_tm tshift_wfindex_ty : wf.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : infra.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : shift.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : shift_wf.
 Hint Resolve shift_wfKind shift_wfTm shift_wfTy tshift_wfKind tshift_wfTm tshift_wfTy : wf.
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
  Inductive substhvl_tm (k11 : Hvl) : (forall (d : (Trace tm)) (k12 : Hvl) (k13 : Hvl) ,
    Prop) :=
    | substhvl_tm_here :
        (substhvl_tm k11 X0 (HS tm k11) k11)
    | substhvl_tm_there_tm
        {d : (Trace tm)} {k12 : Hvl}
        {k13 : Hvl} :
        (substhvl_tm k11 d k12 k13) -> (substhvl_tm k11 (XS tm d) (HS tm k12) (HS tm k13))
    | substhvl_tm_there_ty
        {d : (Trace tm)} {k12 : Hvl}
        {k13 : Hvl} :
        (substhvl_tm k11 d k12 k13) -> (substhvl_tm k11 (XS ty d) (HS ty k12) (HS ty k13)).
  Inductive substhvl_ty (k11 : Hvl) : (forall (d : (Trace ty)) (k12 : Hvl) (k13 : Hvl) ,
    Prop) :=
    | substhvl_ty_here :
        (substhvl_ty k11 X0 (HS ty k11) k11)
    | substhvl_ty_there_tm
        {d : (Trace ty)} {k12 : Hvl}
        {k13 : Hvl} :
        (substhvl_ty k11 d k12 k13) -> (substhvl_ty k11 (XS tm d) (HS tm k12) (HS tm k13))
    | substhvl_ty_there_ty
        {d : (Trace ty)} {k12 : Hvl}
        {k13 : Hvl} :
        (substhvl_ty k11 d k12 k13) -> (substhvl_ty k11 (XS ty d) (HS ty k12) (HS ty k13)).
  Lemma weaken_substhvl_tm  :
    (forall {k12 : Hvl} (k11 : Hvl) {d : (Trace tm)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_tm k12 d k13 k14) -> (substhvl_tm k12 (weakenTrace d k11) (appendHvl k13 k11) (appendHvl k14 k11))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_ty  :
    (forall {k12 : Hvl} (k11 : Hvl) {d : (Trace ty)} {k13 : Hvl} {k14 : Hvl} ,
      (substhvl_ty k12 d k13 k14) -> (substhvl_ty k12 (weakenTrace d k11) (appendHvl k13 k11) (appendHvl k14 k11))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_tm_wfindex_tm {k11 : Hvl} {s4 : Tm} (wft : (wfTm k11 s4)) :
    (forall {d : (Trace tm)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_tm k11 d k12 k13) -> (forall {x6 : (Index tm)} ,
        (wfindex k12 x6) -> (wfTm k13 (substIndex d s4 x6)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_ty_wfindex_ty {k11 : Hvl} {S37 : Ty} (wft : (wfTy k11 S37)) :
    (forall {d : (Trace ty)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_ty k11 d k12 k13) -> (forall {X49 : (Index ty)} ,
        (wfindex k12 X49) -> (wfTy k13 (tsubstIndex d S37 X49)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_tm_wfindex_ty {k11 : Hvl} :
    (forall {d : (Trace tm)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_tm k11 d k12 k13) -> (forall {X49 : (Index ty)} ,
        (wfindex k12 X49) -> (wfindex k13 X49))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_ty_wfindex_tm {k11 : Hvl} :
    (forall {d : (Trace ty)} {k12 : Hvl} {k13 : Hvl} ,
      (substhvl_ty k11 d k12 k13) -> (forall {x6 : (Index tm)} ,
        (wfindex k12 x6) -> (wfindex k13 x6))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_tm_wfKind {k11 : Hvl} : (forall (k12 : Hvl) ,
    (forall (K84 : Kind) (wf0 : (wfKind k12 K84)) ,
      (forall {d : (Trace tm)} {k13 : Hvl} ,
        (substhvl_tm k11 d k12 k13) -> (wfKind k13 K84)))) := (fun (k12 : Hvl) =>
    (ind_wfKind k12 (fun (K84 : Kind) (wf0 : (wfKind k12 K84)) =>
      (forall {d : (Trace tm)} {k13 : Hvl} ,
        (substhvl_tm k11 d k12 k13) -> (wfKind k13 K84))) (fun {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
      (wfKind_star k13)) (fun (K1 : Kind) (wf0 : (wfKind k12 K1)) IHK1 (K2 : Kind) (wf1 : (wfKind k12 K2)) IHK2 {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
      (wfKind_karr k13 (IHK1 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)) (IHK2 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)))))).
  Definition substhvl_ty_wfKind {k11 : Hvl} : (forall (k12 : Hvl) ,
    (forall (K84 : Kind) (wf0 : (wfKind k12 K84)) ,
      (forall {d : (Trace ty)} {k13 : Hvl} ,
        (substhvl_ty k11 d k12 k13) -> (wfKind k13 K84)))) := (fun (k12 : Hvl) =>
    (ind_wfKind k12 (fun (K84 : Kind) (wf0 : (wfKind k12 K84)) =>
      (forall {d : (Trace ty)} {k13 : Hvl} ,
        (substhvl_ty k11 d k12 k13) -> (wfKind k13 K84))) (fun {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
      (wfKind_star k13)) (fun (K1 : Kind) (wf0 : (wfKind k12 K1)) IHK1 (K2 : Kind) (wf1 : (wfKind k12 K2)) IHK2 {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
      (wfKind_karr k13 (IHK1 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)) (IHK2 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)))))).
  Definition substhvl_tm_wfTy {k11 : Hvl} : (forall (k12 : Hvl) ,
    (forall (S37 : Ty) (wf0 : (wfTy k12 S37)) ,
      (forall {d : (Trace tm)} {k13 : Hvl} ,
        (substhvl_tm k11 d k12 k13) -> (wfTy k13 S37)))) := (ind_wfTy (fun (k12 : Hvl) (S37 : Ty) (wf0 : (wfTy k12 S37)) =>
    (forall {d : (Trace tm)} {k13 : Hvl} ,
      (substhvl_tm k11 d k12 k13) -> (wfTy k13 S37))) (fun (k12 : Hvl) {X49 : (Index ty)} (wfi : (wfindex k12 X49)) {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTy_tvar k13 _ (substhvl_tm_wfindex_ty del wfi))) (fun (k12 : Hvl) (K : Kind) (wf0 : (wfKind k12 K)) (T : Ty) (wf1 : (wfTy (HS ty k12) T)) IHT {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTy_tabs k13 (substhvl_tm_wfKind k12 K wf0 (weaken_substhvl_tm H0 del)) (IHT (weakenTrace d (HS ty H0)) (HS ty k13) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k12 : Hvl) (T1 : Ty) (wf0 : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k12 T2)) IHT2 {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTy_tapp k13 (IHT1 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)))) (fun (k12 : Hvl) (T1 : Ty) (wf0 : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k12 T2)) IHT2 {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTy_tarr k13 (IHT1 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)) (IHT2 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)))) (fun (k12 : Hvl) (K : Kind) (wf0 : (wfKind k12 K)) (T : Ty) (wf1 : (wfTy (HS ty k12) T)) IHT {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTy_tall k13 (substhvl_tm_wfKind k12 K wf0 (weaken_substhvl_tm H0 del)) (IHT (weakenTrace d (HS ty H0)) (HS ty k13) (weaken_substhvl_tm (HS ty H0) del))))).
  Definition substhvl_ty_wfTy {k11 : Hvl} {S37 : Ty} (wf : (wfTy k11 S37)) : (forall (k12 : Hvl) ,
    (forall (S38 : Ty) (wf0 : (wfTy k12 S38)) ,
      (forall {d : (Trace ty)} {k13 : Hvl} ,
        (substhvl_ty k11 d k12 k13) -> (wfTy k13 (tsubstTy d S37 S38))))) := (ind_wfTy (fun (k12 : Hvl) (S38 : Ty) (wf0 : (wfTy k12 S38)) =>
    (forall {d : (Trace ty)} {k13 : Hvl} ,
      (substhvl_ty k11 d k12 k13) -> (wfTy k13 (tsubstTy d S37 S38)))) (fun (k12 : Hvl) {X49 : (Index ty)} (wfi : (wfindex k12 X49)) {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (substhvl_ty_wfindex_ty wf del wfi)) (fun (k12 : Hvl) (K : Kind) (wf0 : (wfKind k12 K)) (T : Ty) (wf1 : (wfTy (HS ty k12) T)) IHT {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTy_tabs k13 (substhvl_ty_wfKind k12 K wf0 (weaken_substhvl_ty H0 del)) (IHT (weakenTrace d (HS ty H0)) (HS ty k13) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k12 : Hvl) (T1 : Ty) (wf0 : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k12 T2)) IHT2 {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTy_tapp k13 (IHT1 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)))) (fun (k12 : Hvl) (T1 : Ty) (wf0 : (wfTy k12 T1)) IHT1 (T2 : Ty) (wf1 : (wfTy k12 T2)) IHT2 {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTy_tarr k13 (IHT1 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)) (IHT2 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)))) (fun (k12 : Hvl) (K : Kind) (wf0 : (wfKind k12 K)) (T : Ty) (wf1 : (wfTy (HS ty k12) T)) IHT {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTy_tall k13 (substhvl_ty_wfKind k12 K wf0 (weaken_substhvl_ty H0 del)) (IHT (weakenTrace d (HS ty H0)) (HS ty k13) (weaken_substhvl_ty (HS ty H0) del))))).
  Definition substhvl_tm_wfTm {k11 : Hvl} {s4 : Tm} (wf : (wfTm k11 s4)) : (forall (k12 : Hvl) ,
    (forall (s5 : Tm) (wf0 : (wfTm k12 s5)) ,
      (forall {d : (Trace tm)} {k13 : Hvl} ,
        (substhvl_tm k11 d k12 k13) -> (wfTm k13 (substTm d s4 s5))))) := (ind_wfTm (fun (k12 : Hvl) (s5 : Tm) (wf0 : (wfTm k12 s5)) =>
    (forall {d : (Trace tm)} {k13 : Hvl} ,
      (substhvl_tm k11 d k12 k13) -> (wfTm k13 (substTm d s4 s5)))) (fun (k12 : Hvl) {x6 : (Index tm)} (wfi : (wfindex k12 x6)) {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (substhvl_tm_wfindex_tm wf del wfi)) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) (t : Tm) (wf1 : (wfTm (HS tm k12) t)) IHt {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTm_abs k13 (substhvl_tm_wfTy k12 T wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d (HS tm H0)) (HS tm k13) (weaken_substhvl_tm (HS tm H0) del)))) (fun (k12 : Hvl) (t1 : Tm) (wf0 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k12 t2)) IHt2 {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTm_app k13 (IHt1 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)) (IHt2 (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)))) (fun (k12 : Hvl) (K : Kind) (wf0 : (wfKind k12 K)) (t : Tm) (wf1 : (wfTm (HS ty k12) t)) IHt {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTm_tyabs k13 (substhvl_tm_wfKind k12 K wf0 (weaken_substhvl_tm H0 del)) (IHt (weakenTrace d (HS ty H0)) (HS ty k13) (weaken_substhvl_tm (HS ty H0) del)))) (fun (k12 : Hvl) (t : Tm) (wf0 : (wfTm k12 t)) IHt (T : Ty) (wf1 : (wfTy k12 T)) {d : (Trace tm)} {k13 : Hvl} (del : (substhvl_tm k11 d k12 k13)) =>
    (wfTm_tyapp k13 (IHt (weakenTrace d H0) k13 (weaken_substhvl_tm H0 del)) (substhvl_tm_wfTy k12 T wf1 (weaken_substhvl_tm H0 del))))).
  Definition substhvl_ty_wfTm {k11 : Hvl} {S37 : Ty} (wf : (wfTy k11 S37)) : (forall (k12 : Hvl) ,
    (forall (s4 : Tm) (wf0 : (wfTm k12 s4)) ,
      (forall {d : (Trace ty)} {k13 : Hvl} ,
        (substhvl_ty k11 d k12 k13) -> (wfTm k13 (tsubstTm d S37 s4))))) := (ind_wfTm (fun (k12 : Hvl) (s4 : Tm) (wf0 : (wfTm k12 s4)) =>
    (forall {d : (Trace ty)} {k13 : Hvl} ,
      (substhvl_ty k11 d k12 k13) -> (wfTm k13 (tsubstTm d S37 s4)))) (fun (k12 : Hvl) {x6 : (Index tm)} (wfi : (wfindex k12 x6)) {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTm_var k13 _ (substhvl_ty_wfindex_tm del wfi))) (fun (k12 : Hvl) (T : Ty) (wf0 : (wfTy k12 T)) (t : Tm) (wf1 : (wfTm (HS tm k12) t)) IHt {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTm_abs k13 (substhvl_ty_wfTy wf k12 T wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d (HS tm H0)) (HS tm k13) (weaken_substhvl_ty (HS tm H0) del)))) (fun (k12 : Hvl) (t1 : Tm) (wf0 : (wfTm k12 t1)) IHt1 (t2 : Tm) (wf1 : (wfTm k12 t2)) IHt2 {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTm_app k13 (IHt1 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)) (IHt2 (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)))) (fun (k12 : Hvl) (K : Kind) (wf0 : (wfKind k12 K)) (t : Tm) (wf1 : (wfTm (HS ty k12) t)) IHt {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTm_tyabs k13 (substhvl_ty_wfKind k12 K wf0 (weaken_substhvl_ty H0 del)) (IHt (weakenTrace d (HS ty H0)) (HS ty k13) (weaken_substhvl_ty (HS ty H0) del)))) (fun (k12 : Hvl) (t : Tm) (wf0 : (wfTm k12 t)) IHt (T : Ty) (wf1 : (wfTy k12 T)) {d : (Trace ty)} {k13 : Hvl} (del : (substhvl_ty k11 d k12 k13)) =>
    (wfTm_tyapp k13 (IHt (weakenTrace d H0) k13 (weaken_substhvl_ty H0 del)) (substhvl_ty_wfTy wf k12 T wf1 (weaken_substhvl_ty H0 del))))).
End SubstWellFormed.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : infra.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : subst_wf.
 Hint Resolve substhvl_tm_wfindex_tm substhvl_tm_wfindex_ty substhvl_ty_wfindex_tm substhvl_ty_wfindex_ty : wf.
 Hint Resolve substhvl_tm_wfKind substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfKind substhvl_ty_wfTm substhvl_ty_wfTy : infra.
 Hint Resolve substhvl_tm_wfKind substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfKind substhvl_ty_wfTm substhvl_ty_wfTy : subst.
 Hint Resolve substhvl_tm_wfKind substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfKind substhvl_ty_wfTm substhvl_ty_wfTy : subst_wf.
 Hint Resolve substhvl_tm_wfKind substhvl_tm_wfTm substhvl_tm_wfTy substhvl_ty_wfKind substhvl_ty_wfTm substhvl_ty_wfTy : wf.
 Hint Constructors substhvl_tm substhvl_ty : infra.
 Hint Constructors substhvl_tm substhvl_ty : subst.
 Hint Constructors substhvl_tm substhvl_ty : subst_wf.
 Hint Constructors substhvl_tm substhvl_ty : wf.
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
      | (evar G0 T) => (HS tm (domainEnv G0))
      | (etvar G0 K) => (HS ty (domainEnv G0))
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
  Fixpoint shiftEnv (c : (Cutoff tm)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (shiftEnv c G0) T)
      | (etvar G0 K) => (etvar (shiftEnv c G0) K)
    end.
  Fixpoint tshiftEnv (c : (Cutoff ty)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tshiftEnv c G0) (tshiftTy (weakenCutoffty c (domainEnv G0)) T))
      | (etvar G0 K) => (etvar (tshiftEnv c G0) K)
    end.
  Fixpoint weakenEnv (G : Env) (k11 : Hvl) {struct k11} :
  Env :=
    match k11 with
      | (H0) => G
      | (HS tm k11) => (weakenEnv G k11)
      | (HS ty k11) => (tshiftEnv C0 (weakenEnv G k11))
    end.
  Fixpoint substEnv (d : (Trace tm)) (s4 : Tm) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (substEnv d s4 G0) T)
      | (etvar G0 K) => (etvar (substEnv d s4 G0) K)
    end.
  Fixpoint tsubstEnv (d : (Trace ty)) (S37 : Ty) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (evar G0 T) => (evar (tsubstEnv d S37 G0) (tsubstTy (weakenTrace d (domainEnv G0)) S37 T))
      | (etvar G0 K) => (etvar (tsubstEnv d S37 G0) K)
    end.
  Lemma domainEnv_shiftEnv  :
    (forall (c : (Cutoff tm)) (G : Env) ,
      ((domainEnv (shiftEnv c G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_tshiftEnv  :
    (forall (c : (Cutoff ty)) (G : Env) ,
      ((domainEnv (tshiftEnv c G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_substEnv  :
    (forall (d : (Trace tm)) (s4 : Tm) (G : Env) ,
      ((domainEnv (substEnv d s4 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_tsubstEnv  :
    (forall (d : (Trace ty)) (S37 : Ty) (G : Env) ,
      ((domainEnv (tsubstEnv d S37 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shiftEnv_appendEnv  :
      (forall (c : (Cutoff tm)) (G : Env) (G0 : Env) ,
        ((shiftEnv c (appendEnv G G0)) = (appendEnv (shiftEnv c G) (shiftEnv (weakenCutofftm c (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma tshiftEnv_appendEnv  :
      (forall (c : (Cutoff ty)) (G : Env) (G0 : Env) ,
        ((tshiftEnv c (appendEnv G G0)) = (appendEnv (tshiftEnv c G) (tshiftEnv (weakenCutoffty c (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma substEnv_appendEnv  :
      (forall (d : (Trace tm)) (s4 : Tm) (G : Env) (G0 : Env) ,
        ((substEnv d s4 (appendEnv G G0)) = (appendEnv (substEnv d s4 G) (substEnv (weakenTrace d (domainEnv G)) s4 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma tsubstEnv_appendEnv  :
      (forall (d : (Trace ty)) (S37 : Ty) (G : Env) (G0 : Env) ,
        ((tsubstEnv d S37 (appendEnv G G0)) = (appendEnv (tsubstEnv d S37 G) (tsubstEnv (weakenTrace d (domainEnv G)) S37 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenKind_append  :
    (forall (K84 : Kind) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenKind (weakenKind K84 k11) k12) = (weakenKind K84 (appendHvl k11 k12)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTy_append  :
    (forall (S37 : Ty) (k11 : Hvl) (k12 : Hvl) ,
      ((weakenTy (weakenTy S37 k11) k12) = (weakenTy S37 (appendHvl k11 k12)))).
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
    Inductive lookup_evar : Env -> (Index tm) -> Ty -> Prop :=
      | lookup_evar_here {G : Env}
          (T98 : Ty) :
          (wfTy (domainEnv G) T98) -> (lookup_evar (evar G T98) I0 T98)
      | lookup_evar_there_evar
          {G : Env} {x6 : (Index tm)}
          (T99 : Ty) (T100 : Ty) :
          (lookup_evar G x6 T99) -> (lookup_evar (evar G T100) (IS x6) T99)
      | lookup_evar_there_etvar
          {G : Env} {x6 : (Index tm)}
          (T99 : Ty) (K84 : Kind) :
          (lookup_evar G x6 T99) -> (lookup_evar (etvar G K84) x6 (tshiftTy C0 T99)).
    Inductive lookup_etvar : Env -> (Index ty) -> Kind -> Prop :=
      | lookup_etvar_here {G : Env}
          (K84 : Kind) :
          (wfKind (domainEnv G) K84) -> (lookup_etvar (etvar G K84) I0 K84)
      | lookup_etvar_there_evar
          {G : Env} {X49 : (Index ty)}
          (K85 : Kind) (T99 : Ty) :
          (lookup_etvar G X49 K85) -> (lookup_etvar (evar G T99) X49 K85)
      | lookup_etvar_there_etvar
          {G : Env} {X49 : (Index ty)}
          (K85 : Kind) (K86 : Kind) :
          (lookup_etvar G X49 K85) -> (lookup_etvar (etvar G K86) (IS X49) K85).
    Lemma lookup_evar_inversion_here  :
      (forall (G : Env) (T99 : Ty) (T100 : Ty) ,
        (lookup_evar (evar G T99) I0 T100) -> (T99 = T100)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_etvar_inversion_here  :
      (forall (G : Env) (K85 : Kind) (K86 : Kind) ,
        (lookup_etvar (etvar G K85) I0 K86) -> (K85 = K86)).
    Proof.
      needleGenericLookupInversion .
    Qed.
    Lemma lookup_evar_functional  :
      (forall {G : Env} {x6 : (Index tm)} ,
        (forall (T99 : Ty) ,
          (lookup_evar G x6 T99) -> (forall (T100 : Ty) ,
            (lookup_evar G x6 T100) -> (T99 = T100)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_etvar_functional  :
      (forall {G : Env} {X49 : (Index ty)} ,
        (forall (K85 : Kind) ,
          (lookup_etvar G X49 K85) -> (forall (K86 : Kind) ,
            (lookup_etvar G X49 K86) -> (K85 = K86)))).
    Proof.
      needleGenericLookupFunctional .
    Qed.
    Lemma lookup_evar_wf  :
      (forall {G : Env} {x6 : (Index tm)} (T99 : Ty) ,
        (lookup_evar G x6 T99) -> (wfTy (domainEnv G) T99)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma lookup_etvar_wf  :
      (forall {G : Env} {X49 : (Index ty)} (K85 : Kind) ,
        (lookup_etvar G X49 K85) -> (wfKind (domainEnv G) K85)).
    Proof.
      needleGenericLookupWellformedData .
    Qed.
    Lemma weaken_lookup_evar  :
      (forall {G : Env} (G0 : Env) {x6 : (Index tm)} (T99 : Ty) ,
        (lookup_evar G x6 T99) -> (lookup_evar (appendEnv G G0) (weakenIndextm x6 (domainEnv G0)) (weakenTy T99 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_etvar  :
      (forall {G : Env} (G0 : Env) {X49 : (Index ty)} (K85 : Kind) ,
        (lookup_etvar G X49 K85) -> (lookup_etvar (appendEnv G G0) (weakenIndexty X49 (domainEnv G0)) (weakenKind K85 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_evar_wfindex  :
      (forall {G : Env} {x6 : (Index tm)} (T101 : Ty) ,
        (lookup_evar G x6 T101) -> (wfindex (domainEnv G) x6)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_etvar_wfindex  :
      (forall {G : Env} {X49 : (Index ty)} (K87 : Kind) ,
        (lookup_etvar G X49 K87) -> (wfindex (domainEnv G) X49)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_evar : (Cutoff tm) -> Env -> Env -> Prop :=
    | shift_evar_here {G : Env}
        {T99 : Ty} :
        (shift_evar C0 G (evar G T99))
    | shiftevar_there_evar
        {c : (Cutoff tm)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_evar c G G0) -> (shift_evar (CS c) (evar G T) (evar G0 T))
    | shiftevar_there_etvar
        {c : (Cutoff tm)} {G : Env}
        {G0 : Env} {K : Kind} :
        (shift_evar c G G0) -> (shift_evar c (etvar G K) (etvar G0 K)).
  Lemma weaken_shift_evar  :
    (forall (G : Env) {c : (Cutoff tm)} {G0 : Env} {G1 : Env} ,
      (shift_evar c G0 G1) -> (shift_evar (weakenCutofftm c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_etvar : (Cutoff ty) -> Env -> Env -> Prop :=
    | shift_etvar_here {G : Env}
        {K85 : Kind} :
        (shift_etvar C0 G (etvar G K85))
    | shiftetvar_there_evar
        {c : (Cutoff ty)} {G : Env}
        {G0 : Env} {T : Ty} :
        (shift_etvar c G G0) -> (shift_etvar c (evar G T) (evar G0 (tshiftTy c T)))
    | shiftetvar_there_etvar
        {c : (Cutoff ty)} {G : Env}
        {G0 : Env} {K : Kind} :
        (shift_etvar c G G0) -> (shift_etvar (CS c) (etvar G K) (etvar G0 K)).
  Lemma weaken_shift_etvar  :
    (forall (G : Env) {c : (Cutoff ty)} {G0 : Env} {G1 : Env} ,
      (shift_etvar c G0 G1) -> (shift_etvar (weakenCutoffty c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 (tshiftEnv c G)))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_evar_shifthvl_tm  :
    (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} ,
      (shift_evar c G G0) -> (shifthvl_tm c (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_etvar_shifthvl_ty  :
    (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} ,
      (shift_etvar c G G0) -> (shifthvl_ty c (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_evar (G : Env) (T99 : Ty) (s4 : Tm) : (Trace tm) -> Env -> Env -> Prop :=
    | subst_evar_here :
        (subst_evar G T99 s4 X0 (evar G T99) G)
    | subst_evar_there_evar
        {d : (Trace tm)} {G0 : Env}
        {G1 : Env} (T100 : Ty) :
        (subst_evar G T99 s4 d G0 G1) -> (subst_evar G T99 s4 (XS tm d) (evar G0 T100) (evar G1 T100))
    | subst_evar_there_etvar
        {d : (Trace tm)} {G0 : Env}
        {G1 : Env} (K85 : Kind) :
        (subst_evar G T99 s4 d G0 G1) -> (subst_evar G T99 s4 (XS ty d) (etvar G0 K85) (etvar G1 K85)).
  Lemma weaken_subst_evar {G : Env} (T99 : Ty) {s4 : Tm} :
    (forall (G0 : Env) {d : (Trace tm)} {G1 : Env} {G2 : Env} ,
      (subst_evar G T99 s4 d G1 G2) -> (subst_evar G T99 s4 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_etvar (G : Env) (K85 : Kind) (S37 : Ty) : (Trace ty) -> Env -> Env -> Prop :=
    | subst_etvar_here :
        (subst_etvar G K85 S37 X0 (etvar G K85) G)
    | subst_etvar_there_evar
        {d : (Trace ty)} {G0 : Env}
        {G1 : Env} (T99 : Ty) :
        (subst_etvar G K85 S37 d G0 G1) -> (subst_etvar G K85 S37 (XS tm d) (evar G0 T99) (evar G1 (tsubstTy d S37 T99)))
    | subst_etvar_there_etvar
        {d : (Trace ty)} {G0 : Env}
        {G1 : Env} (K86 : Kind) :
        (subst_etvar G K85 S37 d G0 G1) -> (subst_etvar G K85 S37 (XS ty d) (etvar G0 K86) (etvar G1 K86)).
  Lemma weaken_subst_etvar {G : Env} (K85 : Kind) {S37 : Ty} :
    (forall (G0 : Env) {d : (Trace ty)} {G1 : Env} {G2 : Env} ,
      (subst_etvar G K85 S37 d G1 G2) -> (subst_etvar G K85 S37 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 (tsubstEnv d S37 G0)))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_evar_substhvl_tm {G : Env} {s4 : Tm} (T99 : Ty) :
    (forall {d : (Trace tm)} {G0 : Env} {G1 : Env} ,
      (subst_evar G T99 s4 d G0 G1) -> (substhvl_tm (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_etvar_substhvl_ty {G : Env} {S37 : Ty} (K85 : Kind) :
    (forall {d : (Trace ty)} {G0 : Env} {G1 : Env} ,
      (subst_etvar G K85 S37 d G0 G1) -> (substhvl_ty (domainEnv G) d (domainEnv G0) (domainEnv G1))).
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
  (forall {G : Env} (G0 : Env) {T99 : Ty} (wf : (wfTy (domainEnv G) T99)) ,
    (lookup_evar (appendEnv (evar G T99) G0) (weakenIndextm I0 (domainEnv G0)) (weakenTy T99 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_etvar_here  :
  (forall {G : Env} (G0 : Env) {K85 : Kind} (wf : (wfKind (domainEnv G) K85)) ,
    (lookup_etvar (appendEnv (etvar G K85) G0) (weakenIndexty I0 (domainEnv G0)) (weakenKind K85 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfKind wfTm wfTy : infra.
 Hint Constructors wfKind wfTm wfTy : wf.
 Hint Extern 10 ((wfKind _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTy _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfKind _ _)) => match goal with
  | H41 : (wfKind _ (star)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfKind _ (karr _ _)) |- _ => inversion H41; subst; clear H41
end : infra wf.
 Hint Extern 2 ((wfTy _ _)) => match goal with
  | H41 : (wfTy _ (tvar _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTy _ (tabs _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTy _ (tapp _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTy _ (tarr _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTy _ (tall _ _)) |- _ => inversion H41; subst; clear H41
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H41 : (wfTm _ (var _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (abs _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (app _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (tyabs _ _)) |- _ => inversion H41; subst; clear H41
  | H41 : (wfTm _ (tyapp _ _)) |- _ => inversion H41; subst; clear H41
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
  (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {x6 : (Index tm)} {T99 : Ty} ,
    (lookup_evar G x6 T99) -> (lookup_evar G0 (shiftIndex c x6) T99)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_evar_lookup_etvar  :
  (forall {c : (Cutoff tm)} {G : Env} {G0 : Env} (ins : (shift_evar c G G0)) {X49 : (Index ty)} {K85 : Kind} ,
    (lookup_etvar G X49 K85) -> (lookup_etvar G0 X49 K85)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_evar  :
  (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {x6 : (Index tm)} {T99 : Ty} ,
    (lookup_evar G x6 T99) -> (lookup_evar G0 x6 (tshiftTy c T99))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_etvar_lookup_etvar  :
  (forall {c : (Cutoff ty)} {G : Env} {G0 : Env} (ins : (shift_etvar c G G0)) {X49 : (Index ty)} {K85 : Kind} ,
    (lookup_etvar G X49 K85) -> (lookup_etvar G0 (tshiftIndex c X49) K85)).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : infra.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : lookup.
 Hint Resolve shift_evar_lookup_evar shift_evar_lookup_etvar shift_etvar_lookup_evar shift_etvar_lookup_etvar : shift.
Lemma subst_evar_lookup_etvar {G : Env} (T100 : Ty) {s4 : Tm} :
  (forall {d : (Trace tm)} {G0 : Env} {G1 : Env} (sub : (subst_evar G T100 s4 d G0 G1)) {X49 : (Index ty)} (K86 : Kind) ,
    (lookup_etvar G0 X49 K86) -> (lookup_etvar G1 X49 K86)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_etvar_lookup_evar {G : Env} (K86 : Kind) {S37 : Ty} (wf : (wfTy (domainEnv G) S37)) :
  (forall {d : (Trace ty)} {G0 : Env} {G1 : Env} (sub : (subst_etvar G K86 S37 d G0 G1)) {x6 : (Index tm)} (T100 : Ty) ,
    (lookup_evar G0 x6 T100) -> (lookup_evar G1 x6 (tsubstTy d S37 T100))).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : infra.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : lookup.
 Hint Resolve subst_evar_lookup_etvar subst_etvar_lookup_evar : subst.
Fixpoint size_Kind (K82 : Kind) {struct K82} :
nat :=
  match K82 with
    | (star) => 1
    | (karr K83 K84) => (plus 1 (plus (size_Kind K83) (size_Kind K84)))
  end.
Fixpoint size_Ty (S32 : Ty) {struct S32} :
nat :=
  match S32 with
    | (tvar X49) => 1
    | (tabs K82 T98) => (plus 1 (plus (size_Kind K82) (size_Ty T98)))
    | (tapp T99 T100) => (plus 1 (plus (size_Ty T99) (size_Ty T100)))
    | (tarr T101 T102) => (plus 1 (plus (size_Ty T101) (size_Ty T102)))
    | (tall K83 T103) => (plus 1 (plus (size_Kind K83) (size_Ty T103)))
  end.
Fixpoint size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (var x6) => 1
    | (abs T98 t17) => (plus 1 (plus (size_Ty T98) (size_Tm t17)))
    | (app t18 t19) => (plus 1 (plus (size_Tm t18) (size_Tm t19)))
    | (tyabs K82 t20) => (plus 1 (plus (size_Kind K82) (size_Tm t20)))
    | (tyapp t21 T99) => (plus 1 (plus (size_Tm t21) (size_Ty T99)))
  end.
Fixpoint tshift_size_Ty (S32 : Ty) (c : (Cutoff ty)) {struct S32} :
((size_Ty (tshiftTy c S32)) = (size_Ty S32)) :=
  match S32 return ((size_Ty (tshiftTy c S32)) = (size_Ty S32)) with
    | (tvar _) => eq_refl
    | (tabs K T) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (tshift_size_Ty T (CS c))))
    | (tapp T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c) (tshift_size_Ty T2 c)))
    | (tarr T1 T2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T1 c) (tshift_size_Ty T2 c)))
    | (tall K T) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (tshift_size_Ty T (CS c))))
  end.
Fixpoint shift_size_Tm (s : Tm) (c : (Cutoff tm)) {struct s} :
((size_Tm (shiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (shiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t (CS c))))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t1 c) (shift_size_Tm t2 c)))
    | (tyabs K t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (shift_size_Tm t c)))
    | (tyapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_size_Tm t c) eq_refl))
  end.
Fixpoint tshift_size_Tm (s : Tm) (c : (Cutoff ty)) {struct s} :
((size_Tm (tshiftTm c s)) = (size_Tm s)) :=
  match s return ((size_Tm (tshiftTm c s)) = (size_Tm s)) with
    | (var _) => eq_refl
    | (abs T t) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Ty T c) (tshift_size_Tm t c)))
    | (app t1 t2) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t1 c) (tshift_size_Tm t2 c)))
    | (tyabs K t) => (f_equal2 plus eq_refl (f_equal2 plus eq_refl (tshift_size_Tm t (CS c))))
    | (tyapp t T) => (f_equal2 plus eq_refl (f_equal2 plus (tshift_size_Tm t c) (tshift_size_Ty T c)))
  end.
 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : interaction.
 Hint Rewrite shift_size_Tm tshift_size_Tm tshift_size_Ty : shift_size.
Lemma weaken_size_Kind  :
  (forall (k : Hvl) (K82 : Kind) ,
    ((size_Kind (weakenKind K82 k)) = (size_Kind K82))).
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
  (forall (k : Hvl) (S32 : Ty) ,
    ((size_Ty (weakenTy S32 k)) = (size_Ty S32))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Kind weaken_size_Tm weaken_size_Ty : interaction.
 Hint Rewrite weaken_size_Kind weaken_size_Tm weaken_size_Ty : weaken_size.
Inductive TRed (G : Env) : Ty -> Ty -> Kind -> Prop :=
  | QR_Var (K : Kind)
      (X : (Index ty))
      (lk : (lookup_etvar G X K))
      (H26 : (wfKind (domainEnv G) K))
      (H27 : (wfindex (domainEnv G) X))
      : (TRed G (tvar X) (tvar X) K)
  | QR_Arrow (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm27 : (TRed G S1 T1 (star)))
      (jm28 : (TRed G S2 T2 (star))) :
      (TRed G (tarr S1 S2) (tarr T1 T2) (star))
  | QR_Abs (K1 : Kind) (K2 : Kind)
      (S2 : Ty) (T2 : Ty)
      (jm29 : (TRed (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0))))
      (H32 : (wfKind (domainEnv G) K1))
      (H33 : (wfKind (domainEnv G) K2))
      :
      (TRed G (tabs K1 S2) (tabs K1 T2) (karr K1 K2))
  | QR_App (K1 : Kind) (K2 : Kind)
      (S1 : Ty) (S2 : Ty) (T1 : Ty)
      (T2 : Ty)
      (jm30 : (TRed G S1 T1 (karr K2 K1)))
      (jm31 : (TRed G S2 T2 K2)) :
      (TRed G (tapp S1 S2) (tapp T1 T2) K1)
  | QR_All (K1 : Kind) (S2 : Ty)
      (T2 : Ty)
      (jm32 : (TRed (etvar G K1) S2 T2 (star)))
      (H42 : (wfKind (domainEnv G) K1))
      :
      (TRed G (tall K1 S2) (tall K1 T2) (star))
  | QR_Beta (K1 : Kind)
      (K2 : Kind) (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm33 : (TRed (etvar G K2) S1 T1 (weakenKind K1 (HS ty H0))))
      (jm34 : (TRed G S2 T2 K2))
      (H45 : (wfKind (domainEnv G) K1))
      :
      (TRed G (tapp (tabs K2 S1) S2) (tsubstTy X0 T2 T1) K1).
Inductive Kinding (G : Env) : Ty -> Kind -> Prop :=
  | K_TVar (K : Kind)
      (X : (Index ty))
      (lk : (lookup_etvar G X K))
      (H25 : (wfKind (domainEnv G) K))
      (H26 : (wfindex (domainEnv G) X))
      : (Kinding G (tvar X) K)
  | K_Abs (K1 : Kind) (K2 : Kind)
      (T2 : Ty)
      (jm : (Kinding (etvar G K1) T2 (weakenKind K2 (HS ty H0))))
      (H27 : (wfKind (domainEnv G) K1))
      (H28 : (wfKind (domainEnv G) K2))
      :
      (Kinding G (tabs K1 T2) (karr K1 K2))
  | K_App (K11 : Kind)
      (K12 : Kind) (T1 : Ty) (T2 : Ty)
      (jm0 : (Kinding G T1 (karr K11 K12)))
      (jm1 : (Kinding G T2 K11)) :
      (Kinding G (tapp T1 T2) K12)
  | K_Arr (T1 : Ty) (T2 : Ty)
      (jm2 : (Kinding G T1 (star)))
      (jm3 : (Kinding G T2 (star))) :
      (Kinding G (tarr T1 T2) (star))
  | K_All (K1 : Kind) (T2 : Ty)
      (jm4 : (Kinding (etvar G K1) T2 (star)))
      (H36 : (wfKind (domainEnv G) K1))
      :
      (Kinding G (tall K1 T2) (star)).
Inductive TRedStar (G : Env) : Ty -> Ty -> Kind -> Prop :=
  | QRS_Nil (K : Kind) (T : Ty)
      (jm35 : (Kinding G T K)) :
      (TRedStar G T T K)
  | QRS_Cons (K : Kind) (S1 : Ty)
      (T : Ty) (U : Ty)
      (jm36 : (TRedStar G S1 T K))
      (jm37 : (TRed G T U K)) :
      (TRedStar G S1 U K).
Inductive TyEq (G : Env) : Ty -> Ty -> Kind -> Prop :=
  | Q_Arrow (S1 : Ty) (S2 : Ty)
      (T1 : Ty) (T2 : Ty)
      (jm5 : (TyEq G S1 T1 (star)))
      (jm6 : (TyEq G S2 T2 (star))) :
      (TyEq G (tarr S1 S2) (tarr T1 T2) (star))
  | Q_Abs (K1 : Kind) (K2 : Kind)
      (S2 : Ty) (T2 : Ty)
      (jm7 : (TyEq (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0))))
      (H30 : (wfKind (domainEnv G) K1))
      (H31 : (wfKind (domainEnv G) K2))
      :
      (TyEq G (tabs K1 S2) (tabs K1 T2) (karr K1 K2))
  | Q_App (K1 : Kind) (K2 : Kind)
      (S1 : Ty) (S2 : Ty) (T1 : Ty)
      (T2 : Ty)
      (jm8 : (TyEq G S1 T1 (karr K1 K2)))
      (jm9 : (TyEq G S2 T2 K1)) :
      (TyEq G (tapp S1 S2) (tapp T1 T2) K2)
  | Q_All (K1 : Kind) (S2 : Ty)
      (T2 : Ty)
      (jm10 : (TyEq (etvar G K1) S2 T2 (star)))
      (H40 : (wfKind (domainEnv G) K1))
      :
      (TyEq G (tall K1 S2) (tall K1 T2) (star))
  | Q_Beta (K11 : Kind)
      (K12 : Kind) (T12 : Ty)
      (T2 : Ty)
      (jm11 : (Kinding (etvar G K11) T12 (weakenKind K12 (HS ty H0))))
      (jm12 : (Kinding G T2 K11))
      (H44 : (wfKind (domainEnv G) K12))
      :
      (TyEq G (tapp (tabs K11 T12) T2) (tsubstTy X0 T2 T12) K12)
  | Q_Eta (K1 : Kind) (K2 : Kind)
      (T : Ty)
      (jm13 : (Kinding G T (karr K1 K2)))
      :
      (TyEq G (tabs K1 (tapp (weakenTy T (HS ty H0)) (tvar I0))) T (karr K1 K2))
  | Q_Refl (K : Kind) (T : Ty)
      (jm14 : (Kinding G T K)) :
      (TyEq G T T K)
  | Q_Symm (K : Kind) (T : Ty)
      (U : Ty) (jm15 : (TyEq G T U K))
      : (TyEq G U T K)
  | Q_Trans (K : Kind) (T : Ty)
      (U : Ty) (V : Ty)
      (jm16 : (TyEq G T U K))
      (jm17 : (TyEq G U V K)) :
      (TyEq G T V K).
Inductive Typing (G : Env) : Tm -> Ty -> Prop :=
  | T_Var (T : Ty)
      (y : (Index tm))
      (lk0 : (lookup_evar G y T))
      (H25 : (wfTy (domainEnv G) T))
      (H26 : (wfindex (domainEnv G) y))
      : (Typing G (var y) T)
  | T_Abs (T1 : Ty) (T2 : Ty)
      (t : Tm)
      (jm18 : (Kinding G T1 (star)))
      (jm19 : (Typing (evar G T1) t (weakenTy T2 (HS tm H0))))
      (H28 : (wfTy (domainEnv G) T2))
      :
      (Typing G (abs T1 t) (tarr T1 T2))
  | T_App (T11 : Ty) (T12 : Ty)
      (t1 : Tm) (t2 : Tm)
      (jm20 : (Typing G t1 (tarr T11 T12)))
      (jm21 : (Typing G t2 T11)) :
      (Typing G (app t1 t2) T12)
  | T_TAbs (K : Kind) (T : Ty)
      (t : Tm)
      (jm22 : (Typing (etvar G K) t T))
      (H34 : (wfKind (domainEnv G) K))
      :
      (Typing G (tyabs K t) (tall K T))
  | T_TApp (K11 : Kind) (T12 : Ty)
      (T2 : Ty) (t1 : Tm)
      (jm23 : (Typing G t1 (tall K11 T12)))
      (jm24 : (Kinding G T2 K11)) :
      (Typing G (tyapp t1 T2) (tsubstTy X0 T2 T12))
  | T_Eq (S1 : Ty) (T : Ty)
      (t : Tm)
      (jm25 : (Typing G t S1))
      (jm26 : (TyEq G S1 T (star))) :
      (Typing G t T).
Lemma TRed_cast  :
  (forall (G : Env) (T101 : Ty) (T102 : Ty) (K87 : Kind) (G0 : Env) (T103 : Ty) (T104 : Ty) (K88 : Kind) ,
    (G = G0) -> (T101 = T103) -> (T102 = T104) -> (K87 = K88) -> (TRed G T101 T102 K87) -> (TRed G0 T103 T104 K88)).
Proof.
  congruence .
Qed.
Lemma Kinding_cast  :
  (forall (G : Env) (T101 : Ty) (K87 : Kind) (G0 : Env) (T102 : Ty) (K88 : Kind) ,
    (G = G0) -> (T101 = T102) -> (K87 = K88) -> (Kinding G T101 K87) -> (Kinding G0 T102 K88)).
Proof.
  congruence .
Qed.
Lemma TRedStar_cast  :
  (forall (G : Env) (T101 : Ty) (T102 : Ty) (K87 : Kind) (G0 : Env) (T103 : Ty) (T104 : Ty) (K88 : Kind) ,
    (G = G0) -> (T101 = T103) -> (T102 = T104) -> (K87 = K88) -> (TRedStar G T101 T102 K87) -> (TRedStar G0 T103 T104 K88)).
Proof.
  congruence .
Qed.
Lemma TyEq_cast  :
  (forall (G : Env) (T101 : Ty) (T102 : Ty) (K87 : Kind) (G0 : Env) (T103 : Ty) (T104 : Ty) (K88 : Kind) ,
    (G = G0) -> (T101 = T103) -> (T102 = T104) -> (K87 = K88) -> (TyEq G T101 T102 K87) -> (TyEq G0 T103 T104 K88)).
Proof.
  congruence .
Qed.
Lemma Typing_cast  :
  (forall (G : Env) (t17 : Tm) (T101 : Ty) (G0 : Env) (t18 : Tm) (T102 : Ty) ,
    (G = G0) -> (t17 = t18) -> (T101 = T102) -> (Typing G t17 T101) -> (Typing G0 t18 T102)).
Proof.
  congruence .
Qed.
Fixpoint shift_evar_TRed (G9 : Env) (T116 : Ty) (T117 : Ty) (K99 : Kind) (jm51 : (TRed G9 T116 T117 K99)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) ,
  (TRed G10 T116 T117 K99)) :=
  match jm51 in (TRed _ T116 T117 K99) return (forall (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) ,
    (TRed G10 T116 T117 K99)) with
    | (QR_Var K96 X54 lk1 H64 H65) => (fun (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) =>
      (QR_Var G10 K96 X54 (shift_evar_lookup_etvar H92 lk1) (shift_wfKind _ _ H64 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H92))) (shift_wfindex_ty _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H92)) _ H65)))
    | (QR_Arrow S37 S38 T114 T115 jm43 jm44) => (fun (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) =>
      (QR_Arrow G10 S37 S38 T114 T115 (shift_evar_TRed G9 S37 T114 (star) jm43 c G10 (weaken_shift_evar empty H92)) (shift_evar_TRed G9 S38 T115 (star) jm44 c G10 (weaken_shift_evar empty H92))))
    | (QR_Abs K97 K98 S38 T115 jm45 H70 H71) => (fun (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) =>
      (QR_Abs G10 K97 K98 S38 T115 (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_evar_TRed (etvar G9 K97) S38 T115 (weakenKind K98 (HS ty H0)) jm45 c (etvar G10 K97) (weaken_shift_evar (etvar empty K97) H92))) (shift_wfKind _ _ H70 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H92))) (shift_wfKind _ _ H71 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H92)))))
    | (QR_App K97 K98 S37 S38 T114 T115 jm46 jm47) => (fun (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) =>
      (QR_App G10 K97 K98 S37 S38 T114 T115 (shift_evar_TRed G9 S37 T114 (karr K98 K97) jm46 c G10 (weaken_shift_evar empty H92)) (shift_evar_TRed G9 S38 T115 K98 jm47 c G10 (weaken_shift_evar empty H92))))
    | (QR_All K97 S38 T115 jm48 H80) => (fun (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) =>
      (QR_All G10 K97 S38 T115 (shift_evar_TRed (etvar G9 K97) S38 T115 (star) jm48 c (etvar G10 K97) (weaken_shift_evar (etvar empty K97) H92)) (shift_wfKind _ _ H80 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H92)))))
    | (QR_Beta K97 K98 S37 S38 T114 T115 jm49 jm50 H83) => (fun (c : (Cutoff tm)) (G10 : Env) (H92 : (shift_evar c G9 G10)) =>
      (QR_Beta G10 K97 K98 S37 S38 T114 T115 (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_evar_TRed (etvar G9 K98) S37 T114 (weakenKind K97 (HS ty H0)) jm49 c (etvar G10 K98) (weaken_shift_evar (etvar empty K98) H92))) (shift_evar_TRed G9 S38 T115 K98 jm50 c G10 (weaken_shift_evar empty H92)) (shift_wfKind _ _ H83 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H92)))))
  end.
Fixpoint shift_etvar_TRed (G9 : Env) (T116 : Ty) (T117 : Ty) (K99 : Kind) (jm51 : (TRed G9 T116 T117 K99)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) ,
  (TRed G10 (tshiftTy c T116) (tshiftTy c T117) K99)) :=
  match jm51 in (TRed _ T116 T117 K99) return (forall (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) ,
    (TRed G10 (tshiftTy c T116) (tshiftTy c T117) K99)) with
    | (QR_Var K96 X54 lk1 H64 H65) => (fun (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) =>
      (QR_Var G10 K96 (tshiftIndex c X54) (shift_etvar_lookup_etvar H92 lk1) (tshift_wfKind _ _ H64 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H92))) (tshift_wfindex_ty _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H92)) _ H65)))
    | (QR_Arrow S37 S38 T114 T115 jm43 jm44) => (fun (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) =>
      (QR_Arrow G10 (tshiftTy c S37) (tshiftTy c S38) (tshiftTy c T114) (tshiftTy c T115) (shift_etvar_TRed G9 S37 T114 (star) jm43 c G10 (weaken_shift_etvar empty H92)) (shift_etvar_TRed G9 S38 T115 (star) jm44 c G10 (weaken_shift_etvar empty H92))))
    | (QR_Abs K97 K98 S38 T115 jm45 H70 H71) => (fun (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) =>
      (QR_Abs G10 K97 K98 (tshiftTy (CS c) S38) (tshiftTy (CS c) T115) (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_TRed (etvar G9 K97) S38 T115 (weakenKind K98 (HS ty H0)) jm45 (CS c) (etvar G10 K97) (weaken_shift_etvar (etvar empty K97) H92))) (tshift_wfKind _ _ H70 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H92))) (tshift_wfKind _ _ H71 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H92)))))
    | (QR_App K97 K98 S37 S38 T114 T115 jm46 jm47) => (fun (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) =>
      (QR_App G10 K97 K98 (tshiftTy c S37) (tshiftTy c S38) (tshiftTy c T114) (tshiftTy c T115) (shift_etvar_TRed G9 S37 T114 (karr K98 K97) jm46 c G10 (weaken_shift_etvar empty H92)) (shift_etvar_TRed G9 S38 T115 K98 jm47 c G10 (weaken_shift_etvar empty H92))))
    | (QR_All K97 S38 T115 jm48 H80) => (fun (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) =>
      (QR_All G10 K97 (tshiftTy (CS c) S38) (tshiftTy (CS c) T115) (shift_etvar_TRed (etvar G9 K97) S38 T115 (star) jm48 (CS c) (etvar G10 K97) (weaken_shift_etvar (etvar empty K97) H92)) (tshift_wfKind _ _ H80 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H92)))))
    | (QR_Beta K97 K98 S37 S38 T114 T115 jm49 jm50 H83) => (fun (c : (Cutoff ty)) (G10 : Env) (H92 : (shift_etvar c G9 G10)) =>
      (TRed_cast G10 _ _ _ G10 (tshiftTy c (tapp (tabs K98 S37) S38)) (tshiftTy c (tsubstTy X0 T115 T114)) K97 eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T114 c T115)) eq_refl (QR_Beta G10 K97 K98 (tshiftTy (CS c) S37) (tshiftTy c S38) (tshiftTy (CS c) T114) (tshiftTy c T115) (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_TRed (etvar G9 K98) S37 T114 (weakenKind K97 (HS ty H0)) jm49 (CS c) (etvar G10 K98) (weaken_shift_etvar (etvar empty K98) H92))) (shift_etvar_TRed G9 S38 T115 K98 jm50 c G10 (weaken_shift_etvar empty H92)) (tshift_wfKind _ _ H83 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H92))))))
  end.
Fixpoint shift_evar_Kinding (G9 : Env) (T116 : Ty) (K101 : Kind) (jm49 : (Kinding G9 T116 K101)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H79 : (shift_evar c G9 G10)) ,
  (Kinding G10 T116 K101)) :=
  match jm49 in (Kinding _ T116 K101) return (forall (c : (Cutoff tm)) (G10 : Env) (H79 : (shift_evar c G9 G10)) ,
    (Kinding G10 T116 K101)) with
    | (K_TVar K96 X54 lk1 H64 H65) => (fun (c : (Cutoff tm)) (G10 : Env) (H79 : (shift_evar c G9 G10)) =>
      (K_TVar G10 K96 X54 (shift_evar_lookup_etvar H79 lk1) (shift_wfKind _ _ H64 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H79))) (shift_wfindex_ty _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H79)) _ H65)))
    | (K_Abs K97 K100 T115 jm43 H66 H67) => (fun (c : (Cutoff tm)) (G10 : Env) (H79 : (shift_evar c G9 G10)) =>
      (K_Abs G10 K97 K100 T115 (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Kinding (etvar G9 K97) T115 (weakenKind K100 (HS ty H0)) jm43 c (etvar G10 K97) (weaken_shift_evar (etvar empty K97) H79))) (shift_wfKind _ _ H66 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H79))) (shift_wfKind _ _ H67 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H79)))))
    | (K_App K98 K99 T114 T115 jm44 jm45) => (fun (c : (Cutoff tm)) (G10 : Env) (H79 : (shift_evar c G9 G10)) =>
      (K_App G10 K98 K99 T114 T115 (shift_evar_Kinding G9 T114 (karr K98 K99) jm44 c G10 (weaken_shift_evar empty H79)) (shift_evar_Kinding G9 T115 K98 jm45 c G10 (weaken_shift_evar empty H79))))
    | (K_Arr T114 T115 jm46 jm47) => (fun (c : (Cutoff tm)) (G10 : Env) (H79 : (shift_evar c G9 G10)) =>
      (K_Arr G10 T114 T115 (shift_evar_Kinding G9 T114 (star) jm46 c G10 (weaken_shift_evar empty H79)) (shift_evar_Kinding G9 T115 (star) jm47 c G10 (weaken_shift_evar empty H79))))
    | (K_All K97 T115 jm48 H75) => (fun (c : (Cutoff tm)) (G10 : Env) (H79 : (shift_evar c G9 G10)) =>
      (K_All G10 K97 T115 (shift_evar_Kinding (etvar G9 K97) T115 (star) jm48 c (etvar G10 K97) (weaken_shift_evar (etvar empty K97) H79)) (shift_wfKind _ _ H75 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H79)))))
  end.
Fixpoint shift_etvar_Kinding (G9 : Env) (T116 : Ty) (K101 : Kind) (jm49 : (Kinding G9 T116 K101)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H79 : (shift_etvar c G9 G10)) ,
  (Kinding G10 (tshiftTy c T116) K101)) :=
  match jm49 in (Kinding _ T116 K101) return (forall (c : (Cutoff ty)) (G10 : Env) (H79 : (shift_etvar c G9 G10)) ,
    (Kinding G10 (tshiftTy c T116) K101)) with
    | (K_TVar K96 X54 lk1 H64 H65) => (fun (c : (Cutoff ty)) (G10 : Env) (H79 : (shift_etvar c G9 G10)) =>
      (K_TVar G10 K96 (tshiftIndex c X54) (shift_etvar_lookup_etvar H79 lk1) (tshift_wfKind _ _ H64 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H79))) (tshift_wfindex_ty _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H79)) _ H65)))
    | (K_Abs K97 K100 T115 jm43 H66 H67) => (fun (c : (Cutoff ty)) (G10 : Env) (H79 : (shift_etvar c G9 G10)) =>
      (K_Abs G10 K97 K100 (tshiftTy (CS c) T115) (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_Kinding (etvar G9 K97) T115 (weakenKind K100 (HS ty H0)) jm43 (CS c) (etvar G10 K97) (weaken_shift_etvar (etvar empty K97) H79))) (tshift_wfKind _ _ H66 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H79))) (tshift_wfKind _ _ H67 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H79)))))
    | (K_App K98 K99 T114 T115 jm44 jm45) => (fun (c : (Cutoff ty)) (G10 : Env) (H79 : (shift_etvar c G9 G10)) =>
      (K_App G10 K98 K99 (tshiftTy c T114) (tshiftTy c T115) (shift_etvar_Kinding G9 T114 (karr K98 K99) jm44 c G10 (weaken_shift_etvar empty H79)) (shift_etvar_Kinding G9 T115 K98 jm45 c G10 (weaken_shift_etvar empty H79))))
    | (K_Arr T114 T115 jm46 jm47) => (fun (c : (Cutoff ty)) (G10 : Env) (H79 : (shift_etvar c G9 G10)) =>
      (K_Arr G10 (tshiftTy c T114) (tshiftTy c T115) (shift_etvar_Kinding G9 T114 (star) jm46 c G10 (weaken_shift_etvar empty H79)) (shift_etvar_Kinding G9 T115 (star) jm47 c G10 (weaken_shift_etvar empty H79))))
    | (K_All K97 T115 jm48 H75) => (fun (c : (Cutoff ty)) (G10 : Env) (H79 : (shift_etvar c G9 G10)) =>
      (K_All G10 K97 (tshiftTy (CS c) T115) (shift_etvar_Kinding (etvar G9 K97) T115 (star) jm48 (CS c) (etvar G10 K97) (weaken_shift_etvar (etvar empty K97) H79)) (tshift_wfKind _ _ H75 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H79)))))
  end.
Fixpoint shift_evar_TRedStar (G9 : Env) (T115 : Ty) (T116 : Ty) (K97 : Kind) (jm46 : (TRedStar G9 T115 T116 K97)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H73 : (shift_evar c G9 G10)) ,
  (TRedStar G10 T115 T116 K97)) :=
  match jm46 in (TRedStar _ T115 T116 K97) return (forall (c : (Cutoff tm)) (G10 : Env) (H73 : (shift_evar c G9 G10)) ,
    (TRedStar G10 T115 T116 K97)) with
    | (QRS_Nil K96 T114 jm43) => (fun (c : (Cutoff tm)) (G10 : Env) (H73 : (shift_evar c G9 G10)) =>
      (QRS_Nil G10 K96 T114 (shift_evar_Kinding G9 T114 K96 jm43 c G10 (weaken_shift_evar empty H73))))
    | (QRS_Cons K96 S37 T114 U5 jm44 jm45) => (fun (c : (Cutoff tm)) (G10 : Env) (H73 : (shift_evar c G9 G10)) =>
      (QRS_Cons G10 K96 S37 T114 U5 (shift_evar_TRedStar G9 S37 T114 K96 jm44 c G10 (weaken_shift_evar empty H73)) (shift_evar_TRed G9 T114 U5 K96 jm45 c G10 (weaken_shift_evar empty H73))))
  end.
Fixpoint shift_etvar_TRedStar (G9 : Env) (T115 : Ty) (T116 : Ty) (K97 : Kind) (jm46 : (TRedStar G9 T115 T116 K97)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H73 : (shift_etvar c G9 G10)) ,
  (TRedStar G10 (tshiftTy c T115) (tshiftTy c T116) K97)) :=
  match jm46 in (TRedStar _ T115 T116 K97) return (forall (c : (Cutoff ty)) (G10 : Env) (H73 : (shift_etvar c G9 G10)) ,
    (TRedStar G10 (tshiftTy c T115) (tshiftTy c T116) K97)) with
    | (QRS_Nil K96 T114 jm43) => (fun (c : (Cutoff ty)) (G10 : Env) (H73 : (shift_etvar c G9 G10)) =>
      (QRS_Nil G10 K96 (tshiftTy c T114) (shift_etvar_Kinding G9 T114 K96 jm43 c G10 (weaken_shift_etvar empty H73))))
    | (QRS_Cons K96 S37 T114 U5 jm44 jm45) => (fun (c : (Cutoff ty)) (G10 : Env) (H73 : (shift_etvar c G9 G10)) =>
      (QRS_Cons G10 K96 (tshiftTy c S37) (tshiftTy c T114) (tshiftTy c U5) (shift_etvar_TRedStar G9 S37 T114 K96 jm44 c G10 (weaken_shift_etvar empty H73)) (shift_etvar_TRed G9 T114 U5 K96 jm45 c G10 (weaken_shift_etvar empty H73))))
  end.
Fixpoint shift_evar_TyEq (G9 : Env) (T118 : Ty) (T119 : Ty) (K101 : Kind) (jm56 : (TyEq G9 T118 T119 K101)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H100 : (shift_evar c G9 G10)) ,
  (TyEq G10 T118 T119 K101)) :=
  match jm56 in (TyEq _ T118 T119 K101) return (forall (c : (Cutoff tm)) (G10 : Env) (H100 : (shift_evar c G9 G10)) ,
    (TyEq G10 T118 T119 K101)) with
    | (Q_Arrow S37 S38 T115 T117 jm51 jm52) => (fun (c : (Cutoff tm)) (G10 : Env) (H100 : (shift_evar c G9 G10)) =>
      (Q_Arrow G10 S37 S38 T115 T117 (shift_evar_TyEq G9 S37 T115 (star) jm51 c G10 (weaken_shift_evar empty H100)) (shift_evar_TyEq G9 S38 T117 (star) jm52 c G10 (weaken_shift_evar empty H100))))
    | (Q_Abs K97 K100 S38 T117 jm53 H68 H69) => (fun (c : (Cutoff tm)) (G10 : Env) (H100 : (shift_evar c G9 G10)) =>
      (Q_Abs G10 K97 K100 S38 T117 (TyEq_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_evar_TyEq (etvar G9 K97) S38 T117 (weakenKind K100 (HS ty H0)) jm53 c (etvar G10 K97) (weaken_shift_evar (etvar empty K97) H100))) (shift_wfKind _ _ H68 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H100))) (shift_wfKind _ _ H69 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H100)))))
    | (Q_App K97 K100 S37 S38 T115 T117 jm54 jm55) => (fun (c : (Cutoff tm)) (G10 : Env) (H100 : (shift_evar c G9 G10)) =>
      (Q_App G10 K97 K100 S37 S38 T115 T117 (shift_evar_TyEq G9 S37 T115 (karr K97 K100) jm54 c G10 (weaken_shift_evar empty H100)) (shift_evar_TyEq G9 S38 T117 K97 jm55 c G10 (weaken_shift_evar empty H100))))
    | (Q_All K97 S38 T117 jm43 H78) => (fun (c : (Cutoff tm)) (G10 : Env) (H100 : (shift_evar c G9 G10)) =>
      (Q_All G10 K97 S38 T117 (shift_evar_TyEq (etvar G9 K97) S38 T117 (star) jm43 c (etvar G10 K97) (weaken_shift_evar (etvar empty K97) H100)) (shift_wfKind _ _ H78 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H100)))))
    | (Q_Beta K98 K99 T116 T117 jm44 jm45 H82) => (fun (c : (Cutoff tm)) (G10 : Env) (H100 : (shift_evar c G9 G10)) =>
      (Q_Beta G10 K98 K99 T116 T117 (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Kinding (etvar G9 K98) T116 (weakenKind K99 (HS ty H0)) jm44 c (etvar G10 K98) (weaken_shift_evar (etvar empty K98) H100))) (shift_evar_Kinding G9 T117 K98 jm45 c G10 (weaken_shift_evar empty H100)) (shift_wfKind _ _ H82 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H100)))))
    | (Q_Eta K97 K100 T114 jm46) => (fun (c : (Cutoff tm)) (G10 : Env) (H100 : (shift_evar c G9 G10)) =>
      (TyEq_cast G10 _ _ _ G10 (tabs K97 (tapp (weakenTy T114 (HS ty H0)) (tvar I0))) T114 (karr K97 K100) eq_refl (f_equal2 tabs eq_refl (f_equal2 tapp eq_refl eq_refl)) eq_refl eq_refl (Q_Eta G10 K97 K100 T114 (shift_evar_Kinding G9 T114 (karr K97 K100) jm46 c G10 (weaken_shift_evar empty H100)))))
    | (Q_Refl K96 T114 jm47) => (fun (c : (Cutoff tm)) (G10 : Env) (H100 : (shift_evar c G9 G10)) =>
      (Q_Refl G10 K96 T114 (shift_evar_Kinding G9 T114 K96 jm47 c G10 (weaken_shift_evar empty H100))))
    | (Q_Symm K96 T114 U5 jm48) => (fun (c : (Cutoff tm)) (G10 : Env) (H100 : (shift_evar c G9 G10)) =>
      (Q_Symm G10 K96 T114 U5 (shift_evar_TyEq G9 T114 U5 K96 jm48 c G10 (weaken_shift_evar empty H100))))
    | (Q_Trans K96 T114 U5 V1 jm49 jm50) => (fun (c : (Cutoff tm)) (G10 : Env) (H100 : (shift_evar c G9 G10)) =>
      (Q_Trans G10 K96 T114 U5 V1 (shift_evar_TyEq G9 T114 U5 K96 jm49 c G10 (weaken_shift_evar empty H100)) (shift_evar_TyEq G9 U5 V1 K96 jm50 c G10 (weaken_shift_evar empty H100))))
  end.
Fixpoint shift_etvar_TyEq (G9 : Env) (T118 : Ty) (T119 : Ty) (K101 : Kind) (jm56 : (TyEq G9 T118 T119 K101)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H100 : (shift_etvar c G9 G10)) ,
  (TyEq G10 (tshiftTy c T118) (tshiftTy c T119) K101)) :=
  match jm56 in (TyEq _ T118 T119 K101) return (forall (c : (Cutoff ty)) (G10 : Env) (H100 : (shift_etvar c G9 G10)) ,
    (TyEq G10 (tshiftTy c T118) (tshiftTy c T119) K101)) with
    | (Q_Arrow S37 S38 T115 T117 jm51 jm52) => (fun (c : (Cutoff ty)) (G10 : Env) (H100 : (shift_etvar c G9 G10)) =>
      (Q_Arrow G10 (tshiftTy c S37) (tshiftTy c S38) (tshiftTy c T115) (tshiftTy c T117) (shift_etvar_TyEq G9 S37 T115 (star) jm51 c G10 (weaken_shift_etvar empty H100)) (shift_etvar_TyEq G9 S38 T117 (star) jm52 c G10 (weaken_shift_etvar empty H100))))
    | (Q_Abs K97 K100 S38 T117 jm53 H68 H69) => (fun (c : (Cutoff ty)) (G10 : Env) (H100 : (shift_etvar c G9 G10)) =>
      (Q_Abs G10 K97 K100 (tshiftTy (CS c) S38) (tshiftTy (CS c) T117) (TyEq_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_TyEq (etvar G9 K97) S38 T117 (weakenKind K100 (HS ty H0)) jm53 (CS c) (etvar G10 K97) (weaken_shift_etvar (etvar empty K97) H100))) (tshift_wfKind _ _ H68 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H100))) (tshift_wfKind _ _ H69 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H100)))))
    | (Q_App K97 K100 S37 S38 T115 T117 jm54 jm55) => (fun (c : (Cutoff ty)) (G10 : Env) (H100 : (shift_etvar c G9 G10)) =>
      (Q_App G10 K97 K100 (tshiftTy c S37) (tshiftTy c S38) (tshiftTy c T115) (tshiftTy c T117) (shift_etvar_TyEq G9 S37 T115 (karr K97 K100) jm54 c G10 (weaken_shift_etvar empty H100)) (shift_etvar_TyEq G9 S38 T117 K97 jm55 c G10 (weaken_shift_etvar empty H100))))
    | (Q_All K97 S38 T117 jm43 H78) => (fun (c : (Cutoff ty)) (G10 : Env) (H100 : (shift_etvar c G9 G10)) =>
      (Q_All G10 K97 (tshiftTy (CS c) S38) (tshiftTy (CS c) T117) (shift_etvar_TyEq (etvar G9 K97) S38 T117 (star) jm43 (CS c) (etvar G10 K97) (weaken_shift_etvar (etvar empty K97) H100)) (tshift_wfKind _ _ H78 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H100)))))
    | (Q_Beta K98 K99 T116 T117 jm44 jm45 H82) => (fun (c : (Cutoff ty)) (G10 : Env) (H100 : (shift_etvar c G9 G10)) =>
      (TyEq_cast G10 _ _ _ G10 (tshiftTy c (tapp (tabs K98 T116) T117)) (tshiftTy c (tsubstTy X0 T117 T116)) K99 eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T116 c T117)) eq_refl (Q_Beta G10 K98 K99 (tshiftTy (CS c) T116) (tshiftTy c T117) (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_etvar_Kinding (etvar G9 K98) T116 (weakenKind K99 (HS ty H0)) jm44 (CS c) (etvar G10 K98) (weaken_shift_etvar (etvar empty K98) H100))) (shift_etvar_Kinding G9 T117 K98 jm45 c G10 (weaken_shift_etvar empty H100)) (tshift_wfKind _ _ H82 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H100))))))
    | (Q_Eta K97 K100 T114 jm46) => (fun (c : (Cutoff ty)) (G10 : Env) (H100 : (shift_etvar c G9 G10)) =>
      (TyEq_cast G10 _ _ _ G10 (tshiftTy c (tabs K97 (tapp (weakenTy T114 (HS ty H0)) (tvar I0)))) (tshiftTy c T114) (karr K97 K100) eq_refl (f_equal2 tabs eq_refl (f_equal2 tapp (weakenTy_tshiftTy (HS ty H0) c T114) eq_refl)) eq_refl eq_refl (Q_Eta G10 K97 K100 (tshiftTy c T114) (shift_etvar_Kinding G9 T114 (karr K97 K100) jm46 c G10 (weaken_shift_etvar empty H100)))))
    | (Q_Refl K96 T114 jm47) => (fun (c : (Cutoff ty)) (G10 : Env) (H100 : (shift_etvar c G9 G10)) =>
      (Q_Refl G10 K96 (tshiftTy c T114) (shift_etvar_Kinding G9 T114 K96 jm47 c G10 (weaken_shift_etvar empty H100))))
    | (Q_Symm K96 T114 U5 jm48) => (fun (c : (Cutoff ty)) (G10 : Env) (H100 : (shift_etvar c G9 G10)) =>
      (Q_Symm G10 K96 (tshiftTy c T114) (tshiftTy c U5) (shift_etvar_TyEq G9 T114 U5 K96 jm48 c G10 (weaken_shift_etvar empty H100))))
    | (Q_Trans K96 T114 U5 V1 jm49 jm50) => (fun (c : (Cutoff ty)) (G10 : Env) (H100 : (shift_etvar c G9 G10)) =>
      (Q_Trans G10 K96 (tshiftTy c T114) (tshiftTy c U5) (tshiftTy c V1) (shift_etvar_TyEq G9 T114 U5 K96 jm49 c G10 (weaken_shift_etvar empty H100)) (shift_etvar_TyEq G9 U5 V1 K96 jm50 c G10 (weaken_shift_etvar empty H100))))
  end.
Fixpoint shift_evar_Typing (G9 : Env) (t21 : Tm) (T119 : Ty) (jm52 : (Typing G9 t21 T119)) :
(forall (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) ,
  (Typing G10 (shiftTm c t21) T119)) :=
  match jm52 in (Typing _ t21 T119) return (forall (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) ,
    (Typing G10 (shiftTm c t21) T119)) with
    | (T_Var T114 y1 lk1 H64 H65) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (T_Var G10 T114 (shiftIndex c y1) (shift_evar_lookup_evar H85 lk1) (shift_wfTy _ _ H64 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H85))) (shift_wfindex_tm _ _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H85)) _ H65)))
    | (T_Abs T115 T118 t18 jm43 jm44 H67) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (T_Abs G10 T115 T118 (shiftTm (CS c) t18) (shift_evar_Kinding G9 T115 (star) jm43 c G10 (weaken_shift_evar empty H85)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (shift_evar_Typing (evar G9 T115) t18 (weakenTy T118 (HS tm H0)) jm44 (CS c) (evar G10 T115) (weaken_shift_evar (evar empty T115) H85))) (shift_wfTy _ _ H67 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H85)))))
    | (T_App T116 T117 t19 t20 jm45 jm46) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (T_App G10 T116 T117 (shiftTm c t19) (shiftTm c t20) (shift_evar_Typing G9 t19 (tarr T116 T117) jm45 c G10 (weaken_shift_evar empty H85)) (shift_evar_Typing G9 t20 T116 jm46 c G10 (weaken_shift_evar empty H85))))
    | (T_TAbs K96 T114 t18 jm47 H73) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (T_TAbs G10 K96 T114 (shiftTm c t18) (shift_evar_Typing (etvar G9 K96) t18 T114 jm47 c (etvar G10 K96) (weaken_shift_evar (etvar empty K96) H85)) (shift_wfKind _ _ H73 _ _ (weaken_shifthvl_tm H0 (shift_evar_shifthvl_tm H85)))))
    | (T_TApp K97 T117 T118 t19 jm48 jm49) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (T_TApp G10 K97 T117 T118 (shiftTm c t19) (shift_evar_Typing G9 t19 (tall K97 T117) jm48 c G10 (weaken_shift_evar empty H85)) (shift_evar_Kinding G9 T118 K97 jm49 c G10 (weaken_shift_evar empty H85))))
    | (T_Eq S37 T114 t18 jm50 jm51) => (fun (c : (Cutoff tm)) (G10 : Env) (H85 : (shift_evar c G9 G10)) =>
      (T_Eq G10 S37 T114 (shiftTm c t18) (shift_evar_Typing G9 t18 S37 jm50 c G10 (weaken_shift_evar empty H85)) (shift_evar_TyEq G9 S37 T114 (star) jm51 c G10 (weaken_shift_evar empty H85))))
  end.
Fixpoint shift_etvar_Typing (G9 : Env) (t21 : Tm) (T119 : Ty) (jm52 : (Typing G9 t21 T119)) :
(forall (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) ,
  (Typing G10 (tshiftTm c t21) (tshiftTy c T119))) :=
  match jm52 in (Typing _ t21 T119) return (forall (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) ,
    (Typing G10 (tshiftTm c t21) (tshiftTy c T119))) with
    | (T_Var T114 y1 lk1 H64 H65) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (T_Var G10 (tshiftTy c T114) y1 (shift_etvar_lookup_evar H85 lk1) (tshift_wfTy _ _ H64 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H85))) (tshift_wfindex_tm _ _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H85)) _ H65)))
    | (T_Abs T115 T118 t18 jm43 jm44 H67) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (T_Abs G10 (tshiftTy c T115) (tshiftTy c T118) (tshiftTm c t18) (shift_etvar_Kinding G9 T115 (star) jm43 c G10 (weaken_shift_etvar empty H85)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tshiftTy (HS tm H0) c T118)) (shift_etvar_Typing (evar G9 T115) t18 (weakenTy T118 (HS tm H0)) jm44 c (evar G10 (tshiftTy c T115)) (weaken_shift_etvar (evar empty T115) H85))) (tshift_wfTy _ _ H67 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H85)))))
    | (T_App T116 T117 t19 t20 jm45 jm46) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (T_App G10 (tshiftTy c T116) (tshiftTy c T117) (tshiftTm c t19) (tshiftTm c t20) (shift_etvar_Typing G9 t19 (tarr T116 T117) jm45 c G10 (weaken_shift_etvar empty H85)) (shift_etvar_Typing G9 t20 T116 jm46 c G10 (weaken_shift_etvar empty H85))))
    | (T_TAbs K96 T114 t18 jm47 H73) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (T_TAbs G10 K96 (tshiftTy (CS c) T114) (tshiftTm (CS c) t18) (shift_etvar_Typing (etvar G9 K96) t18 T114 jm47 (CS c) (etvar G10 K96) (weaken_shift_etvar (etvar empty K96) H85)) (tshift_wfKind _ _ H73 _ _ (weaken_shifthvl_ty H0 (shift_etvar_shifthvl_ty H85)))))
    | (T_TApp K97 T117 T118 t19 jm48 jm49) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (Typing_cast G10 _ _ G10 (tshiftTm c (tyapp t19 T118)) (tshiftTy c (tsubstTy X0 T118 T117)) eq_refl eq_refl (eq_sym (tshiftTy_tsubstTy0_comm T117 c T118)) (T_TApp G10 K97 (tshiftTy (CS c) T117) (tshiftTy c T118) (tshiftTm c t19) (shift_etvar_Typing G9 t19 (tall K97 T117) jm48 c G10 (weaken_shift_etvar empty H85)) (shift_etvar_Kinding G9 T118 K97 jm49 c G10 (weaken_shift_etvar empty H85)))))
    | (T_Eq S37 T114 t18 jm50 jm51) => (fun (c : (Cutoff ty)) (G10 : Env) (H85 : (shift_etvar c G9 G10)) =>
      (T_Eq G10 (tshiftTy c S37) (tshiftTy c T114) (tshiftTm c t18) (shift_etvar_Typing G9 t18 S37 jm50 c G10 (weaken_shift_etvar empty H85)) (shift_etvar_TyEq G9 S37 T114 (star) jm51 c G10 (weaken_shift_etvar empty H85))))
  end.
 Hint Resolve shift_evar_Kinding shift_etvar_Kinding shift_evar_TRed shift_etvar_TRed shift_evar_TRedStar shift_etvar_TRedStar shift_evar_TyEq shift_etvar_TyEq shift_evar_Typing shift_etvar_Typing : infra.
 Hint Resolve shift_evar_Kinding shift_etvar_Kinding shift_evar_TRed shift_etvar_TRed shift_evar_TRedStar shift_etvar_TRedStar shift_evar_TyEq shift_etvar_TyEq shift_evar_Typing shift_etvar_Typing : shift.
Fixpoint weaken_TRed (G : Env) :
(forall (G0 : Env) (T101 : Ty) (T102 : Ty) (K87 : Kind) (jm38 : (TRed G0 T101 T102 K87)) ,
  (TRed (appendEnv G0 G) (weakenTy T101 (domainEnv G)) (weakenTy T102 (domainEnv G)) (weakenKind K87 (domainEnv G)))) :=
  match G return (forall (G0 : Env) (T101 : Ty) (T102 : Ty) (K87 : Kind) (jm38 : (TRed G0 T101 T102 K87)) ,
    (TRed (appendEnv G0 G) (weakenTy T101 (domainEnv G)) (weakenTy T102 (domainEnv G)) (weakenKind K87 (domainEnv G)))) with
    | (empty) => (fun (G0 : Env) (T101 : Ty) (T102 : Ty) (K87 : Kind) (jm38 : (TRed G0 T101 T102 K87)) =>
      jm38)
    | (evar G T103) => (fun (G0 : Env) (T101 : Ty) (T102 : Ty) (K87 : Kind) (jm38 : (TRed G0 T101 T102 K87)) =>
      (shift_evar_TRed (appendEnv G0 G) (weakenTy T101 (domainEnv G)) (weakenTy T102 (domainEnv G)) (weakenKind K87 (domainEnv G)) (weaken_TRed G G0 T101 T102 K87 jm38) C0 (evar (appendEnv G0 G) T103) shift_evar_here))
    | (etvar G K88) => (fun (G0 : Env) (T101 : Ty) (T102 : Ty) (K87 : Kind) (jm38 : (TRed G0 T101 T102 K87)) =>
      (shift_etvar_TRed (appendEnv G0 G) (weakenTy T101 (domainEnv G)) (weakenTy T102 (domainEnv G)) (weakenKind K87 (domainEnv G)) (weaken_TRed G G0 T101 T102 K87 jm38) C0 (etvar (appendEnv G0 G) K88) shift_etvar_here))
  end.
Fixpoint weaken_Kinding (G1 : Env) :
(forall (G2 : Env) (T104 : Ty) (K89 : Kind) (jm39 : (Kinding G2 T104 K89)) ,
  (Kinding (appendEnv G2 G1) (weakenTy T104 (domainEnv G1)) (weakenKind K89 (domainEnv G1)))) :=
  match G1 return (forall (G2 : Env) (T104 : Ty) (K89 : Kind) (jm39 : (Kinding G2 T104 K89)) ,
    (Kinding (appendEnv G2 G1) (weakenTy T104 (domainEnv G1)) (weakenKind K89 (domainEnv G1)))) with
    | (empty) => (fun (G2 : Env) (T104 : Ty) (K89 : Kind) (jm39 : (Kinding G2 T104 K89)) =>
      jm39)
    | (evar G1 T105) => (fun (G2 : Env) (T104 : Ty) (K89 : Kind) (jm39 : (Kinding G2 T104 K89)) =>
      (shift_evar_Kinding (appendEnv G2 G1) (weakenTy T104 (domainEnv G1)) (weakenKind K89 (domainEnv G1)) (weaken_Kinding G1 G2 T104 K89 jm39) C0 (evar (appendEnv G2 G1) T105) shift_evar_here))
    | (etvar G1 K90) => (fun (G2 : Env) (T104 : Ty) (K89 : Kind) (jm39 : (Kinding G2 T104 K89)) =>
      (shift_etvar_Kinding (appendEnv G2 G1) (weakenTy T104 (domainEnv G1)) (weakenKind K89 (domainEnv G1)) (weaken_Kinding G1 G2 T104 K89 jm39) C0 (etvar (appendEnv G2 G1) K90) shift_etvar_here))
  end.
Fixpoint weaken_TRedStar (G3 : Env) :
(forall (G4 : Env) (T106 : Ty) (T107 : Ty) (K91 : Kind) (jm40 : (TRedStar G4 T106 T107 K91)) ,
  (TRedStar (appendEnv G4 G3) (weakenTy T106 (domainEnv G3)) (weakenTy T107 (domainEnv G3)) (weakenKind K91 (domainEnv G3)))) :=
  match G3 return (forall (G4 : Env) (T106 : Ty) (T107 : Ty) (K91 : Kind) (jm40 : (TRedStar G4 T106 T107 K91)) ,
    (TRedStar (appendEnv G4 G3) (weakenTy T106 (domainEnv G3)) (weakenTy T107 (domainEnv G3)) (weakenKind K91 (domainEnv G3)))) with
    | (empty) => (fun (G4 : Env) (T106 : Ty) (T107 : Ty) (K91 : Kind) (jm40 : (TRedStar G4 T106 T107 K91)) =>
      jm40)
    | (evar G3 T108) => (fun (G4 : Env) (T106 : Ty) (T107 : Ty) (K91 : Kind) (jm40 : (TRedStar G4 T106 T107 K91)) =>
      (shift_evar_TRedStar (appendEnv G4 G3) (weakenTy T106 (domainEnv G3)) (weakenTy T107 (domainEnv G3)) (weakenKind K91 (domainEnv G3)) (weaken_TRedStar G3 G4 T106 T107 K91 jm40) C0 (evar (appendEnv G4 G3) T108) shift_evar_here))
    | (etvar G3 K92) => (fun (G4 : Env) (T106 : Ty) (T107 : Ty) (K91 : Kind) (jm40 : (TRedStar G4 T106 T107 K91)) =>
      (shift_etvar_TRedStar (appendEnv G4 G3) (weakenTy T106 (domainEnv G3)) (weakenTy T107 (domainEnv G3)) (weakenKind K91 (domainEnv G3)) (weaken_TRedStar G3 G4 T106 T107 K91 jm40) C0 (etvar (appendEnv G4 G3) K92) shift_etvar_here))
  end.
Fixpoint weaken_TyEq (G5 : Env) :
(forall (G6 : Env) (T109 : Ty) (T110 : Ty) (K93 : Kind) (jm41 : (TyEq G6 T109 T110 K93)) ,
  (TyEq (appendEnv G6 G5) (weakenTy T109 (domainEnv G5)) (weakenTy T110 (domainEnv G5)) (weakenKind K93 (domainEnv G5)))) :=
  match G5 return (forall (G6 : Env) (T109 : Ty) (T110 : Ty) (K93 : Kind) (jm41 : (TyEq G6 T109 T110 K93)) ,
    (TyEq (appendEnv G6 G5) (weakenTy T109 (domainEnv G5)) (weakenTy T110 (domainEnv G5)) (weakenKind K93 (domainEnv G5)))) with
    | (empty) => (fun (G6 : Env) (T109 : Ty) (T110 : Ty) (K93 : Kind) (jm41 : (TyEq G6 T109 T110 K93)) =>
      jm41)
    | (evar G5 T111) => (fun (G6 : Env) (T109 : Ty) (T110 : Ty) (K93 : Kind) (jm41 : (TyEq G6 T109 T110 K93)) =>
      (shift_evar_TyEq (appendEnv G6 G5) (weakenTy T109 (domainEnv G5)) (weakenTy T110 (domainEnv G5)) (weakenKind K93 (domainEnv G5)) (weaken_TyEq G5 G6 T109 T110 K93 jm41) C0 (evar (appendEnv G6 G5) T111) shift_evar_here))
    | (etvar G5 K94) => (fun (G6 : Env) (T109 : Ty) (T110 : Ty) (K93 : Kind) (jm41 : (TyEq G6 T109 T110 K93)) =>
      (shift_etvar_TyEq (appendEnv G6 G5) (weakenTy T109 (domainEnv G5)) (weakenTy T110 (domainEnv G5)) (weakenKind K93 (domainEnv G5)) (weaken_TyEq G5 G6 T109 T110 K93 jm41) C0 (etvar (appendEnv G6 G5) K94) shift_etvar_here))
  end.
Fixpoint weaken_Typing (G7 : Env) :
(forall (G8 : Env) (t17 : Tm) (T112 : Ty) (jm42 : (Typing G8 t17 T112)) ,
  (Typing (appendEnv G8 G7) (weakenTm t17 (domainEnv G7)) (weakenTy T112 (domainEnv G7)))) :=
  match G7 return (forall (G8 : Env) (t17 : Tm) (T112 : Ty) (jm42 : (Typing G8 t17 T112)) ,
    (Typing (appendEnv G8 G7) (weakenTm t17 (domainEnv G7)) (weakenTy T112 (domainEnv G7)))) with
    | (empty) => (fun (G8 : Env) (t17 : Tm) (T112 : Ty) (jm42 : (Typing G8 t17 T112)) =>
      jm42)
    | (evar G7 T113) => (fun (G8 : Env) (t17 : Tm) (T112 : Ty) (jm42 : (Typing G8 t17 T112)) =>
      (shift_evar_Typing (appendEnv G8 G7) (weakenTm t17 (domainEnv G7)) (weakenTy T112 (domainEnv G7)) (weaken_Typing G7 G8 t17 T112 jm42) C0 (evar (appendEnv G8 G7) T113) shift_evar_here))
    | (etvar G7 K95) => (fun (G8 : Env) (t17 : Tm) (T112 : Ty) (jm42 : (Typing G8 t17 T112)) =>
      (shift_etvar_Typing (appendEnv G8 G7) (weakenTm t17 (domainEnv G7)) (weakenTy T112 (domainEnv G7)) (weaken_Typing G7 G8 t17 T112 jm42) C0 (etvar (appendEnv G8 G7) K95) shift_etvar_here))
  end.
Fixpoint TRed_wf_0 (G : Env) (T114 : Ty) (T115 : Ty) (K96 : Kind) (jm43 : (TRed G T114 T115 K96)) {struct jm43} :
(wfTy (domainEnv G) T114) :=
  match jm43 in (TRed _ T114 T115 K96) return (wfTy (domainEnv G) T114) with
    | (QR_Var K X lk H26 H27) => (wfTy_tvar (domainEnv G) _ H27)
    | (QR_Arrow S1 S2 T1 T2 jm27 jm28) => (wfTy_tarr (domainEnv G) (TRed_wf_0 G S1 T1 (star) jm27) (TRed_wf_0 G S2 T2 (star) jm28))
    | (QR_Abs K1 K2 S2 T2 jm29 H32 H33) => (wfTy_tabs (domainEnv G) H32 (TRed_wf_0 (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0)) jm29))
    | (QR_App K1 K2 S1 S2 T1 T2 jm30 jm31) => (wfTy_tapp (domainEnv G) (TRed_wf_0 G S1 T1 (karr K2 K1) jm30) (TRed_wf_0 G S2 T2 K2 jm31))
    | (QR_All K1 S2 T2 jm32 H42) => (wfTy_tall (domainEnv G) H42 (TRed_wf_0 (etvar G K1) S2 T2 (star) jm32))
    | (QR_Beta K1 K2 S1 S2 T1 T2 jm33 jm34 H45) => (wfTy_tapp (domainEnv G) (wfTy_tabs (domainEnv G) (TRed_wf_2 G S2 T2 K2 jm34) (TRed_wf_0 (etvar G K2) S1 T1 (weakenKind K1 (HS ty H0)) jm33)) (TRed_wf_0 G S2 T2 K2 jm34))
  end
with TRed_wf_1 (G : Env) (T114 : Ty) (T115 : Ty) (K96 : Kind) (jm44 : (TRed G T114 T115 K96)) {struct jm44} :
(wfTy (domainEnv G) T115) :=
  match jm44 in (TRed _ T114 T115 K96) return (wfTy (domainEnv G) T115) with
    | (QR_Var K X lk H26 H27) => (wfTy_tvar (domainEnv G) _ H27)
    | (QR_Arrow S1 S2 T1 T2 jm27 jm28) => (wfTy_tarr (domainEnv G) (TRed_wf_1 G S1 T1 (star) jm27) (TRed_wf_1 G S2 T2 (star) jm28))
    | (QR_Abs K1 K2 S2 T2 jm29 H32 H33) => (wfTy_tabs (domainEnv G) H32 (TRed_wf_1 (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0)) jm29))
    | (QR_App K1 K2 S1 S2 T1 T2 jm30 jm31) => (wfTy_tapp (domainEnv G) (TRed_wf_1 G S1 T1 (karr K2 K1) jm30) (TRed_wf_1 G S2 T2 K2 jm31))
    | (QR_All K1 S2 T2 jm32 H42) => (wfTy_tall (domainEnv G) H42 (TRed_wf_1 (etvar G K1) S2 T2 (star) jm32))
    | (QR_Beta K1 K2 S1 S2 T1 T2 jm33 jm34 H45) => (substhvl_ty_wfTy (TRed_wf_1 G S2 T2 K2 jm34) (HS ty (domainEnv G)) T1 (TRed_wf_1 (etvar G K2) S1 T1 (weakenKind K1 (HS ty H0)) jm33) (substhvl_ty_here (domainEnv G)))
  end
with TRed_wf_2 (G : Env) (T114 : Ty) (T115 : Ty) (K96 : Kind) (jm45 : (TRed G T114 T115 K96)) {struct jm45} :
(wfKind (domainEnv G) K96) :=
  match jm45 in (TRed _ T114 T115 K96) return (wfKind (domainEnv G) K96) with
    | (QR_Var K X lk H26 H27) => H26
    | (QR_Arrow S1 S2 T1 T2 jm27 jm28) => (wfKind_star (domainEnv G))
    | (QR_Abs K1 K2 S2 T2 jm29 H32 H33) => (wfKind_karr (domainEnv G) H32 H33)
    | (QR_App K1 K2 S1 S2 T1 T2 jm30 jm31) => (inversion_wfKind_karr_1 (domainEnv G) K2 K1 (TRed_wf_2 G S1 T1 (karr K2 K1) jm30))
    | (QR_All K1 S2 T2 jm32 H42) => (wfKind_star (domainEnv G))
    | (QR_Beta K1 K2 S1 S2 T1 T2 jm33 jm34 H45) => H45
  end.
Fixpoint Kinding_wf_0 (G : Env) (T116 : Ty) (K97 : Kind) (jm46 : (Kinding G T116 K97)) {struct jm46} :
(wfTy (domainEnv G) T116) :=
  match jm46 in (Kinding _ T116 K97) return (wfTy (domainEnv G) T116) with
    | (K_TVar K X lk1 H25 H26) => (wfTy_tvar (domainEnv G) _ H26)
    | (K_Abs K1 K2 T2 jm H27 H28) => (wfTy_tabs (domainEnv G) H27 (Kinding_wf_0 (etvar G K1) T2 (weakenKind K2 (HS ty H0)) jm))
    | (K_App K11 K12 T1 T2 jm0 jm1) => (wfTy_tapp (domainEnv G) (Kinding_wf_0 G T1 (karr K11 K12) jm0) (Kinding_wf_0 G T2 K11 jm1))
    | (K_Arr T1 T2 jm2 jm3) => (wfTy_tarr (domainEnv G) (Kinding_wf_0 G T1 (star) jm2) (Kinding_wf_0 G T2 (star) jm3))
    | (K_All K1 T2 jm4 H36) => (wfTy_tall (domainEnv G) H36 (Kinding_wf_0 (etvar G K1) T2 (star) jm4))
  end
with Kinding_wf_1 (G : Env) (T116 : Ty) (K97 : Kind) (jm47 : (Kinding G T116 K97)) {struct jm47} :
(wfKind (domainEnv G) K97) :=
  match jm47 in (Kinding _ T116 K97) return (wfKind (domainEnv G) K97) with
    | (K_TVar K X lk2 H25 H26) => H25
    | (K_Abs K1 K2 T2 jm H27 H28) => (wfKind_karr (domainEnv G) H27 H28)
    | (K_App K11 K12 T1 T2 jm0 jm1) => (inversion_wfKind_karr_1 (domainEnv G) K11 K12 (Kinding_wf_1 G T1 (karr K11 K12) jm0))
    | (K_Arr T1 T2 jm2 jm3) => (wfKind_star (domainEnv G))
    | (K_All K1 T2 jm4 H36) => (wfKind_star (domainEnv G))
  end.
Fixpoint TRedStar_wf_0 (G : Env) (T117 : Ty) (T118 : Ty) (K98 : Kind) (jm48 : (TRedStar G T117 T118 K98)) {struct jm48} :
(wfTy (domainEnv G) T117) :=
  match jm48 in (TRedStar _ T117 T118 K98) return (wfTy (domainEnv G) T117) with
    | (QRS_Nil K T jm35) => (Kinding_wf_0 G T K jm35)
    | (QRS_Cons K S1 T U jm36 jm37) => (TRedStar_wf_0 G S1 T K jm36)
  end
with TRedStar_wf_1 (G : Env) (T117 : Ty) (T118 : Ty) (K98 : Kind) (jm49 : (TRedStar G T117 T118 K98)) {struct jm49} :
(wfTy (domainEnv G) T118) :=
  match jm49 in (TRedStar _ T117 T118 K98) return (wfTy (domainEnv G) T118) with
    | (QRS_Nil K T jm35) => (Kinding_wf_0 G T K jm35)
    | (QRS_Cons K S1 T U jm36 jm37) => (TRed_wf_1 G T U K jm37)
  end
with TRedStar_wf_2 (G : Env) (T117 : Ty) (T118 : Ty) (K98 : Kind) (jm50 : (TRedStar G T117 T118 K98)) {struct jm50} :
(wfKind (domainEnv G) K98) :=
  match jm50 in (TRedStar _ T117 T118 K98) return (wfKind (domainEnv G) K98) with
    | (QRS_Nil K T jm35) => (Kinding_wf_1 G T K jm35)
    | (QRS_Cons K S1 T U jm36 jm37) => (TRed_wf_2 G T U K jm37)
  end.
Fixpoint TyEq_wf_0 (G : Env) (T119 : Ty) (T120 : Ty) (K99 : Kind) (jm51 : (TyEq G T119 T120 K99)) {struct jm51} :
(wfTy (domainEnv G) T119) :=
  match jm51 in (TyEq _ T119 T120 K99) return (wfTy (domainEnv G) T119) with
    | (Q_Arrow S1 S2 T1 T2 jm5 jm6) => (wfTy_tarr (domainEnv G) (TyEq_wf_0 G S1 T1 (star) jm5) (TyEq_wf_0 G S2 T2 (star) jm6))
    | (Q_Abs K1 K2 S2 T2 jm7 H30 H31) => (wfTy_tabs (domainEnv G) H30 (TyEq_wf_0 (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0)) jm7))
    | (Q_App K1 K2 S1 S2 T1 T2 jm8 jm9) => (wfTy_tapp (domainEnv G) (TyEq_wf_0 G S1 T1 (karr K1 K2) jm8) (TyEq_wf_0 G S2 T2 K1 jm9))
    | (Q_All K1 S2 T2 jm10 H40) => (wfTy_tall (domainEnv G) H40 (TyEq_wf_0 (etvar G K1) S2 T2 (star) jm10))
    | (Q_Beta K11 K12 T12 T2 jm11 jm12 H44) => (wfTy_tapp (domainEnv G) (wfTy_tabs (domainEnv G) (Kinding_wf_1 G T2 K11 jm12) (Kinding_wf_0 (etvar G K11) T12 (weakenKind K12 (HS ty H0)) jm11)) (Kinding_wf_0 G T2 K11 jm12))
    | (Q_Eta K1 K2 T jm13) => (wfTy_tabs (domainEnv G) (inversion_wfKind_karr_0 (domainEnv G) K1 K2 (Kinding_wf_1 G T (karr K1 K2) jm13)) (wfTy_tapp (HS ty (domainEnv G)) (weaken_wfTy (HS ty H0) (domainEnv G) T (Kinding_wf_0 G T (karr K1 K2) jm13)) (wfTy_tvar (HS ty (domainEnv G)) I0 I)))
    | (Q_Refl K T jm14) => (Kinding_wf_0 G T K jm14)
    | (Q_Symm K T U jm15) => (TyEq_wf_1 G T U K jm15)
    | (Q_Trans K T U V jm16 jm17) => (TyEq_wf_0 G T U K jm16)
  end
with TyEq_wf_1 (G : Env) (T119 : Ty) (T120 : Ty) (K99 : Kind) (jm52 : (TyEq G T119 T120 K99)) {struct jm52} :
(wfTy (domainEnv G) T120) :=
  match jm52 in (TyEq _ T119 T120 K99) return (wfTy (domainEnv G) T120) with
    | (Q_Arrow S1 S2 T1 T2 jm5 jm6) => (wfTy_tarr (domainEnv G) (TyEq_wf_1 G S1 T1 (star) jm5) (TyEq_wf_1 G S2 T2 (star) jm6))
    | (Q_Abs K1 K2 S2 T2 jm7 H30 H31) => (wfTy_tabs (domainEnv G) H30 (TyEq_wf_1 (etvar G K1) S2 T2 (weakenKind K2 (HS ty H0)) jm7))
    | (Q_App K1 K2 S1 S2 T1 T2 jm8 jm9) => (wfTy_tapp (domainEnv G) (TyEq_wf_1 G S1 T1 (karr K1 K2) jm8) (TyEq_wf_1 G S2 T2 K1 jm9))
    | (Q_All K1 S2 T2 jm10 H40) => (wfTy_tall (domainEnv G) H40 (TyEq_wf_1 (etvar G K1) S2 T2 (star) jm10))
    | (Q_Beta K11 K12 T12 T2 jm11 jm12 H44) => (substhvl_ty_wfTy (Kinding_wf_0 G T2 K11 jm12) (HS ty (domainEnv G)) T12 (Kinding_wf_0 (etvar G K11) T12 (weakenKind K12 (HS ty H0)) jm11) (substhvl_ty_here (domainEnv G)))
    | (Q_Eta K1 K2 T jm13) => (Kinding_wf_0 G T (karr K1 K2) jm13)
    | (Q_Refl K T jm14) => (Kinding_wf_0 G T K jm14)
    | (Q_Symm K T U jm15) => (TyEq_wf_0 G T U K jm15)
    | (Q_Trans K T U V jm16 jm17) => (TyEq_wf_1 G U V K jm17)
  end
with TyEq_wf_2 (G : Env) (T119 : Ty) (T120 : Ty) (K99 : Kind) (jm53 : (TyEq G T119 T120 K99)) {struct jm53} :
(wfKind (domainEnv G) K99) :=
  match jm53 in (TyEq _ T119 T120 K99) return (wfKind (domainEnv G) K99) with
    | (Q_Arrow S1 S2 T1 T2 jm5 jm6) => (wfKind_star (domainEnv G))
    | (Q_Abs K1 K2 S2 T2 jm7 H30 H31) => (wfKind_karr (domainEnv G) H30 H31)
    | (Q_App K1 K2 S1 S2 T1 T2 jm8 jm9) => (inversion_wfKind_karr_1 (domainEnv G) K1 K2 (TyEq_wf_2 G S1 T1 (karr K1 K2) jm8))
    | (Q_All K1 S2 T2 jm10 H40) => (wfKind_star (domainEnv G))
    | (Q_Beta K11 K12 T12 T2 jm11 jm12 H44) => H44
    | (Q_Eta K1 K2 T jm13) => (wfKind_karr (domainEnv G) (inversion_wfKind_karr_0 (domainEnv G) K1 K2 (Kinding_wf_1 G T (karr K1 K2) jm13)) (inversion_wfKind_karr_1 (domainEnv G) K1 K2 (Kinding_wf_1 G T (karr K1 K2) jm13)))
    | (Q_Refl K T jm14) => (Kinding_wf_1 G T K jm14)
    | (Q_Symm K T U jm15) => (TyEq_wf_2 G T U K jm15)
    | (Q_Trans K T U V jm16 jm17) => (TyEq_wf_2 G U V K jm17)
  end.
Fixpoint Typing_wf_0 (G : Env) (t18 : Tm) (T121 : Ty) (jm54 : (Typing G t18 T121)) {struct jm54} :
(wfTm (domainEnv G) t18) :=
  match jm54 in (Typing _ t18 T121) return (wfTm (domainEnv G) t18) with
    | (T_Var T y lk3 H25 H26) => (wfTm_var (domainEnv G) _ H26)
    | (T_Abs T1 T2 t jm18 jm19 H28) => (wfTm_abs (domainEnv G) (Kinding_wf_0 G T1 (star) jm18) (Typing_wf_0 (evar G T1) t (weakenTy T2 (HS tm H0)) jm19))
    | (T_App T11 T12 t1 t2 jm20 jm21) => (wfTm_app (domainEnv G) (Typing_wf_0 G t1 (tarr T11 T12) jm20) (Typing_wf_0 G t2 T11 jm21))
    | (T_TAbs K T t jm22 H34) => (wfTm_tyabs (domainEnv G) H34 (Typing_wf_0 (etvar G K) t T jm22))
    | (T_TApp K11 T12 T2 t1 jm23 jm24) => (wfTm_tyapp (domainEnv G) (Typing_wf_0 G t1 (tall K11 T12) jm23) (Kinding_wf_0 G T2 K11 jm24))
    | (T_Eq S1 T t jm25 jm26) => (Typing_wf_0 G t S1 jm25)
  end
with Typing_wf_1 (G : Env) (t18 : Tm) (T121 : Ty) (jm55 : (Typing G t18 T121)) {struct jm55} :
(wfTy (domainEnv G) T121) :=
  match jm55 in (Typing _ t18 T121) return (wfTy (domainEnv G) T121) with
    | (T_Var T y lk4 H25 H26) => H25
    | (T_Abs T1 T2 t jm18 jm19 H28) => (wfTy_tarr (domainEnv G) (Kinding_wf_0 G T1 (star) jm18) H28)
    | (T_App T11 T12 t1 t2 jm20 jm21) => (inversion_wfTy_tarr_1 (domainEnv G) T11 T12 (Typing_wf_1 G t1 (tarr T11 T12) jm20))
    | (T_TAbs K T t jm22 H34) => (wfTy_tall (domainEnv G) H34 (Typing_wf_1 (etvar G K) t T jm22))
    | (T_TApp K11 T12 T2 t1 jm23 jm24) => (substhvl_ty_wfTy (Kinding_wf_0 G T2 K11 jm24) (HS ty (domainEnv G)) T12 (inversion_wfTy_tall_2 (domainEnv G) K11 T12 (Typing_wf_1 G t1 (tall K11 T12) jm23)) (substhvl_ty_here (domainEnv G)))
    | (T_Eq S1 T t jm25 jm26) => (TyEq_wf_1 G S1 T (star) jm26)
  end.
 Hint Extern 8 => match goal with
  | H77 : (TRed _ _ _ _) |- _ => pose proof ((TRed_wf_0 _ _ _ _ H77)); pose proof ((TRed_wf_1 _ _ _ _ H77)); pose proof ((TRed_wf_2 _ _ _ _ H77)); clear H77
end : wf.
 Hint Extern 8 => match goal with
  | H78 : (Kinding _ _ _) |- _ => pose proof ((Kinding_wf_0 _ _ _ H78)); pose proof ((Kinding_wf_1 _ _ _ H78)); clear H78
end : wf.
 Hint Extern 8 => match goal with
  | H79 : (TRedStar _ _ _ _) |- _ => pose proof ((TRedStar_wf_0 _ _ _ _ H79)); pose proof ((TRedStar_wf_1 _ _ _ _ H79)); pose proof ((TRedStar_wf_2 _ _ _ _ H79)); clear H79
end : wf.
 Hint Extern 8 => match goal with
  | H80 : (TyEq _ _ _ _) |- _ => pose proof ((TyEq_wf_0 _ _ _ _ H80)); pose proof ((TyEq_wf_1 _ _ _ _ H80)); pose proof ((TyEq_wf_2 _ _ _ _ H80)); clear H80
end : wf.
 Hint Extern 8 => match goal with
  | H81 : (Typing _ _ _) |- _ => pose proof ((Typing_wf_0 _ _ _ H81)); pose proof ((Typing_wf_1 _ _ _ H81)); clear H81
end : wf.
Lemma subst_evar_lookup_evar (G9 : Env) (s4 : Tm) (T122 : Ty) (jm56 : (Typing G9 s4 T122)) :
  (forall (d : (Trace tm)) (G10 : Env) (G12 : Env) (sub : (subst_evar G9 T122 s4 d G10 G12)) (x11 : (Index tm)) (T123 : Ty) ,
    (lookup_evar G10 x11 T123) -> (Typing G12 (substIndex d s4 x11) T123)).
Proof.
  needleGenericSubstEnvLookupHom (T_Var).
Qed.
Lemma subst_etvar_lookup_etvar (G9 : Env) (S37 : Ty) (K100 : Kind) (jm56 : (Kinding G9 S37 K100)) :
  (forall (d : (Trace ty)) (G10 : Env) (G12 : Env) (sub : (subst_etvar G9 K100 S37 d G10 G12)) (X54 : (Index ty)) (K101 : Kind) ,
    (lookup_etvar G10 X54 K101) -> (Kinding G12 (tsubstIndex d S37 X54) K101)).
Proof.
  needleGenericSubstEnvLookupHom (K_TVar).
Qed.
Class Obligation_Env_reg_TRed : Prop := { Env_reg_QR_Var (G : Env) (K : Kind) (S37 : Ty) (jm56 : (Kinding G S37 K)) (H26 : (wfKind (domainEnv G) K)) (H82 : (wfTy (domainEnv G) S37)) : (TRed G (weakenTy S37 H0) (weakenTy S37 H0) K) }.
Context {obligation_Env_reg_TRed : Obligation_Env_reg_TRed} .
Fixpoint subst_evar_TRed (G10 : Env) (s4 : Tm) (T122 : Ty) (jm65 : (Typing G10 s4 T122)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm66 : (TRed G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T122 s4 d G9 G11)) ,
  (TRed G11 T1 T2 K)) :=
  match jm66 in (TRed _ T1 T2 K) return (forall (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T122 s4 d G9 G11)) ,
    (TRed G11 T1 T2 K)) with
    | (QR_Var K100 X54 lk5 H84 H85) => (fun (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T122 s4 d G9 G11)) =>
      (QR_Var G11 K100 X54 (subst_evar_lookup_etvar T122 H109 K100 lk5) (substhvl_tm_wfKind _ _ H84 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H109))) (substhvl_tm_wfindex_ty (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H109)) H85)))
    | (QR_Arrow S38 S39 T123 T124 jm57 jm58) => (fun (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T122 s4 d G9 G11)) =>
      (QR_Arrow G11 S38 S39 T123 T124 (subst_evar_TRed G10 s4 T122 jm65 G9 S38 T123 (star) jm57 G11 d (weaken_subst_evar _ empty H109)) (subst_evar_TRed G10 s4 T122 jm65 G9 S39 T124 (star) jm58 G11 d (weaken_subst_evar _ empty H109))))
    | (QR_Abs K101 K102 S39 T124 jm59 H90 H91) => (fun (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T122 s4 d G9 G11)) =>
      (QR_Abs G11 K101 K102 S39 T124 (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_evar_TRed G10 s4 T122 jm65 (etvar G9 K101) S39 T124 (weakenKind K102 (HS ty H0)) jm59 (appendEnv G11 (etvar empty K101)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K101) H109))) (substhvl_tm_wfKind _ _ H90 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H109))) (substhvl_tm_wfKind _ _ H91 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H109)))))
    | (QR_App K101 K102 S38 S39 T123 T124 jm60 jm61) => (fun (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T122 s4 d G9 G11)) =>
      (QR_App G11 K101 K102 S38 S39 T123 T124 (subst_evar_TRed G10 s4 T122 jm65 G9 S38 T123 (karr K102 K101) jm60 G11 d (weaken_subst_evar _ empty H109)) (subst_evar_TRed G10 s4 T122 jm65 G9 S39 T124 K102 jm61 G11 d (weaken_subst_evar _ empty H109))))
    | (QR_All K101 S39 T124 jm62 H100) => (fun (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T122 s4 d G9 G11)) =>
      (QR_All G11 K101 S39 T124 (subst_evar_TRed G10 s4 T122 jm65 (etvar G9 K101) S39 T124 (star) jm62 (appendEnv G11 (etvar empty K101)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K101) H109)) (substhvl_tm_wfKind _ _ H100 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H109)))))
    | (QR_Beta K101 K102 S38 S39 T123 T124 jm63 jm64 H103) => (fun (G11 : Env) (d : (Trace tm)) (H109 : (subst_evar G10 T122 s4 d G9 G11)) =>
      (QR_Beta G11 K101 K102 S38 S39 T123 T124 (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_evar_TRed G10 s4 T122 jm65 (etvar G9 K102) S38 T123 (weakenKind K101 (HS ty H0)) jm63 (appendEnv G11 (etvar empty K102)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K102) H109))) (subst_evar_TRed G10 s4 T122 jm65 G9 S39 T124 K102 jm64 G11 d (weaken_subst_evar _ empty H109)) (substhvl_tm_wfKind _ _ H103 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H109)))))
  end.
Fixpoint subst_etvar_TRed (G10 : Env) (S40 : Ty) (K100 : Kind) (jm65 : (Kinding G10 S40 K100)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm66 : (TRed G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K100 S40 d G9 G11)) ,
  (TRed G11 (tsubstTy d S40 T1) (tsubstTy d S40 T2) K)) :=
  match jm66 in (TRed _ T1 T2 K) return (forall (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K100 S40 d G9 G11)) ,
    (TRed G11 (tsubstTy d S40 T1) (tsubstTy d S40 T2) K)) with
    | (QR_Var K101 X54 lk5 H85 H86) => (fun (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K100 S40 d G9 G11)) =>
      (Env_reg_QR_Var G11 K101 _ (subst_etvar_lookup_etvar G10 S40 K100 jm65 d _ _ H110 X54 K101 lk5) (substhvl_ty_wfKind _ _ H85 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H110))) (substhvl_ty_wfindex_ty (Kinding_wf_0 G10 S40 K100 jm65) (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H110)) H86)))
    | (QR_Arrow S38 S39 T123 T124 jm57 jm58) => (fun (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K100 S40 d G9 G11)) =>
      (QR_Arrow G11 (tsubstTy (weakenTrace d H0) S40 S38) (tsubstTy (weakenTrace d H0) S40 S39) (tsubstTy (weakenTrace d H0) S40 T123) (tsubstTy (weakenTrace d H0) S40 T124) (subst_etvar_TRed G10 S40 K100 jm65 G9 S38 T123 (star) jm57 G11 d (weaken_subst_etvar _ empty H110)) (subst_etvar_TRed G10 S40 K100 jm65 G9 S39 T124 (star) jm58 G11 d (weaken_subst_etvar _ empty H110))))
    | (QR_Abs K102 K103 S39 T124 jm59 H91 H92) => (fun (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K100 S40 d G9 G11)) =>
      (QR_Abs G11 K102 K103 (tsubstTy (weakenTrace d (HS ty H0)) S40 S39) (tsubstTy (weakenTrace d (HS ty H0)) S40 T124) (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_TRed G10 S40 K100 jm65 (etvar G9 K102) S39 T124 (weakenKind K103 (HS ty H0)) jm59 (appendEnv G11 (tsubstEnv d S40 (etvar empty K102))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K102) H110))) (substhvl_ty_wfKind _ _ H91 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H110))) (substhvl_ty_wfKind _ _ H92 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H110)))))
    | (QR_App K102 K103 S38 S39 T123 T124 jm60 jm61) => (fun (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K100 S40 d G9 G11)) =>
      (QR_App G11 K102 K103 (tsubstTy (weakenTrace d H0) S40 S38) (tsubstTy (weakenTrace d H0) S40 S39) (tsubstTy (weakenTrace d H0) S40 T123) (tsubstTy (weakenTrace d H0) S40 T124) (subst_etvar_TRed G10 S40 K100 jm65 G9 S38 T123 (karr K103 K102) jm60 G11 d (weaken_subst_etvar _ empty H110)) (subst_etvar_TRed G10 S40 K100 jm65 G9 S39 T124 K103 jm61 G11 d (weaken_subst_etvar _ empty H110))))
    | (QR_All K102 S39 T124 jm62 H101) => (fun (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K100 S40 d G9 G11)) =>
      (QR_All G11 K102 (tsubstTy (weakenTrace d (HS ty H0)) S40 S39) (tsubstTy (weakenTrace d (HS ty H0)) S40 T124) (subst_etvar_TRed G10 S40 K100 jm65 (etvar G9 K102) S39 T124 (star) jm62 (appendEnv G11 (tsubstEnv d S40 (etvar empty K102))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K102) H110)) (substhvl_ty_wfKind _ _ H101 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H110)))))
    | (QR_Beta K102 K103 S38 S39 T123 T124 jm63 jm64 H104) => (fun (G11 : Env) (d : (Trace ty)) (H110 : (subst_etvar G10 K100 S40 d G9 G11)) =>
      (TRed_cast G11 _ _ _ G11 (tsubstTy d S40 (tapp (tabs K103 S38) S39)) (tsubstTy d S40 (tsubstTy X0 T124 T123)) K102 eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T123 d S40 T124)) eq_refl (QR_Beta G11 K102 K103 (tsubstTy (weakenTrace d (HS ty H0)) S40 S38) (tsubstTy (weakenTrace d H0) S40 S39) (tsubstTy (weakenTrace d (HS ty H0)) S40 T123) (tsubstTy (weakenTrace d H0) S40 T124) (TRed_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_TRed G10 S40 K100 jm65 (etvar G9 K103) S38 T123 (weakenKind K102 (HS ty H0)) jm63 (appendEnv G11 (tsubstEnv d S40 (etvar empty K103))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K103) H110))) (subst_etvar_TRed G10 S40 K100 jm65 G9 S39 T124 K103 jm64 G11 d (weaken_subst_etvar _ empty H110)) (substhvl_ty_wfKind _ _ H104 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H110))))))
  end.
Fixpoint subst_evar_Kinding (G10 : Env) (s4 : Tm) (T123 : Ty) (jm63 : (Typing G10 s4 T123)) (G9 : Env) (T : Ty) (K : Kind) (jm64 : (Kinding G9 T K)) :
(forall (G11 : Env) (d : (Trace tm)) (H99 : (subst_evar G10 T123 s4 d G9 G11)) ,
  (Kinding G11 T K)) :=
  match jm64 in (Kinding _ T K) return (forall (G11 : Env) (d : (Trace tm)) (H99 : (subst_evar G10 T123 s4 d G9 G11)) ,
    (Kinding G11 T K)) with
    | (K_TVar K101 X54 lk5 H86 H87) => (fun (G11 : Env) (d : (Trace tm)) (H99 : (subst_evar G10 T123 s4 d G9 G11)) =>
      (K_TVar G11 K101 X54 (subst_evar_lookup_etvar T123 H99 K101 lk5) (substhvl_tm_wfKind _ _ H86 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H99))) (substhvl_tm_wfindex_ty (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H99)) H87)))
    | (K_Abs K102 K105 T125 jm57 H88 H89) => (fun (G11 : Env) (d : (Trace tm)) (H99 : (subst_evar G10 T123 s4 d G9 G11)) =>
      (K_Abs G11 K102 K105 T125 (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Kinding G10 s4 T123 jm63 (etvar G9 K102) T125 (weakenKind K105 (HS ty H0)) jm57 (appendEnv G11 (etvar empty K102)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K102) H99))) (substhvl_tm_wfKind _ _ H88 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H99))) (substhvl_tm_wfKind _ _ H89 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H99)))))
    | (K_App K103 K104 T124 T125 jm58 jm59) => (fun (G11 : Env) (d : (Trace tm)) (H99 : (subst_evar G10 T123 s4 d G9 G11)) =>
      (K_App G11 K103 K104 T124 T125 (subst_evar_Kinding G10 s4 T123 jm63 G9 T124 (karr K103 K104) jm58 G11 d (weaken_subst_evar _ empty H99)) (subst_evar_Kinding G10 s4 T123 jm63 G9 T125 K103 jm59 G11 d (weaken_subst_evar _ empty H99))))
    | (K_Arr T124 T125 jm60 jm61) => (fun (G11 : Env) (d : (Trace tm)) (H99 : (subst_evar G10 T123 s4 d G9 G11)) =>
      (K_Arr G11 T124 T125 (subst_evar_Kinding G10 s4 T123 jm63 G9 T124 (star) jm60 G11 d (weaken_subst_evar _ empty H99)) (subst_evar_Kinding G10 s4 T123 jm63 G9 T125 (star) jm61 G11 d (weaken_subst_evar _ empty H99))))
    | (K_All K102 T125 jm62 H97) => (fun (G11 : Env) (d : (Trace tm)) (H99 : (subst_evar G10 T123 s4 d G9 G11)) =>
      (K_All G11 K102 T125 (subst_evar_Kinding G10 s4 T123 jm63 (etvar G9 K102) T125 (star) jm62 (appendEnv G11 (etvar empty K102)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K102) H99)) (substhvl_tm_wfKind _ _ H97 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H99)))))
  end.
Fixpoint subst_etvar_Kinding (G10 : Env) (S38 : Ty) (K101 : Kind) (jm63 : (Kinding G10 S38 K101)) (G9 : Env) (T : Ty) (K : Kind) (jm64 : (Kinding G9 T K)) :
(forall (G11 : Env) (d : (Trace ty)) (H100 : (subst_etvar G10 K101 S38 d G9 G11)) ,
  (Kinding G11 (tsubstTy d S38 T) K)) :=
  match jm64 in (Kinding _ T K) return (forall (G11 : Env) (d : (Trace ty)) (H100 : (subst_etvar G10 K101 S38 d G9 G11)) ,
    (Kinding G11 (tsubstTy d S38 T) K)) with
    | (K_TVar K102 X54 lk5 H87 H88) => (fun (G11 : Env) (d : (Trace ty)) (H100 : (subst_etvar G10 K101 S38 d G9 G11)) =>
      (subst_etvar_lookup_etvar G10 S38 K101 jm63 d G9 G11 H100 X54 K102 lk5))
    | (K_Abs K103 K106 T125 jm57 H89 H90) => (fun (G11 : Env) (d : (Trace ty)) (H100 : (subst_etvar G10 K101 S38 d G9 G11)) =>
      (K_Abs G11 K103 K106 (tsubstTy (weakenTrace d (HS ty H0)) S38 T125) (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_Kinding G10 S38 K101 jm63 (etvar G9 K103) T125 (weakenKind K106 (HS ty H0)) jm57 (appendEnv G11 (tsubstEnv d S38 (etvar empty K103))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K103) H100))) (substhvl_ty_wfKind _ _ H89 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H100))) (substhvl_ty_wfKind _ _ H90 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H100)))))
    | (K_App K104 K105 T124 T125 jm58 jm59) => (fun (G11 : Env) (d : (Trace ty)) (H100 : (subst_etvar G10 K101 S38 d G9 G11)) =>
      (K_App G11 K104 K105 (tsubstTy (weakenTrace d H0) S38 T124) (tsubstTy (weakenTrace d H0) S38 T125) (subst_etvar_Kinding G10 S38 K101 jm63 G9 T124 (karr K104 K105) jm58 G11 d (weaken_subst_etvar _ empty H100)) (subst_etvar_Kinding G10 S38 K101 jm63 G9 T125 K104 jm59 G11 d (weaken_subst_etvar _ empty H100))))
    | (K_Arr T124 T125 jm60 jm61) => (fun (G11 : Env) (d : (Trace ty)) (H100 : (subst_etvar G10 K101 S38 d G9 G11)) =>
      (K_Arr G11 (tsubstTy (weakenTrace d H0) S38 T124) (tsubstTy (weakenTrace d H0) S38 T125) (subst_etvar_Kinding G10 S38 K101 jm63 G9 T124 (star) jm60 G11 d (weaken_subst_etvar _ empty H100)) (subst_etvar_Kinding G10 S38 K101 jm63 G9 T125 (star) jm61 G11 d (weaken_subst_etvar _ empty H100))))
    | (K_All K103 T125 jm62 H98) => (fun (G11 : Env) (d : (Trace ty)) (H100 : (subst_etvar G10 K101 S38 d G9 G11)) =>
      (K_All G11 K103 (tsubstTy (weakenTrace d (HS ty H0)) S38 T125) (subst_etvar_Kinding G10 S38 K101 jm63 (etvar G9 K103) T125 (star) jm62 (appendEnv G11 (tsubstEnv d S38 (etvar empty K103))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K103) H100)) (substhvl_ty_wfKind _ _ H98 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H100)))))
  end.
Fixpoint subst_evar_TRedStar (G10 : Env) (s4 : Tm) (T124 : Ty) (jm60 : (Typing G10 s4 T124)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm61 : (TRedStar G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace tm)) (H94 : (subst_evar G10 T124 s4 d G9 G11)) ,
  (TRedStar G11 T1 T2 K)) :=
  match jm61 in (TRedStar _ T1 T2 K) return (forall (G11 : Env) (d : (Trace tm)) (H94 : (subst_evar G10 T124 s4 d G9 G11)) ,
    (TRedStar G11 T1 T2 K)) with
    | (QRS_Nil K102 T125 jm57) => (fun (G11 : Env) (d : (Trace tm)) (H94 : (subst_evar G10 T124 s4 d G9 G11)) =>
      (QRS_Nil G11 K102 T125 (subst_evar_Kinding G10 s4 T124 jm60 G9 T125 K102 jm57 G11 d (weaken_subst_evar _ empty H94))))
    | (QRS_Cons K102 S38 T125 U5 jm58 jm59) => (fun (G11 : Env) (d : (Trace tm)) (H94 : (subst_evar G10 T124 s4 d G9 G11)) =>
      (QRS_Cons G11 K102 S38 T125 U5 (subst_evar_TRedStar G10 s4 T124 jm60 G9 S38 T125 K102 jm58 G11 d (weaken_subst_evar _ empty H94)) (subst_evar_TRed G10 s4 T124 jm60 G9 T125 U5 K102 jm59 G11 d (weaken_subst_evar _ empty H94))))
  end.
Fixpoint subst_etvar_TRedStar (G10 : Env) (S39 : Ty) (K102 : Kind) (jm60 : (Kinding G10 S39 K102)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm61 : (TRedStar G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace ty)) (H95 : (subst_etvar G10 K102 S39 d G9 G11)) ,
  (TRedStar G11 (tsubstTy d S39 T1) (tsubstTy d S39 T2) K)) :=
  match jm61 in (TRedStar _ T1 T2 K) return (forall (G11 : Env) (d : (Trace ty)) (H95 : (subst_etvar G10 K102 S39 d G9 G11)) ,
    (TRedStar G11 (tsubstTy d S39 T1) (tsubstTy d S39 T2) K)) with
    | (QRS_Nil K103 T125 jm57) => (fun (G11 : Env) (d : (Trace ty)) (H95 : (subst_etvar G10 K102 S39 d G9 G11)) =>
      (QRS_Nil G11 K103 (tsubstTy (weakenTrace d H0) S39 T125) (subst_etvar_Kinding G10 S39 K102 jm60 G9 T125 K103 jm57 G11 d (weaken_subst_etvar _ empty H95))))
    | (QRS_Cons K103 S38 T125 U5 jm58 jm59) => (fun (G11 : Env) (d : (Trace ty)) (H95 : (subst_etvar G10 K102 S39 d G9 G11)) =>
      (QRS_Cons G11 K103 (tsubstTy (weakenTrace d H0) S39 S38) (tsubstTy (weakenTrace d H0) S39 T125) (tsubstTy (weakenTrace d H0) S39 U5) (subst_etvar_TRedStar G10 S39 K102 jm60 G9 S38 T125 K103 jm58 G11 d (weaken_subst_etvar _ empty H95)) (subst_etvar_TRed G10 S39 K102 jm60 G9 T125 U5 K103 jm59 G11 d (weaken_subst_etvar _ empty H95))))
  end.
Fixpoint subst_evar_TyEq (G10 : Env) (s4 : Tm) (T125 : Ty) (jm70 : (Typing G10 s4 T125)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm71 : (TyEq G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace tm)) (H123 : (subst_evar G10 T125 s4 d G9 G11)) ,
  (TyEq G11 T1 T2 K)) :=
  match jm71 in (TyEq _ T1 T2 K) return (forall (G11 : Env) (d : (Trace tm)) (H123 : (subst_evar G10 T125 s4 d G9 G11)) ,
    (TyEq G11 T1 T2 K)) with
    | (Q_Arrow S38 S39 T127 T129 jm65 jm66) => (fun (G11 : Env) (d : (Trace tm)) (H123 : (subst_evar G10 T125 s4 d G9 G11)) =>
      (Q_Arrow G11 S38 S39 T127 T129 (subst_evar_TyEq G10 s4 T125 jm70 G9 S38 T127 (star) jm65 G11 d (weaken_subst_evar _ empty H123)) (subst_evar_TyEq G10 s4 T125 jm70 G9 S39 T129 (star) jm66 G11 d (weaken_subst_evar _ empty H123))))
    | (Q_Abs K104 K107 S39 T129 jm67 H94 H95) => (fun (G11 : Env) (d : (Trace tm)) (H123 : (subst_evar G10 T125 s4 d G9 G11)) =>
      (Q_Abs G11 K104 K107 S39 T129 (TyEq_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_evar_TyEq G10 s4 T125 jm70 (etvar G9 K104) S39 T129 (weakenKind K107 (HS ty H0)) jm67 (appendEnv G11 (etvar empty K104)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K104) H123))) (substhvl_tm_wfKind _ _ H94 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H123))) (substhvl_tm_wfKind _ _ H95 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H123)))))
    | (Q_App K104 K107 S38 S39 T127 T129 jm68 jm69) => (fun (G11 : Env) (d : (Trace tm)) (H123 : (subst_evar G10 T125 s4 d G9 G11)) =>
      (Q_App G11 K104 K107 S38 S39 T127 T129 (subst_evar_TyEq G10 s4 T125 jm70 G9 S38 T127 (karr K104 K107) jm68 G11 d (weaken_subst_evar _ empty H123)) (subst_evar_TyEq G10 s4 T125 jm70 G9 S39 T129 K104 jm69 G11 d (weaken_subst_evar _ empty H123))))
    | (Q_All K104 S39 T129 jm57 H104) => (fun (G11 : Env) (d : (Trace tm)) (H123 : (subst_evar G10 T125 s4 d G9 G11)) =>
      (Q_All G11 K104 S39 T129 (subst_evar_TyEq G10 s4 T125 jm70 (etvar G9 K104) S39 T129 (star) jm57 (appendEnv G11 (etvar empty K104)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K104) H123)) (substhvl_tm_wfKind _ _ H104 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H123)))))
    | (Q_Beta K105 K106 T128 T129 jm58 jm59 H108) => (fun (G11 : Env) (d : (Trace tm)) (H123 : (subst_evar G10 T125 s4 d G9 G11)) =>
      (Q_Beta G11 K105 K106 T128 T129 (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Kinding G10 s4 T125 jm70 (etvar G9 K105) T128 (weakenKind K106 (HS ty H0)) jm58 (appendEnv G11 (etvar empty K105)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K105) H123))) (subst_evar_Kinding G10 s4 T125 jm70 G9 T129 K105 jm59 G11 d (weaken_subst_evar _ empty H123)) (substhvl_tm_wfKind _ _ H108 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H123)))))
    | (Q_Eta K104 K107 T126 jm60) => (fun (G11 : Env) (d : (Trace tm)) (H123 : (subst_evar G10 T125 s4 d G9 G11)) =>
      (TyEq_cast G11 _ _ _ G11 (tabs K104 (tapp (weakenTy T126 (HS ty H0)) (tvar I0))) T126 (karr K104 K107) eq_refl (f_equal2 tabs eq_refl (f_equal2 tapp eq_refl eq_refl)) eq_refl eq_refl (Q_Eta G11 K104 K107 T126 (subst_evar_Kinding G10 s4 T125 jm70 G9 T126 (karr K104 K107) jm60 G11 d (weaken_subst_evar _ empty H123)))))
    | (Q_Refl K103 T126 jm61) => (fun (G11 : Env) (d : (Trace tm)) (H123 : (subst_evar G10 T125 s4 d G9 G11)) =>
      (Q_Refl G11 K103 T126 (subst_evar_Kinding G10 s4 T125 jm70 G9 T126 K103 jm61 G11 d (weaken_subst_evar _ empty H123))))
    | (Q_Symm K103 T126 U5 jm62) => (fun (G11 : Env) (d : (Trace tm)) (H123 : (subst_evar G10 T125 s4 d G9 G11)) =>
      (Q_Symm G11 K103 T126 U5 (subst_evar_TyEq G10 s4 T125 jm70 G9 T126 U5 K103 jm62 G11 d (weaken_subst_evar _ empty H123))))
    | (Q_Trans K103 T126 U5 V1 jm63 jm64) => (fun (G11 : Env) (d : (Trace tm)) (H123 : (subst_evar G10 T125 s4 d G9 G11)) =>
      (Q_Trans G11 K103 T126 U5 V1 (subst_evar_TyEq G10 s4 T125 jm70 G9 T126 U5 K103 jm63 G11 d (weaken_subst_evar _ empty H123)) (subst_evar_TyEq G10 s4 T125 jm70 G9 U5 V1 K103 jm64 G11 d (weaken_subst_evar _ empty H123))))
  end.
Fixpoint subst_etvar_TyEq (G10 : Env) (S40 : Ty) (K103 : Kind) (jm70 : (Kinding G10 S40 K103)) (G9 : Env) (T1 : Ty) (T2 : Ty) (K : Kind) (jm71 : (TyEq G9 T1 T2 K)) :
(forall (G11 : Env) (d : (Trace ty)) (H124 : (subst_etvar G10 K103 S40 d G9 G11)) ,
  (TyEq G11 (tsubstTy d S40 T1) (tsubstTy d S40 T2) K)) :=
  match jm71 in (TyEq _ T1 T2 K) return (forall (G11 : Env) (d : (Trace ty)) (H124 : (subst_etvar G10 K103 S40 d G9 G11)) ,
    (TyEq G11 (tsubstTy d S40 T1) (tsubstTy d S40 T2) K)) with
    | (Q_Arrow S38 S39 T127 T129 jm65 jm66) => (fun (G11 : Env) (d : (Trace ty)) (H124 : (subst_etvar G10 K103 S40 d G9 G11)) =>
      (Q_Arrow G11 (tsubstTy (weakenTrace d H0) S40 S38) (tsubstTy (weakenTrace d H0) S40 S39) (tsubstTy (weakenTrace d H0) S40 T127) (tsubstTy (weakenTrace d H0) S40 T129) (subst_etvar_TyEq G10 S40 K103 jm70 G9 S38 T127 (star) jm65 G11 d (weaken_subst_etvar _ empty H124)) (subst_etvar_TyEq G10 S40 K103 jm70 G9 S39 T129 (star) jm66 G11 d (weaken_subst_etvar _ empty H124))))
    | (Q_Abs K105 K108 S39 T129 jm67 H95 H96) => (fun (G11 : Env) (d : (Trace ty)) (H124 : (subst_etvar G10 K103 S40 d G9 G11)) =>
      (Q_Abs G11 K105 K108 (tsubstTy (weakenTrace d (HS ty H0)) S40 S39) (tsubstTy (weakenTrace d (HS ty H0)) S40 T129) (TyEq_cast _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_TyEq G10 S40 K103 jm70 (etvar G9 K105) S39 T129 (weakenKind K108 (HS ty H0)) jm67 (appendEnv G11 (tsubstEnv d S40 (etvar empty K105))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K105) H124))) (substhvl_ty_wfKind _ _ H95 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H124))) (substhvl_ty_wfKind _ _ H96 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H124)))))
    | (Q_App K105 K108 S38 S39 T127 T129 jm68 jm69) => (fun (G11 : Env) (d : (Trace ty)) (H124 : (subst_etvar G10 K103 S40 d G9 G11)) =>
      (Q_App G11 K105 K108 (tsubstTy (weakenTrace d H0) S40 S38) (tsubstTy (weakenTrace d H0) S40 S39) (tsubstTy (weakenTrace d H0) S40 T127) (tsubstTy (weakenTrace d H0) S40 T129) (subst_etvar_TyEq G10 S40 K103 jm70 G9 S38 T127 (karr K105 K108) jm68 G11 d (weaken_subst_etvar _ empty H124)) (subst_etvar_TyEq G10 S40 K103 jm70 G9 S39 T129 K105 jm69 G11 d (weaken_subst_etvar _ empty H124))))
    | (Q_All K105 S39 T129 jm57 H105) => (fun (G11 : Env) (d : (Trace ty)) (H124 : (subst_etvar G10 K103 S40 d G9 G11)) =>
      (Q_All G11 K105 (tsubstTy (weakenTrace d (HS ty H0)) S40 S39) (tsubstTy (weakenTrace d (HS ty H0)) S40 T129) (subst_etvar_TyEq G10 S40 K103 jm70 (etvar G9 K105) S39 T129 (star) jm57 (appendEnv G11 (tsubstEnv d S40 (etvar empty K105))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K105) H124)) (substhvl_ty_wfKind _ _ H105 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H124)))))
    | (Q_Beta K106 K107 T128 T129 jm58 jm59 H109) => (fun (G11 : Env) (d : (Trace ty)) (H124 : (subst_etvar G10 K103 S40 d G9 G11)) =>
      (TyEq_cast G11 _ _ _ G11 (tsubstTy d S40 (tapp (tabs K106 T128) T129)) (tsubstTy d S40 (tsubstTy X0 T129 T128)) K107 eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T128 d S40 T129)) eq_refl (Q_Beta G11 K106 K107 (tsubstTy (weakenTrace d (HS ty H0)) S40 T128) (tsubstTy (weakenTrace d H0) S40 T129) (Kinding_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_etvar_Kinding G10 S40 K103 jm70 (etvar G9 K106) T128 (weakenKind K107 (HS ty H0)) jm58 (appendEnv G11 (tsubstEnv d S40 (etvar empty K106))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K106) H124))) (subst_etvar_Kinding G10 S40 K103 jm70 G9 T129 K106 jm59 G11 d (weaken_subst_etvar _ empty H124)) (substhvl_ty_wfKind _ _ H109 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H124))))))
    | (Q_Eta K105 K108 T126 jm60) => (fun (G11 : Env) (d : (Trace ty)) (H124 : (subst_etvar G10 K103 S40 d G9 G11)) =>
      (TyEq_cast G11 _ _ _ G11 (tsubstTy d S40 (tabs K105 (tapp (weakenTy T126 (HS ty H0)) (tvar I0)))) (tsubstTy d S40 T126) (karr K105 K108) eq_refl (f_equal2 tabs eq_refl (f_equal2 tapp (weakenTy_tsubstTy (HS ty H0) d S40 T126) eq_refl)) eq_refl eq_refl (Q_Eta G11 K105 K108 (tsubstTy (weakenTrace d H0) S40 T126) (subst_etvar_Kinding G10 S40 K103 jm70 G9 T126 (karr K105 K108) jm60 G11 d (weaken_subst_etvar _ empty H124)))))
    | (Q_Refl K104 T126 jm61) => (fun (G11 : Env) (d : (Trace ty)) (H124 : (subst_etvar G10 K103 S40 d G9 G11)) =>
      (Q_Refl G11 K104 (tsubstTy (weakenTrace d H0) S40 T126) (subst_etvar_Kinding G10 S40 K103 jm70 G9 T126 K104 jm61 G11 d (weaken_subst_etvar _ empty H124))))
    | (Q_Symm K104 T126 U5 jm62) => (fun (G11 : Env) (d : (Trace ty)) (H124 : (subst_etvar G10 K103 S40 d G9 G11)) =>
      (Q_Symm G11 K104 (tsubstTy (weakenTrace d H0) S40 T126) (tsubstTy (weakenTrace d H0) S40 U5) (subst_etvar_TyEq G10 S40 K103 jm70 G9 T126 U5 K104 jm62 G11 d (weaken_subst_etvar _ empty H124))))
    | (Q_Trans K104 T126 U5 V1 jm63 jm64) => (fun (G11 : Env) (d : (Trace ty)) (H124 : (subst_etvar G10 K103 S40 d G9 G11)) =>
      (Q_Trans G11 K104 (tsubstTy (weakenTrace d H0) S40 T126) (tsubstTy (weakenTrace d H0) S40 U5) (tsubstTy (weakenTrace d H0) S40 V1) (subst_etvar_TyEq G10 S40 K103 jm70 G9 T126 U5 K104 jm63 G11 d (weaken_subst_etvar _ empty H124)) (subst_etvar_TyEq G10 S40 K103 jm70 G9 U5 V1 K104 jm64 G11 d (weaken_subst_etvar _ empty H124))))
  end.
Fixpoint subst_evar_Typing (G10 : Env) (s4 : Tm) (T126 : Ty) (jm66 : (Typing G10 s4 T126)) (G9 : Env) (t : Tm) (T : Ty) (jm67 : (Typing G9 t T)) :
(forall (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T126 s4 d G9 G11)) ,
  (Typing G11 (substTm d s4 t) T)) :=
  match jm67 in (Typing _ t T) return (forall (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T126 s4 d G9 G11)) ,
    (Typing G11 (substTm d s4 t) T)) with
    | (T_Var T127 y1 lk5 H92 H93) => (fun (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T126 s4 d G9 G11)) =>
      (subst_evar_lookup_evar G10 s4 T126 jm66 d G9 G11 H111 y1 T127 lk5))
    | (T_Abs T128 T131 t19 jm57 jm58 H95) => (fun (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T126 s4 d G9 G11)) =>
      (T_Abs G11 T128 T131 (substTm (weakenTrace d (HS tm H0)) s4 t19) (subst_evar_Kinding G10 s4 T126 jm66 G9 T128 (star) jm57 G11 d (weaken_subst_evar _ empty H111)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym eq_refl) (subst_evar_Typing G10 s4 T126 jm66 (evar G9 T128) t19 (weakenTy T131 (HS tm H0)) jm58 (appendEnv G11 (evar empty T128)) (weakenTrace d (HS tm H0)) (weaken_subst_evar _ (evar empty T128) H111))) (substhvl_tm_wfTy _ _ H95 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H111)))))
    | (T_App T129 T130 t20 t21 jm59 jm60) => (fun (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T126 s4 d G9 G11)) =>
      (T_App G11 T129 T130 (substTm (weakenTrace d H0) s4 t20) (substTm (weakenTrace d H0) s4 t21) (subst_evar_Typing G10 s4 T126 jm66 G9 t20 (tarr T129 T130) jm59 G11 d (weaken_subst_evar _ empty H111)) (subst_evar_Typing G10 s4 T126 jm66 G9 t21 T129 jm60 G11 d (weaken_subst_evar _ empty H111))))
    | (T_TAbs K104 T127 t19 jm61 H101) => (fun (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T126 s4 d G9 G11)) =>
      (T_TAbs G11 K104 T127 (substTm (weakenTrace d (HS ty H0)) s4 t19) (subst_evar_Typing G10 s4 T126 jm66 (etvar G9 K104) t19 T127 jm61 (appendEnv G11 (etvar empty K104)) (weakenTrace d (HS ty H0)) (weaken_subst_evar _ (etvar empty K104) H111)) (substhvl_tm_wfKind _ _ H101 (weaken_substhvl_tm H0 (subst_evar_substhvl_tm _ H111)))))
    | (T_TApp K105 T130 T131 t20 jm62 jm63) => (fun (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T126 s4 d G9 G11)) =>
      (T_TApp G11 K105 T130 T131 (substTm (weakenTrace d H0) s4 t20) (subst_evar_Typing G10 s4 T126 jm66 G9 t20 (tall K105 T130) jm62 G11 d (weaken_subst_evar _ empty H111)) (subst_evar_Kinding G10 s4 T126 jm66 G9 T131 K105 jm63 G11 d (weaken_subst_evar _ empty H111))))
    | (T_Eq S38 T127 t19 jm64 jm65) => (fun (G11 : Env) (d : (Trace tm)) (H111 : (subst_evar G10 T126 s4 d G9 G11)) =>
      (T_Eq G11 S38 T127 (substTm (weakenTrace d H0) s4 t19) (subst_evar_Typing G10 s4 T126 jm66 G9 t19 S38 jm64 G11 d (weaken_subst_evar _ empty H111)) (subst_evar_TyEq G10 s4 T126 jm66 G9 S38 T127 (star) jm65 G11 d (weaken_subst_evar _ empty H111))))
  end.
Fixpoint subst_etvar_Typing (G10 : Env) (S39 : Ty) (K104 : Kind) (jm66 : (Kinding G10 S39 K104)) (G9 : Env) (t : Tm) (T : Ty) (jm67 : (Typing G9 t T)) :
(forall (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K104 S39 d G9 G11)) ,
  (Typing G11 (tsubstTm d S39 t) (tsubstTy d S39 T))) :=
  match jm67 in (Typing _ t T) return (forall (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K104 S39 d G9 G11)) ,
    (Typing G11 (tsubstTm d S39 t) (tsubstTy d S39 T))) with
    | (T_Var T127 y1 lk5 H93 H94) => (fun (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K104 S39 d G9 G11)) =>
      (T_Var G11 (tsubstTy (weakenTrace d H0) S39 T127) y1 (subst_etvar_lookup_evar K104 (Kinding_wf_0 G10 S39 K104 jm66) H112 T127 lk5) (substhvl_ty_wfTy (Kinding_wf_0 G10 S39 K104 jm66) _ _ H93 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H112))) (substhvl_ty_wfindex_tm (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H112)) H94)))
    | (T_Abs T128 T131 t19 jm57 jm58 H96) => (fun (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K104 S39 d G9 G11)) =>
      (T_Abs G11 (tsubstTy (weakenTrace d H0) S39 T128) (tsubstTy (weakenTrace d H0) S39 T131) (tsubstTm (weakenTrace d (HS tm H0)) S39 t19) (subst_etvar_Kinding G10 S39 K104 jm66 G9 T128 (star) jm57 G11 d (weaken_subst_etvar _ empty H112)) (Typing_cast _ _ _ _ _ _ eq_refl eq_refl (eq_sym (weakenTy_tsubstTy (HS tm H0) d S39 T131)) (subst_etvar_Typing G10 S39 K104 jm66 (evar G9 T128) t19 (weakenTy T131 (HS tm H0)) jm58 (appendEnv G11 (tsubstEnv d S39 (evar empty T128))) (weakenTrace d (HS tm H0)) (weaken_subst_etvar _ (evar empty T128) H112))) (substhvl_ty_wfTy (Kinding_wf_0 G10 S39 K104 jm66) _ _ H96 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H112)))))
    | (T_App T129 T130 t20 t21 jm59 jm60) => (fun (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K104 S39 d G9 G11)) =>
      (T_App G11 (tsubstTy (weakenTrace d H0) S39 T129) (tsubstTy (weakenTrace d H0) S39 T130) (tsubstTm (weakenTrace d H0) S39 t20) (tsubstTm (weakenTrace d H0) S39 t21) (subst_etvar_Typing G10 S39 K104 jm66 G9 t20 (tarr T129 T130) jm59 G11 d (weaken_subst_etvar _ empty H112)) (subst_etvar_Typing G10 S39 K104 jm66 G9 t21 T129 jm60 G11 d (weaken_subst_etvar _ empty H112))))
    | (T_TAbs K105 T127 t19 jm61 H102) => (fun (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K104 S39 d G9 G11)) =>
      (T_TAbs G11 K105 (tsubstTy (weakenTrace d (HS ty H0)) S39 T127) (tsubstTm (weakenTrace d (HS ty H0)) S39 t19) (subst_etvar_Typing G10 S39 K104 jm66 (etvar G9 K105) t19 T127 jm61 (appendEnv G11 (tsubstEnv d S39 (etvar empty K105))) (weakenTrace d (HS ty H0)) (weaken_subst_etvar _ (etvar empty K105) H112)) (substhvl_ty_wfKind _ _ H102 (weaken_substhvl_ty H0 (subst_etvar_substhvl_ty _ H112)))))
    | (T_TApp K106 T130 T131 t20 jm62 jm63) => (fun (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K104 S39 d G9 G11)) =>
      (Typing_cast G11 _ _ G11 (tsubstTm d S39 (tyapp t20 T131)) (tsubstTy d S39 (tsubstTy X0 T131 T130)) eq_refl eq_refl (eq_sym (tsubstTy_tsubstTy0_comm T130 d S39 T131)) (T_TApp G11 K106 (tsubstTy (weakenTrace d (HS ty H0)) S39 T130) (tsubstTy (weakenTrace d H0) S39 T131) (tsubstTm (weakenTrace d H0) S39 t20) (subst_etvar_Typing G10 S39 K104 jm66 G9 t20 (tall K106 T130) jm62 G11 d (weaken_subst_etvar _ empty H112)) (subst_etvar_Kinding G10 S39 K104 jm66 G9 T131 K106 jm63 G11 d (weaken_subst_etvar _ empty H112)))))
    | (T_Eq S38 T127 t19 jm64 jm65) => (fun (G11 : Env) (d : (Trace ty)) (H112 : (subst_etvar G10 K104 S39 d G9 G11)) =>
      (T_Eq G11 (tsubstTy (weakenTrace d H0) S39 S38) (tsubstTy (weakenTrace d H0) S39 T127) (tsubstTm (weakenTrace d H0) S39 t19) (subst_etvar_Typing G10 S39 K104 jm66 G9 t19 S38 jm64 G11 d (weaken_subst_etvar _ empty H112)) (subst_etvar_TyEq G10 S39 K104 jm66 G9 S38 T127 (star) jm65 G11 d (weaken_subst_etvar _ empty H112))))
  end.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutofftm_append weakenCutoffty_append weakenTrace_append weakenKind_append weakenTm_append weakenTy_append appendHvl_assoc : interaction.