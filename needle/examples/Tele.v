Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export Needle.

Local Set Asymmetric Patterns.

Section Namespace.
  Inductive Namespace : Type :=
    | TmVar .
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
  
  Fixpoint weakenIndexTmVar (x4 : (Index TmVar)) (k : Hvl) {struct k} :
  (Index TmVar) :=
    match k with
      | (H0) => x4
      | (HS a k) => match a with
        | (TmVar) => (IS (weakenIndexTmVar x4 k))
      end
    end.
  Lemma weakenIndexTmVar_append  :
    (forall (x4 : (Index TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexTmVar (weakenIndexTmVar x4 k) k0) = (weakenIndexTmVar x4 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive Tele : Set :=
    | TNil 
    | TCons (T : Tm) (d : Tele)
  with Tm : Set :=
    | Var (x : (Index TmVar))
    | Abs (d : Tele) (t : Tm)
    | Pi (d : Tele) (T : Tm)
    | App (t : Tm) (ts : Terms)
  with Terms : Set :=
    | Nil 
    | Cons (t : Tm) (ts : Terms).
  Scheme ind_Tele := Induction for Tele Sort Prop
  with ind_Tm := Induction for Tm Sort Prop
  with ind_Terms := Induction for Terms Sort Prop.
  Combined Scheme ind_Tele_Tm_Terms from ind_Tele, ind_Tm, ind_Terms.
End Terms.

Section Functions.
  Fixpoint bind (d6 : Tele) {struct d6} :
  Hvl :=
    match d6 with
      | (TNil) => H0
      | (TCons T d) => (appendHvl (HS TmVar H0) (bind d))
    end.
  Scheme ind_bind_Tele := Induction for Tele Sort Prop.
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
      end
    end.
  
  Lemma weakenCutoffTmVar_append  :
    (forall (c : (Cutoff TmVar)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffTmVar (weakenCutoffTmVar c k) k0) = (weakenCutoffTmVar c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint shift_TmVar_Index (c : (Cutoff TmVar)) (x4 : (Index TmVar)) {struct c} :
  (Index TmVar) :=
    match c with
      | (C0) => (IS x4)
      | (CS c) => match x4 with
        | (I0) => I0
        | (IS x4) => (IS (shift_TmVar_Index c x4))
      end
    end.
  Fixpoint shift_TmVar_Tele (c : (Cutoff TmVar)) (d7 : Tele) {struct d7} :
  Tele :=
    match d7 with
      | (TNil) => (TNil)
      | (TCons T1 d8) => (TCons (shift_TmVar_Tm c T1) (shift_TmVar_Tele (CS c) d8))
    end
  with shift_TmVar_Tm (c : (Cutoff TmVar)) (s : Tm) {struct s} :
  Tm :=
    match s with
      | (Var x4) => (Var (shift_TmVar_Index c x4))
      | (Abs d7 t3) => (Abs (shift_TmVar_Tele c d7) (shift_TmVar_Tm (weakenCutoffTmVar c (appendHvl H0 (bind d7))) t3))
      | (Pi d8 T1) => (Pi (shift_TmVar_Tele c d8) (shift_TmVar_Tm (weakenCutoffTmVar c (appendHvl H0 (bind d8))) T1))
      | (App t4 ts1) => (App (shift_TmVar_Tm c t4) (shift_TmVar_Terms c ts1))
    end
  with shift_TmVar_Terms (c : (Cutoff TmVar)) (ts1 : Terms) {struct ts1} :
  Terms :=
    match ts1 with
      | (Nil) => (Nil)
      | (Cons t3 ts2) => (Cons (shift_TmVar_Tm c t3) (shift_TmVar_Terms c ts2))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenTele (d7 : Tele) (k : Hvl) {struct k} :
  Tele :=
    match k with
      | (H0) => d7
      | (HS TmVar k) => (shift_TmVar_Tele C0 (weakenTele d7 k))
    end.
  Fixpoint weakenTm (s : Tm) (k : Hvl) {struct k} :
  Tm :=
    match k with
      | (H0) => s
      | (HS TmVar k) => (shift_TmVar_Tm C0 (weakenTm s k))
    end.
  Fixpoint weakenTerms (ts1 : Terms) (k : Hvl) {struct k} :
  Terms :=
    match k with
      | (H0) => ts1
      | (HS TmVar k) => (shift_TmVar_Terms C0 (weakenTerms ts1 k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a : Namespace) : Type :=
    | X0 
    | XS (b : Namespace)
        (T1 : (Trace a)).
  
  Global Arguments X0 [a] .
  Global Arguments XS [a] b _ .
  Fixpoint weakenTrace {a : Namespace} (x4 : (Trace a)) (k : Hvl) {struct k} :
  (Trace a) :=
    match k with
      | (H0) => x4
      | (HS b k) => (XS b (weakenTrace x4 k))
    end.
  Lemma weakenTrace_append (a : Namespace) :
    (forall (x4 : (Trace a)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x4 k) k0) = (weakenTrace x4 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint subst_TmVar_Index (d7 : (Trace TmVar)) (s : Tm) (x4 : (Index TmVar)) {struct d7} :
  Tm :=
    match d7 with
      | (X0) => match x4 with
        | (I0) => s
        | (IS x4) => (Var x4)
      end
      | (XS TmVar d7) => match x4 with
        | (I0) => (Var I0)
        | (IS x4) => (shift_TmVar_Tm C0 (subst_TmVar_Index d7 s x4))
      end
    end.
  Fixpoint subst_TmVar_Tele (d7 : (Trace TmVar)) (s : Tm) (d8 : Tele) {struct d8} :
  Tele :=
    match d8 with
      | (TNil) => (TNil)
      | (TCons T1 d9) => (TCons (subst_TmVar_Tm d7 s T1) (subst_TmVar_Tele (weakenTrace d7 (HS TmVar H0)) s d9))
    end
  with subst_TmVar_Tm (d7 : (Trace TmVar)) (s : Tm) (s0 : Tm) {struct s0} :
  Tm :=
    match s0 with
      | (Var x4) => (subst_TmVar_Index d7 s x4)
      | (Abs d8 t3) => (Abs (subst_TmVar_Tele d7 s d8) (subst_TmVar_Tm (weakenTrace d7 (appendHvl H0 (bind d8))) s t3))
      | (Pi d9 T1) => (Pi (subst_TmVar_Tele d7 s d9) (subst_TmVar_Tm (weakenTrace d7 (appendHvl H0 (bind d9))) s T1))
      | (App t4 ts1) => (App (subst_TmVar_Tm d7 s t4) (subst_TmVar_Terms d7 s ts1))
    end
  with subst_TmVar_Terms (d7 : (Trace TmVar)) (s : Tm) (ts1 : Terms) {struct ts1} :
  Terms :=
    match ts1 with
      | (Nil) => (Nil)
      | (Cons t3 ts2) => (Cons (subst_TmVar_Tm d7 s t3) (subst_TmVar_Terms d7 s ts2))
    end.
End Subst.

Global Hint Resolve (f_equal (shift_TmVar_Tele C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TmVar_Terms C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_TmVar_Tm C0)) : cong_shift0.
 Hint Rewrite weakenCutoffTmVar_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Lemma stability_shift_TmVar__bind  :
  (forall (d7 : Tele) ,
    (forall (c : (Cutoff TmVar)) ,
      ((bind (shift_TmVar_Tele c d7)) = (bind d7)))).
Proof.
  apply_mutual_ind (ind_bind_Tele); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_shift_TmVar__bind : interaction.
 Hint Rewrite stability_shift_TmVar__bind : stability_shift.
Lemma stability_weaken_bind  :
  (forall (k : Hvl) (d8 : Tele) ,
    ((bind (weakenTele d8 k)) = (bind d8))).
Proof.
  needleGenericStabilityWeaken .
Qed.
 Hint Rewrite stability_weaken_bind : interaction.
 Hint Rewrite stability_weaken_bind : stability_weaken.
Lemma stability_subst_TmVar__bind  :
  (forall (d8 : Tele) ,
    (forall (d9 : (Trace TmVar)) (s : Tm) ,
      ((bind (subst_TmVar_Tele d9 s d8)) = (bind d8)))).
Proof.
  apply_mutual_ind (ind_bind_Tele); simpl; intros; congruence .
Qed.
 Hint Rewrite stability_subst_TmVar__bind : interaction.
 Hint Rewrite stability_subst_TmVar__bind : stability_subst.
Section SubstShiftReflection.
  Lemma subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind (s0 : Tm) :
    (forall (k : Hvl) (x4 : (Index TmVar)) ,
      ((subst_TmVar_Index (weakenTrace X0 k) s0 (shift_TmVar_Index (weakenCutoffTmVar C0 k) x4)) = (Var x4))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst_TmVar_0_shift_TmVar_0_Tele_reflection_ind (d10 : Tele) (k : Hvl) (s0 : Tm) {struct d10} :
  ((subst_TmVar_Tele (weakenTrace X0 k) s0 (shift_TmVar_Tele (weakenCutoffTmVar C0 k) d10)) = d10) :=
    match d10 return ((subst_TmVar_Tele (weakenTrace X0 k) s0 (shift_TmVar_Tele (weakenCutoffTmVar C0 k) d10)) = d10) with
      | (TNil) => eq_refl
      | (TCons T1 d11) => (f_equal2 TCons (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind T1 k s0) (eq_trans (f_equal3 subst_TmVar_Tele (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl) (subst_TmVar_0_shift_TmVar_0_Tele_reflection_ind d11 (HS TmVar k) s0)))
    end
  with subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind (s1 : Tm) (k : Hvl) (s0 : Tm) {struct s1} :
  ((subst_TmVar_Tm (weakenTrace X0 k) s0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s1)) = s1) :=
    match s1 return ((subst_TmVar_Tm (weakenTrace X0 k) s0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s1)) = s1) with
      | (Var x5) => (subst_TmVar_Index0_shift_TmVar_Index0_reflection_ind s0 k x5)
      | (Abs d12 t3) => (f_equal2 Abs (subst_TmVar_0_shift_TmVar_0_Tele_reflection_ind d12 k s0) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d12)))) eq_refl (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d12))) eq_refl)) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t3 (appendHvl k (appendHvl H0 (bind d12))) s0)))
      | (Pi d12 T2) => (f_equal2 Pi (subst_TmVar_0_shift_TmVar_0_Tele_reflection_ind d12 k s0) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d12)))) eq_refl (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d12))) eq_refl)) (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind T2 (appendHvl k (appendHvl H0 (bind d12))) s0)))
      | (App t3 ts1) => (f_equal2 App (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t3 k s0) (subst_TmVar_0_shift_TmVar_0_Terms_reflection_ind ts1 k s0))
    end
  with subst_TmVar_0_shift_TmVar_0_Terms_reflection_ind (ts2 : Terms) (k : Hvl) (s0 : Tm) {struct ts2} :
  ((subst_TmVar_Terms (weakenTrace X0 k) s0 (shift_TmVar_Terms (weakenCutoffTmVar C0 k) ts2)) = ts2) :=
    match ts2 return ((subst_TmVar_Terms (weakenTrace X0 k) s0 (shift_TmVar_Terms (weakenCutoffTmVar C0 k) ts2)) = ts2) with
      | (Nil) => eq_refl
      | (Cons t4 ts3) => (f_equal2 Cons (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind t4 k s0) (subst_TmVar_0_shift_TmVar_0_Terms_reflection_ind ts3 k s0))
    end.
  Definition subst_TmVar_Tele0_shift_TmVar_Tele0_reflection (d10 : Tele) : (forall (s0 : Tm) ,
    ((subst_TmVar_Tele X0 s0 (shift_TmVar_Tele C0 d10)) = d10)) := (subst_TmVar_0_shift_TmVar_0_Tele_reflection_ind d10 H0).
  Definition subst_TmVar_Tm0_shift_TmVar_Tm0_reflection (s1 : Tm) : (forall (s0 : Tm) ,
    ((subst_TmVar_Tm X0 s0 (shift_TmVar_Tm C0 s1)) = s1)) := (subst_TmVar_0_shift_TmVar_0_Tm_reflection_ind s1 H0).
  Definition subst_TmVar_Terms0_shift_TmVar_Terms0_reflection (ts1 : Terms) : (forall (s0 : Tm) ,
    ((subst_TmVar_Terms X0 s0 (shift_TmVar_Terms C0 ts1)) = ts1)) := (subst_TmVar_0_shift_TmVar_0_Terms_reflection_ind ts1 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shift_TmVar_Index_shift_TmVar_Index0_comm_ind  :
      (forall (k : Hvl) (c0 : (Cutoff TmVar)) (x4 : (Index TmVar)) ,
        ((shift_TmVar_Index (weakenCutoffTmVar (CS c0) k) (shift_TmVar_Index (weakenCutoffTmVar C0 k) x4)) = (shift_TmVar_Index (weakenCutoffTmVar C0 k) (shift_TmVar_Index (weakenCutoffTmVar c0 k) x4)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint shift_TmVar__shift_TmVar_0_Tele_comm_ind (d10 : Tele) (k : Hvl) (c0 : (Cutoff TmVar)) {struct d10} :
    ((shift_TmVar_Tele (weakenCutoffTmVar (CS c0) k) (shift_TmVar_Tele (weakenCutoffTmVar C0 k) d10)) = (shift_TmVar_Tele (weakenCutoffTmVar C0 k) (shift_TmVar_Tele (weakenCutoffTmVar c0 k) d10))) :=
      match d10 return ((shift_TmVar_Tele (weakenCutoffTmVar (CS c0) k) (shift_TmVar_Tele (weakenCutoffTmVar C0 k) d10)) = (shift_TmVar_Tele (weakenCutoffTmVar C0 k) (shift_TmVar_Tele (weakenCutoffTmVar c0 k) d10))) with
        | (TNil) => eq_refl
        | (TCons T1 d11) => (f_equal2 TCons (shift_TmVar__shift_TmVar_0_Tm_comm_ind T1 k c0) (shift_TmVar__shift_TmVar_0_Tele_comm_ind d11 (HS TmVar k) c0))
      end
    with shift_TmVar__shift_TmVar_0_Tm_comm_ind (s0 : Tm) (k : Hvl) (c0 : (Cutoff TmVar)) {struct s0} :
    ((shift_TmVar_Tm (weakenCutoffTmVar (CS c0) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c0 k) s0))) :=
      match s0 return ((shift_TmVar_Tm (weakenCutoffTmVar (CS c0) k) (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s0)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (shift_TmVar_Tm (weakenCutoffTmVar c0 k) s0))) with
        | (Var x5) => (f_equal Var (shift_TmVar_Index_shift_TmVar_Index0_comm_ind k c0 x5))
        | (Abs d12 t3) => (f_equal2 Abs (shift_TmVar__shift_TmVar_0_Tele_comm_ind d12 k c0) (eq_trans (f_equal2 shift_TmVar_Tm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenCutoffTmVar_append (CS c0) k (appendHvl H0 (bind d12)))) (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d12))) eq_refl)) (eq_trans (shift_TmVar__shift_TmVar_0_Tm_comm_ind t3 (appendHvl k (appendHvl H0 (bind d12))) c0) (f_equal2 shift_TmVar_Tm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d12)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _))))) (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append c0 k (appendHvl H0 (bind d12)))) eq_refl)))))
        | (Pi d12 T2) => (f_equal2 Pi (shift_TmVar__shift_TmVar_0_Tele_comm_ind d12 k c0) (eq_trans (f_equal2 shift_TmVar_Tm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenCutoffTmVar_append (CS c0) k (appendHvl H0 (bind d12)))) (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d12))) eq_refl)) (eq_trans (shift_TmVar__shift_TmVar_0_Tm_comm_ind T2 (appendHvl k (appendHvl H0 (bind d12))) c0) (f_equal2 shift_TmVar_Tm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d12)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _))))) (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append c0 k (appendHvl H0 (bind d12)))) eq_refl)))))
        | (App t3 ts1) => (f_equal2 App (shift_TmVar__shift_TmVar_0_Tm_comm_ind t3 k c0) (shift_TmVar__shift_TmVar_0_Terms_comm_ind ts1 k c0))
      end
    with shift_TmVar__shift_TmVar_0_Terms_comm_ind (ts2 : Terms) (k : Hvl) (c0 : (Cutoff TmVar)) {struct ts2} :
    ((shift_TmVar_Terms (weakenCutoffTmVar (CS c0) k) (shift_TmVar_Terms (weakenCutoffTmVar C0 k) ts2)) = (shift_TmVar_Terms (weakenCutoffTmVar C0 k) (shift_TmVar_Terms (weakenCutoffTmVar c0 k) ts2))) :=
      match ts2 return ((shift_TmVar_Terms (weakenCutoffTmVar (CS c0) k) (shift_TmVar_Terms (weakenCutoffTmVar C0 k) ts2)) = (shift_TmVar_Terms (weakenCutoffTmVar C0 k) (shift_TmVar_Terms (weakenCutoffTmVar c0 k) ts2))) with
        | (Nil) => eq_refl
        | (Cons t4 ts3) => (f_equal2 Cons (shift_TmVar__shift_TmVar_0_Tm_comm_ind t4 k c0) (shift_TmVar__shift_TmVar_0_Terms_comm_ind ts3 k c0))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition shift_TmVar__shift_TmVar_0_Tele_comm (d10 : Tele) : (forall (c0 : (Cutoff TmVar)) ,
      ((shift_TmVar_Tele (CS c0) (shift_TmVar_Tele C0 d10)) = (shift_TmVar_Tele C0 (shift_TmVar_Tele c0 d10)))) := (shift_TmVar__shift_TmVar_0_Tele_comm_ind d10 H0).
    Definition shift_TmVar__shift_TmVar_0_Tm_comm (s0 : Tm) : (forall (c0 : (Cutoff TmVar)) ,
      ((shift_TmVar_Tm (CS c0) (shift_TmVar_Tm C0 s0)) = (shift_TmVar_Tm C0 (shift_TmVar_Tm c0 s0)))) := (shift_TmVar__shift_TmVar_0_Tm_comm_ind s0 H0).
    Definition shift_TmVar__shift_TmVar_0_Terms_comm (ts1 : Terms) : (forall (c0 : (Cutoff TmVar)) ,
      ((shift_TmVar_Terms (CS c0) (shift_TmVar_Terms C0 ts1)) = (shift_TmVar_Terms C0 (shift_TmVar_Terms c0 ts1)))) := (shift_TmVar__shift_TmVar_0_Terms_comm_ind ts1 H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_TmVar__shift_TmVar_0_Tele_comm shift_TmVar__shift_TmVar_0_Terms_comm shift_TmVar__shift_TmVar_0_Tm_comm : interaction.
 Hint Rewrite shift_TmVar__shift_TmVar_0_Tele_comm shift_TmVar__shift_TmVar_0_Terms_comm shift_TmVar__shift_TmVar_0_Tm_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenTele_shift_TmVar_Tele  :
    (forall (k : Hvl) (c0 : (Cutoff TmVar)) (d10 : Tele) ,
      ((weakenTele (shift_TmVar_Tele c0 d10) k) = (shift_TmVar_Tele (weakenCutoffTmVar c0 k) (weakenTele d10 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTm_shift_TmVar_Tm  :
    (forall (k : Hvl) (c0 : (Cutoff TmVar)) (s0 : Tm) ,
      ((weakenTm (shift_TmVar_Tm c0 s0) k) = (shift_TmVar_Tm (weakenCutoffTmVar c0 k) (weakenTm s0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenTerms_shift_TmVar_Terms  :
    (forall (k : Hvl) (c0 : (Cutoff TmVar)) (ts1 : Terms) ,
      ((weakenTerms (shift_TmVar_Terms c0 ts1) k) = (shift_TmVar_Terms (weakenCutoffTmVar c0 k) (weakenTerms ts1 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shift_TmVar_Tm_subst_TmVar_Index0_comm_ind (c0 : (Cutoff TmVar)) (s0 : Tm) :
      (forall (k : Hvl) (x4 : (Index TmVar)) ,
        ((shift_TmVar_Tm (weakenCutoffTmVar c0 k) (subst_TmVar_Index (weakenTrace X0 k) s0 x4)) = (subst_TmVar_Index (weakenTrace X0 k) (shift_TmVar_Tm c0 s0) (shift_TmVar_Index (weakenCutoffTmVar (CS c0) k) x4)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint shift_TmVar__subst_TmVar_0_Tele_comm_ind (d10 : Tele) (k : Hvl) (c0 : (Cutoff TmVar)) (s0 : Tm) {struct d10} :
    ((shift_TmVar_Tele (weakenCutoffTmVar c0 k) (subst_TmVar_Tele (weakenTrace X0 k) s0 d10)) = (subst_TmVar_Tele (weakenTrace X0 k) (shift_TmVar_Tm c0 s0) (shift_TmVar_Tele (weakenCutoffTmVar (CS c0) k) d10))) :=
      match d10 return ((shift_TmVar_Tele (weakenCutoffTmVar c0 k) (subst_TmVar_Tele (weakenTrace X0 k) s0 d10)) = (subst_TmVar_Tele (weakenTrace X0 k) (shift_TmVar_Tm c0 s0) (shift_TmVar_Tele (weakenCutoffTmVar (CS c0) k) d10))) with
        | (TNil) => eq_refl
        | (TCons T1 d11) => (f_equal2 TCons (shift_TmVar__subst_TmVar_0_Tm_comm_ind T1 k c0 s0) (eq_trans (f_equal2 shift_TmVar_Tele eq_refl (f_equal3 subst_TmVar_Tele (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tele_comm_ind d11 (HS TmVar k) c0 s0) (f_equal3 subst_TmVar_Tele (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl eq_refl))))
      end
    with shift_TmVar__subst_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (c0 : (Cutoff TmVar)) (s0 : Tm) {struct s1} :
    ((shift_TmVar_Tm (weakenCutoffTmVar c0 k) (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c0 s0) (shift_TmVar_Tm (weakenCutoffTmVar (CS c0) k) s1))) :=
      match s1 return ((shift_TmVar_Tm (weakenCutoffTmVar c0 k) (subst_TmVar_Tm (weakenTrace X0 k) s0 s1)) = (subst_TmVar_Tm (weakenTrace X0 k) (shift_TmVar_Tm c0 s0) (shift_TmVar_Tm (weakenCutoffTmVar (CS c0) k) s1))) with
        | (Var x5) => (shift_TmVar_Tm_subst_TmVar_Index0_comm_ind c0 s0 k x5)
        | (Abs d12 t3) => (f_equal2 Abs (shift_TmVar__subst_TmVar_0_Tele_comm_ind d12 k c0 s0) (eq_trans (f_equal2 shift_TmVar_Tm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TmVar__bind _ _ _) (eq_refl H0)))) (weakenCutoffTmVar_append c0 k (appendHvl H0 (bind d12)))) (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d12))) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind t3 (appendHvl k (appendHvl H0 (bind d12))) c0 s0) (f_equal3 subst_TmVar_Tm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d12)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _))))) eq_refl (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append (CS c0) k (appendHvl H0 (bind d12)))) eq_refl)))))
        | (Pi d12 T2) => (f_equal2 Pi (shift_TmVar__subst_TmVar_0_Tele_comm_ind d12 k c0 s0) (eq_trans (f_equal2 shift_TmVar_Tm (eq_trans (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TmVar__bind _ _ _) (eq_refl H0)))) (weakenCutoffTmVar_append c0 k (appendHvl H0 (bind d12)))) (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d12))) eq_refl eq_refl)) (eq_trans (shift_TmVar__subst_TmVar_0_Tm_comm_ind T2 (appendHvl k (appendHvl H0 (bind d12))) c0 s0) (f_equal3 subst_TmVar_Tm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d12)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _))))) eq_refl (f_equal2 shift_TmVar_Tm (eq_sym (weakenCutoffTmVar_append (CS c0) k (appendHvl H0 (bind d12)))) eq_refl)))))
        | (App t3 ts1) => (f_equal2 App (shift_TmVar__subst_TmVar_0_Tm_comm_ind t3 k c0 s0) (shift_TmVar__subst_TmVar_0_Terms_comm_ind ts1 k c0 s0))
      end
    with shift_TmVar__subst_TmVar_0_Terms_comm_ind (ts2 : Terms) (k : Hvl) (c0 : (Cutoff TmVar)) (s0 : Tm) {struct ts2} :
    ((shift_TmVar_Terms (weakenCutoffTmVar c0 k) (subst_TmVar_Terms (weakenTrace X0 k) s0 ts2)) = (subst_TmVar_Terms (weakenTrace X0 k) (shift_TmVar_Tm c0 s0) (shift_TmVar_Terms (weakenCutoffTmVar (CS c0) k) ts2))) :=
      match ts2 return ((shift_TmVar_Terms (weakenCutoffTmVar c0 k) (subst_TmVar_Terms (weakenTrace X0 k) s0 ts2)) = (subst_TmVar_Terms (weakenTrace X0 k) (shift_TmVar_Tm c0 s0) (shift_TmVar_Terms (weakenCutoffTmVar (CS c0) k) ts2))) with
        | (Nil) => eq_refl
        | (Cons t4 ts3) => (f_equal2 Cons (shift_TmVar__subst_TmVar_0_Tm_comm_ind t4 k c0 s0) (shift_TmVar__subst_TmVar_0_Terms_comm_ind ts3 k c0 s0))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shift_TmVar_Tele_subst_TmVar_Tele0_comm (d10 : Tele) : (forall (c0 : (Cutoff TmVar)) (s0 : Tm) ,
      ((shift_TmVar_Tele c0 (subst_TmVar_Tele X0 s0 d10)) = (subst_TmVar_Tele X0 (shift_TmVar_Tm c0 s0) (shift_TmVar_Tele (CS c0) d10)))) := (shift_TmVar__subst_TmVar_0_Tele_comm_ind d10 H0).
    Definition shift_TmVar_Tm_subst_TmVar_Tm0_comm (s1 : Tm) : (forall (c0 : (Cutoff TmVar)) (s0 : Tm) ,
      ((shift_TmVar_Tm c0 (subst_TmVar_Tm X0 s0 s1)) = (subst_TmVar_Tm X0 (shift_TmVar_Tm c0 s0) (shift_TmVar_Tm (CS c0) s1)))) := (shift_TmVar__subst_TmVar_0_Tm_comm_ind s1 H0).
    Definition shift_TmVar_Terms_subst_TmVar_Terms0_comm (ts1 : Terms) : (forall (c0 : (Cutoff TmVar)) (s0 : Tm) ,
      ((shift_TmVar_Terms c0 (subst_TmVar_Terms X0 s0 ts1)) = (subst_TmVar_Terms X0 (shift_TmVar_Tm c0 s0) (shift_TmVar_Terms (CS c0) ts1)))) := (shift_TmVar__subst_TmVar_0_Terms_comm_ind ts1 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma subst_TmVar_Index_shift_TmVar_Tm0_comm_ind (d10 : (Trace TmVar)) (s0 : Tm) :
      (forall (k : Hvl) (x4 : (Index TmVar)) ,
        ((subst_TmVar_Index (weakenTrace (XS TmVar d10) k) s0 (shift_TmVar_Index (weakenCutoffTmVar C0 k) x4)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Index (weakenTrace d10 k) s0 x4)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_TmVar__shift_TmVar_0_Tele_comm_ind (d11 : Tele) (k : Hvl) (d10 : (Trace TmVar)) (s0 : Tm) {struct d11} :
    ((subst_TmVar_Tele (weakenTrace (XS TmVar d10) k) s0 (shift_TmVar_Tele (weakenCutoffTmVar C0 k) d11)) = (shift_TmVar_Tele (weakenCutoffTmVar C0 k) (subst_TmVar_Tele (weakenTrace d10 k) s0 d11))) :=
      match d11 return ((subst_TmVar_Tele (weakenTrace (XS TmVar d10) k) s0 (shift_TmVar_Tele (weakenCutoffTmVar C0 k) d11)) = (shift_TmVar_Tele (weakenCutoffTmVar C0 k) (subst_TmVar_Tele (weakenTrace d10 k) s0 d11))) with
        | (TNil) => eq_refl
        | (TCons T1 d12) => (f_equal2 TCons (subst_TmVar__shift_TmVar_0_Tm_comm_ind T1 k d10 s0) (eq_trans (f_equal3 subst_TmVar_Tele (weakenTrace_append TmVar (XS TmVar d10) k (HS TmVar H0)) eq_refl eq_refl) (eq_trans (subst_TmVar__shift_TmVar_0_Tele_comm_ind d12 (HS TmVar k) d10 s0) (f_equal2 shift_TmVar_Tele eq_refl (f_equal3 subst_TmVar_Tele (eq_sym (weakenTrace_append TmVar d10 k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TmVar__shift_TmVar_0_Tm_comm_ind (s1 : Tm) (k : Hvl) (d10 : (Trace TmVar)) (s0 : Tm) {struct s1} :
    ((subst_TmVar_Tm (weakenTrace (XS TmVar d10) k) s0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s1)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d10 k) s0 s1))) :=
      match s1 return ((subst_TmVar_Tm (weakenTrace (XS TmVar d10) k) s0 (shift_TmVar_Tm (weakenCutoffTmVar C0 k) s1)) = (shift_TmVar_Tm (weakenCutoffTmVar C0 k) (subst_TmVar_Tm (weakenTrace d10 k) s0 s1))) with
        | (Var x5) => (subst_TmVar_Index_shift_TmVar_Tm0_comm_ind d10 s0 k x5)
        | (Abs d13 t3) => (f_equal2 Abs (subst_TmVar__shift_TmVar_0_Tele_comm_ind d13 k d10 s0) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenTrace_append TmVar (XS TmVar d10) k (appendHvl H0 (bind d13)))) eq_refl (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d13))) eq_refl)) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind t3 (appendHvl k (appendHvl H0 (bind d13))) d10 s0) (f_equal2 shift_TmVar_Tm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d13)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0))))) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d10 k (appendHvl H0 (bind d13)))) eq_refl eq_refl)))))
        | (Pi d13 T2) => (f_equal2 Pi (subst_TmVar__shift_TmVar_0_Tele_comm_ind d13 k d10 s0) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (stability_shift_TmVar__bind _ _))) (weakenTrace_append TmVar (XS TmVar d10) k (appendHvl H0 (bind d13)))) eq_refl (f_equal2 shift_TmVar_Tm (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d13))) eq_refl)) (eq_trans (subst_TmVar__shift_TmVar_0_Tm_comm_ind T2 (appendHvl k (appendHvl H0 (bind d13))) d10 s0) (f_equal2 shift_TmVar_Tm (eq_trans (eq_sym (weakenCutoffTmVar_append C0 k (appendHvl H0 (bind d13)))) (f_equal2 weakenCutoffTmVar eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0))))) (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar d10 k (appendHvl H0 (bind d13)))) eq_refl eq_refl)))))
        | (App t3 ts1) => (f_equal2 App (subst_TmVar__shift_TmVar_0_Tm_comm_ind t3 k d10 s0) (subst_TmVar__shift_TmVar_0_Terms_comm_ind ts1 k d10 s0))
      end
    with subst_TmVar__shift_TmVar_0_Terms_comm_ind (ts2 : Terms) (k : Hvl) (d10 : (Trace TmVar)) (s0 : Tm) {struct ts2} :
    ((subst_TmVar_Terms (weakenTrace (XS TmVar d10) k) s0 (shift_TmVar_Terms (weakenCutoffTmVar C0 k) ts2)) = (shift_TmVar_Terms (weakenCutoffTmVar C0 k) (subst_TmVar_Terms (weakenTrace d10 k) s0 ts2))) :=
      match ts2 return ((subst_TmVar_Terms (weakenTrace (XS TmVar d10) k) s0 (shift_TmVar_Terms (weakenCutoffTmVar C0 k) ts2)) = (shift_TmVar_Terms (weakenCutoffTmVar C0 k) (subst_TmVar_Terms (weakenTrace d10 k) s0 ts2))) with
        | (Nil) => eq_refl
        | (Cons t4 ts3) => (f_equal2 Cons (subst_TmVar__shift_TmVar_0_Tm_comm_ind t4 k d10 s0) (subst_TmVar__shift_TmVar_0_Terms_comm_ind ts3 k d10 s0))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition subst_TmVar_Tele_shift_TmVar_Tele0_comm (d11 : Tele) : (forall (d10 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Tele (XS TmVar d10) s0 (shift_TmVar_Tele C0 d11)) = (shift_TmVar_Tele C0 (subst_TmVar_Tele d10 s0 d11)))) := (subst_TmVar__shift_TmVar_0_Tele_comm_ind d11 H0).
    Definition subst_TmVar_Tm_shift_TmVar_Tm0_comm (s1 : Tm) : (forall (d10 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Tm (XS TmVar d10) s0 (shift_TmVar_Tm C0 s1)) = (shift_TmVar_Tm C0 (subst_TmVar_Tm d10 s0 s1)))) := (subst_TmVar__shift_TmVar_0_Tm_comm_ind s1 H0).
    Definition subst_TmVar_Terms_shift_TmVar_Terms0_comm (ts1 : Terms) : (forall (d10 : (Trace TmVar)) (s0 : Tm) ,
      ((subst_TmVar_Terms (XS TmVar d10) s0 (shift_TmVar_Terms C0 ts1)) = (shift_TmVar_Terms C0 (subst_TmVar_Terms d10 s0 ts1)))) := (subst_TmVar__shift_TmVar_0_Terms_comm_ind ts1 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    
  End SubstSubordInd.
  Section SubstSubord.
    
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite subst_TmVar_Tele0_shift_TmVar_Tele0_reflection subst_TmVar_Terms0_shift_TmVar_Terms0_reflection subst_TmVar_Tm0_shift_TmVar_Tm0_reflection : interaction.
 Hint Rewrite subst_TmVar_Tele0_shift_TmVar_Tele0_reflection subst_TmVar_Terms0_shift_TmVar_Terms0_reflection subst_TmVar_Tm0_shift_TmVar_Tm0_reflection : reflection.
 Hint Rewrite subst_TmVar_Tele_shift_TmVar_Tele0_comm subst_TmVar_Terms_shift_TmVar_Terms0_comm subst_TmVar_Tm_shift_TmVar_Tm0_comm : interaction.
 Hint Rewrite subst_TmVar_Tele_shift_TmVar_Tele0_comm subst_TmVar_Terms_shift_TmVar_Terms0_comm subst_TmVar_Tm_shift_TmVar_Tm0_comm : subst_shift0.
 Hint Rewrite shift_TmVar_Tele_subst_TmVar_Tele0_comm shift_TmVar_Terms_subst_TmVar_Terms0_comm shift_TmVar_Tm_subst_TmVar_Tm0_comm : interaction.
 Hint Rewrite shift_TmVar_Tele_subst_TmVar_Tele0_comm shift_TmVar_Terms_subst_TmVar_Terms0_comm shift_TmVar_Tm_subst_TmVar_Tm0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma subst_TmVar_Tm_subst_TmVar_Index0_commright_ind (d10 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) :
      (forall (k : Hvl) (x4 : (Index TmVar)) ,
        ((subst_TmVar_Tm (weakenTrace d10 k) s0 (subst_TmVar_Index (weakenTrace X0 k) s1 x4)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d10 s0 s1) (subst_TmVar_Index (weakenTrace (XS TmVar d10) k) s0 x4)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_TmVar__subst_TmVar_0_Tele_comm_ind (d11 : Tele) (k : Hvl) (d10 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) {struct d11} :
    ((subst_TmVar_Tele (weakenTrace d10 k) s0 (subst_TmVar_Tele (weakenTrace X0 k) s1 d11)) = (subst_TmVar_Tele (weakenTrace X0 k) (subst_TmVar_Tm d10 s0 s1) (subst_TmVar_Tele (weakenTrace (XS TmVar d10) k) s0 d11))) :=
      match d11 return ((subst_TmVar_Tele (weakenTrace d10 k) s0 (subst_TmVar_Tele (weakenTrace X0 k) s1 d11)) = (subst_TmVar_Tele (weakenTrace X0 k) (subst_TmVar_Tm d10 s0 s1) (subst_TmVar_Tele (weakenTrace (XS TmVar d10) k) s0 d11))) with
        | (TNil) => eq_refl
        | (TCons T1 d12) => (f_equal2 TCons (subst_TmVar__subst_TmVar_0_Tm_comm_ind T1 k d10 s0 s1) (eq_trans (f_equal3 subst_TmVar_Tele (weakenTrace_append TmVar d10 k (HS TmVar H0)) eq_refl (f_equal3 subst_TmVar_Tele (weakenTrace_append TmVar X0 k (HS TmVar H0)) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tele_comm_ind d12 (HS TmVar k) d10 s0 s1) (f_equal3 subst_TmVar_Tele (eq_sym (weakenTrace_append TmVar X0 k (HS TmVar H0))) eq_refl (f_equal3 subst_TmVar_Tele (eq_sym (weakenTrace_append TmVar (XS TmVar d10) k (HS TmVar H0))) eq_refl eq_refl)))))
      end
    with subst_TmVar__subst_TmVar_0_Tm_comm_ind (s2 : Tm) (k : Hvl) (d10 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) {struct s2} :
    ((subst_TmVar_Tm (weakenTrace d10 k) s0 (subst_TmVar_Tm (weakenTrace X0 k) s1 s2)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d10 s0 s1) (subst_TmVar_Tm (weakenTrace (XS TmVar d10) k) s0 s2))) :=
      match s2 return ((subst_TmVar_Tm (weakenTrace d10 k) s0 (subst_TmVar_Tm (weakenTrace X0 k) s1 s2)) = (subst_TmVar_Tm (weakenTrace X0 k) (subst_TmVar_Tm d10 s0 s1) (subst_TmVar_Tm (weakenTrace (XS TmVar d10) k) s0 s2))) with
        | (Var x5) => (subst_TmVar_Tm_subst_TmVar_Index0_commright_ind d10 s0 s1 k x5)
        | (Abs d13 t3) => (f_equal2 Abs (subst_TmVar__subst_TmVar_0_Tele_comm_ind d13 k d10 s0 s1) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TmVar__bind _ _ _) (eq_refl H0)))) (weakenTrace_append TmVar d10 k (appendHvl H0 (bind d13)))) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d13))) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind t3 (appendHvl k (appendHvl H0 (bind d13))) d10 s0 s1) (f_equal3 subst_TmVar_Tm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d13)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d10) k (appendHvl H0 (bind d13)))) eq_refl eq_refl)))))
        | (Pi d13 T2) => (f_equal2 Pi (subst_TmVar__subst_TmVar_0_Tele_comm_ind d13 k d10 s0 s1) (eq_trans (f_equal3 subst_TmVar_Tm (eq_trans (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (stability_subst_TmVar__bind _ _ _) (eq_refl H0)))) (weakenTrace_append TmVar d10 k (appendHvl H0 (bind d13)))) eq_refl (f_equal3 subst_TmVar_Tm (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d13))) eq_refl eq_refl)) (eq_trans (subst_TmVar__subst_TmVar_0_Tm_comm_ind T2 (appendHvl k (appendHvl H0 (bind d13))) d10 s0 s1) (f_equal3 subst_TmVar_Tm (eq_trans (eq_sym (weakenTrace_append TmVar X0 k (appendHvl H0 (bind d13)))) (f_equal2 weakenTrace eq_refl (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0))))) eq_refl (f_equal3 subst_TmVar_Tm (eq_sym (weakenTrace_append TmVar (XS TmVar d10) k (appendHvl H0 (bind d13)))) eq_refl eq_refl)))))
        | (App t3 ts1) => (f_equal2 App (subst_TmVar__subst_TmVar_0_Tm_comm_ind t3 k d10 s0 s1) (subst_TmVar__subst_TmVar_0_Terms_comm_ind ts1 k d10 s0 s1))
      end
    with subst_TmVar__subst_TmVar_0_Terms_comm_ind (ts2 : Terms) (k : Hvl) (d10 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) {struct ts2} :
    ((subst_TmVar_Terms (weakenTrace d10 k) s0 (subst_TmVar_Terms (weakenTrace X0 k) s1 ts2)) = (subst_TmVar_Terms (weakenTrace X0 k) (subst_TmVar_Tm d10 s0 s1) (subst_TmVar_Terms (weakenTrace (XS TmVar d10) k) s0 ts2))) :=
      match ts2 return ((subst_TmVar_Terms (weakenTrace d10 k) s0 (subst_TmVar_Terms (weakenTrace X0 k) s1 ts2)) = (subst_TmVar_Terms (weakenTrace X0 k) (subst_TmVar_Tm d10 s0 s1) (subst_TmVar_Terms (weakenTrace (XS TmVar d10) k) s0 ts2))) with
        | (Nil) => eq_refl
        | (Cons t4 ts3) => (f_equal2 Cons (subst_TmVar__subst_TmVar_0_Tm_comm_ind t4 k d10 s0 s1) (subst_TmVar__subst_TmVar_0_Terms_comm_ind ts3 k d10 s0 s1))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition subst_TmVar_Tele_subst_TmVar_Tele0_comm (d11 : Tele) : (forall (d10 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) ,
      ((subst_TmVar_Tele d10 s0 (subst_TmVar_Tele X0 s1 d11)) = (subst_TmVar_Tele X0 (subst_TmVar_Tm d10 s0 s1) (subst_TmVar_Tele (XS TmVar d10) s0 d11)))) := (subst_TmVar__subst_TmVar_0_Tele_comm_ind d11 H0).
    Definition subst_TmVar_Tm_subst_TmVar_Tm0_comm (s2 : Tm) : (forall (d10 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) ,
      ((subst_TmVar_Tm d10 s0 (subst_TmVar_Tm X0 s1 s2)) = (subst_TmVar_Tm X0 (subst_TmVar_Tm d10 s0 s1) (subst_TmVar_Tm (XS TmVar d10) s0 s2)))) := (subst_TmVar__subst_TmVar_0_Tm_comm_ind s2 H0).
    Definition subst_TmVar_Terms_subst_TmVar_Terms0_comm (ts1 : Terms) : (forall (d10 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) ,
      ((subst_TmVar_Terms d10 s0 (subst_TmVar_Terms X0 s1 ts1)) = (subst_TmVar_Terms X0 (subst_TmVar_Tm d10 s0 s1) (subst_TmVar_Terms (XS TmVar d10) s0 ts1)))) := (subst_TmVar__subst_TmVar_0_Terms_comm_ind ts1 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenTele_subst_TmVar_Tele  :
      (forall (k : Hvl) (d10 : (Trace TmVar)) (s0 : Tm) (d11 : Tele) ,
        ((weakenTele (subst_TmVar_Tele d10 s0 d11) k) = (subst_TmVar_Tele (weakenTrace d10 k) s0 (weakenTele d11 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTm_subst_TmVar_Tm  :
      (forall (k : Hvl) (d10 : (Trace TmVar)) (s0 : Tm) (s1 : Tm) ,
        ((weakenTm (subst_TmVar_Tm d10 s0 s1) k) = (subst_TmVar_Tm (weakenTrace d10 k) s0 (weakenTm s1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenTerms_subst_TmVar_Terms  :
      (forall (k : Hvl) (d10 : (Trace TmVar)) (s0 : Tm) (ts1 : Terms) ,
        ((weakenTerms (subst_TmVar_Terms d10 s0 ts1) k) = (subst_TmVar_Terms (weakenTrace d10 k) s0 (weakenTerms ts1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite subst_TmVar_Tele_subst_TmVar_Tele0_comm subst_TmVar_Terms_subst_TmVar_Terms0_comm subst_TmVar_Tm_subst_TmVar_Tm0_comm : interaction.
 Hint Rewrite subst_TmVar_Tele_subst_TmVar_Tele0_comm subst_TmVar_Terms_subst_TmVar_Terms0_comm subst_TmVar_Tm_subst_TmVar_Tm0_comm : subst_subst0.
 Hint Rewrite weakenTele_shift_TmVar_Tele weakenTerms_shift_TmVar_Terms weakenTm_shift_TmVar_Tm : weaken_shift.
 Hint Rewrite weakenTele_subst_TmVar_Tele weakenTerms_subst_TmVar_Terms weakenTm_subst_TmVar_Tm : weaken_subst.
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
  Inductive wfTele (k : Hvl) : Tele -> Prop :=
    | wfTele_TNil :
        (wfTele k (TNil))
    | wfTele_TCons {T1 : Tm}
        (wf : (wfTm k T1)) {d10 : Tele}
        (wf0 : (wfTele (HS TmVar k) d10))
        : (wfTele k (TCons T1 d10))
  with wfTm (k : Hvl) : Tm -> Prop :=
    | wfTm_Var
        (x4 : (Index TmVar))
        (wfi : (wfindex k x4)) :
        (wfTm k (Var x4))
    | wfTm_Abs {d10 : Tele}
        (wf : (wfTele k d10)) {t3 : Tm}
        (wf0 : (wfTm (appendHvl k (appendHvl H0 (bind d10))) t3))
        : (wfTm k (Abs d10 t3))
    | wfTm_Pi {d11 : Tele}
        (wf : (wfTele k d11)) {T1 : Tm}
        (wf0 : (wfTm (appendHvl k (appendHvl H0 (bind d11))) T1))
        : (wfTm k (Pi d11 T1))
    | wfTm_App {t4 : Tm}
        (wf : (wfTm k t4)) {ts1 : Terms}
        (wf0 : (wfTerms k ts1)) :
        (wfTm k (App t4 ts1))
  with wfTerms (k : Hvl) : Terms -> Prop :=
    | wfTerms_Nil :
        (wfTerms k (Nil))
    | wfTerms_Cons {t3 : Tm}
        (wf : (wfTm k t3)) {ts1 : Terms}
        (wf0 : (wfTerms k ts1)) :
        (wfTerms k (Cons t3 ts1)).
  Definition inversion_wfTele_TCons_1 (k0 : Hvl) (T : Tm) (d : Tele) (H13 : (wfTele k0 (TCons T d))) : (wfTm k0 T) := match H13 in (wfTele _ d11) return match d11 return Prop with
    | (TCons T d) => (wfTm k0 T)
    | _ => True
  end with
    | (wfTele_TCons T H1 d H2) => H1
    | _ => I
  end.
  Definition inversion_wfTele_TCons_2 (k0 : Hvl) (T : Tm) (d : Tele) (H13 : (wfTele k0 (TCons T d))) : (wfTele (HS TmVar k0) d) := match H13 in (wfTele _ d11) return match d11 return Prop with
    | (TCons T d) => (wfTele (HS TmVar k0) d)
    | _ => True
  end with
    | (wfTele_TCons T H1 d H2) => H2
    | _ => I
  end.
  Definition inversion_wfTm_Var_1 (k1 : Hvl) (x : (Index TmVar)) (H14 : (wfTm k1 (Var x))) : (wfindex k1 x) := match H14 in (wfTm _ s0) return match s0 return Prop with
    | (Var x) => (wfindex k1 x)
    | _ => True
  end with
    | (wfTm_Var x H3) => H3
    | _ => I
  end.
  Definition inversion_wfTm_Abs_0 (k2 : Hvl) (d : Tele) (t : Tm) (H15 : (wfTm k2 (Abs d t))) : (wfTele k2 d) := match H15 in (wfTm _ s1) return match s1 return Prop with
    | (Abs d t) => (wfTele k2 d)
    | _ => True
  end with
    | (wfTm_Abs d H4 t H5) => H4
    | _ => I
  end.
  Definition inversion_wfTm_Abs_1 (k2 : Hvl) (d : Tele) (t : Tm) (H15 : (wfTm k2 (Abs d t))) : (wfTm (appendHvl k2 (appendHvl H0 (bind d))) t) := match H15 in (wfTm _ s1) return match s1 return Prop with
    | (Abs d t) => (wfTm (appendHvl k2 (appendHvl H0 (bind d))) t)
    | _ => True
  end with
    | (wfTm_Abs d H4 t H5) => H5
    | _ => I
  end.
  Definition inversion_wfTm_Pi_0 (k3 : Hvl) (d : Tele) (T : Tm) (H16 : (wfTm k3 (Pi d T))) : (wfTele k3 d) := match H16 in (wfTm _ s2) return match s2 return Prop with
    | (Pi d T) => (wfTele k3 d)
    | _ => True
  end with
    | (wfTm_Pi d H6 T H7) => H6
    | _ => I
  end.
  Definition inversion_wfTm_Pi_1 (k3 : Hvl) (d : Tele) (T : Tm) (H16 : (wfTm k3 (Pi d T))) : (wfTm (appendHvl k3 (appendHvl H0 (bind d))) T) := match H16 in (wfTm _ s2) return match s2 return Prop with
    | (Pi d T) => (wfTm (appendHvl k3 (appendHvl H0 (bind d))) T)
    | _ => True
  end with
    | (wfTm_Pi d H6 T H7) => H7
    | _ => I
  end.
  Definition inversion_wfTm_App_0 (k4 : Hvl) (t : Tm) (ts : Terms) (H17 : (wfTm k4 (App t ts))) : (wfTm k4 t) := match H17 in (wfTm _ s3) return match s3 return Prop with
    | (App t ts) => (wfTm k4 t)
    | _ => True
  end with
    | (wfTm_App t H8 ts H9) => H8
    | _ => I
  end.
  Definition inversion_wfTm_App_1 (k4 : Hvl) (t : Tm) (ts : Terms) (H17 : (wfTm k4 (App t ts))) : (wfTerms k4 ts) := match H17 in (wfTm _ s3) return match s3 return Prop with
    | (App t ts) => (wfTerms k4 ts)
    | _ => True
  end with
    | (wfTm_App t H8 ts H9) => H9
    | _ => I
  end.
  Definition inversion_wfTerms_Cons_0 (k6 : Hvl) (t : Tm) (ts : Terms) (H19 : (wfTerms k6 (Cons t ts))) : (wfTm k6 t) := match H19 in (wfTerms _ ts2) return match ts2 return Prop with
    | (Cons t ts) => (wfTm k6 t)
    | _ => True
  end with
    | (wfTerms_Cons t H10 ts H11) => H10
    | _ => I
  end.
  Definition inversion_wfTerms_Cons_1 (k6 : Hvl) (t : Tm) (ts : Terms) (H19 : (wfTerms k6 (Cons t ts))) : (wfTerms k6 ts) := match H19 in (wfTerms _ ts2) return match ts2 return Prop with
    | (Cons t ts) => (wfTerms k6 ts)
    | _ => True
  end with
    | (wfTerms_Cons t H10 ts H11) => H11
    | _ => I
  end.
  Scheme ind_wfTele := Induction for wfTele Sort Prop
  with ind_wfTm := Induction for wfTm Sort Prop
  with ind_wfTerms := Induction for wfTerms Sort Prop.
  Combined Scheme ind_wfTele_Tm_Terms from ind_wfTele, ind_wfTm, ind_wfTerms.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_TmVar : (forall (c0 : (Cutoff TmVar)) (k7 : Hvl) (k8 : Hvl) ,
    Prop) :=
    | shifthvl_TmVar_here
        (k7 : Hvl) :
        (shifthvl_TmVar C0 k7 (HS TmVar k7))
    | shifthvl_TmVar_there_TmVar
        (c0 : (Cutoff TmVar)) (k7 : Hvl)
        (k8 : Hvl) :
        (shifthvl_TmVar c0 k7 k8) -> (shifthvl_TmVar (CS c0) (HS TmVar k7) (HS TmVar k8)).
  Lemma weaken_shifthvl_TmVar  :
    (forall (k7 : Hvl) {c0 : (Cutoff TmVar)} {k8 : Hvl} {k9 : Hvl} ,
      (shifthvl_TmVar c0 k8 k9) -> (shifthvl_TmVar (weakenCutoffTmVar c0 k7) (appendHvl k8 k7) (appendHvl k9 k7))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_TmVar__wfindex_TmVar  :
    (forall (c0 : (Cutoff TmVar)) (k7 : Hvl) (k8 : Hvl) (ins : (shifthvl_TmVar c0 k7 k8)) (x4 : (Index TmVar)) ,
      (wfindex k7 x4) -> (wfindex k8 (shift_TmVar_Index c0 x4))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_TmVar__wfTele_Tm_Terms : (forall (k7 : Hvl) ,
    (forall (d12 : Tele) (wf : (wfTele k7 d12)) ,
      (forall (c0 : (Cutoff TmVar)) (k8 : Hvl) ,
        (shifthvl_TmVar c0 k7 k8) -> (wfTele k8 (shift_TmVar_Tele c0 d12)))) /\
    (forall (s4 : Tm) (wf : (wfTm k7 s4)) ,
      (forall (c0 : (Cutoff TmVar)) (k8 : Hvl) ,
        (shifthvl_TmVar c0 k7 k8) -> (wfTm k8 (shift_TmVar_Tm c0 s4)))) /\
    (forall (ts3 : Terms) (wf : (wfTerms k7 ts3)) ,
      (forall (c0 : (Cutoff TmVar)) (k8 : Hvl) ,
        (shifthvl_TmVar c0 k7 k8) -> (wfTerms k8 (shift_TmVar_Terms c0 ts3))))) := (ind_wfTele_Tm_Terms (fun (k7 : Hvl) (d12 : Tele) (wf : (wfTele k7 d12)) =>
    (forall (c0 : (Cutoff TmVar)) (k8 : Hvl) ,
      (shifthvl_TmVar c0 k7 k8) -> (wfTele k8 (shift_TmVar_Tele c0 d12)))) (fun (k7 : Hvl) (s4 : Tm) (wf : (wfTm k7 s4)) =>
    (forall (c0 : (Cutoff TmVar)) (k8 : Hvl) ,
      (shifthvl_TmVar c0 k7 k8) -> (wfTm k8 (shift_TmVar_Tm c0 s4)))) (fun (k7 : Hvl) (ts3 : Terms) (wf : (wfTerms k7 ts3)) =>
    (forall (c0 : (Cutoff TmVar)) (k8 : Hvl) ,
      (shifthvl_TmVar c0 k7 k8) -> (wfTerms k8 (shift_TmVar_Terms c0 ts3)))) (fun (k7 : Hvl) (c0 : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c0 k7 k8)) =>
    (wfTele_TNil k8)) (fun (k7 : Hvl) (T : Tm) (wf : (wfTm k7 T)) IHT (d : Tele) (wf0 : (wfTele (HS TmVar k7) d)) IHd (c0 : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c0 k7 k8)) =>
    (wfTele_TCons k8 (IHT c0 k8 (weaken_shifthvl_TmVar H0 ins)) (IHd (CS c0) (HS TmVar k8) (weaken_shifthvl_TmVar (HS TmVar H0) ins)))) (fun (k7 : Hvl) (x4 : (Index TmVar)) (wfi : (wfindex k7 x4)) (c0 : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c0 k7 k8)) =>
    (wfTm_Var k8 _ (shift_TmVar__wfindex_TmVar c0 k7 k8 ins x4 wfi))) (fun (k7 : Hvl) (d : Tele) (wf : (wfTele k7 d)) IHd (t : Tm) (wf0 : (wfTm (appendHvl k7 (appendHvl H0 (bind d))) t)) IHt (c0 : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c0 k7 k8)) =>
    (wfTm_Abs k8 (IHd c0 k8 (weaken_shifthvl_TmVar H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k8) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _)))) eq_refl (IHt (weakenCutoffTmVar c0 (appendHvl H0 (bind d))) (appendHvl k8 (appendHvl H0 (bind d))) (weaken_shifthvl_TmVar (appendHvl H0 (bind d)) ins))))) (fun (k7 : Hvl) (d : Tele) (wf : (wfTele k7 d)) IHd (T : Tm) (wf0 : (wfTm (appendHvl k7 (appendHvl H0 (bind d))) T)) IHT (c0 : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c0 k7 k8)) =>
    (wfTm_Pi k8 (IHd c0 k8 (weaken_shifthvl_TmVar H0 ins)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k8) (f_equal2 appendHvl (eq_refl H0) (eq_sym (stability_shift_TmVar__bind _ _)))) eq_refl (IHT (weakenCutoffTmVar c0 (appendHvl H0 (bind d))) (appendHvl k8 (appendHvl H0 (bind d))) (weaken_shifthvl_TmVar (appendHvl H0 (bind d)) ins))))) (fun (k7 : Hvl) (t : Tm) (wf : (wfTm k7 t)) IHt (ts : Terms) (wf0 : (wfTerms k7 ts)) IHts (c0 : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c0 k7 k8)) =>
    (wfTm_App k8 (IHt c0 k8 (weaken_shifthvl_TmVar H0 ins)) (IHts c0 k8 (weaken_shifthvl_TmVar H0 ins)))) (fun (k7 : Hvl) (c0 : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c0 k7 k8)) =>
    (wfTerms_Nil k8)) (fun (k7 : Hvl) (t : Tm) (wf : (wfTm k7 t)) IHt (ts : Terms) (wf0 : (wfTerms k7 ts)) IHts (c0 : (Cutoff TmVar)) (k8 : Hvl) (ins : (shifthvl_TmVar c0 k7 k8)) =>
    (wfTerms_Cons k8 (IHt c0 k8 (weaken_shifthvl_TmVar H0 ins)) (IHts c0 k8 (weaken_shifthvl_TmVar H0 ins))))).
  Lemma shift_TmVar__wfTele (k7 : Hvl) :
    (forall (d12 : Tele) (wf : (wfTele k7 d12)) ,
      (forall (c0 : (Cutoff TmVar)) (k8 : Hvl) ,
        (shifthvl_TmVar c0 k7 k8) -> (wfTele k8 (shift_TmVar_Tele c0 d12)))).
  Proof.
    pose proof ((shift_TmVar__wfTele_Tm_Terms k7)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_TmVar__wfTm (k7 : Hvl) :
    (forall (s4 : Tm) (wf0 : (wfTm k7 s4)) ,
      (forall (c1 : (Cutoff TmVar)) (k9 : Hvl) ,
        (shifthvl_TmVar c1 k7 k9) -> (wfTm k9 (shift_TmVar_Tm c1 s4)))).
  Proof.
    pose proof ((shift_TmVar__wfTele_Tm_Terms k7)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_TmVar__wfTerms (k7 : Hvl) :
    (forall (ts3 : Terms) (wf1 : (wfTerms k7 ts3)) ,
      (forall (c2 : (Cutoff TmVar)) (k10 : Hvl) ,
        (shifthvl_TmVar c2 k7 k10) -> (wfTerms k10 (shift_TmVar_Terms c2 ts3)))).
  Proof.
    pose proof ((shift_TmVar__wfTele_Tm_Terms k7)).
    destruct_conjs .
    easy .
  Qed.
  Fixpoint weaken_wfTele (k7 : Hvl) {struct k7} :
  (forall (k8 : Hvl) (d12 : Tele) (wf : (wfTele k8 d12)) ,
    (wfTele (appendHvl k8 k7) (weakenTele d12 k7))) :=
    match k7 return (forall (k8 : Hvl) (d12 : Tele) (wf : (wfTele k8 d12)) ,
      (wfTele (appendHvl k8 k7) (weakenTele d12 k7))) with
      | (H0) => (fun (k8 : Hvl) (d12 : Tele) (wf : (wfTele k8 d12)) =>
        wf)
      | (HS TmVar k7) => (fun (k8 : Hvl) (d12 : Tele) (wf : (wfTele k8 d12)) =>
        (shift_TmVar__wfTele (appendHvl k8 k7) (weakenTele d12 k7) (weaken_wfTele k7 k8 d12 wf) C0 (HS TmVar (appendHvl k8 k7)) (shifthvl_TmVar_here (appendHvl k8 k7))))
    end.
  Fixpoint weaken_wfTm (k7 : Hvl) {struct k7} :
  (forall (k8 : Hvl) (s4 : Tm) (wf : (wfTm k8 s4)) ,
    (wfTm (appendHvl k8 k7) (weakenTm s4 k7))) :=
    match k7 return (forall (k8 : Hvl) (s4 : Tm) (wf : (wfTm k8 s4)) ,
      (wfTm (appendHvl k8 k7) (weakenTm s4 k7))) with
      | (H0) => (fun (k8 : Hvl) (s4 : Tm) (wf : (wfTm k8 s4)) =>
        wf)
      | (HS TmVar k7) => (fun (k8 : Hvl) (s4 : Tm) (wf : (wfTm k8 s4)) =>
        (shift_TmVar__wfTm (appendHvl k8 k7) (weakenTm s4 k7) (weaken_wfTm k7 k8 s4 wf) C0 (HS TmVar (appendHvl k8 k7)) (shifthvl_TmVar_here (appendHvl k8 k7))))
    end.
  Fixpoint weaken_wfTerms (k7 : Hvl) {struct k7} :
  (forall (k8 : Hvl) (ts3 : Terms) (wf : (wfTerms k8 ts3)) ,
    (wfTerms (appendHvl k8 k7) (weakenTerms ts3 k7))) :=
    match k7 return (forall (k8 : Hvl) (ts3 : Terms) (wf : (wfTerms k8 ts3)) ,
      (wfTerms (appendHvl k8 k7) (weakenTerms ts3 k7))) with
      | (H0) => (fun (k8 : Hvl) (ts3 : Terms) (wf : (wfTerms k8 ts3)) =>
        wf)
      | (HS TmVar k7) => (fun (k8 : Hvl) (ts3 : Terms) (wf : (wfTerms k8 ts3)) =>
        (shift_TmVar__wfTerms (appendHvl k8 k7) (weakenTerms ts3 k7) (weaken_wfTerms k7 k8 ts3 wf) C0 (HS TmVar (appendHvl k8 k7)) (shifthvl_TmVar_here (appendHvl k8 k7))))
    end.
End ShiftWellFormed.
Lemma wfTele_cast  :
  (forall (k7 : Hvl) (d12 : Tele) (k8 : Hvl) (d13 : Tele) ,
    (k7 = k8) -> (d12 = d13) -> (wfTele k7 d12) -> (wfTele k8 d13)).
Proof.
  congruence .
Qed.
Lemma wfTm_cast  :
  (forall (k7 : Hvl) (s4 : Tm) (k8 : Hvl) (s5 : Tm) ,
    (k7 = k8) -> (s4 = s5) -> (wfTm k7 s4) -> (wfTm k8 s5)).
Proof.
  congruence .
Qed.
Lemma wfTerms_cast  :
  (forall (k7 : Hvl) (ts3 : Terms) (k8 : Hvl) (ts4 : Terms) ,
    (k7 = k8) -> (ts3 = ts4) -> (wfTerms k7 ts3) -> (wfTerms k8 ts4)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_TmVar__wfindex_TmVar : infra.
 Hint Resolve shift_TmVar__wfindex_TmVar : shift.
 Hint Resolve shift_TmVar__wfindex_TmVar : shift_wf.
 Hint Resolve shift_TmVar__wfindex_TmVar : wf.
 Hint Resolve shift_TmVar__wfTele shift_TmVar__wfTerms shift_TmVar__wfTm : infra.
 Hint Resolve shift_TmVar__wfTele shift_TmVar__wfTerms shift_TmVar__wfTm : shift.
 Hint Resolve shift_TmVar__wfTele shift_TmVar__wfTerms shift_TmVar__wfTm : shift_wf.
 Hint Resolve shift_TmVar__wfTele shift_TmVar__wfTerms shift_TmVar__wfTm : wf.
 Hint Constructors shifthvl_TmVar : infra.
 Hint Constructors shifthvl_TmVar : shift.
 Hint Constructors shifthvl_TmVar : shift_wf.
 Hint Constructors shifthvl_TmVar : wf.
 Hint Resolve weaken_shifthvl_TmVar : infra.
 Hint Resolve weaken_shifthvl_TmVar : shift.
 Hint Resolve weaken_shifthvl_TmVar : shift_wf.
 Hint Resolve weaken_shifthvl_TmVar : weaken.
 Hint Resolve weaken_shifthvl_TmVar : wf.
Section SubstWellFormed.
  Inductive substhvl_TmVar (k7 : Hvl) : (forall (d12 : (Trace TmVar)) (k8 : Hvl) (k9 : Hvl) ,
    Prop) :=
    | substhvl_TmVar_here :
        (substhvl_TmVar k7 X0 (HS TmVar k7) k7)
    | substhvl_TmVar_there_TmVar
        {d12 : (Trace TmVar)} {k8 : Hvl}
        {k9 : Hvl} :
        (substhvl_TmVar k7 d12 k8 k9) -> (substhvl_TmVar k7 (XS TmVar d12) (HS TmVar k8) (HS TmVar k9)).
  Lemma weaken_substhvl_TmVar  :
    (forall {k8 : Hvl} (k7 : Hvl) {d12 : (Trace TmVar)} {k9 : Hvl} {k10 : Hvl} ,
      (substhvl_TmVar k8 d12 k9 k10) -> (substhvl_TmVar k8 (weakenTrace d12 k7) (appendHvl k9 k7) (appendHvl k10 k7))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_TmVar_wfindex_TmVar {k7 : Hvl} {s4 : Tm} (wft : (wfTm k7 s4)) :
    (forall {d12 : (Trace TmVar)} {k8 : Hvl} {k9 : Hvl} ,
      (substhvl_TmVar k7 d12 k8 k9) -> (forall {x4 : (Index TmVar)} ,
        (wfindex k8 x4) -> (wfTm k9 (subst_TmVar_Index d12 s4 x4)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Definition substhvl_TmVar_wfTele_Tm_Terms {k7 : Hvl} {s4 : Tm} (wf : (wfTm k7 s4)) : (forall (k8 : Hvl) ,
    (forall (d12 : Tele) (wf0 : (wfTele k8 d12)) ,
      (forall {d13 : (Trace TmVar)} {k9 : Hvl} ,
        (substhvl_TmVar k7 d13 k8 k9) -> (wfTele k9 (subst_TmVar_Tele d13 s4 d12)))) /\
    (forall (s5 : Tm) (wf0 : (wfTm k8 s5)) ,
      (forall {d12 : (Trace TmVar)} {k9 : Hvl} ,
        (substhvl_TmVar k7 d12 k8 k9) -> (wfTm k9 (subst_TmVar_Tm d12 s4 s5)))) /\
    (forall (ts3 : Terms) (wf0 : (wfTerms k8 ts3)) ,
      (forall {d12 : (Trace TmVar)} {k9 : Hvl} ,
        (substhvl_TmVar k7 d12 k8 k9) -> (wfTerms k9 (subst_TmVar_Terms d12 s4 ts3))))) := (ind_wfTele_Tm_Terms (fun (k8 : Hvl) (d12 : Tele) (wf0 : (wfTele k8 d12)) =>
    (forall {d13 : (Trace TmVar)} {k9 : Hvl} ,
      (substhvl_TmVar k7 d13 k8 k9) -> (wfTele k9 (subst_TmVar_Tele d13 s4 d12)))) (fun (k8 : Hvl) (s5 : Tm) (wf0 : (wfTm k8 s5)) =>
    (forall {d12 : (Trace TmVar)} {k9 : Hvl} ,
      (substhvl_TmVar k7 d12 k8 k9) -> (wfTm k9 (subst_TmVar_Tm d12 s4 s5)))) (fun (k8 : Hvl) (ts3 : Terms) (wf0 : (wfTerms k8 ts3)) =>
    (forall {d12 : (Trace TmVar)} {k9 : Hvl} ,
      (substhvl_TmVar k7 d12 k8 k9) -> (wfTerms k9 (subst_TmVar_Terms d12 s4 ts3)))) (fun (k8 : Hvl) {d12 : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d12 k8 k9)) =>
    (wfTele_TNil k9)) (fun (k8 : Hvl) (T : Tm) (wf0 : (wfTm k8 T)) IHT (d : Tele) (wf1 : (wfTele (HS TmVar k8) d)) IHd {d12 : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d12 k8 k9)) =>
    (wfTele_TCons k9 (IHT (weakenTrace d12 H0) k9 (weaken_substhvl_TmVar H0 del)) (IHd (weakenTrace d12 (HS TmVar H0)) (HS TmVar k9) (weaken_substhvl_TmVar (HS TmVar H0) del)))) (fun (k8 : Hvl) {x4 : (Index TmVar)} (wfi : (wfindex k8 x4)) {d12 : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d12 k8 k9)) =>
    (substhvl_TmVar_wfindex_TmVar wf del wfi)) (fun (k8 : Hvl) (d : Tele) (wf0 : (wfTele k8 d)) IHd (t : Tm) (wf1 : (wfTm (appendHvl k8 (appendHvl H0 (bind d))) t)) IHt {d12 : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d12 k8 k9)) =>
    (wfTm_Abs k9 (IHd (weakenTrace d12 H0) k9 (weaken_substhvl_TmVar H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k9) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0)))) eq_refl (IHt (weakenTrace d12 (appendHvl H0 (bind d))) (appendHvl k9 (appendHvl H0 (bind d))) (weaken_substhvl_TmVar (appendHvl H0 (bind d)) del))))) (fun (k8 : Hvl) (d : Tele) (wf0 : (wfTele k8 d)) IHd (T : Tm) (wf1 : (wfTm (appendHvl k8 (appendHvl H0 (bind d))) T)) IHT {d12 : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d12 k8 k9)) =>
    (wfTm_Pi k9 (IHd (weakenTrace d12 H0) k9 (weaken_substhvl_TmVar H0 del)) (eq_ind2 wfTm (f_equal2 appendHvl (eq_refl k9) (f_equal2 appendHvl (eq_refl H0) (f_equal2 appendHvl (eq_sym (stability_subst_TmVar__bind _ _ _)) (eq_refl H0)))) eq_refl (IHT (weakenTrace d12 (appendHvl H0 (bind d))) (appendHvl k9 (appendHvl H0 (bind d))) (weaken_substhvl_TmVar (appendHvl H0 (bind d)) del))))) (fun (k8 : Hvl) (t : Tm) (wf0 : (wfTm k8 t)) IHt (ts : Terms) (wf1 : (wfTerms k8 ts)) IHts {d12 : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d12 k8 k9)) =>
    (wfTm_App k9 (IHt (weakenTrace d12 H0) k9 (weaken_substhvl_TmVar H0 del)) (IHts (weakenTrace d12 H0) k9 (weaken_substhvl_TmVar H0 del)))) (fun (k8 : Hvl) {d12 : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d12 k8 k9)) =>
    (wfTerms_Nil k9)) (fun (k8 : Hvl) (t : Tm) (wf0 : (wfTm k8 t)) IHt (ts : Terms) (wf1 : (wfTerms k8 ts)) IHts {d12 : (Trace TmVar)} {k9 : Hvl} (del : (substhvl_TmVar k7 d12 k8 k9)) =>
    (wfTerms_Cons k9 (IHt (weakenTrace d12 H0) k9 (weaken_substhvl_TmVar H0 del)) (IHts (weakenTrace d12 H0) k9 (weaken_substhvl_TmVar H0 del))))).
  Lemma substhvl_TmVar_wfTele {k7 : Hvl} {s4 : Tm} (wf : (wfTm k7 s4)) (k8 : Hvl) (d12 : Tele) (wf0 : (wfTele k8 d12)) :
    (forall {d13 : (Trace TmVar)} {k9 : Hvl} ,
      (substhvl_TmVar k7 d13 k8 k9) -> (wfTele k9 (subst_TmVar_Tele d13 s4 d12))).
  Proof.
    apply ((substhvl_TmVar_wfTele_Tm_Terms wf k8)).
    auto .
  Qed.
  Lemma substhvl_TmVar_wfTm {k7 : Hvl} {s4 : Tm} (wf : (wfTm k7 s4)) (k8 : Hvl) (s5 : Tm) (wf1 : (wfTm k8 s5)) :
    (forall {d14 : (Trace TmVar)} {k10 : Hvl} ,
      (substhvl_TmVar k7 d14 k8 k10) -> (wfTm k10 (subst_TmVar_Tm d14 s4 s5))).
  Proof.
    apply ((substhvl_TmVar_wfTele_Tm_Terms wf k8)).
    auto .
  Qed.
  Lemma substhvl_TmVar_wfTerms {k7 : Hvl} {s4 : Tm} (wf : (wfTm k7 s4)) (k8 : Hvl) (ts3 : Terms) (wf2 : (wfTerms k8 ts3)) :
    (forall {d15 : (Trace TmVar)} {k11 : Hvl} ,
      (substhvl_TmVar k7 d15 k8 k11) -> (wfTerms k11 (subst_TmVar_Terms d15 s4 ts3))).
  Proof.
    apply ((substhvl_TmVar_wfTele_Tm_Terms wf k8)).
    auto .
  Qed.
End SubstWellFormed.
 Hint Resolve substhvl_TmVar_wfindex_TmVar : infra.
 Hint Resolve substhvl_TmVar_wfindex_TmVar : subst.
 Hint Resolve substhvl_TmVar_wfindex_TmVar : subst_wf.
 Hint Resolve substhvl_TmVar_wfindex_TmVar : wf.
 Hint Resolve substhvl_TmVar_wfTele substhvl_TmVar_wfTerms substhvl_TmVar_wfTm : infra.
 Hint Resolve substhvl_TmVar_wfTele substhvl_TmVar_wfTerms substhvl_TmVar_wfTm : subst.
 Hint Resolve substhvl_TmVar_wfTele substhvl_TmVar_wfTerms substhvl_TmVar_wfTm : subst_wf.
 Hint Resolve substhvl_TmVar_wfTele substhvl_TmVar_wfTerms substhvl_TmVar_wfTm : wf.
 Hint Constructors substhvl_TmVar : infra.
 Hint Constructors substhvl_TmVar : subst.
 Hint Constructors substhvl_TmVar : subst_wf.
 Hint Constructors substhvl_TmVar : wf.
Fixpoint subhvl_TmVar (k7 : Hvl) {struct k7} :
Prop :=
  match k7 with
    | (H0) => True
    | (HS a k7) => match a with
      | (TmVar) => (subhvl_TmVar k7)
    end
  end.
Lemma subhvl_TmVar_append  :
  (forall (k7 : Hvl) (k8 : Hvl) ,
    (subhvl_TmVar k7) -> (subhvl_TmVar k8) -> (subhvl_TmVar (appendHvl k7 k8))).
Proof.
  needleGenericSubHvlAppend .
Qed.
 Hint Resolve subhvl_TmVar_append : infra.
 Hint Resolve subhvl_TmVar_append : wf.
Section Context.
  
End Context.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    
  End SubstEnvAppendEnv.
  Lemma weakenTele_append  :
    (forall (d12 : Tele) (k7 : Hvl) (k8 : Hvl) ,
      ((weakenTele (weakenTele d12 k7) k8) = (weakenTele d12 (appendHvl k7 k8)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTm_append  :
    (forall (s4 : Tm) (k7 : Hvl) (k8 : Hvl) ,
      ((weakenTm (weakenTm s4 k7) k8) = (weakenTm s4 (appendHvl k7 k8)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenTerms_append  :
    (forall (ts3 : Terms) (k7 : Hvl) (k8 : Hvl) ,
      ((weakenTerms (weakenTerms ts3 k7) k8) = (weakenTerms ts3 (appendHvl k7 k8)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    
  End Lookups.
End ContextStuff.
 Hint Constructors wfTele wfTerms wfTm : infra.
 Hint Constructors wfTele wfTerms wfTm : wf.
 Hint Extern 10 ((wfTele _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTerms _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfTm _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfTele _ _)) => match goal with
  | H20 : (wfTele _ (TNil)) |- _ => inversion H20; subst; clear H20
  | H20 : (wfTele _ (TCons _ _)) |- _ => inversion H20; subst; clear H20
end : infra wf.
 Hint Extern 2 ((wfTm _ _)) => match goal with
  | H20 : (wfTm _ (Var _)) |- _ => inversion H20; subst; clear H20
  | H20 : (wfTm _ (Abs _ _)) |- _ => inversion H20; subst; clear H20
  | H20 : (wfTm _ (Pi _ _)) |- _ => inversion H20; subst; clear H20
  | H20 : (wfTm _ (App _ _)) |- _ => inversion H20; subst; clear H20
end : infra wf.
 Hint Extern 2 ((wfTerms _ _)) => match goal with
  | H20 : (wfTerms _ (Nil)) |- _ => inversion H20; subst; clear H20
  | H20 : (wfTerms _ (Cons _ _)) |- _ => inversion H20; subst; clear H20
end : infra wf.
Fixpoint size_Tele (d7 : Tele) {struct d7} :
nat :=
  match d7 with
    | (TNil) => 1
    | (TCons T1 d8) => (plus 1 (plus (size_Tm T1) (size_Tele d8)))
  end
with size_Tm (s : Tm) {struct s} :
nat :=
  match s with
    | (Var x4) => 1
    | (Abs d7 t3) => (plus 1 (plus (size_Tele d7) (size_Tm t3)))
    | (Pi d8 T1) => (plus 1 (plus (size_Tele d8) (size_Tm T1)))
    | (App t4 ts1) => (plus 1 (plus (size_Tm t4) (size_Terms ts1)))
  end
with size_Terms (ts1 : Terms) {struct ts1} :
nat :=
  match ts1 with
    | (Nil) => 1
    | (Cons t3 ts2) => (plus 1 (plus (size_Tm t3) (size_Terms ts2)))
  end.
Fixpoint shift_TmVar__size_Tele (d10 : Tele) (c0 : (Cutoff TmVar)) {struct d10} :
((size_Tele (shift_TmVar_Tele c0 d10)) = (size_Tele d10)) :=
  match d10 return ((size_Tele (shift_TmVar_Tele c0 d10)) = (size_Tele d10)) with
    | (TNil) => eq_refl
    | (TCons T d) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm T c0) (shift_TmVar__size_Tele d (CS c0))))
  end
with shift_TmVar__size_Tm (s0 : Tm) (c0 : (Cutoff TmVar)) {struct s0} :
((size_Tm (shift_TmVar_Tm c0 s0)) = (size_Tm s0)) :=
  match s0 return ((size_Tm (shift_TmVar_Tm c0 s0)) = (size_Tm s0)) with
    | (Var _) => eq_refl
    | (Abs d t) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tele d c0) (shift_TmVar__size_Tm t (weakenCutoffTmVar c0 (appendHvl H0 (bind d))))))
    | (Pi d T) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tele d c0) (shift_TmVar__size_Tm T (weakenCutoffTmVar c0 (appendHvl H0 (bind d))))))
    | (App t ts) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t c0) (shift_TmVar__size_Terms ts c0)))
  end
with shift_TmVar__size_Terms (ts1 : Terms) (c0 : (Cutoff TmVar)) {struct ts1} :
((size_Terms (shift_TmVar_Terms c0 ts1)) = (size_Terms ts1)) :=
  match ts1 return ((size_Terms (shift_TmVar_Terms c0 ts1)) = (size_Terms ts1)) with
    | (Nil) => eq_refl
    | (Cons t ts) => (f_equal2 plus eq_refl (f_equal2 plus (shift_TmVar__size_Tm t c0) (shift_TmVar__size_Terms ts c0)))
  end.
 Hint Rewrite shift_TmVar__size_Tele shift_TmVar__size_Terms shift_TmVar__size_Tm : interaction.
 Hint Rewrite shift_TmVar__size_Tele shift_TmVar__size_Terms shift_TmVar__size_Tm : shift_size.
Lemma weaken_size_Tele  :
  (forall (k : Hvl) (d10 : Tele) ,
    ((size_Tele (weakenTele d10 k)) = (size_Tele d10))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Terms  :
  (forall (k : Hvl) (ts1 : Terms) ,
    ((size_Terms (weakenTerms ts1 k)) = (size_Terms ts1))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_Tm  :
  (forall (k : Hvl) (s0 : Tm) ,
    ((size_Tm (weakenTm s0 k)) = (size_Tm s0))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_Tele weaken_size_Terms weaken_size_Tm : interaction.
 Hint Rewrite weaken_size_Tele weaken_size_Terms weaken_size_Tm : weaken_size.
 Hint Rewrite <- weakenCutoffTmVar_append weakenTrace_append weakenTele_append weakenTerms_append weakenTm_append appendHvl_assoc : interaction.