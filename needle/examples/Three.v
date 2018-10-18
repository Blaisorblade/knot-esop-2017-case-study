Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export Needle.

Local Set Asymmetric Patterns.

Section Namespace.
  Inductive Namespace : Type :=
    | A 
    | B 
    | Z .
  Lemma eq_namespace_dec (a3 : Namespace) (b3 : Namespace) :
    (sumbool (a3 = b3) (not (a3 = b3))).
  Proof.
    decide equality .
  Defined.
End Namespace.

Section HVarlist.
  Inductive Hvl : Type :=
    | H0 
    | HS (a3 : Namespace) (k : Hvl).
  
  Fixpoint appendHvl (k : Hvl) (k0 : Hvl) {struct k0} :
  Hvl :=
    match k0 with
      | (H0) => k
      | (HS a3 k0) => (HS a3 (appendHvl k k0))
    end.
  
  Lemma appendHvl_assoc  :
    (forall (k : Hvl) (k0 : Hvl) (k1 : Hvl) ,
      ((appendHvl (appendHvl k k0) k1) = (appendHvl k (appendHvl k0 k1)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End HVarlist.

Section Index.
  Inductive Index (a3 : Namespace) : Type :=
    | I0 
    | IS : (Index a3) -> (Index a3).
  
  Global Arguments I0 [a3] .
  Global Arguments IS [a3] _ .
  
  Lemma eq_index_dec {a3 : Namespace} (i : (Index a3)) (j : (Index a3)) :
    (sumbool (i = j) (not (i = j))).
  Proof.
    decide equality .
  Qed.
  
  Fixpoint weakenIndexA (a4 : (Index A)) (k : Hvl) {struct k} :
  (Index A) :=
    match k with
      | (H0) => a4
      | (HS a3 k) => match a3 with
        | (A) => (IS (weakenIndexA a4 k))
        | _ => (weakenIndexA a4 k)
      end
    end.
  Fixpoint weakenIndexB (b3 : (Index B)) (k : Hvl) {struct k} :
  (Index B) :=
    match k with
      | (H0) => b3
      | (HS a3 k) => match a3 with
        | (B) => (IS (weakenIndexB b3 k))
        | _ => (weakenIndexB b3 k)
      end
    end.
  Fixpoint weakenIndexZ (z0 : (Index Z)) (k : Hvl) {struct k} :
  (Index Z) :=
    match k with
      | (H0) => z0
      | (HS a3 k) => match a3 with
        | (Z) => (IS (weakenIndexZ z0 k))
        | _ => (weakenIndexZ z0 k)
      end
    end.
  Lemma weakenIndexA_append  :
    (forall (a3 : (Index A)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexA (weakenIndexA a3 k) k0) = (weakenIndexA a3 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexB_append  :
    (forall (b3 : (Index B)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexB (weakenIndexB b3 k) k0) = (weakenIndexB b3 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenIndexZ_append  :
    (forall (z0 : (Index Z)) (k : Hvl) (k0 : Hvl) ,
      ((weakenIndexZ (weakenIndexZ z0 k) k0) = (weakenIndexZ z0 (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
End Index.

Section Terms.
  Inductive AA : Set :=
    | avar (a : (Index A))
    | arec (zz : ZZ)
  with ZZ : Set :=
    | zvar (z : (Index Z))
    | aabs (aa : AA)
    | babs (bb : BB)
  with BB : Set :=
    | bvar (b : (Index B))
    | brec (zz : ZZ).
  Scheme ind_AA := Induction for AA Sort Prop
  with ind_ZZ := Induction for ZZ Sort Prop
  with ind_BB := Induction for BB Sort Prop.
  Combined Scheme ind_AA_ZZ_BB from ind_AA, ind_ZZ, ind_BB.
End Terms.

Section Functions.
  
End Functions.

Section Shift.
  Inductive Cutoff (a3 : Namespace) : Type :=
    | C0 
    | CS :
        (Cutoff a3) -> (Cutoff a3).
  
  Global Arguments C0 {a3} .
  Global Arguments CS {a3} _ .
  Fixpoint weakenCutoffA (c : (Cutoff A)) (k : Hvl) {struct k} :
  (Cutoff A) :=
    match k with
      | (H0) => c
      | (HS a3 k) => match a3 with
        | (A) => (CS (weakenCutoffA c k))
        | _ => (weakenCutoffA c k)
      end
    end.
  Fixpoint weakenCutoffB (c : (Cutoff B)) (k : Hvl) {struct k} :
  (Cutoff B) :=
    match k with
      | (H0) => c
      | (HS a3 k) => match a3 with
        | (B) => (CS (weakenCutoffB c k))
        | _ => (weakenCutoffB c k)
      end
    end.
  Fixpoint weakenCutoffZ (c : (Cutoff Z)) (k : Hvl) {struct k} :
  (Cutoff Z) :=
    match k with
      | (H0) => c
      | (HS a3 k) => match a3 with
        | (Z) => (CS (weakenCutoffZ c k))
        | _ => (weakenCutoffZ c k)
      end
    end.
  
  Lemma weakenCutoffA_append  :
    (forall (c : (Cutoff A)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffA (weakenCutoffA c k) k0) = (weakenCutoffA c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenCutoffB_append  :
    (forall (c : (Cutoff B)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffB (weakenCutoffB c k) k0) = (weakenCutoffB c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenCutoffZ_append  :
    (forall (c : (Cutoff Z)) (k : Hvl) (k0 : Hvl) ,
      ((weakenCutoffZ (weakenCutoffZ c k) k0) = (weakenCutoffZ c (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint shift_A_Index (c : (Cutoff A)) (a3 : (Index A)) {struct c} :
  (Index A) :=
    match c with
      | (C0) => (IS a3)
      | (CS c) => match a3 with
        | (I0) => I0
        | (IS a3) => (IS (shift_A_Index c a3))
      end
    end.
  Fixpoint shift_B_Index (c : (Cutoff B)) (b3 : (Index B)) {struct c} :
  (Index B) :=
    match c with
      | (C0) => (IS b3)
      | (CS c) => match b3 with
        | (I0) => I0
        | (IS b3) => (IS (shift_B_Index c b3))
      end
    end.
  Fixpoint shift_Z_Index (c : (Cutoff Z)) (z0 : (Index Z)) {struct c} :
  (Index Z) :=
    match c with
      | (C0) => (IS z0)
      | (CS c) => match z0 with
        | (I0) => I0
        | (IS z0) => (IS (shift_Z_Index c z0))
      end
    end.
  Fixpoint shift_A_AA (c : (Cutoff A)) (aa0 : AA) {struct aa0} :
  AA :=
    match aa0 with
      | (avar a3) => (avar (shift_A_Index c a3))
      | (arec zz1) => (arec (shift_A_ZZ c zz1))
    end
  with shift_A_ZZ (c : (Cutoff A)) (zz1 : ZZ) {struct zz1} :
  ZZ :=
    match zz1 with
      | (zvar z0) => (zvar z0)
      | (aabs aa0) => (aabs (shift_A_AA (CS c) aa0))
      | (babs bb0) => (babs (shift_A_BB c bb0))
    end
  with shift_A_BB (c : (Cutoff A)) (bb0 : BB) {struct bb0} :
  BB :=
    match bb0 with
      | (bvar b3) => (bvar b3)
      | (brec zz1) => (brec (shift_A_ZZ c zz1))
    end.
  Fixpoint shift_B_AA (c : (Cutoff B)) (aa0 : AA) {struct aa0} :
  AA :=
    match aa0 with
      | (avar a3) => (avar a3)
      | (arec zz1) => (arec (shift_B_ZZ c zz1))
    end
  with shift_B_ZZ (c : (Cutoff B)) (zz1 : ZZ) {struct zz1} :
  ZZ :=
    match zz1 with
      | (zvar z0) => (zvar z0)
      | (aabs aa0) => (aabs (shift_B_AA c aa0))
      | (babs bb0) => (babs (shift_B_BB (CS c) bb0))
    end
  with shift_B_BB (c : (Cutoff B)) (bb0 : BB) {struct bb0} :
  BB :=
    match bb0 with
      | (bvar b3) => (bvar (shift_B_Index c b3))
      | (brec zz1) => (brec (shift_B_ZZ c zz1))
    end.
  Fixpoint shift_Z_AA (c : (Cutoff Z)) (aa0 : AA) {struct aa0} :
  AA :=
    match aa0 with
      | (avar a3) => (avar a3)
      | (arec zz1) => (arec (shift_Z_ZZ c zz1))
    end
  with shift_Z_ZZ (c : (Cutoff Z)) (zz1 : ZZ) {struct zz1} :
  ZZ :=
    match zz1 with
      | (zvar z0) => (zvar (shift_Z_Index c z0))
      | (aabs aa0) => (aabs (shift_Z_AA c aa0))
      | (babs bb0) => (babs (shift_Z_BB c bb0))
    end
  with shift_Z_BB (c : (Cutoff Z)) (bb0 : BB) {struct bb0} :
  BB :=
    match bb0 with
      | (bvar b3) => (bvar b3)
      | (brec zz1) => (brec (shift_Z_ZZ c zz1))
    end.
End Shift.

Section Weaken.
  Fixpoint weakenAA (aa0 : AA) (k : Hvl) {struct k} :
  AA :=
    match k with
      | (H0) => aa0
      | (HS A k) => (shift_A_AA C0 (weakenAA aa0 k))
      | (HS B k) => (shift_B_AA C0 (weakenAA aa0 k))
      | (HS Z k) => (shift_Z_AA C0 (weakenAA aa0 k))
    end.
  Fixpoint weakenZZ (zz1 : ZZ) (k : Hvl) {struct k} :
  ZZ :=
    match k with
      | (H0) => zz1
      | (HS A k) => (shift_A_ZZ C0 (weakenZZ zz1 k))
      | (HS B k) => (shift_B_ZZ C0 (weakenZZ zz1 k))
      | (HS Z k) => (shift_Z_ZZ C0 (weakenZZ zz1 k))
    end.
  Fixpoint weakenBB (bb0 : BB) (k : Hvl) {struct k} :
  BB :=
    match k with
      | (H0) => bb0
      | (HS A k) => (shift_A_BB C0 (weakenBB bb0 k))
      | (HS B k) => (shift_B_BB C0 (weakenBB bb0 k))
      | (HS Z k) => (shift_Z_BB C0 (weakenBB bb0 k))
    end.
End Weaken.

Section Subst.
  Inductive Trace (a3 : Namespace) : Type :=
    | X0 
    | XS (b3 : Namespace)
        (T : (Trace a3)).
  
  Global Arguments X0 [a3] .
  Global Arguments XS [a3] b3 _ .
  Fixpoint weakenTrace {a3 : Namespace} (x : (Trace a3)) (k : Hvl) {struct k} :
  (Trace a3) :=
    match k with
      | (H0) => x
      | (HS b3 k) => (XS b3 (weakenTrace x k))
    end.
  Lemma weakenTrace_append (a3 : Namespace) :
    (forall (x : (Trace a3)) (k : Hvl) (k0 : Hvl) ,
      ((weakenTrace (weakenTrace x k) k0) = (weakenTrace x (appendHvl k k0)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Fixpoint subst_A_Index (d : (Trace A)) (aa0 : AA) (a3 : (Index A)) {struct d} :
  AA :=
    match d with
      | (X0) => match a3 with
        | (I0) => aa0
        | (IS a3) => (avar a3)
      end
      | (XS A d) => match a3 with
        | (I0) => (avar I0)
        | (IS a3) => (shift_A_AA C0 (subst_A_Index d aa0 a3))
      end
      | (XS B d) => (shift_B_AA C0 (subst_A_Index d aa0 a3))
      | (XS Z d) => (shift_Z_AA C0 (subst_A_Index d aa0 a3))
    end.
  Fixpoint subst_B_Index (d : (Trace B)) (bb0 : BB) (b3 : (Index B)) {struct d} :
  BB :=
    match d with
      | (X0) => match b3 with
        | (I0) => bb0
        | (IS b3) => (bvar b3)
      end
      | (XS A d) => (shift_A_BB C0 (subst_B_Index d bb0 b3))
      | (XS B d) => match b3 with
        | (I0) => (bvar I0)
        | (IS b3) => (shift_B_BB C0 (subst_B_Index d bb0 b3))
      end
      | (XS Z d) => (shift_Z_BB C0 (subst_B_Index d bb0 b3))
    end.
  Fixpoint subst_Z_Index (d : (Trace Z)) (zz1 : ZZ) (z0 : (Index Z)) {struct d} :
  ZZ :=
    match d with
      | (X0) => match z0 with
        | (I0) => zz1
        | (IS z0) => (zvar z0)
      end
      | (XS A d) => (shift_A_ZZ C0 (subst_Z_Index d zz1 z0))
      | (XS B d) => (shift_B_ZZ C0 (subst_Z_Index d zz1 z0))
      | (XS Z d) => match z0 with
        | (I0) => (zvar I0)
        | (IS z0) => (shift_Z_ZZ C0 (subst_Z_Index d zz1 z0))
      end
    end.
  Fixpoint subst_A_AA (d : (Trace A)) (aa0 : AA) (aa1 : AA) {struct aa1} :
  AA :=
    match aa1 with
      | (avar a3) => (subst_A_Index d aa0 a3)
      | (arec zz1) => (arec (subst_A_ZZ d aa0 zz1))
    end
  with subst_A_ZZ (d : (Trace A)) (aa0 : AA) (zz1 : ZZ) {struct zz1} :
  ZZ :=
    match zz1 with
      | (zvar z0) => (zvar z0)
      | (aabs aa1) => (aabs (subst_A_AA (weakenTrace d (HS A H0)) aa0 aa1))
      | (babs bb0) => (babs (subst_A_BB (weakenTrace d (HS B H0)) aa0 bb0))
    end
  with subst_A_BB (d : (Trace A)) (aa0 : AA) (bb0 : BB) {struct bb0} :
  BB :=
    match bb0 with
      | (bvar b3) => (bvar b3)
      | (brec zz1) => (brec (subst_A_ZZ d aa0 zz1))
    end.
  Fixpoint subst_B_AA (d : (Trace B)) (bb0 : BB) (aa0 : AA) {struct aa0} :
  AA :=
    match aa0 with
      | (avar a3) => (avar a3)
      | (arec zz1) => (arec (subst_B_ZZ d bb0 zz1))
    end
  with subst_B_ZZ (d : (Trace B)) (bb0 : BB) (zz1 : ZZ) {struct zz1} :
  ZZ :=
    match zz1 with
      | (zvar z0) => (zvar z0)
      | (aabs aa0) => (aabs (subst_B_AA (weakenTrace d (HS A H0)) bb0 aa0))
      | (babs bb1) => (babs (subst_B_BB (weakenTrace d (HS B H0)) bb0 bb1))
    end
  with subst_B_BB (d : (Trace B)) (bb0 : BB) (bb1 : BB) {struct bb1} :
  BB :=
    match bb1 with
      | (bvar b3) => (subst_B_Index d bb0 b3)
      | (brec zz1) => (brec (subst_B_ZZ d bb0 zz1))
    end.
  Fixpoint subst_Z_AA (d : (Trace Z)) (zz1 : ZZ) (aa0 : AA) {struct aa0} :
  AA :=
    match aa0 with
      | (avar a3) => (avar a3)
      | (arec zz2) => (arec (subst_Z_ZZ d zz1 zz2))
    end
  with subst_Z_ZZ (d : (Trace Z)) (zz1 : ZZ) (zz2 : ZZ) {struct zz2} :
  ZZ :=
    match zz2 with
      | (zvar z0) => (subst_Z_Index d zz1 z0)
      | (aabs aa0) => (aabs (subst_Z_AA (weakenTrace d (HS A H0)) zz1 aa0))
      | (babs bb0) => (babs (subst_Z_BB (weakenTrace d (HS B H0)) zz1 bb0))
    end
  with subst_Z_BB (d : (Trace Z)) (zz1 : ZZ) (bb0 : BB) {struct bb0} :
  BB :=
    match bb0 with
      | (bvar b3) => (bvar b3)
      | (brec zz2) => (brec (subst_Z_ZZ d zz1 zz2))
    end.
End Subst.

Global Hint Resolve (f_equal (shift_A_AA C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_B_AA C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_Z_AA C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_A_BB C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_B_BB C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_Z_BB C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_A_ZZ C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_B_ZZ C0)) : cong_shift0.
Global Hint Resolve (f_equal (shift_Z_ZZ C0)) : cong_shift0.
 Hint Rewrite weakenCutoffA_append weakenCutoffB_append weakenCutoffZ_append : weakencutoff_append.
 Hint Rewrite weakenTrace_append : weakentrace_append.
Section SubstShiftReflection.
  Lemma subst_A_Index0_shift_A_Index0_reflection_ind (aa0 : AA) :
    (forall (k : Hvl) (a3 : (Index A)) ,
      ((subst_A_Index (weakenTrace X0 k) aa0 (shift_A_Index (weakenCutoffA C0 k) a3)) = (avar a3))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma subst_B_Index0_shift_B_Index0_reflection_ind (bb0 : BB) :
    (forall (k : Hvl) (b3 : (Index B)) ,
      ((subst_B_Index (weakenTrace X0 k) bb0 (shift_B_Index (weakenCutoffB C0 k) b3)) = (bvar b3))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Lemma subst_Z_Index0_shift_Z_Index0_reflection_ind (zz1 : ZZ) :
    (forall (k : Hvl) (z0 : (Index Z)) ,
      ((subst_Z_Index (weakenTrace X0 k) zz1 (shift_Z_Index (weakenCutoffZ C0 k) z0)) = (zvar z0))).
  Proof.
    needleGenericSubstIndexShiftIndexReflectionInd .
  Qed.
  Fixpoint subst_A_0_shift_A_0_AA_reflection_ind (aa1 : AA) (k : Hvl) (aa0 : AA) {struct aa1} :
  ((subst_A_AA (weakenTrace X0 k) aa0 (shift_A_AA (weakenCutoffA C0 k) aa1)) = aa1) :=
    match aa1 return ((subst_A_AA (weakenTrace X0 k) aa0 (shift_A_AA (weakenCutoffA C0 k) aa1)) = aa1) with
      | (avar a3) => (subst_A_Index0_shift_A_Index0_reflection_ind aa0 k a3)
      | (arec zz1) => (f_equal arec (subst_A_0_shift_A_0_ZZ_reflection_ind zz1 k aa0))
    end
  with subst_A_0_shift_A_0_ZZ_reflection_ind (zz2 : ZZ) (k : Hvl) (aa0 : AA) {struct zz2} :
  ((subst_A_ZZ (weakenTrace X0 k) aa0 (shift_A_ZZ (weakenCutoffA C0 k) zz2)) = zz2) :=
    match zz2 return ((subst_A_ZZ (weakenTrace X0 k) aa0 (shift_A_ZZ (weakenCutoffA C0 k) zz2)) = zz2) with
      | (zvar z0) => eq_refl
      | (aabs aa2) => (f_equal aabs (eq_trans (f_equal3 subst_A_AA (weakenTrace_append A X0 k (HS A H0)) eq_refl eq_refl) (subst_A_0_shift_A_0_AA_reflection_ind aa2 (HS A k) aa0)))
      | (babs bb0) => (f_equal babs (eq_trans (f_equal3 subst_A_BB (weakenTrace_append A X0 k (HS B H0)) eq_refl eq_refl) (subst_A_0_shift_A_0_BB_reflection_ind bb0 (HS B k) aa0)))
    end
  with subst_A_0_shift_A_0_BB_reflection_ind (bb1 : BB) (k : Hvl) (aa0 : AA) {struct bb1} :
  ((subst_A_BB (weakenTrace X0 k) aa0 (shift_A_BB (weakenCutoffA C0 k) bb1)) = bb1) :=
    match bb1 return ((subst_A_BB (weakenTrace X0 k) aa0 (shift_A_BB (weakenCutoffA C0 k) bb1)) = bb1) with
      | (bvar b4) => eq_refl
      | (brec zz3) => (f_equal brec (subst_A_0_shift_A_0_ZZ_reflection_ind zz3 k aa0))
    end.
  Fixpoint subst_B_0_shift_B_0_AA_reflection_ind (aa0 : AA) (k : Hvl) (bb0 : BB) {struct aa0} :
  ((subst_B_AA (weakenTrace X0 k) bb0 (shift_B_AA (weakenCutoffB C0 k) aa0)) = aa0) :=
    match aa0 return ((subst_B_AA (weakenTrace X0 k) bb0 (shift_B_AA (weakenCutoffB C0 k) aa0)) = aa0) with
      | (avar a3) => eq_refl
      | (arec zz1) => (f_equal arec (subst_B_0_shift_B_0_ZZ_reflection_ind zz1 k bb0))
    end
  with subst_B_0_shift_B_0_ZZ_reflection_ind (zz2 : ZZ) (k : Hvl) (bb0 : BB) {struct zz2} :
  ((subst_B_ZZ (weakenTrace X0 k) bb0 (shift_B_ZZ (weakenCutoffB C0 k) zz2)) = zz2) :=
    match zz2 return ((subst_B_ZZ (weakenTrace X0 k) bb0 (shift_B_ZZ (weakenCutoffB C0 k) zz2)) = zz2) with
      | (zvar z0) => eq_refl
      | (aabs aa1) => (f_equal aabs (eq_trans (f_equal3 subst_B_AA (weakenTrace_append B X0 k (HS A H0)) eq_refl eq_refl) (subst_B_0_shift_B_0_AA_reflection_ind aa1 (HS A k) bb0)))
      | (babs bb1) => (f_equal babs (eq_trans (f_equal3 subst_B_BB (weakenTrace_append B X0 k (HS B H0)) eq_refl eq_refl) (subst_B_0_shift_B_0_BB_reflection_ind bb1 (HS B k) bb0)))
    end
  with subst_B_0_shift_B_0_BB_reflection_ind (bb2 : BB) (k : Hvl) (bb0 : BB) {struct bb2} :
  ((subst_B_BB (weakenTrace X0 k) bb0 (shift_B_BB (weakenCutoffB C0 k) bb2)) = bb2) :=
    match bb2 return ((subst_B_BB (weakenTrace X0 k) bb0 (shift_B_BB (weakenCutoffB C0 k) bb2)) = bb2) with
      | (bvar b4) => (subst_B_Index0_shift_B_Index0_reflection_ind bb0 k b4)
      | (brec zz3) => (f_equal brec (subst_B_0_shift_B_0_ZZ_reflection_ind zz3 k bb0))
    end.
  Fixpoint subst_Z_0_shift_Z_0_AA_reflection_ind (aa0 : AA) (k : Hvl) (zz1 : ZZ) {struct aa0} :
  ((subst_Z_AA (weakenTrace X0 k) zz1 (shift_Z_AA (weakenCutoffZ C0 k) aa0)) = aa0) :=
    match aa0 return ((subst_Z_AA (weakenTrace X0 k) zz1 (shift_Z_AA (weakenCutoffZ C0 k) aa0)) = aa0) with
      | (avar a3) => eq_refl
      | (arec zz2) => (f_equal arec (subst_Z_0_shift_Z_0_ZZ_reflection_ind zz2 k zz1))
    end
  with subst_Z_0_shift_Z_0_ZZ_reflection_ind (zz3 : ZZ) (k : Hvl) (zz1 : ZZ) {struct zz3} :
  ((subst_Z_ZZ (weakenTrace X0 k) zz1 (shift_Z_ZZ (weakenCutoffZ C0 k) zz3)) = zz3) :=
    match zz3 return ((subst_Z_ZZ (weakenTrace X0 k) zz1 (shift_Z_ZZ (weakenCutoffZ C0 k) zz3)) = zz3) with
      | (zvar z0) => (subst_Z_Index0_shift_Z_Index0_reflection_ind zz1 k z0)
      | (aabs aa1) => (f_equal aabs (eq_trans (f_equal3 subst_Z_AA (weakenTrace_append Z X0 k (HS A H0)) eq_refl eq_refl) (subst_Z_0_shift_Z_0_AA_reflection_ind aa1 (HS A k) zz1)))
      | (babs bb0) => (f_equal babs (eq_trans (f_equal3 subst_Z_BB (weakenTrace_append Z X0 k (HS B H0)) eq_refl eq_refl) (subst_Z_0_shift_Z_0_BB_reflection_ind bb0 (HS B k) zz1)))
    end
  with subst_Z_0_shift_Z_0_BB_reflection_ind (bb1 : BB) (k : Hvl) (zz1 : ZZ) {struct bb1} :
  ((subst_Z_BB (weakenTrace X0 k) zz1 (shift_Z_BB (weakenCutoffZ C0 k) bb1)) = bb1) :=
    match bb1 return ((subst_Z_BB (weakenTrace X0 k) zz1 (shift_Z_BB (weakenCutoffZ C0 k) bb1)) = bb1) with
      | (bvar b4) => eq_refl
      | (brec zz4) => (f_equal brec (subst_Z_0_shift_Z_0_ZZ_reflection_ind zz4 k zz1))
    end.
  Definition subst_A_AA0_shift_A_AA0_reflection (aa1 : AA) : (forall (aa0 : AA) ,
    ((subst_A_AA X0 aa0 (shift_A_AA C0 aa1)) = aa1)) := (subst_A_0_shift_A_0_AA_reflection_ind aa1 H0).
  Definition subst_A_ZZ0_shift_A_ZZ0_reflection (zz1 : ZZ) : (forall (aa0 : AA) ,
    ((subst_A_ZZ X0 aa0 (shift_A_ZZ C0 zz1)) = zz1)) := (subst_A_0_shift_A_0_ZZ_reflection_ind zz1 H0).
  Definition subst_A_BB0_shift_A_BB0_reflection (bb0 : BB) : (forall (aa0 : AA) ,
    ((subst_A_BB X0 aa0 (shift_A_BB C0 bb0)) = bb0)) := (subst_A_0_shift_A_0_BB_reflection_ind bb0 H0).
  Definition subst_B_AA0_shift_B_AA0_reflection (aa0 : AA) : (forall (bb0 : BB) ,
    ((subst_B_AA X0 bb0 (shift_B_AA C0 aa0)) = aa0)) := (subst_B_0_shift_B_0_AA_reflection_ind aa0 H0).
  Definition subst_B_ZZ0_shift_B_ZZ0_reflection (zz1 : ZZ) : (forall (bb0 : BB) ,
    ((subst_B_ZZ X0 bb0 (shift_B_ZZ C0 zz1)) = zz1)) := (subst_B_0_shift_B_0_ZZ_reflection_ind zz1 H0).
  Definition subst_B_BB0_shift_B_BB0_reflection (bb1 : BB) : (forall (bb0 : BB) ,
    ((subst_B_BB X0 bb0 (shift_B_BB C0 bb1)) = bb1)) := (subst_B_0_shift_B_0_BB_reflection_ind bb1 H0).
  Definition subst_Z_AA0_shift_Z_AA0_reflection (aa0 : AA) : (forall (zz1 : ZZ) ,
    ((subst_Z_AA X0 zz1 (shift_Z_AA C0 aa0)) = aa0)) := (subst_Z_0_shift_Z_0_AA_reflection_ind aa0 H0).
  Definition subst_Z_ZZ0_shift_Z_ZZ0_reflection (zz2 : ZZ) : (forall (zz1 : ZZ) ,
    ((subst_Z_ZZ X0 zz1 (shift_Z_ZZ C0 zz2)) = zz2)) := (subst_Z_0_shift_Z_0_ZZ_reflection_ind zz2 H0).
  Definition subst_Z_BB0_shift_Z_BB0_reflection (bb0 : BB) : (forall (zz1 : ZZ) ,
    ((subst_Z_BB X0 zz1 (shift_Z_BB C0 bb0)) = bb0)) := (subst_Z_0_shift_Z_0_BB_reflection_ind bb0 H0).
End SubstShiftReflection.
Section ShiftInteraction.
  Section ShiftIndexCommInd.
    Lemma shift_A_Index_shift_A_Index0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff A)) (a3 : (Index A)) ,
        ((shift_A_Index (weakenCutoffA (CS c) k) (shift_A_Index (weakenCutoffA C0 k) a3)) = (shift_A_Index (weakenCutoffA C0 k) (shift_A_Index (weakenCutoffA c k) a3)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma shift_B_Index_shift_B_Index0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff B)) (b3 : (Index B)) ,
        ((shift_B_Index (weakenCutoffB (CS c) k) (shift_B_Index (weakenCutoffB C0 k) b3)) = (shift_B_Index (weakenCutoffB C0 k) (shift_B_Index (weakenCutoffB c k) b3)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
    Lemma shift_Z_Index_shift_Z_Index0_comm_ind  :
      (forall (k : Hvl) (c : (Cutoff Z)) (z0 : (Index Z)) ,
        ((shift_Z_Index (weakenCutoffZ (CS c) k) (shift_Z_Index (weakenCutoffZ C0 k) z0)) = (shift_Z_Index (weakenCutoffZ C0 k) (shift_Z_Index (weakenCutoffZ c k) z0)))).
    Proof.
      needleGenericShiftIndexCommInd .
    Qed.
  End ShiftIndexCommInd.
  Section ShiftCommInd.
    Fixpoint shift_A__shift_A_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff A)) {struct aa0} :
    ((shift_A_AA (weakenCutoffA (CS c) k) (shift_A_AA (weakenCutoffA C0 k) aa0)) = (shift_A_AA (weakenCutoffA C0 k) (shift_A_AA (weakenCutoffA c k) aa0))) :=
      match aa0 return ((shift_A_AA (weakenCutoffA (CS c) k) (shift_A_AA (weakenCutoffA C0 k) aa0)) = (shift_A_AA (weakenCutoffA C0 k) (shift_A_AA (weakenCutoffA c k) aa0))) with
        | (avar a3) => (f_equal avar (shift_A_Index_shift_A_Index0_comm_ind k c a3))
        | (arec zz1) => (f_equal arec (shift_A__shift_A_0_ZZ_comm_ind zz1 k c))
      end
    with shift_A__shift_A_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff A)) {struct zz2} :
    ((shift_A_ZZ (weakenCutoffA (CS c) k) (shift_A_ZZ (weakenCutoffA C0 k) zz2)) = (shift_A_ZZ (weakenCutoffA C0 k) (shift_A_ZZ (weakenCutoffA c k) zz2))) :=
      match zz2 return ((shift_A_ZZ (weakenCutoffA (CS c) k) (shift_A_ZZ (weakenCutoffA C0 k) zz2)) = (shift_A_ZZ (weakenCutoffA C0 k) (shift_A_ZZ (weakenCutoffA c k) zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (shift_A__shift_A_0_AA_comm_ind aa1 (HS A k) c))
        | (babs bb0) => (f_equal babs (shift_A__shift_A_0_BB_comm_ind bb0 (HS B k) c))
      end
    with shift_A__shift_A_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff A)) {struct bb1} :
    ((shift_A_BB (weakenCutoffA (CS c) k) (shift_A_BB (weakenCutoffA C0 k) bb1)) = (shift_A_BB (weakenCutoffA C0 k) (shift_A_BB (weakenCutoffA c k) bb1))) :=
      match bb1 return ((shift_A_BB (weakenCutoffA (CS c) k) (shift_A_BB (weakenCutoffA C0 k) bb1)) = (shift_A_BB (weakenCutoffA C0 k) (shift_A_BB (weakenCutoffA c k) bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (shift_A__shift_A_0_ZZ_comm_ind zz3 k c))
      end.
    Fixpoint shift_A__shift_B_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff A)) {struct aa0} :
    ((shift_A_AA (weakenCutoffA c k) (shift_B_AA (weakenCutoffB C0 k) aa0)) = (shift_B_AA (weakenCutoffB C0 k) (shift_A_AA (weakenCutoffA c k) aa0))) :=
      match aa0 return ((shift_A_AA (weakenCutoffA c k) (shift_B_AA (weakenCutoffB C0 k) aa0)) = (shift_B_AA (weakenCutoffB C0 k) (shift_A_AA (weakenCutoffA c k) aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (shift_A__shift_B_0_ZZ_comm_ind zz1 k c))
      end
    with shift_A__shift_B_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff A)) {struct zz2} :
    ((shift_A_ZZ (weakenCutoffA c k) (shift_B_ZZ (weakenCutoffB C0 k) zz2)) = (shift_B_ZZ (weakenCutoffB C0 k) (shift_A_ZZ (weakenCutoffA c k) zz2))) :=
      match zz2 return ((shift_A_ZZ (weakenCutoffA c k) (shift_B_ZZ (weakenCutoffB C0 k) zz2)) = (shift_B_ZZ (weakenCutoffB C0 k) (shift_A_ZZ (weakenCutoffA c k) zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (shift_A__shift_B_0_AA_comm_ind aa1 (HS A k) c))
        | (babs bb0) => (f_equal babs (shift_A__shift_B_0_BB_comm_ind bb0 (HS B k) c))
      end
    with shift_A__shift_B_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff A)) {struct bb1} :
    ((shift_A_BB (weakenCutoffA c k) (shift_B_BB (weakenCutoffB C0 k) bb1)) = (shift_B_BB (weakenCutoffB C0 k) (shift_A_BB (weakenCutoffA c k) bb1))) :=
      match bb1 return ((shift_A_BB (weakenCutoffA c k) (shift_B_BB (weakenCutoffB C0 k) bb1)) = (shift_B_BB (weakenCutoffB C0 k) (shift_A_BB (weakenCutoffA c k) bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (shift_A__shift_B_0_ZZ_comm_ind zz3 k c))
      end.
    Fixpoint shift_A__shift_Z_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff A)) {struct aa0} :
    ((shift_A_AA (weakenCutoffA c k) (shift_Z_AA (weakenCutoffZ C0 k) aa0)) = (shift_Z_AA (weakenCutoffZ C0 k) (shift_A_AA (weakenCutoffA c k) aa0))) :=
      match aa0 return ((shift_A_AA (weakenCutoffA c k) (shift_Z_AA (weakenCutoffZ C0 k) aa0)) = (shift_Z_AA (weakenCutoffZ C0 k) (shift_A_AA (weakenCutoffA c k) aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (shift_A__shift_Z_0_ZZ_comm_ind zz1 k c))
      end
    with shift_A__shift_Z_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff A)) {struct zz2} :
    ((shift_A_ZZ (weakenCutoffA c k) (shift_Z_ZZ (weakenCutoffZ C0 k) zz2)) = (shift_Z_ZZ (weakenCutoffZ C0 k) (shift_A_ZZ (weakenCutoffA c k) zz2))) :=
      match zz2 return ((shift_A_ZZ (weakenCutoffA c k) (shift_Z_ZZ (weakenCutoffZ C0 k) zz2)) = (shift_Z_ZZ (weakenCutoffZ C0 k) (shift_A_ZZ (weakenCutoffA c k) zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (shift_A__shift_Z_0_AA_comm_ind aa1 (HS A k) c))
        | (babs bb0) => (f_equal babs (shift_A__shift_Z_0_BB_comm_ind bb0 (HS B k) c))
      end
    with shift_A__shift_Z_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff A)) {struct bb1} :
    ((shift_A_BB (weakenCutoffA c k) (shift_Z_BB (weakenCutoffZ C0 k) bb1)) = (shift_Z_BB (weakenCutoffZ C0 k) (shift_A_BB (weakenCutoffA c k) bb1))) :=
      match bb1 return ((shift_A_BB (weakenCutoffA c k) (shift_Z_BB (weakenCutoffZ C0 k) bb1)) = (shift_Z_BB (weakenCutoffZ C0 k) (shift_A_BB (weakenCutoffA c k) bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (shift_A__shift_Z_0_ZZ_comm_ind zz3 k c))
      end.
    Fixpoint shift_B__shift_A_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff B)) {struct aa0} :
    ((shift_B_AA (weakenCutoffB c k) (shift_A_AA (weakenCutoffA C0 k) aa0)) = (shift_A_AA (weakenCutoffA C0 k) (shift_B_AA (weakenCutoffB c k) aa0))) :=
      match aa0 return ((shift_B_AA (weakenCutoffB c k) (shift_A_AA (weakenCutoffA C0 k) aa0)) = (shift_A_AA (weakenCutoffA C0 k) (shift_B_AA (weakenCutoffB c k) aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (shift_B__shift_A_0_ZZ_comm_ind zz1 k c))
      end
    with shift_B__shift_A_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff B)) {struct zz2} :
    ((shift_B_ZZ (weakenCutoffB c k) (shift_A_ZZ (weakenCutoffA C0 k) zz2)) = (shift_A_ZZ (weakenCutoffA C0 k) (shift_B_ZZ (weakenCutoffB c k) zz2))) :=
      match zz2 return ((shift_B_ZZ (weakenCutoffB c k) (shift_A_ZZ (weakenCutoffA C0 k) zz2)) = (shift_A_ZZ (weakenCutoffA C0 k) (shift_B_ZZ (weakenCutoffB c k) zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (shift_B__shift_A_0_AA_comm_ind aa1 (HS A k) c))
        | (babs bb0) => (f_equal babs (shift_B__shift_A_0_BB_comm_ind bb0 (HS B k) c))
      end
    with shift_B__shift_A_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff B)) {struct bb1} :
    ((shift_B_BB (weakenCutoffB c k) (shift_A_BB (weakenCutoffA C0 k) bb1)) = (shift_A_BB (weakenCutoffA C0 k) (shift_B_BB (weakenCutoffB c k) bb1))) :=
      match bb1 return ((shift_B_BB (weakenCutoffB c k) (shift_A_BB (weakenCutoffA C0 k) bb1)) = (shift_A_BB (weakenCutoffA C0 k) (shift_B_BB (weakenCutoffB c k) bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (shift_B__shift_A_0_ZZ_comm_ind zz3 k c))
      end.
    Fixpoint shift_B__shift_B_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff B)) {struct aa0} :
    ((shift_B_AA (weakenCutoffB (CS c) k) (shift_B_AA (weakenCutoffB C0 k) aa0)) = (shift_B_AA (weakenCutoffB C0 k) (shift_B_AA (weakenCutoffB c k) aa0))) :=
      match aa0 return ((shift_B_AA (weakenCutoffB (CS c) k) (shift_B_AA (weakenCutoffB C0 k) aa0)) = (shift_B_AA (weakenCutoffB C0 k) (shift_B_AA (weakenCutoffB c k) aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (shift_B__shift_B_0_ZZ_comm_ind zz1 k c))
      end
    with shift_B__shift_B_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff B)) {struct zz2} :
    ((shift_B_ZZ (weakenCutoffB (CS c) k) (shift_B_ZZ (weakenCutoffB C0 k) zz2)) = (shift_B_ZZ (weakenCutoffB C0 k) (shift_B_ZZ (weakenCutoffB c k) zz2))) :=
      match zz2 return ((shift_B_ZZ (weakenCutoffB (CS c) k) (shift_B_ZZ (weakenCutoffB C0 k) zz2)) = (shift_B_ZZ (weakenCutoffB C0 k) (shift_B_ZZ (weakenCutoffB c k) zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (shift_B__shift_B_0_AA_comm_ind aa1 (HS A k) c))
        | (babs bb0) => (f_equal babs (shift_B__shift_B_0_BB_comm_ind bb0 (HS B k) c))
      end
    with shift_B__shift_B_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff B)) {struct bb1} :
    ((shift_B_BB (weakenCutoffB (CS c) k) (shift_B_BB (weakenCutoffB C0 k) bb1)) = (shift_B_BB (weakenCutoffB C0 k) (shift_B_BB (weakenCutoffB c k) bb1))) :=
      match bb1 return ((shift_B_BB (weakenCutoffB (CS c) k) (shift_B_BB (weakenCutoffB C0 k) bb1)) = (shift_B_BB (weakenCutoffB C0 k) (shift_B_BB (weakenCutoffB c k) bb1))) with
        | (bvar b4) => (f_equal bvar (shift_B_Index_shift_B_Index0_comm_ind k c b4))
        | (brec zz3) => (f_equal brec (shift_B__shift_B_0_ZZ_comm_ind zz3 k c))
      end.
    Fixpoint shift_B__shift_Z_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff B)) {struct aa0} :
    ((shift_B_AA (weakenCutoffB c k) (shift_Z_AA (weakenCutoffZ C0 k) aa0)) = (shift_Z_AA (weakenCutoffZ C0 k) (shift_B_AA (weakenCutoffB c k) aa0))) :=
      match aa0 return ((shift_B_AA (weakenCutoffB c k) (shift_Z_AA (weakenCutoffZ C0 k) aa0)) = (shift_Z_AA (weakenCutoffZ C0 k) (shift_B_AA (weakenCutoffB c k) aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (shift_B__shift_Z_0_ZZ_comm_ind zz1 k c))
      end
    with shift_B__shift_Z_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff B)) {struct zz2} :
    ((shift_B_ZZ (weakenCutoffB c k) (shift_Z_ZZ (weakenCutoffZ C0 k) zz2)) = (shift_Z_ZZ (weakenCutoffZ C0 k) (shift_B_ZZ (weakenCutoffB c k) zz2))) :=
      match zz2 return ((shift_B_ZZ (weakenCutoffB c k) (shift_Z_ZZ (weakenCutoffZ C0 k) zz2)) = (shift_Z_ZZ (weakenCutoffZ C0 k) (shift_B_ZZ (weakenCutoffB c k) zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (shift_B__shift_Z_0_AA_comm_ind aa1 (HS A k) c))
        | (babs bb0) => (f_equal babs (shift_B__shift_Z_0_BB_comm_ind bb0 (HS B k) c))
      end
    with shift_B__shift_Z_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff B)) {struct bb1} :
    ((shift_B_BB (weakenCutoffB c k) (shift_Z_BB (weakenCutoffZ C0 k) bb1)) = (shift_Z_BB (weakenCutoffZ C0 k) (shift_B_BB (weakenCutoffB c k) bb1))) :=
      match bb1 return ((shift_B_BB (weakenCutoffB c k) (shift_Z_BB (weakenCutoffZ C0 k) bb1)) = (shift_Z_BB (weakenCutoffZ C0 k) (shift_B_BB (weakenCutoffB c k) bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (shift_B__shift_Z_0_ZZ_comm_ind zz3 k c))
      end.
    Fixpoint shift_Z__shift_A_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff Z)) {struct aa0} :
    ((shift_Z_AA (weakenCutoffZ c k) (shift_A_AA (weakenCutoffA C0 k) aa0)) = (shift_A_AA (weakenCutoffA C0 k) (shift_Z_AA (weakenCutoffZ c k) aa0))) :=
      match aa0 return ((shift_Z_AA (weakenCutoffZ c k) (shift_A_AA (weakenCutoffA C0 k) aa0)) = (shift_A_AA (weakenCutoffA C0 k) (shift_Z_AA (weakenCutoffZ c k) aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (shift_Z__shift_A_0_ZZ_comm_ind zz1 k c))
      end
    with shift_Z__shift_A_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff Z)) {struct zz2} :
    ((shift_Z_ZZ (weakenCutoffZ c k) (shift_A_ZZ (weakenCutoffA C0 k) zz2)) = (shift_A_ZZ (weakenCutoffA C0 k) (shift_Z_ZZ (weakenCutoffZ c k) zz2))) :=
      match zz2 return ((shift_Z_ZZ (weakenCutoffZ c k) (shift_A_ZZ (weakenCutoffA C0 k) zz2)) = (shift_A_ZZ (weakenCutoffA C0 k) (shift_Z_ZZ (weakenCutoffZ c k) zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (shift_Z__shift_A_0_AA_comm_ind aa1 (HS A k) c))
        | (babs bb0) => (f_equal babs (shift_Z__shift_A_0_BB_comm_ind bb0 (HS B k) c))
      end
    with shift_Z__shift_A_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff Z)) {struct bb1} :
    ((shift_Z_BB (weakenCutoffZ c k) (shift_A_BB (weakenCutoffA C0 k) bb1)) = (shift_A_BB (weakenCutoffA C0 k) (shift_Z_BB (weakenCutoffZ c k) bb1))) :=
      match bb1 return ((shift_Z_BB (weakenCutoffZ c k) (shift_A_BB (weakenCutoffA C0 k) bb1)) = (shift_A_BB (weakenCutoffA C0 k) (shift_Z_BB (weakenCutoffZ c k) bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (shift_Z__shift_A_0_ZZ_comm_ind zz3 k c))
      end.
    Fixpoint shift_Z__shift_B_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff Z)) {struct aa0} :
    ((shift_Z_AA (weakenCutoffZ c k) (shift_B_AA (weakenCutoffB C0 k) aa0)) = (shift_B_AA (weakenCutoffB C0 k) (shift_Z_AA (weakenCutoffZ c k) aa0))) :=
      match aa0 return ((shift_Z_AA (weakenCutoffZ c k) (shift_B_AA (weakenCutoffB C0 k) aa0)) = (shift_B_AA (weakenCutoffB C0 k) (shift_Z_AA (weakenCutoffZ c k) aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (shift_Z__shift_B_0_ZZ_comm_ind zz1 k c))
      end
    with shift_Z__shift_B_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff Z)) {struct zz2} :
    ((shift_Z_ZZ (weakenCutoffZ c k) (shift_B_ZZ (weakenCutoffB C0 k) zz2)) = (shift_B_ZZ (weakenCutoffB C0 k) (shift_Z_ZZ (weakenCutoffZ c k) zz2))) :=
      match zz2 return ((shift_Z_ZZ (weakenCutoffZ c k) (shift_B_ZZ (weakenCutoffB C0 k) zz2)) = (shift_B_ZZ (weakenCutoffB C0 k) (shift_Z_ZZ (weakenCutoffZ c k) zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (shift_Z__shift_B_0_AA_comm_ind aa1 (HS A k) c))
        | (babs bb0) => (f_equal babs (shift_Z__shift_B_0_BB_comm_ind bb0 (HS B k) c))
      end
    with shift_Z__shift_B_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff Z)) {struct bb1} :
    ((shift_Z_BB (weakenCutoffZ c k) (shift_B_BB (weakenCutoffB C0 k) bb1)) = (shift_B_BB (weakenCutoffB C0 k) (shift_Z_BB (weakenCutoffZ c k) bb1))) :=
      match bb1 return ((shift_Z_BB (weakenCutoffZ c k) (shift_B_BB (weakenCutoffB C0 k) bb1)) = (shift_B_BB (weakenCutoffB C0 k) (shift_Z_BB (weakenCutoffZ c k) bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (shift_Z__shift_B_0_ZZ_comm_ind zz3 k c))
      end.
    Fixpoint shift_Z__shift_Z_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff Z)) {struct aa0} :
    ((shift_Z_AA (weakenCutoffZ (CS c) k) (shift_Z_AA (weakenCutoffZ C0 k) aa0)) = (shift_Z_AA (weakenCutoffZ C0 k) (shift_Z_AA (weakenCutoffZ c k) aa0))) :=
      match aa0 return ((shift_Z_AA (weakenCutoffZ (CS c) k) (shift_Z_AA (weakenCutoffZ C0 k) aa0)) = (shift_Z_AA (weakenCutoffZ C0 k) (shift_Z_AA (weakenCutoffZ c k) aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (shift_Z__shift_Z_0_ZZ_comm_ind zz1 k c))
      end
    with shift_Z__shift_Z_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff Z)) {struct zz2} :
    ((shift_Z_ZZ (weakenCutoffZ (CS c) k) (shift_Z_ZZ (weakenCutoffZ C0 k) zz2)) = (shift_Z_ZZ (weakenCutoffZ C0 k) (shift_Z_ZZ (weakenCutoffZ c k) zz2))) :=
      match zz2 return ((shift_Z_ZZ (weakenCutoffZ (CS c) k) (shift_Z_ZZ (weakenCutoffZ C0 k) zz2)) = (shift_Z_ZZ (weakenCutoffZ C0 k) (shift_Z_ZZ (weakenCutoffZ c k) zz2))) with
        | (zvar z0) => (f_equal zvar (shift_Z_Index_shift_Z_Index0_comm_ind k c z0))
        | (aabs aa1) => (f_equal aabs (shift_Z__shift_Z_0_AA_comm_ind aa1 (HS A k) c))
        | (babs bb0) => (f_equal babs (shift_Z__shift_Z_0_BB_comm_ind bb0 (HS B k) c))
      end
    with shift_Z__shift_Z_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff Z)) {struct bb1} :
    ((shift_Z_BB (weakenCutoffZ (CS c) k) (shift_Z_BB (weakenCutoffZ C0 k) bb1)) = (shift_Z_BB (weakenCutoffZ C0 k) (shift_Z_BB (weakenCutoffZ c k) bb1))) :=
      match bb1 return ((shift_Z_BB (weakenCutoffZ (CS c) k) (shift_Z_BB (weakenCutoffZ C0 k) bb1)) = (shift_Z_BB (weakenCutoffZ C0 k) (shift_Z_BB (weakenCutoffZ c k) bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (shift_Z__shift_Z_0_ZZ_comm_ind zz3 k c))
      end.
  End ShiftCommInd.
  Section ShiftComm.
    Definition shift_A__shift_A_0_AA_comm (aa0 : AA) : (forall (c : (Cutoff A)) ,
      ((shift_A_AA (CS c) (shift_A_AA C0 aa0)) = (shift_A_AA C0 (shift_A_AA c aa0)))) := (shift_A__shift_A_0_AA_comm_ind aa0 H0).
    Definition shift_A__shift_A_0_ZZ_comm (zz1 : ZZ) : (forall (c : (Cutoff A)) ,
      ((shift_A_ZZ (CS c) (shift_A_ZZ C0 zz1)) = (shift_A_ZZ C0 (shift_A_ZZ c zz1)))) := (shift_A__shift_A_0_ZZ_comm_ind zz1 H0).
    Definition shift_A__shift_A_0_BB_comm (bb0 : BB) : (forall (c : (Cutoff A)) ,
      ((shift_A_BB (CS c) (shift_A_BB C0 bb0)) = (shift_A_BB C0 (shift_A_BB c bb0)))) := (shift_A__shift_A_0_BB_comm_ind bb0 H0).
    Definition shift_A__shift_B_0_AA_comm (aa0 : AA) : (forall (c : (Cutoff A)) ,
      ((shift_A_AA c (shift_B_AA C0 aa0)) = (shift_B_AA C0 (shift_A_AA c aa0)))) := (shift_A__shift_B_0_AA_comm_ind aa0 H0).
    Definition shift_A__shift_B_0_ZZ_comm (zz1 : ZZ) : (forall (c : (Cutoff A)) ,
      ((shift_A_ZZ c (shift_B_ZZ C0 zz1)) = (shift_B_ZZ C0 (shift_A_ZZ c zz1)))) := (shift_A__shift_B_0_ZZ_comm_ind zz1 H0).
    Definition shift_A__shift_B_0_BB_comm (bb0 : BB) : (forall (c : (Cutoff A)) ,
      ((shift_A_BB c (shift_B_BB C0 bb0)) = (shift_B_BB C0 (shift_A_BB c bb0)))) := (shift_A__shift_B_0_BB_comm_ind bb0 H0).
    Definition shift_A__shift_Z_0_AA_comm (aa0 : AA) : (forall (c : (Cutoff A)) ,
      ((shift_A_AA c (shift_Z_AA C0 aa0)) = (shift_Z_AA C0 (shift_A_AA c aa0)))) := (shift_A__shift_Z_0_AA_comm_ind aa0 H0).
    Definition shift_A__shift_Z_0_ZZ_comm (zz1 : ZZ) : (forall (c : (Cutoff A)) ,
      ((shift_A_ZZ c (shift_Z_ZZ C0 zz1)) = (shift_Z_ZZ C0 (shift_A_ZZ c zz1)))) := (shift_A__shift_Z_0_ZZ_comm_ind zz1 H0).
    Definition shift_A__shift_Z_0_BB_comm (bb0 : BB) : (forall (c : (Cutoff A)) ,
      ((shift_A_BB c (shift_Z_BB C0 bb0)) = (shift_Z_BB C0 (shift_A_BB c bb0)))) := (shift_A__shift_Z_0_BB_comm_ind bb0 H0).
    Definition shift_B__shift_A_0_AA_comm (aa0 : AA) : (forall (c : (Cutoff B)) ,
      ((shift_B_AA c (shift_A_AA C0 aa0)) = (shift_A_AA C0 (shift_B_AA c aa0)))) := (shift_B__shift_A_0_AA_comm_ind aa0 H0).
    Definition shift_B__shift_A_0_ZZ_comm (zz1 : ZZ) : (forall (c : (Cutoff B)) ,
      ((shift_B_ZZ c (shift_A_ZZ C0 zz1)) = (shift_A_ZZ C0 (shift_B_ZZ c zz1)))) := (shift_B__shift_A_0_ZZ_comm_ind zz1 H0).
    Definition shift_B__shift_A_0_BB_comm (bb0 : BB) : (forall (c : (Cutoff B)) ,
      ((shift_B_BB c (shift_A_BB C0 bb0)) = (shift_A_BB C0 (shift_B_BB c bb0)))) := (shift_B__shift_A_0_BB_comm_ind bb0 H0).
    Definition shift_B__shift_B_0_AA_comm (aa0 : AA) : (forall (c : (Cutoff B)) ,
      ((shift_B_AA (CS c) (shift_B_AA C0 aa0)) = (shift_B_AA C0 (shift_B_AA c aa0)))) := (shift_B__shift_B_0_AA_comm_ind aa0 H0).
    Definition shift_B__shift_B_0_ZZ_comm (zz1 : ZZ) : (forall (c : (Cutoff B)) ,
      ((shift_B_ZZ (CS c) (shift_B_ZZ C0 zz1)) = (shift_B_ZZ C0 (shift_B_ZZ c zz1)))) := (shift_B__shift_B_0_ZZ_comm_ind zz1 H0).
    Definition shift_B__shift_B_0_BB_comm (bb0 : BB) : (forall (c : (Cutoff B)) ,
      ((shift_B_BB (CS c) (shift_B_BB C0 bb0)) = (shift_B_BB C0 (shift_B_BB c bb0)))) := (shift_B__shift_B_0_BB_comm_ind bb0 H0).
    Definition shift_B__shift_Z_0_AA_comm (aa0 : AA) : (forall (c : (Cutoff B)) ,
      ((shift_B_AA c (shift_Z_AA C0 aa0)) = (shift_Z_AA C0 (shift_B_AA c aa0)))) := (shift_B__shift_Z_0_AA_comm_ind aa0 H0).
    Definition shift_B__shift_Z_0_ZZ_comm (zz1 : ZZ) : (forall (c : (Cutoff B)) ,
      ((shift_B_ZZ c (shift_Z_ZZ C0 zz1)) = (shift_Z_ZZ C0 (shift_B_ZZ c zz1)))) := (shift_B__shift_Z_0_ZZ_comm_ind zz1 H0).
    Definition shift_B__shift_Z_0_BB_comm (bb0 : BB) : (forall (c : (Cutoff B)) ,
      ((shift_B_BB c (shift_Z_BB C0 bb0)) = (shift_Z_BB C0 (shift_B_BB c bb0)))) := (shift_B__shift_Z_0_BB_comm_ind bb0 H0).
    Definition shift_Z__shift_A_0_AA_comm (aa0 : AA) : (forall (c : (Cutoff Z)) ,
      ((shift_Z_AA c (shift_A_AA C0 aa0)) = (shift_A_AA C0 (shift_Z_AA c aa0)))) := (shift_Z__shift_A_0_AA_comm_ind aa0 H0).
    Definition shift_Z__shift_A_0_ZZ_comm (zz1 : ZZ) : (forall (c : (Cutoff Z)) ,
      ((shift_Z_ZZ c (shift_A_ZZ C0 zz1)) = (shift_A_ZZ C0 (shift_Z_ZZ c zz1)))) := (shift_Z__shift_A_0_ZZ_comm_ind zz1 H0).
    Definition shift_Z__shift_A_0_BB_comm (bb0 : BB) : (forall (c : (Cutoff Z)) ,
      ((shift_Z_BB c (shift_A_BB C0 bb0)) = (shift_A_BB C0 (shift_Z_BB c bb0)))) := (shift_Z__shift_A_0_BB_comm_ind bb0 H0).
    Definition shift_Z__shift_B_0_AA_comm (aa0 : AA) : (forall (c : (Cutoff Z)) ,
      ((shift_Z_AA c (shift_B_AA C0 aa0)) = (shift_B_AA C0 (shift_Z_AA c aa0)))) := (shift_Z__shift_B_0_AA_comm_ind aa0 H0).
    Definition shift_Z__shift_B_0_ZZ_comm (zz1 : ZZ) : (forall (c : (Cutoff Z)) ,
      ((shift_Z_ZZ c (shift_B_ZZ C0 zz1)) = (shift_B_ZZ C0 (shift_Z_ZZ c zz1)))) := (shift_Z__shift_B_0_ZZ_comm_ind zz1 H0).
    Definition shift_Z__shift_B_0_BB_comm (bb0 : BB) : (forall (c : (Cutoff Z)) ,
      ((shift_Z_BB c (shift_B_BB C0 bb0)) = (shift_B_BB C0 (shift_Z_BB c bb0)))) := (shift_Z__shift_B_0_BB_comm_ind bb0 H0).
    Definition shift_Z__shift_Z_0_AA_comm (aa0 : AA) : (forall (c : (Cutoff Z)) ,
      ((shift_Z_AA (CS c) (shift_Z_AA C0 aa0)) = (shift_Z_AA C0 (shift_Z_AA c aa0)))) := (shift_Z__shift_Z_0_AA_comm_ind aa0 H0).
    Definition shift_Z__shift_Z_0_ZZ_comm (zz1 : ZZ) : (forall (c : (Cutoff Z)) ,
      ((shift_Z_ZZ (CS c) (shift_Z_ZZ C0 zz1)) = (shift_Z_ZZ C0 (shift_Z_ZZ c zz1)))) := (shift_Z__shift_Z_0_ZZ_comm_ind zz1 H0).
    Definition shift_Z__shift_Z_0_BB_comm (bb0 : BB) : (forall (c : (Cutoff Z)) ,
      ((shift_Z_BB (CS c) (shift_Z_BB C0 bb0)) = (shift_Z_BB C0 (shift_Z_BB c bb0)))) := (shift_Z__shift_Z_0_BB_comm_ind bb0 H0).
  End ShiftComm.
End ShiftInteraction.
 Hint Rewrite shift_A__shift_A_0_AA_comm shift_A__shift_B_0_AA_comm shift_A__shift_Z_0_AA_comm shift_B__shift_A_0_AA_comm shift_B__shift_B_0_AA_comm shift_B__shift_Z_0_AA_comm shift_Z__shift_A_0_AA_comm shift_Z__shift_B_0_AA_comm shift_Z__shift_Z_0_AA_comm shift_A__shift_A_0_BB_comm shift_A__shift_B_0_BB_comm shift_A__shift_Z_0_BB_comm shift_B__shift_A_0_BB_comm shift_B__shift_B_0_BB_comm shift_B__shift_Z_0_BB_comm shift_Z__shift_A_0_BB_comm shift_Z__shift_B_0_BB_comm shift_Z__shift_Z_0_BB_comm shift_A__shift_A_0_ZZ_comm shift_A__shift_B_0_ZZ_comm shift_A__shift_Z_0_ZZ_comm shift_B__shift_A_0_ZZ_comm shift_B__shift_B_0_ZZ_comm shift_B__shift_Z_0_ZZ_comm shift_Z__shift_A_0_ZZ_comm shift_Z__shift_B_0_ZZ_comm shift_Z__shift_Z_0_ZZ_comm : interaction.
 Hint Rewrite shift_A__shift_A_0_AA_comm shift_A__shift_B_0_AA_comm shift_A__shift_Z_0_AA_comm shift_B__shift_A_0_AA_comm shift_B__shift_B_0_AA_comm shift_B__shift_Z_0_AA_comm shift_Z__shift_A_0_AA_comm shift_Z__shift_B_0_AA_comm shift_Z__shift_Z_0_AA_comm shift_A__shift_A_0_BB_comm shift_A__shift_B_0_BB_comm shift_A__shift_Z_0_BB_comm shift_B__shift_A_0_BB_comm shift_B__shift_B_0_BB_comm shift_B__shift_Z_0_BB_comm shift_Z__shift_A_0_BB_comm shift_Z__shift_B_0_BB_comm shift_Z__shift_Z_0_BB_comm shift_A__shift_A_0_ZZ_comm shift_A__shift_B_0_ZZ_comm shift_A__shift_Z_0_ZZ_comm shift_B__shift_A_0_ZZ_comm shift_B__shift_B_0_ZZ_comm shift_B__shift_Z_0_ZZ_comm shift_Z__shift_A_0_ZZ_comm shift_Z__shift_B_0_ZZ_comm shift_Z__shift_Z_0_ZZ_comm : shift_shift0.
Section WeakenShift.
  Lemma weakenAA_shift_A_AA  :
    (forall (k : Hvl) (c : (Cutoff A)) (aa0 : AA) ,
      ((weakenAA (shift_A_AA c aa0) k) = (shift_A_AA (weakenCutoffA c k) (weakenAA aa0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenZZ_shift_A_ZZ  :
    (forall (k : Hvl) (c : (Cutoff A)) (zz1 : ZZ) ,
      ((weakenZZ (shift_A_ZZ c zz1) k) = (shift_A_ZZ (weakenCutoffA c k) (weakenZZ zz1 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenBB_shift_A_BB  :
    (forall (k : Hvl) (c : (Cutoff A)) (bb0 : BB) ,
      ((weakenBB (shift_A_BB c bb0) k) = (shift_A_BB (weakenCutoffA c k) (weakenBB bb0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenAA_shift_B_AA  :
    (forall (k : Hvl) (c : (Cutoff B)) (aa0 : AA) ,
      ((weakenAA (shift_B_AA c aa0) k) = (shift_B_AA (weakenCutoffB c k) (weakenAA aa0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenZZ_shift_B_ZZ  :
    (forall (k : Hvl) (c : (Cutoff B)) (zz1 : ZZ) ,
      ((weakenZZ (shift_B_ZZ c zz1) k) = (shift_B_ZZ (weakenCutoffB c k) (weakenZZ zz1 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenBB_shift_B_BB  :
    (forall (k : Hvl) (c : (Cutoff B)) (bb0 : BB) ,
      ((weakenBB (shift_B_BB c bb0) k) = (shift_B_BB (weakenCutoffB c k) (weakenBB bb0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenAA_shift_Z_AA  :
    (forall (k : Hvl) (c : (Cutoff Z)) (aa0 : AA) ,
      ((weakenAA (shift_Z_AA c aa0) k) = (shift_Z_AA (weakenCutoffZ c k) (weakenAA aa0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenZZ_shift_Z_ZZ  :
    (forall (k : Hvl) (c : (Cutoff Z)) (zz1 : ZZ) ,
      ((weakenZZ (shift_Z_ZZ c zz1) k) = (shift_Z_ZZ (weakenCutoffZ c k) (weakenZZ zz1 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
  Lemma weakenBB_shift_Z_BB  :
    (forall (k : Hvl) (c : (Cutoff Z)) (bb0 : BB) ,
      ((weakenBB (shift_Z_BB c bb0) k) = (shift_Z_BB (weakenCutoffZ c k) (weakenBB bb0 k)))).
  Proof.
    needleGenericWeakenShift .
  Qed.
End WeakenShift.
Section ShiftSubstInteraction.
  Section ShiftSubstIndexCommInd.
    Lemma shift_A_AA_subst_A_Index0_comm_ind (c : (Cutoff A)) (aa0 : AA) :
      (forall (k : Hvl) (a3 : (Index A)) ,
        ((shift_A_AA (weakenCutoffA c k) (subst_A_Index (weakenTrace X0 k) aa0 a3)) = (subst_A_Index (weakenTrace X0 k) (shift_A_AA c aa0) (shift_A_Index (weakenCutoffA (CS c) k) a3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_B_AA_subst_A_Index0_comm_ind (c : (Cutoff B)) (aa0 : AA) :
      (forall (k : Hvl) (a3 : (Index A)) ,
        ((shift_B_AA (weakenCutoffB c k) (subst_A_Index (weakenTrace X0 k) aa0 a3)) = (subst_A_Index (weakenTrace X0 k) (shift_B_AA c aa0) a3))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_Z_AA_subst_A_Index0_comm_ind (c : (Cutoff Z)) (aa0 : AA) :
      (forall (k : Hvl) (a3 : (Index A)) ,
        ((shift_Z_AA (weakenCutoffZ c k) (subst_A_Index (weakenTrace X0 k) aa0 a3)) = (subst_A_Index (weakenTrace X0 k) (shift_Z_AA c aa0) a3))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_A_BB_subst_B_Index0_comm_ind (c : (Cutoff A)) (bb0 : BB) :
      (forall (k : Hvl) (b3 : (Index B)) ,
        ((shift_A_BB (weakenCutoffA c k) (subst_B_Index (weakenTrace X0 k) bb0 b3)) = (subst_B_Index (weakenTrace X0 k) (shift_A_BB c bb0) b3))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_B_BB_subst_B_Index0_comm_ind (c : (Cutoff B)) (bb0 : BB) :
      (forall (k : Hvl) (b3 : (Index B)) ,
        ((shift_B_BB (weakenCutoffB c k) (subst_B_Index (weakenTrace X0 k) bb0 b3)) = (subst_B_Index (weakenTrace X0 k) (shift_B_BB c bb0) (shift_B_Index (weakenCutoffB (CS c) k) b3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_Z_BB_subst_B_Index0_comm_ind (c : (Cutoff Z)) (bb0 : BB) :
      (forall (k : Hvl) (b3 : (Index B)) ,
        ((shift_Z_BB (weakenCutoffZ c k) (subst_B_Index (weakenTrace X0 k) bb0 b3)) = (subst_B_Index (weakenTrace X0 k) (shift_Z_BB c bb0) b3))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_A_ZZ_subst_Z_Index0_comm_ind (c : (Cutoff A)) (zz1 : ZZ) :
      (forall (k : Hvl) (z0 : (Index Z)) ,
        ((shift_A_ZZ (weakenCutoffA c k) (subst_Z_Index (weakenTrace X0 k) zz1 z0)) = (subst_Z_Index (weakenTrace X0 k) (shift_A_ZZ c zz1) z0))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_B_ZZ_subst_Z_Index0_comm_ind (c : (Cutoff B)) (zz1 : ZZ) :
      (forall (k : Hvl) (z0 : (Index Z)) ,
        ((shift_B_ZZ (weakenCutoffB c k) (subst_Z_Index (weakenTrace X0 k) zz1 z0)) = (subst_Z_Index (weakenTrace X0 k) (shift_B_ZZ c zz1) z0))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma shift_Z_ZZ_subst_Z_Index0_comm_ind (c : (Cutoff Z)) (zz1 : ZZ) :
      (forall (k : Hvl) (z0 : (Index Z)) ,
        ((shift_Z_ZZ (weakenCutoffZ c k) (subst_Z_Index (weakenTrace X0 k) zz1 z0)) = (subst_Z_Index (weakenTrace X0 k) (shift_Z_ZZ c zz1) (shift_Z_Index (weakenCutoffZ (CS c) k) z0)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End ShiftSubstIndexCommInd.
  Section ShiftSubstCommInd.
    Fixpoint shift_A__subst_A_0_AA_comm_ind (aa1 : AA) (k : Hvl) (c : (Cutoff A)) (aa0 : AA) {struct aa1} :
    ((shift_A_AA (weakenCutoffA c k) (subst_A_AA (weakenTrace X0 k) aa0 aa1)) = (subst_A_AA (weakenTrace X0 k) (shift_A_AA c aa0) (shift_A_AA (weakenCutoffA (CS c) k) aa1))) :=
      match aa1 return ((shift_A_AA (weakenCutoffA c k) (subst_A_AA (weakenTrace X0 k) aa0 aa1)) = (subst_A_AA (weakenTrace X0 k) (shift_A_AA c aa0) (shift_A_AA (weakenCutoffA (CS c) k) aa1))) with
        | (avar a3) => (shift_A_AA_subst_A_Index0_comm_ind c aa0 k a3)
        | (arec zz1) => (f_equal arec (shift_A__subst_A_0_ZZ_comm_ind zz1 k c aa0))
      end
    with shift_A__subst_A_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff A)) (aa0 : AA) {struct zz2} :
    ((shift_A_ZZ (weakenCutoffA c k) (subst_A_ZZ (weakenTrace X0 k) aa0 zz2)) = (subst_A_ZZ (weakenTrace X0 k) (shift_A_AA c aa0) (shift_A_ZZ (weakenCutoffA (CS c) k) zz2))) :=
      match zz2 return ((shift_A_ZZ (weakenCutoffA c k) (subst_A_ZZ (weakenTrace X0 k) aa0 zz2)) = (subst_A_ZZ (weakenTrace X0 k) (shift_A_AA c aa0) (shift_A_ZZ (weakenCutoffA (CS c) k) zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa2) => (f_equal aabs (eq_trans (f_equal2 shift_A_AA eq_refl (f_equal3 subst_A_AA (weakenTrace_append A X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (shift_A__subst_A_0_AA_comm_ind aa2 (HS A k) c aa0) (f_equal3 subst_A_AA (eq_sym (weakenTrace_append A X0 k (HS A H0))) eq_refl eq_refl))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal2 shift_A_BB eq_refl (f_equal3 subst_A_BB (weakenTrace_append A X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (shift_A__subst_A_0_BB_comm_ind bb0 (HS B k) c aa0) (f_equal3 subst_A_BB (eq_sym (weakenTrace_append A X0 k (HS B H0))) eq_refl eq_refl))))
      end
    with shift_A__subst_A_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff A)) (aa0 : AA) {struct bb1} :
    ((shift_A_BB (weakenCutoffA c k) (subst_A_BB (weakenTrace X0 k) aa0 bb1)) = (subst_A_BB (weakenTrace X0 k) (shift_A_AA c aa0) (shift_A_BB (weakenCutoffA (CS c) k) bb1))) :=
      match bb1 return ((shift_A_BB (weakenCutoffA c k) (subst_A_BB (weakenTrace X0 k) aa0 bb1)) = (subst_A_BB (weakenTrace X0 k) (shift_A_AA c aa0) (shift_A_BB (weakenCutoffA (CS c) k) bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (shift_A__subst_A_0_ZZ_comm_ind zz3 k c aa0))
      end.
    Fixpoint shift_A__subst_B_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff A)) (bb0 : BB) {struct aa0} :
    ((shift_A_AA (weakenCutoffA c k) (subst_B_AA (weakenTrace X0 k) bb0 aa0)) = (subst_B_AA (weakenTrace X0 k) (shift_A_BB c bb0) (shift_A_AA (weakenCutoffA c k) aa0))) :=
      match aa0 return ((shift_A_AA (weakenCutoffA c k) (subst_B_AA (weakenTrace X0 k) bb0 aa0)) = (subst_B_AA (weakenTrace X0 k) (shift_A_BB c bb0) (shift_A_AA (weakenCutoffA c k) aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (shift_A__subst_B_0_ZZ_comm_ind zz1 k c bb0))
      end
    with shift_A__subst_B_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff A)) (bb0 : BB) {struct zz2} :
    ((shift_A_ZZ (weakenCutoffA c k) (subst_B_ZZ (weakenTrace X0 k) bb0 zz2)) = (subst_B_ZZ (weakenTrace X0 k) (shift_A_BB c bb0) (shift_A_ZZ (weakenCutoffA c k) zz2))) :=
      match zz2 return ((shift_A_ZZ (weakenCutoffA c k) (subst_B_ZZ (weakenTrace X0 k) bb0 zz2)) = (subst_B_ZZ (weakenTrace X0 k) (shift_A_BB c bb0) (shift_A_ZZ (weakenCutoffA c k) zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal2 shift_A_AA eq_refl (f_equal3 subst_B_AA (weakenTrace_append B X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (shift_A__subst_B_0_AA_comm_ind aa1 (HS A k) c bb0) (f_equal3 subst_B_AA (eq_sym (weakenTrace_append B X0 k (HS A H0))) eq_refl eq_refl))))
        | (babs bb1) => (f_equal babs (eq_trans (f_equal2 shift_A_BB eq_refl (f_equal3 subst_B_BB (weakenTrace_append B X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (shift_A__subst_B_0_BB_comm_ind bb1 (HS B k) c bb0) (f_equal3 subst_B_BB (eq_sym (weakenTrace_append B X0 k (HS B H0))) eq_refl eq_refl))))
      end
    with shift_A__subst_B_0_BB_comm_ind (bb2 : BB) (k : Hvl) (c : (Cutoff A)) (bb0 : BB) {struct bb2} :
    ((shift_A_BB (weakenCutoffA c k) (subst_B_BB (weakenTrace X0 k) bb0 bb2)) = (subst_B_BB (weakenTrace X0 k) (shift_A_BB c bb0) (shift_A_BB (weakenCutoffA c k) bb2))) :=
      match bb2 return ((shift_A_BB (weakenCutoffA c k) (subst_B_BB (weakenTrace X0 k) bb0 bb2)) = (subst_B_BB (weakenTrace X0 k) (shift_A_BB c bb0) (shift_A_BB (weakenCutoffA c k) bb2))) with
        | (bvar b4) => (shift_A_BB_subst_B_Index0_comm_ind c bb0 k b4)
        | (brec zz3) => (f_equal brec (shift_A__subst_B_0_ZZ_comm_ind zz3 k c bb0))
      end.
    Fixpoint shift_A__subst_Z_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff A)) (zz1 : ZZ) {struct aa0} :
    ((shift_A_AA (weakenCutoffA c k) (subst_Z_AA (weakenTrace X0 k) zz1 aa0)) = (subst_Z_AA (weakenTrace X0 k) (shift_A_ZZ c zz1) (shift_A_AA (weakenCutoffA c k) aa0))) :=
      match aa0 return ((shift_A_AA (weakenCutoffA c k) (subst_Z_AA (weakenTrace X0 k) zz1 aa0)) = (subst_Z_AA (weakenTrace X0 k) (shift_A_ZZ c zz1) (shift_A_AA (weakenCutoffA c k) aa0))) with
        | (avar a3) => eq_refl
        | (arec zz2) => (f_equal arec (shift_A__subst_Z_0_ZZ_comm_ind zz2 k c zz1))
      end
    with shift_A__subst_Z_0_ZZ_comm_ind (zz3 : ZZ) (k : Hvl) (c : (Cutoff A)) (zz1 : ZZ) {struct zz3} :
    ((shift_A_ZZ (weakenCutoffA c k) (subst_Z_ZZ (weakenTrace X0 k) zz1 zz3)) = (subst_Z_ZZ (weakenTrace X0 k) (shift_A_ZZ c zz1) (shift_A_ZZ (weakenCutoffA c k) zz3))) :=
      match zz3 return ((shift_A_ZZ (weakenCutoffA c k) (subst_Z_ZZ (weakenTrace X0 k) zz1 zz3)) = (subst_Z_ZZ (weakenTrace X0 k) (shift_A_ZZ c zz1) (shift_A_ZZ (weakenCutoffA c k) zz3))) with
        | (zvar z0) => (shift_A_ZZ_subst_Z_Index0_comm_ind c zz1 k z0)
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal2 shift_A_AA eq_refl (f_equal3 subst_Z_AA (weakenTrace_append Z X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (shift_A__subst_Z_0_AA_comm_ind aa1 (HS A k) c zz1) (f_equal3 subst_Z_AA (eq_sym (weakenTrace_append Z X0 k (HS A H0))) eq_refl eq_refl))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal2 shift_A_BB eq_refl (f_equal3 subst_Z_BB (weakenTrace_append Z X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (shift_A__subst_Z_0_BB_comm_ind bb0 (HS B k) c zz1) (f_equal3 subst_Z_BB (eq_sym (weakenTrace_append Z X0 k (HS B H0))) eq_refl eq_refl))))
      end
    with shift_A__subst_Z_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff A)) (zz1 : ZZ) {struct bb1} :
    ((shift_A_BB (weakenCutoffA c k) (subst_Z_BB (weakenTrace X0 k) zz1 bb1)) = (subst_Z_BB (weakenTrace X0 k) (shift_A_ZZ c zz1) (shift_A_BB (weakenCutoffA c k) bb1))) :=
      match bb1 return ((shift_A_BB (weakenCutoffA c k) (subst_Z_BB (weakenTrace X0 k) zz1 bb1)) = (subst_Z_BB (weakenTrace X0 k) (shift_A_ZZ c zz1) (shift_A_BB (weakenCutoffA c k) bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz4) => (f_equal brec (shift_A__subst_Z_0_ZZ_comm_ind zz4 k c zz1))
      end.
    Fixpoint shift_B__subst_A_0_AA_comm_ind (aa1 : AA) (k : Hvl) (c : (Cutoff B)) (aa0 : AA) {struct aa1} :
    ((shift_B_AA (weakenCutoffB c k) (subst_A_AA (weakenTrace X0 k) aa0 aa1)) = (subst_A_AA (weakenTrace X0 k) (shift_B_AA c aa0) (shift_B_AA (weakenCutoffB c k) aa1))) :=
      match aa1 return ((shift_B_AA (weakenCutoffB c k) (subst_A_AA (weakenTrace X0 k) aa0 aa1)) = (subst_A_AA (weakenTrace X0 k) (shift_B_AA c aa0) (shift_B_AA (weakenCutoffB c k) aa1))) with
        | (avar a3) => (shift_B_AA_subst_A_Index0_comm_ind c aa0 k a3)
        | (arec zz1) => (f_equal arec (shift_B__subst_A_0_ZZ_comm_ind zz1 k c aa0))
      end
    with shift_B__subst_A_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff B)) (aa0 : AA) {struct zz2} :
    ((shift_B_ZZ (weakenCutoffB c k) (subst_A_ZZ (weakenTrace X0 k) aa0 zz2)) = (subst_A_ZZ (weakenTrace X0 k) (shift_B_AA c aa0) (shift_B_ZZ (weakenCutoffB c k) zz2))) :=
      match zz2 return ((shift_B_ZZ (weakenCutoffB c k) (subst_A_ZZ (weakenTrace X0 k) aa0 zz2)) = (subst_A_ZZ (weakenTrace X0 k) (shift_B_AA c aa0) (shift_B_ZZ (weakenCutoffB c k) zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa2) => (f_equal aabs (eq_trans (f_equal2 shift_B_AA eq_refl (f_equal3 subst_A_AA (weakenTrace_append A X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (shift_B__subst_A_0_AA_comm_ind aa2 (HS A k) c aa0) (f_equal3 subst_A_AA (eq_sym (weakenTrace_append A X0 k (HS A H0))) eq_refl eq_refl))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal2 shift_B_BB eq_refl (f_equal3 subst_A_BB (weakenTrace_append A X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (shift_B__subst_A_0_BB_comm_ind bb0 (HS B k) c aa0) (f_equal3 subst_A_BB (eq_sym (weakenTrace_append A X0 k (HS B H0))) eq_refl eq_refl))))
      end
    with shift_B__subst_A_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff B)) (aa0 : AA) {struct bb1} :
    ((shift_B_BB (weakenCutoffB c k) (subst_A_BB (weakenTrace X0 k) aa0 bb1)) = (subst_A_BB (weakenTrace X0 k) (shift_B_AA c aa0) (shift_B_BB (weakenCutoffB c k) bb1))) :=
      match bb1 return ((shift_B_BB (weakenCutoffB c k) (subst_A_BB (weakenTrace X0 k) aa0 bb1)) = (subst_A_BB (weakenTrace X0 k) (shift_B_AA c aa0) (shift_B_BB (weakenCutoffB c k) bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (shift_B__subst_A_0_ZZ_comm_ind zz3 k c aa0))
      end.
    Fixpoint shift_B__subst_B_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff B)) (bb0 : BB) {struct aa0} :
    ((shift_B_AA (weakenCutoffB c k) (subst_B_AA (weakenTrace X0 k) bb0 aa0)) = (subst_B_AA (weakenTrace X0 k) (shift_B_BB c bb0) (shift_B_AA (weakenCutoffB (CS c) k) aa0))) :=
      match aa0 return ((shift_B_AA (weakenCutoffB c k) (subst_B_AA (weakenTrace X0 k) bb0 aa0)) = (subst_B_AA (weakenTrace X0 k) (shift_B_BB c bb0) (shift_B_AA (weakenCutoffB (CS c) k) aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (shift_B__subst_B_0_ZZ_comm_ind zz1 k c bb0))
      end
    with shift_B__subst_B_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff B)) (bb0 : BB) {struct zz2} :
    ((shift_B_ZZ (weakenCutoffB c k) (subst_B_ZZ (weakenTrace X0 k) bb0 zz2)) = (subst_B_ZZ (weakenTrace X0 k) (shift_B_BB c bb0) (shift_B_ZZ (weakenCutoffB (CS c) k) zz2))) :=
      match zz2 return ((shift_B_ZZ (weakenCutoffB c k) (subst_B_ZZ (weakenTrace X0 k) bb0 zz2)) = (subst_B_ZZ (weakenTrace X0 k) (shift_B_BB c bb0) (shift_B_ZZ (weakenCutoffB (CS c) k) zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal2 shift_B_AA eq_refl (f_equal3 subst_B_AA (weakenTrace_append B X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (shift_B__subst_B_0_AA_comm_ind aa1 (HS A k) c bb0) (f_equal3 subst_B_AA (eq_sym (weakenTrace_append B X0 k (HS A H0))) eq_refl eq_refl))))
        | (babs bb1) => (f_equal babs (eq_trans (f_equal2 shift_B_BB eq_refl (f_equal3 subst_B_BB (weakenTrace_append B X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (shift_B__subst_B_0_BB_comm_ind bb1 (HS B k) c bb0) (f_equal3 subst_B_BB (eq_sym (weakenTrace_append B X0 k (HS B H0))) eq_refl eq_refl))))
      end
    with shift_B__subst_B_0_BB_comm_ind (bb2 : BB) (k : Hvl) (c : (Cutoff B)) (bb0 : BB) {struct bb2} :
    ((shift_B_BB (weakenCutoffB c k) (subst_B_BB (weakenTrace X0 k) bb0 bb2)) = (subst_B_BB (weakenTrace X0 k) (shift_B_BB c bb0) (shift_B_BB (weakenCutoffB (CS c) k) bb2))) :=
      match bb2 return ((shift_B_BB (weakenCutoffB c k) (subst_B_BB (weakenTrace X0 k) bb0 bb2)) = (subst_B_BB (weakenTrace X0 k) (shift_B_BB c bb0) (shift_B_BB (weakenCutoffB (CS c) k) bb2))) with
        | (bvar b4) => (shift_B_BB_subst_B_Index0_comm_ind c bb0 k b4)
        | (brec zz3) => (f_equal brec (shift_B__subst_B_0_ZZ_comm_ind zz3 k c bb0))
      end.
    Fixpoint shift_B__subst_Z_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff B)) (zz1 : ZZ) {struct aa0} :
    ((shift_B_AA (weakenCutoffB c k) (subst_Z_AA (weakenTrace X0 k) zz1 aa0)) = (subst_Z_AA (weakenTrace X0 k) (shift_B_ZZ c zz1) (shift_B_AA (weakenCutoffB c k) aa0))) :=
      match aa0 return ((shift_B_AA (weakenCutoffB c k) (subst_Z_AA (weakenTrace X0 k) zz1 aa0)) = (subst_Z_AA (weakenTrace X0 k) (shift_B_ZZ c zz1) (shift_B_AA (weakenCutoffB c k) aa0))) with
        | (avar a3) => eq_refl
        | (arec zz2) => (f_equal arec (shift_B__subst_Z_0_ZZ_comm_ind zz2 k c zz1))
      end
    with shift_B__subst_Z_0_ZZ_comm_ind (zz3 : ZZ) (k : Hvl) (c : (Cutoff B)) (zz1 : ZZ) {struct zz3} :
    ((shift_B_ZZ (weakenCutoffB c k) (subst_Z_ZZ (weakenTrace X0 k) zz1 zz3)) = (subst_Z_ZZ (weakenTrace X0 k) (shift_B_ZZ c zz1) (shift_B_ZZ (weakenCutoffB c k) zz3))) :=
      match zz3 return ((shift_B_ZZ (weakenCutoffB c k) (subst_Z_ZZ (weakenTrace X0 k) zz1 zz3)) = (subst_Z_ZZ (weakenTrace X0 k) (shift_B_ZZ c zz1) (shift_B_ZZ (weakenCutoffB c k) zz3))) with
        | (zvar z0) => (shift_B_ZZ_subst_Z_Index0_comm_ind c zz1 k z0)
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal2 shift_B_AA eq_refl (f_equal3 subst_Z_AA (weakenTrace_append Z X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (shift_B__subst_Z_0_AA_comm_ind aa1 (HS A k) c zz1) (f_equal3 subst_Z_AA (eq_sym (weakenTrace_append Z X0 k (HS A H0))) eq_refl eq_refl))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal2 shift_B_BB eq_refl (f_equal3 subst_Z_BB (weakenTrace_append Z X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (shift_B__subst_Z_0_BB_comm_ind bb0 (HS B k) c zz1) (f_equal3 subst_Z_BB (eq_sym (weakenTrace_append Z X0 k (HS B H0))) eq_refl eq_refl))))
      end
    with shift_B__subst_Z_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff B)) (zz1 : ZZ) {struct bb1} :
    ((shift_B_BB (weakenCutoffB c k) (subst_Z_BB (weakenTrace X0 k) zz1 bb1)) = (subst_Z_BB (weakenTrace X0 k) (shift_B_ZZ c zz1) (shift_B_BB (weakenCutoffB c k) bb1))) :=
      match bb1 return ((shift_B_BB (weakenCutoffB c k) (subst_Z_BB (weakenTrace X0 k) zz1 bb1)) = (subst_Z_BB (weakenTrace X0 k) (shift_B_ZZ c zz1) (shift_B_BB (weakenCutoffB c k) bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz4) => (f_equal brec (shift_B__subst_Z_0_ZZ_comm_ind zz4 k c zz1))
      end.
    Fixpoint shift_Z__subst_A_0_AA_comm_ind (aa1 : AA) (k : Hvl) (c : (Cutoff Z)) (aa0 : AA) {struct aa1} :
    ((shift_Z_AA (weakenCutoffZ c k) (subst_A_AA (weakenTrace X0 k) aa0 aa1)) = (subst_A_AA (weakenTrace X0 k) (shift_Z_AA c aa0) (shift_Z_AA (weakenCutoffZ c k) aa1))) :=
      match aa1 return ((shift_Z_AA (weakenCutoffZ c k) (subst_A_AA (weakenTrace X0 k) aa0 aa1)) = (subst_A_AA (weakenTrace X0 k) (shift_Z_AA c aa0) (shift_Z_AA (weakenCutoffZ c k) aa1))) with
        | (avar a3) => (shift_Z_AA_subst_A_Index0_comm_ind c aa0 k a3)
        | (arec zz1) => (f_equal arec (shift_Z__subst_A_0_ZZ_comm_ind zz1 k c aa0))
      end
    with shift_Z__subst_A_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff Z)) (aa0 : AA) {struct zz2} :
    ((shift_Z_ZZ (weakenCutoffZ c k) (subst_A_ZZ (weakenTrace X0 k) aa0 zz2)) = (subst_A_ZZ (weakenTrace X0 k) (shift_Z_AA c aa0) (shift_Z_ZZ (weakenCutoffZ c k) zz2))) :=
      match zz2 return ((shift_Z_ZZ (weakenCutoffZ c k) (subst_A_ZZ (weakenTrace X0 k) aa0 zz2)) = (subst_A_ZZ (weakenTrace X0 k) (shift_Z_AA c aa0) (shift_Z_ZZ (weakenCutoffZ c k) zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa2) => (f_equal aabs (eq_trans (f_equal2 shift_Z_AA eq_refl (f_equal3 subst_A_AA (weakenTrace_append A X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (shift_Z__subst_A_0_AA_comm_ind aa2 (HS A k) c aa0) (f_equal3 subst_A_AA (eq_sym (weakenTrace_append A X0 k (HS A H0))) eq_refl eq_refl))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal2 shift_Z_BB eq_refl (f_equal3 subst_A_BB (weakenTrace_append A X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (shift_Z__subst_A_0_BB_comm_ind bb0 (HS B k) c aa0) (f_equal3 subst_A_BB (eq_sym (weakenTrace_append A X0 k (HS B H0))) eq_refl eq_refl))))
      end
    with shift_Z__subst_A_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff Z)) (aa0 : AA) {struct bb1} :
    ((shift_Z_BB (weakenCutoffZ c k) (subst_A_BB (weakenTrace X0 k) aa0 bb1)) = (subst_A_BB (weakenTrace X0 k) (shift_Z_AA c aa0) (shift_Z_BB (weakenCutoffZ c k) bb1))) :=
      match bb1 return ((shift_Z_BB (weakenCutoffZ c k) (subst_A_BB (weakenTrace X0 k) aa0 bb1)) = (subst_A_BB (weakenTrace X0 k) (shift_Z_AA c aa0) (shift_Z_BB (weakenCutoffZ c k) bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (shift_Z__subst_A_0_ZZ_comm_ind zz3 k c aa0))
      end.
    Fixpoint shift_Z__subst_B_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff Z)) (bb0 : BB) {struct aa0} :
    ((shift_Z_AA (weakenCutoffZ c k) (subst_B_AA (weakenTrace X0 k) bb0 aa0)) = (subst_B_AA (weakenTrace X0 k) (shift_Z_BB c bb0) (shift_Z_AA (weakenCutoffZ c k) aa0))) :=
      match aa0 return ((shift_Z_AA (weakenCutoffZ c k) (subst_B_AA (weakenTrace X0 k) bb0 aa0)) = (subst_B_AA (weakenTrace X0 k) (shift_Z_BB c bb0) (shift_Z_AA (weakenCutoffZ c k) aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (shift_Z__subst_B_0_ZZ_comm_ind zz1 k c bb0))
      end
    with shift_Z__subst_B_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (c : (Cutoff Z)) (bb0 : BB) {struct zz2} :
    ((shift_Z_ZZ (weakenCutoffZ c k) (subst_B_ZZ (weakenTrace X0 k) bb0 zz2)) = (subst_B_ZZ (weakenTrace X0 k) (shift_Z_BB c bb0) (shift_Z_ZZ (weakenCutoffZ c k) zz2))) :=
      match zz2 return ((shift_Z_ZZ (weakenCutoffZ c k) (subst_B_ZZ (weakenTrace X0 k) bb0 zz2)) = (subst_B_ZZ (weakenTrace X0 k) (shift_Z_BB c bb0) (shift_Z_ZZ (weakenCutoffZ c k) zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal2 shift_Z_AA eq_refl (f_equal3 subst_B_AA (weakenTrace_append B X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (shift_Z__subst_B_0_AA_comm_ind aa1 (HS A k) c bb0) (f_equal3 subst_B_AA (eq_sym (weakenTrace_append B X0 k (HS A H0))) eq_refl eq_refl))))
        | (babs bb1) => (f_equal babs (eq_trans (f_equal2 shift_Z_BB eq_refl (f_equal3 subst_B_BB (weakenTrace_append B X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (shift_Z__subst_B_0_BB_comm_ind bb1 (HS B k) c bb0) (f_equal3 subst_B_BB (eq_sym (weakenTrace_append B X0 k (HS B H0))) eq_refl eq_refl))))
      end
    with shift_Z__subst_B_0_BB_comm_ind (bb2 : BB) (k : Hvl) (c : (Cutoff Z)) (bb0 : BB) {struct bb2} :
    ((shift_Z_BB (weakenCutoffZ c k) (subst_B_BB (weakenTrace X0 k) bb0 bb2)) = (subst_B_BB (weakenTrace X0 k) (shift_Z_BB c bb0) (shift_Z_BB (weakenCutoffZ c k) bb2))) :=
      match bb2 return ((shift_Z_BB (weakenCutoffZ c k) (subst_B_BB (weakenTrace X0 k) bb0 bb2)) = (subst_B_BB (weakenTrace X0 k) (shift_Z_BB c bb0) (shift_Z_BB (weakenCutoffZ c k) bb2))) with
        | (bvar b4) => (shift_Z_BB_subst_B_Index0_comm_ind c bb0 k b4)
        | (brec zz3) => (f_equal brec (shift_Z__subst_B_0_ZZ_comm_ind zz3 k c bb0))
      end.
    Fixpoint shift_Z__subst_Z_0_AA_comm_ind (aa0 : AA) (k : Hvl) (c : (Cutoff Z)) (zz1 : ZZ) {struct aa0} :
    ((shift_Z_AA (weakenCutoffZ c k) (subst_Z_AA (weakenTrace X0 k) zz1 aa0)) = (subst_Z_AA (weakenTrace X0 k) (shift_Z_ZZ c zz1) (shift_Z_AA (weakenCutoffZ (CS c) k) aa0))) :=
      match aa0 return ((shift_Z_AA (weakenCutoffZ c k) (subst_Z_AA (weakenTrace X0 k) zz1 aa0)) = (subst_Z_AA (weakenTrace X0 k) (shift_Z_ZZ c zz1) (shift_Z_AA (weakenCutoffZ (CS c) k) aa0))) with
        | (avar a3) => eq_refl
        | (arec zz2) => (f_equal arec (shift_Z__subst_Z_0_ZZ_comm_ind zz2 k c zz1))
      end
    with shift_Z__subst_Z_0_ZZ_comm_ind (zz3 : ZZ) (k : Hvl) (c : (Cutoff Z)) (zz1 : ZZ) {struct zz3} :
    ((shift_Z_ZZ (weakenCutoffZ c k) (subst_Z_ZZ (weakenTrace X0 k) zz1 zz3)) = (subst_Z_ZZ (weakenTrace X0 k) (shift_Z_ZZ c zz1) (shift_Z_ZZ (weakenCutoffZ (CS c) k) zz3))) :=
      match zz3 return ((shift_Z_ZZ (weakenCutoffZ c k) (subst_Z_ZZ (weakenTrace X0 k) zz1 zz3)) = (subst_Z_ZZ (weakenTrace X0 k) (shift_Z_ZZ c zz1) (shift_Z_ZZ (weakenCutoffZ (CS c) k) zz3))) with
        | (zvar z0) => (shift_Z_ZZ_subst_Z_Index0_comm_ind c zz1 k z0)
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal2 shift_Z_AA eq_refl (f_equal3 subst_Z_AA (weakenTrace_append Z X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (shift_Z__subst_Z_0_AA_comm_ind aa1 (HS A k) c zz1) (f_equal3 subst_Z_AA (eq_sym (weakenTrace_append Z X0 k (HS A H0))) eq_refl eq_refl))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal2 shift_Z_BB eq_refl (f_equal3 subst_Z_BB (weakenTrace_append Z X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (shift_Z__subst_Z_0_BB_comm_ind bb0 (HS B k) c zz1) (f_equal3 subst_Z_BB (eq_sym (weakenTrace_append Z X0 k (HS B H0))) eq_refl eq_refl))))
      end
    with shift_Z__subst_Z_0_BB_comm_ind (bb1 : BB) (k : Hvl) (c : (Cutoff Z)) (zz1 : ZZ) {struct bb1} :
    ((shift_Z_BB (weakenCutoffZ c k) (subst_Z_BB (weakenTrace X0 k) zz1 bb1)) = (subst_Z_BB (weakenTrace X0 k) (shift_Z_ZZ c zz1) (shift_Z_BB (weakenCutoffZ (CS c) k) bb1))) :=
      match bb1 return ((shift_Z_BB (weakenCutoffZ c k) (subst_Z_BB (weakenTrace X0 k) zz1 bb1)) = (subst_Z_BB (weakenTrace X0 k) (shift_Z_ZZ c zz1) (shift_Z_BB (weakenCutoffZ (CS c) k) bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz4) => (f_equal brec (shift_Z__subst_Z_0_ZZ_comm_ind zz4 k c zz1))
      end.
  End ShiftSubstCommInd.
  Section ShiftSubstComm.
    Definition shift_A_AA_subst_A_AA0_comm (aa1 : AA) : (forall (c : (Cutoff A)) (aa0 : AA) ,
      ((shift_A_AA c (subst_A_AA X0 aa0 aa1)) = (subst_A_AA X0 (shift_A_AA c aa0) (shift_A_AA (CS c) aa1)))) := (shift_A__subst_A_0_AA_comm_ind aa1 H0).
    Definition shift_A_ZZ_subst_A_ZZ0_comm (zz1 : ZZ) : (forall (c : (Cutoff A)) (aa0 : AA) ,
      ((shift_A_ZZ c (subst_A_ZZ X0 aa0 zz1)) = (subst_A_ZZ X0 (shift_A_AA c aa0) (shift_A_ZZ (CS c) zz1)))) := (shift_A__subst_A_0_ZZ_comm_ind zz1 H0).
    Definition shift_A_BB_subst_A_BB0_comm (bb0 : BB) : (forall (c : (Cutoff A)) (aa0 : AA) ,
      ((shift_A_BB c (subst_A_BB X0 aa0 bb0)) = (subst_A_BB X0 (shift_A_AA c aa0) (shift_A_BB (CS c) bb0)))) := (shift_A__subst_A_0_BB_comm_ind bb0 H0).
    Definition shift_A_AA_subst_B_AA0_comm (aa0 : AA) : (forall (c : (Cutoff A)) (bb0 : BB) ,
      ((shift_A_AA c (subst_B_AA X0 bb0 aa0)) = (subst_B_AA X0 (shift_A_BB c bb0) (shift_A_AA c aa0)))) := (shift_A__subst_B_0_AA_comm_ind aa0 H0).
    Definition shift_A_ZZ_subst_B_ZZ0_comm (zz1 : ZZ) : (forall (c : (Cutoff A)) (bb0 : BB) ,
      ((shift_A_ZZ c (subst_B_ZZ X0 bb0 zz1)) = (subst_B_ZZ X0 (shift_A_BB c bb0) (shift_A_ZZ c zz1)))) := (shift_A__subst_B_0_ZZ_comm_ind zz1 H0).
    Definition shift_A_BB_subst_B_BB0_comm (bb1 : BB) : (forall (c : (Cutoff A)) (bb0 : BB) ,
      ((shift_A_BB c (subst_B_BB X0 bb0 bb1)) = (subst_B_BB X0 (shift_A_BB c bb0) (shift_A_BB c bb1)))) := (shift_A__subst_B_0_BB_comm_ind bb1 H0).
    Definition shift_A_AA_subst_Z_AA0_comm (aa0 : AA) : (forall (c : (Cutoff A)) (zz1 : ZZ) ,
      ((shift_A_AA c (subst_Z_AA X0 zz1 aa0)) = (subst_Z_AA X0 (shift_A_ZZ c zz1) (shift_A_AA c aa0)))) := (shift_A__subst_Z_0_AA_comm_ind aa0 H0).
    Definition shift_A_ZZ_subst_Z_ZZ0_comm (zz2 : ZZ) : (forall (c : (Cutoff A)) (zz1 : ZZ) ,
      ((shift_A_ZZ c (subst_Z_ZZ X0 zz1 zz2)) = (subst_Z_ZZ X0 (shift_A_ZZ c zz1) (shift_A_ZZ c zz2)))) := (shift_A__subst_Z_0_ZZ_comm_ind zz2 H0).
    Definition shift_A_BB_subst_Z_BB0_comm (bb0 : BB) : (forall (c : (Cutoff A)) (zz1 : ZZ) ,
      ((shift_A_BB c (subst_Z_BB X0 zz1 bb0)) = (subst_Z_BB X0 (shift_A_ZZ c zz1) (shift_A_BB c bb0)))) := (shift_A__subst_Z_0_BB_comm_ind bb0 H0).
    Definition shift_B_AA_subst_A_AA0_comm (aa1 : AA) : (forall (c : (Cutoff B)) (aa0 : AA) ,
      ((shift_B_AA c (subst_A_AA X0 aa0 aa1)) = (subst_A_AA X0 (shift_B_AA c aa0) (shift_B_AA c aa1)))) := (shift_B__subst_A_0_AA_comm_ind aa1 H0).
    Definition shift_B_ZZ_subst_A_ZZ0_comm (zz1 : ZZ) : (forall (c : (Cutoff B)) (aa0 : AA) ,
      ((shift_B_ZZ c (subst_A_ZZ X0 aa0 zz1)) = (subst_A_ZZ X0 (shift_B_AA c aa0) (shift_B_ZZ c zz1)))) := (shift_B__subst_A_0_ZZ_comm_ind zz1 H0).
    Definition shift_B_BB_subst_A_BB0_comm (bb0 : BB) : (forall (c : (Cutoff B)) (aa0 : AA) ,
      ((shift_B_BB c (subst_A_BB X0 aa0 bb0)) = (subst_A_BB X0 (shift_B_AA c aa0) (shift_B_BB c bb0)))) := (shift_B__subst_A_0_BB_comm_ind bb0 H0).
    Definition shift_B_AA_subst_B_AA0_comm (aa0 : AA) : (forall (c : (Cutoff B)) (bb0 : BB) ,
      ((shift_B_AA c (subst_B_AA X0 bb0 aa0)) = (subst_B_AA X0 (shift_B_BB c bb0) (shift_B_AA (CS c) aa0)))) := (shift_B__subst_B_0_AA_comm_ind aa0 H0).
    Definition shift_B_ZZ_subst_B_ZZ0_comm (zz1 : ZZ) : (forall (c : (Cutoff B)) (bb0 : BB) ,
      ((shift_B_ZZ c (subst_B_ZZ X0 bb0 zz1)) = (subst_B_ZZ X0 (shift_B_BB c bb0) (shift_B_ZZ (CS c) zz1)))) := (shift_B__subst_B_0_ZZ_comm_ind zz1 H0).
    Definition shift_B_BB_subst_B_BB0_comm (bb1 : BB) : (forall (c : (Cutoff B)) (bb0 : BB) ,
      ((shift_B_BB c (subst_B_BB X0 bb0 bb1)) = (subst_B_BB X0 (shift_B_BB c bb0) (shift_B_BB (CS c) bb1)))) := (shift_B__subst_B_0_BB_comm_ind bb1 H0).
    Definition shift_B_AA_subst_Z_AA0_comm (aa0 : AA) : (forall (c : (Cutoff B)) (zz1 : ZZ) ,
      ((shift_B_AA c (subst_Z_AA X0 zz1 aa0)) = (subst_Z_AA X0 (shift_B_ZZ c zz1) (shift_B_AA c aa0)))) := (shift_B__subst_Z_0_AA_comm_ind aa0 H0).
    Definition shift_B_ZZ_subst_Z_ZZ0_comm (zz2 : ZZ) : (forall (c : (Cutoff B)) (zz1 : ZZ) ,
      ((shift_B_ZZ c (subst_Z_ZZ X0 zz1 zz2)) = (subst_Z_ZZ X0 (shift_B_ZZ c zz1) (shift_B_ZZ c zz2)))) := (shift_B__subst_Z_0_ZZ_comm_ind zz2 H0).
    Definition shift_B_BB_subst_Z_BB0_comm (bb0 : BB) : (forall (c : (Cutoff B)) (zz1 : ZZ) ,
      ((shift_B_BB c (subst_Z_BB X0 zz1 bb0)) = (subst_Z_BB X0 (shift_B_ZZ c zz1) (shift_B_BB c bb0)))) := (shift_B__subst_Z_0_BB_comm_ind bb0 H0).
    Definition shift_Z_AA_subst_A_AA0_comm (aa1 : AA) : (forall (c : (Cutoff Z)) (aa0 : AA) ,
      ((shift_Z_AA c (subst_A_AA X0 aa0 aa1)) = (subst_A_AA X0 (shift_Z_AA c aa0) (shift_Z_AA c aa1)))) := (shift_Z__subst_A_0_AA_comm_ind aa1 H0).
    Definition shift_Z_ZZ_subst_A_ZZ0_comm (zz1 : ZZ) : (forall (c : (Cutoff Z)) (aa0 : AA) ,
      ((shift_Z_ZZ c (subst_A_ZZ X0 aa0 zz1)) = (subst_A_ZZ X0 (shift_Z_AA c aa0) (shift_Z_ZZ c zz1)))) := (shift_Z__subst_A_0_ZZ_comm_ind zz1 H0).
    Definition shift_Z_BB_subst_A_BB0_comm (bb0 : BB) : (forall (c : (Cutoff Z)) (aa0 : AA) ,
      ((shift_Z_BB c (subst_A_BB X0 aa0 bb0)) = (subst_A_BB X0 (shift_Z_AA c aa0) (shift_Z_BB c bb0)))) := (shift_Z__subst_A_0_BB_comm_ind bb0 H0).
    Definition shift_Z_AA_subst_B_AA0_comm (aa0 : AA) : (forall (c : (Cutoff Z)) (bb0 : BB) ,
      ((shift_Z_AA c (subst_B_AA X0 bb0 aa0)) = (subst_B_AA X0 (shift_Z_BB c bb0) (shift_Z_AA c aa0)))) := (shift_Z__subst_B_0_AA_comm_ind aa0 H0).
    Definition shift_Z_ZZ_subst_B_ZZ0_comm (zz1 : ZZ) : (forall (c : (Cutoff Z)) (bb0 : BB) ,
      ((shift_Z_ZZ c (subst_B_ZZ X0 bb0 zz1)) = (subst_B_ZZ X0 (shift_Z_BB c bb0) (shift_Z_ZZ c zz1)))) := (shift_Z__subst_B_0_ZZ_comm_ind zz1 H0).
    Definition shift_Z_BB_subst_B_BB0_comm (bb1 : BB) : (forall (c : (Cutoff Z)) (bb0 : BB) ,
      ((shift_Z_BB c (subst_B_BB X0 bb0 bb1)) = (subst_B_BB X0 (shift_Z_BB c bb0) (shift_Z_BB c bb1)))) := (shift_Z__subst_B_0_BB_comm_ind bb1 H0).
    Definition shift_Z_AA_subst_Z_AA0_comm (aa0 : AA) : (forall (c : (Cutoff Z)) (zz1 : ZZ) ,
      ((shift_Z_AA c (subst_Z_AA X0 zz1 aa0)) = (subst_Z_AA X0 (shift_Z_ZZ c zz1) (shift_Z_AA (CS c) aa0)))) := (shift_Z__subst_Z_0_AA_comm_ind aa0 H0).
    Definition shift_Z_ZZ_subst_Z_ZZ0_comm (zz2 : ZZ) : (forall (c : (Cutoff Z)) (zz1 : ZZ) ,
      ((shift_Z_ZZ c (subst_Z_ZZ X0 zz1 zz2)) = (subst_Z_ZZ X0 (shift_Z_ZZ c zz1) (shift_Z_ZZ (CS c) zz2)))) := (shift_Z__subst_Z_0_ZZ_comm_ind zz2 H0).
    Definition shift_Z_BB_subst_Z_BB0_comm (bb0 : BB) : (forall (c : (Cutoff Z)) (zz1 : ZZ) ,
      ((shift_Z_BB c (subst_Z_BB X0 zz1 bb0)) = (subst_Z_BB X0 (shift_Z_ZZ c zz1) (shift_Z_BB (CS c) bb0)))) := (shift_Z__subst_Z_0_BB_comm_ind bb0 H0).
  End ShiftSubstComm.
  Section SubstShiftIndexCommInd.
    Lemma subst_A_Index_shift_A_AA0_comm_ind (d : (Trace A)) (aa0 : AA) :
      (forall (k : Hvl) (a3 : (Index A)) ,
        ((subst_A_Index (weakenTrace (XS A d) k) aa0 (shift_A_Index (weakenCutoffA C0 k) a3)) = (shift_A_AA (weakenCutoffA C0 k) (subst_A_Index (weakenTrace d k) aa0 a3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_A_Index_shift_B_AA0_comm_ind (d : (Trace A)) (aa0 : AA) :
      (forall (k : Hvl) (a3 : (Index A)) ,
        ((subst_A_Index (weakenTrace (XS B d) k) aa0 a3) = (shift_B_AA (weakenCutoffB C0 k) (subst_A_Index (weakenTrace d k) aa0 a3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_A_Index_shift_Z_AA0_comm_ind (d : (Trace A)) (aa0 : AA) :
      (forall (k : Hvl) (a3 : (Index A)) ,
        ((subst_A_Index (weakenTrace (XS Z d) k) aa0 a3) = (shift_Z_AA (weakenCutoffZ C0 k) (subst_A_Index (weakenTrace d k) aa0 a3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_B_Index_shift_A_BB0_comm_ind (d : (Trace B)) (bb0 : BB) :
      (forall (k : Hvl) (b3 : (Index B)) ,
        ((subst_B_Index (weakenTrace (XS A d) k) bb0 b3) = (shift_A_BB (weakenCutoffA C0 k) (subst_B_Index (weakenTrace d k) bb0 b3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_B_Index_shift_B_BB0_comm_ind (d : (Trace B)) (bb0 : BB) :
      (forall (k : Hvl) (b3 : (Index B)) ,
        ((subst_B_Index (weakenTrace (XS B d) k) bb0 (shift_B_Index (weakenCutoffB C0 k) b3)) = (shift_B_BB (weakenCutoffB C0 k) (subst_B_Index (weakenTrace d k) bb0 b3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_B_Index_shift_Z_BB0_comm_ind (d : (Trace B)) (bb0 : BB) :
      (forall (k : Hvl) (b3 : (Index B)) ,
        ((subst_B_Index (weakenTrace (XS Z d) k) bb0 b3) = (shift_Z_BB (weakenCutoffZ C0 k) (subst_B_Index (weakenTrace d k) bb0 b3)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_Z_Index_shift_A_ZZ0_comm_ind (d : (Trace Z)) (zz1 : ZZ) :
      (forall (k : Hvl) (z0 : (Index Z)) ,
        ((subst_Z_Index (weakenTrace (XS A d) k) zz1 z0) = (shift_A_ZZ (weakenCutoffA C0 k) (subst_Z_Index (weakenTrace d k) zz1 z0)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_Z_Index_shift_B_ZZ0_comm_ind (d : (Trace Z)) (zz1 : ZZ) :
      (forall (k : Hvl) (z0 : (Index Z)) ,
        ((subst_Z_Index (weakenTrace (XS B d) k) zz1 z0) = (shift_B_ZZ (weakenCutoffB C0 k) (subst_Z_Index (weakenTrace d k) zz1 z0)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
    Lemma subst_Z_Index_shift_Z_ZZ0_comm_ind (d : (Trace Z)) (zz1 : ZZ) :
      (forall (k : Hvl) (z0 : (Index Z)) ,
        ((subst_Z_Index (weakenTrace (XS Z d) k) zz1 (shift_Z_Index (weakenCutoffZ C0 k) z0)) = (shift_Z_ZZ (weakenCutoffZ C0 k) (subst_Z_Index (weakenTrace d k) zz1 z0)))).
    Proof.
      needleGenericShiftSubstIndexCommInd .
    Qed.
  End SubstShiftIndexCommInd.
  Section SubstShiftCommInd.
    Fixpoint subst_A__shift_A_0_AA_comm_ind (aa1 : AA) (k : Hvl) (d : (Trace A)) (aa0 : AA) {struct aa1} :
    ((subst_A_AA (weakenTrace (XS A d) k) aa0 (shift_A_AA (weakenCutoffA C0 k) aa1)) = (shift_A_AA (weakenCutoffA C0 k) (subst_A_AA (weakenTrace d k) aa0 aa1))) :=
      match aa1 return ((subst_A_AA (weakenTrace (XS A d) k) aa0 (shift_A_AA (weakenCutoffA C0 k) aa1)) = (shift_A_AA (weakenCutoffA C0 k) (subst_A_AA (weakenTrace d k) aa0 aa1))) with
        | (avar a3) => (subst_A_Index_shift_A_AA0_comm_ind d aa0 k a3)
        | (arec zz1) => (f_equal arec (subst_A__shift_A_0_ZZ_comm_ind zz1 k d aa0))
      end
    with subst_A__shift_A_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (d : (Trace A)) (aa0 : AA) {struct zz2} :
    ((subst_A_ZZ (weakenTrace (XS A d) k) aa0 (shift_A_ZZ (weakenCutoffA C0 k) zz2)) = (shift_A_ZZ (weakenCutoffA C0 k) (subst_A_ZZ (weakenTrace d k) aa0 zz2))) :=
      match zz2 return ((subst_A_ZZ (weakenTrace (XS A d) k) aa0 (shift_A_ZZ (weakenCutoffA C0 k) zz2)) = (shift_A_ZZ (weakenCutoffA C0 k) (subst_A_ZZ (weakenTrace d k) aa0 zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa2) => (f_equal aabs (eq_trans (f_equal3 subst_A_AA (weakenTrace_append A (XS A d) k (HS A H0)) eq_refl eq_refl) (eq_trans (subst_A__shift_A_0_AA_comm_ind aa2 (HS A k) d aa0) (f_equal2 shift_A_AA eq_refl (f_equal3 subst_A_AA (eq_sym (weakenTrace_append A d k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal3 subst_A_BB (weakenTrace_append A (XS A d) k (HS B H0)) eq_refl eq_refl) (eq_trans (subst_A__shift_A_0_BB_comm_ind bb0 (HS B k) d aa0) (f_equal2 shift_A_BB eq_refl (f_equal3 subst_A_BB (eq_sym (weakenTrace_append A d k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_A__shift_A_0_BB_comm_ind (bb1 : BB) (k : Hvl) (d : (Trace A)) (aa0 : AA) {struct bb1} :
    ((subst_A_BB (weakenTrace (XS A d) k) aa0 (shift_A_BB (weakenCutoffA C0 k) bb1)) = (shift_A_BB (weakenCutoffA C0 k) (subst_A_BB (weakenTrace d k) aa0 bb1))) :=
      match bb1 return ((subst_A_BB (weakenTrace (XS A d) k) aa0 (shift_A_BB (weakenCutoffA C0 k) bb1)) = (shift_A_BB (weakenCutoffA C0 k) (subst_A_BB (weakenTrace d k) aa0 bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (subst_A__shift_A_0_ZZ_comm_ind zz3 k d aa0))
      end.
    Fixpoint subst_A__shift_B_0_AA_comm_ind (aa1 : AA) (k : Hvl) (d : (Trace A)) (aa0 : AA) {struct aa1} :
    ((subst_A_AA (weakenTrace (XS B d) k) aa0 (shift_B_AA (weakenCutoffB C0 k) aa1)) = (shift_B_AA (weakenCutoffB C0 k) (subst_A_AA (weakenTrace d k) aa0 aa1))) :=
      match aa1 return ((subst_A_AA (weakenTrace (XS B d) k) aa0 (shift_B_AA (weakenCutoffB C0 k) aa1)) = (shift_B_AA (weakenCutoffB C0 k) (subst_A_AA (weakenTrace d k) aa0 aa1))) with
        | (avar a3) => (subst_A_Index_shift_B_AA0_comm_ind d aa0 k a3)
        | (arec zz1) => (f_equal arec (subst_A__shift_B_0_ZZ_comm_ind zz1 k d aa0))
      end
    with subst_A__shift_B_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (d : (Trace A)) (aa0 : AA) {struct zz2} :
    ((subst_A_ZZ (weakenTrace (XS B d) k) aa0 (shift_B_ZZ (weakenCutoffB C0 k) zz2)) = (shift_B_ZZ (weakenCutoffB C0 k) (subst_A_ZZ (weakenTrace d k) aa0 zz2))) :=
      match zz2 return ((subst_A_ZZ (weakenTrace (XS B d) k) aa0 (shift_B_ZZ (weakenCutoffB C0 k) zz2)) = (shift_B_ZZ (weakenCutoffB C0 k) (subst_A_ZZ (weakenTrace d k) aa0 zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa2) => (f_equal aabs (eq_trans (f_equal3 subst_A_AA (weakenTrace_append A (XS B d) k (HS A H0)) eq_refl eq_refl) (eq_trans (subst_A__shift_B_0_AA_comm_ind aa2 (HS A k) d aa0) (f_equal2 shift_B_AA eq_refl (f_equal3 subst_A_AA (eq_sym (weakenTrace_append A d k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal3 subst_A_BB (weakenTrace_append A (XS B d) k (HS B H0)) eq_refl eq_refl) (eq_trans (subst_A__shift_B_0_BB_comm_ind bb0 (HS B k) d aa0) (f_equal2 shift_B_BB eq_refl (f_equal3 subst_A_BB (eq_sym (weakenTrace_append A d k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_A__shift_B_0_BB_comm_ind (bb1 : BB) (k : Hvl) (d : (Trace A)) (aa0 : AA) {struct bb1} :
    ((subst_A_BB (weakenTrace (XS B d) k) aa0 (shift_B_BB (weakenCutoffB C0 k) bb1)) = (shift_B_BB (weakenCutoffB C0 k) (subst_A_BB (weakenTrace d k) aa0 bb1))) :=
      match bb1 return ((subst_A_BB (weakenTrace (XS B d) k) aa0 (shift_B_BB (weakenCutoffB C0 k) bb1)) = (shift_B_BB (weakenCutoffB C0 k) (subst_A_BB (weakenTrace d k) aa0 bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (subst_A__shift_B_0_ZZ_comm_ind zz3 k d aa0))
      end.
    Fixpoint subst_A__shift_Z_0_AA_comm_ind (aa1 : AA) (k : Hvl) (d : (Trace A)) (aa0 : AA) {struct aa1} :
    ((subst_A_AA (weakenTrace (XS Z d) k) aa0 (shift_Z_AA (weakenCutoffZ C0 k) aa1)) = (shift_Z_AA (weakenCutoffZ C0 k) (subst_A_AA (weakenTrace d k) aa0 aa1))) :=
      match aa1 return ((subst_A_AA (weakenTrace (XS Z d) k) aa0 (shift_Z_AA (weakenCutoffZ C0 k) aa1)) = (shift_Z_AA (weakenCutoffZ C0 k) (subst_A_AA (weakenTrace d k) aa0 aa1))) with
        | (avar a3) => (subst_A_Index_shift_Z_AA0_comm_ind d aa0 k a3)
        | (arec zz1) => (f_equal arec (subst_A__shift_Z_0_ZZ_comm_ind zz1 k d aa0))
      end
    with subst_A__shift_Z_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (d : (Trace A)) (aa0 : AA) {struct zz2} :
    ((subst_A_ZZ (weakenTrace (XS Z d) k) aa0 (shift_Z_ZZ (weakenCutoffZ C0 k) zz2)) = (shift_Z_ZZ (weakenCutoffZ C0 k) (subst_A_ZZ (weakenTrace d k) aa0 zz2))) :=
      match zz2 return ((subst_A_ZZ (weakenTrace (XS Z d) k) aa0 (shift_Z_ZZ (weakenCutoffZ C0 k) zz2)) = (shift_Z_ZZ (weakenCutoffZ C0 k) (subst_A_ZZ (weakenTrace d k) aa0 zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa2) => (f_equal aabs (eq_trans (f_equal3 subst_A_AA (weakenTrace_append A (XS Z d) k (HS A H0)) eq_refl eq_refl) (eq_trans (subst_A__shift_Z_0_AA_comm_ind aa2 (HS A k) d aa0) (f_equal2 shift_Z_AA eq_refl (f_equal3 subst_A_AA (eq_sym (weakenTrace_append A d k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal3 subst_A_BB (weakenTrace_append A (XS Z d) k (HS B H0)) eq_refl eq_refl) (eq_trans (subst_A__shift_Z_0_BB_comm_ind bb0 (HS B k) d aa0) (f_equal2 shift_Z_BB eq_refl (f_equal3 subst_A_BB (eq_sym (weakenTrace_append A d k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_A__shift_Z_0_BB_comm_ind (bb1 : BB) (k : Hvl) (d : (Trace A)) (aa0 : AA) {struct bb1} :
    ((subst_A_BB (weakenTrace (XS Z d) k) aa0 (shift_Z_BB (weakenCutoffZ C0 k) bb1)) = (shift_Z_BB (weakenCutoffZ C0 k) (subst_A_BB (weakenTrace d k) aa0 bb1))) :=
      match bb1 return ((subst_A_BB (weakenTrace (XS Z d) k) aa0 (shift_Z_BB (weakenCutoffZ C0 k) bb1)) = (shift_Z_BB (weakenCutoffZ C0 k) (subst_A_BB (weakenTrace d k) aa0 bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (subst_A__shift_Z_0_ZZ_comm_ind zz3 k d aa0))
      end.
    Fixpoint subst_B__shift_A_0_AA_comm_ind (aa0 : AA) (k : Hvl) (d : (Trace B)) (bb0 : BB) {struct aa0} :
    ((subst_B_AA (weakenTrace (XS A d) k) bb0 (shift_A_AA (weakenCutoffA C0 k) aa0)) = (shift_A_AA (weakenCutoffA C0 k) (subst_B_AA (weakenTrace d k) bb0 aa0))) :=
      match aa0 return ((subst_B_AA (weakenTrace (XS A d) k) bb0 (shift_A_AA (weakenCutoffA C0 k) aa0)) = (shift_A_AA (weakenCutoffA C0 k) (subst_B_AA (weakenTrace d k) bb0 aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (subst_B__shift_A_0_ZZ_comm_ind zz1 k d bb0))
      end
    with subst_B__shift_A_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (d : (Trace B)) (bb0 : BB) {struct zz2} :
    ((subst_B_ZZ (weakenTrace (XS A d) k) bb0 (shift_A_ZZ (weakenCutoffA C0 k) zz2)) = (shift_A_ZZ (weakenCutoffA C0 k) (subst_B_ZZ (weakenTrace d k) bb0 zz2))) :=
      match zz2 return ((subst_B_ZZ (weakenTrace (XS A d) k) bb0 (shift_A_ZZ (weakenCutoffA C0 k) zz2)) = (shift_A_ZZ (weakenCutoffA C0 k) (subst_B_ZZ (weakenTrace d k) bb0 zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal3 subst_B_AA (weakenTrace_append B (XS A d) k (HS A H0)) eq_refl eq_refl) (eq_trans (subst_B__shift_A_0_AA_comm_ind aa1 (HS A k) d bb0) (f_equal2 shift_A_AA eq_refl (f_equal3 subst_B_AA (eq_sym (weakenTrace_append B d k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb1) => (f_equal babs (eq_trans (f_equal3 subst_B_BB (weakenTrace_append B (XS A d) k (HS B H0)) eq_refl eq_refl) (eq_trans (subst_B__shift_A_0_BB_comm_ind bb1 (HS B k) d bb0) (f_equal2 shift_A_BB eq_refl (f_equal3 subst_B_BB (eq_sym (weakenTrace_append B d k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_B__shift_A_0_BB_comm_ind (bb2 : BB) (k : Hvl) (d : (Trace B)) (bb0 : BB) {struct bb2} :
    ((subst_B_BB (weakenTrace (XS A d) k) bb0 (shift_A_BB (weakenCutoffA C0 k) bb2)) = (shift_A_BB (weakenCutoffA C0 k) (subst_B_BB (weakenTrace d k) bb0 bb2))) :=
      match bb2 return ((subst_B_BB (weakenTrace (XS A d) k) bb0 (shift_A_BB (weakenCutoffA C0 k) bb2)) = (shift_A_BB (weakenCutoffA C0 k) (subst_B_BB (weakenTrace d k) bb0 bb2))) with
        | (bvar b4) => (subst_B_Index_shift_A_BB0_comm_ind d bb0 k b4)
        | (brec zz3) => (f_equal brec (subst_B__shift_A_0_ZZ_comm_ind zz3 k d bb0))
      end.
    Fixpoint subst_B__shift_B_0_AA_comm_ind (aa0 : AA) (k : Hvl) (d : (Trace B)) (bb0 : BB) {struct aa0} :
    ((subst_B_AA (weakenTrace (XS B d) k) bb0 (shift_B_AA (weakenCutoffB C0 k) aa0)) = (shift_B_AA (weakenCutoffB C0 k) (subst_B_AA (weakenTrace d k) bb0 aa0))) :=
      match aa0 return ((subst_B_AA (weakenTrace (XS B d) k) bb0 (shift_B_AA (weakenCutoffB C0 k) aa0)) = (shift_B_AA (weakenCutoffB C0 k) (subst_B_AA (weakenTrace d k) bb0 aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (subst_B__shift_B_0_ZZ_comm_ind zz1 k d bb0))
      end
    with subst_B__shift_B_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (d : (Trace B)) (bb0 : BB) {struct zz2} :
    ((subst_B_ZZ (weakenTrace (XS B d) k) bb0 (shift_B_ZZ (weakenCutoffB C0 k) zz2)) = (shift_B_ZZ (weakenCutoffB C0 k) (subst_B_ZZ (weakenTrace d k) bb0 zz2))) :=
      match zz2 return ((subst_B_ZZ (weakenTrace (XS B d) k) bb0 (shift_B_ZZ (weakenCutoffB C0 k) zz2)) = (shift_B_ZZ (weakenCutoffB C0 k) (subst_B_ZZ (weakenTrace d k) bb0 zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal3 subst_B_AA (weakenTrace_append B (XS B d) k (HS A H0)) eq_refl eq_refl) (eq_trans (subst_B__shift_B_0_AA_comm_ind aa1 (HS A k) d bb0) (f_equal2 shift_B_AA eq_refl (f_equal3 subst_B_AA (eq_sym (weakenTrace_append B d k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb1) => (f_equal babs (eq_trans (f_equal3 subst_B_BB (weakenTrace_append B (XS B d) k (HS B H0)) eq_refl eq_refl) (eq_trans (subst_B__shift_B_0_BB_comm_ind bb1 (HS B k) d bb0) (f_equal2 shift_B_BB eq_refl (f_equal3 subst_B_BB (eq_sym (weakenTrace_append B d k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_B__shift_B_0_BB_comm_ind (bb2 : BB) (k : Hvl) (d : (Trace B)) (bb0 : BB) {struct bb2} :
    ((subst_B_BB (weakenTrace (XS B d) k) bb0 (shift_B_BB (weakenCutoffB C0 k) bb2)) = (shift_B_BB (weakenCutoffB C0 k) (subst_B_BB (weakenTrace d k) bb0 bb2))) :=
      match bb2 return ((subst_B_BB (weakenTrace (XS B d) k) bb0 (shift_B_BB (weakenCutoffB C0 k) bb2)) = (shift_B_BB (weakenCutoffB C0 k) (subst_B_BB (weakenTrace d k) bb0 bb2))) with
        | (bvar b4) => (subst_B_Index_shift_B_BB0_comm_ind d bb0 k b4)
        | (brec zz3) => (f_equal brec (subst_B__shift_B_0_ZZ_comm_ind zz3 k d bb0))
      end.
    Fixpoint subst_B__shift_Z_0_AA_comm_ind (aa0 : AA) (k : Hvl) (d : (Trace B)) (bb0 : BB) {struct aa0} :
    ((subst_B_AA (weakenTrace (XS Z d) k) bb0 (shift_Z_AA (weakenCutoffZ C0 k) aa0)) = (shift_Z_AA (weakenCutoffZ C0 k) (subst_B_AA (weakenTrace d k) bb0 aa0))) :=
      match aa0 return ((subst_B_AA (weakenTrace (XS Z d) k) bb0 (shift_Z_AA (weakenCutoffZ C0 k) aa0)) = (shift_Z_AA (weakenCutoffZ C0 k) (subst_B_AA (weakenTrace d k) bb0 aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (subst_B__shift_Z_0_ZZ_comm_ind zz1 k d bb0))
      end
    with subst_B__shift_Z_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (d : (Trace B)) (bb0 : BB) {struct zz2} :
    ((subst_B_ZZ (weakenTrace (XS Z d) k) bb0 (shift_Z_ZZ (weakenCutoffZ C0 k) zz2)) = (shift_Z_ZZ (weakenCutoffZ C0 k) (subst_B_ZZ (weakenTrace d k) bb0 zz2))) :=
      match zz2 return ((subst_B_ZZ (weakenTrace (XS Z d) k) bb0 (shift_Z_ZZ (weakenCutoffZ C0 k) zz2)) = (shift_Z_ZZ (weakenCutoffZ C0 k) (subst_B_ZZ (weakenTrace d k) bb0 zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal3 subst_B_AA (weakenTrace_append B (XS Z d) k (HS A H0)) eq_refl eq_refl) (eq_trans (subst_B__shift_Z_0_AA_comm_ind aa1 (HS A k) d bb0) (f_equal2 shift_Z_AA eq_refl (f_equal3 subst_B_AA (eq_sym (weakenTrace_append B d k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb1) => (f_equal babs (eq_trans (f_equal3 subst_B_BB (weakenTrace_append B (XS Z d) k (HS B H0)) eq_refl eq_refl) (eq_trans (subst_B__shift_Z_0_BB_comm_ind bb1 (HS B k) d bb0) (f_equal2 shift_Z_BB eq_refl (f_equal3 subst_B_BB (eq_sym (weakenTrace_append B d k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_B__shift_Z_0_BB_comm_ind (bb2 : BB) (k : Hvl) (d : (Trace B)) (bb0 : BB) {struct bb2} :
    ((subst_B_BB (weakenTrace (XS Z d) k) bb0 (shift_Z_BB (weakenCutoffZ C0 k) bb2)) = (shift_Z_BB (weakenCutoffZ C0 k) (subst_B_BB (weakenTrace d k) bb0 bb2))) :=
      match bb2 return ((subst_B_BB (weakenTrace (XS Z d) k) bb0 (shift_Z_BB (weakenCutoffZ C0 k) bb2)) = (shift_Z_BB (weakenCutoffZ C0 k) (subst_B_BB (weakenTrace d k) bb0 bb2))) with
        | (bvar b4) => (subst_B_Index_shift_Z_BB0_comm_ind d bb0 k b4)
        | (brec zz3) => (f_equal brec (subst_B__shift_Z_0_ZZ_comm_ind zz3 k d bb0))
      end.
    Fixpoint subst_Z__shift_A_0_AA_comm_ind (aa0 : AA) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) {struct aa0} :
    ((subst_Z_AA (weakenTrace (XS A d) k) zz1 (shift_A_AA (weakenCutoffA C0 k) aa0)) = (shift_A_AA (weakenCutoffA C0 k) (subst_Z_AA (weakenTrace d k) zz1 aa0))) :=
      match aa0 return ((subst_Z_AA (weakenTrace (XS A d) k) zz1 (shift_A_AA (weakenCutoffA C0 k) aa0)) = (shift_A_AA (weakenCutoffA C0 k) (subst_Z_AA (weakenTrace d k) zz1 aa0))) with
        | (avar a3) => eq_refl
        | (arec zz2) => (f_equal arec (subst_Z__shift_A_0_ZZ_comm_ind zz2 k d zz1))
      end
    with subst_Z__shift_A_0_ZZ_comm_ind (zz3 : ZZ) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) {struct zz3} :
    ((subst_Z_ZZ (weakenTrace (XS A d) k) zz1 (shift_A_ZZ (weakenCutoffA C0 k) zz3)) = (shift_A_ZZ (weakenCutoffA C0 k) (subst_Z_ZZ (weakenTrace d k) zz1 zz3))) :=
      match zz3 return ((subst_Z_ZZ (weakenTrace (XS A d) k) zz1 (shift_A_ZZ (weakenCutoffA C0 k) zz3)) = (shift_A_ZZ (weakenCutoffA C0 k) (subst_Z_ZZ (weakenTrace d k) zz1 zz3))) with
        | (zvar z0) => (subst_Z_Index_shift_A_ZZ0_comm_ind d zz1 k z0)
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal3 subst_Z_AA (weakenTrace_append Z (XS A d) k (HS A H0)) eq_refl eq_refl) (eq_trans (subst_Z__shift_A_0_AA_comm_ind aa1 (HS A k) d zz1) (f_equal2 shift_A_AA eq_refl (f_equal3 subst_Z_AA (eq_sym (weakenTrace_append Z d k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal3 subst_Z_BB (weakenTrace_append Z (XS A d) k (HS B H0)) eq_refl eq_refl) (eq_trans (subst_Z__shift_A_0_BB_comm_ind bb0 (HS B k) d zz1) (f_equal2 shift_A_BB eq_refl (f_equal3 subst_Z_BB (eq_sym (weakenTrace_append Z d k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_Z__shift_A_0_BB_comm_ind (bb1 : BB) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) {struct bb1} :
    ((subst_Z_BB (weakenTrace (XS A d) k) zz1 (shift_A_BB (weakenCutoffA C0 k) bb1)) = (shift_A_BB (weakenCutoffA C0 k) (subst_Z_BB (weakenTrace d k) zz1 bb1))) :=
      match bb1 return ((subst_Z_BB (weakenTrace (XS A d) k) zz1 (shift_A_BB (weakenCutoffA C0 k) bb1)) = (shift_A_BB (weakenCutoffA C0 k) (subst_Z_BB (weakenTrace d k) zz1 bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz4) => (f_equal brec (subst_Z__shift_A_0_ZZ_comm_ind zz4 k d zz1))
      end.
    Fixpoint subst_Z__shift_B_0_AA_comm_ind (aa0 : AA) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) {struct aa0} :
    ((subst_Z_AA (weakenTrace (XS B d) k) zz1 (shift_B_AA (weakenCutoffB C0 k) aa0)) = (shift_B_AA (weakenCutoffB C0 k) (subst_Z_AA (weakenTrace d k) zz1 aa0))) :=
      match aa0 return ((subst_Z_AA (weakenTrace (XS B d) k) zz1 (shift_B_AA (weakenCutoffB C0 k) aa0)) = (shift_B_AA (weakenCutoffB C0 k) (subst_Z_AA (weakenTrace d k) zz1 aa0))) with
        | (avar a3) => eq_refl
        | (arec zz2) => (f_equal arec (subst_Z__shift_B_0_ZZ_comm_ind zz2 k d zz1))
      end
    with subst_Z__shift_B_0_ZZ_comm_ind (zz3 : ZZ) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) {struct zz3} :
    ((subst_Z_ZZ (weakenTrace (XS B d) k) zz1 (shift_B_ZZ (weakenCutoffB C0 k) zz3)) = (shift_B_ZZ (weakenCutoffB C0 k) (subst_Z_ZZ (weakenTrace d k) zz1 zz3))) :=
      match zz3 return ((subst_Z_ZZ (weakenTrace (XS B d) k) zz1 (shift_B_ZZ (weakenCutoffB C0 k) zz3)) = (shift_B_ZZ (weakenCutoffB C0 k) (subst_Z_ZZ (weakenTrace d k) zz1 zz3))) with
        | (zvar z0) => (subst_Z_Index_shift_B_ZZ0_comm_ind d zz1 k z0)
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal3 subst_Z_AA (weakenTrace_append Z (XS B d) k (HS A H0)) eq_refl eq_refl) (eq_trans (subst_Z__shift_B_0_AA_comm_ind aa1 (HS A k) d zz1) (f_equal2 shift_B_AA eq_refl (f_equal3 subst_Z_AA (eq_sym (weakenTrace_append Z d k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal3 subst_Z_BB (weakenTrace_append Z (XS B d) k (HS B H0)) eq_refl eq_refl) (eq_trans (subst_Z__shift_B_0_BB_comm_ind bb0 (HS B k) d zz1) (f_equal2 shift_B_BB eq_refl (f_equal3 subst_Z_BB (eq_sym (weakenTrace_append Z d k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_Z__shift_B_0_BB_comm_ind (bb1 : BB) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) {struct bb1} :
    ((subst_Z_BB (weakenTrace (XS B d) k) zz1 (shift_B_BB (weakenCutoffB C0 k) bb1)) = (shift_B_BB (weakenCutoffB C0 k) (subst_Z_BB (weakenTrace d k) zz1 bb1))) :=
      match bb1 return ((subst_Z_BB (weakenTrace (XS B d) k) zz1 (shift_B_BB (weakenCutoffB C0 k) bb1)) = (shift_B_BB (weakenCutoffB C0 k) (subst_Z_BB (weakenTrace d k) zz1 bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz4) => (f_equal brec (subst_Z__shift_B_0_ZZ_comm_ind zz4 k d zz1))
      end.
    Fixpoint subst_Z__shift_Z_0_AA_comm_ind (aa0 : AA) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) {struct aa0} :
    ((subst_Z_AA (weakenTrace (XS Z d) k) zz1 (shift_Z_AA (weakenCutoffZ C0 k) aa0)) = (shift_Z_AA (weakenCutoffZ C0 k) (subst_Z_AA (weakenTrace d k) zz1 aa0))) :=
      match aa0 return ((subst_Z_AA (weakenTrace (XS Z d) k) zz1 (shift_Z_AA (weakenCutoffZ C0 k) aa0)) = (shift_Z_AA (weakenCutoffZ C0 k) (subst_Z_AA (weakenTrace d k) zz1 aa0))) with
        | (avar a3) => eq_refl
        | (arec zz2) => (f_equal arec (subst_Z__shift_Z_0_ZZ_comm_ind zz2 k d zz1))
      end
    with subst_Z__shift_Z_0_ZZ_comm_ind (zz3 : ZZ) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) {struct zz3} :
    ((subst_Z_ZZ (weakenTrace (XS Z d) k) zz1 (shift_Z_ZZ (weakenCutoffZ C0 k) zz3)) = (shift_Z_ZZ (weakenCutoffZ C0 k) (subst_Z_ZZ (weakenTrace d k) zz1 zz3))) :=
      match zz3 return ((subst_Z_ZZ (weakenTrace (XS Z d) k) zz1 (shift_Z_ZZ (weakenCutoffZ C0 k) zz3)) = (shift_Z_ZZ (weakenCutoffZ C0 k) (subst_Z_ZZ (weakenTrace d k) zz1 zz3))) with
        | (zvar z0) => (subst_Z_Index_shift_Z_ZZ0_comm_ind d zz1 k z0)
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal3 subst_Z_AA (weakenTrace_append Z (XS Z d) k (HS A H0)) eq_refl eq_refl) (eq_trans (subst_Z__shift_Z_0_AA_comm_ind aa1 (HS A k) d zz1) (f_equal2 shift_Z_AA eq_refl (f_equal3 subst_Z_AA (eq_sym (weakenTrace_append Z d k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal3 subst_Z_BB (weakenTrace_append Z (XS Z d) k (HS B H0)) eq_refl eq_refl) (eq_trans (subst_Z__shift_Z_0_BB_comm_ind bb0 (HS B k) d zz1) (f_equal2 shift_Z_BB eq_refl (f_equal3 subst_Z_BB (eq_sym (weakenTrace_append Z d k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_Z__shift_Z_0_BB_comm_ind (bb1 : BB) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) {struct bb1} :
    ((subst_Z_BB (weakenTrace (XS Z d) k) zz1 (shift_Z_BB (weakenCutoffZ C0 k) bb1)) = (shift_Z_BB (weakenCutoffZ C0 k) (subst_Z_BB (weakenTrace d k) zz1 bb1))) :=
      match bb1 return ((subst_Z_BB (weakenTrace (XS Z d) k) zz1 (shift_Z_BB (weakenCutoffZ C0 k) bb1)) = (shift_Z_BB (weakenCutoffZ C0 k) (subst_Z_BB (weakenTrace d k) zz1 bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz4) => (f_equal brec (subst_Z__shift_Z_0_ZZ_comm_ind zz4 k d zz1))
      end.
  End SubstShiftCommInd.
  Section SubstShiftComm.
    Definition subst_A_AA_shift_A_AA0_comm (aa1 : AA) : (forall (d : (Trace A)) (aa0 : AA) ,
      ((subst_A_AA (XS A d) aa0 (shift_A_AA C0 aa1)) = (shift_A_AA C0 (subst_A_AA d aa0 aa1)))) := (subst_A__shift_A_0_AA_comm_ind aa1 H0).
    Definition subst_A_ZZ_shift_A_ZZ0_comm (zz1 : ZZ) : (forall (d : (Trace A)) (aa0 : AA) ,
      ((subst_A_ZZ (XS A d) aa0 (shift_A_ZZ C0 zz1)) = (shift_A_ZZ C0 (subst_A_ZZ d aa0 zz1)))) := (subst_A__shift_A_0_ZZ_comm_ind zz1 H0).
    Definition subst_A_BB_shift_A_BB0_comm (bb0 : BB) : (forall (d : (Trace A)) (aa0 : AA) ,
      ((subst_A_BB (XS A d) aa0 (shift_A_BB C0 bb0)) = (shift_A_BB C0 (subst_A_BB d aa0 bb0)))) := (subst_A__shift_A_0_BB_comm_ind bb0 H0).
    Definition subst_A_AA_shift_B_AA0_comm (aa1 : AA) : (forall (d : (Trace A)) (aa0 : AA) ,
      ((subst_A_AA (XS B d) aa0 (shift_B_AA C0 aa1)) = (shift_B_AA C0 (subst_A_AA d aa0 aa1)))) := (subst_A__shift_B_0_AA_comm_ind aa1 H0).
    Definition subst_A_ZZ_shift_B_ZZ0_comm (zz1 : ZZ) : (forall (d : (Trace A)) (aa0 : AA) ,
      ((subst_A_ZZ (XS B d) aa0 (shift_B_ZZ C0 zz1)) = (shift_B_ZZ C0 (subst_A_ZZ d aa0 zz1)))) := (subst_A__shift_B_0_ZZ_comm_ind zz1 H0).
    Definition subst_A_BB_shift_B_BB0_comm (bb0 : BB) : (forall (d : (Trace A)) (aa0 : AA) ,
      ((subst_A_BB (XS B d) aa0 (shift_B_BB C0 bb0)) = (shift_B_BB C0 (subst_A_BB d aa0 bb0)))) := (subst_A__shift_B_0_BB_comm_ind bb0 H0).
    Definition subst_A_AA_shift_Z_AA0_comm (aa1 : AA) : (forall (d : (Trace A)) (aa0 : AA) ,
      ((subst_A_AA (XS Z d) aa0 (shift_Z_AA C0 aa1)) = (shift_Z_AA C0 (subst_A_AA d aa0 aa1)))) := (subst_A__shift_Z_0_AA_comm_ind aa1 H0).
    Definition subst_A_ZZ_shift_Z_ZZ0_comm (zz1 : ZZ) : (forall (d : (Trace A)) (aa0 : AA) ,
      ((subst_A_ZZ (XS Z d) aa0 (shift_Z_ZZ C0 zz1)) = (shift_Z_ZZ C0 (subst_A_ZZ d aa0 zz1)))) := (subst_A__shift_Z_0_ZZ_comm_ind zz1 H0).
    Definition subst_A_BB_shift_Z_BB0_comm (bb0 : BB) : (forall (d : (Trace A)) (aa0 : AA) ,
      ((subst_A_BB (XS Z d) aa0 (shift_Z_BB C0 bb0)) = (shift_Z_BB C0 (subst_A_BB d aa0 bb0)))) := (subst_A__shift_Z_0_BB_comm_ind bb0 H0).
    Definition subst_B_AA_shift_A_AA0_comm (aa0 : AA) : (forall (d : (Trace B)) (bb0 : BB) ,
      ((subst_B_AA (XS A d) bb0 (shift_A_AA C0 aa0)) = (shift_A_AA C0 (subst_B_AA d bb0 aa0)))) := (subst_B__shift_A_0_AA_comm_ind aa0 H0).
    Definition subst_B_ZZ_shift_A_ZZ0_comm (zz1 : ZZ) : (forall (d : (Trace B)) (bb0 : BB) ,
      ((subst_B_ZZ (XS A d) bb0 (shift_A_ZZ C0 zz1)) = (shift_A_ZZ C0 (subst_B_ZZ d bb0 zz1)))) := (subst_B__shift_A_0_ZZ_comm_ind zz1 H0).
    Definition subst_B_BB_shift_A_BB0_comm (bb1 : BB) : (forall (d : (Trace B)) (bb0 : BB) ,
      ((subst_B_BB (XS A d) bb0 (shift_A_BB C0 bb1)) = (shift_A_BB C0 (subst_B_BB d bb0 bb1)))) := (subst_B__shift_A_0_BB_comm_ind bb1 H0).
    Definition subst_B_AA_shift_B_AA0_comm (aa0 : AA) : (forall (d : (Trace B)) (bb0 : BB) ,
      ((subst_B_AA (XS B d) bb0 (shift_B_AA C0 aa0)) = (shift_B_AA C0 (subst_B_AA d bb0 aa0)))) := (subst_B__shift_B_0_AA_comm_ind aa0 H0).
    Definition subst_B_ZZ_shift_B_ZZ0_comm (zz1 : ZZ) : (forall (d : (Trace B)) (bb0 : BB) ,
      ((subst_B_ZZ (XS B d) bb0 (shift_B_ZZ C0 zz1)) = (shift_B_ZZ C0 (subst_B_ZZ d bb0 zz1)))) := (subst_B__shift_B_0_ZZ_comm_ind zz1 H0).
    Definition subst_B_BB_shift_B_BB0_comm (bb1 : BB) : (forall (d : (Trace B)) (bb0 : BB) ,
      ((subst_B_BB (XS B d) bb0 (shift_B_BB C0 bb1)) = (shift_B_BB C0 (subst_B_BB d bb0 bb1)))) := (subst_B__shift_B_0_BB_comm_ind bb1 H0).
    Definition subst_B_AA_shift_Z_AA0_comm (aa0 : AA) : (forall (d : (Trace B)) (bb0 : BB) ,
      ((subst_B_AA (XS Z d) bb0 (shift_Z_AA C0 aa0)) = (shift_Z_AA C0 (subst_B_AA d bb0 aa0)))) := (subst_B__shift_Z_0_AA_comm_ind aa0 H0).
    Definition subst_B_ZZ_shift_Z_ZZ0_comm (zz1 : ZZ) : (forall (d : (Trace B)) (bb0 : BB) ,
      ((subst_B_ZZ (XS Z d) bb0 (shift_Z_ZZ C0 zz1)) = (shift_Z_ZZ C0 (subst_B_ZZ d bb0 zz1)))) := (subst_B__shift_Z_0_ZZ_comm_ind zz1 H0).
    Definition subst_B_BB_shift_Z_BB0_comm (bb1 : BB) : (forall (d : (Trace B)) (bb0 : BB) ,
      ((subst_B_BB (XS Z d) bb0 (shift_Z_BB C0 bb1)) = (shift_Z_BB C0 (subst_B_BB d bb0 bb1)))) := (subst_B__shift_Z_0_BB_comm_ind bb1 H0).
    Definition subst_Z_AA_shift_A_AA0_comm (aa0 : AA) : (forall (d : (Trace Z)) (zz1 : ZZ) ,
      ((subst_Z_AA (XS A d) zz1 (shift_A_AA C0 aa0)) = (shift_A_AA C0 (subst_Z_AA d zz1 aa0)))) := (subst_Z__shift_A_0_AA_comm_ind aa0 H0).
    Definition subst_Z_ZZ_shift_A_ZZ0_comm (zz2 : ZZ) : (forall (d : (Trace Z)) (zz1 : ZZ) ,
      ((subst_Z_ZZ (XS A d) zz1 (shift_A_ZZ C0 zz2)) = (shift_A_ZZ C0 (subst_Z_ZZ d zz1 zz2)))) := (subst_Z__shift_A_0_ZZ_comm_ind zz2 H0).
    Definition subst_Z_BB_shift_A_BB0_comm (bb0 : BB) : (forall (d : (Trace Z)) (zz1 : ZZ) ,
      ((subst_Z_BB (XS A d) zz1 (shift_A_BB C0 bb0)) = (shift_A_BB C0 (subst_Z_BB d zz1 bb0)))) := (subst_Z__shift_A_0_BB_comm_ind bb0 H0).
    Definition subst_Z_AA_shift_B_AA0_comm (aa0 : AA) : (forall (d : (Trace Z)) (zz1 : ZZ) ,
      ((subst_Z_AA (XS B d) zz1 (shift_B_AA C0 aa0)) = (shift_B_AA C0 (subst_Z_AA d zz1 aa0)))) := (subst_Z__shift_B_0_AA_comm_ind aa0 H0).
    Definition subst_Z_ZZ_shift_B_ZZ0_comm (zz2 : ZZ) : (forall (d : (Trace Z)) (zz1 : ZZ) ,
      ((subst_Z_ZZ (XS B d) zz1 (shift_B_ZZ C0 zz2)) = (shift_B_ZZ C0 (subst_Z_ZZ d zz1 zz2)))) := (subst_Z__shift_B_0_ZZ_comm_ind zz2 H0).
    Definition subst_Z_BB_shift_B_BB0_comm (bb0 : BB) : (forall (d : (Trace Z)) (zz1 : ZZ) ,
      ((subst_Z_BB (XS B d) zz1 (shift_B_BB C0 bb0)) = (shift_B_BB C0 (subst_Z_BB d zz1 bb0)))) := (subst_Z__shift_B_0_BB_comm_ind bb0 H0).
    Definition subst_Z_AA_shift_Z_AA0_comm (aa0 : AA) : (forall (d : (Trace Z)) (zz1 : ZZ) ,
      ((subst_Z_AA (XS Z d) zz1 (shift_Z_AA C0 aa0)) = (shift_Z_AA C0 (subst_Z_AA d zz1 aa0)))) := (subst_Z__shift_Z_0_AA_comm_ind aa0 H0).
    Definition subst_Z_ZZ_shift_Z_ZZ0_comm (zz2 : ZZ) : (forall (d : (Trace Z)) (zz1 : ZZ) ,
      ((subst_Z_ZZ (XS Z d) zz1 (shift_Z_ZZ C0 zz2)) = (shift_Z_ZZ C0 (subst_Z_ZZ d zz1 zz2)))) := (subst_Z__shift_Z_0_ZZ_comm_ind zz2 H0).
    Definition subst_Z_BB_shift_Z_BB0_comm (bb0 : BB) : (forall (d : (Trace Z)) (zz1 : ZZ) ,
      ((subst_Z_BB (XS Z d) zz1 (shift_Z_BB C0 bb0)) = (shift_Z_BB C0 (subst_Z_BB d zz1 bb0)))) := (subst_Z__shift_Z_0_BB_comm_ind bb0 H0).
  End SubstShiftComm.
  Section SubstSubordInd.
    
  End SubstSubordInd.
  Section SubstSubord.
    
  End SubstSubord.
End ShiftSubstInteraction.
 Hint Rewrite subst_A_AA0_shift_A_AA0_reflection subst_B_AA0_shift_B_AA0_reflection subst_Z_AA0_shift_Z_AA0_reflection subst_A_BB0_shift_A_BB0_reflection subst_B_BB0_shift_B_BB0_reflection subst_Z_BB0_shift_Z_BB0_reflection subst_A_ZZ0_shift_A_ZZ0_reflection subst_B_ZZ0_shift_B_ZZ0_reflection subst_Z_ZZ0_shift_Z_ZZ0_reflection : interaction.
 Hint Rewrite subst_A_AA0_shift_A_AA0_reflection subst_B_AA0_shift_B_AA0_reflection subst_Z_AA0_shift_Z_AA0_reflection subst_A_BB0_shift_A_BB0_reflection subst_B_BB0_shift_B_BB0_reflection subst_Z_BB0_shift_Z_BB0_reflection subst_A_ZZ0_shift_A_ZZ0_reflection subst_B_ZZ0_shift_B_ZZ0_reflection subst_Z_ZZ0_shift_Z_ZZ0_reflection : reflection.
 Hint Rewrite subst_A_AA_shift_A_AA0_comm subst_A_AA_shift_B_AA0_comm subst_A_AA_shift_Z_AA0_comm subst_B_AA_shift_A_AA0_comm subst_B_AA_shift_B_AA0_comm subst_B_AA_shift_Z_AA0_comm subst_Z_AA_shift_A_AA0_comm subst_Z_AA_shift_B_AA0_comm subst_Z_AA_shift_Z_AA0_comm subst_A_BB_shift_A_BB0_comm subst_A_BB_shift_B_BB0_comm subst_A_BB_shift_Z_BB0_comm subst_B_BB_shift_A_BB0_comm subst_B_BB_shift_B_BB0_comm subst_B_BB_shift_Z_BB0_comm subst_Z_BB_shift_A_BB0_comm subst_Z_BB_shift_B_BB0_comm subst_Z_BB_shift_Z_BB0_comm subst_A_ZZ_shift_A_ZZ0_comm subst_A_ZZ_shift_B_ZZ0_comm subst_A_ZZ_shift_Z_ZZ0_comm subst_B_ZZ_shift_A_ZZ0_comm subst_B_ZZ_shift_B_ZZ0_comm subst_B_ZZ_shift_Z_ZZ0_comm subst_Z_ZZ_shift_A_ZZ0_comm subst_Z_ZZ_shift_B_ZZ0_comm subst_Z_ZZ_shift_Z_ZZ0_comm : interaction.
 Hint Rewrite subst_A_AA_shift_A_AA0_comm subst_A_AA_shift_B_AA0_comm subst_A_AA_shift_Z_AA0_comm subst_B_AA_shift_A_AA0_comm subst_B_AA_shift_B_AA0_comm subst_B_AA_shift_Z_AA0_comm subst_Z_AA_shift_A_AA0_comm subst_Z_AA_shift_B_AA0_comm subst_Z_AA_shift_Z_AA0_comm subst_A_BB_shift_A_BB0_comm subst_A_BB_shift_B_BB0_comm subst_A_BB_shift_Z_BB0_comm subst_B_BB_shift_A_BB0_comm subst_B_BB_shift_B_BB0_comm subst_B_BB_shift_Z_BB0_comm subst_Z_BB_shift_A_BB0_comm subst_Z_BB_shift_B_BB0_comm subst_Z_BB_shift_Z_BB0_comm subst_A_ZZ_shift_A_ZZ0_comm subst_A_ZZ_shift_B_ZZ0_comm subst_A_ZZ_shift_Z_ZZ0_comm subst_B_ZZ_shift_A_ZZ0_comm subst_B_ZZ_shift_B_ZZ0_comm subst_B_ZZ_shift_Z_ZZ0_comm subst_Z_ZZ_shift_A_ZZ0_comm subst_Z_ZZ_shift_B_ZZ0_comm subst_Z_ZZ_shift_Z_ZZ0_comm : subst_shift0.
 Hint Rewrite shift_A_AA_subst_A_AA0_comm shift_A_AA_subst_B_AA0_comm shift_A_AA_subst_Z_AA0_comm shift_B_AA_subst_A_AA0_comm shift_B_AA_subst_B_AA0_comm shift_B_AA_subst_Z_AA0_comm shift_Z_AA_subst_A_AA0_comm shift_Z_AA_subst_B_AA0_comm shift_Z_AA_subst_Z_AA0_comm shift_A_BB_subst_A_BB0_comm shift_A_BB_subst_B_BB0_comm shift_A_BB_subst_Z_BB0_comm shift_B_BB_subst_A_BB0_comm shift_B_BB_subst_B_BB0_comm shift_B_BB_subst_Z_BB0_comm shift_Z_BB_subst_A_BB0_comm shift_Z_BB_subst_B_BB0_comm shift_Z_BB_subst_Z_BB0_comm shift_A_ZZ_subst_A_ZZ0_comm shift_A_ZZ_subst_B_ZZ0_comm shift_A_ZZ_subst_Z_ZZ0_comm shift_B_ZZ_subst_A_ZZ0_comm shift_B_ZZ_subst_B_ZZ0_comm shift_B_ZZ_subst_Z_ZZ0_comm shift_Z_ZZ_subst_A_ZZ0_comm shift_Z_ZZ_subst_B_ZZ0_comm shift_Z_ZZ_subst_Z_ZZ0_comm : interaction.
 Hint Rewrite shift_A_AA_subst_A_AA0_comm shift_A_AA_subst_B_AA0_comm shift_A_AA_subst_Z_AA0_comm shift_B_AA_subst_A_AA0_comm shift_B_AA_subst_B_AA0_comm shift_B_AA_subst_Z_AA0_comm shift_Z_AA_subst_A_AA0_comm shift_Z_AA_subst_B_AA0_comm shift_Z_AA_subst_Z_AA0_comm shift_A_BB_subst_A_BB0_comm shift_A_BB_subst_B_BB0_comm shift_A_BB_subst_Z_BB0_comm shift_B_BB_subst_A_BB0_comm shift_B_BB_subst_B_BB0_comm shift_B_BB_subst_Z_BB0_comm shift_Z_BB_subst_A_BB0_comm shift_Z_BB_subst_B_BB0_comm shift_Z_BB_subst_Z_BB0_comm shift_A_ZZ_subst_A_ZZ0_comm shift_A_ZZ_subst_B_ZZ0_comm shift_A_ZZ_subst_Z_ZZ0_comm shift_B_ZZ_subst_A_ZZ0_comm shift_B_ZZ_subst_B_ZZ0_comm shift_B_ZZ_subst_Z_ZZ0_comm shift_Z_ZZ_subst_A_ZZ0_comm shift_Z_ZZ_subst_B_ZZ0_comm shift_Z_ZZ_subst_Z_ZZ0_comm : shift_subst0.
Section SubstSubstInteraction.
  Section SubstSubstIndexCommInd.
    Lemma subst_A_AA_subst_A_Index0_commright_ind (d : (Trace A)) (aa0 : AA) (aa1 : AA) :
      (forall (k : Hvl) (a3 : (Index A)) ,
        ((subst_A_AA (weakenTrace d k) aa0 (subst_A_Index (weakenTrace X0 k) aa1 a3)) = (subst_A_AA (weakenTrace X0 k) (subst_A_AA d aa0 aa1) (subst_A_Index (weakenTrace (XS A d) k) aa0 a3)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_B_AA_subst_A_Index0_commright_ind (d : (Trace B)) (bb0 : BB) (aa0 : AA) :
      (forall (k : Hvl) (a3 : (Index A)) ,
        ((subst_B_AA (weakenTrace d k) bb0 (subst_A_Index (weakenTrace X0 k) aa0 a3)) = (subst_A_Index (weakenTrace X0 k) (subst_B_AA d bb0 aa0) a3))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_Z_AA_subst_A_Index0_commright_ind (d : (Trace Z)) (zz1 : ZZ) (aa0 : AA) :
      (forall (k : Hvl) (a3 : (Index A)) ,
        ((subst_Z_AA (weakenTrace d k) zz1 (subst_A_Index (weakenTrace X0 k) aa0 a3)) = (subst_A_Index (weakenTrace X0 k) (subst_Z_AA d zz1 aa0) a3))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_A_BB_subst_B_Index0_commright_ind (d : (Trace A)) (aa0 : AA) (bb0 : BB) :
      (forall (k : Hvl) (b3 : (Index B)) ,
        ((subst_A_BB (weakenTrace d k) aa0 (subst_B_Index (weakenTrace X0 k) bb0 b3)) = (subst_B_Index (weakenTrace X0 k) (subst_A_BB d aa0 bb0) b3))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_B_BB_subst_B_Index0_commright_ind (d : (Trace B)) (bb0 : BB) (bb1 : BB) :
      (forall (k : Hvl) (b3 : (Index B)) ,
        ((subst_B_BB (weakenTrace d k) bb0 (subst_B_Index (weakenTrace X0 k) bb1 b3)) = (subst_B_BB (weakenTrace X0 k) (subst_B_BB d bb0 bb1) (subst_B_Index (weakenTrace (XS B d) k) bb0 b3)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_Z_BB_subst_B_Index0_commright_ind (d : (Trace Z)) (zz1 : ZZ) (bb0 : BB) :
      (forall (k : Hvl) (b3 : (Index B)) ,
        ((subst_Z_BB (weakenTrace d k) zz1 (subst_B_Index (weakenTrace X0 k) bb0 b3)) = (subst_B_Index (weakenTrace X0 k) (subst_Z_BB d zz1 bb0) b3))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_A_ZZ_subst_Z_Index0_commright_ind (d : (Trace A)) (aa0 : AA) (zz1 : ZZ) :
      (forall (k : Hvl) (z0 : (Index Z)) ,
        ((subst_A_ZZ (weakenTrace d k) aa0 (subst_Z_Index (weakenTrace X0 k) zz1 z0)) = (subst_Z_Index (weakenTrace X0 k) (subst_A_ZZ d aa0 zz1) z0))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_B_ZZ_subst_Z_Index0_commright_ind (d : (Trace B)) (bb0 : BB) (zz1 : ZZ) :
      (forall (k : Hvl) (z0 : (Index Z)) ,
        ((subst_B_ZZ (weakenTrace d k) bb0 (subst_Z_Index (weakenTrace X0 k) zz1 z0)) = (subst_Z_Index (weakenTrace X0 k) (subst_B_ZZ d bb0 zz1) z0))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_Z_ZZ_subst_Z_Index0_commright_ind (d : (Trace Z)) (zz1 : ZZ) (zz2 : ZZ) :
      (forall (k : Hvl) (z0 : (Index Z)) ,
        ((subst_Z_ZZ (weakenTrace d k) zz1 (subst_Z_Index (weakenTrace X0 k) zz2 z0)) = (subst_Z_ZZ (weakenTrace X0 k) (subst_Z_ZZ d zz1 zz2) (subst_Z_Index (weakenTrace (XS Z d) k) zz1 z0)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_A_BB_subst_B_Index0_commleft_ind (d : (Trace A)) (aa0 : AA) (bb0 : BB) :
      (forall (k : Hvl) (a3 : (Index A)) ,
        ((subst_A_Index (weakenTrace d k) aa0 a3) = (subst_B_AA (weakenTrace X0 k) (subst_A_BB d aa0 bb0) (subst_A_Index (weakenTrace (XS B d) k) aa0 a3)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_A_ZZ_subst_Z_Index0_commleft_ind (d : (Trace A)) (aa0 : AA) (zz1 : ZZ) :
      (forall (k : Hvl) (a3 : (Index A)) ,
        ((subst_A_Index (weakenTrace d k) aa0 a3) = (subst_Z_AA (weakenTrace X0 k) (subst_A_ZZ d aa0 zz1) (subst_A_Index (weakenTrace (XS Z d) k) aa0 a3)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_B_AA_subst_A_Index0_commleft_ind (d : (Trace B)) (bb0 : BB) (aa0 : AA) :
      (forall (k : Hvl) (b3 : (Index B)) ,
        ((subst_B_Index (weakenTrace d k) bb0 b3) = (subst_A_BB (weakenTrace X0 k) (subst_B_AA d bb0 aa0) (subst_B_Index (weakenTrace (XS A d) k) bb0 b3)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_B_ZZ_subst_Z_Index0_commleft_ind (d : (Trace B)) (bb0 : BB) (zz1 : ZZ) :
      (forall (k : Hvl) (b3 : (Index B)) ,
        ((subst_B_Index (weakenTrace d k) bb0 b3) = (subst_Z_BB (weakenTrace X0 k) (subst_B_ZZ d bb0 zz1) (subst_B_Index (weakenTrace (XS Z d) k) bb0 b3)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_Z_AA_subst_A_Index0_commleft_ind (d : (Trace Z)) (zz1 : ZZ) (aa0 : AA) :
      (forall (k : Hvl) (z0 : (Index Z)) ,
        ((subst_Z_Index (weakenTrace d k) zz1 z0) = (subst_A_ZZ (weakenTrace X0 k) (subst_Z_AA d zz1 aa0) (subst_Z_Index (weakenTrace (XS A d) k) zz1 z0)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
    Lemma subst_Z_BB_subst_B_Index0_commleft_ind (d : (Trace Z)) (zz1 : ZZ) (bb0 : BB) :
      (forall (k : Hvl) (z0 : (Index Z)) ,
        ((subst_Z_Index (weakenTrace d k) zz1 z0) = (subst_B_ZZ (weakenTrace X0 k) (subst_Z_BB d zz1 bb0) (subst_Z_Index (weakenTrace (XS B d) k) zz1 z0)))).
    Proof.
      needleGenericSubstSubstIndexCommInd .
    Qed.
  End SubstSubstIndexCommInd.
  Section SubstSubstCommInd.
    Fixpoint subst_A__subst_A_0_AA_comm_ind (aa2 : AA) (k : Hvl) (d : (Trace A)) (aa0 : AA) (aa1 : AA) {struct aa2} :
    ((subst_A_AA (weakenTrace d k) aa0 (subst_A_AA (weakenTrace X0 k) aa1 aa2)) = (subst_A_AA (weakenTrace X0 k) (subst_A_AA d aa0 aa1) (subst_A_AA (weakenTrace (XS A d) k) aa0 aa2))) :=
      match aa2 return ((subst_A_AA (weakenTrace d k) aa0 (subst_A_AA (weakenTrace X0 k) aa1 aa2)) = (subst_A_AA (weakenTrace X0 k) (subst_A_AA d aa0 aa1) (subst_A_AA (weakenTrace (XS A d) k) aa0 aa2))) with
        | (avar a3) => (subst_A_AA_subst_A_Index0_commright_ind d aa0 aa1 k a3)
        | (arec zz1) => (f_equal arec (subst_A__subst_A_0_ZZ_comm_ind zz1 k d aa0 aa1))
      end
    with subst_A__subst_A_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (d : (Trace A)) (aa0 : AA) (aa1 : AA) {struct zz2} :
    ((subst_A_ZZ (weakenTrace d k) aa0 (subst_A_ZZ (weakenTrace X0 k) aa1 zz2)) = (subst_A_ZZ (weakenTrace X0 k) (subst_A_AA d aa0 aa1) (subst_A_ZZ (weakenTrace (XS A d) k) aa0 zz2))) :=
      match zz2 return ((subst_A_ZZ (weakenTrace d k) aa0 (subst_A_ZZ (weakenTrace X0 k) aa1 zz2)) = (subst_A_ZZ (weakenTrace X0 k) (subst_A_AA d aa0 aa1) (subst_A_ZZ (weakenTrace (XS A d) k) aa0 zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa3) => (f_equal aabs (eq_trans (f_equal3 subst_A_AA (weakenTrace_append A d k (HS A H0)) eq_refl (f_equal3 subst_A_AA (weakenTrace_append A X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (subst_A__subst_A_0_AA_comm_ind aa3 (HS A k) d aa0 aa1) (f_equal3 subst_A_AA (eq_sym (weakenTrace_append A X0 k (HS A H0))) eq_refl (f_equal3 subst_A_AA (eq_sym (weakenTrace_append A (XS A d) k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal3 subst_A_BB (weakenTrace_append A d k (HS B H0)) eq_refl (f_equal3 subst_A_BB (weakenTrace_append A X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (subst_A__subst_A_0_BB_comm_ind bb0 (HS B k) d aa0 aa1) (f_equal3 subst_A_BB (eq_sym (weakenTrace_append A X0 k (HS B H0))) eq_refl (f_equal3 subst_A_BB (eq_sym (weakenTrace_append A (XS A d) k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_A__subst_A_0_BB_comm_ind (bb1 : BB) (k : Hvl) (d : (Trace A)) (aa0 : AA) (aa1 : AA) {struct bb1} :
    ((subst_A_BB (weakenTrace d k) aa0 (subst_A_BB (weakenTrace X0 k) aa1 bb1)) = (subst_A_BB (weakenTrace X0 k) (subst_A_AA d aa0 aa1) (subst_A_BB (weakenTrace (XS A d) k) aa0 bb1))) :=
      match bb1 return ((subst_A_BB (weakenTrace d k) aa0 (subst_A_BB (weakenTrace X0 k) aa1 bb1)) = (subst_A_BB (weakenTrace X0 k) (subst_A_AA d aa0 aa1) (subst_A_BB (weakenTrace (XS A d) k) aa0 bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz3) => (f_equal brec (subst_A__subst_A_0_ZZ_comm_ind zz3 k d aa0 aa1))
      end.
    Fixpoint subst_A__subst_B_0_AA_comm_ind (aa1 : AA) (k : Hvl) (d : (Trace A)) (aa0 : AA) (bb0 : BB) {struct aa1} :
    ((subst_A_AA (weakenTrace d k) aa0 (subst_B_AA (weakenTrace X0 k) bb0 aa1)) = (subst_B_AA (weakenTrace X0 k) (subst_A_BB d aa0 bb0) (subst_A_AA (weakenTrace (XS B d) k) aa0 aa1))) :=
      match aa1 return ((subst_A_AA (weakenTrace d k) aa0 (subst_B_AA (weakenTrace X0 k) bb0 aa1)) = (subst_B_AA (weakenTrace X0 k) (subst_A_BB d aa0 bb0) (subst_A_AA (weakenTrace (XS B d) k) aa0 aa1))) with
        | (avar a3) => (subst_A_BB_subst_B_Index0_commleft_ind d aa0 bb0 k a3)
        | (arec zz1) => (f_equal arec (subst_A__subst_B_0_ZZ_comm_ind zz1 k d aa0 bb0))
      end
    with subst_A__subst_B_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (d : (Trace A)) (aa0 : AA) (bb0 : BB) {struct zz2} :
    ((subst_A_ZZ (weakenTrace d k) aa0 (subst_B_ZZ (weakenTrace X0 k) bb0 zz2)) = (subst_B_ZZ (weakenTrace X0 k) (subst_A_BB d aa0 bb0) (subst_A_ZZ (weakenTrace (XS B d) k) aa0 zz2))) :=
      match zz2 return ((subst_A_ZZ (weakenTrace d k) aa0 (subst_B_ZZ (weakenTrace X0 k) bb0 zz2)) = (subst_B_ZZ (weakenTrace X0 k) (subst_A_BB d aa0 bb0) (subst_A_ZZ (weakenTrace (XS B d) k) aa0 zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa2) => (f_equal aabs (eq_trans (f_equal3 subst_A_AA (weakenTrace_append A d k (HS A H0)) eq_refl (f_equal3 subst_B_AA (weakenTrace_append B X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (subst_A__subst_B_0_AA_comm_ind aa2 (HS A k) d aa0 bb0) (f_equal3 subst_B_AA (eq_sym (weakenTrace_append B X0 k (HS A H0))) eq_refl (f_equal3 subst_A_AA (eq_sym (weakenTrace_append A (XS B d) k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb1) => (f_equal babs (eq_trans (f_equal3 subst_A_BB (weakenTrace_append A d k (HS B H0)) eq_refl (f_equal3 subst_B_BB (weakenTrace_append B X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (subst_A__subst_B_0_BB_comm_ind bb1 (HS B k) d aa0 bb0) (f_equal3 subst_B_BB (eq_sym (weakenTrace_append B X0 k (HS B H0))) eq_refl (f_equal3 subst_A_BB (eq_sym (weakenTrace_append A (XS B d) k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_A__subst_B_0_BB_comm_ind (bb2 : BB) (k : Hvl) (d : (Trace A)) (aa0 : AA) (bb0 : BB) {struct bb2} :
    ((subst_A_BB (weakenTrace d k) aa0 (subst_B_BB (weakenTrace X0 k) bb0 bb2)) = (subst_B_BB (weakenTrace X0 k) (subst_A_BB d aa0 bb0) (subst_A_BB (weakenTrace (XS B d) k) aa0 bb2))) :=
      match bb2 return ((subst_A_BB (weakenTrace d k) aa0 (subst_B_BB (weakenTrace X0 k) bb0 bb2)) = (subst_B_BB (weakenTrace X0 k) (subst_A_BB d aa0 bb0) (subst_A_BB (weakenTrace (XS B d) k) aa0 bb2))) with
        | (bvar b4) => (subst_A_BB_subst_B_Index0_commright_ind d aa0 bb0 k b4)
        | (brec zz3) => (f_equal brec (subst_A__subst_B_0_ZZ_comm_ind zz3 k d aa0 bb0))
      end.
    Fixpoint subst_A__subst_Z_0_AA_comm_ind (aa1 : AA) (k : Hvl) (d : (Trace A)) (aa0 : AA) (zz1 : ZZ) {struct aa1} :
    ((subst_A_AA (weakenTrace d k) aa0 (subst_Z_AA (weakenTrace X0 k) zz1 aa1)) = (subst_Z_AA (weakenTrace X0 k) (subst_A_ZZ d aa0 zz1) (subst_A_AA (weakenTrace (XS Z d) k) aa0 aa1))) :=
      match aa1 return ((subst_A_AA (weakenTrace d k) aa0 (subst_Z_AA (weakenTrace X0 k) zz1 aa1)) = (subst_Z_AA (weakenTrace X0 k) (subst_A_ZZ d aa0 zz1) (subst_A_AA (weakenTrace (XS Z d) k) aa0 aa1))) with
        | (avar a3) => (subst_A_ZZ_subst_Z_Index0_commleft_ind d aa0 zz1 k a3)
        | (arec zz2) => (f_equal arec (subst_A__subst_Z_0_ZZ_comm_ind zz2 k d aa0 zz1))
      end
    with subst_A__subst_Z_0_ZZ_comm_ind (zz3 : ZZ) (k : Hvl) (d : (Trace A)) (aa0 : AA) (zz1 : ZZ) {struct zz3} :
    ((subst_A_ZZ (weakenTrace d k) aa0 (subst_Z_ZZ (weakenTrace X0 k) zz1 zz3)) = (subst_Z_ZZ (weakenTrace X0 k) (subst_A_ZZ d aa0 zz1) (subst_A_ZZ (weakenTrace (XS Z d) k) aa0 zz3))) :=
      match zz3 return ((subst_A_ZZ (weakenTrace d k) aa0 (subst_Z_ZZ (weakenTrace X0 k) zz1 zz3)) = (subst_Z_ZZ (weakenTrace X0 k) (subst_A_ZZ d aa0 zz1) (subst_A_ZZ (weakenTrace (XS Z d) k) aa0 zz3))) with
        | (zvar z0) => (subst_A_ZZ_subst_Z_Index0_commright_ind d aa0 zz1 k z0)
        | (aabs aa2) => (f_equal aabs (eq_trans (f_equal3 subst_A_AA (weakenTrace_append A d k (HS A H0)) eq_refl (f_equal3 subst_Z_AA (weakenTrace_append Z X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (subst_A__subst_Z_0_AA_comm_ind aa2 (HS A k) d aa0 zz1) (f_equal3 subst_Z_AA (eq_sym (weakenTrace_append Z X0 k (HS A H0))) eq_refl (f_equal3 subst_A_AA (eq_sym (weakenTrace_append A (XS Z d) k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal3 subst_A_BB (weakenTrace_append A d k (HS B H0)) eq_refl (f_equal3 subst_Z_BB (weakenTrace_append Z X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (subst_A__subst_Z_0_BB_comm_ind bb0 (HS B k) d aa0 zz1) (f_equal3 subst_Z_BB (eq_sym (weakenTrace_append Z X0 k (HS B H0))) eq_refl (f_equal3 subst_A_BB (eq_sym (weakenTrace_append A (XS Z d) k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_A__subst_Z_0_BB_comm_ind (bb1 : BB) (k : Hvl) (d : (Trace A)) (aa0 : AA) (zz1 : ZZ) {struct bb1} :
    ((subst_A_BB (weakenTrace d k) aa0 (subst_Z_BB (weakenTrace X0 k) zz1 bb1)) = (subst_Z_BB (weakenTrace X0 k) (subst_A_ZZ d aa0 zz1) (subst_A_BB (weakenTrace (XS Z d) k) aa0 bb1))) :=
      match bb1 return ((subst_A_BB (weakenTrace d k) aa0 (subst_Z_BB (weakenTrace X0 k) zz1 bb1)) = (subst_Z_BB (weakenTrace X0 k) (subst_A_ZZ d aa0 zz1) (subst_A_BB (weakenTrace (XS Z d) k) aa0 bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz4) => (f_equal brec (subst_A__subst_Z_0_ZZ_comm_ind zz4 k d aa0 zz1))
      end.
    Fixpoint subst_B__subst_A_0_AA_comm_ind (aa1 : AA) (k : Hvl) (d : (Trace B)) (bb0 : BB) (aa0 : AA) {struct aa1} :
    ((subst_B_AA (weakenTrace d k) bb0 (subst_A_AA (weakenTrace X0 k) aa0 aa1)) = (subst_A_AA (weakenTrace X0 k) (subst_B_AA d bb0 aa0) (subst_B_AA (weakenTrace (XS A d) k) bb0 aa1))) :=
      match aa1 return ((subst_B_AA (weakenTrace d k) bb0 (subst_A_AA (weakenTrace X0 k) aa0 aa1)) = (subst_A_AA (weakenTrace X0 k) (subst_B_AA d bb0 aa0) (subst_B_AA (weakenTrace (XS A d) k) bb0 aa1))) with
        | (avar a3) => (subst_B_AA_subst_A_Index0_commright_ind d bb0 aa0 k a3)
        | (arec zz1) => (f_equal arec (subst_B__subst_A_0_ZZ_comm_ind zz1 k d bb0 aa0))
      end
    with subst_B__subst_A_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (d : (Trace B)) (bb0 : BB) (aa0 : AA) {struct zz2} :
    ((subst_B_ZZ (weakenTrace d k) bb0 (subst_A_ZZ (weakenTrace X0 k) aa0 zz2)) = (subst_A_ZZ (weakenTrace X0 k) (subst_B_AA d bb0 aa0) (subst_B_ZZ (weakenTrace (XS A d) k) bb0 zz2))) :=
      match zz2 return ((subst_B_ZZ (weakenTrace d k) bb0 (subst_A_ZZ (weakenTrace X0 k) aa0 zz2)) = (subst_A_ZZ (weakenTrace X0 k) (subst_B_AA d bb0 aa0) (subst_B_ZZ (weakenTrace (XS A d) k) bb0 zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa2) => (f_equal aabs (eq_trans (f_equal3 subst_B_AA (weakenTrace_append B d k (HS A H0)) eq_refl (f_equal3 subst_A_AA (weakenTrace_append A X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (subst_B__subst_A_0_AA_comm_ind aa2 (HS A k) d bb0 aa0) (f_equal3 subst_A_AA (eq_sym (weakenTrace_append A X0 k (HS A H0))) eq_refl (f_equal3 subst_B_AA (eq_sym (weakenTrace_append B (XS A d) k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb1) => (f_equal babs (eq_trans (f_equal3 subst_B_BB (weakenTrace_append B d k (HS B H0)) eq_refl (f_equal3 subst_A_BB (weakenTrace_append A X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (subst_B__subst_A_0_BB_comm_ind bb1 (HS B k) d bb0 aa0) (f_equal3 subst_A_BB (eq_sym (weakenTrace_append A X0 k (HS B H0))) eq_refl (f_equal3 subst_B_BB (eq_sym (weakenTrace_append B (XS A d) k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_B__subst_A_0_BB_comm_ind (bb2 : BB) (k : Hvl) (d : (Trace B)) (bb0 : BB) (aa0 : AA) {struct bb2} :
    ((subst_B_BB (weakenTrace d k) bb0 (subst_A_BB (weakenTrace X0 k) aa0 bb2)) = (subst_A_BB (weakenTrace X0 k) (subst_B_AA d bb0 aa0) (subst_B_BB (weakenTrace (XS A d) k) bb0 bb2))) :=
      match bb2 return ((subst_B_BB (weakenTrace d k) bb0 (subst_A_BB (weakenTrace X0 k) aa0 bb2)) = (subst_A_BB (weakenTrace X0 k) (subst_B_AA d bb0 aa0) (subst_B_BB (weakenTrace (XS A d) k) bb0 bb2))) with
        | (bvar b4) => (subst_B_AA_subst_A_Index0_commleft_ind d bb0 aa0 k b4)
        | (brec zz3) => (f_equal brec (subst_B__subst_A_0_ZZ_comm_ind zz3 k d bb0 aa0))
      end.
    Fixpoint subst_B__subst_B_0_AA_comm_ind (aa0 : AA) (k : Hvl) (d : (Trace B)) (bb0 : BB) (bb1 : BB) {struct aa0} :
    ((subst_B_AA (weakenTrace d k) bb0 (subst_B_AA (weakenTrace X0 k) bb1 aa0)) = (subst_B_AA (weakenTrace X0 k) (subst_B_BB d bb0 bb1) (subst_B_AA (weakenTrace (XS B d) k) bb0 aa0))) :=
      match aa0 return ((subst_B_AA (weakenTrace d k) bb0 (subst_B_AA (weakenTrace X0 k) bb1 aa0)) = (subst_B_AA (weakenTrace X0 k) (subst_B_BB d bb0 bb1) (subst_B_AA (weakenTrace (XS B d) k) bb0 aa0))) with
        | (avar a3) => eq_refl
        | (arec zz1) => (f_equal arec (subst_B__subst_B_0_ZZ_comm_ind zz1 k d bb0 bb1))
      end
    with subst_B__subst_B_0_ZZ_comm_ind (zz2 : ZZ) (k : Hvl) (d : (Trace B)) (bb0 : BB) (bb1 : BB) {struct zz2} :
    ((subst_B_ZZ (weakenTrace d k) bb0 (subst_B_ZZ (weakenTrace X0 k) bb1 zz2)) = (subst_B_ZZ (weakenTrace X0 k) (subst_B_BB d bb0 bb1) (subst_B_ZZ (weakenTrace (XS B d) k) bb0 zz2))) :=
      match zz2 return ((subst_B_ZZ (weakenTrace d k) bb0 (subst_B_ZZ (weakenTrace X0 k) bb1 zz2)) = (subst_B_ZZ (weakenTrace X0 k) (subst_B_BB d bb0 bb1) (subst_B_ZZ (weakenTrace (XS B d) k) bb0 zz2))) with
        | (zvar z0) => eq_refl
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal3 subst_B_AA (weakenTrace_append B d k (HS A H0)) eq_refl (f_equal3 subst_B_AA (weakenTrace_append B X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (subst_B__subst_B_0_AA_comm_ind aa1 (HS A k) d bb0 bb1) (f_equal3 subst_B_AA (eq_sym (weakenTrace_append B X0 k (HS A H0))) eq_refl (f_equal3 subst_B_AA (eq_sym (weakenTrace_append B (XS B d) k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb2) => (f_equal babs (eq_trans (f_equal3 subst_B_BB (weakenTrace_append B d k (HS B H0)) eq_refl (f_equal3 subst_B_BB (weakenTrace_append B X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (subst_B__subst_B_0_BB_comm_ind bb2 (HS B k) d bb0 bb1) (f_equal3 subst_B_BB (eq_sym (weakenTrace_append B X0 k (HS B H0))) eq_refl (f_equal3 subst_B_BB (eq_sym (weakenTrace_append B (XS B d) k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_B__subst_B_0_BB_comm_ind (bb3 : BB) (k : Hvl) (d : (Trace B)) (bb0 : BB) (bb1 : BB) {struct bb3} :
    ((subst_B_BB (weakenTrace d k) bb0 (subst_B_BB (weakenTrace X0 k) bb1 bb3)) = (subst_B_BB (weakenTrace X0 k) (subst_B_BB d bb0 bb1) (subst_B_BB (weakenTrace (XS B d) k) bb0 bb3))) :=
      match bb3 return ((subst_B_BB (weakenTrace d k) bb0 (subst_B_BB (weakenTrace X0 k) bb1 bb3)) = (subst_B_BB (weakenTrace X0 k) (subst_B_BB d bb0 bb1) (subst_B_BB (weakenTrace (XS B d) k) bb0 bb3))) with
        | (bvar b4) => (subst_B_BB_subst_B_Index0_commright_ind d bb0 bb1 k b4)
        | (brec zz3) => (f_equal brec (subst_B__subst_B_0_ZZ_comm_ind zz3 k d bb0 bb1))
      end.
    Fixpoint subst_B__subst_Z_0_AA_comm_ind (aa0 : AA) (k : Hvl) (d : (Trace B)) (bb0 : BB) (zz1 : ZZ) {struct aa0} :
    ((subst_B_AA (weakenTrace d k) bb0 (subst_Z_AA (weakenTrace X0 k) zz1 aa0)) = (subst_Z_AA (weakenTrace X0 k) (subst_B_ZZ d bb0 zz1) (subst_B_AA (weakenTrace (XS Z d) k) bb0 aa0))) :=
      match aa0 return ((subst_B_AA (weakenTrace d k) bb0 (subst_Z_AA (weakenTrace X0 k) zz1 aa0)) = (subst_Z_AA (weakenTrace X0 k) (subst_B_ZZ d bb0 zz1) (subst_B_AA (weakenTrace (XS Z d) k) bb0 aa0))) with
        | (avar a3) => eq_refl
        | (arec zz2) => (f_equal arec (subst_B__subst_Z_0_ZZ_comm_ind zz2 k d bb0 zz1))
      end
    with subst_B__subst_Z_0_ZZ_comm_ind (zz3 : ZZ) (k : Hvl) (d : (Trace B)) (bb0 : BB) (zz1 : ZZ) {struct zz3} :
    ((subst_B_ZZ (weakenTrace d k) bb0 (subst_Z_ZZ (weakenTrace X0 k) zz1 zz3)) = (subst_Z_ZZ (weakenTrace X0 k) (subst_B_ZZ d bb0 zz1) (subst_B_ZZ (weakenTrace (XS Z d) k) bb0 zz3))) :=
      match zz3 return ((subst_B_ZZ (weakenTrace d k) bb0 (subst_Z_ZZ (weakenTrace X0 k) zz1 zz3)) = (subst_Z_ZZ (weakenTrace X0 k) (subst_B_ZZ d bb0 zz1) (subst_B_ZZ (weakenTrace (XS Z d) k) bb0 zz3))) with
        | (zvar z0) => (subst_B_ZZ_subst_Z_Index0_commright_ind d bb0 zz1 k z0)
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal3 subst_B_AA (weakenTrace_append B d k (HS A H0)) eq_refl (f_equal3 subst_Z_AA (weakenTrace_append Z X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (subst_B__subst_Z_0_AA_comm_ind aa1 (HS A k) d bb0 zz1) (f_equal3 subst_Z_AA (eq_sym (weakenTrace_append Z X0 k (HS A H0))) eq_refl (f_equal3 subst_B_AA (eq_sym (weakenTrace_append B (XS Z d) k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb1) => (f_equal babs (eq_trans (f_equal3 subst_B_BB (weakenTrace_append B d k (HS B H0)) eq_refl (f_equal3 subst_Z_BB (weakenTrace_append Z X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (subst_B__subst_Z_0_BB_comm_ind bb1 (HS B k) d bb0 zz1) (f_equal3 subst_Z_BB (eq_sym (weakenTrace_append Z X0 k (HS B H0))) eq_refl (f_equal3 subst_B_BB (eq_sym (weakenTrace_append B (XS Z d) k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_B__subst_Z_0_BB_comm_ind (bb2 : BB) (k : Hvl) (d : (Trace B)) (bb0 : BB) (zz1 : ZZ) {struct bb2} :
    ((subst_B_BB (weakenTrace d k) bb0 (subst_Z_BB (weakenTrace X0 k) zz1 bb2)) = (subst_Z_BB (weakenTrace X0 k) (subst_B_ZZ d bb0 zz1) (subst_B_BB (weakenTrace (XS Z d) k) bb0 bb2))) :=
      match bb2 return ((subst_B_BB (weakenTrace d k) bb0 (subst_Z_BB (weakenTrace X0 k) zz1 bb2)) = (subst_Z_BB (weakenTrace X0 k) (subst_B_ZZ d bb0 zz1) (subst_B_BB (weakenTrace (XS Z d) k) bb0 bb2))) with
        | (bvar b4) => (subst_B_ZZ_subst_Z_Index0_commleft_ind d bb0 zz1 k b4)
        | (brec zz4) => (f_equal brec (subst_B__subst_Z_0_ZZ_comm_ind zz4 k d bb0 zz1))
      end.
    Fixpoint subst_Z__subst_A_0_AA_comm_ind (aa1 : AA) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) (aa0 : AA) {struct aa1} :
    ((subst_Z_AA (weakenTrace d k) zz1 (subst_A_AA (weakenTrace X0 k) aa0 aa1)) = (subst_A_AA (weakenTrace X0 k) (subst_Z_AA d zz1 aa0) (subst_Z_AA (weakenTrace (XS A d) k) zz1 aa1))) :=
      match aa1 return ((subst_Z_AA (weakenTrace d k) zz1 (subst_A_AA (weakenTrace X0 k) aa0 aa1)) = (subst_A_AA (weakenTrace X0 k) (subst_Z_AA d zz1 aa0) (subst_Z_AA (weakenTrace (XS A d) k) zz1 aa1))) with
        | (avar a3) => (subst_Z_AA_subst_A_Index0_commright_ind d zz1 aa0 k a3)
        | (arec zz2) => (f_equal arec (subst_Z__subst_A_0_ZZ_comm_ind zz2 k d zz1 aa0))
      end
    with subst_Z__subst_A_0_ZZ_comm_ind (zz3 : ZZ) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) (aa0 : AA) {struct zz3} :
    ((subst_Z_ZZ (weakenTrace d k) zz1 (subst_A_ZZ (weakenTrace X0 k) aa0 zz3)) = (subst_A_ZZ (weakenTrace X0 k) (subst_Z_AA d zz1 aa0) (subst_Z_ZZ (weakenTrace (XS A d) k) zz1 zz3))) :=
      match zz3 return ((subst_Z_ZZ (weakenTrace d k) zz1 (subst_A_ZZ (weakenTrace X0 k) aa0 zz3)) = (subst_A_ZZ (weakenTrace X0 k) (subst_Z_AA d zz1 aa0) (subst_Z_ZZ (weakenTrace (XS A d) k) zz1 zz3))) with
        | (zvar z0) => (subst_Z_AA_subst_A_Index0_commleft_ind d zz1 aa0 k z0)
        | (aabs aa2) => (f_equal aabs (eq_trans (f_equal3 subst_Z_AA (weakenTrace_append Z d k (HS A H0)) eq_refl (f_equal3 subst_A_AA (weakenTrace_append A X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (subst_Z__subst_A_0_AA_comm_ind aa2 (HS A k) d zz1 aa0) (f_equal3 subst_A_AA (eq_sym (weakenTrace_append A X0 k (HS A H0))) eq_refl (f_equal3 subst_Z_AA (eq_sym (weakenTrace_append Z (XS A d) k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal3 subst_Z_BB (weakenTrace_append Z d k (HS B H0)) eq_refl (f_equal3 subst_A_BB (weakenTrace_append A X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (subst_Z__subst_A_0_BB_comm_ind bb0 (HS B k) d zz1 aa0) (f_equal3 subst_A_BB (eq_sym (weakenTrace_append A X0 k (HS B H0))) eq_refl (f_equal3 subst_Z_BB (eq_sym (weakenTrace_append Z (XS A d) k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_Z__subst_A_0_BB_comm_ind (bb1 : BB) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) (aa0 : AA) {struct bb1} :
    ((subst_Z_BB (weakenTrace d k) zz1 (subst_A_BB (weakenTrace X0 k) aa0 bb1)) = (subst_A_BB (weakenTrace X0 k) (subst_Z_AA d zz1 aa0) (subst_Z_BB (weakenTrace (XS A d) k) zz1 bb1))) :=
      match bb1 return ((subst_Z_BB (weakenTrace d k) zz1 (subst_A_BB (weakenTrace X0 k) aa0 bb1)) = (subst_A_BB (weakenTrace X0 k) (subst_Z_AA d zz1 aa0) (subst_Z_BB (weakenTrace (XS A d) k) zz1 bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz4) => (f_equal brec (subst_Z__subst_A_0_ZZ_comm_ind zz4 k d zz1 aa0))
      end.
    Fixpoint subst_Z__subst_B_0_AA_comm_ind (aa0 : AA) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) (bb0 : BB) {struct aa0} :
    ((subst_Z_AA (weakenTrace d k) zz1 (subst_B_AA (weakenTrace X0 k) bb0 aa0)) = (subst_B_AA (weakenTrace X0 k) (subst_Z_BB d zz1 bb0) (subst_Z_AA (weakenTrace (XS B d) k) zz1 aa0))) :=
      match aa0 return ((subst_Z_AA (weakenTrace d k) zz1 (subst_B_AA (weakenTrace X0 k) bb0 aa0)) = (subst_B_AA (weakenTrace X0 k) (subst_Z_BB d zz1 bb0) (subst_Z_AA (weakenTrace (XS B d) k) zz1 aa0))) with
        | (avar a3) => eq_refl
        | (arec zz2) => (f_equal arec (subst_Z__subst_B_0_ZZ_comm_ind zz2 k d zz1 bb0))
      end
    with subst_Z__subst_B_0_ZZ_comm_ind (zz3 : ZZ) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) (bb0 : BB) {struct zz3} :
    ((subst_Z_ZZ (weakenTrace d k) zz1 (subst_B_ZZ (weakenTrace X0 k) bb0 zz3)) = (subst_B_ZZ (weakenTrace X0 k) (subst_Z_BB d zz1 bb0) (subst_Z_ZZ (weakenTrace (XS B d) k) zz1 zz3))) :=
      match zz3 return ((subst_Z_ZZ (weakenTrace d k) zz1 (subst_B_ZZ (weakenTrace X0 k) bb0 zz3)) = (subst_B_ZZ (weakenTrace X0 k) (subst_Z_BB d zz1 bb0) (subst_Z_ZZ (weakenTrace (XS B d) k) zz1 zz3))) with
        | (zvar z0) => (subst_Z_BB_subst_B_Index0_commleft_ind d zz1 bb0 k z0)
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal3 subst_Z_AA (weakenTrace_append Z d k (HS A H0)) eq_refl (f_equal3 subst_B_AA (weakenTrace_append B X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (subst_Z__subst_B_0_AA_comm_ind aa1 (HS A k) d zz1 bb0) (f_equal3 subst_B_AA (eq_sym (weakenTrace_append B X0 k (HS A H0))) eq_refl (f_equal3 subst_Z_AA (eq_sym (weakenTrace_append Z (XS B d) k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb1) => (f_equal babs (eq_trans (f_equal3 subst_Z_BB (weakenTrace_append Z d k (HS B H0)) eq_refl (f_equal3 subst_B_BB (weakenTrace_append B X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (subst_Z__subst_B_0_BB_comm_ind bb1 (HS B k) d zz1 bb0) (f_equal3 subst_B_BB (eq_sym (weakenTrace_append B X0 k (HS B H0))) eq_refl (f_equal3 subst_Z_BB (eq_sym (weakenTrace_append Z (XS B d) k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_Z__subst_B_0_BB_comm_ind (bb2 : BB) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) (bb0 : BB) {struct bb2} :
    ((subst_Z_BB (weakenTrace d k) zz1 (subst_B_BB (weakenTrace X0 k) bb0 bb2)) = (subst_B_BB (weakenTrace X0 k) (subst_Z_BB d zz1 bb0) (subst_Z_BB (weakenTrace (XS B d) k) zz1 bb2))) :=
      match bb2 return ((subst_Z_BB (weakenTrace d k) zz1 (subst_B_BB (weakenTrace X0 k) bb0 bb2)) = (subst_B_BB (weakenTrace X0 k) (subst_Z_BB d zz1 bb0) (subst_Z_BB (weakenTrace (XS B d) k) zz1 bb2))) with
        | (bvar b4) => (subst_Z_BB_subst_B_Index0_commright_ind d zz1 bb0 k b4)
        | (brec zz4) => (f_equal brec (subst_Z__subst_B_0_ZZ_comm_ind zz4 k d zz1 bb0))
      end.
    Fixpoint subst_Z__subst_Z_0_AA_comm_ind (aa0 : AA) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) (zz2 : ZZ) {struct aa0} :
    ((subst_Z_AA (weakenTrace d k) zz1 (subst_Z_AA (weakenTrace X0 k) zz2 aa0)) = (subst_Z_AA (weakenTrace X0 k) (subst_Z_ZZ d zz1 zz2) (subst_Z_AA (weakenTrace (XS Z d) k) zz1 aa0))) :=
      match aa0 return ((subst_Z_AA (weakenTrace d k) zz1 (subst_Z_AA (weakenTrace X0 k) zz2 aa0)) = (subst_Z_AA (weakenTrace X0 k) (subst_Z_ZZ d zz1 zz2) (subst_Z_AA (weakenTrace (XS Z d) k) zz1 aa0))) with
        | (avar a3) => eq_refl
        | (arec zz3) => (f_equal arec (subst_Z__subst_Z_0_ZZ_comm_ind zz3 k d zz1 zz2))
      end
    with subst_Z__subst_Z_0_ZZ_comm_ind (zz4 : ZZ) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) (zz2 : ZZ) {struct zz4} :
    ((subst_Z_ZZ (weakenTrace d k) zz1 (subst_Z_ZZ (weakenTrace X0 k) zz2 zz4)) = (subst_Z_ZZ (weakenTrace X0 k) (subst_Z_ZZ d zz1 zz2) (subst_Z_ZZ (weakenTrace (XS Z d) k) zz1 zz4))) :=
      match zz4 return ((subst_Z_ZZ (weakenTrace d k) zz1 (subst_Z_ZZ (weakenTrace X0 k) zz2 zz4)) = (subst_Z_ZZ (weakenTrace X0 k) (subst_Z_ZZ d zz1 zz2) (subst_Z_ZZ (weakenTrace (XS Z d) k) zz1 zz4))) with
        | (zvar z0) => (subst_Z_ZZ_subst_Z_Index0_commright_ind d zz1 zz2 k z0)
        | (aabs aa1) => (f_equal aabs (eq_trans (f_equal3 subst_Z_AA (weakenTrace_append Z d k (HS A H0)) eq_refl (f_equal3 subst_Z_AA (weakenTrace_append Z X0 k (HS A H0)) eq_refl eq_refl)) (eq_trans (subst_Z__subst_Z_0_AA_comm_ind aa1 (HS A k) d zz1 zz2) (f_equal3 subst_Z_AA (eq_sym (weakenTrace_append Z X0 k (HS A H0))) eq_refl (f_equal3 subst_Z_AA (eq_sym (weakenTrace_append Z (XS Z d) k (HS A H0))) eq_refl eq_refl)))))
        | (babs bb0) => (f_equal babs (eq_trans (f_equal3 subst_Z_BB (weakenTrace_append Z d k (HS B H0)) eq_refl (f_equal3 subst_Z_BB (weakenTrace_append Z X0 k (HS B H0)) eq_refl eq_refl)) (eq_trans (subst_Z__subst_Z_0_BB_comm_ind bb0 (HS B k) d zz1 zz2) (f_equal3 subst_Z_BB (eq_sym (weakenTrace_append Z X0 k (HS B H0))) eq_refl (f_equal3 subst_Z_BB (eq_sym (weakenTrace_append Z (XS Z d) k (HS B H0))) eq_refl eq_refl)))))
      end
    with subst_Z__subst_Z_0_BB_comm_ind (bb1 : BB) (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) (zz2 : ZZ) {struct bb1} :
    ((subst_Z_BB (weakenTrace d k) zz1 (subst_Z_BB (weakenTrace X0 k) zz2 bb1)) = (subst_Z_BB (weakenTrace X0 k) (subst_Z_ZZ d zz1 zz2) (subst_Z_BB (weakenTrace (XS Z d) k) zz1 bb1))) :=
      match bb1 return ((subst_Z_BB (weakenTrace d k) zz1 (subst_Z_BB (weakenTrace X0 k) zz2 bb1)) = (subst_Z_BB (weakenTrace X0 k) (subst_Z_ZZ d zz1 zz2) (subst_Z_BB (weakenTrace (XS Z d) k) zz1 bb1))) with
        | (bvar b4) => eq_refl
        | (brec zz5) => (f_equal brec (subst_Z__subst_Z_0_ZZ_comm_ind zz5 k d zz1 zz2))
      end.
  End SubstSubstCommInd.
  Section SubstSubstComm.
    Definition subst_A_AA_subst_A_AA0_comm (aa2 : AA) : (forall (d : (Trace A)) (aa0 : AA) (aa1 : AA) ,
      ((subst_A_AA d aa0 (subst_A_AA X0 aa1 aa2)) = (subst_A_AA X0 (subst_A_AA d aa0 aa1) (subst_A_AA (XS A d) aa0 aa2)))) := (subst_A__subst_A_0_AA_comm_ind aa2 H0).
    Definition subst_A_ZZ_subst_A_ZZ0_comm (zz1 : ZZ) : (forall (d : (Trace A)) (aa0 : AA) (aa1 : AA) ,
      ((subst_A_ZZ d aa0 (subst_A_ZZ X0 aa1 zz1)) = (subst_A_ZZ X0 (subst_A_AA d aa0 aa1) (subst_A_ZZ (XS A d) aa0 zz1)))) := (subst_A__subst_A_0_ZZ_comm_ind zz1 H0).
    Definition subst_A_BB_subst_A_BB0_comm (bb0 : BB) : (forall (d : (Trace A)) (aa0 : AA) (aa1 : AA) ,
      ((subst_A_BB d aa0 (subst_A_BB X0 aa1 bb0)) = (subst_A_BB X0 (subst_A_AA d aa0 aa1) (subst_A_BB (XS A d) aa0 bb0)))) := (subst_A__subst_A_0_BB_comm_ind bb0 H0).
    Definition subst_A_AA_subst_B_AA0_comm (aa1 : AA) : (forall (d : (Trace A)) (aa0 : AA) (bb0 : BB) ,
      ((subst_A_AA d aa0 (subst_B_AA X0 bb0 aa1)) = (subst_B_AA X0 (subst_A_BB d aa0 bb0) (subst_A_AA (XS B d) aa0 aa1)))) := (subst_A__subst_B_0_AA_comm_ind aa1 H0).
    Definition subst_A_ZZ_subst_B_ZZ0_comm (zz1 : ZZ) : (forall (d : (Trace A)) (aa0 : AA) (bb0 : BB) ,
      ((subst_A_ZZ d aa0 (subst_B_ZZ X0 bb0 zz1)) = (subst_B_ZZ X0 (subst_A_BB d aa0 bb0) (subst_A_ZZ (XS B d) aa0 zz1)))) := (subst_A__subst_B_0_ZZ_comm_ind zz1 H0).
    Definition subst_A_BB_subst_B_BB0_comm (bb1 : BB) : (forall (d : (Trace A)) (aa0 : AA) (bb0 : BB) ,
      ((subst_A_BB d aa0 (subst_B_BB X0 bb0 bb1)) = (subst_B_BB X0 (subst_A_BB d aa0 bb0) (subst_A_BB (XS B d) aa0 bb1)))) := (subst_A__subst_B_0_BB_comm_ind bb1 H0).
    Definition subst_A_AA_subst_Z_AA0_comm (aa1 : AA) : (forall (d : (Trace A)) (aa0 : AA) (zz1 : ZZ) ,
      ((subst_A_AA d aa0 (subst_Z_AA X0 zz1 aa1)) = (subst_Z_AA X0 (subst_A_ZZ d aa0 zz1) (subst_A_AA (XS Z d) aa0 aa1)))) := (subst_A__subst_Z_0_AA_comm_ind aa1 H0).
    Definition subst_A_ZZ_subst_Z_ZZ0_comm (zz2 : ZZ) : (forall (d : (Trace A)) (aa0 : AA) (zz1 : ZZ) ,
      ((subst_A_ZZ d aa0 (subst_Z_ZZ X0 zz1 zz2)) = (subst_Z_ZZ X0 (subst_A_ZZ d aa0 zz1) (subst_A_ZZ (XS Z d) aa0 zz2)))) := (subst_A__subst_Z_0_ZZ_comm_ind zz2 H0).
    Definition subst_A_BB_subst_Z_BB0_comm (bb0 : BB) : (forall (d : (Trace A)) (aa0 : AA) (zz1 : ZZ) ,
      ((subst_A_BB d aa0 (subst_Z_BB X0 zz1 bb0)) = (subst_Z_BB X0 (subst_A_ZZ d aa0 zz1) (subst_A_BB (XS Z d) aa0 bb0)))) := (subst_A__subst_Z_0_BB_comm_ind bb0 H0).
    Definition subst_B_AA_subst_A_AA0_comm (aa1 : AA) : (forall (d : (Trace B)) (bb0 : BB) (aa0 : AA) ,
      ((subst_B_AA d bb0 (subst_A_AA X0 aa0 aa1)) = (subst_A_AA X0 (subst_B_AA d bb0 aa0) (subst_B_AA (XS A d) bb0 aa1)))) := (subst_B__subst_A_0_AA_comm_ind aa1 H0).
    Definition subst_B_ZZ_subst_A_ZZ0_comm (zz1 : ZZ) : (forall (d : (Trace B)) (bb0 : BB) (aa0 : AA) ,
      ((subst_B_ZZ d bb0 (subst_A_ZZ X0 aa0 zz1)) = (subst_A_ZZ X0 (subst_B_AA d bb0 aa0) (subst_B_ZZ (XS A d) bb0 zz1)))) := (subst_B__subst_A_0_ZZ_comm_ind zz1 H0).
    Definition subst_B_BB_subst_A_BB0_comm (bb1 : BB) : (forall (d : (Trace B)) (bb0 : BB) (aa0 : AA) ,
      ((subst_B_BB d bb0 (subst_A_BB X0 aa0 bb1)) = (subst_A_BB X0 (subst_B_AA d bb0 aa0) (subst_B_BB (XS A d) bb0 bb1)))) := (subst_B__subst_A_0_BB_comm_ind bb1 H0).
    Definition subst_B_AA_subst_B_AA0_comm (aa0 : AA) : (forall (d : (Trace B)) (bb0 : BB) (bb1 : BB) ,
      ((subst_B_AA d bb0 (subst_B_AA X0 bb1 aa0)) = (subst_B_AA X0 (subst_B_BB d bb0 bb1) (subst_B_AA (XS B d) bb0 aa0)))) := (subst_B__subst_B_0_AA_comm_ind aa0 H0).
    Definition subst_B_ZZ_subst_B_ZZ0_comm (zz1 : ZZ) : (forall (d : (Trace B)) (bb0 : BB) (bb1 : BB) ,
      ((subst_B_ZZ d bb0 (subst_B_ZZ X0 bb1 zz1)) = (subst_B_ZZ X0 (subst_B_BB d bb0 bb1) (subst_B_ZZ (XS B d) bb0 zz1)))) := (subst_B__subst_B_0_ZZ_comm_ind zz1 H0).
    Definition subst_B_BB_subst_B_BB0_comm (bb2 : BB) : (forall (d : (Trace B)) (bb0 : BB) (bb1 : BB) ,
      ((subst_B_BB d bb0 (subst_B_BB X0 bb1 bb2)) = (subst_B_BB X0 (subst_B_BB d bb0 bb1) (subst_B_BB (XS B d) bb0 bb2)))) := (subst_B__subst_B_0_BB_comm_ind bb2 H0).
    Definition subst_B_AA_subst_Z_AA0_comm (aa0 : AA) : (forall (d : (Trace B)) (bb0 : BB) (zz1 : ZZ) ,
      ((subst_B_AA d bb0 (subst_Z_AA X0 zz1 aa0)) = (subst_Z_AA X0 (subst_B_ZZ d bb0 zz1) (subst_B_AA (XS Z d) bb0 aa0)))) := (subst_B__subst_Z_0_AA_comm_ind aa0 H0).
    Definition subst_B_ZZ_subst_Z_ZZ0_comm (zz2 : ZZ) : (forall (d : (Trace B)) (bb0 : BB) (zz1 : ZZ) ,
      ((subst_B_ZZ d bb0 (subst_Z_ZZ X0 zz1 zz2)) = (subst_Z_ZZ X0 (subst_B_ZZ d bb0 zz1) (subst_B_ZZ (XS Z d) bb0 zz2)))) := (subst_B__subst_Z_0_ZZ_comm_ind zz2 H0).
    Definition subst_B_BB_subst_Z_BB0_comm (bb1 : BB) : (forall (d : (Trace B)) (bb0 : BB) (zz1 : ZZ) ,
      ((subst_B_BB d bb0 (subst_Z_BB X0 zz1 bb1)) = (subst_Z_BB X0 (subst_B_ZZ d bb0 zz1) (subst_B_BB (XS Z d) bb0 bb1)))) := (subst_B__subst_Z_0_BB_comm_ind bb1 H0).
    Definition subst_Z_AA_subst_A_AA0_comm (aa1 : AA) : (forall (d : (Trace Z)) (zz1 : ZZ) (aa0 : AA) ,
      ((subst_Z_AA d zz1 (subst_A_AA X0 aa0 aa1)) = (subst_A_AA X0 (subst_Z_AA d zz1 aa0) (subst_Z_AA (XS A d) zz1 aa1)))) := (subst_Z__subst_A_0_AA_comm_ind aa1 H0).
    Definition subst_Z_ZZ_subst_A_ZZ0_comm (zz2 : ZZ) : (forall (d : (Trace Z)) (zz1 : ZZ) (aa0 : AA) ,
      ((subst_Z_ZZ d zz1 (subst_A_ZZ X0 aa0 zz2)) = (subst_A_ZZ X0 (subst_Z_AA d zz1 aa0) (subst_Z_ZZ (XS A d) zz1 zz2)))) := (subst_Z__subst_A_0_ZZ_comm_ind zz2 H0).
    Definition subst_Z_BB_subst_A_BB0_comm (bb0 : BB) : (forall (d : (Trace Z)) (zz1 : ZZ) (aa0 : AA) ,
      ((subst_Z_BB d zz1 (subst_A_BB X0 aa0 bb0)) = (subst_A_BB X0 (subst_Z_AA d zz1 aa0) (subst_Z_BB (XS A d) zz1 bb0)))) := (subst_Z__subst_A_0_BB_comm_ind bb0 H0).
    Definition subst_Z_AA_subst_B_AA0_comm (aa0 : AA) : (forall (d : (Trace Z)) (zz1 : ZZ) (bb0 : BB) ,
      ((subst_Z_AA d zz1 (subst_B_AA X0 bb0 aa0)) = (subst_B_AA X0 (subst_Z_BB d zz1 bb0) (subst_Z_AA (XS B d) zz1 aa0)))) := (subst_Z__subst_B_0_AA_comm_ind aa0 H0).
    Definition subst_Z_ZZ_subst_B_ZZ0_comm (zz2 : ZZ) : (forall (d : (Trace Z)) (zz1 : ZZ) (bb0 : BB) ,
      ((subst_Z_ZZ d zz1 (subst_B_ZZ X0 bb0 zz2)) = (subst_B_ZZ X0 (subst_Z_BB d zz1 bb0) (subst_Z_ZZ (XS B d) zz1 zz2)))) := (subst_Z__subst_B_0_ZZ_comm_ind zz2 H0).
    Definition subst_Z_BB_subst_B_BB0_comm (bb1 : BB) : (forall (d : (Trace Z)) (zz1 : ZZ) (bb0 : BB) ,
      ((subst_Z_BB d zz1 (subst_B_BB X0 bb0 bb1)) = (subst_B_BB X0 (subst_Z_BB d zz1 bb0) (subst_Z_BB (XS B d) zz1 bb1)))) := (subst_Z__subst_B_0_BB_comm_ind bb1 H0).
    Definition subst_Z_AA_subst_Z_AA0_comm (aa0 : AA) : (forall (d : (Trace Z)) (zz1 : ZZ) (zz2 : ZZ) ,
      ((subst_Z_AA d zz1 (subst_Z_AA X0 zz2 aa0)) = (subst_Z_AA X0 (subst_Z_ZZ d zz1 zz2) (subst_Z_AA (XS Z d) zz1 aa0)))) := (subst_Z__subst_Z_0_AA_comm_ind aa0 H0).
    Definition subst_Z_ZZ_subst_Z_ZZ0_comm (zz3 : ZZ) : (forall (d : (Trace Z)) (zz1 : ZZ) (zz2 : ZZ) ,
      ((subst_Z_ZZ d zz1 (subst_Z_ZZ X0 zz2 zz3)) = (subst_Z_ZZ X0 (subst_Z_ZZ d zz1 zz2) (subst_Z_ZZ (XS Z d) zz1 zz3)))) := (subst_Z__subst_Z_0_ZZ_comm_ind zz3 H0).
    Definition subst_Z_BB_subst_Z_BB0_comm (bb0 : BB) : (forall (d : (Trace Z)) (zz1 : ZZ) (zz2 : ZZ) ,
      ((subst_Z_BB d zz1 (subst_Z_BB X0 zz2 bb0)) = (subst_Z_BB X0 (subst_Z_ZZ d zz1 zz2) (subst_Z_BB (XS Z d) zz1 bb0)))) := (subst_Z__subst_Z_0_BB_comm_ind bb0 H0).
  End SubstSubstComm.
  Section WeakenSubst.
    Lemma weakenAA_subst_A_AA  :
      (forall (k : Hvl) (d : (Trace A)) (aa0 : AA) (aa1 : AA) ,
        ((weakenAA (subst_A_AA d aa0 aa1) k) = (subst_A_AA (weakenTrace d k) aa0 (weakenAA aa1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenZZ_subst_A_ZZ  :
      (forall (k : Hvl) (d : (Trace A)) (aa0 : AA) (zz1 : ZZ) ,
        ((weakenZZ (subst_A_ZZ d aa0 zz1) k) = (subst_A_ZZ (weakenTrace d k) aa0 (weakenZZ zz1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenBB_subst_A_BB  :
      (forall (k : Hvl) (d : (Trace A)) (aa0 : AA) (bb0 : BB) ,
        ((weakenBB (subst_A_BB d aa0 bb0) k) = (subst_A_BB (weakenTrace d k) aa0 (weakenBB bb0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenAA_subst_B_AA  :
      (forall (k : Hvl) (d : (Trace B)) (bb0 : BB) (aa0 : AA) ,
        ((weakenAA (subst_B_AA d bb0 aa0) k) = (subst_B_AA (weakenTrace d k) bb0 (weakenAA aa0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenZZ_subst_B_ZZ  :
      (forall (k : Hvl) (d : (Trace B)) (bb0 : BB) (zz1 : ZZ) ,
        ((weakenZZ (subst_B_ZZ d bb0 zz1) k) = (subst_B_ZZ (weakenTrace d k) bb0 (weakenZZ zz1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenBB_subst_B_BB  :
      (forall (k : Hvl) (d : (Trace B)) (bb0 : BB) (bb1 : BB) ,
        ((weakenBB (subst_B_BB d bb0 bb1) k) = (subst_B_BB (weakenTrace d k) bb0 (weakenBB bb1 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenAA_subst_Z_AA  :
      (forall (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) (aa0 : AA) ,
        ((weakenAA (subst_Z_AA d zz1 aa0) k) = (subst_Z_AA (weakenTrace d k) zz1 (weakenAA aa0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenZZ_subst_Z_ZZ  :
      (forall (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) (zz2 : ZZ) ,
        ((weakenZZ (subst_Z_ZZ d zz1 zz2) k) = (subst_Z_ZZ (weakenTrace d k) zz1 (weakenZZ zz2 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
    Lemma weakenBB_subst_Z_BB  :
      (forall (k : Hvl) (d : (Trace Z)) (zz1 : ZZ) (bb0 : BB) ,
        ((weakenBB (subst_Z_BB d zz1 bb0) k) = (subst_Z_BB (weakenTrace d k) zz1 (weakenBB bb0 k)))).
    Proof.
      needleGenericWeakenSubst .
    Qed.
  End WeakenSubst.
End SubstSubstInteraction.
 Hint Rewrite subst_A_AA_subst_A_AA0_comm subst_B_AA_subst_B_AA0_comm subst_Z_AA_subst_Z_AA0_comm subst_A_BB_subst_A_BB0_comm subst_B_BB_subst_B_BB0_comm subst_Z_BB_subst_Z_BB0_comm subst_A_ZZ_subst_A_ZZ0_comm subst_B_ZZ_subst_B_ZZ0_comm subst_Z_ZZ_subst_Z_ZZ0_comm : interaction.
 Hint Rewrite subst_A_AA_subst_A_AA0_comm subst_B_AA_subst_B_AA0_comm subst_Z_AA_subst_Z_AA0_comm subst_A_BB_subst_A_BB0_comm subst_B_BB_subst_B_BB0_comm subst_Z_BB_subst_Z_BB0_comm subst_A_ZZ_subst_A_ZZ0_comm subst_B_ZZ_subst_B_ZZ0_comm subst_Z_ZZ_subst_Z_ZZ0_comm : subst_subst0.
 Hint Rewrite weakenAA_shift_A_AA weakenAA_shift_B_AA weakenAA_shift_Z_AA weakenBB_shift_A_BB weakenBB_shift_B_BB weakenBB_shift_Z_BB weakenZZ_shift_A_ZZ weakenZZ_shift_B_ZZ weakenZZ_shift_Z_ZZ : weaken_shift.
 Hint Rewrite weakenAA_subst_A_AA weakenAA_subst_B_AA weakenAA_subst_Z_AA weakenBB_subst_A_BB weakenBB_subst_B_BB weakenBB_subst_Z_BB weakenZZ_subst_A_ZZ weakenZZ_subst_B_ZZ weakenZZ_subst_Z_ZZ : weaken_subst.
Section WellFormed.
  Fixpoint wfindex {a3 : Namespace} (k : Hvl) (i : (Index a3)) {struct k} :
  Prop :=
    match k with
      | (H0) => False
      | (HS b3 k) => match (eq_namespace_dec a3 b3) with
        | (left e) => match i with
          | (I0) => True
          | (IS i) => (wfindex k i)
        end
        | (right n) => (wfindex k i)
      end
    end.
  Inductive wfAA (k : Hvl) : AA -> Prop :=
    | wfAA_avar (a3 : (Index A))
        (wfi : (wfindex k a3)) :
        (wfAA k (avar a3))
    | wfAA_arec {zz1 : ZZ}
        (wf : (wfZZ k zz1)) :
        (wfAA k (arec zz1))
  with wfZZ (k : Hvl) : ZZ -> Prop :=
    | wfZZ_zvar (z0 : (Index Z))
        (wfi : (wfindex k z0)) :
        (wfZZ k (zvar z0))
    | wfZZ_aabs {aa0 : AA}
        (wf : (wfAA (HS A k) aa0)) :
        (wfZZ k (aabs aa0))
    | wfZZ_babs {bb0 : BB}
        (wf : (wfBB (HS B k) bb0)) :
        (wfZZ k (babs bb0))
  with wfBB (k : Hvl) : BB -> Prop :=
    | wfBB_bvar (b3 : (Index B))
        (wfi : (wfindex k b3)) :
        (wfBB k (bvar b3))
    | wfBB_brec {zz1 : ZZ}
        (wf : (wfZZ k zz1)) :
        (wfBB k (brec zz1)).
  Definition inversion_wfAA_avar_1 (k : Hvl) (a : (Index A)) (H8 : (wfAA k (avar a))) : (wfindex k a) := match H8 in (wfAA _ aa0) return match aa0 return Prop with
    | (avar a) => (wfindex k a)
    | _ => True
  end with
    | (wfAA_avar a H1) => H1
    | _ => I
  end.
  Definition inversion_wfAA_arec_0 (k0 : Hvl) (zz : ZZ) (H9 : (wfAA k0 (arec zz))) : (wfZZ k0 zz) := match H9 in (wfAA _ aa1) return match aa1 return Prop with
    | (arec zz) => (wfZZ k0 zz)
    | _ => True
  end with
    | (wfAA_arec zz H2) => H2
    | _ => I
  end.
  Definition inversion_wfZZ_zvar_1 (k1 : Hvl) (z : (Index Z)) (H10 : (wfZZ k1 (zvar z))) : (wfindex k1 z) := match H10 in (wfZZ _ zz1) return match zz1 return Prop with
    | (zvar z) => (wfindex k1 z)
    | _ => True
  end with
    | (wfZZ_zvar z H3) => H3
    | _ => I
  end.
  Definition inversion_wfZZ_aabs_1 (k2 : Hvl) (aa : AA) (H11 : (wfZZ k2 (aabs aa))) : (wfAA (HS A k2) aa) := match H11 in (wfZZ _ zz2) return match zz2 return Prop with
    | (aabs aa) => (wfAA (HS A k2) aa)
    | _ => True
  end with
    | (wfZZ_aabs aa H4) => H4
    | _ => I
  end.
  Definition inversion_wfZZ_babs_1 (k3 : Hvl) (bb : BB) (H12 : (wfZZ k3 (babs bb))) : (wfBB (HS B k3) bb) := match H12 in (wfZZ _ zz3) return match zz3 return Prop with
    | (babs bb) => (wfBB (HS B k3) bb)
    | _ => True
  end with
    | (wfZZ_babs bb H5) => H5
    | _ => I
  end.
  Definition inversion_wfBB_bvar_1 (k4 : Hvl) (b : (Index B)) (H13 : (wfBB k4 (bvar b))) : (wfindex k4 b) := match H13 in (wfBB _ bb0) return match bb0 return Prop with
    | (bvar b) => (wfindex k4 b)
    | _ => True
  end with
    | (wfBB_bvar b H6) => H6
    | _ => I
  end.
  Definition inversion_wfBB_brec_0 (k5 : Hvl) (zz : ZZ) (H14 : (wfBB k5 (brec zz))) : (wfZZ k5 zz) := match H14 in (wfBB _ bb1) return match bb1 return Prop with
    | (brec zz) => (wfZZ k5 zz)
    | _ => True
  end with
    | (wfBB_brec zz H7) => H7
    | _ => I
  end.
  Scheme ind_wfAA := Induction for wfAA Sort Prop
  with ind_wfZZ := Induction for wfZZ Sort Prop
  with ind_wfBB := Induction for wfBB Sort Prop.
  Combined Scheme ind_wfAA_ZZ_BB from ind_wfAA, ind_wfZZ, ind_wfBB.
End WellFormed.
Section ShiftWellFormed.
  Inductive shifthvl_A : (forall (c : (Cutoff A)) (k6 : Hvl) (k7 : Hvl) ,
    Prop) :=
    | shifthvl_A_here (k6 : Hvl) :
        (shifthvl_A C0 k6 (HS A k6))
    | shifthvl_A_there_A
        (c : (Cutoff A)) (k6 : Hvl)
        (k7 : Hvl) :
        (shifthvl_A c k6 k7) -> (shifthvl_A (CS c) (HS A k6) (HS A k7))
    | shifthvl_A_there_B
        (c : (Cutoff A)) (k6 : Hvl)
        (k7 : Hvl) :
        (shifthvl_A c k6 k7) -> (shifthvl_A c (HS B k6) (HS B k7))
    | shifthvl_A_there_Z
        (c : (Cutoff A)) (k6 : Hvl)
        (k7 : Hvl) :
        (shifthvl_A c k6 k7) -> (shifthvl_A c (HS Z k6) (HS Z k7)).
  Inductive shifthvl_B : (forall (c : (Cutoff B)) (k6 : Hvl) (k7 : Hvl) ,
    Prop) :=
    | shifthvl_B_here (k6 : Hvl) :
        (shifthvl_B C0 k6 (HS B k6))
    | shifthvl_B_there_A
        (c : (Cutoff B)) (k6 : Hvl)
        (k7 : Hvl) :
        (shifthvl_B c k6 k7) -> (shifthvl_B c (HS A k6) (HS A k7))
    | shifthvl_B_there_B
        (c : (Cutoff B)) (k6 : Hvl)
        (k7 : Hvl) :
        (shifthvl_B c k6 k7) -> (shifthvl_B (CS c) (HS B k6) (HS B k7))
    | shifthvl_B_there_Z
        (c : (Cutoff B)) (k6 : Hvl)
        (k7 : Hvl) :
        (shifthvl_B c k6 k7) -> (shifthvl_B c (HS Z k6) (HS Z k7)).
  Inductive shifthvl_Z : (forall (c : (Cutoff Z)) (k6 : Hvl) (k7 : Hvl) ,
    Prop) :=
    | shifthvl_Z_here (k6 : Hvl) :
        (shifthvl_Z C0 k6 (HS Z k6))
    | shifthvl_Z_there_A
        (c : (Cutoff Z)) (k6 : Hvl)
        (k7 : Hvl) :
        (shifthvl_Z c k6 k7) -> (shifthvl_Z c (HS A k6) (HS A k7))
    | shifthvl_Z_there_B
        (c : (Cutoff Z)) (k6 : Hvl)
        (k7 : Hvl) :
        (shifthvl_Z c k6 k7) -> (shifthvl_Z c (HS B k6) (HS B k7))
    | shifthvl_Z_there_Z
        (c : (Cutoff Z)) (k6 : Hvl)
        (k7 : Hvl) :
        (shifthvl_Z c k6 k7) -> (shifthvl_Z (CS c) (HS Z k6) (HS Z k7)).
  Lemma weaken_shifthvl_A  :
    (forall (k6 : Hvl) {c : (Cutoff A)} {k7 : Hvl} {k8 : Hvl} ,
      (shifthvl_A c k7 k8) -> (shifthvl_A (weakenCutoffA c k6) (appendHvl k7 k6) (appendHvl k8 k6))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_B  :
    (forall (k6 : Hvl) {c : (Cutoff B)} {k7 : Hvl} {k8 : Hvl} ,
      (shifthvl_B c k7 k8) -> (shifthvl_B (weakenCutoffB c k6) (appendHvl k7 k6) (appendHvl k8 k6))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma weaken_shifthvl_Z  :
    (forall (k6 : Hvl) {c : (Cutoff Z)} {k7 : Hvl} {k8 : Hvl} ,
      (shifthvl_Z c k7 k8) -> (shifthvl_Z (weakenCutoffZ c k6) (appendHvl k7 k6) (appendHvl k8 k6))).
  Proof.
    needleGenericWeakenHVarlistInsert .
  Qed.
  Lemma shift_A__wfindex_A  :
    (forall (c : (Cutoff A)) (k6 : Hvl) (k7 : Hvl) (ins : (shifthvl_A c k6 k7)) (a3 : (Index A)) ,
      (wfindex k6 a3) -> (wfindex k7 (shift_A_Index c a3))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_A__wfindex_B  :
    (forall (c : (Cutoff A)) (k6 : Hvl) (k7 : Hvl) (ins : (shifthvl_A c k6 k7)) (b3 : (Index B)) ,
      (wfindex k6 b3) -> (wfindex k7 b3)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_A__wfindex_Z  :
    (forall (c : (Cutoff A)) (k6 : Hvl) (k7 : Hvl) (ins : (shifthvl_A c k6 k7)) (z0 : (Index Z)) ,
      (wfindex k6 z0) -> (wfindex k7 z0)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_B__wfindex_A  :
    (forall (c : (Cutoff B)) (k6 : Hvl) (k7 : Hvl) (ins : (shifthvl_B c k6 k7)) (a3 : (Index A)) ,
      (wfindex k6 a3) -> (wfindex k7 a3)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_B__wfindex_B  :
    (forall (c : (Cutoff B)) (k6 : Hvl) (k7 : Hvl) (ins : (shifthvl_B c k6 k7)) (b3 : (Index B)) ,
      (wfindex k6 b3) -> (wfindex k7 (shift_B_Index c b3))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_B__wfindex_Z  :
    (forall (c : (Cutoff B)) (k6 : Hvl) (k7 : Hvl) (ins : (shifthvl_B c k6 k7)) (z0 : (Index Z)) ,
      (wfindex k6 z0) -> (wfindex k7 z0)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_Z__wfindex_A  :
    (forall (c : (Cutoff Z)) (k6 : Hvl) (k7 : Hvl) (ins : (shifthvl_Z c k6 k7)) (a3 : (Index A)) ,
      (wfindex k6 a3) -> (wfindex k7 a3)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_Z__wfindex_B  :
    (forall (c : (Cutoff Z)) (k6 : Hvl) (k7 : Hvl) (ins : (shifthvl_Z c k6 k7)) (b3 : (Index B)) ,
      (wfindex k6 b3) -> (wfindex k7 b3)).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Lemma shift_Z__wfindex_Z  :
    (forall (c : (Cutoff Z)) (k6 : Hvl) (k7 : Hvl) (ins : (shifthvl_Z c k6 k7)) (z0 : (Index Z)) ,
      (wfindex k6 z0) -> (wfindex k7 (shift_Z_Index c z0))).
  Proof.
    needleGenericShiftWellFormedIndex .
  Qed.
  Definition shift_A__wfAA_ZZ_BB : (forall (k6 : Hvl) ,
    (forall (aa2 : AA) (wf : (wfAA k6 aa2)) ,
      (forall (c : (Cutoff A)) (k7 : Hvl) ,
        (shifthvl_A c k6 k7) -> (wfAA k7 (shift_A_AA c aa2)))) /\
    (forall (zz4 : ZZ) (wf : (wfZZ k6 zz4)) ,
      (forall (c : (Cutoff A)) (k7 : Hvl) ,
        (shifthvl_A c k6 k7) -> (wfZZ k7 (shift_A_ZZ c zz4)))) /\
    (forall (bb2 : BB) (wf : (wfBB k6 bb2)) ,
      (forall (c : (Cutoff A)) (k7 : Hvl) ,
        (shifthvl_A c k6 k7) -> (wfBB k7 (shift_A_BB c bb2))))) := (ind_wfAA_ZZ_BB (fun (k6 : Hvl) (aa2 : AA) (wf : (wfAA k6 aa2)) =>
    (forall (c : (Cutoff A)) (k7 : Hvl) ,
      (shifthvl_A c k6 k7) -> (wfAA k7 (shift_A_AA c aa2)))) (fun (k6 : Hvl) (zz4 : ZZ) (wf : (wfZZ k6 zz4)) =>
    (forall (c : (Cutoff A)) (k7 : Hvl) ,
      (shifthvl_A c k6 k7) -> (wfZZ k7 (shift_A_ZZ c zz4)))) (fun (k6 : Hvl) (bb2 : BB) (wf : (wfBB k6 bb2)) =>
    (forall (c : (Cutoff A)) (k7 : Hvl) ,
      (shifthvl_A c k6 k7) -> (wfBB k7 (shift_A_BB c bb2)))) (fun (k6 : Hvl) (a3 : (Index A)) (wfi : (wfindex k6 a3)) (c : (Cutoff A)) (k7 : Hvl) (ins : (shifthvl_A c k6 k7)) =>
    (wfAA_avar k7 _ (shift_A__wfindex_A c k6 k7 ins a3 wfi))) (fun (k6 : Hvl) (zz : ZZ) (wf : (wfZZ k6 zz)) IHzz (c : (Cutoff A)) (k7 : Hvl) (ins : (shifthvl_A c k6 k7)) =>
    (wfAA_arec k7 (IHzz c k7 (weaken_shifthvl_A H0 ins)))) (fun (k6 : Hvl) (z0 : (Index Z)) (wfi : (wfindex k6 z0)) (c : (Cutoff A)) (k7 : Hvl) (ins : (shifthvl_A c k6 k7)) =>
    (wfZZ_zvar k7 _ (shift_A__wfindex_Z c k6 k7 ins z0 wfi))) (fun (k6 : Hvl) (aa : AA) (wf : (wfAA (HS A k6) aa)) IHaa (c : (Cutoff A)) (k7 : Hvl) (ins : (shifthvl_A c k6 k7)) =>
    (wfZZ_aabs k7 (IHaa (CS c) (HS A k7) (weaken_shifthvl_A (HS A H0) ins)))) (fun (k6 : Hvl) (bb : BB) (wf : (wfBB (HS B k6) bb)) IHbb (c : (Cutoff A)) (k7 : Hvl) (ins : (shifthvl_A c k6 k7)) =>
    (wfZZ_babs k7 (IHbb c (HS B k7) (weaken_shifthvl_A (HS B H0) ins)))) (fun (k6 : Hvl) (b3 : (Index B)) (wfi : (wfindex k6 b3)) (c : (Cutoff A)) (k7 : Hvl) (ins : (shifthvl_A c k6 k7)) =>
    (wfBB_bvar k7 _ (shift_A__wfindex_B c k6 k7 ins b3 wfi))) (fun (k6 : Hvl) (zz : ZZ) (wf : (wfZZ k6 zz)) IHzz (c : (Cutoff A)) (k7 : Hvl) (ins : (shifthvl_A c k6 k7)) =>
    (wfBB_brec k7 (IHzz c k7 (weaken_shifthvl_A H0 ins))))).
  Lemma shift_A__wfAA (k6 : Hvl) :
    (forall (aa2 : AA) (wf : (wfAA k6 aa2)) ,
      (forall (c : (Cutoff A)) (k7 : Hvl) ,
        (shifthvl_A c k6 k7) -> (wfAA k7 (shift_A_AA c aa2)))).
  Proof.
    pose proof ((shift_A__wfAA_ZZ_BB k6)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_A__wfZZ (k6 : Hvl) :
    (forall (zz4 : ZZ) (wf0 : (wfZZ k6 zz4)) ,
      (forall (c0 : (Cutoff A)) (k8 : Hvl) ,
        (shifthvl_A c0 k6 k8) -> (wfZZ k8 (shift_A_ZZ c0 zz4)))).
  Proof.
    pose proof ((shift_A__wfAA_ZZ_BB k6)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_A__wfBB (k6 : Hvl) :
    (forall (bb2 : BB) (wf1 : (wfBB k6 bb2)) ,
      (forall (c1 : (Cutoff A)) (k9 : Hvl) ,
        (shifthvl_A c1 k6 k9) -> (wfBB k9 (shift_A_BB c1 bb2)))).
  Proof.
    pose proof ((shift_A__wfAA_ZZ_BB k6)).
    destruct_conjs .
    easy .
  Qed.
  Definition shift_B__wfAA_ZZ_BB : (forall (k6 : Hvl) ,
    (forall (aa2 : AA) (wf : (wfAA k6 aa2)) ,
      (forall (c : (Cutoff B)) (k7 : Hvl) ,
        (shifthvl_B c k6 k7) -> (wfAA k7 (shift_B_AA c aa2)))) /\
    (forall (zz4 : ZZ) (wf : (wfZZ k6 zz4)) ,
      (forall (c : (Cutoff B)) (k7 : Hvl) ,
        (shifthvl_B c k6 k7) -> (wfZZ k7 (shift_B_ZZ c zz4)))) /\
    (forall (bb2 : BB) (wf : (wfBB k6 bb2)) ,
      (forall (c : (Cutoff B)) (k7 : Hvl) ,
        (shifthvl_B c k6 k7) -> (wfBB k7 (shift_B_BB c bb2))))) := (ind_wfAA_ZZ_BB (fun (k6 : Hvl) (aa2 : AA) (wf : (wfAA k6 aa2)) =>
    (forall (c : (Cutoff B)) (k7 : Hvl) ,
      (shifthvl_B c k6 k7) -> (wfAA k7 (shift_B_AA c aa2)))) (fun (k6 : Hvl) (zz4 : ZZ) (wf : (wfZZ k6 zz4)) =>
    (forall (c : (Cutoff B)) (k7 : Hvl) ,
      (shifthvl_B c k6 k7) -> (wfZZ k7 (shift_B_ZZ c zz4)))) (fun (k6 : Hvl) (bb2 : BB) (wf : (wfBB k6 bb2)) =>
    (forall (c : (Cutoff B)) (k7 : Hvl) ,
      (shifthvl_B c k6 k7) -> (wfBB k7 (shift_B_BB c bb2)))) (fun (k6 : Hvl) (a3 : (Index A)) (wfi : (wfindex k6 a3)) (c : (Cutoff B)) (k7 : Hvl) (ins : (shifthvl_B c k6 k7)) =>
    (wfAA_avar k7 _ (shift_B__wfindex_A c k6 k7 ins a3 wfi))) (fun (k6 : Hvl) (zz : ZZ) (wf : (wfZZ k6 zz)) IHzz (c : (Cutoff B)) (k7 : Hvl) (ins : (shifthvl_B c k6 k7)) =>
    (wfAA_arec k7 (IHzz c k7 (weaken_shifthvl_B H0 ins)))) (fun (k6 : Hvl) (z0 : (Index Z)) (wfi : (wfindex k6 z0)) (c : (Cutoff B)) (k7 : Hvl) (ins : (shifthvl_B c k6 k7)) =>
    (wfZZ_zvar k7 _ (shift_B__wfindex_Z c k6 k7 ins z0 wfi))) (fun (k6 : Hvl) (aa : AA) (wf : (wfAA (HS A k6) aa)) IHaa (c : (Cutoff B)) (k7 : Hvl) (ins : (shifthvl_B c k6 k7)) =>
    (wfZZ_aabs k7 (IHaa c (HS A k7) (weaken_shifthvl_B (HS A H0) ins)))) (fun (k6 : Hvl) (bb : BB) (wf : (wfBB (HS B k6) bb)) IHbb (c : (Cutoff B)) (k7 : Hvl) (ins : (shifthvl_B c k6 k7)) =>
    (wfZZ_babs k7 (IHbb (CS c) (HS B k7) (weaken_shifthvl_B (HS B H0) ins)))) (fun (k6 : Hvl) (b3 : (Index B)) (wfi : (wfindex k6 b3)) (c : (Cutoff B)) (k7 : Hvl) (ins : (shifthvl_B c k6 k7)) =>
    (wfBB_bvar k7 _ (shift_B__wfindex_B c k6 k7 ins b3 wfi))) (fun (k6 : Hvl) (zz : ZZ) (wf : (wfZZ k6 zz)) IHzz (c : (Cutoff B)) (k7 : Hvl) (ins : (shifthvl_B c k6 k7)) =>
    (wfBB_brec k7 (IHzz c k7 (weaken_shifthvl_B H0 ins))))).
  Lemma shift_B__wfAA (k6 : Hvl) :
    (forall (aa2 : AA) (wf : (wfAA k6 aa2)) ,
      (forall (c : (Cutoff B)) (k7 : Hvl) ,
        (shifthvl_B c k6 k7) -> (wfAA k7 (shift_B_AA c aa2)))).
  Proof.
    pose proof ((shift_B__wfAA_ZZ_BB k6)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_B__wfZZ (k6 : Hvl) :
    (forall (zz4 : ZZ) (wf0 : (wfZZ k6 zz4)) ,
      (forall (c0 : (Cutoff B)) (k8 : Hvl) ,
        (shifthvl_B c0 k6 k8) -> (wfZZ k8 (shift_B_ZZ c0 zz4)))).
  Proof.
    pose proof ((shift_B__wfAA_ZZ_BB k6)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_B__wfBB (k6 : Hvl) :
    (forall (bb2 : BB) (wf1 : (wfBB k6 bb2)) ,
      (forall (c1 : (Cutoff B)) (k9 : Hvl) ,
        (shifthvl_B c1 k6 k9) -> (wfBB k9 (shift_B_BB c1 bb2)))).
  Proof.
    pose proof ((shift_B__wfAA_ZZ_BB k6)).
    destruct_conjs .
    easy .
  Qed.
  Definition shift_Z__wfAA_ZZ_BB : (forall (k6 : Hvl) ,
    (forall (aa2 : AA) (wf : (wfAA k6 aa2)) ,
      (forall (c : (Cutoff Z)) (k7 : Hvl) ,
        (shifthvl_Z c k6 k7) -> (wfAA k7 (shift_Z_AA c aa2)))) /\
    (forall (zz4 : ZZ) (wf : (wfZZ k6 zz4)) ,
      (forall (c : (Cutoff Z)) (k7 : Hvl) ,
        (shifthvl_Z c k6 k7) -> (wfZZ k7 (shift_Z_ZZ c zz4)))) /\
    (forall (bb2 : BB) (wf : (wfBB k6 bb2)) ,
      (forall (c : (Cutoff Z)) (k7 : Hvl) ,
        (shifthvl_Z c k6 k7) -> (wfBB k7 (shift_Z_BB c bb2))))) := (ind_wfAA_ZZ_BB (fun (k6 : Hvl) (aa2 : AA) (wf : (wfAA k6 aa2)) =>
    (forall (c : (Cutoff Z)) (k7 : Hvl) ,
      (shifthvl_Z c k6 k7) -> (wfAA k7 (shift_Z_AA c aa2)))) (fun (k6 : Hvl) (zz4 : ZZ) (wf : (wfZZ k6 zz4)) =>
    (forall (c : (Cutoff Z)) (k7 : Hvl) ,
      (shifthvl_Z c k6 k7) -> (wfZZ k7 (shift_Z_ZZ c zz4)))) (fun (k6 : Hvl) (bb2 : BB) (wf : (wfBB k6 bb2)) =>
    (forall (c : (Cutoff Z)) (k7 : Hvl) ,
      (shifthvl_Z c k6 k7) -> (wfBB k7 (shift_Z_BB c bb2)))) (fun (k6 : Hvl) (a3 : (Index A)) (wfi : (wfindex k6 a3)) (c : (Cutoff Z)) (k7 : Hvl) (ins : (shifthvl_Z c k6 k7)) =>
    (wfAA_avar k7 _ (shift_Z__wfindex_A c k6 k7 ins a3 wfi))) (fun (k6 : Hvl) (zz : ZZ) (wf : (wfZZ k6 zz)) IHzz (c : (Cutoff Z)) (k7 : Hvl) (ins : (shifthvl_Z c k6 k7)) =>
    (wfAA_arec k7 (IHzz c k7 (weaken_shifthvl_Z H0 ins)))) (fun (k6 : Hvl) (z0 : (Index Z)) (wfi : (wfindex k6 z0)) (c : (Cutoff Z)) (k7 : Hvl) (ins : (shifthvl_Z c k6 k7)) =>
    (wfZZ_zvar k7 _ (shift_Z__wfindex_Z c k6 k7 ins z0 wfi))) (fun (k6 : Hvl) (aa : AA) (wf : (wfAA (HS A k6) aa)) IHaa (c : (Cutoff Z)) (k7 : Hvl) (ins : (shifthvl_Z c k6 k7)) =>
    (wfZZ_aabs k7 (IHaa c (HS A k7) (weaken_shifthvl_Z (HS A H0) ins)))) (fun (k6 : Hvl) (bb : BB) (wf : (wfBB (HS B k6) bb)) IHbb (c : (Cutoff Z)) (k7 : Hvl) (ins : (shifthvl_Z c k6 k7)) =>
    (wfZZ_babs k7 (IHbb c (HS B k7) (weaken_shifthvl_Z (HS B H0) ins)))) (fun (k6 : Hvl) (b3 : (Index B)) (wfi : (wfindex k6 b3)) (c : (Cutoff Z)) (k7 : Hvl) (ins : (shifthvl_Z c k6 k7)) =>
    (wfBB_bvar k7 _ (shift_Z__wfindex_B c k6 k7 ins b3 wfi))) (fun (k6 : Hvl) (zz : ZZ) (wf : (wfZZ k6 zz)) IHzz (c : (Cutoff Z)) (k7 : Hvl) (ins : (shifthvl_Z c k6 k7)) =>
    (wfBB_brec k7 (IHzz c k7 (weaken_shifthvl_Z H0 ins))))).
  Lemma shift_Z__wfAA (k6 : Hvl) :
    (forall (aa2 : AA) (wf : (wfAA k6 aa2)) ,
      (forall (c : (Cutoff Z)) (k7 : Hvl) ,
        (shifthvl_Z c k6 k7) -> (wfAA k7 (shift_Z_AA c aa2)))).
  Proof.
    pose proof ((shift_Z__wfAA_ZZ_BB k6)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_Z__wfZZ (k6 : Hvl) :
    (forall (zz4 : ZZ) (wf0 : (wfZZ k6 zz4)) ,
      (forall (c0 : (Cutoff Z)) (k8 : Hvl) ,
        (shifthvl_Z c0 k6 k8) -> (wfZZ k8 (shift_Z_ZZ c0 zz4)))).
  Proof.
    pose proof ((shift_Z__wfAA_ZZ_BB k6)).
    destruct_conjs .
    easy .
  Qed.
  Lemma shift_Z__wfBB (k6 : Hvl) :
    (forall (bb2 : BB) (wf1 : (wfBB k6 bb2)) ,
      (forall (c1 : (Cutoff Z)) (k9 : Hvl) ,
        (shifthvl_Z c1 k6 k9) -> (wfBB k9 (shift_Z_BB c1 bb2)))).
  Proof.
    pose proof ((shift_Z__wfAA_ZZ_BB k6)).
    destruct_conjs .
    easy .
  Qed.
  Fixpoint weaken_wfAA (k6 : Hvl) {struct k6} :
  (forall (k7 : Hvl) (aa2 : AA) (wf : (wfAA k7 aa2)) ,
    (wfAA (appendHvl k7 k6) (weakenAA aa2 k6))) :=
    match k6 return (forall (k7 : Hvl) (aa2 : AA) (wf : (wfAA k7 aa2)) ,
      (wfAA (appendHvl k7 k6) (weakenAA aa2 k6))) with
      | (H0) => (fun (k7 : Hvl) (aa2 : AA) (wf : (wfAA k7 aa2)) =>
        wf)
      | (HS A k6) => (fun (k7 : Hvl) (aa2 : AA) (wf : (wfAA k7 aa2)) =>
        (shift_A__wfAA (appendHvl k7 k6) (weakenAA aa2 k6) (weaken_wfAA k6 k7 aa2 wf) C0 (HS A (appendHvl k7 k6)) (shifthvl_A_here (appendHvl k7 k6))))
      | (HS B k6) => (fun (k7 : Hvl) (aa2 : AA) (wf : (wfAA k7 aa2)) =>
        (shift_B__wfAA (appendHvl k7 k6) (weakenAA aa2 k6) (weaken_wfAA k6 k7 aa2 wf) C0 (HS B (appendHvl k7 k6)) (shifthvl_B_here (appendHvl k7 k6))))
      | (HS Z k6) => (fun (k7 : Hvl) (aa2 : AA) (wf : (wfAA k7 aa2)) =>
        (shift_Z__wfAA (appendHvl k7 k6) (weakenAA aa2 k6) (weaken_wfAA k6 k7 aa2 wf) C0 (HS Z (appendHvl k7 k6)) (shifthvl_Z_here (appendHvl k7 k6))))
    end.
  Fixpoint weaken_wfZZ (k6 : Hvl) {struct k6} :
  (forall (k7 : Hvl) (zz4 : ZZ) (wf : (wfZZ k7 zz4)) ,
    (wfZZ (appendHvl k7 k6) (weakenZZ zz4 k6))) :=
    match k6 return (forall (k7 : Hvl) (zz4 : ZZ) (wf : (wfZZ k7 zz4)) ,
      (wfZZ (appendHvl k7 k6) (weakenZZ zz4 k6))) with
      | (H0) => (fun (k7 : Hvl) (zz4 : ZZ) (wf : (wfZZ k7 zz4)) =>
        wf)
      | (HS A k6) => (fun (k7 : Hvl) (zz4 : ZZ) (wf : (wfZZ k7 zz4)) =>
        (shift_A__wfZZ (appendHvl k7 k6) (weakenZZ zz4 k6) (weaken_wfZZ k6 k7 zz4 wf) C0 (HS A (appendHvl k7 k6)) (shifthvl_A_here (appendHvl k7 k6))))
      | (HS B k6) => (fun (k7 : Hvl) (zz4 : ZZ) (wf : (wfZZ k7 zz4)) =>
        (shift_B__wfZZ (appendHvl k7 k6) (weakenZZ zz4 k6) (weaken_wfZZ k6 k7 zz4 wf) C0 (HS B (appendHvl k7 k6)) (shifthvl_B_here (appendHvl k7 k6))))
      | (HS Z k6) => (fun (k7 : Hvl) (zz4 : ZZ) (wf : (wfZZ k7 zz4)) =>
        (shift_Z__wfZZ (appendHvl k7 k6) (weakenZZ zz4 k6) (weaken_wfZZ k6 k7 zz4 wf) C0 (HS Z (appendHvl k7 k6)) (shifthvl_Z_here (appendHvl k7 k6))))
    end.
  Fixpoint weaken_wfBB (k6 : Hvl) {struct k6} :
  (forall (k7 : Hvl) (bb2 : BB) (wf : (wfBB k7 bb2)) ,
    (wfBB (appendHvl k7 k6) (weakenBB bb2 k6))) :=
    match k6 return (forall (k7 : Hvl) (bb2 : BB) (wf : (wfBB k7 bb2)) ,
      (wfBB (appendHvl k7 k6) (weakenBB bb2 k6))) with
      | (H0) => (fun (k7 : Hvl) (bb2 : BB) (wf : (wfBB k7 bb2)) =>
        wf)
      | (HS A k6) => (fun (k7 : Hvl) (bb2 : BB) (wf : (wfBB k7 bb2)) =>
        (shift_A__wfBB (appendHvl k7 k6) (weakenBB bb2 k6) (weaken_wfBB k6 k7 bb2 wf) C0 (HS A (appendHvl k7 k6)) (shifthvl_A_here (appendHvl k7 k6))))
      | (HS B k6) => (fun (k7 : Hvl) (bb2 : BB) (wf : (wfBB k7 bb2)) =>
        (shift_B__wfBB (appendHvl k7 k6) (weakenBB bb2 k6) (weaken_wfBB k6 k7 bb2 wf) C0 (HS B (appendHvl k7 k6)) (shifthvl_B_here (appendHvl k7 k6))))
      | (HS Z k6) => (fun (k7 : Hvl) (bb2 : BB) (wf : (wfBB k7 bb2)) =>
        (shift_Z__wfBB (appendHvl k7 k6) (weakenBB bb2 k6) (weaken_wfBB k6 k7 bb2 wf) C0 (HS Z (appendHvl k7 k6)) (shifthvl_Z_here (appendHvl k7 k6))))
    end.
End ShiftWellFormed.
Lemma wfAA_cast  :
  (forall (k6 : Hvl) (aa2 : AA) (k7 : Hvl) (aa3 : AA) ,
    (k6 = k7) -> (aa2 = aa3) -> (wfAA k6 aa2) -> (wfAA k7 aa3)).
Proof.
  congruence .
Qed.
Lemma wfZZ_cast  :
  (forall (k6 : Hvl) (zz4 : ZZ) (k7 : Hvl) (zz5 : ZZ) ,
    (k6 = k7) -> (zz4 = zz5) -> (wfZZ k6 zz4) -> (wfZZ k7 zz5)).
Proof.
  congruence .
Qed.
Lemma wfBB_cast  :
  (forall (k6 : Hvl) (bb2 : BB) (k7 : Hvl) (bb3 : BB) ,
    (k6 = k7) -> (bb2 = bb3) -> (wfBB k6 bb2) -> (wfBB k7 bb3)).
Proof.
  congruence .
Qed.
 Hint Resolve shift_A__wfindex_A shift_A__wfindex_B shift_A__wfindex_Z shift_B__wfindex_A shift_B__wfindex_B shift_B__wfindex_Z shift_Z__wfindex_A shift_Z__wfindex_B shift_Z__wfindex_Z : infra.
 Hint Resolve shift_A__wfindex_A shift_A__wfindex_B shift_A__wfindex_Z shift_B__wfindex_A shift_B__wfindex_B shift_B__wfindex_Z shift_Z__wfindex_A shift_Z__wfindex_B shift_Z__wfindex_Z : shift.
 Hint Resolve shift_A__wfindex_A shift_A__wfindex_B shift_A__wfindex_Z shift_B__wfindex_A shift_B__wfindex_B shift_B__wfindex_Z shift_Z__wfindex_A shift_Z__wfindex_B shift_Z__wfindex_Z : shift_wf.
 Hint Resolve shift_A__wfindex_A shift_A__wfindex_B shift_A__wfindex_Z shift_B__wfindex_A shift_B__wfindex_B shift_B__wfindex_Z shift_Z__wfindex_A shift_Z__wfindex_B shift_Z__wfindex_Z : wf.
 Hint Resolve shift_A__wfAA shift_A__wfBB shift_A__wfZZ shift_B__wfAA shift_B__wfBB shift_B__wfZZ shift_Z__wfAA shift_Z__wfBB shift_Z__wfZZ : infra.
 Hint Resolve shift_A__wfAA shift_A__wfBB shift_A__wfZZ shift_B__wfAA shift_B__wfBB shift_B__wfZZ shift_Z__wfAA shift_Z__wfBB shift_Z__wfZZ : shift.
 Hint Resolve shift_A__wfAA shift_A__wfBB shift_A__wfZZ shift_B__wfAA shift_B__wfBB shift_B__wfZZ shift_Z__wfAA shift_Z__wfBB shift_Z__wfZZ : shift_wf.
 Hint Resolve shift_A__wfAA shift_A__wfBB shift_A__wfZZ shift_B__wfAA shift_B__wfBB shift_B__wfZZ shift_Z__wfAA shift_Z__wfBB shift_Z__wfZZ : wf.
 Hint Constructors shifthvl_A shifthvl_B shifthvl_Z : infra.
 Hint Constructors shifthvl_A shifthvl_B shifthvl_Z : shift.
 Hint Constructors shifthvl_A shifthvl_B shifthvl_Z : shift_wf.
 Hint Constructors shifthvl_A shifthvl_B shifthvl_Z : wf.
 Hint Resolve weaken_shifthvl_A weaken_shifthvl_B weaken_shifthvl_Z : infra.
 Hint Resolve weaken_shifthvl_A weaken_shifthvl_B weaken_shifthvl_Z : shift.
 Hint Resolve weaken_shifthvl_A weaken_shifthvl_B weaken_shifthvl_Z : shift_wf.
 Hint Resolve weaken_shifthvl_A weaken_shifthvl_B weaken_shifthvl_Z : weaken.
 Hint Resolve weaken_shifthvl_A weaken_shifthvl_B weaken_shifthvl_Z : wf.
Section SubstWellFormed.
  Inductive substhvl_A (k6 : Hvl) : (forall (d : (Trace A)) (k7 : Hvl) (k8 : Hvl) ,
    Prop) :=
    | substhvl_A_here :
        (substhvl_A k6 X0 (HS A k6) k6)
    | substhvl_A_there_A
        {d : (Trace A)} {k7 : Hvl}
        {k8 : Hvl} :
        (substhvl_A k6 d k7 k8) -> (substhvl_A k6 (XS A d) (HS A k7) (HS A k8))
    | substhvl_A_there_B
        {d : (Trace A)} {k7 : Hvl}
        {k8 : Hvl} :
        (substhvl_A k6 d k7 k8) -> (substhvl_A k6 (XS B d) (HS B k7) (HS B k8))
    | substhvl_A_there_Z
        {d : (Trace A)} {k7 : Hvl}
        {k8 : Hvl} :
        (substhvl_A k6 d k7 k8) -> (substhvl_A k6 (XS Z d) (HS Z k7) (HS Z k8)).
  Inductive substhvl_B (k6 : Hvl) : (forall (d : (Trace B)) (k7 : Hvl) (k8 : Hvl) ,
    Prop) :=
    | substhvl_B_here :
        (substhvl_B k6 X0 (HS B k6) k6)
    | substhvl_B_there_A
        {d : (Trace B)} {k7 : Hvl}
        {k8 : Hvl} :
        (substhvl_B k6 d k7 k8) -> (substhvl_B k6 (XS A d) (HS A k7) (HS A k8))
    | substhvl_B_there_B
        {d : (Trace B)} {k7 : Hvl}
        {k8 : Hvl} :
        (substhvl_B k6 d k7 k8) -> (substhvl_B k6 (XS B d) (HS B k7) (HS B k8))
    | substhvl_B_there_Z
        {d : (Trace B)} {k7 : Hvl}
        {k8 : Hvl} :
        (substhvl_B k6 d k7 k8) -> (substhvl_B k6 (XS Z d) (HS Z k7) (HS Z k8)).
  Inductive substhvl_Z (k6 : Hvl) : (forall (d : (Trace Z)) (k7 : Hvl) (k8 : Hvl) ,
    Prop) :=
    | substhvl_Z_here :
        (substhvl_Z k6 X0 (HS Z k6) k6)
    | substhvl_Z_there_A
        {d : (Trace Z)} {k7 : Hvl}
        {k8 : Hvl} :
        (substhvl_Z k6 d k7 k8) -> (substhvl_Z k6 (XS A d) (HS A k7) (HS A k8))
    | substhvl_Z_there_B
        {d : (Trace Z)} {k7 : Hvl}
        {k8 : Hvl} :
        (substhvl_Z k6 d k7 k8) -> (substhvl_Z k6 (XS B d) (HS B k7) (HS B k8))
    | substhvl_Z_there_Z
        {d : (Trace Z)} {k7 : Hvl}
        {k8 : Hvl} :
        (substhvl_Z k6 d k7 k8) -> (substhvl_Z k6 (XS Z d) (HS Z k7) (HS Z k8)).
  Lemma weaken_substhvl_A  :
    (forall {k7 : Hvl} (k6 : Hvl) {d : (Trace A)} {k8 : Hvl} {k9 : Hvl} ,
      (substhvl_A k7 d k8 k9) -> (substhvl_A k7 (weakenTrace d k6) (appendHvl k8 k6) (appendHvl k9 k6))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_B  :
    (forall {k7 : Hvl} (k6 : Hvl) {d : (Trace B)} {k8 : Hvl} {k9 : Hvl} ,
      (substhvl_B k7 d k8 k9) -> (substhvl_B k7 (weakenTrace d k6) (appendHvl k8 k6) (appendHvl k9 k6))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma weaken_substhvl_Z  :
    (forall {k7 : Hvl} (k6 : Hvl) {d : (Trace Z)} {k8 : Hvl} {k9 : Hvl} ,
      (substhvl_Z k7 d k8 k9) -> (substhvl_Z k7 (weakenTrace d k6) (appendHvl k8 k6) (appendHvl k9 k6))).
  Proof.
    needleGenericWeakenSubstHvl .
  Qed.
  Lemma substhvl_A_wfindex_A {k6 : Hvl} {aa2 : AA} (wft : (wfAA k6 aa2)) :
    (forall {d : (Trace A)} {k7 : Hvl} {k8 : Hvl} ,
      (substhvl_A k6 d k7 k8) -> (forall {a3 : (Index A)} ,
        (wfindex k7 a3) -> (wfAA k8 (subst_A_Index d aa2 a3)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_B_wfindex_B {k6 : Hvl} {bb2 : BB} (wft : (wfBB k6 bb2)) :
    (forall {d : (Trace B)} {k7 : Hvl} {k8 : Hvl} ,
      (substhvl_B k6 d k7 k8) -> (forall {b3 : (Index B)} ,
        (wfindex k7 b3) -> (wfBB k8 (subst_B_Index d bb2 b3)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_Z_wfindex_Z {k6 : Hvl} {zz4 : ZZ} (wft : (wfZZ k6 zz4)) :
    (forall {d : (Trace Z)} {k7 : Hvl} {k8 : Hvl} ,
      (substhvl_Z k6 d k7 k8) -> (forall {z0 : (Index Z)} ,
        (wfindex k7 z0) -> (wfZZ k8 (subst_Z_Index d zz4 z0)))).
  Proof.
    needleGenericSubstHvlWfIndexHom .
  Qed.
  Lemma substhvl_A_wfindex_B {k6 : Hvl} :
    (forall {d : (Trace A)} {k7 : Hvl} {k8 : Hvl} ,
      (substhvl_A k6 d k7 k8) -> (forall {b3 : (Index B)} ,
        (wfindex k7 b3) -> (wfindex k8 b3))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_A_wfindex_Z {k6 : Hvl} :
    (forall {d : (Trace A)} {k7 : Hvl} {k8 : Hvl} ,
      (substhvl_A k6 d k7 k8) -> (forall {z0 : (Index Z)} ,
        (wfindex k7 z0) -> (wfindex k8 z0))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_B_wfindex_A {k6 : Hvl} :
    (forall {d : (Trace B)} {k7 : Hvl} {k8 : Hvl} ,
      (substhvl_B k6 d k7 k8) -> (forall {a3 : (Index A)} ,
        (wfindex k7 a3) -> (wfindex k8 a3))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_B_wfindex_Z {k6 : Hvl} :
    (forall {d : (Trace B)} {k7 : Hvl} {k8 : Hvl} ,
      (substhvl_B k6 d k7 k8) -> (forall {z0 : (Index Z)} ,
        (wfindex k7 z0) -> (wfindex k8 z0))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_Z_wfindex_A {k6 : Hvl} :
    (forall {d : (Trace Z)} {k7 : Hvl} {k8 : Hvl} ,
      (substhvl_Z k6 d k7 k8) -> (forall {a3 : (Index A)} ,
        (wfindex k7 a3) -> (wfindex k8 a3))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Lemma substhvl_Z_wfindex_B {k6 : Hvl} :
    (forall {d : (Trace Z)} {k7 : Hvl} {k8 : Hvl} ,
      (substhvl_Z k6 d k7 k8) -> (forall {b3 : (Index B)} ,
        (wfindex k7 b3) -> (wfindex k8 b3))).
  Proof.
    needleGenericSubstHvlWfIndexHet .
  Qed.
  Definition substhvl_A_wfAA_ZZ_BB {k6 : Hvl} {aa2 : AA} (wf : (wfAA k6 aa2)) : (forall (k7 : Hvl) ,
    (forall (aa3 : AA) (wf0 : (wfAA k7 aa3)) ,
      (forall {d : (Trace A)} {k8 : Hvl} ,
        (substhvl_A k6 d k7 k8) -> (wfAA k8 (subst_A_AA d aa2 aa3)))) /\
    (forall (zz4 : ZZ) (wf0 : (wfZZ k7 zz4)) ,
      (forall {d : (Trace A)} {k8 : Hvl} ,
        (substhvl_A k6 d k7 k8) -> (wfZZ k8 (subst_A_ZZ d aa2 zz4)))) /\
    (forall (bb2 : BB) (wf0 : (wfBB k7 bb2)) ,
      (forall {d : (Trace A)} {k8 : Hvl} ,
        (substhvl_A k6 d k7 k8) -> (wfBB k8 (subst_A_BB d aa2 bb2))))) := (ind_wfAA_ZZ_BB (fun (k7 : Hvl) (aa3 : AA) (wf0 : (wfAA k7 aa3)) =>
    (forall {d : (Trace A)} {k8 : Hvl} ,
      (substhvl_A k6 d k7 k8) -> (wfAA k8 (subst_A_AA d aa2 aa3)))) (fun (k7 : Hvl) (zz4 : ZZ) (wf0 : (wfZZ k7 zz4)) =>
    (forall {d : (Trace A)} {k8 : Hvl} ,
      (substhvl_A k6 d k7 k8) -> (wfZZ k8 (subst_A_ZZ d aa2 zz4)))) (fun (k7 : Hvl) (bb2 : BB) (wf0 : (wfBB k7 bb2)) =>
    (forall {d : (Trace A)} {k8 : Hvl} ,
      (substhvl_A k6 d k7 k8) -> (wfBB k8 (subst_A_BB d aa2 bb2)))) (fun (k7 : Hvl) {a3 : (Index A)} (wfi : (wfindex k7 a3)) {d : (Trace A)} {k8 : Hvl} (del : (substhvl_A k6 d k7 k8)) =>
    (substhvl_A_wfindex_A wf del wfi)) (fun (k7 : Hvl) (zz : ZZ) (wf0 : (wfZZ k7 zz)) IHzz {d : (Trace A)} {k8 : Hvl} (del : (substhvl_A k6 d k7 k8)) =>
    (wfAA_arec k8 (IHzz (weakenTrace d H0) k8 (weaken_substhvl_A H0 del)))) (fun (k7 : Hvl) {z0 : (Index Z)} (wfi : (wfindex k7 z0)) {d : (Trace A)} {k8 : Hvl} (del : (substhvl_A k6 d k7 k8)) =>
    (wfZZ_zvar k8 _ (substhvl_A_wfindex_Z del wfi))) (fun (k7 : Hvl) (aa : AA) (wf0 : (wfAA (HS A k7) aa)) IHaa {d : (Trace A)} {k8 : Hvl} (del : (substhvl_A k6 d k7 k8)) =>
    (wfZZ_aabs k8 (IHaa (weakenTrace d (HS A H0)) (HS A k8) (weaken_substhvl_A (HS A H0) del)))) (fun (k7 : Hvl) (bb : BB) (wf0 : (wfBB (HS B k7) bb)) IHbb {d : (Trace A)} {k8 : Hvl} (del : (substhvl_A k6 d k7 k8)) =>
    (wfZZ_babs k8 (IHbb (weakenTrace d (HS B H0)) (HS B k8) (weaken_substhvl_A (HS B H0) del)))) (fun (k7 : Hvl) {b3 : (Index B)} (wfi : (wfindex k7 b3)) {d : (Trace A)} {k8 : Hvl} (del : (substhvl_A k6 d k7 k8)) =>
    (wfBB_bvar k8 _ (substhvl_A_wfindex_B del wfi))) (fun (k7 : Hvl) (zz : ZZ) (wf0 : (wfZZ k7 zz)) IHzz {d : (Trace A)} {k8 : Hvl} (del : (substhvl_A k6 d k7 k8)) =>
    (wfBB_brec k8 (IHzz (weakenTrace d H0) k8 (weaken_substhvl_A H0 del))))).
  Lemma substhvl_A_wfAA {k6 : Hvl} {aa2 : AA} (wf : (wfAA k6 aa2)) (k7 : Hvl) (aa3 : AA) (wf0 : (wfAA k7 aa3)) :
    (forall {d : (Trace A)} {k8 : Hvl} ,
      (substhvl_A k6 d k7 k8) -> (wfAA k8 (subst_A_AA d aa2 aa3))).
  Proof.
    apply ((substhvl_A_wfAA_ZZ_BB wf k7)).
    auto .
  Qed.
  Lemma substhvl_A_wfZZ {k6 : Hvl} {aa2 : AA} (wf : (wfAA k6 aa2)) (k7 : Hvl) (zz4 : ZZ) (wf1 : (wfZZ k7 zz4)) :
    (forall {d0 : (Trace A)} {k9 : Hvl} ,
      (substhvl_A k6 d0 k7 k9) -> (wfZZ k9 (subst_A_ZZ d0 aa2 zz4))).
  Proof.
    apply ((substhvl_A_wfAA_ZZ_BB wf k7)).
    auto .
  Qed.
  Lemma substhvl_A_wfBB {k6 : Hvl} {aa2 : AA} (wf : (wfAA k6 aa2)) (k7 : Hvl) (bb2 : BB) (wf2 : (wfBB k7 bb2)) :
    (forall {d1 : (Trace A)} {k10 : Hvl} ,
      (substhvl_A k6 d1 k7 k10) -> (wfBB k10 (subst_A_BB d1 aa2 bb2))).
  Proof.
    apply ((substhvl_A_wfAA_ZZ_BB wf k7)).
    auto .
  Qed.
  Definition substhvl_B_wfAA_ZZ_BB {k6 : Hvl} {bb2 : BB} (wf : (wfBB k6 bb2)) : (forall (k7 : Hvl) ,
    (forall (aa2 : AA) (wf0 : (wfAA k7 aa2)) ,
      (forall {d : (Trace B)} {k8 : Hvl} ,
        (substhvl_B k6 d k7 k8) -> (wfAA k8 (subst_B_AA d bb2 aa2)))) /\
    (forall (zz4 : ZZ) (wf0 : (wfZZ k7 zz4)) ,
      (forall {d : (Trace B)} {k8 : Hvl} ,
        (substhvl_B k6 d k7 k8) -> (wfZZ k8 (subst_B_ZZ d bb2 zz4)))) /\
    (forall (bb3 : BB) (wf0 : (wfBB k7 bb3)) ,
      (forall {d : (Trace B)} {k8 : Hvl} ,
        (substhvl_B k6 d k7 k8) -> (wfBB k8 (subst_B_BB d bb2 bb3))))) := (ind_wfAA_ZZ_BB (fun (k7 : Hvl) (aa2 : AA) (wf0 : (wfAA k7 aa2)) =>
    (forall {d : (Trace B)} {k8 : Hvl} ,
      (substhvl_B k6 d k7 k8) -> (wfAA k8 (subst_B_AA d bb2 aa2)))) (fun (k7 : Hvl) (zz4 : ZZ) (wf0 : (wfZZ k7 zz4)) =>
    (forall {d : (Trace B)} {k8 : Hvl} ,
      (substhvl_B k6 d k7 k8) -> (wfZZ k8 (subst_B_ZZ d bb2 zz4)))) (fun (k7 : Hvl) (bb3 : BB) (wf0 : (wfBB k7 bb3)) =>
    (forall {d : (Trace B)} {k8 : Hvl} ,
      (substhvl_B k6 d k7 k8) -> (wfBB k8 (subst_B_BB d bb2 bb3)))) (fun (k7 : Hvl) {a3 : (Index A)} (wfi : (wfindex k7 a3)) {d : (Trace B)} {k8 : Hvl} (del : (substhvl_B k6 d k7 k8)) =>
    (wfAA_avar k8 _ (substhvl_B_wfindex_A del wfi))) (fun (k7 : Hvl) (zz : ZZ) (wf0 : (wfZZ k7 zz)) IHzz {d : (Trace B)} {k8 : Hvl} (del : (substhvl_B k6 d k7 k8)) =>
    (wfAA_arec k8 (IHzz (weakenTrace d H0) k8 (weaken_substhvl_B H0 del)))) (fun (k7 : Hvl) {z0 : (Index Z)} (wfi : (wfindex k7 z0)) {d : (Trace B)} {k8 : Hvl} (del : (substhvl_B k6 d k7 k8)) =>
    (wfZZ_zvar k8 _ (substhvl_B_wfindex_Z del wfi))) (fun (k7 : Hvl) (aa : AA) (wf0 : (wfAA (HS A k7) aa)) IHaa {d : (Trace B)} {k8 : Hvl} (del : (substhvl_B k6 d k7 k8)) =>
    (wfZZ_aabs k8 (IHaa (weakenTrace d (HS A H0)) (HS A k8) (weaken_substhvl_B (HS A H0) del)))) (fun (k7 : Hvl) (bb : BB) (wf0 : (wfBB (HS B k7) bb)) IHbb {d : (Trace B)} {k8 : Hvl} (del : (substhvl_B k6 d k7 k8)) =>
    (wfZZ_babs k8 (IHbb (weakenTrace d (HS B H0)) (HS B k8) (weaken_substhvl_B (HS B H0) del)))) (fun (k7 : Hvl) {b3 : (Index B)} (wfi : (wfindex k7 b3)) {d : (Trace B)} {k8 : Hvl} (del : (substhvl_B k6 d k7 k8)) =>
    (substhvl_B_wfindex_B wf del wfi)) (fun (k7 : Hvl) (zz : ZZ) (wf0 : (wfZZ k7 zz)) IHzz {d : (Trace B)} {k8 : Hvl} (del : (substhvl_B k6 d k7 k8)) =>
    (wfBB_brec k8 (IHzz (weakenTrace d H0) k8 (weaken_substhvl_B H0 del))))).
  Lemma substhvl_B_wfAA {k6 : Hvl} {bb2 : BB} (wf : (wfBB k6 bb2)) (k7 : Hvl) (aa2 : AA) (wf0 : (wfAA k7 aa2)) :
    (forall {d : (Trace B)} {k8 : Hvl} ,
      (substhvl_B k6 d k7 k8) -> (wfAA k8 (subst_B_AA d bb2 aa2))).
  Proof.
    apply ((substhvl_B_wfAA_ZZ_BB wf k7)).
    auto .
  Qed.
  Lemma substhvl_B_wfZZ {k6 : Hvl} {bb2 : BB} (wf : (wfBB k6 bb2)) (k7 : Hvl) (zz4 : ZZ) (wf1 : (wfZZ k7 zz4)) :
    (forall {d0 : (Trace B)} {k9 : Hvl} ,
      (substhvl_B k6 d0 k7 k9) -> (wfZZ k9 (subst_B_ZZ d0 bb2 zz4))).
  Proof.
    apply ((substhvl_B_wfAA_ZZ_BB wf k7)).
    auto .
  Qed.
  Lemma substhvl_B_wfBB {k6 : Hvl} {bb2 : BB} (wf : (wfBB k6 bb2)) (k7 : Hvl) (bb3 : BB) (wf2 : (wfBB k7 bb3)) :
    (forall {d1 : (Trace B)} {k10 : Hvl} ,
      (substhvl_B k6 d1 k7 k10) -> (wfBB k10 (subst_B_BB d1 bb2 bb3))).
  Proof.
    apply ((substhvl_B_wfAA_ZZ_BB wf k7)).
    auto .
  Qed.
  Definition substhvl_Z_wfAA_ZZ_BB {k6 : Hvl} {zz4 : ZZ} (wf : (wfZZ k6 zz4)) : (forall (k7 : Hvl) ,
    (forall (aa2 : AA) (wf0 : (wfAA k7 aa2)) ,
      (forall {d : (Trace Z)} {k8 : Hvl} ,
        (substhvl_Z k6 d k7 k8) -> (wfAA k8 (subst_Z_AA d zz4 aa2)))) /\
    (forall (zz5 : ZZ) (wf0 : (wfZZ k7 zz5)) ,
      (forall {d : (Trace Z)} {k8 : Hvl} ,
        (substhvl_Z k6 d k7 k8) -> (wfZZ k8 (subst_Z_ZZ d zz4 zz5)))) /\
    (forall (bb2 : BB) (wf0 : (wfBB k7 bb2)) ,
      (forall {d : (Trace Z)} {k8 : Hvl} ,
        (substhvl_Z k6 d k7 k8) -> (wfBB k8 (subst_Z_BB d zz4 bb2))))) := (ind_wfAA_ZZ_BB (fun (k7 : Hvl) (aa2 : AA) (wf0 : (wfAA k7 aa2)) =>
    (forall {d : (Trace Z)} {k8 : Hvl} ,
      (substhvl_Z k6 d k7 k8) -> (wfAA k8 (subst_Z_AA d zz4 aa2)))) (fun (k7 : Hvl) (zz5 : ZZ) (wf0 : (wfZZ k7 zz5)) =>
    (forall {d : (Trace Z)} {k8 : Hvl} ,
      (substhvl_Z k6 d k7 k8) -> (wfZZ k8 (subst_Z_ZZ d zz4 zz5)))) (fun (k7 : Hvl) (bb2 : BB) (wf0 : (wfBB k7 bb2)) =>
    (forall {d : (Trace Z)} {k8 : Hvl} ,
      (substhvl_Z k6 d k7 k8) -> (wfBB k8 (subst_Z_BB d zz4 bb2)))) (fun (k7 : Hvl) {a3 : (Index A)} (wfi : (wfindex k7 a3)) {d : (Trace Z)} {k8 : Hvl} (del : (substhvl_Z k6 d k7 k8)) =>
    (wfAA_avar k8 _ (substhvl_Z_wfindex_A del wfi))) (fun (k7 : Hvl) (zz : ZZ) (wf0 : (wfZZ k7 zz)) IHzz {d : (Trace Z)} {k8 : Hvl} (del : (substhvl_Z k6 d k7 k8)) =>
    (wfAA_arec k8 (IHzz (weakenTrace d H0) k8 (weaken_substhvl_Z H0 del)))) (fun (k7 : Hvl) {z0 : (Index Z)} (wfi : (wfindex k7 z0)) {d : (Trace Z)} {k8 : Hvl} (del : (substhvl_Z k6 d k7 k8)) =>
    (substhvl_Z_wfindex_Z wf del wfi)) (fun (k7 : Hvl) (aa : AA) (wf0 : (wfAA (HS A k7) aa)) IHaa {d : (Trace Z)} {k8 : Hvl} (del : (substhvl_Z k6 d k7 k8)) =>
    (wfZZ_aabs k8 (IHaa (weakenTrace d (HS A H0)) (HS A k8) (weaken_substhvl_Z (HS A H0) del)))) (fun (k7 : Hvl) (bb : BB) (wf0 : (wfBB (HS B k7) bb)) IHbb {d : (Trace Z)} {k8 : Hvl} (del : (substhvl_Z k6 d k7 k8)) =>
    (wfZZ_babs k8 (IHbb (weakenTrace d (HS B H0)) (HS B k8) (weaken_substhvl_Z (HS B H0) del)))) (fun (k7 : Hvl) {b3 : (Index B)} (wfi : (wfindex k7 b3)) {d : (Trace Z)} {k8 : Hvl} (del : (substhvl_Z k6 d k7 k8)) =>
    (wfBB_bvar k8 _ (substhvl_Z_wfindex_B del wfi))) (fun (k7 : Hvl) (zz : ZZ) (wf0 : (wfZZ k7 zz)) IHzz {d : (Trace Z)} {k8 : Hvl} (del : (substhvl_Z k6 d k7 k8)) =>
    (wfBB_brec k8 (IHzz (weakenTrace d H0) k8 (weaken_substhvl_Z H0 del))))).
  Lemma substhvl_Z_wfAA {k6 : Hvl} {zz4 : ZZ} (wf : (wfZZ k6 zz4)) (k7 : Hvl) (aa2 : AA) (wf0 : (wfAA k7 aa2)) :
    (forall {d : (Trace Z)} {k8 : Hvl} ,
      (substhvl_Z k6 d k7 k8) -> (wfAA k8 (subst_Z_AA d zz4 aa2))).
  Proof.
    apply ((substhvl_Z_wfAA_ZZ_BB wf k7)).
    auto .
  Qed.
  Lemma substhvl_Z_wfZZ {k6 : Hvl} {zz4 : ZZ} (wf : (wfZZ k6 zz4)) (k7 : Hvl) (zz5 : ZZ) (wf1 : (wfZZ k7 zz5)) :
    (forall {d0 : (Trace Z)} {k9 : Hvl} ,
      (substhvl_Z k6 d0 k7 k9) -> (wfZZ k9 (subst_Z_ZZ d0 zz4 zz5))).
  Proof.
    apply ((substhvl_Z_wfAA_ZZ_BB wf k7)).
    auto .
  Qed.
  Lemma substhvl_Z_wfBB {k6 : Hvl} {zz4 : ZZ} (wf : (wfZZ k6 zz4)) (k7 : Hvl) (bb2 : BB) (wf2 : (wfBB k7 bb2)) :
    (forall {d1 : (Trace Z)} {k10 : Hvl} ,
      (substhvl_Z k6 d1 k7 k10) -> (wfBB k10 (subst_Z_BB d1 zz4 bb2))).
  Proof.
    apply ((substhvl_Z_wfAA_ZZ_BB wf k7)).
    auto .
  Qed.
End SubstWellFormed.
 Hint Resolve substhvl_A_wfindex_A substhvl_A_wfindex_B substhvl_A_wfindex_Z substhvl_B_wfindex_A substhvl_B_wfindex_B substhvl_B_wfindex_Z substhvl_Z_wfindex_A substhvl_Z_wfindex_B substhvl_Z_wfindex_Z : infra.
 Hint Resolve substhvl_A_wfindex_A substhvl_A_wfindex_B substhvl_A_wfindex_Z substhvl_B_wfindex_A substhvl_B_wfindex_B substhvl_B_wfindex_Z substhvl_Z_wfindex_A substhvl_Z_wfindex_B substhvl_Z_wfindex_Z : subst.
 Hint Resolve substhvl_A_wfindex_A substhvl_A_wfindex_B substhvl_A_wfindex_Z substhvl_B_wfindex_A substhvl_B_wfindex_B substhvl_B_wfindex_Z substhvl_Z_wfindex_A substhvl_Z_wfindex_B substhvl_Z_wfindex_Z : subst_wf.
 Hint Resolve substhvl_A_wfindex_A substhvl_A_wfindex_B substhvl_A_wfindex_Z substhvl_B_wfindex_A substhvl_B_wfindex_B substhvl_B_wfindex_Z substhvl_Z_wfindex_A substhvl_Z_wfindex_B substhvl_Z_wfindex_Z : wf.
 Hint Resolve substhvl_A_wfAA substhvl_A_wfBB substhvl_A_wfZZ substhvl_B_wfAA substhvl_B_wfBB substhvl_B_wfZZ substhvl_Z_wfAA substhvl_Z_wfBB substhvl_Z_wfZZ : infra.
 Hint Resolve substhvl_A_wfAA substhvl_A_wfBB substhvl_A_wfZZ substhvl_B_wfAA substhvl_B_wfBB substhvl_B_wfZZ substhvl_Z_wfAA substhvl_Z_wfBB substhvl_Z_wfZZ : subst.
 Hint Resolve substhvl_A_wfAA substhvl_A_wfBB substhvl_A_wfZZ substhvl_B_wfAA substhvl_B_wfBB substhvl_B_wfZZ substhvl_Z_wfAA substhvl_Z_wfBB substhvl_Z_wfZZ : subst_wf.
 Hint Resolve substhvl_A_wfAA substhvl_A_wfBB substhvl_A_wfZZ substhvl_B_wfAA substhvl_B_wfBB substhvl_B_wfZZ substhvl_Z_wfAA substhvl_Z_wfBB substhvl_Z_wfZZ : wf.
 Hint Constructors substhvl_A substhvl_B substhvl_Z : infra.
 Hint Constructors substhvl_A substhvl_B substhvl_Z : subst.
 Hint Constructors substhvl_A substhvl_B substhvl_Z : subst_wf.
 Hint Constructors substhvl_A substhvl_B substhvl_Z : wf.
Section Context.
  Inductive Env : Type :=
    | empty 
    | ea (G : Env)
    | eb (G : Env).
  Fixpoint appendEnv (G : Env) (G0 : Env) :
  Env :=
    match G0 with
      | (empty) => G
      | (ea G1) => (ea (appendEnv G G1))
      | (eb G1) => (eb (appendEnv G G1))
    end.
  Fixpoint domainEnv (G : Env) :
  Hvl :=
    match G with
      | (empty) => H0
      | (ea G0) => (HS A (domainEnv G0))
      | (eb G0) => (HS B (domainEnv G0))
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
  Fixpoint shift_A_Env (c : (Cutoff A)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (ea G0) => (ea (shift_A_Env c G0))
      | (eb G0) => (eb (shift_A_Env c G0))
    end.
  Fixpoint shift_B_Env (c : (Cutoff B)) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (ea G0) => (ea (shift_B_Env c G0))
      | (eb G0) => (eb (shift_B_Env c G0))
    end.
  Fixpoint weakenEnv (G : Env) (k6 : Hvl) {struct k6} :
  Env :=
    match k6 with
      | (H0) => G
      | (HS A k6) => (weakenEnv G k6)
      | (HS B k6) => (weakenEnv G k6)
      | (HS Z k6) => (weakenEnv G k6)
    end.
  Fixpoint subst_A_Env (d : (Trace A)) (aa2 : AA) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (ea G0) => (ea (subst_A_Env d aa2 G0))
      | (eb G0) => (eb (subst_A_Env d aa2 G0))
    end.
  Fixpoint subst_B_Env (d : (Trace B)) (bb2 : BB) (G : Env) :
  Env :=
    match G with
      | (empty) => empty
      | (ea G0) => (ea (subst_B_Env d bb2 G0))
      | (eb G0) => (eb (subst_B_Env d bb2 G0))
    end.
  Lemma domainEnv_shift_A_Env  :
    (forall (c : (Cutoff A)) (G : Env) ,
      ((domainEnv (shift_A_Env c G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_shift_B_Env  :
    (forall (c : (Cutoff B)) (G : Env) ,
      ((domainEnv (shift_B_Env c G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvShiftEnv .
  Qed.
  Lemma domainEnv_subst_A_Env  :
    (forall (d : (Trace A)) (aa2 : AA) (G : Env) ,
      ((domainEnv (subst_A_Env d aa2 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
  Lemma domainEnv_subst_B_Env  :
    (forall (d : (Trace B)) (bb2 : BB) (G : Env) ,
      ((domainEnv (subst_B_Env d bb2 G)) = (domainEnv G))).
  Proof.
    needleGenericDomainEnvSubstEnv .
  Qed.
End Context.
 Hint Rewrite domainEnv_appendEnv : interaction.
 Hint Rewrite domainEnv_appendEnv : env_domain_append.
Section ContextStuff.
  Section ShiftEnvAppendEnv.
    Lemma shift_A_Env_appendEnv  :
      (forall (c : (Cutoff A)) (G : Env) (G0 : Env) ,
        ((shift_A_Env c (appendEnv G G0)) = (appendEnv (shift_A_Env c G) (shift_A_Env (weakenCutoffA c (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
    Lemma shift_B_Env_appendEnv  :
      (forall (c : (Cutoff B)) (G : Env) (G0 : Env) ,
        ((shift_B_Env c (appendEnv G G0)) = (appendEnv (shift_B_Env c G) (shift_B_Env (weakenCutoffB c (domainEnv G)) G0)))).
    Proof.
      needleGenericShiftEnvAppendEnv .
    Qed.
  End ShiftEnvAppendEnv.
  Section SubstEnvAppendEnv.
    Lemma subst_A_Env_appendEnv  :
      (forall (d : (Trace A)) (aa2 : AA) (G : Env) (G0 : Env) ,
        ((subst_A_Env d aa2 (appendEnv G G0)) = (appendEnv (subst_A_Env d aa2 G) (subst_A_Env (weakenTrace d (domainEnv G)) aa2 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
    Lemma subst_B_Env_appendEnv  :
      (forall (d : (Trace B)) (bb2 : BB) (G : Env) (G0 : Env) ,
        ((subst_B_Env d bb2 (appendEnv G G0)) = (appendEnv (subst_B_Env d bb2 G) (subst_B_Env (weakenTrace d (domainEnv G)) bb2 G0)))).
    Proof.
      needleGenericSubstEnvAppendEnv .
    Qed.
  End SubstEnvAppendEnv.
  Lemma weakenAA_append  :
    (forall (aa2 : AA) (k6 : Hvl) (k7 : Hvl) ,
      ((weakenAA (weakenAA aa2 k6) k7) = (weakenAA aa2 (appendHvl k6 k7)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenZZ_append  :
    (forall (zz4 : ZZ) (k6 : Hvl) (k7 : Hvl) ,
      ((weakenZZ (weakenZZ zz4 k6) k7) = (weakenZZ zz4 (appendHvl k6 k7)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Lemma weakenBB_append  :
    (forall (bb2 : BB) (k6 : Hvl) (k7 : Hvl) ,
      ((weakenBB (weakenBB bb2 k6) k7) = (weakenBB bb2 (appendHvl k6 k7)))).
  Proof.
    needleGenericWeakenAppend .
  Qed.
  Section Lookups.
    Inductive lookup_ea : Env -> (Index A) -> Prop :=
      | lookup_ea_here {G : Env} :
          (lookup_ea (ea G) I0)
      | lookup_ea_there_ea {G : Env}
          {a3 : (Index A)} :
          (lookup_ea G a3) -> (lookup_ea (ea G) (IS a3))
      | lookup_ea_there_eb {G : Env}
          {a3 : (Index A)} :
          (lookup_ea G a3) -> (lookup_ea (eb G) a3).
    Inductive lookup_eb : Env -> (Index B) -> Prop :=
      | lookup_eb_here {G : Env} :
          (lookup_eb (eb G) I0)
      | lookup_eb_there_ea {G : Env}
          {b3 : (Index B)} :
          (lookup_eb G b3) -> (lookup_eb (ea G) b3)
      | lookup_eb_there_eb {G : Env}
          {b3 : (Index B)} :
          (lookup_eb G b3) -> (lookup_eb (eb G) (IS b3)).
    Lemma weaken_lookup_ea  :
      (forall {G : Env} (G0 : Env) {a3 : (Index A)} ,
        (lookup_ea G a3) -> (lookup_ea (appendEnv G G0) (weakenIndexA a3 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma weaken_lookup_eb  :
      (forall {G : Env} (G0 : Env) {b3 : (Index B)} ,
        (lookup_eb G b3) -> (lookup_eb (appendEnv G G0) (weakenIndexB b3 (domainEnv G0)))).
    Proof.
      needleGenericWeakenLookup .
    Qed.
    Lemma lookup_ea_wfindex  :
      (forall {G : Env} {a3 : (Index A)} ,
        (lookup_ea G a3) -> (wfindex (domainEnv G) a3)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
    Lemma lookup_eb_wfindex  :
      (forall {G : Env} {b3 : (Index B)} ,
        (lookup_eb G b3) -> (wfindex (domainEnv G) b3)).
    Proof.
      needleGenericLookupWellformedIndex .
    Qed.
  End Lookups.
  Inductive shift_ea : (Cutoff A) -> Env -> Env -> Prop :=
    | shift_ea_here {G : Env} :
        (shift_ea C0 G (ea G))
    | shiftea_there_ea
        {c : (Cutoff A)} {G : Env}
        {G0 : Env} :
        (shift_ea c G G0) -> (shift_ea (CS c) (ea G) (ea G0))
    | shiftea_there_eb
        {c : (Cutoff A)} {G : Env}
        {G0 : Env} :
        (shift_ea c G G0) -> (shift_ea c (eb G) (eb G0)).
  Lemma weaken_shift_ea  :
    (forall (G : Env) {c : (Cutoff A)} {G0 : Env} {G1 : Env} ,
      (shift_ea c G0 G1) -> (shift_ea (weakenCutoffA c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Inductive shift_eb : (Cutoff B) -> Env -> Env -> Prop :=
    | shift_eb_here {G : Env} :
        (shift_eb C0 G (eb G))
    | shifteb_there_ea
        {c : (Cutoff B)} {G : Env}
        {G0 : Env} :
        (shift_eb c G G0) -> (shift_eb c (ea G) (ea G0))
    | shifteb_there_eb
        {c : (Cutoff B)} {G : Env}
        {G0 : Env} :
        (shift_eb c G G0) -> (shift_eb (CS c) (eb G) (eb G0)).
  Lemma weaken_shift_eb  :
    (forall (G : Env) {c : (Cutoff B)} {G0 : Env} {G1 : Env} ,
      (shift_eb c G0 G1) -> (shift_eb (weakenCutoffB c (domainEnv G)) (appendEnv G0 G) (appendEnv G1 G))).
  Proof.
    needleGenericWeakenInsertEnv .
  Qed.
  Lemma shift_ea_shifthvl_A  :
    (forall {c : (Cutoff A)} {G : Env} {G0 : Env} ,
      (shift_ea c G G0) -> (shifthvl_A c (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Lemma shift_eb_shifthvl_B  :
    (forall {c : (Cutoff B)} {G : Env} {G0 : Env} ,
      (shift_eb c G G0) -> (shifthvl_B c (domainEnv G) (domainEnv G0))).
  Proof.
    needleGenericInsertEnvInsertHvl .
  Qed.
  Inductive subst_ea (G : Env) (aa2 : AA) : (Trace A) -> Env -> Env -> Prop :=
    | subst_ea_here :
        (subst_ea G aa2 X0 (ea G) G)
    | subst_ea_there_ea
        {d : (Trace A)} {G0 : Env}
        {G1 : Env} :
        (subst_ea G aa2 d G0 G1) -> (subst_ea G aa2 (XS A d) (ea G0) (ea G1))
    | subst_ea_there_eb
        {d : (Trace A)} {G0 : Env}
        {G1 : Env} :
        (subst_ea G aa2 d G0 G1) -> (subst_ea G aa2 (XS B d) (eb G0) (eb G1)).
  Lemma weaken_subst_ea {G : Env} {aa2 : AA} :
    (forall (G0 : Env) {d : (Trace A)} {G1 : Env} {G2 : Env} ,
      (subst_ea G aa2 d G1 G2) -> (subst_ea G aa2 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Inductive subst_eb (G : Env) (bb2 : BB) : (Trace B) -> Env -> Env -> Prop :=
    | subst_eb_here :
        (subst_eb G bb2 X0 (eb G) G)
    | subst_eb_there_ea
        {d : (Trace B)} {G0 : Env}
        {G1 : Env} :
        (subst_eb G bb2 d G0 G1) -> (subst_eb G bb2 (XS A d) (ea G0) (ea G1))
    | subst_eb_there_eb
        {d : (Trace B)} {G0 : Env}
        {G1 : Env} :
        (subst_eb G bb2 d G0 G1) -> (subst_eb G bb2 (XS B d) (eb G0) (eb G1)).
  Lemma weaken_subst_eb {G : Env} {bb2 : BB} :
    (forall (G0 : Env) {d : (Trace B)} {G1 : Env} {G2 : Env} ,
      (subst_eb G bb2 d G1 G2) -> (subst_eb G bb2 (weakenTrace d (domainEnv G0)) (appendEnv G1 G0) (appendEnv G2 G0))).
  Proof.
    needleGenericWeakenSubstEnv .
  Qed.
  Lemma subst_ea_substhvl_A {G : Env} {aa2 : AA} :
    (forall {d : (Trace A)} {G0 : Env} {G1 : Env} ,
      (subst_ea G aa2 d G0 G1) -> (substhvl_A (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
  Lemma subst_eb_substhvl_B {G : Env} {bb2 : BB} :
    (forall {d : (Trace B)} {G0 : Env} {G1 : Env} ,
      (subst_eb G bb2 d G0 G1) -> (substhvl_B (domainEnv G) d (domainEnv G0) (domainEnv G1))).
  Proof.
    needleGenericSubstEnvSubstHvl .
  Qed.
End ContextStuff.
 Hint Constructors lookup_ea lookup_eb : infra.
 Hint Constructors lookup_ea lookup_eb : lookup.
 Hint Constructors lookup_ea lookup_eb : shift.
 Hint Constructors lookup_ea lookup_eb : subst.
 Hint Resolve weaken_lookup_ea weaken_lookup_eb : infra.
 Hint Resolve weaken_lookup_ea weaken_lookup_eb : lookup.
 Hint Resolve weaken_lookup_ea weaken_lookup_eb : shift.
 Hint Resolve weaken_lookup_ea weaken_lookup_eb : weaken.
Lemma weaken_lookup_ea_here  :
  (forall {G : Env} (G0 : Env) ,
    (lookup_ea (appendEnv (ea G) G0) (weakenIndexA I0 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
Lemma weaken_lookup_eb_here  :
  (forall {G : Env} (G0 : Env) ,
    (lookup_eb (appendEnv (eb G) G0) (weakenIndexB I0 (domainEnv G0)))).
Proof.
  eauto with lookup .
Qed.
 Hint Constructors wfAA wfBB wfZZ : infra.
 Hint Constructors wfAA wfBB wfZZ : wf.
 Hint Extern 10 ((wfAA _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfBB _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 10 ((wfZZ _ _)) => autorewrite with env_domain_append in *  : infra wf.
 Hint Extern 2 ((wfAA _ _)) => match goal with
  | H15 : (wfAA _ (avar _)) |- _ => inversion H15; subst; clear H15
  | H15 : (wfAA _ (arec _)) |- _ => inversion H15; subst; clear H15
end : infra wf.
 Hint Extern 2 ((wfZZ _ _)) => match goal with
  | H15 : (wfZZ _ (zvar _)) |- _ => inversion H15; subst; clear H15
  | H15 : (wfZZ _ (aabs _)) |- _ => inversion H15; subst; clear H15
  | H15 : (wfZZ _ (babs _)) |- _ => inversion H15; subst; clear H15
end : infra wf.
 Hint Extern 2 ((wfBB _ _)) => match goal with
  | H15 : (wfBB _ (bvar _)) |- _ => inversion H15; subst; clear H15
  | H15 : (wfBB _ (brec _)) |- _ => inversion H15; subst; clear H15
end : infra wf.
 Hint Resolve lookup_ea_wfindex lookup_eb_wfindex : infra.
 Hint Resolve lookup_ea_wfindex lookup_eb_wfindex : lookup.
 Hint Resolve lookup_ea_wfindex lookup_eb_wfindex : wf.
 Hint Constructors shift_ea shift_eb : infra.
 Hint Constructors shift_ea shift_eb : shift.
 Hint Constructors shift_ea shift_eb : subst.
 Hint Resolve weaken_shift_ea weaken_shift_eb : infra.
 Hint Resolve weaken_shift_ea weaken_shift_eb : shift.
 Hint Resolve shift_ea_shifthvl_A shift_eb_shifthvl_B : infra.
 Hint Resolve shift_ea_shifthvl_A shift_eb_shifthvl_B : shift.
 Hint Resolve shift_ea_shifthvl_A shift_eb_shifthvl_B : shift_wf.
 Hint Resolve shift_ea_shifthvl_A shift_eb_shifthvl_B : wf.
 Hint Constructors subst_ea subst_eb : infra.
 Hint Constructors subst_ea subst_eb : subst.
 Hint Resolve weaken_subst_ea weaken_subst_eb : infra.
 Hint Resolve weaken_subst_ea weaken_subst_eb : subst.
 Hint Resolve subst_ea_substhvl_A subst_eb_substhvl_B : infra.
 Hint Resolve subst_ea_substhvl_A subst_eb_substhvl_B : subst.
 Hint Resolve subst_ea_substhvl_A subst_eb_substhvl_B : subst_wf.
 Hint Resolve subst_ea_substhvl_A subst_eb_substhvl_B : wf.
 Hint Resolve subst_ea_substhvl_A subst_eb_substhvl_B : substenv_substhvl.
Lemma shift_ea_lookup_ea  :
  (forall {c : (Cutoff A)} {G : Env} {G0 : Env} (ins : (shift_ea c G G0)) {a3 : (Index A)} ,
    (lookup_ea G a3) -> (lookup_ea G0 (shift_A_Index c a3))).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_ea_lookup_eb  :
  (forall {c : (Cutoff A)} {G : Env} {G0 : Env} (ins : (shift_ea c G G0)) {b3 : (Index B)} ,
    (lookup_eb G b3) -> (lookup_eb G0 b3)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_eb_lookup_ea  :
  (forall {c : (Cutoff B)} {G : Env} {G0 : Env} (ins : (shift_eb c G G0)) {a3 : (Index A)} ,
    (lookup_ea G a3) -> (lookup_ea G0 a3)).
Proof.
  needleGenericInsertLookup .
Qed.
Lemma shift_eb_lookup_eb  :
  (forall {c : (Cutoff B)} {G : Env} {G0 : Env} (ins : (shift_eb c G G0)) {b3 : (Index B)} ,
    (lookup_eb G b3) -> (lookup_eb G0 (shift_B_Index c b3))).
Proof.
  needleGenericInsertLookup .
Qed.
 Hint Resolve shift_ea_lookup_ea shift_ea_lookup_eb shift_eb_lookup_ea shift_eb_lookup_eb : infra.
 Hint Resolve shift_ea_lookup_ea shift_ea_lookup_eb shift_eb_lookup_ea shift_eb_lookup_eb : lookup.
 Hint Resolve shift_ea_lookup_ea shift_ea_lookup_eb shift_eb_lookup_ea shift_eb_lookup_eb : shift.
Lemma subst_ea_lookup_eb {G : Env} {aa2 : AA} :
  (forall {d : (Trace A)} {G0 : Env} {G1 : Env} (sub : (subst_ea G aa2 d G0 G1)) {b3 : (Index B)} ,
    (lookup_eb G0 b3) -> (lookup_eb G1 b3)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
Lemma subst_eb_lookup_ea {G : Env} {bb2 : BB} :
  (forall {d : (Trace B)} {G0 : Env} {G1 : Env} (sub : (subst_eb G bb2 d G0 G1)) {a3 : (Index A)} ,
    (lookup_ea G0 a3) -> (lookup_ea G1 a3)).
Proof.
  needleGenericSubstEnvLookup .
Qed.
 Hint Resolve subst_ea_lookup_eb subst_eb_lookup_ea : infra.
 Hint Resolve subst_ea_lookup_eb subst_eb_lookup_ea : lookup.
 Hint Resolve subst_ea_lookup_eb subst_eb_lookup_ea : subst.
Fixpoint size_AA (aa0 : AA) {struct aa0} :
nat :=
  match aa0 with
    | (avar a3) => 1
    | (arec zz1) => (plus 1 (size_ZZ zz1))
  end
with size_ZZ (zz1 : ZZ) {struct zz1} :
nat :=
  match zz1 with
    | (zvar z0) => 1
    | (aabs aa0) => (plus 1 (size_AA aa0))
    | (babs bb0) => (plus 1 (size_BB bb0))
  end
with size_BB (bb0 : BB) {struct bb0} :
nat :=
  match bb0 with
    | (bvar b3) => 1
    | (brec zz1) => (plus 1 (size_ZZ zz1))
  end.
Fixpoint shift_A__size_AA (aa0 : AA) (c : (Cutoff A)) {struct aa0} :
((size_AA (shift_A_AA c aa0)) = (size_AA aa0)) :=
  match aa0 return ((size_AA (shift_A_AA c aa0)) = (size_AA aa0)) with
    | (avar _) => eq_refl
    | (arec zz) => (f_equal2 plus eq_refl (shift_A__size_ZZ zz c))
  end
with shift_A__size_ZZ (zz1 : ZZ) (c : (Cutoff A)) {struct zz1} :
((size_ZZ (shift_A_ZZ c zz1)) = (size_ZZ zz1)) :=
  match zz1 return ((size_ZZ (shift_A_ZZ c zz1)) = (size_ZZ zz1)) with
    | (zvar _) => eq_refl
    | (aabs aa) => (f_equal2 plus eq_refl (shift_A__size_AA aa (CS c)))
    | (babs bb) => (f_equal2 plus eq_refl (shift_A__size_BB bb c))
  end
with shift_A__size_BB (bb0 : BB) (c : (Cutoff A)) {struct bb0} :
((size_BB (shift_A_BB c bb0)) = (size_BB bb0)) :=
  match bb0 return ((size_BB (shift_A_BB c bb0)) = (size_BB bb0)) with
    | (bvar _) => eq_refl
    | (brec zz) => (f_equal2 plus eq_refl (shift_A__size_ZZ zz c))
  end.
Fixpoint shift_B__size_AA (aa0 : AA) (c : (Cutoff B)) {struct aa0} :
((size_AA (shift_B_AA c aa0)) = (size_AA aa0)) :=
  match aa0 return ((size_AA (shift_B_AA c aa0)) = (size_AA aa0)) with
    | (avar _) => eq_refl
    | (arec zz) => (f_equal2 plus eq_refl (shift_B__size_ZZ zz c))
  end
with shift_B__size_ZZ (zz1 : ZZ) (c : (Cutoff B)) {struct zz1} :
((size_ZZ (shift_B_ZZ c zz1)) = (size_ZZ zz1)) :=
  match zz1 return ((size_ZZ (shift_B_ZZ c zz1)) = (size_ZZ zz1)) with
    | (zvar _) => eq_refl
    | (aabs aa) => (f_equal2 plus eq_refl (shift_B__size_AA aa c))
    | (babs bb) => (f_equal2 plus eq_refl (shift_B__size_BB bb (CS c)))
  end
with shift_B__size_BB (bb0 : BB) (c : (Cutoff B)) {struct bb0} :
((size_BB (shift_B_BB c bb0)) = (size_BB bb0)) :=
  match bb0 return ((size_BB (shift_B_BB c bb0)) = (size_BB bb0)) with
    | (bvar _) => eq_refl
    | (brec zz) => (f_equal2 plus eq_refl (shift_B__size_ZZ zz c))
  end.
Fixpoint shift_Z__size_AA (aa0 : AA) (c : (Cutoff Z)) {struct aa0} :
((size_AA (shift_Z_AA c aa0)) = (size_AA aa0)) :=
  match aa0 return ((size_AA (shift_Z_AA c aa0)) = (size_AA aa0)) with
    | (avar _) => eq_refl
    | (arec zz) => (f_equal2 plus eq_refl (shift_Z__size_ZZ zz c))
  end
with shift_Z__size_ZZ (zz1 : ZZ) (c : (Cutoff Z)) {struct zz1} :
((size_ZZ (shift_Z_ZZ c zz1)) = (size_ZZ zz1)) :=
  match zz1 return ((size_ZZ (shift_Z_ZZ c zz1)) = (size_ZZ zz1)) with
    | (zvar _) => eq_refl
    | (aabs aa) => (f_equal2 plus eq_refl (shift_Z__size_AA aa c))
    | (babs bb) => (f_equal2 plus eq_refl (shift_Z__size_BB bb c))
  end
with shift_Z__size_BB (bb0 : BB) (c : (Cutoff Z)) {struct bb0} :
((size_BB (shift_Z_BB c bb0)) = (size_BB bb0)) :=
  match bb0 return ((size_BB (shift_Z_BB c bb0)) = (size_BB bb0)) with
    | (bvar _) => eq_refl
    | (brec zz) => (f_equal2 plus eq_refl (shift_Z__size_ZZ zz c))
  end.
 Hint Rewrite shift_A__size_AA shift_B__size_AA shift_Z__size_AA shift_A__size_BB shift_B__size_BB shift_Z__size_BB shift_A__size_ZZ shift_B__size_ZZ shift_Z__size_ZZ : interaction.
 Hint Rewrite shift_A__size_AA shift_B__size_AA shift_Z__size_AA shift_A__size_BB shift_B__size_BB shift_Z__size_BB shift_A__size_ZZ shift_B__size_ZZ shift_Z__size_ZZ : shift_size.
Lemma weaken_size_AA  :
  (forall (k : Hvl) (aa0 : AA) ,
    ((size_AA (weakenAA aa0 k)) = (size_AA aa0))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_BB  :
  (forall (k : Hvl) (bb0 : BB) ,
    ((size_BB (weakenBB bb0 k)) = (size_BB bb0))).
Proof.
  needleGenericWeakenSize .
Qed.
Lemma weaken_size_ZZ  :
  (forall (k : Hvl) (zz1 : ZZ) ,
    ((size_ZZ (weakenZZ zz1 k)) = (size_ZZ zz1))).
Proof.
  needleGenericWeakenSize .
Qed.
 Hint Rewrite weaken_size_AA weaken_size_BB weaken_size_ZZ : interaction.
 Hint Rewrite weaken_size_AA weaken_size_BB weaken_size_ZZ : weaken_size.
 Hint Rewrite appendEnv_assoc : interaction.
 Hint Rewrite <- weakenCutoffA_append weakenCutoffB_append weakenCutoffZ_append weakenTrace_append weakenAA_append weakenBB_append weakenZZ_append appendHvl_assoc : interaction.