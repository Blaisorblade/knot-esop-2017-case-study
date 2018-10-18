Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.
Require Import Coq.Unicode.Utf8.
Set Implicit Arguments.

(******************************************************************************)
(* Representation of types.                                                   *)
(******************************************************************************)

Inductive Ty : Set :=
  | tvar (X : nat)
  | top
  | tarrow (T1 T2 : Ty)
  | tall (T1 : Ty) (T2 : Ty).

(******************************************************************************)
(* Representation of terms.                                                   *)
(******************************************************************************)

Inductive Tm : Set :=
  | var  (x  : nat)
  | abs  (T  : Ty) (t  : Tm)
  | app  (t1 : Tm) (t2 : Tm)
  | tabs (T  : Ty) (t  : Tm)
  | tapp (t  : Tm) (T  : Ty).


(******************************************************************************)
(* Representation of contexts.                                                *)
(******************************************************************************)

Inductive Env : Set :=
  | empty
  | evar   (G : Env) (T : Ty)
  | ebound (G : Env) (T : Ty).

Fixpoint append (Γ1 Γ2 : Env) : Env :=
  match Γ2 with
    | empty       => Γ1
    | evar   Γ2 T => evar (append Γ1 Γ2) T
    | ebound Γ2 T => ebound (append Γ1 Γ2) T
  end.

(******************************************************************************)
(* Shifting                                                                   *)
(******************************************************************************)

Fixpoint shiftNat (c : nat) (i : nat) : nat :=
  match c with
    | O   => S i
    | S c =>
      match i with
        | O   => O
        | S i => S (shiftNat c i)
      end
  end.

Fixpoint tshiftTy (c : nat) (T : Ty) : Ty :=
  match T with
    | tvar X       => tvar (shiftNat c X)
    | top          => top
    | tarrow T1 T2 => tarrow (tshiftTy c T1) (tshiftTy c T2)
    | tall T1 T2   => tall (tshiftTy c T1) (tshiftTy (S c) T2)
  end.

Fixpoint tshiftTm (c : nat) (t : Tm) : Tm :=
  match t with
  | var x        => var x
  | abs T1 t2    => abs (tshiftTy c T1) (tshiftTm c t2)
  | app t1 t2    => app (tshiftTm c t1) (tshiftTm c t2)
  | tabs T1 t2   => tabs (tshiftTy c T1) (tshiftTm (S c) t2)
  | tapp t1 T2   => tapp (tshiftTm c t1) (tshiftTy c T2)
  end.

Fixpoint shiftTm (c : nat) (t : Tm) : Tm :=
  match t with
  | var x        => var (shiftNat c x)
  | abs T1 t2    => abs T1 (shiftTm (S c) t2)
  | app t1 t2    => app (shiftTm c t1) (shiftTm c t2)
  | tabs T1 t2   => tabs T1 (shiftTm c t2)
  | tapp t1 T2   => tapp (shiftTm c t1) T2
  end.

Fixpoint weakenTm (t : Tm) (k : nat) : Tm :=
  match k with
    | O   => t
    | S k => shiftTm O (weakenTm t k)
  end.

(******************************************************************************)
(* Type substitution.                                                         *)
(******************************************************************************)

Fixpoint tsubstNat (X : nat) (T' : Ty) (Y : nat) : Ty :=
  match X , Y with
    | O   , O   => T'
    | O   , S Y => tvar Y
    | S X , O   => tvar O
    | S X , S Y => tshiftTy 0 (tsubstNat X T' Y)
  end.

Fixpoint tsubstTy (X : nat) (T' : Ty) (T : Ty) : Ty :=
  match T with
    | tvar Y       => tsubstNat X T' Y
    | top          => top
    | tarrow T1 T2 => tarrow (tsubstTy X T' T1) (tsubstTy X T' T2)
    | tall T1 T2   => tall (tsubstTy X T' T1) (tsubstTy (S X) T' T2)
  end.

Fixpoint tsubstTm (X : nat) (T' : Ty) (t : Tm) : Tm :=
  match t with
  | var x        => var x
  | abs T1 t2    => abs  (tsubstTy X T' T1) (tsubstTm X T' t2)
  | app t1 t2    => app  (tsubstTm X T' t1) (tsubstTm X T' t2)
  | tabs T1 t2   => tabs (tsubstTy X T' T1) (tsubstTm (S X) T' t2)
  | tapp t1 T2   => tapp (tsubstTm X T' t1) (tsubstTy X T' T2)
  end.

(******************************************************************************)
(* Term substitutions.                                                        *)
(******************************************************************************)

Inductive Subst : Set :=
  | sub_here  : Subst
  | sub_var   : Subst -> Subst
  | sub_bound : Subst -> Subst.

Fixpoint weakenSubst (sub : Subst) (k : nat) : Subst :=
  match k with
   | O   => sub
   | S k => sub_var (weakenSubst sub k)
  end.

Fixpoint substNat (x : Subst) (t : Tm) (y : nat) : Tm :=
  match x , y with
    | sub_here    , O   => t
    | sub_here    , S y => var y
    | sub_var x   , O   => var O
    | sub_var x   , S y => shiftTm O (substNat x t y)
    | sub_bound x , y   => tshiftTm O (substNat x t y)
  end.

Fixpoint substTm (x : Subst) (t' : Tm) (t : Tm) : Tm :=
  match t with
    | var y        => substNat x t' y
    | abs T1 t2    => abs T1 (substTm (sub_var x) t' t2)
    | app t1 t2    => app (substTm x t' t1) (substTm x t' t2)
    | tabs T1 t2   => tabs T1 (substTm (sub_bound x) t' t2)
    | tapp t1 T2   => tapp (substTm x t' t1) T2
  end.

(******************************************************************************)
(* Context lookups.                                                           *)
(******************************************************************************)

Inductive GetBound : Env -> nat -> Ty -> Prop :=
  | gb_here
      {Γ : Env} {T} :
      GetBound (ebound Γ T) O (tshiftTy O T)
  | gb_var
      {Γ : Env} {T T' X} :
      GetBound Γ X T ->
      GetBound (evar Γ T') X T
  | gb_bound
      {Γ : Env} {T T' X} :
      GetBound Γ X T ->
      GetBound (ebound Γ T') (S X) (tshiftTy O T).

Inductive GetVar : Env -> nat -> Ty -> Prop :=
  | gv_here
      {Γ : Env} {T} :
      GetVar (evar Γ T) O T
  | gv_var
      {Γ : Env} {T T' X} :
      GetVar Γ X T ->
      GetVar (evar Γ T') (S X) T
  | gv_bound
      {Γ : Env} {T T' X} :
      GetVar Γ X T ->
      GetVar (ebound Γ T') X (tshiftTy O T).

(******************************************************************************)
(* Context lookups.                                                           *)
(******************************************************************************)

Lemma getbound_functional {Γ : Env} {X} {S T} :
  GetBound Γ X S → GetBound Γ X T → S = T.
Proof.
  intros gbS gbT; revert S gbS.
  induction gbT; intros; dependent destruction gbS; simpl; f_equal; auto.
Qed.

Lemma getvar_functional {Γ : Env} {X} {S T} :
  GetVar Γ X S → GetVar Γ X T → S = T.
Proof.
  intros gvS gvT; revert S gvS.
  induction gvT; intros; dependent destruction gvS; simpl; f_equal; auto.
Qed.

(******************************************************************************)
(* Size induction                                                             *)
(******************************************************************************)

Fixpoint size (T : Ty) : nat :=
  match T with
  | tvar _       => 0
  | top          => 0
  | tarrow T1 T2 => 1 + size T1 + size T2
  | tall T1 T2   => 1 + size T1 + size T2
  end.

Lemma Ty_sizeind
  (P : Ty -> Prop)
  (f : forall (T : Ty), (forall (S : Ty), size S < size T -> P S) -> P T)
  : forall (T : Ty), P T.
Proof.
  assert (H : forall (n : nat) (T1 : Ty), size T1 < n -> P T1).
  induction n; intros.
  assert False; omega.
  case (le_lt_or_eq _ _ H).
  intro H'; apply IHn; omega; auto.
  intro E; inversion E; clear E; subst; auto.
  intros T; apply (H (S (size T))); omega.
Qed.

(******************************************************************************)
(* Lemmas.                                                                    *)
(******************************************************************************)

Lemma tshift_preserves_size T : ∀ c, size (tshiftTy c T) = size T.
Proof.
  induction T; trivial; simpl; intros; rewrite IHT1; rewrite IHT2; trivial.
Qed.

Ltac specialize_suc :=
  progress
    match goal with
      | [ H : forall _ : nat, _, k : nat |- _ ] => apply (H (S k))
    end.
Ltac var_case :=
  match goal with
    | [ |- forall v i, _ ] =>
      induction v; simpl; intros; destruct i; auto;
      try apply (f_equal (tshiftTy O)) with (y := tvar _); auto
  end.
Ltac ty_case T v :=
  induction T; simpl; intros;
  try solve [ try apply f_equal with (f := tvar); apply v
            | trivial
            | apply f_equal2 with (f := tarrow); trivial
            | apply f_equal2 with (f := tall); try specialize_suc; trivial
            ].

Lemma shiftNat_comm_ind :
  forall v i c,
    shiftNat (v + S c) (shiftNat (v + O) i) =
    shiftNat (v + O  ) (shiftNat (v + c) i).
Proof.
  var_case.
Qed.

Lemma tshiftTy_comm_ind (T : Ty) :
  forall v c,
    tshiftTy (v + S c) (tshiftTy (v + O) T) =
    tshiftTy (v + O  ) (tshiftTy (v + c) T).
Proof.
  ty_case T shiftNat_comm_ind.
Qed.

Lemma tshiftTy_comm (c : nat) (T : Ty) :
    tshiftTy (S c) (tshiftTy O T)
  = tshiftTy O     (tshiftTy c T).
Proof.
  apply (tshiftTy_comm_ind _ 0).
Qed.

Lemma tsubstNat_shiftNat_reflection_ind :
  forall (k X : nat) (T : Ty),
    tsubstNat (k + 0) T (shiftNat (k + O) X) = tvar X.
Proof.
  var_case.
Qed.

Lemma tsubstTy_tshiftTy_reflection_ind (T : Ty) :
  forall k T',
    tsubstTy (k + 0) T' (tshiftTy (k + O) T) = T.
Proof.
  ty_case T tsubstNat_shiftNat_reflection_ind.
Qed.

Lemma tsubstTy_tshiftTy_reflection (T' T : Ty) :
  tsubstTy 0 T' (tshiftTy O T) = T.
Proof.
  apply (tsubstTy_tshiftTy_reflection_ind _ 0).
Qed.

Lemma tshiftTy_tsubstNat_comm_ind :
  forall (k X c : nat) (T : Ty),
    tshiftTy (k + c) (tsubstNat (k + 0) T X) =
    tsubstNat (k + 0) (tshiftTy c T) (shiftNat (k + S c) X).
Proof.
  var_case.
  rewrite tshiftTy_comm; f_equal; auto.
Qed.

Lemma tshiftTy_tsubstTy_comm_ind (T : Ty):
  forall (k c : nat) (T' : Ty),
    tshiftTy (k + c) (tsubstTy (k + 0) T' T) =
    tsubstTy (k + 0) (tshiftTy c T') (tshiftTy (k + S c) T).
Proof.
  ty_case T tshiftTy_tsubstNat_comm_ind.
Qed.

Lemma tshiftTy_tsubstTy_comm c (T T2 : Ty) :
    tshiftTy c (tsubstTy O T T2)
  = tsubstTy O (tshiftTy c T) (tshiftTy (S c) T2).
Proof.
  apply (tshiftTy_tsubstTy_comm_ind _ 0).
Qed.

Lemma tsubstNat_shiftNat_comm_ind :
  forall k Y X T',
    tsubstNat (k + S X) T' (shiftNat (k + 0) Y) =
    tshiftTy (k + 0) (tsubstNat (k + X) T' Y).
Proof.
  var_case.
  rewrite tshiftTy_comm; f_equal; auto.
Qed.

Lemma tsubstTy_tshiftTy_comm_ind (T : Ty) :
  forall k X T',
    tsubstTy (k + S X) T' (tshiftTy (k + 0) T) =
    tshiftTy (k + 0) (tsubstTy (k + X) T' T).
Proof.
  ty_case T tsubstNat_shiftNat_comm_ind.
Qed.

Lemma tsubstTy_tshiftTy_comm :
  forall X T' T,
    tsubstTy (S X) T' (tshiftTy 0 T) =
    tshiftTy 0 (tsubstTy X T' T).
Proof.
  intros; apply (tsubstTy_tshiftTy_comm_ind _ 0).
Qed.

Lemma tsubstTy_tsubstNat_comm_ind :
  forall k Y T1 T2 X,
    tsubstTy (k + X) T1 (tsubstNat (k + 0) T2 Y) =
    tsubstTy (k + 0) (tsubstTy X T1 T2) (tsubstNat (k + S X) T1 Y).
Proof.
  var_case.
  rewrite tsubstTy_tshiftTy_reflection; auto.
  repeat rewrite tsubstTy_tshiftTy_comm; f_equal; auto.
Qed.

Lemma tsubstTy_tsubstTy_comm_ind (T : Ty) :
  forall k X T1 T2,
    tsubstTy (k + X) T1 (tsubstTy (k + 0) T2 T) =
    tsubstTy (k + 0) (tsubstTy X T1 T2) (tsubstTy (k + (S X)) T1 T).
Proof.
  ty_case T tsubstTy_tsubstNat_comm_ind.
Qed.

Lemma tsubstTy_tsubstTy_comm :
  forall X T1 T2 T,
    tsubstTy X T1 (tsubstTy 0 T2 T) =
    tsubstTy 0 (tsubstTy X T1 T2) (tsubstTy (S X) T1 T).
Proof.
  intros; apply (tsubstTy_tsubstTy_comm_ind _ 0).
Qed.

(******************************************************************************)
(* Interaction between term substitutions and typevar shifting.               *)
(******************************************************************************)

Lemma shiftTm_tshiftTm_comm (t : Tm) :
  ∀ ca cb,
    shiftTm  cb (tshiftTm ca t) =
    tshiftTm ca (shiftTm  cb t).
Proof.
  induction t; simpl; intros; f_equal; trivial.
Qed.

(******************************************************************************)
(* Context insertions.                                                        *)
(******************************************************************************)

Inductive InsertBound : nat → Env → Env → Prop :=
  | ib_here
      {Γ : Env} {T} :
      InsertBound O Γ (ebound Γ T)
  | ib_var
      {Γ1 : Env} {Γ2 : Env} {c T} :
      InsertBound c Γ1 Γ2 →
      InsertBound c (evar Γ1 T) (evar Γ2 (tshiftTy c T))
  | ib_bound
      {Γ1 : Env} {Γ2 : Env} {c T} :
      InsertBound c Γ1 Γ2 →
      InsertBound (S c) (ebound Γ1 T) (ebound Γ2 (tshiftTy c T)).

Inductive InsertVar : nat → Env → Env → Prop :=
  | iv_here
      {Γ : Env} {T} :
      InsertVar O Γ (evar Γ T)
  | iv_var
      {Γ1 : Env} {Γ2 : Env} {c T} :
      InsertVar c Γ1 Γ2 →
      InsertVar (S c) (evar Γ1 T) (evar Γ2 T)
  | iv_bound
      {Γ1 : Env} {Γ2 : Env} {c T} :
      InsertVar c Γ1 Γ2 →
      InsertVar c (ebound Γ1 T) (ebound Γ2 T).

(******************************************************************************)
(* Lemmas about shifting and context lookups.                                 *)
(******************************************************************************)

Lemma shift_bound_getbound {Γ1 Γ2 c} (ib : InsertBound c Γ1 Γ2) :
  ∀ X T, GetBound Γ1 X T →
         GetBound Γ2 (shiftNat c X) (tshiftTy c T).
Proof.
  induction ib; intros; dependent destruction H; simpl;
    try rewrite tshiftTy_comm; repeat constructor; auto.
Qed.

Lemma shift_bound_getvar {Γ1 Γ2 c} (ib : InsertBound c Γ1 Γ2) :
  ∀ x T, GetVar Γ1 x T →
         GetVar Γ2 x (tshiftTy c T).
Proof.
  induction ib; intros; dependent destruction H; simpl;
    try rewrite tshiftTy_comm; repeat constructor; auto.
Qed.

Lemma shift_var_getbound {Γ1 Γ2 c} (iv : InsertVar c Γ1 Γ2) :
  ∀ X T, GetBound Γ1 X T → GetBound Γ2 X T.
Proof.
  induction iv; intros; dependent destruction H; simpl;
    repeat constructor; auto.
Qed.

Lemma shift_var_getvar {Γ1 Γ2 c} (iv : InsertVar c Γ1 Γ2) :
  ∀ x T, GetVar Γ1 x T → GetVar Γ2 (shiftNat c x) T.
Proof.
  induction iv; intros; dependent destruction H; simpl;
    repeat constructor; auto.
Qed.

(******************************************************************************)
(* Subtyping relation                                                         *)
(******************************************************************************)

Inductive Sub : Env -> Ty -> Ty -> Prop :=
  | SA_Top {G : Env} {S} :
      Sub G S top
  | SA_Refl_TVar {G : Env} {X} :
      Sub G (tvar X) (tvar X)
  | SA_Trans_TVar {G : Env} {X T U} :
      GetBound G X U -> Sub G U T ->
      Sub G (tvar X) T
  | SA_Arrow {G : Env} {T1 T2 S1 S2} :
      Sub G T1 S1 -> Sub G S2 T2 ->
      Sub G (tarrow S1 S2) (tarrow T1 T2)
  | SA_All {G : Env} {T1 T2 S1 S2} :
      Sub G T1 S1 -> Sub (ebound G T1) S2 T2 ->
      Sub G (tall S1 S2) (tall T1 T2).

(******************************************************************************)
(* Weakening lemmas for subtyping.                                            *)
(******************************************************************************)

Lemma shift_bound_sub {c Γ1 Γ2 U V} :
  InsertBound c Γ1 Γ2 → Sub Γ1 U V → Sub Γ2 (tshiftTy c U) (tshiftTy c V).
Proof.
  intros ib sub; revert c Γ2 ib.
  induction sub; simpl; intros.
  apply SA_Top.
  apply SA_Refl_TVar.
  apply SA_Trans_TVar with (2 := IHsub c Γ2 ib).
  apply (shift_bound_getbound ib H).
  apply SA_Arrow; auto.
  apply SA_All; auto.
  apply (IHsub2 (S c) _ (ib_bound ib)).
Qed.

Lemma weakening_bound_sub {Γ : Env} {T U V} :
  Sub Γ U V → Sub (ebound Γ T) (tshiftTy O U) (tshiftTy O V).
Proof.
  apply (shift_bound_sub ib_here).
Qed.

Lemma shift_var_sub {c Γ1 Γ2 U V} :
  InsertVar c Γ1 Γ2 → Sub Γ1 U V → Sub Γ2 U V.
Proof.
  intros iv sub; revert c Γ2 iv.
  induction sub; simpl; intros.
  apply SA_Top.
  apply SA_Refl_TVar.
  apply SA_Trans_TVar with (2 := IHsub c Γ2 iv).
  apply (shift_var_getbound iv H).
  apply SA_Arrow; eauto.
  apply SA_All; eauto.
  apply (IHsub2 c _ (iv_bound iv)).
Qed.

Lemma weakening_var_sub {Γ : Env} {T U V} :
  Sub Γ U V → Sub (evar Γ T) U V.
Proof.
  apply (shift_var_sub iv_here).
Qed.

Lemma reflexivity_sub (T : Ty) : forall {G}, Sub G T T.
Proof.
  induction T; intros; constructor; auto.
Qed.

Inductive Narrow : nat -> Env -> Env -> Prop :=
  | nw_here {G T1 T2} :
      Sub G T2 T1 ->
      Narrow O (ebound G T1) (ebound G T2)
  | nw_var {X G1 G2 T} :
      Narrow X G1 G2 ->
      Narrow X (evar G1 T) (evar G2 T)
  | nw_bound {X G1 G2 T} :
      Narrow X G1 G2 ->
      Narrow (S X) (ebound G1 T) (ebound G2 T).

Lemma narrow_getbound_ne {X G1 G2} (nw : Narrow X G1 G2) :
  forall {T1 Y} (gb1 : GetBound G1 Y T1) (neq : Y <> X), GetBound G2 Y T1.
Proof.
  induction nw; intros; dependent destruction gb1;
    try (constructor; auto); try (apply IHnw); congruence.
Qed.

Lemma narrow_getbound_eq {X G1 G2} (nw : Narrow X G1 G2) :
  exists T1 T2, GetBound G1 X T1 /\ GetBound G2 X T2 /\ Sub G2 T2 T1.
Proof.
  induction nw; intros.
  - exists (tshiftTy O T1),(tshiftTy O T2); repeat constructor.
    apply weakening_bound_sub; auto.
  - destruct IHnw as [T1 [T2 [gb1 [gb2 sub]]]].
    exists T1, T2; repeat constructor; auto.
    apply weakening_var_sub; auto.
  - destruct IHnw as [T1 [T2 [gb1 [gb2 sub]]]].
    exists (tshiftTy O T1),(tshiftTy O T2); repeat constructor; auto.
    apply weakening_bound_sub; auto.
Qed.

Lemma narrow_getvar {X G1 G2} (nw : Narrow X G1 G2) :
  forall {T x}, GetVar G1 x T -> GetVar G2 x T.
Proof.
  induction nw; intros T' x gv; dependent destruction gv;
    try constructor; auto.
Qed.

Definition Transitivity (Q : Ty) :=
  forall G S T, Sub G S Q -> Sub G Q T -> Sub G S T.

Definition Narrowing (Q : Ty) :=
  forall G1 G2 X S T,
    Narrow X G1 G2 -> GetBound G1 X Q -> Sub G1 S T -> Sub G2 S T.

Lemma transitivity_case (Q : Ty)
  (hypT : forall (Q' : Ty), size Q' < size Q -> Transitivity Q')
  (hypN : forall (Q' : Ty), size Q' < size Q -> Narrowing Q') :
  Transitivity Q.
Proof.
  intros G S T subSQ subQT.
  induction subSQ; intros; try assumption.
  - dependent destruction subQT; constructor.
  - apply (SA_Trans_TVar H); auto.
  - dependent destruction subQT; constructor.
    + apply (hypT T1); simpl; try omega; auto.
    + apply (hypT T2); simpl; try omega; auto.
  - dependent destruction subQT; constructor.
    + apply (hypT T1); auto; simpl; omega.
    + apply (hypT T2); auto; simpl; try omega.
      apply (hypN (tshiftTy 0 T1)) with (2 := nw_here subQT1); auto.
      rewrite tshift_preserves_size; simpl; omega.
      constructor.
Qed.

Lemma narrowing_case (Q : Ty)
  (hypT : forall (Q' : Ty), size Q' = size Q -> Transitivity Q') :
  Narrowing Q.
Proof.
  intros G1 G2 X T1 T2 nrwX gbX subUT; revert Q hypT G2 X nrwX gbX.
  induction subUT; intros Q hypT G2 Y nrwY gbY.
  - apply SA_Top.
  - apply SA_Refl_TVar.
  - case (eq_nat_dec X Y); intros; subst.
    + pose proof (getbound_functional gbY H); subst.
      apply (hypT U); eauto.
      destruct (narrow_getbound_eq nrwY) as [T1 [T2 [gb1 [gb2 sub]]]].
      pose proof (getbound_functional H gb1); subst.
      apply (SA_Trans_TVar gb2 sub); eauto.
    + apply (SA_Trans_TVar (U := U)); eauto.
      apply (narrow_getbound_ne nrwY); trivial.
  - apply SA_Arrow; eauto.
  - apply SA_All; eauto.
    eapply IHsubUT2; try econstructor; eauto.
    intros Q' eq; apply hypT; rewrite eq; apply tshift_preserves_size.
Qed.

Lemma transitivity_and_narrowing :
  forall (Q : Ty), Transitivity Q /\ Narrowing Q.
Proof.
  apply Ty_sizeind; intros; split.
  apply transitivity_case; apply H; auto.
  apply narrowing_case; intros Q' eq.
  apply transitivity_case; rewrite eq; apply H; auto.
Qed.

Lemma sub_transitivity (G : Env) (T U V : Ty) :
  Sub G T U -> Sub G U V -> Sub G T V.
Proof.
  apply (transitivity_and_narrowing).
Qed.

Lemma narrow_sub (G1 G2 : Env) (X : nat) (S T : Ty) :
  Narrow X G1 G2 -> Sub G1 S T -> Sub G2 S T.
Proof.
  intros nrwX sub.
  destruct (narrow_getbound_eq nrwX) as (Q, (P, (gbX, _))).
  apply (proj2 (transitivity_and_narrowing Q)) with (1:=nrwX); auto.
Qed.


(******************************************************************************)
(* Typing relation.                                                           *)
(******************************************************************************)

Inductive Typing : Env -> Tm -> Ty -> Prop :=
  | T_Var {G x T} :
      GetVar G x T -> Typing G (var x) T
  | T_Abs {G t T1 T2} :
      Typing (evar G T1) t T2 ->
      Typing G (abs T1 t) (tarrow T1 T2)
  | T_App {G t1 t2 T11 T12} :
      Typing G t1 (tarrow T11 T12) -> Typing G t2 T11 ->
      Typing G (app t1 t2) T12
  | T_Tabs {G t T1 T2} :
      Typing (ebound G T1) t T2 ->
      Typing G (tabs T1 t) (tall T1 T2)
  | T_Tapp {G t1 T11 T12 T2} :
      Typing G t1 (tall T11 T12) -> Sub G T2 T11 ->
      Typing G (tapp t1 T2) (tsubstTy O T2 T12)
  | T_Sub {G t T1 T2} :
      Typing G t T1 -> Sub G T1 T2 ->
      Typing G t T2.


(******************************************************************************)
(* Weakening lemmas for typing.                                               *)
(******************************************************************************)

Lemma shift_bound_typing {Γ1 : Env} {Γ2 : Env} {c t T} :
  InsertBound c Γ1 Γ2 → Typing Γ1 t T → Typing Γ2 (tshiftTm c t) (tshiftTy c T).
Proof.
  intros ib wt; revert c Γ2 ib.
  induction wt; simpl; intros.
  apply (T_Var (shift_bound_getvar ib H)).
  apply (T_Abs (IHwt _ _ (ib_var ib))).
  apply (T_App (IHwt1 _ _ ib) (IHwt2 _ _ ib)).
  apply (T_Tabs (IHwt _ _ (ib_bound ib))).
  rewrite tshiftTy_tsubstTy_comm.
  apply (T_Tapp (IHwt _ _ ib) (shift_bound_sub ib H)).
  apply (T_Sub (IHwt _ _ ib) (shift_bound_sub ib H)).
Qed.

Lemma shift_var_typing {Γ1 Γ2 : Env} {c t T} :
  InsertVar c Γ1 Γ2 → Typing Γ1 t T → Typing Γ2 (shiftTm c t) T.
Proof.
  intros iv wt; revert c Γ2 iv.
  induction wt; simpl; intros.
  apply (T_Var (shift_var_getvar iv H)).
  apply (T_Abs (IHwt _ _ (iv_var iv))).
  apply (T_App (IHwt1 _ _ iv) (IHwt2 _ _ iv)).
  apply (T_Tabs (IHwt _ _ (iv_bound iv))).
  apply (T_Tapp (IHwt _ _ iv) (shift_var_sub iv H)).
  apply (T_Sub (IHwt _ _ iv) (shift_var_sub iv H)).
Qed.

Lemma weakening_bound_typing {Γ : Env} {t T T'} :
  Typing Γ t T → Typing (ebound Γ T') (tshiftTm O t) (tshiftTy O T).
Proof.
  apply (shift_bound_typing ib_here).
Qed.

Lemma weakening_var_typing {Γ : Env} {t T T'} :
  Typing Γ t T → Typing (evar Γ T') (shiftTm O t) T.
Proof.
  apply (shift_var_typing iv_here).
Qed.

(******************************************************************************)
(* Typing substitution.                                                       *)
(******************************************************************************)

Inductive SubstTyping : Subst → Tm → Env → Env → Prop :=
  | se_here
      {Γ : Env} {t T} :
      Typing Γ t T →
      SubstTyping sub_here t (evar Γ T) Γ
  | se_var
      {Γ1 Γ2 : Env} {T T'} {x} :
      SubstTyping x T' Γ1 Γ2 →
      SubstTyping (sub_var x) T' (evar Γ1 T) (evar Γ2 T)
  | se_bound
      {Γ1 Γ2 : Env} {x} {T' T} :
      SubstTyping x T' Γ1 Γ2 →
      SubstTyping (sub_bound x) T' (ebound Γ1 T) (ebound Γ2 T).

Lemma subst_getvar {Γ1 Γ2 : Env} {x T' y T} :
  SubstTyping x T' Γ1 Γ2 → GetVar Γ1 y T → Typing Γ2 (substNat x T' y) T.
Proof.
  intros esub gv; revert Γ2 x esub.
  induction gv; intros; dependent destruction esub; simpl.
  exact H.
  apply (T_Var gv_here).
  apply (T_Var gv).
  apply (weakening_var_typing (IHgv _ _ esub)).
  apply (weakening_bound_typing (IHgv _ _ esub)).
Qed.


(******************************************************************************)
(* Subtyping substitution.                                                    *)
(******************************************************************************)

Inductive SubstSubtyping : nat → Ty -> Env → Env → Prop :=
  | tse_here
      {Γ : Env} {S T} :
      Sub Γ S T →
      SubstSubtyping 0 S (ebound Γ T) Γ
  | tse_var
      {Γ1 : Env} {Γ2 : Env} {T' T} {X} :
      SubstSubtyping X T' Γ1 Γ2 →
      SubstSubtyping X T' (evar Γ1 T) (evar Γ2 (tsubstTy X T' T))
  | tse_bound
      {Γ1 : Env} {Γ2 : Env} {X T' T} :
      SubstSubtyping X T' Γ1 Γ2 →
      SubstSubtyping (S X) T' (ebound Γ1 T) (ebound Γ2 (tsubstTy X T' T)).

Lemma substsubtyping_getbound {Γ1 Γ2 : Env} {X T' Y U} :
  SubstSubtyping X T' Γ1 Γ2 → GetBound Γ1 Y U →
  Sub Γ2 (tsubstNat X T' Y) (tsubstTy X T' U).
Proof.
  intros esub gb; revert Y U gb.
  induction esub; intros.
  dependent destruction gb; simpl.
  rewrite tsubstTy_tshiftTy_reflection.
  trivial.
  rewrite tsubstTy_tshiftTy_reflection.
  apply (SA_Trans_TVar gb).
  apply reflexivity_sub.
  apply weakening_var_sub.
  apply IHesub.
  dependent destruction gb; auto.
  dependent destruction gb; simpl.
  rewrite tsubstTy_tshiftTy_comm.
  apply (SA_Trans_TVar gb_here).
  apply reflexivity_sub.
  rewrite tsubstTy_tshiftTy_comm.
  apply weakening_bound_sub.
  apply IHesub; auto.
Qed.

Lemma substsubtyping_preserves_subtyping {Γ1 Γ2 : Env} {X T' U V} :
  SubstSubtyping X T' Γ1 Γ2 → Sub Γ1 U V →
  Sub Γ2 (tsubstTy X T' U) (tsubstTy X T' V).
Proof.
  intros esub st; revert Γ2 X T' esub.
  induction st; simpl; intros.
  apply SA_Top.
  apply reflexivity_sub.
  apply (sub_transitivity (U := tsubstTy X0 T' U)).
  apply (substsubtyping_getbound esub H).
  apply IHst; trivial.
  apply SA_Arrow.
  apply IHst1; trivial.
  apply IHst2; trivial.
  apply SA_All.
  apply IHst1; trivial.
  apply IHst2 with (1 := tse_bound esub).
Qed.

Lemma tsubst_getvar
  {Γ1 : Env} {Γ2 : Env} {X x T' T} :
  SubstSubtyping X T' Γ1 Γ2 → GetVar Γ1 x T →
  GetVar Γ2 x (tsubstTy X T' T).
Proof.
  intros sube gv; revert x T gv.
  induction sube; intros; dependent destruction gv; simpl;
    try rewrite tsubstTy_tshiftTy_reflection;
    try rewrite tsubstTy_tshiftTy_comm;
    try constructor; auto.
Qed.

(******************************************************************************)
(* Preservation lemmas.                                                       *)
(******************************************************************************)

Lemma substtyping_getbound {Γ1 Γ2 : Env} {x t' Y T} :
  SubstTyping x t' Γ1 Γ2 → GetBound Γ1 Y T → GetBound Γ2 Y T.
Proof.
  intros sube gv; revert Y T gv.
  induction sube; intros; dependent destruction gv; simpl;
    try constructor; auto.
Qed.

Lemma substtyping_preserves_subtyping_ind {Γ1 Γ2 : Env} {X T' T1 T2} :
  SubstTyping X T' Γ1 Γ2 → Sub Γ1 T1 T2 → Sub Γ2 T1 T2.
Proof.
  intros esub st; revert Γ2 X T' esub.
  induction st; simpl; intros.
  apply SA_Top.
  apply SA_Refl_TVar.
  apply (SA_Trans_TVar (substtyping_getbound esub H) (IHst _ _ _ esub)).
  apply (SA_Arrow (IHst1 _ _ _ esub) (IHst2 _ _ _ esub)).
  apply (SA_All (IHst1 _ _ _ esub)).
  apply (IHst2 _ _ _ (se_bound esub)).
Qed.

Lemma substtyping_preserves_subtyping {Γ : Env} {s S T1 T2} :
  Typing Γ s S → Sub (evar Γ S) T1 T2 → Sub Γ T1 T2.
Proof.
  intros wt; apply (substtyping_preserves_subtyping_ind (se_here wt)).
Qed.

Lemma substtyping_preserves_typing_ind {Γ1 Γ2 : Env} {X T' t T} :
  SubstTyping X T' Γ1 Γ2 → Typing Γ1 t T → Typing Γ2 (substTm X T' t) T.
Proof.
  intros esub wt; revert Γ2 X T' esub.
  induction wt; simpl; intros.
  apply (subst_getvar esub); auto.
  apply (T_Abs (IHwt _ _ _ (se_var esub))).
  apply (T_App (IHwt1 _ _ _ esub) (IHwt2 _ _ _ esub)).
  apply (T_Tabs (IHwt _ _ _ (se_bound esub))).
  apply (T_Tapp (IHwt _ _ _ esub) (substtyping_preserves_subtyping_ind esub H)).
  apply (T_Sub (IHwt _ _ _ esub) (substtyping_preserves_subtyping_ind esub H)).
Qed.

Lemma substtyping_preserves_typing {Γ : Env} {s S t T} :
  Typing Γ s S → Typing (evar Γ S) t T → Typing Γ (substTm sub_here s t) T.
Proof.
  intros wt_s; apply (substtyping_preserves_typing_ind (se_here wt_s)).
Qed.

Lemma substsubtyping_preserves_typing {Γ1 Γ2 : Env} {X T' t T} :
  SubstSubtyping X T' Γ1 Γ2 → Typing Γ1 t T →
  Typing Γ2 (tsubstTm X T' t) (tsubstTy X T' T).
Proof.
  intros esub wt; revert Γ2 X T' esub.
  induction wt; simpl; intros.
  apply (T_Var (tsubst_getvar esub H)).
  apply (T_Abs (IHwt _ _ _ (tse_var esub))).
  apply (T_App (IHwt1 _ _ _ esub) (IHwt2 _ _ _ esub)).
  apply (T_Tabs (IHwt _ _ _ (tse_bound esub))).
  rewrite tsubstTy_tsubstTy_comm.
  apply (T_Tapp (IHwt _ _ _ esub) (substsubtyping_preserves_subtyping esub H)).
  apply (T_Sub (IHwt _ _ _ esub) (substsubtyping_preserves_subtyping esub H)).
Qed.

Fixpoint Value (t : Tm) : Prop :=
  match t with
  | abs _ _  => True
  | tabs _ _ => True
  | _        => False
  end.

(*************************************************************************)
(*                      Alternate reduction relation                     *)
(*************************************************************************)

Inductive red' : Tm -> Tm -> Prop :=
  | appabs {T11 t12 t2} :
        Value t2 -> red' (app (abs T11 t12) t2) (substTm sub_here t2 t12)
  | tapptabs {T11 T2 t12} :
        red' (tapp (tabs T11 t12) T2) (tsubstTm 0 T2 t12)
  | appfun {t1 t1' t2} :
        red' t1 t1' -> red' (app t1 t2) (app t1' t2)
  | apparg {t1 t2 t2'} :
        Value t1 -> red' t2 t2' -> red' (app t1 t2) (app t1 t2')
  | typefun {t1 t1' T2} :
      red' t1 t1' -> red' (tapp t1 T2) (tapp t1' T2).

Lemma narrow_typing_ind {X} {G1 G2 : Env} (nw : Narrow X G1 G2) :
  forall {t T}, Typing G1 t T -> Typing G2 t T.
Proof.
  intros t T wt; revert X G2 nw; induction wt; simpl; intros.
  apply (T_Var (narrow_getvar nw H)).
  apply (T_Abs (IHwt _ _ (nw_var nw))).
  apply (T_App (IHwt1 _ _ nw) (IHwt2 _ _ nw)).
  apply (T_Tabs (IHwt _ _ (nw_bound nw))).
  apply (T_Tapp (IHwt _ _ nw) (narrow_sub nw H)).
  apply (T_Sub (IHwt _ _ nw) (narrow_sub nw H)).
Qed.

Lemma narrow_typing {G : Env} {t T S1 S2} :
  Sub G S2 S1 -> Typing (ebound G S1) t T -> Typing (ebound G S2) t T.
Proof.
  intros sub; apply narrow_typing_ind with (1:=nw_here sub).
Qed.

Lemma t_abs_inversion {G t T0 T1 T2 T3} :
  Typing G (abs T1 t) T0 -> Sub G T0 (tarrow T2 T3) ->
  exists T4, Sub G T2 T1 /\ Sub G T4 T3 /\ Typing (evar G T1) t T4.
Proof.
  intros wt; dependent induction wt; intro st.
  exists T0; dependent destruction st; auto.
  apply IHwt; apply (sub_transitivity H st).
Qed.

Lemma t_tabs_inversion {G : Env} {t T0 T1 T2 T3} :
  Typing G (tabs T1 t) T0 -> Sub G T0 (tall T2 T3) ->
  exists T4, Sub G T2 T1 /\ Sub (ebound G T2) T4 T3 /\ Typing (ebound G T2) t T4.
Proof.
  intros wt; revert T2 T3; dependent induction wt; intros.
  dependent destruction H; exists T2; repeat split; auto.
  apply narrow_typing with (2 := wt); auto.
  apply IHwt; apply (sub_transitivity H H0).
Qed.

Lemma fun_value {t : Tm} {T1 T2} :
  Value t -> Typing empty t (tarrow T1 T2) ->
  exists t' T1', t = abs T1' t'.
Proof.
  intros vt wt; dependent induction wt; try contradiction.
  exists t, T1; reflexivity.
  dependent destruction H.
  dependent destruction H.
  apply (IHwt S1 S2 vt); auto.
Qed.

Lemma typefun_value {t : Tm} {T1 T2} :
  Value t -> Typing empty t (tall T1 T2) ->
  exists t' T1', t = tabs T1' t'.
Proof.
  intros vt wt; dependent induction wt; try contradiction.
  exists t, T1; reflexivity.
  dependent destruction H.
  dependent destruction H.
  apply (IHwt S1 S2 vt); auto.
Qed.

Lemma value_not_var_type {G : Env} {t : Tm} {X : nat} :
  Typing G t (tvar X) -> Value t -> False.
Proof.
  intros wt; dependent induction wt; auto.
  dependent induction H; eauto.
Qed.

Lemma progress' {t : Tm} {U : Ty} :
  Typing empty t U -> Value t \/ exists t', red' t t'.
Proof.
  intros wt; dependent induction wt; simpl; auto; right.
  - inversion H.
  - destruct IHwt1 as [vt1|[t1' r1]].
    + destruct IHwt2 as [vt2|[t2' r2]].
      * destruct (fun_value vt1 wt1) as [t' [T1' eq_t1]]; subst.
        exists (substTm sub_here t2 t'); constructor; auto.
      * exists (app t1 t2'); constructor; auto.
    + exists (app t1' t2); constructor; auto.
  - destruct IHwt as [vt|[t1' r1]].
    + destruct (typefun_value vt wt) as [t' [T1' eq_t1]]; subst.
      exists (tsubstTm 0 T2 t'); constructor; auto.
    + exists (tapp t1' T2); constructor; auto.
Qed.

Lemma preservation' {G : Env} {t t' : Tm} {U : Ty} :
  Typing G t U -> red' t t' -> Typing G t' U.
Proof.
  intros wt; revert t'; induction wt; intros.
  - dependent destruction H0.
  - dependent destruction H.
  - dependent destruction H.
    + destruct (t_abs_inversion wt1 (reflexivity_sub (tarrow T11 T12)))
        as (T4, (subT11, (subT4, wt12))).
      apply T_Sub with (2 := subT4).
      apply substtyping_preserves_typing with (2 := wt12).
      apply T_Sub with (2 := subT11); auto.
    + apply T_App with (1 := IHwt1 _ H); trivial.
    + apply T_App with (2 := IHwt2 _ H0); trivial.
  - inversion H.
  - dependent destruction H0.
    destruct (t_tabs_inversion wt (reflexivity_sub _))
      as (H2, (T3, (H4, H5))).
    apply (substsubtyping_preserves_typing (tse_here H) (T_Sub H5 H4)).
    apply T_Tapp with (1 := IHwt _ H0); trivial.
  - apply T_Sub with (2 := H); auto.
Qed.
