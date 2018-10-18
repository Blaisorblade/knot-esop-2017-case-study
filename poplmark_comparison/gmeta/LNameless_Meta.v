Set Implicit Arguments.

Require Import Max.
Require Import Equality.
Require Import Eqdep_dec.
Require Import Variable_Sets.

Require Export DGP_Core.
Require Export Metatheory_Env.

(** Reference: #<a href="http://www.chargueraud.org/arthur/research/2007/binders/">#Aydemir et. al. 2007#</a># *)


(**********************************************************************)
(** * Importing Dgp for the locally nameless approach *)
(**********************************************************************)

Module Export LNameless := Dgp TwoNat Single.

(** [TwoNat] stands for the disjoint union of free variables (using inl)
   and bound variables (using inr).

   [Single] is a unit type and denotes the empty place holder
   for binding variables which are not written directly
   in de Bruijn style representation for abstraction. *)

(** Note that [atom] = [nat]. *)

(**********************************************************************)
(** * 1. Generic Definitions *)
(**********************************************************************)

(**********************************************************************)
(** ** Heterogeneous Substitution *)
(**********************************************************************)

(** The following definition deals with heterogeneous substitution;
   - [r0] is the representation of the variables to be substituted.
   
   - [Var] case: only the case [r = r0] is interesting.

   - [Bind] case: Note that, when [r1 = REC], [r0] is compared with [r]
     because [REC] denotes the representation of the abstraction
     body [r].

   - Note that the argument [r0] is the crucial point
     for the heterogeneous definition. *)

(** Substitution for parameters *)

Fixpoint fsubstRep r r0 s (T:InterpretRep r s)(a:atom)(U:Interpret r0) : InterpretRep r s :=
  match T with
    | Unit           => Unit 
    | Const _ T0     => Const r T0
    | Repr _ T0      => Repr r (fsubst T0 a U)
    | InL _ _ T0     => InL _ (fsubstRep T0 a U) 
    | InR _ _ T0     => InR _ (fsubstRep T0 a U)
    | Pair _ _ T0 T1 => Pair (fsubstRep T0 a U) (fsubstRep T1 a U)
    | Bind r1 _ _ T0 => Bind r1 tt (fsubstRep T0 a U)
    | Rec T0         => Rec (fsubst T0 a U)
  end
with fsubst r r0 (T:Interpret r)(a:atom)(U:Interpret r0) : Interpret r :=
  match T with
    | Var v  => 
      match Rep_dec r r0 with 
        | left same => 
          match v with
            | inl b => if (AtomDT.eq_dec a b) then conv same U else T
            | inr _ => T
          end
        | right _ => T
      end
    | Term T0 => Term (fsubstRep T0 a U)
  end.

(** Substitution for (bound) variables *)

(*
Fixpoint bsubstRep r r0 s (T:InterpretRep r s)(m:atom)(U:Interpret r0) : InterpretRep r s :=
  match T with
    | Unit            => Unit 
    | Const _ T0      => Const r T0
    | Repr _ T0       => Repr r (bsubst T0 m U)
    | InL _ _ T0      => InL _ (bsubstRep T0 m U) 
    | InR _ _ T0      => InR _ (bsubstRep T0 m U)
    | Pair _ _ T0 T1  => Pair (bsubstRep T0 m U) (bsubstRep T1 m U)
    | Bind r1 _ _ T0  =>
      match Rep_dec (if Rep_dec r1 REC then r else r1) r0 with
        | left _ => Bind r1 tt (bsubstRep T0 (S m) U)
        | _      => Bind r1 tt (bsubstRep T0 m U)
      end

    | Rec T0          => Rec (bsubst T0 m U)
  end

with bsubst r r0 (T:Interpret r)(m:atom)(U:Interpret r0) : Interpret r :=
  match T with
    | Var v  => 
      match Rep_dec r r0 with 
        | left same => 
          match v with
            | inl _ => T
            | inr k => if (AtomDT.eq_dec m k) then conv same U else T
          end
        | right _ => T
      end
    | Term T0 => Term (bsubstRep T0 m U)
  end.
*)

Fixpoint bsubstRep r r0 s (T:InterpretRep r s)(m:atom)(U:Interpret r0) : InterpretRep r s :=
  match T with
    | Unit            => Unit 
    | Const _ T0      => Const r T0
    | Repr _ T0       => Repr r (bsubst T0 m U)
    | InL _ _ T0      => InL _ (bsubstRep T0 m U) 
    | InR _ _ T0      => InR _ (bsubstRep T0 m U)
    | Pair _ _ T0 T1  => Pair (bsubstRep T0 m U) (bsubstRep T1 m U)
    | Bind r1 _ _ T0  =>
      match Rep_dec r1 REC with
        | left _ => match Rep_dec r r0 with
                      | left _ => Bind r1 tt (bsubstRep T0 (S m) U)
                      | _      => Bind r1 tt (bsubstRep T0 m U)
                    end
        | _      => match Rep_dec r1 r0 with
                      | left _ => Bind r1 tt (bsubstRep T0 (S m) U)
                      | _      => Bind r1 tt (bsubstRep T0 m U)
                    end
      end
    | Rec T0          => Rec (bsubst T0 m U)
  end

with bsubst r r0 (T:Interpret r)(m:atom)(U:Interpret r0) : Interpret r :=
  match T with
    | Var v  => 
      match Rep_dec r r0 with 
        | left same => 
          match v with
            | inl _ => T
            | inr k => if (AtomDT.eq_dec m k) then conv same U else T
          end
        | right _ => T
      end
    | Term T0 => Term (bsubstRep T0 m U)
  end.

(**********************************************************************)
(** ** Heterogeneous sets of parameters *)
(**********************************************************************)

(** Note that [atoms] ~ [list nat] without redundancy.
   Cf. Coq.FSets.FSetWeakList.Make.slist.
   So we must work with the basic notations from Metatheory.v,
   that is, working with [nil], [app] won't work.

   [destruct_notin], [solve_notin] tactic from [FSetWeakNotin.v] is
   very useful in dealing with atoms.

   Note that the argument [r0] is the crucial point
   for the heterogeneous definition. *)

Fixpoint freevarsRep (r r0 s:Rep)(T:InterpretRep r s): atoms :=
  match T with 
    | Unit          => {}
    | Const _ _     => {} 
    | Repr s0 U     => @freevars s0 r0 U
    | InL _ _ U     => freevarsRep r0 U
    | InR _ _ U     => freevarsRep r0 U
    | Pair _ _ U U0 => (freevarsRep r0 U) `union` (freevarsRep r0 U0)
    | Bind _ _ _ U  => freevarsRep r0 U
    | Rec U         => freevars r0 U
  end

with freevars (r r0:Rep)(T:Interpret r) : atoms :=
  match T with
    | Var v  =>
      match Rep_dec r r0 with
        | left same => 
          match v with
            | inl a => {{ a }}
            | inr _ => {}
          end
        | right _ => {}
      end
    | Term U => freevarsRep r0 U
  end.

(**********************************************************************)
(** ** Heterogenesou well-formedness of a term or a type *)
(**********************************************************************)

(** Intuitive meaning of well-formedness is "no free occurrence
   of bound variables".
   
   - There are several equivalent ways to define well-formedness:
     -- Inductive definition of [wfT] which characterizes
        the set of well-formed terms;
   
     -- Defining [wf] and [wf_basic] directly;
   
   - [wf_basic] is a basic, but equivalent version of [wf].
     With [wf_basic], some lemmas are easier to prove.

   - Note that the argument [r0] is the crucial point
     for the heterogeneous definition.
     The well-formedness of a term is defined with respect to [r0].

   - Cofinite quantification style is used in the binder case. *)
   
(** [wfT] corresponds to [envT] in [LNameless_Meta_Env.v], but
   without using any environments.
   Notet that for the binding case, [cofinite quantification] is used. *)

Inductive wfTRep (r r0:Rep) : forall s, InterpretRep r s -> Prop :=
| wf_Unit  : wfTRep r0 Unit
| wf_Const : forall (s0:Rep)(T:Interpret s0),
  wfTRep r0 (Const r T)
| wf_Repr  : forall (s0:Rep)(T:Interpret s0),
  @wfT s0 r0 T -> wfTRep r0 (Repr r T)
| wf_InL   : forall s0 s1 (T:InterpretRep r s0),
  wfTRep r0 T -> wfTRep r0 (InL s1 T)
| wf_InR   : forall s0 s1 (T:InterpretRep r s1),
  wfTRep r0 T -> wfTRep r0 (InR s0 T)
| wf_Pair  : forall s0 s1 (T:InterpretRep r s0)(U:InterpretRep r s1),
  wfTRep r0 T -> wfTRep r0 U -> wfTRep r0 (Pair T U)
| wf_Bind_REC_homo  : forall s0 (T:InterpretRep r s0) L,
  r = r0 ->
  (forall (a:atom), a `notin` L -> wfTRep r0 (bsubstRep T 0 (Var r0 (inl a)))) ->
  wfTRep r0 (Bind REC tt T)
| wf_Bind_REC_hetero  : forall s0 (T:InterpretRep r s0),
  r <> r0 ->
  wfTRep r0 T ->
  wfTRep r0 (Bind REC tt T)
| wf_Bind_homo  : forall r1 s0 (T:InterpretRep r s0) L,
  r1 <> REC ->
  r1 = r0 ->
  (forall (a:atom), a `notin` L -> wfTRep r0 (bsubstRep T 0 (Var r0 (inl a)))) ->
  wfTRep r0 (Bind r1 tt T)
| wf_Bind_hetero  : forall r1 s0 (T:InterpretRep r s0),
  r1 <> REC ->
  r1 <> r0 ->
  wfTRep r0 T ->
  wfTRep r0 (Bind r1 tt T)
| wf_Rec   : forall T, wfT r0 T -> wfTRep r0 (Rec T)

with wfT (r r0:Rep) : Interpret r -> Prop :=
| wf_fvar : forall v, r = r0 -> wfT r0 (Var r (inl v))
| wf_Var  : forall v, r <> r0 -> wfT r0 (Var r v)
| wf_Term : forall T, wfTRep r0 T -> wfT r0 (Term T).

(** [wf] and [wf_basic] say directly that there are no free
   occurrence of a bound variable. *)

Definition wf r' (r:Rep)(T:Interpret r) := 
  forall (k:atom)(U:Interpret r'), T = bsubst T k U.

Definition wfRep r' (r s:Rep)(T:InterpretRep r s) :=
  forall (k:atom)(U:Interpret r'), T = bsubstRep T k U.

Definition wf_basic r' (r:Rep)(T:Interpret r) :=
  forall (k a:atom), T = bsubst T k (Var r' (inl a)).

Definition wfRep_basic r' (r s:Rep)(T:InterpretRep r s) :=
  forall (k a:atom), T = bsubstRep T k (Var r' (inl a)).

(** Parameters are well-formed. *)

Lemma wf_parameter : forall r' r (a:nat), wf r' (Var r (inl a)).
Proof.
  unfold wf; intros r' r a k U; simpl; case_rep; reflexivity.
Qed.

Hint Resolve wf_parameter.


(**********************************************************************)
(** * 2. Generic Properties *)
(**********************************************************************)


(**********************************************************************)
(** ** About the homomorphism [conv] *)
(**********************************************************************)

(** Note that [conv] is used to overcome Coq's restriction
   in dealing with dependent types for the definition of
   substitution for variables.

   The fact that [conv] deals with essentially the same terms/types
   should reflected in each use of [conv]. *)

(** [conv] and substitutions *)

Lemma conv_fsubst : forall r r0 r1 (e e0:r = r0)(T:Interpret r0)(U:Interpret r1) (a:atom),
  fsubst (conv e T) a U = conv e0 (fsubst T a U).
Proof.
  intros r r0 r1 e; case e.
  intro e0.
  rewrite (Rep_dec_unicity e0 refl).  
  unfold conv, eq_rect_r; simpl; intuition.
Qed.

Lemma conv_bsubst : forall r r0 r1 (e e0:r = r0)(T:Interpret r0)(U:Interpret r1) (m:atom),
  bsubst (conv e T) m U = conv e0 (bsubst T m U).
Proof.
  intros r r0 r1 e; case e.
  intro e0.
  rewrite (Rep_dec_unicity e0 refl).  
  unfold conv, eq_rect_r; simpl; intuition.
Qed.

(** [conv] and sets of free variables (parameters)  *)

Lemma conv_freevars_1 : forall r r0 r1 (e:r = r0) (T:Interpret r0),
  forall (a:atom), a `in` freevars r1 T -> a `in` freevars r1 (conv e T).
Proof.
  intros r r0 r1 e; case e; auto. 
Qed.

Lemma conv_freevars_2 : forall r r0 r1 (e:r = r0) (T:Interpret r0),
  forall (a:atom), a `in` freevars r1 (conv e T) -> a `in` freevars r1 T.
Proof.
  intros r r0 r1 e; case e; auto. 
Qed.  

Lemma conv_freevars_3 : forall r r0 r1 (e:r = r0) (T:Interpret r0),
  forall (a:atom), a `notin` freevars r1 T -> a `notin` freevars r1 (conv e T).
Proof.
  do 6 intro; intro H; contra H; eauto using conv_freevars_2.
Qed.

Lemma conv_freevars_4 : forall r r0 r1 (e:r = r0) (T:Interpret r0),
  forall (a:atom), a `notin` freevars r1 (conv e T) -> a `notin` freevars r1 T.
Proof.
  do 6 intro; intro H; contra H; eauto using conv_freevars_1.
Qed.

(** [conv] and well-formedness *)

Lemma conv_wfT : forall r r0 (e:r = r0)(T:Interpret r0) r1,
  wfT r1 T -> wfT r1 (conv e T).
Proof.
  intros r r0 e; case e.
  unfold conv, eq_rect_r; simpl; tauto.
Qed.

(**********************************************************************)
(** ** About Substitution *)
(**********************************************************************)

(** Substitution and size:
   - Replacing a bound variable by a parameter does not change
     the size of a term. *)

Lemma bsubst_sizeRep : forall r r0 s (T:InterpretRep r s)(k a:atom),
  sizeRep T = sizeRep (bsubstRep T k (Var r0 (inl a)))

  with bsubst_size : forall r r0 (T:Interpret r)(k a:atom),
  size T = size (bsubst T k (Var r0 (inl a))).
Proof.
  induction T as [| | | | | | |]; simpl; intros;
    [reflexivity |
     reflexivity |
     auto 1|   
     auto 1|   
     auto 1|   
     auto 3 with arith|
     repeat case_rep; simpl; auto 2|
     auto 1].   

  induction T as [? v|]; simpl; intros;
    [case_rep; destruct v; simpl; auto 1|
     auto 1];
    case_var; simpl; [rewrite <- conv_size; simpl; reflexivity | reflexivity].
Qed.

(** Substitution of a parameter for itself is an identity. *)

Ltac q_destruct :=
  match goal with
    | q : QQ |- _ => destruct q
  end.

Lemma fsubstRep_self : forall r r0 s (a:atom) (T:InterpretRep r s),
  T = fsubstRep T a (Var r0 (inl a))

  with fsubst_self : forall r r0 (a:atom) (T:Interpret r),
  T = fsubst T a (Var r0 (inl a)).
Proof.
(* fsubstRep_self *)
  destruct T; simpl; func_equal;
    try q_destruct; eauto 1.
  (* fsubst_self *)
  destruct T as [ v|]; simpl;
    [case_rep; destruct v; try reflexivity|
     func_equal; auto 1];
    case_var; eauto using conv_Var. 
Qed.  

(** Substitution for a parameter which does not occur
   is an identity function. *)

Lemma fsubstRep_no_occur : forall (r r0 s:Rep)(T:InterpretRep r s)(a:atom)(U:Interpret r0),
  a `notin` (freevarsRep r0 T) -> T = fsubstRep T a U

  with fsubst_no_occur : forall (r r0:Rep)(T:Interpret r)(a:atom)(U:Interpret r0),
    a `notin` (freevars r0 T) -> T = fsubst T a U.
Proof.
  (* fsubstRep_no_occur *)
  destruct T; simpl; intros; func_equal; eauto; try destruct_notin; try destruct q; eauto.
  (* fsubst_no_occur *)
  destruct T; simpl; intros; func_equal; eauto;
  case_eq (Rep_dec r r0); intros; auto.
  destruct v as [b |]; try case_eq (a == b); intros; try reflexivity.
  destruct (Rep_dec r r0); [idtac | contradiction].
  destruct_notin; congruence.
Qed.

(** Substitution Lemma  *)

Lemma fsubstitutionRep : forall (r r0 r1 s:Rep)
  (T:InterpretRep r s)(U:Interpret r0)(V:Interpret r1)(a b : atom),
  a <> b ->
  a `notin` (freevars r0 V) ->
  fsubstRep (fsubstRep T a U) b V =
  fsubstRep (fsubstRep T b V) a (fsubst U b V)
  
  with fsubstitution : forall (r r0 r1:Rep)
    (T:Interpret r)(U:Interpret r0)(V:Interpret r1)(a b : atom),
    a <> b ->
    a `notin` (freevars r0 V) ->
    fsubst (fsubst T a U) b V =
      fsubst (fsubst T b V) a (fsubst U b V).
Proof.
(* fsubstitutionRep *)
  destruct T; simpl; intros; func_equal; auto.
  
  (* fsubstitution *)
  destruct T; simpl; intros.
  (* Var *)
  destruct (Rep_dec r r0).
  (* r = r0 *)
  destruct v as [b0 |]; simpl.
  case_var; case_rep; try case_var; simpl; try case_rep; try contradiction;
    try case_var; try contradiction; try case_rep; try contradiction;
      try case_var; try contradiction; try case_rep; try contradiction;
        try absurd_math; intuition; auto using conv_fsubst.

  rewrite conv_indep with (e0:=e0);  apply fsubst_no_occur;
    auto using conv_freevars_3.

  case_rep; simpl; case_rep; intuition.
  (* r <> r0 *)
  case_rep; simpl; case_rep; intuition; destruct v; simpl;
    try case_var; intuition; try case_rep; intuition; simpl;
      try case_rep; intuition.
  rewrite conv_indep with (e0:=e);  apply fsubst_no_occur;
    auto using conv_freevars_3.
  (* Rec *)
  func_equal; auto.
Qed.

(** [AtomSetImpl] includes basic library for [union], etc.
   Cf. [Coq.FSets.FsetWeakList.v] *)

Export AtomSetImpl.

(** Substitution of a (bound) variable extends the set of parameters. *)

Lemma freevarsRep_pass_binder : forall r r0 r1 s (T :InterpretRep r s) (U:Interpret r0) (a b:atom),  
  a `in` (freevarsRep r1 T) -> a `in` (freevarsRep r1 (bsubstRep T b U))

  with freevars_pass_binder : forall r r0 r1 (T:Interpret r) (U:Interpret r0) (a b:atom),  
  a `in` (freevars r1 T) -> a `in` (freevars r1 (bsubst T b U)).
Proof.
  destruct T; simpl; intros; auto.
  (* Pair *)
  elim (union_1 H); intros; auto using union_2, union_3.
  (* Bind *)
  case_rep; simpl; case_rep; simpl; auto using freevarsRep_pass_binder.

  destruct T; simpl; intros; try case_rep; simpl; auto; try case_rep; intuition;
    destruct v; simpl; try case_rep; intuition; intuition; simpl;
      try case_rep; intuition; inversion H.
Qed.

(** Substitution of a variable is equivalent to substitution
   of that variable by a parameter which will be substituted again. *)

Lemma bfsubstRep_var_intro : forall r r0 s (T:InterpretRep r s)(U:Interpret r0) (a:atom),
  a `notin` (freevarsRep r0 T) ->
  forall (k:atom), bsubstRep T k U = fsubstRep (bsubstRep T k (Var r0 (inl a))) a U

  with bfsubst_var_intro : forall r r0 (T:Interpret r)(U:Interpret r0) (a:atom),
    a `notin` (freevars r0 T) ->
    forall (k:atom), bsubst T k U = fsubst (bsubst T k (Var r0 (inl a))) a U.
Proof.
  induction T; simpl; intros; destruct_notin; func_equal; auto.
  repeat case_rep; simpl; func_equal; apply IHT; assumption.

  induction T; simpl; intros; destruct_notin; func_equal; auto.
  case_rep; destruct v; try case_var; simpl; try case_rep; try congruence;
    try case_var; try congruence; try solve_notin.
  rewrite conv_fsubst with (e0:=e); func_equal; simpl.
  case_rep; try case_var; try congruence.
  symmetry; apply conv_id.
Qed.

(** Consecutive substitution of the same (bound) variable has no effect. *)

(* bsubstitutionRep_var_twice_1 => bsubstitutionRep_var_twice_wf
   bsubstitution_var_twice_1 => bsubstitution_var_twice_wf *)
Lemma bsubstitutionRep_var_twice_wf : forall r s (T:InterpretRep r s) r0 (k:atom) (V U:Interpret r0),
  wf r0 V ->
  bsubstRep T k V
  = bsubstRep (bsubstRep T k V) k U

  with bsubstitution_var_twice_wf : forall r (T:Interpret r) r0 (k:atom) (V U:Interpret r0),
    wf r0 V ->
    bsubst T k V
    = bsubst (bsubst T k V) k U.
Proof.
  induction T; simpl; intros; try reflexivity.
  f_equal; apply bsubstitution_var_twice_wf; assumption.
  f_equal; apply bsubstitutionRep_var_twice_wf; assumption.
  f_equal; apply bsubstitutionRep_var_twice_wf; assumption.
  f_equal; apply bsubstitutionRep_var_twice_wf; assumption.
  repeat case_rep; simpl; repeat case_rep; try congruence.
  f_equal; apply bsubstitutionRep_var_twice_wf; assumption.
  f_equal; apply bsubstitutionRep_var_twice_wf; assumption.
  f_equal; apply bsubstitutionRep_var_twice_wf; assumption.
  f_equal; apply bsubstitutionRep_var_twice_wf; assumption.

  f_equal; apply bsubstitution_var_twice_wf; assumption.

  induction T; simpl; intros.
  repeat case_rep; destruct v; repeat case_var; simpl;
    repeat case_rep; try congruence; simpl;
      repeat case_var; try congruence.
  rewrite conv_bsubst with (e0:=e).
  f_equal; apply H.

  f_equal; apply bsubstitutionRep_var_twice_wf; assumption.
Qed.

Lemma bsubstitutionRep_var_twice : forall r s (T:InterpretRep r s) r0 k a (U:Interpret r0),
  bsubstRep T k (Var r0 (inl a)) = bsubstRep (bsubstRep T k (Var r0 (inl a))) k U.
Proof.
  intros; apply bsubstitutionRep_var_twice_wf; auto.
Qed.

Lemma bsubstitution_var_twice : forall r (T:Interpret r) r0 k a (U:Interpret r0),
  bsubst T k (Var r0 (inl a)) = bsubst (bsubst T k (Var r0 (inl a))) k U.
Proof.
  intros; apply bsubstitution_var_twice_wf; auto.
Qed.

(* bsubstitutionRep_homo_1 => bsubstitutionRep_homo_wf
   bsubstitution_homo_1 => bsubstitution_homo_wf *)
Lemma bsubstitutionRep_homo_wf: forall r s (T:InterpretRep r s) r0 k l (U V:Interpret r0),
  k <> l ->
  wf r0 U ->
  wf r0 V ->
  bsubstRep (bsubstRep T k U) l V = bsubstRep (bsubstRep T l V) k U

  with bsubstitution_homo_wf: forall r (T:Interpret r) r0 k l (U V:Interpret r0),
    k <> l ->
    wf r0 U ->
    wf r0 V ->
    bsubst (bsubst T k U) l V = bsubst (bsubst T l V) k U.
Proof.
  induction T; simpl; intros; try reflexivity.
  f_equal; apply bsubstitution_homo_wf; assumption.
  f_equal; apply bsubstitutionRep_homo_wf; assumption.
  f_equal; apply bsubstitutionRep_homo_wf; assumption.
  f_equal; apply bsubstitutionRep_homo_wf; assumption.
  repeat case_rep; simpl;
    repeat case_rep; first [absurd_math | try congruence | try contradiction]; func_equal.
  
  apply bsubstitutionRep_homo_wf; auto with arith.
  apply bsubstitutionRep_homo_wf; assumption.
  apply bsubstitutionRep_homo_wf; auto with arith.
  apply bsubstitutionRep_homo_wf; assumption.

  f_equal; apply bsubstitution_homo_wf; assumption.

  induction T; simpl; intros.

  case_rep; destruct v; simpl; try case_rep; repeat case_var;
    try congruence; simpl;
      repeat case_rep; repeat case_var; try congruence.

  rewrite conv_bsubst with (e0:=e0); f_equal; symmetry; apply H0.
  rewrite conv_bsubst with (e0:=e0); f_equal; apply H1.  

  f_equal; apply bsubstitutionRep_homo_wf; assumption.
Qed.

Lemma bsubstitutionRep_homo: forall r s (T:InterpretRep r s) r0 k l a b,
  k <> l ->
  bsubstRep (bsubstRep T k (Var r0 (inl a))) l (Var r0 (inl b))
  = bsubstRep (bsubstRep T l (Var r0 (inl b))) k (Var r0 (inl a)).
Proof.
  intros; apply bsubstitutionRep_homo_wf; auto.
Qed.

Lemma bsubstitution_homo: forall r (T:Interpret r) r0 k l a b,
  k <> l ->
  bsubst (bsubst T k (Var r0 (inl a))) l (Var r0 (inl b))
  = bsubst (bsubst T l (Var r0 (inl b))) k (Var r0 (inl a)).
Proof.
  intros; apply bsubstitution_homo_wf; auto.
Qed.

(* bsubstitutionRep_hetero_1 => bsubstitutionRep_hetero_wf
   bsubstitution_hetero_1 => bsubstitution_hetero_wf *)
Lemma bsubstitutionRep_hetero_wf : forall (r r0 r1 s:Rep) (T:InterpretRep r s)(k l: atom) (U:Interpret r0)(V:Interpret r1),
  r0 <> r1 ->
  wf r1 U ->
  wf r0 V ->
  bsubstRep (bsubstRep T k U) l V = bsubstRep (bsubstRep T l V) k U
  
  with bsubstitution_hetero_wf : forall (r r0 r1:Rep) (T:Interpret r)(k l : atom) (U:Interpret r0)(V:Interpret r1),
  r0 <> r1 ->
  wf r1 U ->
  wf r0 V ->
  bsubst (bsubst T k U) l V = bsubst (bsubst T l V) k U.
Proof.
  destruct T; simpl; intros;
    [ reflexivity
      | reflexivity
      | f_equal; apply bsubstitution_hetero_wf; assumption
      | f_equal; apply bsubstitutionRep_hetero_wf; assumption
      | f_equal; apply bsubstitutionRep_hetero_wf; assumption
      | f_equal; apply bsubstitutionRep_hetero_wf; assumption
      | repeat (case_rep; simpl); try congruence; f_equal;
        apply bsubstitutionRep_hetero_wf; assumption
      | f_equal; apply bsubstitution_hetero_wf; assumption ].

  destruct T; simpl; intros;
    [ repeat (repeat case_rep; try destruct v; simpl; repeat case_var; try congruence);
      erewrite conv_bsubst; f_equal*
      | f_equal; apply bsubstitutionRep_hetero_wf; assumption ].
Qed.

Lemma bsubstitutionRep_hetero : forall (r r0 r1 s:Rep) (T:InterpretRep r s)(k l a b : atom),
  r0 <> r1 ->
  bsubstRep (bsubstRep T k (Var r0 (inl a))) l (Var r1 (inl b)) =
  bsubstRep (bsubstRep T l (Var r1 (inl b))) k (Var r0 (inl a)).
Proof.
  intros; apply bsubstitutionRep_hetero_wf; auto.
Qed.

Lemma bsubstitution_hetero : forall (r r0 r1:Rep) (T:Interpret r)(k l a b : atom),
  r0 <> r1 ->
  bsubst (bsubst T k (Var r0 (inl a))) l (Var r1 (inl b)) =
  bsubst (bsubst T l (Var r1 (inl b))) k (Var r0 (inl a)).
Proof.
  intros; apply bsubstitution_hetero_wf; auto.
Qed.


(**************************************************************)
(** ** Well-formedness and substitution *)
(**************************************************************)

(** Equivalence of [wf] and [wf_basic] *)

Lemma wf_from_wf_basic : forall r' (r:Rep)(T:Interpret r),
  wf_basic r' T -> wf r' T.
Proof.
  unfold wf, wf_basic; intros.
  pick fresh a for (freevars r' T); destruct_notin.
  rewrite bfsubst_var_intro with (a:=a);
    [rewrite <- H; auto using fsubst_no_occur | assumption].
Qed.

(** Preparing lemmas *)

(* bsubstRep_wfT_core => bsubstRep_homo_core
   bsubst_wfT_core => bsubst_homo_core *)
Lemma bsubstRep_homo_core : forall r r0 s (T:InterpretRep r s) (U V:Interpret r0) k j,
  k <> j -> 
  bsubstRep T j V = bsubstRep (bsubstRep T j V) k U -> 
  T = bsubstRep T k U

  with bsubst_homo_core : forall r r0 (T :Interpret r) (U V:Interpret r0) k j,
    k <> j -> 
    bsubst T j V = bsubst (bsubst T j V) k U ->
    T = bsubst T k U.
Proof.
  (* bsubstRep_homo_core *)
  destruct T; simpl; intros U V k j H H0;
    [ reflexivity
      | reflexivity
      | dependent destruction H0; f_equal; eapply bsubst_homo_core; eassumption
      | dependent destruction H0; f_equal; eapply bsubstRep_homo_core; eassumption
      | dependent destruction H0; f_equal; eapply bsubstRep_homo_core; eassumption
      | dependent destruction H0; f_equal; eapply bsubstRep_homo_core; eassumption
      | q_destruct; repeat (repeat case_rep; simpl in *; try congruence);
        dependent destruction H0; f_equal; eapply bsubstRep_homo_core;
          try eassumption; auto with arith
      | dependent destruction H0; f_equal; eapply bsubst_homo_core; eassumption ].
  (* bsubst_homo_core *)
  destruct T; simpl; intros U V k j H H0;
    [ repeat
      (repeat case_rep; try destruct v; repeat case_var; simpl in *; try congruence);
      erewrite conv_indep; eassumption
      | dependent destruction H0; func_equal; eapply bsubstRep_homo_core; eassumption ].
Qed.  

(* bsubstRep_core => bsubstRep_hetero_core
   bsubst_core => bsubst_hetero_core *)
Lemma bsubstRep_hetero_core : forall r r0 r1 s (T:InterpretRep r s)(U:Interpret r0)(V:Interpret r1) k j,
  r0 <> r1 ->
  bsubstRep T j V = bsubstRep (bsubstRep T j V) k U -> 
  T = bsubstRep T k U

  with bsubst_hetero_core : forall r r0 r1 (T :Interpret r) (U:Interpret r0)(V:Interpret r1) k j,
    r0 <> r1 ->
    bsubst T j V = bsubst (bsubst T j V) k U ->
    T = bsubst T k U.
Proof.
  destruct T; simpl; intros U V k j H H0;
    [ reflexivity
      | reflexivity
      | dependent destruction H0; f_equal; eapply bsubst_hetero_core; eassumption
      | dependent destruction H0; f_equal; eapply bsubstRep_hetero_core; eassumption
      | dependent destruction H0; f_equal; eapply bsubstRep_hetero_core; eassumption
      | dependent destruction H0; f_equal; eapply bsubstRep_hetero_core; eassumption
      | q_destruct; repeat (repeat case_rep; simpl in *; try congruence);
        dependent destruction H0; f_equal; eapply bsubstRep_hetero_core;
          try eassumption; auto with arith
      | dependent destruction H0; f_equal; eapply bsubst_hetero_core; eassumption ].

  destruct T; simpl; intros U V k j H H0;
    [ repeat
      (repeat case_rep; try destruct v; repeat case_var; simpl in *; try congruence);
      erewrite conv_indep; eassumption
      | dependent destruction H0; func_equal; eapply bsubstRep_hetero_core; eassumption ].
Qed.  

(** Well-formed terms contains no free occurring bound varibles. *)

(* wfTRep_bsubst_id => wfTRep_wfRep
   wfT_bsubst_id => wfT_wf *)
Lemma wfTRep_wfRep : forall r r0 s (T:InterpretRep r s),
  wfTRep r0 T ->
  forall k (U:Interpret r0), T = bsubstRep T k U

  with wfT_wf : forall r r0 (T:Interpret r),
    wfT r0 T ->
    forall k (U:Interpret r0), T = bsubst T k U.
Proof.
  induction 1; simpl; intros; try do 2 case_rep; intuition; func_equal; auto.
 (* wf_Bind_REC_homo *)
  case_rep; intuition; func_equal.
  pick fresh y for L.
  eapply bsubstRep_homo_core with (j:=0).
  omega.
  eapply H1; eauto.
  (* wf_Bind_REC_hetero *)
  case_rep; intuition; func_equal; auto.  
 (* wf_Bind_homo *)
  pick fresh y for L.
  eapply bsubstRep_homo_core with (j:=0).
  omega.
  eapply H2; eauto.
  
  induction 1; intros.
  (* fvar *)
  simpl; destruct (Rep_dec r r0); reflexivity.
  (* Var *)
  simpl; destruct (Rep_dec r r0); [contradiction | reflexivity].
 
  (* Term *)
  simpl; f_equal; apply wfTRep_wfRep; auto.
Qed.

(**************************************************************)
(** ** Permutation of substitutions *)
(**************************************************************)

Lemma bfsubstRep_permutation_core : forall r r0 r1 s (T:InterpretRep r s)(U:Interpret r0)(V:Interpret r1) a, 
  wfT r1 U ->
  forall k, bsubstRep (fsubstRep T a U) k (fsubst V a U) = fsubstRep (bsubstRep T k V) a U

  with bfsubst_permutation_core : forall r r0 r1 (T:Interpret r)(U:Interpret r0)(V:Interpret r1) a, 
    wfT r1 U ->
    forall k, bsubst (fsubst T a U) k (fsubst V a U) = fsubst (bsubst T k V) a U.
Proof.
  destruct T; simpl; intros U V a H k; try do 2 case_rep;
    intuition; simpl; func_equal; auto.

  destruct T; simpl; intros U V a H k; try case_rep; simpl; func_equal; eauto;
  try case_rep; destruct v; try case_var; simpl; try case_rep; intuition;
    try case_var; intuition; try case_rep; intuition.
  rewrite conv_bsubst with (e0:=e1); func_equal; 
    symmetry; apply wfT_wf; auto.

  rewrite conv_fsubst with (e0:=e1); auto. 

  rewrite conv_bsubst with (e0:=e0); f_equal;
    symmetry; apply wfT_wf; auto.

  rewrite conv_fsubst with (e0:=e); auto.
Qed. 

Lemma bfsubstRep_permutation_core_wf : forall r r0 r1 s
  (T:InterpretRep r s)(U:Interpret r0)(V:Interpret r1) a, 
  wf r1 U ->
  forall k, bsubstRep (fsubstRep T a U) k (fsubst V a U) = fsubstRep (bsubstRep T k V) a U

  with bfsubst_permutation_core_wf : forall r r0 r1
    (T:Interpret r)(U:Interpret r0)(V:Interpret r1) a, 
    wf r1 U ->
    forall k, bsubst (fsubst T a U) k (fsubst V a U) = fsubst (bsubst T k V) a U.
Proof.
  destruct T; simpl; intros U V a Hwf k; func_equal; auto.
  do 2 case_rep; simpl; func_equal; auto.

  unfold wf_basic; destruct T; simpl; intros U V a Hwf k; func_equal; auto.
  repeat case_rep; try destruct v; try case_var; try congruence; simpl;
    repeat case_rep; repeat case_var; try congruence.
  rewrite conv_bsubst with (e0:=e1); func_equal; symmetry; auto.
  rewrite conv_fsubst with (e0:=e1); func_equal; symmetry; auto.
  rewrite conv_bsubst with (e0:=e0); func_equal; symmetry; auto.
  rewrite conv_fsubst with (e0:=e0); func_equal; symmetry; auto.
Qed.

Lemma bfsubstRep_permutation_ind : forall r r0 r1 s (T:InterpretRep r s)(U:Interpret r0)(V:Interpret r1) a, 
  wfT r1 U ->
  a `notin` (freevars r0 V) ->
  forall k, bsubstRep (fsubstRep T a U) k V = fsubstRep (bsubstRep T k V) a U.
Proof.
  intros; pattern V at 1;
    rewrite fsubst_no_occur with (a:=a) (U:=U);
      auto using bfsubstRep_permutation_core.
Qed.
      
Lemma bfsubst_permutation_ind : forall r r0 r1 (T:Interpret r)(U:Interpret r0)(V:Interpret r1) a, 
  wfT r1 U ->
  a `notin` (freevars r0 V) ->
  forall k, bsubst (fsubst T a U) k V = fsubst (bsubst T k V) a U.
Proof.
  intros; pattern V at 1;
    rewrite fsubst_no_occur with (a:=a) (U:=U);
      auto using bfsubst_permutation_core.
Qed.

Lemma bfsubstRep_permutation_ind_wf : forall r r0 r1 s
  (T:InterpretRep r s)(U:Interpret r0)(V:Interpret r1) a, 
  wf r1 U ->
  a `notin` (freevars r0 V) ->
  forall k,
    bsubstRep (fsubstRep T a U) k V = fsubstRep (bsubstRep T k V) a U.
Proof.
  intros; pattern V at 1;
    rewrite fsubst_no_occur with (a:=a) (U:=U);
      auto using bfsubstRep_permutation_core_wf.
Qed.
      
Lemma bfsubst_permutation_ind_wf : forall r r0 r1
  (T:Interpret r)(U:Interpret r0)(V:Interpret r1) a, 
  wf r1 U ->
  a `notin` (freevars r0 V) ->
  forall k,
    bsubst (fsubst T a U) k V = fsubst (bsubst T k V) a U.
Proof.
  intros; pattern V at 1;
    rewrite fsubst_no_occur with (a:=a) (U:=U);
      auto using bfsubst_permutation_core_wf.
Qed.

Lemma bfsubstRep_permutation_wfT : forall r r0 r1 s (T:InterpretRep r s)(U:Interpret r0)(V:Interpret r1) a,
  wfT r1 U -> 
  a `notin` (freevars r0 V) ->
  bsubstRep (fsubstRep T a U) 0 V = fsubstRep (bsubstRep T 0 V) a U.
Proof.
  intros; eauto using bfsubstRep_permutation_ind. 
Qed.

Lemma bfsubst_permutation_wfT : forall r r0 r1 (T:Interpret r)(U:Interpret r0)(V:Interpret r1) a,
  wfT r1 U -> 
  a `notin` (freevars r0 V) ->
  bsubst (fsubst T a U) 0 V = fsubst (bsubst T 0 V) a U.
Proof.
  intros; eauto using bfsubst_permutation_ind. 
Qed.

Lemma bfsubstRep_permutation_wf : forall r r0 r1 s
  (T:InterpretRep r s)(U:Interpret r0)(V:Interpret r1) a,
  wf r1 U -> 
  a `notin` (freevars r0 V) ->
  bsubstRep (fsubstRep T a U) 0 V = fsubstRep (bsubstRep T 0 V) a U.
Proof.
  intros; eauto using bfsubstRep_permutation_ind_wf. 
Qed.

Lemma bfsubst_permutation_wf : forall r r0 r1
  (T:Interpret r)(U:Interpret r0)(V:Interpret r1) a,
  wf r1 U -> 
  a `notin` (freevars r0 V) ->
  bsubst (fsubst T a U) 0 V = fsubst (bsubst T 0 V) a U.
Proof.
  intros; eauto using bfsubst_permutation_ind_wf. 
Qed.

Lemma bfsubstRep_permutation_var_wfT : forall r r0 r1 s (T:InterpretRep r s)(U:Interpret r0) a b,
  a <> b ->
  wfT r1 U -> 
  bsubstRep (fsubstRep T a U) 0 (Var r1 (inl b))
  = fsubstRep (bsubstRep T 0 (Var r1 (inl b))) a U.
Proof.
  intros; apply bfsubstRep_permutation_wfT; try solve_notin;
    simpl; case_rep; simpl; solve_notin.
Qed.

Lemma bfsubst_permutation_var_wfT : forall r r0 r1 (T:Interpret r) (U:Interpret r0) a b,
  a <> b ->
  wfT r1 U -> 
  bsubst (fsubst T a U) 0 (Var r1 (inl b))
  = fsubst (bsubst T 0 (Var r1 (inl b))) a U.
Proof.
  intros; apply bfsubst_permutation_wfT; try solve_notin;
    simpl; case_rep; simpl; solve_notin.
Qed.

Lemma bfsubstRep_permutation_var_wf : forall r r0 r1 s
  (T:InterpretRep r s)(U:Interpret r0) a b,
  a <> b ->
  wf r1 U -> 
  bsubstRep (fsubstRep T a U) 0 (Var r1 (inl b))
  = fsubstRep (bsubstRep T 0 (Var r1 (inl b))) a U.
Proof.
  introv Hneq Hwf.
  rewrite <- bfsubstRep_permutation_core_wf; auto.
  simpl; case_rep; auto; case_var; congruence.
Qed.

Lemma bfsubst_permutation_var_wf : forall r r0 r1
  (T:Interpret r) (U:Interpret r0) a b,
  a <> b ->
  wf r1 U -> 
  bsubst (fsubst T a U) 0 (Var r1 (inl b))
  = fsubst (bsubst T 0 (Var r1 (inl b))) a U.
Proof.
  introv Hneq Hwf.
  rewrite <- bfsubst_permutation_core_wf; auto.
  simpl; case_rep; auto; case_var; congruence.
Qed.

Lemma bfsubst_permutation_var_wfT_hetero : forall r r0 r1 (T:Interpret r) (U:Interpret r0) a b,
  r0 <> r1 ->
  wfT r1 U -> 
  bsubst (fsubst T a U) 0 (Var r1 (inl b))
  = fsubst (bsubst T 0 (Var r1 (inl b))) a U.
Proof.
  intros; apply bfsubst_permutation_wfT; try solve_notin;
    simpl; case_rep; simpl; solve_notin.
Qed.

(** Substitution preserves well-formedness *)

Lemma wfT_fsubstRep : forall r r0 r1 s (T:InterpretRep r s)(U:Interpret r0) a,
  wfTRep r1 T ->
  wfT r1 U ->
  wfTRep r1 (fsubstRep T a U)

  with wfT_fsubst : forall r r0 r1 (T:Interpret r)(U:Interpret r0) a,
    wfT r1 T ->
    wfT r1 U ->
    wfT r1 (fsubst T a U).
Proof.
  destruct 1; simpl; intros;
    [ constructor 1
      | constructor 2
      | constructor 3; apply wfT_fsubst; auto
      | constructor 4; apply wfT_fsubstRep; auto
      | constructor 5; apply wfT_fsubstRep; auto
      | constructor 6; apply wfT_fsubstRep; auto
      | idtac
      | constructor 8; auto
      | idtac
      | constructor 10; auto
      | constructor 11; auto ].
  (* Bind_REC_homo *)
  constructor 7 with (L `union` {{ a }}); intros; auto.
  destruct_notin.
  assert
    (bsubstRep (fsubstRep T a U) 0%nat (Var r1 (inl a0 ))
      = fsubstRep (bsubstRep T 0%nat (Var r1 (inl a0))) a U).
    replace (Var r1 (inl a0)) with (fsubst (Var r1 (inl a0)) a U).
      simpl.
      case_rep.
        destruct (a == a0); intuition.
        apply bfsubstRep_permutation_ind; auto.
        rewrite <- e; simpl.
        destruct (Rep_dec r1 r1); try contradiction.
          solve_notin.
        intuition.
      apply bfsubstRep_permutation_ind; auto.
      simpl; case_rep; try contradiction.
      solve_notin.
    simpl; case_rep; try contradiction; auto; case_var; intuition.
  rewrite H3.
  apply wfT_fsubstRep; auto.
  
  (* Bind_homo *)
  constructor 9 with (L `union` {{ a }}); intros; auto.
  destruct_notin.
  assert
    (bsubstRep (fsubstRep T a U) 0%nat (Var r1 (inl a0))
      = fsubstRep (bsubstRep T 0%nat (Var r1 (inl a0))) a U).
    replace (Var r1 (inl a0)) with (fsubst (Var r1 (inl a0)) a U).
      simpl.
      destruct (Rep_dec r1 r0).
        destruct (a == a0); intuition.
        apply bfsubstRep_permutation_ind; auto.
        rewrite <- e; simpl.
        destruct (Rep_dec r1 r1); try contradiction.
          solve_notin.
        intuition.
      apply bfsubstRep_permutation_ind; auto.
      simpl; case_rep; try contradiction.
      solve_notin.
    simpl; case_rep; try contradiction; auto; case_var; intuition.
  rewrite H4.
  apply wfT_fsubstRep; auto.

  destruct 1; simpl; intros; destruct (Rep_dec r r0); simpl;
    try destruct (a == b); try destruct (a == v); simpl; intuition;
      auto using conv_wfT.
  constructor; auto.
  constructor; auto.
  constructor; auto.
    (* Var *)
  destruct v; auto; try case_var; auto; auto using conv_wfT; try constructor 2; auto.
  constructor 2; auto.

  constructor 3; auto using wfT_fsubstRep.
  constructor 3; auto using wfT_fsubstRep.
Qed.

(* Preparing lemma *)

Lemma wf_fsubstRep_ : forall r r0 r1 s (T:InterpretRep r s)(U:Interpret r0)
  a k (V: Interpret r1),
  T = bsubstRep T k V ->
  wf r1 U ->
  fsubstRep T a U = bsubstRep (fsubstRep T a U) k V

  with wf_fsubst_ : forall r r0 r1 (T:Interpret r)(U:Interpret r0)
    a k (V:Interpret r1),
    T = bsubst T k V ->
    wf r1 U ->
    fsubst T a U = bsubst (fsubst T a U) k V.
Proof.
  induction T; unfold wfRep, wf in *; simpl; intros; func_equal; auto.

  apply wf_fsubst_; [idtac | assumption].
  dependent destruction H; assumption.

  apply wf_fsubstRep_; [idtac | assumption].
  dependent destruction H; assumption.
  
  apply wf_fsubstRep_; [idtac | assumption].
  dependent destruction H; assumption.
  
  apply wf_fsubstRep_; [idtac | assumption].
  dependent destruction H; assumption.
  
  apply wf_fsubstRep_; [idtac | assumption].
  dependent destruction H; assumption.

  repeat case_rep; func_equal; simpl;
  apply wf_fsubstRep_; try assumption;
    dependent destruction H; assumption.

  apply wf_fsubst_; [idtac | assumption].
  dependent destruction H; assumption.

  induction T; unfold wfRep, wf in *; simpl; intros; func_equal; auto.

  repeat case_rep; destruct v; simpl;
    repeat case_rep; try congruence;
      repeat case_var; try congruence; simpl;
        repeat case_rep; try congruence.

  rewrite conv_bsubst with (e0:=e); func_equal; symmetry; auto.
  rewrite H; apply conv_indep.
  rewrite conv_bsubst with (e0:=e); func_equal; symmetry; auto.
  rewrite H; apply conv_indep.

  apply wf_fsubstRep_; [idtac | assumption].
  dependent destruction H; assumption.
Qed.

Lemma wf_fsubstRep : forall r r0 r1 s (T:InterpretRep r s)(U:Interpret r0) a,
  wfRep r1 T -> wf r1 U -> wfRep r1 (fsubstRep T a U).
Proof.
  unfold wfRep; intros; auto using wf_fsubstRep_.
Qed.

Lemma wf_fsubst : forall r r0 r1 (T:Interpret r)(U:Interpret r0) a,
    wf r1 T -> wf r1 U -> wf r1 (fsubst T a U).
Proof.
  unfold wf at -2; intros; auto using wf_fsubst_.
Qed.


(**************************************************************)
(** ** Heterogeneous substitution and well-formedness *)
(**************************************************************)

(** Heterogeneous substitition has no effect on well-formedness  *)

(** Preparing lemma  *)

Lemma wfT_bsubstRep_hetero_ : forall r s (T:InterpretRep r s) r0,
  wfTRep r0 T ->
  forall (T0:InterpretRep r s) r1 k a,
    T = bsubstRep T0 k (Var r1 (inl a)) ->
    r0 <> r1 ->
    wfTRep r0 T0

  with wfT_bsubst_hetero_ : forall r (T:Interpret r) r0,
    wfT r0 T ->
    forall (T0:Interpret r) r1 k a,
      T = bsubst T0 k (Var r1 (inl a)) ->
      r0 <> r1 ->
      wfT r0 T0.
Proof.
  induction 1.

  dependent destruction T0; simpl; intros.
  apply wf_Unit.

  dependent destruction T0; simpl; intros.
  apply wf_Const.

  dependent destruction T0; simpl; intros.
  assert (T = bsubst i k (Var r1 (inl a))).  
  dependent destruction H0; reflexivity.
  apply wf_Repr.
  apply wfT_bsubst_hetero_ with T r1 k a; assumption.

  dependent destruction T0; simpl; intros; [idtac | discriminate].
  assert (T = bsubstRep T0 k (Var r1 (inl a))).
  dependent destruction H0; reflexivity.
  apply wf_InL.
  apply wfT_bsubstRep_hetero_ with T r1 k a; assumption.

  dependent destruction T0; simpl; intros; [discriminate | idtac].
  assert (T = bsubstRep T0 k (Var r1 (inl a))).
  dependent destruction H0; reflexivity.
  apply wf_InR.
  apply wfT_bsubstRep_hetero_ with T r1 k a; assumption.

  dependent destruction T0; simpl; intros.
  assert (T = bsubstRep T0_1 k (Var r1 (inl a))).  
  dependent destruction H1; reflexivity.
  assert (U = bsubstRep T0_2 k (Var r1 (inl a))).  
  dependent destruction H1; reflexivity.
  apply wf_Pair.
  apply wfT_bsubstRep_hetero_ with T r1 k a; assumption.
  apply wfT_bsubstRep_hetero_ with U r1 k a; assumption.

  dependent destruction T0; simpl; intros; destruct q; case_rep.
  assert (T = bsubstRep T0 (S k) (Var r1 (inl a))).  
  dependent destruction H2; reflexivity.
  apply wf_Bind_REC_homo with L; [assumption|idtac]; intros.
  apply wfT_bsubstRep_hetero_ with (bsubstRep T 0 (Var r0 (inl a0))) r1 (S k) a;
    [apply H0; assumption |
      rewrite H4; apply bsubstitutionRep_hetero; congruence |
        assumption].

  assert (T = bsubstRep T0 k (Var r1 (inl a))).  
  dependent destruction H2; reflexivity.
  apply wf_Bind_REC_homo with L; [assumption|idtac]; intros.
  apply wfT_bsubstRep_hetero_ with (bsubstRep T 0 (Var r0 (inl a0))) r1 k a;
    [apply H0; assumption |
      rewrite H4; apply bsubstitutionRep_hetero; congruence |
        assumption].

  dependent destruction T0; simpl; intros; destruct q; case_rep.
  assert (T = bsubstRep T0 (S k) (Var r1 (inl a))).  
  dependent destruction H1; reflexivity.
  apply wf_Bind_REC_hetero; [assumption|idtac].
  apply wfT_bsubstRep_hetero_ with T r1 (S k) a; assumption.

  assert (T = bsubstRep T0 k (Var r1 (inl a))).  
  dependent destruction H1; reflexivity.
  apply wf_Bind_REC_hetero; [assumption|idtac].
  apply wfT_bsubstRep_hetero_ with T r1 k a; assumption.

  dependent destruction T0; simpl; intros; destruct q; repeat case_rep;
    try contradiction.
  assert (T = bsubstRep T0 (S k) (Var r2 (inl a))).
  dependent destruction H3; reflexivity.  
  apply wf_Bind_homo with L; try tauto; intros.
  apply wfT_bsubstRep_hetero_ with (bsubstRep T 0 (Var r0 (inl a0))) r2 (S k) a;
    [apply H1; assumption |
      rewrite H5; apply bsubstitutionRep_hetero; congruence |
        assumption].

  assert (T = bsubstRep T0 k (Var r2 (inl a))).
  dependent destruction H3; reflexivity.  
  apply wf_Bind_homo with L; try tauto; intros.
  apply wfT_bsubstRep_hetero_ with (bsubstRep T 0 (Var r0 (inl a0))) r2 k a;
    [apply H1; assumption |
      rewrite H5; apply bsubstitutionRep_hetero; congruence |
        assumption].

  dependent destruction T0; simpl; intros; destruct q; repeat case_rep;
    try contradiction.
  assert (T = bsubstRep T0 (S k) (Var r2 (inl a))).
  dependent destruction H2; reflexivity.  
  apply wf_Bind_hetero; [assumption | assumption | idtac].
  apply wfT_bsubstRep_hetero_ with T r2 (S k) a; assumption.

  assert (T = bsubstRep T0 k (Var r2 (inl a))).
  dependent destruction H2; reflexivity.  
  apply wf_Bind_hetero; [assumption | assumption | idtac].
  apply wfT_bsubstRep_hetero_ with T r2 k a; assumption.

  dependent destruction T0; simpl; intros.
  assert (T = bsubst i k (Var r1 (inl a))).  
  dependent destruction H0; reflexivity.
  apply wf_Rec.
  apply wfT_bsubst_hetero_ with T r1 k a; assumption.

  induction 1; dependent destruction T0; simpl; intros;
    try case_rep; try destruct v0; try congruence; try discriminate.
  apply wf_fvar; tauto.
  apply wf_Var; tauto.
  apply wf_Var; tauto.
  apply wf_Var; tauto.
  apply wf_Var; tauto.
  destruct v; try discriminate.
  case_var; try rewrite <- conv_Var in H0; discriminate.

  assert (T = bsubstRep i k (Var r1 (inl a))).  
  dependent destruction H0; reflexivity.
  apply wf_Term.
  apply wfT_bsubstRep_hetero_ with T r1 k a; assumption.
Qed.

Lemma wfT_bsubstRep_hetero : forall r s (T:InterpretRep r s) r0 r1 k a,
  wfTRep r0 (bsubstRep T k (Var r1 (inl a))) ->
  r0 <> r1 ->
  wfTRep r0 T.
Proof.
  intros; apply wfT_bsubstRep_hetero_ with (bsubstRep T k (Var r1 (inl a))) r1 k a; auto.
Qed.

Lemma wfT_bsubst_hetero : forall r (T:Interpret r) r0 r1 k a,
  wfT r0 (bsubst T k (Var r1 (inl a))) ->
  r0 <> r1 ->
  wfT r0 T.
Proof.
  intros; apply wfT_bsubst_hetero_ with (bsubst T k (Var r1 (inl a))) r1 k a; auto.
Qed.

Lemma wfT_bsubstRep_hetero_1 : forall r s (T:InterpretRep r s) r0 r1,
  wfTRep r0 T ->
  r0 <> r1 ->
  forall (k a:atom), wfTRep r0 (bsubstRep T k (Var r1 (inl a)))

  with wfT_bsubst_hetero_1 : forall r (T:Interpret r) r0 r1,
    wfT r0 T ->
    r0 <> r1 ->
    forall (k a:atom), wfT r0 (bsubst T k (Var r1 (inl a))).
Proof.
  induction 1; simpl; intros.
  apply wf_Unit.
  apply wf_Const.
  apply wf_Repr; auto.
  apply wf_InL; auto.  
  apply wf_InR; auto.
  apply wf_Pair; auto.

  case_rep;
  apply wf_Bind_REC_homo with L; auto; intros; 
    rewrite bsubstitutionRep_hetero; auto.

  case_rep;
  apply wf_Bind_REC_hetero; auto; intros.

  case_rep; try congruence.
  case_rep; try congruence.
  apply wf_Bind_homo with L; auto; intros; 
    rewrite bsubstitutionRep_hetero; auto.

  case_rep; try congruence.
  case_rep; try congruence;
    apply wf_Bind_hetero; auto; intros.

  apply wf_Rec; auto.

  induction 1; simpl; intros.

  case_rep; try congruence.
  apply wf_fvar; auto.

  case_rep.
  destruct v.
  apply wf_Var; auto.
  case_var.
  rewrite <- conv_Var.
  apply wf_Var; auto.
  apply wf_Var; auto.
  apply wf_Var; auto.

  apply wf_Term; auto.
Qed.



  


