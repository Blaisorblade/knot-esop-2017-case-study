Set Implicit Arguments.

Require Import Equality.
Require Export LNameless_Meta.


(**********************************************************************)
(** * Well-formedness in an environments *)
(**********************************************************************)

(** [envT r' r r0 E t] corresponds to the construction of
   locally-closed term [t] of type [Interpret r] with respect
   to the variable type [Interpret r0] in an environment [E]
   of type [env (Interpret r')]:

   - r' = r = r0 and no [Repr] case : [envT] corresponds to the construction
     of well-formed types in system F.

   - All parameters free in the term/type are bound in the environment.

   - It does not contain free occurrence of de Bruijn variables.
   
   - Cofinite quantification style is used in the binder case. *)

(** [envT] can be generalized as we did with de Brujin style using
   [env (Interpret r' + Interpret r')] instead of [env (Interpret r')] *)
 
Inductive envTRep r' r r0 (E:env (Interpret r')) : forall s, InterpretRep r s -> Prop :=
| env_Unit  : envTRep r0 E Unit
| env_Const : forall (s0:Rep)(T:Interpret s0),
  envTRep r0 E (Const r T)
| env_Repr  : forall (s0:Rep)(T:Interpret s0),
  @envT r' s0 r0 E T -> envTRep r0 E (Repr r T)
| env_InL   : forall s0 s1 (T:InterpretRep r s0),
  envTRep r0 E T -> envTRep r0 E (InL s1 T)
| env_InR   : forall s0 s1 (T:InterpretRep r s1),
  envTRep r0 E T -> envTRep r0 E (InR s0 T)
| env_Pair  : forall s0 s1 (T:InterpretRep r s0)(U:InterpretRep r s1),
  envTRep r0 E T -> envTRep r0 E U -> envTRep r0 E (Pair T U)
| env_Bind_REC_homo  : forall s0 (T:InterpretRep r s0) L V,
  r = r0 ->
  (forall k, k `notin` L -> envTRep r0 (k ~ V ++ E) (bsubstRep T 0 (Var r0 (inl k)))) ->
  envTRep r0 E (Bind REC tt T)
| env_Bind_REC_hetero  : forall s0 (T:InterpretRep r s0),
  r <> r0 ->
  envTRep r0 E T ->
  envTRep r0 E (Bind REC tt T)
| env_Bind_homo  : forall r1 s0 (T:InterpretRep r s0) L V,
  r1 <> REC ->
  r1 = r0 ->
  (forall k, k `notin` L -> envTRep r0 (k ~ V ++ E) (bsubstRep T 0 (Var r0 (inl k)))) ->
  envTRep r0 E (Bind r1 tt T)
| env_Bind_hetero  : forall r1 s0 (T:InterpretRep r s0),
  r1 <> REC ->
  r1 <> r0 ->
  envTRep r0 E T ->
  envTRep r0 E (Bind r1 tt T)
| env_Rec   : forall T, envT r0 E T -> envTRep r0 E (Rec T)

with envT r' r r0 (E:env (Interpret r')) : Interpret r -> Prop :=
| env_fvar : forall v U, r = r0 -> binds v U E -> envT r0 E (Var r (inl v))
| env_Var  : forall v, r <> r0 -> envT r0 E (Var r v)
| env_Term  : forall T, envTRep r0 E T -> envT r0 E (Term T).


(** [envT] implies [wfT] *)

Lemma envTRep_wfT : forall r' r r0 s (E:env (Interpret r')) (T:InterpretRep r s),
  envTRep r0 E T -> wfTRep r0 T

  with envT_wfT : forall r' r r0 (E:env (Interpret r')) (T:Interpret r),
    envT r0 E T -> wfT r0 T.
Proof.
  destruct 1; simpl; func_equal;
    [ constructor 1
      | constructor 2
      | constructor 3; apply envT_wfT with r' E; assumption
      | constructor 4; eauto using envTRep_wfT
      | constructor 5; eauto using envTRep_wfT
      | constructor 6; eauto using envTRep_wfT
      | constructor 7 with L; intros; eauto using envTRep_wfT
      | constructor 8; eauto using envTRep_wfT
      | constructor 9 with L; intros; eauto using envTRep_wfT
      | constructor 10; eauto using envTRep_wfT
      | constructor 11; eauto using envT_wfT ].
  
  destruct 1; simpl; func_equal;
    [ constructor 1; assumption
      | constructor 2; assumption
      | constructor 3; eauto using envTRep_wfT ].
Qed.

(** [conv] and [envT] *)

Lemma conv_envT : forall r' r r0 (e:r = r0)(E:env (Interpret r'))(T:Interpret r0) r1,
  envT r1 E T -> envT r1 E (conv e T).
Proof.
  intros r' r ro e; case e.
  unfold conv, eq_rect_r; tauto.
Qed.

(** [envT] implies [wf].  *)

(* bsubstRep_on_env => envTRep_wfRep *)
Lemma envTrep_wfRep : forall r' r r0 s (E:env (Interpret r'))(T:InterpretRep r s), 
  envTRep r0 E T ->
  forall k (U:Interpret r0), T = bsubstRep T k U.
Proof.
  intros; eauto using envTRep_wfT, wfTRep_wfRep.
Qed.

(* bsubst_on_env => envT_wf *)
Lemma envT_wf : forall r' r r0 (E:env (Interpret r'))(T:Interpret r), 
  envT r0 E T -> forall k (U:Interpret r0), T = bsubst T k U.
Proof.
  intros; eauto using envT_wfT, wfT_wf.
Qed.

(** [envT] binds all parameters in a term. *)

Import AtomSetImpl.

Lemma envTRep_fv : forall r' r r0 s (E:env (Interpret r')) (T:InterpretRep r s) a,
  a # E -> envTRep r0 E T -> a `notin` freevarsRep r0 T

  with envT_fv : forall r' r r0 (E:env (Interpret r')) (T:Interpret r) a,
    a # E -> envT r0 E T -> a `notin` freevars r0 T.
Proof.
  induction 2; simpl; try solve_notin; eauto.
  (* Bind_REC_homo *)
  pick fresh y for (L `union` {{ a }} `union` dom E).    
  destruct_notin.
  cut (a `notin` freevarsRep r0 (bsubstRep T 0 (Var r0 (inl y)))).
  intro HZnotin; contra HZnotin.
  auto using freevarsRep_pass_binder.
  apply H2; auto; simpl in *; solve_notin.
  (* Bind_homo *)
  pick fresh y for (L `union` {{ a }} `union` dom E).    
  destruct_notin.
  cut (a `notin` freevarsRep r0 (bsubstRep T 0 (Var r0 (inl y)))).
  intro HZnotin; contra HZnotin.
  auto using freevarsRep_pass_binder.
  apply H3; auto; simpl in *; solve_notin.

  induction 2; simpl; try solve_notin; eauto.
  (* fvar *)
  destruct (Rep_dec r r0); [idtac | solve_notin].
  intro HZin.
  rewrite (singleton_1 HZin) in H1.
  apply binds_dom_contradiction with (x:=a)(a:=U)(E:=E); auto.
  (* Var *)
  destruct (Rep_dec r r0); [destruct v | idtac]; solve_notin.
Qed.

(** [In_atoms_dec] should be somewhere else. *)
Require Import Sumbool.

Lemma In_atoms_dec : forall (x:atom) (s:atoms), x `in` s  \/ ~ x `in` s.
Proof.
  intros.
  destruct (sumbool_of_bool (mem x s)).
  left; auto using mem_2.
  right; intro; cut (mem x s = true); auto using mem_1; congruence.
Qed.

Lemma envTRep_dom_subset : forall r' r r0 s (E:env (Interpret r')) (T:InterpretRep r s),
  envTRep r0 E T -> freevarsRep r0 T [<=] dom E.
Proof.
  unfold Subset; intros.
  destruct (In_atoms_dec a (dom E)); auto.
  elim envTRep_fv with r' r r0 s E T a; auto.
Qed.

Lemma envT_dom_subset : forall r' r r0 (E:env (Interpret r')) (T:Interpret r),
  envT r0 E T -> freevars r0 T [<=] dom E.
Proof.
  unfold Subset; intros.
  destruct (In_atoms_dec a (dom E)); auto.
  elim envT_fv with r' r r0 E T a; auto.
Qed.

(** if a is fresh from E, and T is well-formed in E, then [T = T [a \ U] ]. *)

Lemma fsubstRep_fresh : forall r' r r0 s
  (E:env (Interpret r'))(T:InterpretRep r s)(U:Interpret r0) a, 
  a # E -> envTRep r0 E T -> T = fsubstRep T a U.
Proof.
  intros; apply fsubstRep_no_occur; eauto using envTRep_fv.
Qed.

Lemma fsubst_fresh : forall r' r r0 (E:env (Interpret r'))(T:Interpret r)(U:Interpret r0) a, 
  a # E -> envT r0 E T -> T = fsubst T a U.
Proof.
  intros; apply fsubst_no_occur; eauto using envT_fv.
Qed.

(** Permutation of a substitution *)

(** The lemmas below are already proved for well-formed terms
   in [LNameless_Meta_Cofin.v]. *)

Lemma bfsubstRep_permutation : forall r' r r0 r1 s
  (E:env (Interpret r')) (T:InterpretRep r s)(U:Interpret r0)(V:Interpret r1) a,
  envT r1 E U -> 
  a `notin` (freevars r0 V) ->
  bsubstRep (fsubstRep T a U) 0 V = fsubstRep (bsubstRep T 0 V) a U.
Proof.
  intros; eauto using bfsubstRep_permutation_wfT, envT_wfT.
Qed.

Lemma bfsubst_permutation : forall r' r r0 r1
  (E:env (Interpret r')) (T:Interpret r)(U:Interpret r0)(V:Interpret r1) a,
  envT r1 E U -> 
  a `notin` (freevars r0 V) ->
  bsubst (fsubst T a U) 0 V = fsubst (bsubst T 0 V) a U.
Proof.
  intros; eauto using bfsubst_permutation_wfT, envT_wfT. 
Qed.

Lemma bfsubstRep_permutation_var : forall r' r r0 r1 s
  (E:env (Interpret r'))(T:InterpretRep r s)(U:Interpret r0) a b,
  a <> b ->
  envT r1 E U -> 
  bsubstRep (fsubstRep T a U) 0 (Var r1 (inl b))
  = fsubstRep (bsubstRep T 0 (Var r1 (inl b))) a U.
Proof.
  intros; eauto using bfsubstRep_permutation_var_wfT, envT_wfT.
Qed.

Lemma bfsubst_permutation_var : forall r' r r0 r1
  (E:env (Interpret r'))(T:Interpret r)(U:Interpret r0) a b,
  a <> b ->
  envT r1 E U -> 
  bsubst (fsubst T a U) 0 (Var r1 (inl b))
  = fsubst (bsubst T 0 (Var r1 (inl b))) a U.
Proof.
  intros; eauto using bfsubst_permutation_var_wfT, envT_wfT.
Qed.


(**********************************************************************)
(** * Weakening of well-formedness  *)
(**********************************************************************)
  
Lemma extendsRep_env: forall r' r r0 s (E F:env (Interpret r')) (T:InterpretRep r s), 
  envTRep r0 E T -> extends E F -> envTRep r0 F T

  with extends_env : forall r' r r0 (E F:env (Interpret r')) (T:Interpret r), 
    envT r0 E T -> extends E F -> envT r0 F T.
Proof.
  destruct 1; simpl; intros;
    [ constructor 1
      | constructor 2
      | constructor 3; auto*
      | constructor 4; auto*
      | constructor 5; auto*
      | constructor 6; auto*
      | constructor 7 with L V; intros; auto;
        apply extendsRep_env with (E:= k ~ V ++ E); auto using extends_push
      | constructor 8; auto*
      | constructor 9 with L V; intros; auto;
        apply extendsRep_env with (E:= k ~ V ++ E); auto using extends_push
      | constructor 10; auto*
      | constructor 11; apply extends_env with E; auto ].
  
  destruct 1; auto*; intros;
    [ constructor 1 with U; auto using H0
      | constructor 2; auto*
      | constructor 3; auto* ].
Qed.

(** [uniq E] means no double occurrence of a variable in [dom E]. *)

Lemma envT_weakenRep : forall r' r r0 s (G E F:env (Interpret r'))(T : InterpretRep r s),
  envTRep r0 (E ++ G) T ->
  uniq (E ++ F ++ G) ->
  envTRep r0 (E ++ F ++ G) T.
Proof.
  intros; apply extendsRep_env with (E ++ G); auto.
  auto using extends_app_L, extends_L.
Qed.

Lemma envT_weaken : forall r' r r0 (E F G:env (Interpret r')) (T : Interpret r),
  envT r0 (E ++ G) T ->
  uniq (E ++ F ++ G) ->
  envT r0 (E ++ F ++ G) T.
Proof.
  intros; apply extends_env with (E ++ G); auto.
  auto using extends_app_L, extends_L.
Qed.

Lemma envT_weaken_left : forall r' r r0 (E F:env (Interpret r'))(T:Interpret r),
  envT r0 F T ->
  uniq (E ++ F) ->
  envT r0 (E ++ F) T.
Proof.
  do 6 intro.
  pattern (E ++ F) ; rewrite <- app_nil_1.
  pattern F at 1; rewrite <- app_nil_1.
  apply envT_weaken. 
Qed.

Lemma envT_weaken_right : forall r' r r0 (E F:env (Interpret r'))(T:Interpret r),
  envT r0 E T ->
  uniq (E ++ F) ->
  envT r0 (E ++ F) T.
Proof.
  do 6 intro.
  pattern (E ++ F) ; rewrite <- app_nil_2.
  pattern E at 1; rewrite <- app_nil_2.
  repeat rewrite app_ass.
  apply envT_weaken. 
Qed.

(** Environment Narrowing  *)

(** [envT_narrow] should be proved as in the following lemma.
   A direct proof using [dependent destruction] does not pass
   the termination checker. *)

Lemma envT_narrowRep_ : forall r' r r0 s (E:env (Interpret r')) (T:InterpretRep r s) a,
  envTRep r0 E T ->
  forall (E0 E1:env (Interpret r'))(U V:Interpret r'),
    E = E0 ++ a ~ V ++ E1 ->
    uniq (E0 ++ a ~ U ++ E1) -> 
    envTRep r0 (E0 ++ a ~ U ++ E1) T

  with envT_narrow_ : forall r' r r0 (E:env (Interpret r')) (T:Interpret r) a,
    envT r0 E T ->
    forall (E0 E1:env (Interpret r'))(U V:Interpret r'),
      E = E0 ++ a ~ V ++ E1 ->
      uniq (E0 ++ a ~ U ++ E1) -> 
      envT r0 (E0 ++ a ~ U ++ E1) T.
Proof.
  destruct 1; intros;
    [ constructor 1
      | constructor 2
      | constructor 3; apply envT_narrow_ with E V; try assumption
      | constructor 4; apply envT_narrowRep_ with E V; try assumption
      | constructor 5; apply envT_narrowRep_ with E V; assumption
      | constructor 6; apply envT_narrowRep_ with E V; assumption
      |   set (L' := dom (E0 ++ a ~ V0 ++ E1));
        constructor 7 with (L `union` L') V; intros; auto;
          destruct_notin; rewrite <- app_ass;
            apply envT_narrowRep_ with (E:= k ~ V ++ E)(V:=V0);
              [ apply H0; assumption
                | rewrite app_ass; rewrite H1; reflexivity
                | rewrite app_ass; rewrite <- app_nil_1;
                  apply uniq_insert_mid;
                    [simpl in *;  assumption | solve_notin | 
                      subst L'; repeat rewrite dom_app in *; solve_notin ] ]
      | constructor 8; auto; apply envT_narrowRep_ with E V; assumption
      |   set (L' := dom (E0 ++ a ~ V0 ++ E1));
        constructor 9 with (L `union` L') V; intros; auto;
          destruct_notin; rewrite <- app_ass;
            apply envT_narrowRep_ with (E:= k ~ V ++ E)(V:=V0);
              [ apply H1; assumption
                | rewrite app_ass; rewrite H2; reflexivity
                | rewrite app_ass; rewrite <- app_nil_1;
                  apply uniq_insert_mid;
                    [simpl in *;  assumption | solve_notin | 
                      subst L'; repeat rewrite dom_app in *; solve_notin] ]
      | constructor 10; auto; apply envT_narrowRep_ with E V; assumption
      | constructor 11; apply envT_narrow_ with E V; assumption ].

  destruct 1; intros;
    [ subst E; destruct_binds_hyp_uniq H0;
      [ constructor 1 with U; [assumption | apply binds_app_2; assumption]
        | constructor 1 with U0;
          [assumption | apply binds_app_3; apply binds_app_2; apply binds_cons_2; reflexivity]
        | constructor 1 with U;
          [assumption | apply binds_app_3; apply binds_app_3; assumption] ]
      | constructor 2; assumption
      | constructor 3; apply envT_narrowRep_ with E V; assumption ].
Qed.

Lemma envT_narrowRep : forall r' r r0 s (E0 E1:env (Interpret r'))(U V:Interpret r')
  (T:InterpretRep r s) a,
  envTRep r0 (E0 ++ a ~ V ++ E1) T ->
  uniq (E0 ++ a ~ U ++ E1) -> 
  envTRep r0 (E0 ++ a ~ U ++ E1) T.
Proof.
  intros; eauto using envT_narrowRep_.
Qed.

Lemma envT_narrow : forall r' r r0 (E0 E1:env (Interpret r'))(U V:Interpret r')
  (T:Interpret r) a,
  envT r0 (E0 ++ a ~ V ++ E1) T ->
  uniq (E0 ++ a ~ U ++ E1) -> 
  envT r0 (E0 ++ a ~ U ++ E1) T.
Proof.
  intros; eauto using envT_narrow_.
Qed.

Lemma envT_narrow_left : forall r' r r0 (E1:env (Interpret r'))(U V:Interpret r')
  (T:Interpret r) a,
  envT r0 (a ~ V ++ E1) T ->
  uniq (a ~ U ++ E1) -> 
  envT r0 (a ~ U ++ E1) T.
Proof.
  intros until 0.
  cut (envT r0 (nil ++ [(a, V)] ++ E1) T ->
   uniq (nil ++ [(a, U)] ++ E1) -> envT r0 (nil ++ [(a, U)] ++ E1) T); auto.
  eauto using envT_narrow.
Qed.

Lemma envT_narrow_right : forall r' r r0 (E0:env (Interpret r'))(U V:Interpret r')
  (T:Interpret r) a,
  envT r0 (E0 ++ a ~ V) T ->
  uniq (E0 ++ a ~ U) -> 
  envT r0 (E0 ++ a ~ U) T.
Proof.
  intros until 0.
  cut (envT r0 (E0 ++ [(a, V)] ++ nil) T ->
   uniq (E0 ++ [(a, U)] ++ nil) -> envT r0 (E0 ++ [(a, U)] ++ nil) T); auto.
  eauto using envT_narrow.
Qed.

(********************************************************************)
(** * Homogeneous cases *)
(********************************************************************)

(** The following lemmas deals with special cases where no [Repr] occurs
   in the DGP representation.
   - The term/type case in STLC

   - The type case in Fsub *)

(** Heterogeneous operations have no effect when there are no [Repr]. *)

Lemma noRepr_fsubstRep_hetero : forall r r0 s (T:InterpretRep r s) a (U:Interpret r0),
  noRepr r ->
  noRepr s ->
  r <> r0 ->
  fsubstRep T a U = T

  with noRepr_fsubst_hetero : forall r r0 (T:Interpret r) a (U:Interpret r0),
    noRepr r ->
    r <> r0 ->
    fsubst T a U = T.
Proof.
  destruct T; simpl; intros a U Hnor Hnos Hneq; try inversion Hnos;
    func_equal; try destruct q; try absurd_math; auto.
  case_rep; simpl in *; try absurd_math; auto. 

  destruct T; simpl; intros a U Hnor Hneq; func_equal; intuition auto.
  case_rep; destruct v; try case_var; intuition auto.
Qed.

Lemma noRepr_bsubstRep_hetero : forall r r0 s (T:InterpretRep r s) a (U:Interpret r0),
  noRepr r ->
  noRepr s ->
  r <> r0 ->
  bsubstRep T a U = T

  with noRepr_bsubst_hetero : forall r r0 (T:Interpret r) a (U:Interpret r0),
    noRepr r ->
    r <> r0 ->
    bsubst T a U = T.
Proof.
  destruct T; simpl; intros a U Hnor Hnos Hneq;
    try repeat case_rep; func_equal; try destruct q; intuition auto.


  destruct T; simpl; intros a U Hnor Hneq; func_equal; intuition auto.
  case_rep; destruct v; try case_var; intuition auto.
Qed.

Lemma noRepr_freevarsRep_hetero : forall r r0 s (T:InterpretRep r s),
  noRepr r ->
  noRepr s ->
  r <> r0 ->
  freevarsRep r0 T [<=] {}

  with noRepr_freevars_hetero : forall r r0 (T:Interpret r),
    noRepr r ->
    r <> r0 ->
    freevars r0 T [<=] {}.
Proof.
  destruct T; simpl; intros Hnos Hnor Hneq; intuition auto; intuition.
  case_rep; intuition auto.

  destruct T; simpl; intros Hnos Hneq; intuition auto; intuition.
  case_rep; destruct v; try case_var; intuition auto; intuition.
Qed.

(** Heterogeneous well-formedness when no [Repr]. *)

Lemma noRepr_wfTRep_hetero : forall r r0 s (T:InterpretRep r s),
  noRepr r ->
  noRepr s ->
  r <> r0 ->
  wfTRep r0 T

  with noRepr_wfT_hetero : forall r r0 (T:Interpret r),
    noRepr r ->
    r <> r0 ->
    wfT r0 T.
Proof.
  destruct T; simpl; intros Hnos Hnor Hneq;
    [ constructor 1
      | constructor 2
      | elim Hnor
      | inversion Hnor; constructor 4; auto using noRepr_wfTRep_hetero
      | inversion Hnor; constructor 5; auto using noRepr_wfTRep_hetero
      | inversion Hnor; constructor 6; auto using noRepr_wfTRep_hetero
      | q_destruct; case_rep; [idtac | absurd_math]; rewrite e; constructor 8; auto
      | constructor 11; auto ].

  destruct T; simpl; intros Hnos Hneq;
    [constructor 2; auto
      | constructor 3; auto ].
Qed.

Lemma noRepr_wfRep_hetero : forall r r0 s (T:InterpretRep r s),
  noRepr r ->
  noRepr s ->
  r <> r0 ->
  wfRep r0 T

  with noRepr_wf_hetero : forall r r0 (T:Interpret r),
    noRepr r ->
    r <> r0 ->
    wf r0 T.
Proof.
  unfold wfRep; destruct T; simpl; intros Hnor Hnos Hneq k U;
    [ reflexivity
      | reflexivity
      | inversion Hnos
      | inversion Hnos; f_equal; apply noRepr_wfRep_hetero; try assumption
      | inversion Hnos; f_equal; apply noRepr_wfRep_hetero; try assumption
      | inversion Hnos; f_equal; apply noRepr_wfRep_hetero; try assumption
      | q_destruct; repeat case_rep; f_equal;
        apply noRepr_wfRep_hetero; intuition (try assumption)
      | inversion Hnos; f_equal; apply noRepr_wf_hetero; try assumption ].

  unfold wf; destruct T; simpl; intros Hnor Hneq k U;
    [ case_rep; destruct v; simpl; try case_var; intuition congruence
      | f_equal; apply noRepr_wfRep_hetero; assumption ].
Qed.

Lemma noRepr_envTRep_hetero : forall r' r r0 s (E:env (Interpret r'))(T:InterpretRep r s),
  noRepr r ->
  noRepr s ->
  r <> r0 ->
  envTRep r0 E T

  with noRepr_envT_hetero : forall r' r r0 (E:env (Interpret r'))(T:Interpret r),
    noRepr r ->
    r <> r0 ->
    envT r0 E T.
Proof.
  destruct T; simpl; intros Hnos Hnor Hneq;
    [ constructor 1
      | constructor 2
      | elim Hnor
      | inversion Hnor; constructor 4; auto using noRepr_envTRep_hetero
      | inversion Hnor; constructor 5; auto using noRepr_envTRep_hetero
      | inversion Hnor; constructor 6; auto using noRepr_envTRep_hetero
      | q_destruct; case_rep; [idtac | absurd_math];
        rewrite e; constructor 8; auto
      | constructor 11; auto ].

  destruct T; simpl; intros Hnos Hneq;
    [ constructor 2; auto
      | constructor 3; auto ].
Qed.

Lemma notin_neq : forall A (E E0:env A) (T:A) a b,
  b # (E ++ a ~ T ++ E0) -> a <> b.
Proof.
  intros; repeat rewrite dom_app in *.
  destruct_notin; simpl_alist in *; solve_notin.
Qed.

(** Substitution preserves the well-formedness in an environment.  *)

(** Preparing Lemma *)

(* envT_fsubstRep => noRepr_envT_fsubstRep
   envT_fsubst => noRepr_envT_fsubstR *)
Lemma noRepr_envT_fsubstRep_ : forall r' r r0 r1 s (E:env (Interpret r')) (T:InterpretRep r s),
  envTRep r1 E T ->
  noRepr r ->
  noRepr s ->
  r = r0 ->
  forall (E0 E1:env (Interpret r')) (P:Interpret r') (Q:Interpret r0) a,
    E = E0 ++ a ~ P ++ E1 ->
    envT r1 E1 Q ->
    uniq (map (fun U => fsubst U a Q) E0 ++ E1) ->
    envTRep r1 (map (fun U => fsubst U a Q) E0 ++ E1) (fsubstRep T a Q)

  with noRepr_envT_fsubst_ : forall r' r r0 r1 (E:env (Interpret r')) (T:Interpret r),
    envT r1 E T ->
    noRepr r ->
    r = r0 ->
    forall (E0 E1:env (Interpret r')) (P:Interpret r')(Q:Interpret r0) a,
      E = E0 ++ a ~ P ++ E1 ->
      envT r1 E1 Q ->
      uniq (map (fun U => fsubst U a Q) E0 ++ E1) ->
      envT r1 (map (fun U => fsubst U a Q) E0 ++ E1) (fsubst T a Q).
Proof.
  destruct 1; simpl; intros Hnor Hnos; intros;
    [ constructor 1
      | constructor 2
      | elim Hnos
      | constructor 4; apply noRepr_envT_fsubstRep_ with E P; inversion Hnos; assumption
      | constructor 5; apply noRepr_envT_fsubstRep_ with E P; inversion Hnos; assumption
      | constructor 6; apply noRepr_envT_fsubstRep_ with E P; inversion Hnos; assumption
      | idtac
      | idtac
      | idtac
      | idtac
      | constructor 11; apply noRepr_envT_fsubst_ with E P; assumption ].

  (* Bind_REC_homo *)
  clear noRepr_envT_fsubst_.
  simpl_alist in *.
  set (L' := dom (E0 ++ a ~ P ++ E1)).
  set (f := fun U : Interpret r' => fsubst U a Q) in *.
  constructor 7 with (L `union` L')(fsubst V a Q); intros; auto.
  subst L'.
  destruct_notin.
  rewrite bfsubstRep_permutation_var_wfT; eauto using envT_wfT, notin_neq.
  assert (k ~ fsubst V a Q ++ map f E0 ++ E1 =
    map f ((k ~ V) ++ E0) ++ E1) as Hmap1; auto.
  rewrite Hmap1.
  apply noRepr_envT_fsubstRep_ with (E:=k ~ V ++ E) (P:=P); try assumption;
    [ rewrite H2 in *; apply H0; try assumption
      | rewrite H2; solve_uniq
      | simpl; apply uniq_cons_3;
        [assumption | repeat rewrite dom_app in *; rewrite dom_map; solve_notin ] ].
  (* Bind_REC_hetero *)
  constructor 8; auto; apply noRepr_envT_fsubstRep_ with E P; assumption.
  (* Bind_homo *)
  case_rep; [idtac | absurd_math].
  clear noRepr_envT_fsubst_.
  simpl_alist in *.
  set (L' := dom (E0 ++ a ~ P ++ E1)).
  set (f := fun U : Interpret r' => fsubst U a Q) in *.
  constructor 9 with (L `union` L')(fsubst V a Q); intros; auto.
  subst L'.
  destruct_notin.
  rewrite bfsubstRep_permutation_var_wfT; eauto using envT_wfT, notin_neq.
  assert (k ~ fsubst V a Q ++ map f E0 ++ E1 =
    map f ((k ~ V) ++ E0) ++ E1) as Hmap1; auto.
  rewrite Hmap1.
  apply noRepr_envT_fsubstRep_ with (E:=k ~ V ++ E) (P:=P); try assumption;
    [ rewrite H3 in *; apply H1; try assumption
      | rewrite H3; solve_uniq
      | simpl; apply uniq_cons_3;
        [assumption | repeat rewrite dom_app in *; rewrite dom_map; solve_notin] ].  
  (* Bind_REC_hetero *)
  case_rep;
  [ constructor 10; auto; apply noRepr_envT_fsubstRep_ with E P; assumption | absurd_math].

  destruct 1; simpl; intros;
    [ clear noRepr_envT_fsubst_; clear noRepr_envT_fsubstRep_;
      destruct (Rep_dec r r0); simpl; try contradiction;
        case_var;
        [ apply conv_envT; apply extends_env with E1;
          [auto using conv_envT | apply extends_L; assumption ]
          | subst E; destruct_binds_hyp H0;
            [ set (f := fun U0 : Interpret r' => fsubst U0 a Q);
              apply extends_env with (map f E0);
                [ constructor 1 with (f U); [assumption | apply binds_map_2; assumption]
                  | apply extends_R ]
              | contradict n; reflexivity
              | apply extends_env with E1;
                [constructor 1 with U | apply extends_L]; assumption ] ]
      | clear noRepr_envT_fsubstRep_; clear noRepr_envT_fsubst_;
        case_rep; try contradiction; destruct v;
          [ case_var;
            [ apply conv_envT; 
              apply extends_env with E1; [auto using conv_envT | apply extends_L; assumption ]
              | constructor 2; assumption ]
            | constructor 2; assumption ]  
      | constructor 3; apply noRepr_envT_fsubstRep_ with E P; auto ].  
Qed.

Lemma noRepr_envT_fsubstRep : forall r' r r1 s (E0 E1:env (Interpret r')) (T:InterpretRep r s)
  (P:Interpret r') (Q:Interpret r) a,
  envTRep r1 (E0 ++ a ~ P ++ E1) T ->
  noRepr r ->
  noRepr s ->
  envT r1 E1 Q ->
  uniq (map (fun U => fsubst U a Q) E0 ++ E1) ->
  envTRep r1 (map (fun U => fsubst U a Q) E0 ++ E1) (fsubstRep T a Q).
Proof.
  intros; eauto using noRepr_envT_fsubstRep_.
Qed.

Lemma noRepr_envT_fsubst : forall r' r r1 (E0 E1:env (Interpret r')) (T:Interpret r)
  (P:Interpret r')(Q:Interpret r) a,
  envT r1 (E0 ++ a ~ P ++ E1) T ->
  noRepr r ->
  envT r1 E1 Q ->
  uniq (map (fun U => fsubst U a Q) E0 ++ E1) ->
  envT r1 (map (fun U => fsubst U a Q) E0 ++ E1) (fsubst T a Q).
Proof.
  intros; eauto using noRepr_envT_fsubst_.
Qed.


(********************************************************************)
(** * Well-formed environments *)
(********************************************************************)

(** Well-formed environments contain only well-formed types. *)

Inductive wf_env (r:Rep): env (Interpret r) -> Prop :=
| wf_env_empty : wf_env empty_env
| wf_env_cons   : forall E (a:atom) T,
  wf_env E -> envT r E T -> a # E -> wf_env (a ~ T ++ E).

(** No duplicated keys for well-formed environments *)

Lemma uniq_from_wf_env : forall r (E:env (Interpret r)),
  wf_env E -> uniq E.
Proof.
  induction 1; unfold empty_env; auto.
Qed.

(** Every type in a well-formed environment is well-formed. *)

Lemma wf_env_binds : forall r (E:env (Interpret r)) a T, 
  wf_env E -> binds a T E -> envT r E T.
Proof.
  induction 1; intro Has;
    [ elim Has
      | inversion Has as [Has1 | ];
        [ injection Has1; intros; subst a T0; clear Has1;
          apply extends_env with E; firstorder
          | apply extends_env with E; firstorder ] ].
Qed.

(** Extraction from a well-formed environment *)

Lemma envT_from_wf_env : forall r (E E0:env (Interpret r)) a T,
  wf_env (E ++ a ~ T ++ E0) -> envT r E0 T.
Proof.
  induction E as [| (b,U)]; simpl; intros E0 a T H;
    [ inversion H; auto
      | simpl_alist in *; inversion H; apply IHE with (a:=a); assumption ].
Qed.

Lemma envT_from_wf_env_left : forall r (E:env (Interpret r)) a T,
  wf_env (a ~ T ++ E) -> envT r E T.
Proof.
  intros; inversion H; auto.
Qed.

(** [uniq] depends only on the variables, not on types. *)

Lemma uniq_dom_only : forall A (E F: env A) X U V,
  uniq (E ++ X ~ U ++ F) -> uniq (E ++ X ~ V ++ F).
Proof.
  intros; solve_uniq.
Qed.

(** Well-formedness of an environment does not depend
   on the types. *)

Lemma wf_env_narrow : forall r (E F: env (Interpret r)) U V a,
  wf_env (E ++ a ~ U ++ F) ->
  envT r F V ->
  wf_env (E ++ a ~ V ++ F).
Proof.
  induction E as [|(b,T)]; simpl; intros; simpl_alist in *; inversion H.
    (* nil *)
  constructor 2; auto.
    (* cons *)
  constructor 2; auto.
  apply IHE with U; auto.
  apply envT_narrow with (V:=U); auto.
  apply uniq_dom_only with U; auto using uniq_from_wf_env.
  simpl_alist in *; solve_notin.
Qed.

Lemma wf_env_narrow_left : forall r (F: env (Interpret r)) U V a,
  wf_env (a ~ U ++ F) ->
  envT r F V ->
  wf_env (a ~ V ++ F).
Proof.
  do 5 intro.
  generalize (@wf_env_narrow r nil); simpl; firstorder.
Qed.

(** Substitution preserves the well-formedness of an environemt *)

(* wf_env_fsubst = noRepr_wf_env_fsubst *)
Lemma noRepr_wf_env_fsubst : forall r (E F:env (Interpret r)) (P:Interpret r)(Q:Interpret r) a,
  wf_env (E ++ a ~ P ++ F) ->
  noRepr r ->
  envT r F Q ->
  wf_env (map (fun U => fsubst U a Q) E ++ F).
Proof.
  induction E as [| (a,V)]; simpl; intros; 
    dependent destruction H; auto.
  simpl_alist.
  apply wf_env_cons;
    [ apply IHE with P; auto
      | apply noRepr_envT_fsubst with P; auto;
        apply map_uniq_5 with (a:=a0)(T:=P);
          simpl_alist in *;         
          apply uniq_from_wf_env; auto
      | simpl_alist in *; solve_notin ].
Qed.




