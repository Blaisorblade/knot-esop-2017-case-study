Set Implicit Arguments.

Require Import Arith.
Require Import Omega.
Require Import deBruijn_Isomorphism.
Require Import deBruijn_Fsub_Iso.
Require Import dB_Template_Two_Sort.


(** Reference: #<a href="https://alliance.seas.upenn.edu/~plclub/cgi-bin/poplmark/index.php?title=Submission_by_J%C3%83%C2%A9r%C3%83%C2%B4me_Vouillon">#J. Vouillon's POPL solution#</a># using de Bruijn indices for parts 1A + 2A *)

(*************************************************************************)
(** * [Progress] and [Preservation] for System F with subtyping *)
(*************************************************************************)

(** Library Import: Having defined an isomorphism between the syntax of
   Fsub and a DGP representation,
   the first thing to do is to import a suitable generic library
   - In case of Fsub, [dBTemplate] can be used.

   - In the generic library, many of the generic properties
     about substitution, environments are already proved *)

(** Module M_tt, M_yt, M_yy, are M_ty are already defined in dB_Template_Two_Sort.v. *)

(*************************************************************************)
(** * Main Formalization *)
(*************************************************************************)

(** [typ] and [term] are already defined in [deBruijn_Fsub_Iso.v]:
<<   
Inductive typ : Set :=
| tvar : nat -> typ
| top : typ
| arrow  : typ -> typ -> typ
| all : typ -> typ -> typ.

Inductive term : Set :=
| var : nat -> term
| abs : typ -> term -> term
| app : term -> term -> term
| tabs : typ -> term -> term
| tapp : term -> typ -> term.
>> *)

(** A lemma about [Twf_typ] which is a generic definition for well-formedness
   of types in an environment. *)

Lemma twf_nil_top : M_yt.Twf_typ nil top.
Proof.
  unfold M_yt.Twf_typ; simpl; auto.
Qed.

Hint Resolve twf_nil_top : iso.

(** Well-formed terms in an environment  *)

Fixpoint wf_term (e : M_yt.TEnv) (t : term) {struct t} : Prop :=
  match t with
    | var x      => Tget_right e x <> None
    | abs T1 t2  => M_yt.Twf_typ e T1  /\ wf_term ((inr T1)::e) t2
    | app t1 t2  =>  wf_term e t1 /\ wf_term e t2
    | tabs T1 t2 => M_yt.Twf_typ e T1  /\ wf_term ((inl T1)::e) t2
    | tapp t1 T2 =>  wf_term e t1 /\ M_yt.Twf_typ e T2
  end.

(** Subtyping relation *)

Inductive sub : M_yt.TEnv -> typ -> typ -> Prop :=
| SA_Top :
  forall (e : M_yt.TEnv) (S : typ), M_yt.Twf_env e -> M_yt.Twf_typ e S -> sub e S top
| SA_Refl_TVar :
  forall (e : M_yt.TEnv) (X : nat),
    M_yt.Twf_env e -> M_yt.Twf_typ e (tvar X) -> sub e (tvar X) (tvar X)
| SA_Trans_TVar :
  forall (e : M_yt.TEnv) (X : nat) (T U : typ),
    Tget_left e X = Some U -> sub e U T -> sub e (tvar X) T
| SA_Arrow :
  forall (e : M_yt.TEnv) (T1 T2 S1 S2 : typ),
    sub e T1 S1 -> sub e S2 T2 -> sub e (arrow S1 S2) (arrow T1 T2)
| SA_All :
  forall (e : M_yt.TEnv) (T1 T2 S1 S2 : typ),
    sub e T1 S1 -> sub ((inl T1)::e) S2 T2 -> sub e (all S1 S2) (all T1 T2).

(** Typing relation *)

Inductive typing : M_yt.TEnv -> term -> typ -> Prop :=
| T_Var :
  forall (e : M_yt.TEnv) (x : nat) (T : typ),
    M_yt.Twf_env e -> Tget_right e x = Some T -> typing e (var x) T
| T_Abs :
  forall (e : M_yt.TEnv) (t : term) (T1 T2 : typ),
    typing ((inr T1)::e) t T2 ->
    typing e (abs T1 t) (arrow T1 T2)
| T_App :
  forall (e : M_yt.TEnv) (t1 t2 : term) (T11 T12 : typ),
    typing e t1 (arrow T11 T12) ->
    typing e t2 T11 -> typing e (app t1 t2) T12
| T_Tabs :
  forall (e : M_yt.TEnv) (t : term) (T1 T2 : typ),
    typing ((inl T1)::e) t T2 -> typing e (tabs T1 t) (all T1 T2)
| T_Tapp :
  forall (e : M_yt.TEnv) (t1 : term) (T11 T12 T2 : typ),
    typing e t1 (all T11 T12) ->
    sub e T2 T11 -> typing e (tapp t1 T2) (M_yy.Tsubst T12 0 T2)
| T_Sub :
  forall (e : M_yt.TEnv) (t : term) (T1 T2 : typ),
    typing e t T1 -> sub e T1 T2 -> typing e t T2.

(** Reduction rules *)

Definition value (t : term) :=
  match t with
    | abs _ _  => True
    | tabs _ _ => True
    | _        => False
  end.

Inductive ctx : Set :=
  c_hole    : ctx
| c_appfun  : ctx -> term -> ctx
| c_apparg  : forall (t : term), value t -> ctx -> ctx
| c_typefun : ctx -> typ -> ctx.


Fixpoint ctx_app (c : ctx) (t : term) {struct c} : term :=
  match c with
    c_hole           => t
    | c_appfun c' t'   => app (ctx_app c' t) t'
    | c_apparg t' _ c' => app t' (ctx_app c' t)
    | c_typefun c' T   => tapp (ctx_app c' t) T
  end.

Inductive red : term -> term -> Prop :=
| E_AppAbs :
  forall (t11 : typ) (t12 t2 : term),
    value t2 -> red (app (abs t11 t12) t2) (M_tt.Tsubst t12 0 t2)
| E_TappTabs :
  forall (t11 t2 : typ) (t12 : term),
    red (tapp (tabs t11 t12) t2) (M_yt.Tsubst t12 0 t2)
| E_Ctx :
  forall (c : ctx) (t1 t1' : term),
    red t1 t1' -> red (ctx_app c t1) (ctx_app c t1').

(** Subtyping relation well-formedness *)

Lemma sub_wf :
  forall (e : M_yt.TEnv) (T U : typ),
    sub e T U -> M_yt.Twf_env e /\ M_yt.Twf_typ e T /\ M_yt.Twf_typ e U.
Proof.
  intros e T U H; induction H;
    repeat split; trivial; try tauto.
  gsimpl; gcase;
  assert ([[[e]]] > X);
    [ apply Tget_left_some_gt with (U:=U) (U':=top); auto with iso
      | omega ].
Qed.

(** Reflexivity of subtyping *)

Lemma sub_reflexivity :
  forall (e : M_yt.TEnv) (T : typ), M_yt.Twf_env e -> M_yt.Twf_typ e T -> sub e T T.
Proof.
  intros e T; gen e.
  induction T; intros e H1 H2;
    [ apply SA_Refl_TVar; trivial
      | apply SA_Top; trivial
      | apply SA_Arrow;
        [ exact (IHT1 _ H1 (proj1 H2))
          | exact (IHT2 _ H1 (proj2 H2)) ]
      | apply SA_All;
        [ exact (IHT1 _ H1 (proj1 H2))
          | apply IHT2 with (2 := (proj2 H2));
            gsimpl; destruct H2; split; auto ] ].
Qed.


(** Weakening for subtyping *)

Open Scope nat_scope.

Lemma sub_weakening_left_ind :
  forall (e e' : M_yt.TEnv) (X : nat) (U V : typ),
    Tinsert_left X e e' -> sub e U V -> sub e' (M_yy.Tshift X U) (M_yy.Tshift X V).
Proof.
  intros e e' X U V H1 H2; gen X e' H1.
  induction H2; intros X' e' H1; gsimpl;
    [ apply SA_Top;
      [ exact (Tinsert_left_wf_env top twf_nil_top H1 H)
        | exact (Tinsert_left_wf_typ _ top twf_nil_top H1 H0) ]
      | apply SA_Refl_TVar;
        [ exact (Tinsert_left_wf_env top twf_nil_top H1 H)
          | exact (Tinsert_left_wf_typ _ top twf_nil_top H1 H0) ]
      | apply SA_Trans_TVar with (2 := (IHsub X' e' H1));
        case (le_gt_dec X' X); intro H3;
          [ rewrite Tget_left_insert_left_ge with (2 := H1) (3 := H3); auto with iso;
            rewrite H; trivial
            | rewrite Tget_left_insert_left_lt with (2 := H1) (3 := H3); auto with iso;
              rewrite H; trivial
          ] 
      | apply SA_Arrow; auto
      | apply SA_All; auto;
        exact (IHsub2 (S X') _ (Til_left T1 H1)) ].
Qed.

Lemma sub_weakening_left :
  forall (e : M_yt.TEnv) (T U V : typ),
    M_yt.Twf_typ e V -> sub e T U -> sub ((inl V)::e) (M_yy.Tshift 0 T) (M_yy.Tshift 0 U).
Proof.
  intros e T U V H0 H; apply sub_weakening_left_ind with (2 := H);
    apply Til_here; trivial.
Qed.

Lemma sub_extensionality :
  forall (e e' : M_yt.TEnv) (U V : typ),
    (forall (X : nat), (Tget_left e X) = (Tget_left e' X)) -> M_yt.Twf_env e' ->
    sub e U V -> sub e' U V.
Proof.
  intros e e' U V H0 H1 H2; gen e' H0 H1.
  induction H2; intros e' H3 H1;
    [ apply SA_Top; trivial; exact (Twf_typ_extensionality _ _ _ H3 H0)
      | apply SA_Refl_TVar; trivial; exact (Twf_typ_extensionality _ _ _ H3 H0)
      | rewrite H3 in H; apply SA_Trans_TVar with (1 := H); auto
      | apply SA_Arrow; auto
      | apply SA_All; auto;
        apply IHsub2 with (e' := ((inl T1)::e'));
          [ intro X; induction X; simpl; trivial;
            generalize (H3 X);intro;
              rewrite H; auto
            | simpl; split; trivial;
              apply Twf_typ_extensionality with (1 := H3);
                exact (proj1 (proj2 (sub_wf H2_))) ] ].
Qed.

Lemma sub_weakening_right_ind :
  forall (e : M_yt.TEnv) (x : nat) (U V : typ),
    M_yt.Twf_env e -> sub (M_yt.Tremove_right e x) U V -> sub e U V.
Proof.
  intros e x U V H1; apply sub_extensionality; trivial.
  intro X; apply sym_eq; apply Tget_left_remove_right.
Qed.

Lemma sub_weakening_right :
  forall (e : M_yt.TEnv) (T U V : typ),
    M_yt.Twf_typ e V -> sub e T U -> sub ((inr V)::e) T U.
Proof.
  intros e T U V H1 H2; apply sub_extensionality with e; trivial.
  simpl; split; trivial; exact (proj1 (sub_wf H2)).
Qed.


(** Relation "E' is a narrow of E"

   The environments [E,X <: Q,E'] and [E,X<:P,E'] are in a narrowing relation
   if [E |- P <: Q]. *)

Inductive narrow : nat -> M_yt.TEnv -> M_yt.TEnv -> Prop :=
  narrow_0 :
  forall (e : M_yt.TEnv) (T T' : typ),
    sub e T' T -> narrow 0 ((inl T)::e) ((inl T')::e)
| narrow_extend_left :
  forall (e e' : M_yt.TEnv) (T : typ) (X : nat),
    M_yt.Twf_typ e' T -> narrow X e e' ->
    narrow (S X) ((inl T)::e) ((inl T)::e')
| narrow_extend_right :
  forall (e e' : M_yt.TEnv) (T : typ) (X : nat),
    M_yt.Twf_typ e' T -> narrow X e e' -> narrow X ((inr T)::e) ((inr T)::e').

Lemma get_left_narrow_ne :
  forall (X X' : nat) (e e' : M_yt.TEnv),
    narrow X e e' -> X' <> X -> Tget_left e X' = Tget_left e' X'.
Proof.
  intros n n' e e' H; gen n'; induction H; intros n' H1;
    [ induction n'; trivial; case H1; trivial
      | destruct n'; trivial; simpl; rewrite IHnarrow; auto
      | apply IHnarrow; auto
    ].
Qed.

Lemma get_left_narrow_eq :
  forall (X : nat) (e e' : M_yt.TEnv),
    narrow X e e' ->
    exists T, exists T',
      Tget_left e X = Some T /\ Tget_left e' X = Some T' /\ sub e' T' T.
Proof.
  intros n e e' H; induction H;
    [ exists (M_yy.Tshift 0 T); exists (M_yy.Tshift 0 T'); repeat split;
      apply sub_weakening_left; trivial; exact (proj1 (proj2 (sub_wf H)))
      | generalize IHnarrow; intros (Q, (P, (H1, (H2, H3))));
        exists (M_yy.Tshift 0 Q); exists (M_yy.Tshift 0 P); simpl; repeat split;
          [ induction (Tget_left e X); try discriminate; inversion H1;
            gsimpl; auto
            | induction (Tget_left e' X); try discriminate; inversion H2;
              gsimpl; auto
            | apply sub_weakening_left; trivial ]
      | generalize IHnarrow; intros (Q, (P, (H1, (H2, H3))));
        exists Q; exists P; repeat split; trivial;
          apply sub_weakening_right; trivial
    ].
Qed.

Lemma get_right_narrow :
  forall (X x' : nat) (e e' : M_yt.TEnv),
    narrow X e e' -> Tget_right e x' = Tget_right e' x'.
Proof.
  intros n n' e e' H; gen n'; induction H;
    [ trivial
      | simpl; intros n';
        generalize (IHnarrow n'); intro;
          rewrite H1; auto
      | simpl; induction n';
        [ trivial
          | apply IHnarrow ] ].
Qed.

Lemma narrow_wf_typ :
  forall (e e' : M_yt.TEnv) (T : typ) (X : nat),
    narrow X e e' -> M_yt.Twf_typ e T -> M_yt.Twf_typ e' T.
Proof.
  intros e e' T n H1 H2; apply Twf_typ_env_weaken with (2 := H2); intros n' H3.
  case (eq_nat_dec n' n);
    [ intros E; rewrite E in H3;
      generalize (get_left_narrow_eq H1);
        intros (Q, (P, (H4, (H5, H6))));
          rewrite H3 in H5; discriminate
      | intro H4; rewrite (get_left_narrow_ne H1 H4); auto ].
Qed.

Lemma narrow_wf_env :
  forall (e e' : M_yt.TEnv) (X : nat),
    narrow X e e' -> M_yt.Twf_env e -> M_yt.Twf_env e'.
Proof.
  intros e e' n H; induction H; simpl;
    [ intros (H1, H2); split; auto;
      exact (proj1 (proj2 (sub_wf H)))
      | intros (H1, H2); split;
        [auto | apply IHnarrow; auto]
      | intros (H1, H2); split;
        [auto | apply IHnarrow; auto] ].
Qed.

(** Transitivity of subtyping *)

Definition transitivity_prop (Q : typ) :=
  forall (e : M_yt.TEnv) (S T : typ), sub e S Q -> sub e Q T -> sub e S T.

Definition narrowing_prop (Q : typ) :=
  forall (e e' : M_yt.TEnv) (X : nat) (S T : typ),
    narrow X e e' -> Tget_left e X = Some Q ->
    sub e S T -> sub e' S T.

Lemma transitivity_case :
  forall Q : typ,
    (forall Q' : typ,
      M_yt.Ysize Q' < M_yt.Ysize Q -> transitivity_prop Q' /\ narrowing_prop Q') ->
    transitivity_prop Q.
Proof.
  intros Q H e S T H1 H2; induction H1;
    [ inversion_clear H2; apply SA_Top; trivial
      | trivial
      | exact (SA_Trans_TVar _ H0 (IHsub H H2))
      | inversion_clear H2;
        [ apply SA_Top; trivial; gsimpl; split;
          [ apply (proj2 (proj2 (sub_wf H1_)))
            | apply (proj1 (proj2 (sub_wf H1_0))) ]
          | apply SA_Arrow;
            [ assert (H5 : M_yt.Ysize T1 < M_yt.Ysize (arrow T1 T2));
              [ gsimpl; unfold lt; apply le_n_S; apply le_max_l 
                | generalize (H _ H5); intros (H6, _); exact (H6 _ _ _ H0 H1_)]
              | assert (H5 : M_yt.Ysize T2 < M_yt.Ysize (arrow T1 T2));
                [ gsimpl; unfold lt; apply le_n_S; apply le_max_r
                  | generalize (H _ H5); intros (H6, _); exact (H6 _ _ _ H1_0 H1)] ] ]
      | inversion_clear H2;
        [ apply SA_Top; trivial;
          gsimpl; split;
            [ apply (proj2 (proj2 (sub_wf H1_)))
              | apply (proj1 (proj2 (sub_wf H1_0)))]
          | assert (H5 : M_yt.Ysize T1 < M_yt.Ysize (all T1 T2));
            [ gsimpl; unfold lt; apply le_n_S; apply le_max_l
              | apply SA_All;
                [ generalize (H _ H5); intros (H6, _); exact (H6 _ _ _ H0 H1_)
                  | assert (H5' : M_yt.Ysize (M_yy.Tshift 0 T1) < M_yt.Ysize (all T1 T2));
                    [ rewrite noRepr_Yshift_preserves_Ysize; auto with iso
                      | generalize (H _ H5'); intros (_, H6);
                        assert (H7 := narrow_0 H0);
                          assert (H7' : Tget_left ((inl T1)::e) 0 = Some (M_yy.Tshift 0 T1));
                            [ trivial
                              | assert (H8 := H6 _ _ _ _ _ H7 H7' H1_0);
                                assert (H9 : M_yt.Ysize T2 < M_yt.Ysize (all T1 T2));
                                  [ gsimpl; unfold lt; apply le_n_S;
                                    assert (H9:= le_max_r (size (Iso_typ.From T1)) (S (size (Iso_typ.From T2))));
                                      omega
                                    | assert (G1 := proj1 (H _ H9));
                                      exact (G1 ((inl T0)::e) _ _ H8 H1) ] ] ] ] ] ] ].
Qed.

Lemma narrowing_case :
  forall Q : typ,
    (forall Q' : typ, M_yt.Ysize Q' = M_yt.Ysize Q -> transitivity_prop Q') ->
    narrowing_prop Q.
Proof.
  intros Q H2 e e' n T1 T2 H3 H4 H5; gen e' n H3 H4; 
    gen Q H2; induction H5; intros Q H2 e' n H3 H4;
      [ apply SA_Top;
        [ exact (narrow_wf_env H3 H)
          | exact (narrow_wf_typ _ H3 H0) ]
        | apply SA_Refl_TVar;
          [ exact (narrow_wf_env H3 H)
            | exact (narrow_wf_typ _ H3 H0) ]
        | case (eq_nat_dec X n);
          [ intro E; rewrite E in H; rewrite E; clear X E;
            assert (H4' := IHsub _ H2 _ _ H3 H4);
              rewrite H in H4; injection H4; intro E; rewrite E in H4';
                apply (H2 _ (refl_equal (M_yt.Ysize Q))) with (2 := H4');
                  rewrite <- E;
                    generalize (get_left_narrow_eq H3);
                      intros (T1, (T2, (H6, (H7, H8))));
                        rewrite H in H6; injection H6;
                          intro E1; rewrite <- E1 in H8;
                            apply SA_Trans_TVar with (2 := H8); trivial
            | intro H6; apply SA_Trans_TVar with (2 := IHsub _ H2 _ _ H3 H4);
              rewrite <- (get_left_narrow_ne H3 H6); trivial ]
        | apply SA_Arrow; eauto
        | apply SA_All;
          [ eauto
            | apply IHsub2 with (Q := M_yy.Tshift 0 Q) (n := (S n));
              [ intros Q' E; apply H2; rewrite E; apply noRepr_Yshift_preserves_Ysize; auto with iso
                | apply narrow_extend_left with (2 := H3);
                  apply narrow_wf_typ with (1 := H3);
                    exact (proj1 (proj2 (sub_wf H5_)))
                | simpl; rewrite H4; trivial ] ] ].
Qed.

Lemma transitivity_and_narrowing :
  forall Q : typ, transitivity_prop Q /\ narrowing_prop Q.
Proof.
  assert (H : forall (n : nat) (Q : typ),
    M_yt.Ysize Q < n -> transitivity_prop Q /\ narrowing_prop Q);
  [ induction n;
    [ intros Q H; assert False; [ omega | contradiction ]
      | intros Q H; case (le_lt_or_eq _ _ H);
        [ intro H'; apply IHn; omega
          | intro E; injection E; clear E; intro E; rewrite <- E in IHn;
            assert
              (H1 : forall Q' : typ, M_yt.Ysize Q' = M_yt.Ysize Q -> transitivity_prop Q');
              [ intros Q' E1; rewrite <- E1 in IHn; apply transitivity_case;
                trivial
                | split; [ apply H1; trivial | apply narrowing_case; trivial ] ] ] ]
    | intro Q; apply (H (S (M_yt.Ysize Q))); omega ].
Qed.

Lemma sub_transitivity :
  forall (e : M_yt.TEnv) (T U V : typ), sub e T U -> sub e U V -> sub e T V.
Proof.
  intros e T U; apply (proj1 (transitivity_and_narrowing U)).
Qed.

Lemma sub_narrowing :
  forall (e e' : M_yt.TEnv) (X : nat) (S T : typ),
    narrow X e e' -> sub e S T -> sub e' S T.
Proof.
  intros e e' n S T H1 H2;
    generalize (get_left_narrow_eq H1); intros (Q, (P, (H3, _)));
      exact (proj2 (transitivity_and_narrowing Q) _ _ _ _ _ H1 H3 H2).
Qed.


(** Substitution of a type variable in an environment
   This corresponds to the environment operation
<<
E, X <: T, E'  |-->  E, [X|->T']E',
>>
   assuming that [E |- T' <: T]. *)

Inductive env_subst : nat -> typ -> M_yt.TEnv -> M_yt.TEnv -> Prop :=
  es_here :
  forall (e : M_yt.TEnv) (T T' : typ),
    sub e T' T -> env_subst 0 T' ((inl T)::e) e
| es_right :
  forall (X : nat) (T T' : typ) (e e' : M_yt.TEnv),
    env_subst X T' e e' ->
    env_subst X T' ((inr T)::e) ((inr (M_yy.Tsubst T X T'))::e')
| es_left :
  forall (X : nat) (T T' : typ) (e e' : M_yt.TEnv),
    env_subst X T' e e' ->
    env_subst (S X) (M_yy.Tshift 0 T') ((inl T)::e) ((inl(M_yy.Tsubst T X T'))::e').

Lemma env_subst_get_right :
  forall (x X' : nat) (e e' : M_yt.TEnv) (T : typ),
    (env_subst  X' T e e') ->
    Tget_right e' x = opt_map (fun T' => M_yy.Tsubst T' X' T) (Tget_right e x).
Proof.
  intros n n' e e' T H; gen n; induction H;
    [ intro n; simpl; induction (Tget_right e n); simpl; trivial;
      apply f_equal with (f := @Some typ); apply noRepr_Ysubst_Yshift
      | intro n'; induction n'; simpl; trivial
      | simpl; intro n'; rewrite IHenv_subst;
        induction (Tget_right e n'); simpl; trivial;
          apply f_equal with (f := @Some typ);
            apply (noRepr_Yshift_Ysubst_1 0 X) ];
    apply typ_noRepr.
Qed.

Lemma env_subst_get_left_lt :
  forall (X X' : nat) (e e' : M_yt.TEnv) (T : typ),
    (env_subst X' T e e') -> X < X' ->
    Tget_left e' X = opt_map (fun T' => M_yy.Tsubst T' X' T) (Tget_left e X).
Proof.
  intros n n' e e' T H; gen n;
    induction H; simpl; trivial; intros n' H1;
      [ inversion H1
        | induction n';
          [ simpl; apply f_equal with (f := @Some typ);
            apply (noRepr_Yshift_Ysubst_1 0 X)
            | clear IHn'; rewrite IHenv_subst;
              [ case (Tget_left e n'); simpl; trivial; intro T'';
                apply f_equal with (f := @Some typ);
                  apply (noRepr_Yshift_Ysubst_1 0 X)
                | omega ] ] ];
      apply typ_noRepr.
Qed.

Lemma env_subst_get_left_ge :
  forall (X X' : nat) (e e' : M_yt.TEnv) (T : typ),
    env_subst X' T e e' -> X' < X ->
    Tget_left e' (X - 1) = opt_map (fun T' => M_yy.Tsubst T' X' T) (Tget_left e X).
Proof.
  intros n n' e e' T H; gen n;
    induction H; simpl; trivial; intros n' H1;
      [ induction n';
        [ inversion H1
          | simpl; rewrite <- minus_n_O; case (Tget_left e n'); simpl; trivial;
            intro T''; apply f_equal with (f := @Some typ);
              apply noRepr_Ysubst_Yshift ]
        | induction n';
          [ inversion H1
            | clear IHn'; replace ((S n') - 1) with (S (n' - 1)); try omega;
              rewrite IHenv_subst; try omega;
                case (Tget_left e n'); simpl; trivial; intro T'';
                  apply f_equal with (f := @Some typ);
                    apply (noRepr_Yshift_Ysubst_1 0 X) ] ];
      apply typ_noRepr.
Qed.

Lemma env_subst_wf_typ_0 :
  forall (e e' : M_yt.TEnv) (T : typ) (X : nat),
    env_subst X T e e' -> M_yt.Twf_env e' -> M_yt.Twf_typ e' T.
Proof.
  intros e e' T X H; induction H; simpl;
    [ intros _; exact (proj1 (proj2 (sub_wf H)))
      | intros (H1, H2); apply M_yt.Twf_typ_weakening_right; auto
      | intros (H1, H2); apply Twf_typ_weakening_left with (U':=top); auto with iso ].
Qed.

Lemma env_subst_le : forall n T e e', 
  env_subst n T e e' -> n <= [[[e']]].
Proof.
  intros n T e e'; gen n T e.
  induction e';
    [ intros; inversion H; omega
      | intros; inversion H;
        [ omega
          | gsimpl; apply IHe' with T e0; auto
          | gsimpl; apply le_n_S; apply IHe' with T' e0; auto ] ].
Qed.

Lemma env_subst_minus_1 : forall n T e e', 
  env_subst n T e e' -> [[[e]]] = S [[[e']]].
Proof.
  induction 1; gsimpl; auto.
Qed.

Lemma env_subst_wf_typ :
  forall (e e' : M_yt.TEnv) (S T : typ) (X : nat),
    env_subst X T e e' -> M_yt.Twf_typ e S -> M_yt.Twf_env e' -> M_yt.Twf_typ e' (M_yy.Tsubst S X T).
Proof.
  intros e e' S; gen e e'; induction S;
    intros e e' T X; gsimpl; auto.
  (* tvar case *)
  gcase; intros; try absurd_math;
    gcase; gsimpl;
    [ gcase; apply env_subst_le in H; omega
      | apply (env_subst_wf_typ_0 H H1)
      | gcase; apply env_subst_minus_1 in H; omega
      | gcase; apply env_subst_minus_1 in H; omega ].
  (* arrow case *)
  intros; destruct H0; split;
    [ apply IHS1 with e; auto
      | apply IHS2 with e; auto ].
  (* all case  *)
  intros; destruct H0; split;
    [ apply IHS1 with e; auto
      | rewrite <- (env_subst_minus_1 H);
        assert ([[[e]]] = [[[inl (M_yy.Tsubst S1 X T) :: e']]]);
          [ gsimpl; auto using (env_subst_minus_1 H)
            | rewrite H3 ;
              apply IHS2 with (e:=inl S1::e);
                [ apply es_left; auto
                  | simpl; auto
                  | simpl; split;
                    [ apply IHS1 with e; auto
                      | auto ] ] ] ].
Qed.

Lemma env_subst_wf_env :
  forall (e e' : M_yt.TEnv) (T : typ) (X : nat),
    env_subst X T e e' -> M_yt.Twf_env e -> M_yt.Twf_env e'.
Proof.
  intros e e' T X H; induction H; simpl; try tauto;
    intros (H1, H2); split; auto;
      apply env_subst_wf_typ with (1 := H); auto.
Qed.

(** Typing relation well-formedness *)

Lemma typing_wf :
  forall (e : M_yt.TEnv) (t : term) (U : typ),
    typing e t U -> M_yt.Twf_env e /\ wf_term e t /\ M_yt.Twf_typ e U.
Proof.
  intros e t1 U H; induction H; gsimpl;
    [ repeat split; trivial;
      [ rewrite H0; discriminate 
        | exact (Tget_right_wf e x top twf_nil_top H H0) ]
      | simpl in IHtyping; repeat split; try tauto
      | repeat split; try tauto;
        generalize IHtyping1; gsimpl; tauto
      | generalize IHtyping; gsimpl;
        repeat split; try tauto
      | assert (H1 := proj1 (proj2 (sub_wf H0)));
        repeat split; try tauto;
          generalize IHtyping; gsimpl; intros;
            apply env_subst_wf_typ with (1 := es_here H0); tauto
      | repeat split; try tauto; exact (proj2 (proj2 (sub_wf H0))) ].
Qed.


(** Weakening for typing (typing part) *)

Lemma typing_weakening_left_ind :
  forall (e e' : M_yt.TEnv) (X : nat) (t : term) (U : typ),
    Tinsert_left X e e' ->
    typing e t U -> typing e' (M_yt.Tshift X t) (M_yy.Tshift X U).
Proof.
  intros e e' n t1 U H1 H2; gen n e' H1.
  induction H2; intros n1 e' H1; gsimpl;
    [ apply T_Var;
      [ exact (Tinsert_left_wf_env top twf_nil_top H1 H)
        | rewrite Tget_right_insert_left with (2 := H1); auto with iso; rewrite H0; trivial ]
      | apply T_Abs; apply IHtyping; apply Til_right; trivial
      | assert (H2 := (IHtyping1 _ _ H1)); assert (H3 := (IHtyping2 _ _ H1));
        exact (T_App H2 H3)
      | apply T_Tabs; apply IHtyping; exact (Til_left T1 H1)
      | rewrite (noRepr_Yshift_Ysubst_2 0 n1); auto with iso;
        apply (T_Tapp (IHtyping _ _ H1) (sub_weakening_left_ind H1 H))
      | exact (T_Sub (IHtyping _ _ H1) (sub_weakening_left_ind H1 H)) ].
Qed.

Lemma typing_weakening_left :
  forall (e : M_yt.TEnv) (t : term) (U V : typ),
    M_yt.Twf_typ e V -> typing e t U ->
    typing ((inl V)::e) (M_yt.Tshift 0 t) (M_yy.Tshift 0 U).
Proof.
  intros e t1 U V H1 H2; apply typing_weakening_left_ind with (2 := H2);
    apply Til_here; trivial.
Qed.

Lemma typing_weakening_right_ind :
  forall (e : M_yt.TEnv) (x : nat) (t : term) (U : typ),
    M_yt.Twf_env e -> typing (M_yt.Tremove_right e x) t U -> typing e (M_tt.Tshift x t) U.
Proof.
  intros e n t1 U H1 H2; cut (exists e', e' = M_yt.Tremove_right e n);
    [ intros (e', E); rewrite <- E in H2; gen n e E H1;
      induction H2; intros n' e' E H1; gsimpl;
        [ apply T_Var; trivial; rewrite E in H0; gcase;
          [ rewrite Tget_right_remove_right_ge in H0; trivial; omega
            | rewrite Tget_right_remove_right_lt in H0; trivial; omega ]
          | rewrite M_ty.Tshift_id; auto with iso; apply T_Abs;
            apply IHtyping;
              [ rewrite E; trivial
                | simpl; split; trivial;
                  assert (H3 := proj1 (proj1 (typing_wf H2))); rewrite E in H3;
                    exact (M_yt.Twf_typ_insert_right e' n' T1 H3) ]
          | exact (T_App (IHtyping1 _ _ E H1) (IHtyping2 _ _ E H1))
          | rewrite M_ty.Tshift_id; auto with iso;
            apply T_Tabs; apply IHtyping;
              [ rewrite E; trivial
                | simpl; split; trivial;
                  assert (H3 := proj1 (proj1 (typing_wf H2))); rewrite E in H3;
                    exact (M_yt.Twf_typ_insert_right e' n' T1 H3) ]
          | rewrite M_ty.Tshift_id; auto with iso;
            apply (T_Tapp (T2 := T2) (IHtyping _ _ E H1));
              rewrite E in H; exact (sub_weakening_right_ind e' n' H1 H)
          | apply (T_Sub (T2 := T2) (IHtyping _ _ E H1));
            rewrite E in H; exact (sub_weakening_right_ind e' n' H1 H) ]
      | exists (M_yt.Tremove_right e n); trivial ].
Qed.

Lemma typing_weakening_right :
  forall (e : M_yt.TEnv) (t : term) (U V : typ),
    M_yt.Twf_typ e V -> typing e t U -> typing ((inr V)::e) (M_tt.Tshift 0 t) U.
Proof.
  intros e t1 U V H1 H2; apply (@typing_weakening_right_ind ((inr V)::e));
    simpl; trivial; split; trivial; exact (proj1 (typing_wf H2)).
Qed.

(** Strengthening *)

Lemma sub_strengthening_right :
  forall (e : M_yt.TEnv) (x : nat) (U V : typ),
    sub e U V -> sub (M_yt.Tremove_right e x) U V.
Proof.
  intros e x U V H1; generalize H1; apply sub_extensionality;
    [ intro X; apply Tget_left_remove_right
      | apply M_yt.Twf_env_remove_right; exact (proj1 (sub_wf H1)) ].
Qed.


(** Narrowing for the Typing Relation *)

Lemma typing_narrowing_ind :
  forall (e e' : M_yt.TEnv) (X : nat) (t : term) (U : typ),
    narrow X e e' -> typing e t U -> typing e' t U.
Proof.
  intros e e' n t1 U H1 H2; generalize e' n H1; clear e' n H1;
    induction H2; intros e' n1 H1;
      [ apply T_Var;
        [ exact (narrow_wf_env H1 H)
          | rewrite <- get_right_narrow with (1 := H1); trivial ]
        | apply T_Abs; apply IHtyping with (n := n1);
          apply narrow_extend_right; trivial;
            exact (narrow_wf_typ T1 H1 (proj1 (proj1 (typing_wf H2))))
        | eapply T_App; eauto
        | apply T_Tabs; apply IHtyping with (n := S n1);
          apply narrow_extend_left with (X := n1); trivial;
            exact (narrow_wf_typ T1 H1 (proj1 (proj1 (typing_wf H2))))
        | eapply T_Tapp; eauto; exact (sub_narrowing H1 H)
        | apply T_Sub with (1 := IHtyping _ _ H1); exact (sub_narrowing H1 H) ].
Qed.

Lemma typing_narrowing :
  forall (e : M_yt.TEnv) (t : term) (U V1 V2 : typ),
    typing ((inl V1)::e) t U -> sub e V2 V1 -> typing ((inl V2)::e) t U.
Proof.
  intros e t1 U V1 V2 H1 H2; exact (typing_narrowing_ind (narrow_0 H2) H1).
Qed.

(** Subtyping preserves typing *)

Lemma subst_preserves_typing :
  forall (e : M_yt.TEnv) (x : nat) (t u : term) (V W : typ),
    typing e t V ->
    typing (M_yt.Tremove_right e x) u W -> Tget_right e x = Some W ->
    typing (M_yt.Tremove_right e x) (M_tt.Tsubst t x u) V.
Proof.
  intros e n T u V W H; gen n u W.
  induction H; intros n' u W H1 E1; gsimpl;
    [ case (lt_eq_lt_dec x n');
      [ intro s; case s; clear s; intro H2;
        [ apply T_Var;
          [ apply M_yt.Twf_env_remove_right; trivial
            | rewrite Tget_right_remove_right_lt with (1 := H2); trivial ]
          | rewrite H2 in H0; rewrite H0 in E1; injection E1;
            intro E3; rewrite E3; trivial ]; gsimpl; auto
        | intro H2; apply T_Var;
          [ apply M_yt.Twf_env_remove_right; trivial
            | induction x;
              [ inversion H2
                | simpl; rewrite <- minus_n_O;
                  rewrite Tget_right_remove_right_ge; trivial; omega ] ] ]
      | rewrite M_ty.Tsubst_id; auto with iso;
        apply T_Abs; apply (IHtyping (S n') (M_tt.Tshift 0 u) W); trivial;
          assert (H2 := M_yt.Twf_typ_remove_right _ n' _ (proj1 (proj1 (typing_wf H))));
            exact (typing_weakening_right _ H2 H1)
      | exact (T_App (IHtyping1 _ u W H1 E1) (IHtyping2 _ u W H1 E1))
      | rewrite M_ty.Tsubst_id; auto with iso;
        apply T_Tabs; apply (IHtyping n' (M_yt.Tshift 0 u) (M_yy.Tshift 0 W));
          [ assert (H2 := M_yt.Twf_typ_remove_right _ n' _ (proj1 (proj1 (typing_wf H))));
            exact (typing_weakening_left _ H2 H1) 
            | simpl; rewrite E1; trivial ]
      | rewrite M_ty.Tsubst_id; auto with iso;
        apply T_Tapp with (1 := (IHtyping _ u W H1 E1));
          exact (sub_strengthening_right n' H0)
      | apply T_Sub with (1 := (IHtyping _ u W H1 E1));
        exact (sub_strengthening_right n' H0) ].
Qed.


(** Type substitution preserves subtyping *)

Lemma env_subst_sub :
  forall (e e' : M_yt.TEnv) (T T' : typ) (X : nat),
    env_subst X T' e e' -> (Tget_left e X) = (Some T) -> M_yt.Twf_env e' ->
    (sub e' T' (M_yy.Tsubst T X T')).
Proof.
  intros e e' T T' X H; gen T; induction H; intro T''; gsimpl;
    [ intros E H1; injection E; clear E; intro E; rewrite <- E;
      rewrite <- noRepr_Ysubst_Yshift; trivial; apply typ_noRepr
      | intros E (H1, H2);
        exact (sub_weakening_right _ H1 (IHenv_subst _ E H2))
      | intros E (H1, H2); induction (Tget_left e X); try discriminate;
        injection E; clear E; intro E; rewrite <- E;
          rewrite <- (noRepr_Yshift_Ysubst_1 0 X);
            [ apply sub_weakening_left with (1 := H1) | apply typ_noRepr]; auto ].
Qed.

Lemma Ysubst_preserves_subtyping :
  forall (e e' : M_yt.TEnv) (X : nat) (T U V : typ),
    env_subst X T e e' -> sub e U V -> sub e' (M_yy.Tsubst U X T) (M_yy.Tsubst V X T).
Proof.
  intros e e' n T U V H1 H2; gen n e' T H1; induction H2;
    [ intros n e' T; gsimpl; intros H1; apply SA_Top;
      [ exact (env_subst_wf_env H1 H)
        | exact (env_subst_wf_typ _ H1 H0 (env_subst_wf_env H1 H)) ]
      | intros n e' T H1; apply sub_reflexivity;
        [ exact (env_subst_wf_env H1 H)
          | exact (env_subst_wf_typ _ H1 H0 (env_subst_wf_env H1 H)) ]
      | intros n e' T' H1; gsimpl; case (lt_eq_lt_dec X n);
        [ intros s; case s; clear s;
          [ intro H5; apply SA_Trans_TVar with (U := M_yy.Tsubst U n T');
            [ rewrite env_subst_get_left_lt with (1 := H1) (2 := H5);
              rewrite H; trivial
              | apply IHsub; trivial ]
            | intro E; apply sub_transitivity with (2 := IHsub _ _ _ H1);
              rewrite E in H; gsimpl; apply (env_subst_sub H1 H);
                exact (env_subst_wf_env H1 (proj1 (sub_wf H2))) ]
          | intro H5; apply SA_Trans_TVar with (U := M_yy.Tsubst U n T');
            [ rewrite env_subst_get_left_ge with (1 := H1); try omega;
              induction X;
                [ assert False; [ omega | contradiction ]
                  | simpl; rewrite H; trivial ]
              | apply IHsub; trivial ] ]
      | intros n e' T H1; gsimpl; apply SA_Arrow; auto
      | intros n e' T H1; gsimpl; apply SA_All; auto;
        exact (IHsub2 _ _ _ (es_left T1 H1)) ].
Qed.


(** Type substitution preserves typing *)

Lemma subst_typ_preserves_typing_ind :
  forall (e e' : M_yt.TEnv) (t : term) (U P : typ) (X : nat),
    env_subst X P e e' ->
    typing e t U -> typing e' (M_yt.Tsubst t X P) (M_yy.Tsubst U X P).
Proof.
  intros e e' T U P n H1 H2; gen n e' P H1; induction H2;
    [ intros n' e' P H1; gsimpl; apply T_Var;
      [ exact (env_subst_wf_env H1 H)
        | rewrite env_subst_get_right with (1 := H1); rewrite H0; trivial ]
      | intros n e' P H1; gsimpl; apply T_Abs; exact (IHtyping _ _ _ (es_right _ H1))
      | intros n e' P H1; exact (T_App (IHtyping1 _ _ _ H1) (IHtyping2 _ _ _ H1))
      | intros n e' P H1; gsimpl; exact (T_Tabs (IHtyping _ _ _ (es_left _ H1)))
      | intros n e' P H1; gsimpl;
        assert (H4 := T_Tapp (T2 := (M_yy.Tsubst T2 n P)) (IHtyping _ _ _ H1));
          gen H4; gsimpl; intro H4;
            rewrite (noRepr_Ysubst_Ysubst 0 n); auto with iso;
              apply H4; exact (Ysubst_preserves_subtyping H1 H)
      | intros n e' P H1; apply T_Sub with (1 := IHtyping _ _ _ H1);
        exact (Ysubst_preserves_subtyping H1 H) ].
Qed.

Lemma subst_typ_preserves_typing :
  forall (e : M_yt.TEnv) (t : term) (U P Q : typ),
    typing ((inl Q)::e) t U -> sub e P Q ->
    typing e (M_yt.Tsubst t 0 P) (M_yy.Tsubst U 0 P).
Proof.
  intros e t1 U P Q H1 H2; exact (subst_typ_preserves_typing_ind (es_here H2) H1).
Qed.

(** Inversion of subtyping *)

Lemma t_abs_inversion :
  forall (e : M_yt.TEnv) (t : term) (T0 T1 T2 T3 : typ),
    typing e (abs T1 t) T0 ->
    sub e T0 (arrow T2 T3) ->
    sub e T2 T1 /\
    (exists T4, sub e T4 T3 /\ typing ((inr T1)::e) t T4).
Proof.
  intros e t1 T0 T1 T2 T3 H; cut (exists t' : _, t' = abs T1 t1);
    [ intros (t', E1); rewrite <- E1 in H; generalize t1 T1 T2 T3 E1;
      clear t1 T1 T2 T3 E1;
        induction H; intros; try discriminate;
          [ injection E1; intros E2 E3; rewrite <- E2; rewrite <- E3;
            inversion_clear H0; split; [ trivial | exists T2; split; trivial ]
            | apply IHtyping with (1 := E1) (2 := sub_transitivity H0 H1) ]
      | exists (abs T1 t1); trivial ].
Qed.

Lemma t_tabs_inversion :
  forall (e : M_yt.TEnv) (t : term) (T0 T1 T2 T3 : typ),
    typing e (tabs T1 t) T0 ->
    sub e T0 (all T2 T3) ->
    sub e T2 T1 /\
    (exists T4, sub ((inl T2)::e) T4 T3 /\ typing ((inl T2)::e) t T4).
Proof.
  intros e t1 T0 T1 T2 T3 H; cut (exists t' : _, t' = tabs T1 t1);
    [ intros (t', E1); rewrite <- E1 in H; generalize t1 T1 T2 T3 E1;
      clear t1 T1 T2 T3 E1;
        induction H; intros; try discriminate;
          [ injection E1; intros E2 E3; rewrite <- E2; rewrite <- E3;
            inversion_clear H0; split; trivial;
              exists T2; split; trivial; exact (typing_narrowing H H1)
            | apply IHtyping with (1 := E1) (2 := sub_transitivity H0 H1) ]
      | exists (tabs T1 t1); trivial ].
Qed.

(** Canonical Forms *)

Lemma fun_value :
  forall (t : term) (T1 T2 : typ),
    value t -> typing nil t (arrow T1 T2) ->
    exists t' , exists T1' , t = abs T1' t'.
Proof.
  intros t1 T1 T2 H1 H; cut (exists e, e = (nil : M_yt.TEnv));
    [ intros (e, E1); rewrite <- E1 in H; cut (exists T0, T0 = arrow T1 T2);
      [ intros (T0, E2); rewrite <- E2 in H; generalize T1 T2 E2;
        clear T1 T2 E2; induction H; try contradiction;
          [ intros T3 T4 E; exists t0; exists T1; trivial
            | intros; discriminate
            | intros T3 T4 E2; rewrite E2 in H0; inversion H0;
              [ rewrite E1 in H2; induction X; discriminate
                | exact (IHtyping H1 E1 _ _ (sym_eq H5)) ] ]
        | exists (arrow T1 T2); trivial ]
      | exists (nil : M_yt.TEnv); trivial ].
Qed.

Lemma typefun_value :
  forall (t : term) (T1 T2 : typ),
    value t -> typing nil t (all T1 T2) ->
    exists t', exists T1', t = tabs T1' t'.
Proof.
  intros t1 T1 T2 H1 H; cut (exists e, e = (nil : M_yt.TEnv));
    [ intros (e, E1); rewrite <- E1 in H; cut (exists T0, T0 = all T1 T2);
      [ intros (T0, E2); rewrite <- E2 in H; generalize T1 T2 E2;
        clear T1 T2 E2; induction H; try contradiction;
          [ intros; discriminate
            | intros T3 T4 E; exists t0; exists T1; trivial
            | intros T3 T4 E2; rewrite E2 in H0; inversion H0;
              [ rewrite E1 in H2; induction X; discriminate
                | exact (IHtyping H1 E1 _ _ (sym_eq H5)) ] ]
        | exists (all T1 T2); trivial ]
      | exists (nil : M_yt.TEnv); trivial ].
Qed.

Lemma local_progress :
  forall (t : term) (U : typ),
    typing nil t U -> value t \/
    exists c, exists t0, exists t0', red t0 t0' /\ t = ctx_app c t0.
Proof.
  intros t1 U H; cut (exists e, e = (nil : M_yt.TEnv));
    [ intros (e, E); rewrite <- E in H;
      induction H;
        [ rewrite E in H0; induction x; discriminate
          | simpl; auto
          | right; case (IHtyping1 E); clear IHtyping1;
            [ intro H2; case (IHtyping2 E); clear IHtyping2;
              [ intro H3; rewrite E in H; generalize (fun_value H2 H);
                intros (t', (T1', E1)); rewrite E1; exists c_hole;
                  exists (app (abs T1' t') t2); exists (M_tt.Tsubst t' 0 t2);
                    split; trivial; apply E_AppAbs; trivial
                | intros (c, (t0, (t0', (H3, E1)))); exists (c_apparg t1 H2 c);
                  exists t0; exists t0'; rewrite E1; auto ]
              | intros (c, (t0, (t0', (H3, E1)))); exists (c_appfun c t2);
                exists t0; exists t0'; rewrite E1; auto ]
          | simpl; auto
          | right; case (IHtyping E); clear IHtyping;
            [ intro H1; rewrite E in H; generalize (typefun_value H1 H);
              intros (t', (T1', E1)); rewrite E1; exists c_hole;
                exists (tapp (tabs T1' t') T2); exists (M_yt.Tsubst t' 0 T2);
                  split; trivial; apply E_TappTabs
              | intros (c, (t0, (t0', (H3, E1)))); exists (c_typefun c T2);
                exists t0; exists t0'; rewrite E1; auto ]
          | auto ]
      | exists (nil : M_yt.TEnv); trivial ].
Qed.


(** Progress *)

Theorem progress :
  forall (t : term) (U : typ),
    typing nil t U -> value t \/ exists t', red t t'.
Proof.
  intros t1 U H; generalize (local_progress H);
    intros [H1 | (c, (t0, (t0', (H1, H2))))]; auto;
      right; exists (ctx_app c t0'); rewrite H2; apply E_Ctx; trivial.
Qed.

Lemma context_replacement :
  forall (e : M_yt.TEnv) (c : ctx) (t t' : term) (T : typ),
    (forall (T' : typ), (typing e t T') -> (typing e t' T')) ->
    typing e (ctx_app c t) T -> typing e (ctx_app c t') T.
Proof.
  intros e c t1 t' T H1 H2; cut (exists t'', t'' = ctx_app c t1);
    [ intros (t'', E); rewrite <- E in H2;
      generalize c E; clear c E; induction H2;
        [ induction c; try (intros; discriminate); simpl;
          intros E; apply H1; rewrite <- E; apply T_Var; trivial
          | induction c; try (intros; discriminate); simpl;
            intros E; apply H1; rewrite <- E; apply T_Abs; trivial
          | induction c; try (intros; discriminate); simpl;
            [ intros E; apply H1; rewrite <- E; exact (T_App H2_ H2_0)
              | intro E; injection E; clear E; intros E1 E2;
                rewrite <- E1; apply T_App with (2 := H2_0);
                  apply IHtyping1; trivial
              | intro E; injection E; clear E; intros E1 E2;
                rewrite <- E2; apply T_App with (1 := H2_);
                  apply IHtyping2; trivial ]
          | induction c; try (intros; discriminate); simpl;
            intros E; apply H1; rewrite <- E; exact (T_Tabs H2)
          | induction c; try (intros; discriminate); simpl;
            [ intros E; apply H1; rewrite <- E; exact (T_Tapp H2 H)
              | intro E; injection E; clear E; intros E1 E2;
                rewrite <- E1; apply T_Tapp with (2 := H);
                  apply IHtyping; trivial ]
          | intros c E; apply T_Sub with (2 := H); apply IHtyping; trivial ]
      | exists (ctx_app c t1); trivial ].
Qed.

Lemma local_preservation_app :
  forall (e : M_yt.TEnv) (t12 t2 : term) (T11 U : typ),
    typing e (app (abs T11 t12) t2) U -> typing e (M_tt.Tsubst t12 0 t2) U.
Proof.
  intros e t12 t2 T11 U H; cut (exists t, t = app (abs T11 t12) t2);
    [ intros (t1, E); rewrite <- E in H; induction H; try discriminate;
      [ injection E; clear E; intros E1 E2; rewrite E2 in H;
        assert (H6 := proj1 (typing_wf H));
          assert (H7 := proj2 (proj2 (typing_wf H)));
            generalize (t_abs_inversion H (sub_reflexivity _ _ H6 H7));
              intros (H2, (T4, (H4, H5))); apply T_Sub with (2 := H4);
                apply (subst_preserves_typing 0 (u := t2) (W := T11) H5);
                  trivial; simpl; rewrite <- E1; exact (T_Sub H0 H2)
        | apply T_Sub with (2 := H0); auto ]
      | exists (app (abs T11 t12) t2); trivial ].
Qed.

Lemma local_preservation_tapp :
  forall (e : M_yt.TEnv) (t12 : term) (T11 T2 U : typ),
    typing e (tapp (tabs T11 t12) T2) U -> typing e (M_yt.Tsubst t12 0 T2) U.
Proof.
  intros e t12 T11 T2 U H; cut (exists t, t = tapp (tabs T11 t12) T2);
    [ intros (t1, E); rewrite <- E in H; induction H; try discriminate;
      [ injection E; clear E; intros E1 E2; rewrite E2 in H;
        assert (H7 := proj1 (typing_wf H));
          assert (H8 := proj2 (proj2 (typing_wf H)));
            generalize (t_tabs_inversion H (sub_reflexivity _ _ H7 H8));
              intros (H2, (T3, (H4, H5))); assert (H6 := T_Sub H5 H4);
                rewrite <- E1; exact (subst_typ_preserves_typing H6 H0)
        | apply T_Sub with (2 := H0); auto ]
      | exists (tapp (tabs T11 t12) T2); trivial ].
Qed.

(** Preservation *)

Theorem preservation :
  forall (e : M_yt.TEnv) (t t' : term) (U : typ),
    typing e t U -> red t t' -> typing e t' U.
Proof.
  intros e t1 t' U H1 H2; generalize U H1; clear U H1; induction H2; intros U H1;
    [ exact (local_preservation_app H1)
      | exact (local_preservation_tapp H1)
      | exact (context_replacement _ IHred H1) ].
Qed.


(** * Alternate reduction relation *)

Inductive red' : term -> term -> Prop :=
| appabs :
  forall (t11 : typ) (t12 t2 : term),
    value t2 -> red' (app (abs t11 t12) t2) (M_tt.Tsubst t12 0 t2)
| tapptabs :
  forall (t11 t2 : typ) (t12 : term),
    red' (tapp (tabs t11 t12) t2) (M_yt.Tsubst t12 0 t2)
| appfun :
  forall t1 t1' t2 : term, red' t1 t1' -> red' (app t1 t2) (app t1' t2)
| apparg :
  forall t1 t2 t2' : term,
    value t1 -> red' t2 t2' -> red' (app t1 t2) (app t1 t2')
| typefun :
  forall (t1 t1' : term) (t2 : typ),
    red' t1 t1' -> red' (tapp t1 t2) (tapp t1' t2).

Theorem progress' :
  forall (t : term) (U : typ),
    typing nil t U -> value t \/ exists t', red' t t'.
Proof.
  intros t1 U H; cut (exists e, e = (nil : M_yt.TEnv));
    [ intros (e, E); rewrite <- E in H;
      induction H;
        [ rewrite E in H0; induction x; discriminate
          | simpl; auto
          | right; case (IHtyping1 E);
            [ intro H2; case (IHtyping2 E);
              [ intro H3; rewrite E in H; generalize (fun_value H2 H);
                intros (t', (T1', E1)); rewrite E1; exists (M_tt.Tsubst t' 0 t2);
                  apply appabs; trivial
                | intros (t2', H3); exists (app t1 t2'); apply apparg; trivial ]
              | intros (t1', H2); exists (app t1' t2); apply appfun; trivial ]
          | simpl; auto
          | right; case (IHtyping E);
            [ intro H1; rewrite E in H; generalize (typefun_value H1 H);
              intros (t', (T1', E1)); rewrite E1; exists (M_yt.Tsubst t' 0 T2);
                apply tapptabs; trivial
              | intros (t1', H1); exists (tapp t1' T2); apply typefun; trivial ]
          | auto ]
      | exists (nil: M_yt.TEnv); trivial ].
Qed.

Theorem preservation' :
  forall (e : M_yt.TEnv) (t t' : term) (U : typ),
    typing e t U -> red' t t' -> typing e t' U.
Proof.
  intros e t1 t' U H1; generalize t'; clear t'; induction H1;
    [ intros t' H1; inversion_clear H1
      | intros t' H2; inversion_clear H2
      | intros t' H2; generalize H1_ IHtyping1; clear H1_ IHtyping1;
        inversion_clear H2;
          [ intros H1 IHtyping1;
            assert (H6 := proj1 (typing_wf H1));
              assert (H7 := proj2 (proj2 (typing_wf H1)));
                generalize (t_abs_inversion H1 (sub_reflexivity _ _ H6 H7));
                  intros (H2, (T4, (H4, H5))); apply T_Sub with (2 := H4);
                    apply (subst_preserves_typing 0 (u := t2) (W := t11) H5);
                      trivial; simpl; exact (T_Sub H1_0 H2)
            | intros H1 IHtyping1; apply T_App with (1 := IHtyping1 _ H); trivial
            | intros H2 IHtyping1; apply T_App with (2 := IHtyping2 _ H0); trivial ]
      | intros t' H2; inversion_clear H2
      | intros t' H2; generalize H1 IHtyping; clear H1 IHtyping;
        inversion_clear H2; intros H1 IHtyping;
          [ assert (H7 := proj1 (typing_wf H1));
            assert (H8 := proj2 (proj2 (typing_wf H1)));
              generalize (t_tabs_inversion H1 (sub_reflexivity _ _ H7 H8));
                intros (H2, (T3, (H4, H5))); assert (H6 := T_Sub H5 H4);
                  exact (subst_typ_preserves_typing H6 H)
            | apply T_Tapp with (1 := IHtyping _ H0); trivial ]
      | intros t' H2; eapply T_Sub; auto ].
Qed.
