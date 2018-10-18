Set Implicit Arguments.

Require Import Variable_Sets.
Require Import deBruijn_Isomorphism.


(** This file provides a connection between the generic meta library
   and some simple typed languages such as STLC or ML
   based on some isomorphisms.

   A concrete type/term class [TT] is isomorphic to the generic
   representation [RR] when there is an isomorphism
   between [TT] and [Interpret RR].

   In the following, two modules [MT] and [MY] are used.
   - MT stands for module for terms of e.g. STLC.
   - MY stands for module for types of e.g. STLC
   *)

Module dBTemplate (iso1 iso2 : Iso_full).


  Hint Rewrite iso1.To_From iso1.From_To iso2.To_From iso2.From_To : isorew.

  Hint Resolve iso1.To_From iso1.From_To iso2.To_From iso2.From_To.


  (**************************************************************)
  (** * Shifting *)
  (**************************************************************)

  (** Shifting for a iso1 variable in a iso2 *) 

  Definition Tshift (X : atom) (T : iso2.TT) : iso2.TT :=
    iso2.To (shift X iso1.RR (iso2.From T)).

  (**************************************************************)
  (** * Substitution *)
  (**************************************************************)

  (** Substitution for a iso1 variable in a iso2 *)

  Definition Tsubst (T:iso2.TT) (m:atom) (U:iso1.TT) : iso2.TT :=
    iso2.To (subst (iso2.From T) m (iso1.From U)).


  (**************************************************************)
  (** * Term size *)
  (**************************************************************)

  Definition Ysize (T:iso1.TT) : nat := size (iso1.From T).


  (**************************************************************)
  (** * A tactic unfolding everything *)
  (**************************************************************)

  Ltac gunfold :=
    unfold Tshift, Tsubst in *;
    unfold Ysize in *;
    intros;
    repeat rewrite iso2.To_From in *; 
    repeat rewrite iso2.From_To in *;
    repeat rewrite iso1.From_To in *;
    repeat rewrite iso1.From_To in *;
    simpl in *.


  (**************************************************************)
  (** * Homomorphisms *)
  (**************************************************************)

  (** [From] is a homomorphism w.r.t. substitutions. *)

  Lemma From_Tshift : forall (T:iso2.TT) (a:atom),
    iso2.From (Tshift a T) = shift a iso1.RR (iso2.From T). 
  Proof.
    unfold Tshift; intros; autorewrite with isorew; auto.
  Qed.

  (** [From] is a homomorphism w.r.t. substitutions. *)

  Lemma From_Tsubst : forall (T:iso2.TT) (a:atom) (U:iso1.TT),
    iso2.From (Tsubst T a U) = subst (iso2.From T) a (iso1.From U).
  Proof.
    unfold Tsubst; intros; autorewrite with isorew; auto.
  Qed.


  (**************************************************************)
  (** Tshift and Tsubst are identity function when no [Repr] occurs. *)
  (**************************************************************)

  Lemma Tshift_id: forall n T,
    noRepr iso2.RR ->
    iso1.RR <> iso2.RR ->
    Tshift n T = T.
  Proof.
    gunfold; rewrite <- noRepr_shift_hetero; autorewrite with isorew; auto.
  Qed.
    
  Lemma Tsubst_id : forall n T U, 
    noRepr iso2.RR ->
    iso1.RR <> iso2.RR ->
    Tsubst T n U = T.
  Proof.
    gunfold; rewrite <- noRepr_subst_hetero; autorewrite with isorew; auto.
  Qed.


  (**************************************************************)
  (** * Environments *)
  (**************************************************************)

  (** TEnv is (TT * TT) list.
     - [inl] is used for type variable binding.
     - [inr] is used for term variable binding. *)

  Notation TEnv := (Env iso1.TT).

  Fixpoint From_TEnv (e:TEnv) : (ENV iso1.RR) :=
    match e with
      | nil => nil
      | inl T :: e' => inl (iso1.From T) :: (From_TEnv e')
      | inr T :: e' => inr (iso1.From T) :: (From_TEnv e')
    end.

  Fixpoint To_TEnv (e:ENV iso1.RR) : TEnv :=
    match e with
      | nil => nil
      | inl T :: e' => inl (iso1.To T) :: (To_TEnv e')
      | inr T :: e' => inr (iso1.To T) :: (To_TEnv e')
    end.


  Lemma From_To_TEnv : forall e : ENV iso1.RR, From_TEnv (To_TEnv e) = e.
  Proof.
    induction e;
      [ simpl; auto
        | destruct a;
          simpl; rewrite IHe; rewrite iso1.From_To; auto
      ].
  Qed.

  Lemma To_From_TEnv : forall e : TEnv, To_TEnv (From_TEnv e) = e.
  Proof.
    induction e; simpl; auto.
    destruct a; simpl; rewrite IHe, iso1.To_From; auto.
  Qed.

  Hint Resolve From_To_TEnv.
  Hint Rewrite From_To_TEnv : isorew.


  Definition Tlth (e : TEnv) : atom := lth (From_TEnv e).

  Notation "[[[ e ]]]" := (Tlth e).

  (** Tremove_right removes the x th element in environment. *)

  Fixpoint Tremove_right (e : TEnv) (x : nat) {struct e} : TEnv :=
    match e with
      | nil         => nil
      | (inl T)::e' => (inl T)::(Tremove_right e' x)
      | (inr T)::e' =>
        match x with
          | O   => e'
          | S x => (inr T::(Tremove_right e' x))
        end
    end.


  (**************************************************************)
  (** To and From function on (option TT) *)
  (**************************************************************)

  Fixpoint opt_To (T : option (Interpret iso1.RR)) : option iso1.TT :=
    match T with
      | None => None
      | Some T' => Some (iso1.To T')
    end.

  Fixpoint opt_From (T : option (iso1.TT)) : option (Interpret iso1.RR) :=
    match T with
      | None => None
      | Some T' => Some (iso1.From T')
    end.

  Lemma opt_To_preserving_none (T : option (Interpret iso1.RR)) :
    T = None -> opt_To T = None.
  Proof.
    intros; rewrite H; auto.
  Qed.

  Lemma opt_To_preserving_none_rev (T : option (Interpret iso1.RR)) :
    opt_To T = None -> T = None.
  Proof.
    induction T; simpl; intros; [discriminate | auto].
  Qed.

  Lemma opt_From_preserving_some (T : option iso1.TT) (t : iso1.TT):
    T = Some t -> opt_From T = Some (iso1.From t).
  Proof.
    intros; rewrite H; auto.
  Qed.

  Lemma opt_To_preserving_some (T : option (Interpret iso1.RR)) (t : Interpret iso1.RR):
    T = Some t -> opt_To T = Some (iso1.To t).
  Proof.
    intros; rewrite H; auto.
  Qed.

  Lemma opt_To_preserving_some_rev (T : option (Interpret iso1.RR)) (t : Interpret iso1.RR):
    opt_To T = Some (iso1.To t) -> T = Some t.
  Proof.
    induction T; simpl; intros; [idtac | discriminate].
    rewrite <- (iso1.From_To a);rewrite <- (iso1.From_To t0).
    rewrite <- opt_To_preserving_some with (T:= Some a) in H;auto.
    rewrite <- opt_To_preserving_some with (T:= Some t0) in H;auto.
    inversion H; rewrite H1;reflexivity.
  Qed.

  Lemma opt_To_preserving_eq (T U : option (Interpret iso1.RR)) :
    T = U -> opt_To T = opt_To U.
  Proof.
    intros; rewrite H; auto.
  Qed.

  Lemma opt_To_preserving_eq_rev (T U : option (Interpret iso1.RR)) :
    opt_To T = opt_To U -> T = U.
  Proof.
    induction T; induction U; intros;
      [ inversion H;
        rewrite <- (iso1.From_To a); rewrite <- (iso1.From_To a0);
        rewrite H1; reflexivity
      | inversion H
      | inversion H
      | auto
      ].
  Qed.

  Hint Resolve 
    opt_To_preserving_none opt_To_preserving_none_rev 
    opt_To_preserving_some opt_To_preserving_some_rev
    opt_To_preserving_eq opt_To_preserving_eq_rev
    opt_From_preserving_some
    : opt.


  (**************************************************************)
  (** Generic versions of [Tget_left] and [Tget_right] *)
  (**************************************************************)  

  Definition gTget_left (e : TEnv) (X : atom) : option (iso1.TT) :=
    opt_To (get_left (From_TEnv e) X).

  Definition gTget_right (e : TEnv) (X : atom) : option (iso1.TT) :=
    opt_To (get_right (From_TEnv e) X).



  (**************************************************************)
  (** * Well-formedness in an environment *)
  (**************************************************************)

  (** Well-formed types in an environment *)

  Definition Twf_typ (e : TEnv) (T : iso1.TT) : Prop :=
    HO_wf [[From_TEnv e]] (iso1.From T).
  
  Fixpoint Twf_env (e : TEnv) : Prop :=
    match e with
      nil          => True
      | (inr T)::e => Twf_typ e T /\ Twf_env e
      | (inl T)::e => Twf_typ e T /\ Twf_env e
    end.

  Definition gTwf_env (e : TEnv) : Prop :=
    wf_env (From_TEnv e).

  Lemma Twf_env_gTwf_env : forall (e: TEnv),
    Twf_env e -> gTwf_env e.
  Proof.
    unfold gTwf_env;induction e;auto.
    simpl;destruct a;intros;destruct H;simpl;
      (split;
        [ unfold Twf_typ in H;auto
          | auto
        ]).
  Qed.

  Lemma gTwf_env_Twf_env : forall (e: TEnv),
    gTwf_env e -> Twf_env e.
  Proof.
    unfold gTwf_env;induction e;auto.
    simpl;destruct a;intros;destruct H;simpl;
      (split;
        [ unfold Twf_typ in H;auto
          | auto
        ]).
  Qed.
    
  Lemma Twf_env_weaken : forall (T : iso1.TT) (n m : TEnv),
    [[[n]]] <= [[[m]]] ->
    Twf_typ n T ->
    Twf_typ m T.
  Proof.
    unfold Twf_typ.
    eauto using HO_wf_weaken.
  Qed.

  (** Generic version of [Tremove_right] *)

  Definition gTremove_right (e : TEnv) (x : nat) : TEnv :=
    To_TEnv (remove_right (From_TEnv e) x).

  Lemma Tremove_right_gTremove_right: forall (e:TEnv)(x:nat),
    Tremove_right e x = gTremove_right e x.
  Proof.
    unfold gTremove_right.
    induction e; simpl; intros; auto.
    destruct a;
    [ simpl; rewrite IHe, iso1.To_From; auto
    | destruct x;
      [ simpl; rewrite To_From_TEnv; auto
      | simpl; rewrite iso1.To_From; rewrite IHe; auto
      ]
    ].
  Qed.

  Lemma Twf_typ_remove_right : forall (e : TEnv) (x : nat) (T : iso1.TT),
    Twf_typ e T -> Twf_typ (Tremove_right e x) T.
  Proof.
    intros.
    rewrite Tremove_right_gTremove_right.
    unfold Twf_typ, gTremove_right; intros.
    autorewrite with isorew.
    auto using HO_wf_remove_right.
  Qed.

  Lemma Twf_typ_insert_right : forall (e : TEnv) (n : nat) (T : iso1.TT),
    Twf_typ (Tremove_right e n) T -> Twf_typ e T.
  Proof.
    intros.
    rewrite Tremove_right_gTremove_right in H.
    unfold Twf_typ, gTremove_right in *; intros.
    autorewrite with isorew in *.
    eauto using HO_wf_insert_right.
  Qed.

  Lemma Twf_env_remove_right : forall (e : TEnv) (x : nat),
    Twf_env e ->
    Twf_env (Tremove_right e x).
  Proof.
    intros.
    rewrite Tremove_right_gTremove_right.
    apply gTwf_env_Twf_env.
    apply Twf_env_gTwf_env in H.
    unfold gTwf_env, gTremove_right in *; intros.
    autorewrite with isorew.
    eauto using wf_env_remove_right.
  Qed.

  (** Generic version of [Tinsert_left] *)

  Definition gTinsert_left n (e e':TEnv) :=
    insert_left n (From_TEnv e) (From_TEnv e').
    

  (** Isomorphisms between generic well-formedness and specific well-formedness *)

  Definition Tinsert (n: nat) (e: TEnv) (T: iso1.TT) (H:Twf_typ nil T) : TEnv :=
    To_TEnv (insert n (From_TEnv e) (iso1.From T) H). 


  Lemma Tinsert_S : forall (e:TEnv) (n:nat) U H,
    S [[[e]]] = [[[Tinsert n e U H]]].
  Proof.
    unfold Tinsert, Tlth; intros.
    autorewrite with isorew.
    apply insert_S.
  Qed.

  Hint Resolve Tinsert_S.

  Lemma Twf_typ_weakening_right : forall (e : TEnv) (T U : iso1.TT),
    Twf_typ e U -> Twf_typ ((inr T)::e) U.
  Proof.
    unfold Twf_typ.
    auto using HO_wf_weakening_right.
  Qed.

  Lemma Twf_typ_strengthening_right : forall (e : TEnv) (T U : iso1.TT),
    Twf_typ ((inr T)::e) U -> Twf_typ e U.
  Proof.
    unfold Twf_typ.
    eauto using HO_wf_strengthening_right.
  Qed.

  Lemma Twf_typ_eleft : forall (T U V : iso1.TT) (e : TEnv),
    Twf_typ ((inl U)::e) T -> Twf_typ ((inl V)::e) T.
  Proof.
    unfold Twf_typ.
    eauto using HO_wf_left.
  Qed.

End dBTemplate.


