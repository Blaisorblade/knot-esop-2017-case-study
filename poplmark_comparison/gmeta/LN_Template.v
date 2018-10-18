Set Implicit Arguments.

Require Import LNameless_Isomorphism.

(**********************************************************************)
(** * Module LNTemplate Definition *)
(**********************************************************************)


(* LNTemplate definition: iso1 is bound in iso2 *)
Module LNTemplate (iso1 iso2 : Iso_full).

  (**************************************************************)
  (** * Substitution *)
  (**************************************************************)

  (** Substitution for an iso2 parameter (free variable) in a iso2 *)

  Definition Tfsubst (T : iso2.TT)(a:atom)(U:iso1.TT) : iso2.TT :=
    iso2.To (LNameless_Meta.fsubst (iso2.From T) a (iso1.From U)).

  (** Substitution for an iso2 variables (bound variable) in a iso2 *)

  Definition Tbsubst (T : iso2.TT)(k:atom)(U:iso1.TT) : iso2.TT :=
    iso2.To (LNameless_Meta.bsubst (iso2.From T) k (iso1.From U)).


  (**************************************************************)
  (** * Set of parameters *)
  (**************************************************************)
 
  (** Set of iso2 parameters in a iso2 *)

  Definition Tfv (T:iso2.TT) : atoms :=
    freevars iso1.RR (iso2.From T).

  Fixpoint env_fv (E:env iso2.TT) : atoms :=
    match E with
      | nil => {}
      | (a,T) :: E0 => Tfv T `union` env_fv E0
    end.

  (**************************************************************)
  (** * Complexivity of terms *)
  (**************************************************************)

  (* [TSize]: size of a term *)
  Definition TSize (T:iso2.TT) := size (iso2.From T).


  (**************************************************************)
  (** * Well-Formedness of iso2 *)
  (**************************************************************)

  (** Intuitive meaning of well-formedness is
     "no free occurrence of bound variables".

     - There are several equivalent ways to define well-formedness:
       -- Using [wfT] (for [TwfT]) which characterizes the set of
          well-formed terms;
       -- Defining [Twf] directly;
       -- Using [wf] (for [gTwf]) which is a generic version of [Twf].

     - [Twf_basic] and [gTwf_basic] are basic versions of [Twf] and [gTwf],
       respectively.
       They are used because some lemmas hold only for them. *)
   
  (** Well-formed iso2 w.r.t. iso2 variables *)

  Definition TwfT (T:iso2.TT) : Prop :=
    wfT iso1.RR (iso2.From T).

  Definition Twf (T:iso2.TT) : Prop :=
    forall k (U:iso1.TT), T = Tbsubst T k U.

  Definition Twf_basic (T:iso2.TT) : Prop :=
    forall k a, T = Tbsubst T k (iso1.To (Var iso1.RR (inl a))).
  
  Definition gTwf (T:iso2.TT) : Prop :=
    wf iso1.RR (iso2.From T). 

  Definition gTwf_basic (T:iso2.TT) :Prop :=
    wf_basic iso1.RR (iso2.From T).
  
  Hint Unfold Tfsubst Tbsubst Tfv TwfT Twf Twf_basic gTwf gTwf_basic TSize.


  (**************************************************************)
  (** * Homomorphisms *)
  (**************************************************************)

  (** [From] is a homomorphism w.r.t. substitutions. *)

  Lemma From_Tfsubst : forall (T:iso2.TT) (a:atom) (U:iso1.TT),
    iso2.From (Tfsubst T a U) = fsubst (iso2.From T) a (iso1.From U).
  Proof.
    firstorder using iso2.From_To. 
  Qed.

  Lemma From_Tbsubst : forall (T:iso2.TT) (k:atom) (U:iso1.TT),
    iso2.From (Tbsubst T k U) = bsubst (iso2.From T) k (iso1.From U).
  Proof.
    firstorder using iso2.From_To. 
  Qed.

  (** For automation  *)

  Lemma From_Tfsubst_var : forall (T:iso2.TT) (a b:atom),
    iso2.From (Tfsubst T a (iso1.To (Var iso1.RR (inl b))))
    = fsubst (iso2.From T) a (Var iso1.RR (inl b)).
  Proof.
    intros.
    replace (Var iso1.RR (inl b)) with (iso1.From (iso1.To (Var iso1.RR (inl b))));
      auto using iso1.From_To.
    rewrite From_Tfsubst; autorewrite with isorew; auto.
  Qed.

  Lemma From_Tbsubst_var : forall (T:iso2.TT) (a b:atom),
    iso2.From (Tbsubst T a (iso1.To (Var iso1.RR (inl b))))
    = bsubst (iso2.From T) a (Var iso1.RR (inl b)).
  Proof.    
    intros.
    replace (Var iso1.RR (inl b)) with (iso1.From (iso1.To (Var iso1.RR (inl b)))); auto.
    rewrite From_Tbsubst; autorewrite with isorew;auto.
  Qed.

  (**************************************************************)
  (** * Tactics I *)
  (**************************************************************)

  Hint Resolve iso2.To_From iso2.From_To iso1.To_From.

  Hint Rewrite iso2.From_To iso2.To_From : isorew.
  Hint Rewrite <- From_Tfsubst : isorew.
  Hint Rewrite <- From_Tbsubst : isorew.
  Hint Rewrite conv_id : isorew.

  Hint Rewrite <- From_Tfsubst_var : isorew.
  Hint Rewrite <- From_Tbsubst_var : isorew.

  (** A tactic unfolding everything *)

  Ltac gunfold :=
    unfold Twf, Twf_basic in *;
    unfold gTwf, gTwf_basic, wf_basic in *;
    unfold Tfsubst, Tbsubst, Tfv, TwfT, TSize in *;
    intros;
    repeat rewrite iso2.To_From in *;
    repeat rewrite iso2.From_To in *;
    repeat rewrite iso1.To_From in *;
    repeat rewrite iso1.From_To in *;
    simpl in *; 
    simpl_env in *.

  (** [grewrite] is can be used in order to apply generic lemmas
     which envolve variables cases such as

     - [Tbfsubst_var_intro], etc. *)
  
  Tactic Notation "grewrite" ident(Y) :=
    let H := fresh in
      poses H Y; simpl in * |-; rewrite H; auto; clear H.

  Tactic Notation "grewrite" "<-" ident(Y) :=
    let H := fresh in
      poses H Y; simpl in * |-; rewrite <- H; auto; clear H.


  (**************************************************************)
  (** * Properties about Substitution *)
  (**************************************************************)

  (** Replacing a variable by a parameter doesn't change the complexivity.
     - For a later use in concrete cases, just need to show
<<
To (Var RR (inl a)) = fvar a
>>
     - Or one can use [grewrite]. *)

  Lemma TSize_Tbsubst : forall (T:iso2.TT)(k a:atom),
    TSize T = TSize (Tbsubst T k (iso1.To (Var iso1.RR (inl a)))).
  Proof.
    gunfold; auto using bsubst_size. 
  Qed.

  (** Substitution of a parameter for himself *)

  Lemma Tfsubst_self : forall (T:iso2.TT) (a:nat),
    T = Tfsubst T a (iso1.To (Var iso1.RR (inl a))).
  Proof.
    gunfold; rewrite <- fsubst_self; auto. 
  Qed.

  (** Substitution of a parameter which does not occur free *)

  Lemma Tfsubst_no_occur : forall (T:iso2.TT)(a:nat)(U:iso1.TT),
    a `notin` (Tfv T) -> T = Tfsubst T a U.
  Proof.
    gunfold; rewrite <- fsubst_no_occur; auto.
  Qed.

  (** When a type variable does not occur in environments *)

  Lemma env_fv_no_occur : forall (E:env iso2.TT) (X:atom)(V:iso1.TT),
    X `notin` env_fv E ->
    map (fun U : iso2.TT => Tfsubst U X V) E = E.
  Proof.
    induction E as [| (a,T)]; simpl; intros; destruct_notin;
      [ reflexivity
        | rewrite <- Tfsubst_no_occur; func_equal; auto ].
  Qed.
    
  (** Extension of the set of parameters by substitution *)

  Lemma Tfv_pass_binder : forall (T:iso2.TT)(U:iso1.TT)(a k:nat),  
    a `in` (Tfv T) -> a `in` (Tfv (Tbsubst T k U)).
  Proof.
    gunfold; auto using freevars_pass_binder.
  Qed.

  Lemma Tfv_pass_binder_1 : forall (T:iso2.TT)(U:iso1.TT)(a k:nat),
    a `notin` (Tfv (Tbsubst T k U)) ->
    a `notin` (Tfv T).
  Proof.
    introv H; contra H; apply Tfv_pass_binder; auto.
  Qed.

  (** Independence of substituted variables *)

  (* wfT_Tbsubst_core => Tbsubst_homo_core *)
  Lemma Tbsubst_homo_core : forall (T:iso2.TT)(U V:iso1.TT) k j,
    k <> j -> 
    Tbsubst T j V = Tbsubst (Tbsubst T j V) k U ->
    T = Tbsubst T k U.
  Proof.
    gunfold; rewrite <- bsubst_homo_core with (V:=iso1.From V) (j:=j);
      auto using iso2.To_inj.
  Qed.

  (** Substitution of a variable is equivalent to substitution
     of that variable by a parameter which will be substituted again. *)

  Lemma Tbfsubst_var_intro : forall (T:iso2.TT)(U:iso1.TT)(a:nat),
    a `notin` Tfv T ->
    forall k, Tbsubst T k U = Tfsubst (Tbsubst T k (iso1.To (Var iso1.RR (inl a)))) a U.
  Proof.
    gunfold; f_equal; auto using bfsubst_var_intro.
  Qed.    
  

  (**************************************************************)
  (** * Equivalence of well-formedness definitions *)
  (**************************************************************)
  
  Lemma Twf_basic_from_Twf : forall (T:iso2.TT), Twf T -> Twf_basic T.
  Proof.
    unfold Twf_basic; intros.
    grewrite <- H; autorewrite with isorew; auto.
  Qed.

  Lemma Twf_from_Twf_basic : forall (T:iso2.TT), Twf_basic T -> Twf T.
  Proof.
    gunfold.
    pick fresh a for (freevars iso1.RR (iso2.From T)); destruct_notin.
    puts (H k a).
    rewrite H0.
    repeat rewrite iso2.From_To.
    repeat rewrite iso1.From_To.
    rewrite <- bsubstitution_var_twice; auto.
  Qed.

  Lemma Twf_gTwf_basic : forall (T:iso2.TT), Twf_basic T -> gTwf_basic T.
  Proof.
    gunfold.
    pattern T at 1; rewrite (H k a).
    gunfold; auto.
  Qed.

  Lemma gTwf_Twf_basic : forall (T:iso2.TT), gTwf_basic T -> Twf_basic T.
  Proof.
    gunfold.
    rewrite <- (H k a).
    autorewrite with isorew; auto.
  Qed.

  Lemma Twf_gTwf : forall (T:iso2.TT), Twf T -> gTwf T.
  Proof.
    gunfold; unfold wf; intros.
    pattern T at 1; rewrite (H k (iso1.To U)).
    gunfold; auto.
  Qed.

  Lemma gTwf_Twf : forall (T:iso2.TT), gTwf T -> Twf T.
  Proof.
    gunfold.
    rewrite <- (H k (iso1.From U)).
    gunfold; auto.
  Qed.

  Lemma gTwf_from_Twf_basic : forall (T:iso2.TT), Twf_basic T -> gTwf T.
  Proof.
    intros.
    cut (Twf T); [apply Twf_gTwf | apply* Twf_from_Twf_basic].
  Qed.

  Lemma Twf_basic_from_gTwf : forall (T:iso2.TT), gTwf T -> Twf_basic T.
  Proof.
    intros.
    cut (Twf T); [apply Twf_basic_from_Twf | apply* gTwf_Twf].
  Qed.

  Hint Resolve gTwf_Twf Twf_gTwf.

  Hint Resolve gTwf_from_Twf_basic Twf_basic_from_gTwf.

  (* wfT_Tbsubst_id => TwfT_Twf *)
  Lemma TwfT_Twf : forall (T:iso2.TT),
    TwfT T ->
    forall (k:nat) (U:iso1.TT), T = Tbsubst T k U.
  Proof.
    gunfold; rewrite <- wfT_wf; auto.
  Qed.

  
  (**************************************************************)
  (** * Permutation of substitutions *)
  (**************************************************************)

  (** Swapping of substitutions for (bound) variables. *)

  Lemma Tbsubst_homo : forall (T:iso2.TT) k l a b,
    k <> l ->
    Tbsubst (Tbsubst T k (iso1.To (Var iso1.RR (inl a)))) l (iso1.To (Var iso1.RR (inl b)))
    = Tbsubst (Tbsubst T l (iso1.To (Var iso1.RR (inl b)))) k (iso1.To (Var iso1.RR (inl a))).
  Proof.
    gunfold; f_equal; apply bsubstitution_homo; assumption.
  Qed.

  (** Consecutive substitution of the same (bound) variable has no effect. *)

  Lemma Tbsubst_var_twice : forall (T:iso2.TT) k a (U:iso1.TT),
    Tbsubst T k (iso1.To (Var iso1.RR (inl a)))
    = Tbsubst (Tbsubst T k (iso1.To (Var iso1.RR (inl a)))) k U.
  Proof.
    gunfold; f_equal; apply bsubstitution_var_twice.
  Qed.


  (**************************************************************)
  (** * No [Repr] cases *)
  (**************************************************************)  

  (** Usually in case of types, there will be no [Repr] cases. *)

  Lemma noRepr_Tfsubst : 
    noRepr iso2.RR ->
    iso1.RR <> iso2.RR ->
    forall (T:iso2.TT) (a:atom) (U:iso1.TT),
      Tfsubst T a U = T.    
  Proof.
    gunfold; rewrite noRepr_fsubst_hetero; auto using iso2.To_From.
  Qed.

  Lemma noRepr_Tbsubst : 
    noRepr iso2.RR ->
    iso1.RR <> iso2.RR ->
    forall (T:iso2.TT) (a:atom) (U:iso1.TT),
      Tbsubst T a U = T.    
  Proof.
    gunfold; rewrite noRepr_bsubst_hetero; auto using iso2.To_From.
  Qed.

  Lemma noRepr_Tfv :
    noRepr iso2.RR ->
    iso1.RR <> iso2.RR ->
    forall (T:iso2.TT), Tfv T [<=] empty.
  Proof.
    gunfold; auto using noRepr_freevars_hetero.
  Qed.

  Lemma noRepr_TwfT : 
    noRepr iso2.RR ->
    iso1.RR <> iso2.RR ->
    forall (T:iso2.TT), TwfT T.
  Proof.
    gunfold; auto using noRepr_wfT_hetero.
  Qed.

  Lemma noRepr_Twf : 
    noRepr iso2.RR ->
    iso1.RR <> iso2.RR ->
    forall (T:iso2.TT), Twf T.
  Proof.
    intros.
    cut (gTwf T); auto 2.
    gunfold; auto using noRepr_wf_hetero.
  Qed.

  Hint Resolve noRepr_Tfv noRepr_TwfT noRepr_Twf.

  Lemma iso_env_map : forall (E:env iso2.TT)(a:nat)(P:iso1.TT),
    map iso2.From (map (fun U : iso2.TT => iso2.To (fsubst (iso2.From U) a (iso1.From P))) E)
    = map (fun U => fsubst U a (iso1.From P)) (map iso2.From E).
  Proof.
    induction E as [|(b,T)]; simpl; intros; auto.
    f_equal; [f_equal | idtac]; auto.
  Qed.


End LNTemplate.


  (**************************************************************)
  (** * Module FWellformed Definition  *)
  (**************************************************************)

Module FWellformed (iso1 iso2 : Iso_full).

  Module Export M := LNTemplate iso1 iso2.

  (**************************************************************)
  (** * Well-Formedness of iso2 in an environment *)
  (**************************************************************)

  (** Well-Formedness of iso2 in an environment
     - The environment collects the information about
       the parameters occurring in an iso2.

     - That is, the environment binds all parameters
       of the well-formed iso2.
     - [TenvT]: Well-formed iso2 in an environment w.r.t. iso2 variables *)
 
  Definition TenvT (E:env iso1.TT)(T:iso2.TT) : Prop :=
    envT iso2.RR (map iso1.From E) (iso2.From T).

  Definition THenvT (E:env iso1.TT)(T:iso2.TT) : Prop :=
    envT iso1.RR (map iso1.From E) (iso2.From T).

  Definition YenvT (E:env iso1.TT)(T:iso2.TT) : Prop :=
    envT iso1.RR (map iso1.From E) (iso2.From T).

  Definition YTenvT (E:env iso1.TT)(F:env iso1.TT)(T:iso2.TT) : Prop :=
    TenvT E T.

  Definition YHenvT (E:env iso2.TT)(T:iso2.TT) : Prop :=
    envT iso1.RR (map iso2.From E) (iso2.From T).

  (**************************************************************)
  (** * Well-formed environments *)
  (**************************************************************)

  (** Well-formed environments contain only well-formed types. *)

  Definition Ywf_env (E:env iso2.TT) : Prop :=
    wf_env (map iso2.From E).

  (** [YTwf_env] can be redefined as follows:

  Definition okt (E:env MY.TT) (F: env MY.TT) : Prop :=
    Ywf_env E /\ ((forall T x, binds x T F -> YenvT E T) /\ uniq F).
    *)

  Hint Unfold TenvT THenvT YenvT YTenvT YHenvT.
  Hint Unfold Ywf_env.

  (** A tactic unfolding everything *)

  Ltac gunfold :=
    unfold M.Twf, M.Twf_basic in *;
    unfold M.gTwf, M.gTwf_basic, wf_basic in *;
    unfold YTenvT in *;
    unfold M.Tfsubst, M.Tbsubst, M.Tfv, M.TwfT, TenvT, M.TSize in *;
    unfold YHenvT in *;
    unfold Ywf_env in *;
    intros;
    repeat rewrite iso2.To_From in *;
    repeat rewrite iso2.From_To in *;
    repeat rewrite iso1.To_From in *;
    repeat rewrite iso1.From_To in *;
    simpl in *; 
    simpl_env in *.


  (**************************************************************)
  (** * Well-formedness in an environment *)
  (**************************************************************)

  (** Well-formed terms/types in an environment are well-formed. *)

  Lemma THenvT_THwfT : forall (E:env iso1.TT)(T:iso2.TT), 
    THenvT E T ->
    M.TwfT T.
  Proof.
    gunfold; eauto using envT_wfT.
  Qed.

  Lemma YenvT_YwfT : forall (E:env iso1.TT)(T:iso2.TT),
    YenvT E T ->
    M.TwfT T.
  Proof.
    gunfold; eauto using envT_wfT.
  Qed.

  (* THbsubst_on_env => THenvT_THwf *)
  Lemma THenvT_Thwf : forall (E:env iso1.TT)(T:iso2.TT), 
    THenvT E T -> forall (k:nat) (U:iso1.TT), T = M.Tbsubst T k U.
  Proof.
    intros; eauto using THenvT_THwfT, M.TwfT_Twf.
  Qed.

  (* Ybsubst_on_env => YenvT_Ywf *)
  Lemma YenvT_Ywf : forall (E:env iso1.TT)(T:iso2.TT), 
    YenvT E T -> forall (k:nat) (U:iso1.TT), T = M.Tbsubst T k U.
  Proof.
    intros; eauto using YenvT_YwfT, M.TwfT_Twf.
  Qed.

  (** Environments capture all the parameters in terms/types *)

  Lemma envT_THfv : forall (E:env iso1.TT) (T:iso2.TT) (a:atom),
    a # E -> THenvT E T -> a `notin` M.Tfv T.
  Proof.
    gunfold;
    apply envT_fv with (r':= iso1.RR)(E:= map iso1.From E); auto.
  Qed.

  Lemma envT_Yfv : forall (E:env iso1.TT) (T:iso2.TT) (a:atom),
    a # E -> YenvT E T -> a `notin` M.Tfv T.
  Proof.
    gunfold;
    apply envT_fv with (r':= iso1.RR)(E:= map iso1.From E); auto.
  Qed.

  (**************************************************************)
  (** * Weakening of well-formedness in an environment *)
  (**************************************************************)  

  (** Preservation of Well-Formation w.r.t. environment ext *)

  Lemma extends_TenvT : forall (E F:env iso1.TT) (T:iso2.TT), 
    TenvT E T -> extends E F -> TenvT F T.
  Proof.
    gunfold; eauto using extends_env.
  Qed.

  (* Weakening environments *)
  
  Lemma TenvT_weaken : forall (E F G:env iso1.TT)(T:iso2.TT),
    TenvT (E ++ G) T ->
    uniq (E ++ F ++ G) ->
    TenvT (E ++ F ++ G) T.
  Proof.
    gunfold; apply envT_weaken; intuition solve_uniq.
  Qed.

  Lemma TenvT_weaken_left : forall (E F:env iso1.TT)(T:iso2.TT),
    TenvT F T ->
    uniq (E ++ F) ->
    TenvT (E ++ F) T.
  Proof.
    gunfold; apply envT_weaken_left; intuition solve_uniq.
  Qed.

  Lemma TenvT_weaken_right : forall (E F:env iso1.TT)(T:iso2.TT),
    TenvT E T ->
    uniq (E ++ F) ->
    TenvT (E ++ F) T.
  Proof.
    gunfold; apply envT_weaken_right; intuition solve_uniq.
  Qed.

  Lemma YTenvT_weaken : forall (E F G D:env iso1.TT)(T:iso2.TT),
    YTenvT (E ++ G) D T ->
    uniq (E ++ F ++ G) ->
    YTenvT (E ++ F ++ G) D T.
  Proof.
    gunfold; apply envT_weaken; intuition solve_uniq.
  Qed.

  Lemma YTenvT_weaken_left : forall (E F D:env iso1.TT)(T:iso2.TT),
    YTenvT F D T ->
    uniq (E ++ F) ->
    YTenvT (E ++ F) D T.
  Proof.
    gunfold; apply envT_weaken_left; intuition solve_uniq.
  Qed.

  Lemma YTenvT_weaken_right : forall (E F D:env iso1.TT)(T:iso2.TT),
    YTenvT E D T ->
    uniq (E ++ F) ->
    YTenvT (E ++ F) D T.
  Proof.
    gunfold; apply envT_weaken_right; intuition solve_uniq.
  Qed.

  Lemma YTenvT_typ_var_indep : forall (E F :env iso1.TT) (T:iso2.TT),
    YTenvT E F T -> forall (G:env iso1.TT), YTenvT E G T.
  Proof.
    firstorder.
  Qed.    

  Lemma YTenvT_typ_var_strengthen : forall (E F G:env iso1.TT) (T:iso2.TT)(U:iso1.TT) (x:nat),
    YTenvT E (F ++ x ~ U ++ G) T ->
    YTenvT E (F ++ G) T.    
  Proof.
    firstorder.
  Qed.    


  (**************************************************************)
  (** * Narrowing of Environments *)
  (**************************************************************)  

  (** Well-formedness does not depend on types. *)  

  Lemma TenvT_narrow : forall (E F:env iso1.TT)(U V:iso1.TT)(T:iso2.TT)(a:nat),
    TenvT (E ++ a ~ V ++ F) T ->
    uniq (E ++ a ~ U ++ F) -> 
    TenvT (E ++ a ~ U ++ F) T.
  Proof.
    gunfold; eapply envT_narrow; eauto.
  Qed.

  Lemma TenvT_narrow_left : forall (F:env iso1.TT)(U V:iso1.TT)(T:iso2.TT)(a:nat),
    TenvT (a ~ V ++ F) T ->
    uniq (a ~ U ++ F) -> 
    TenvT (a ~ U ++ F) T.
  Proof.
    gunfold; eapply envT_narrow_left; eauto; solve_uniq.
  Qed.

  Lemma TenvT_narrow_right : forall (E:env iso1.TT)(U V:iso1.TT)(T:iso2.TT)(a:nat),
    TenvT (E ++ a ~ V) T ->
    uniq (E ++ a ~ U) -> 
    TenvT (E ++ a ~ U) T.
  Proof.
    gunfold; eapply envT_narrow_right; eauto; solve_uniq.
  Qed.

  Lemma YTenvT_narrow : forall (E F D:env iso1.TT)(U V:iso1.TT)(T:iso2.TT)(a:nat),
    YTenvT (E ++ a ~ V ++ F) D T ->
    uniq (E ++ a ~ U ++ F) -> 
    YTenvT (E ++ a ~ U ++ F) D T.
  Proof.
    gunfold; eapply envT_narrow; eauto.
  Qed.

  Lemma YTenvT_narrow_left : forall (F D:env iso1.TT)(U V:iso1.TT)(T:iso2.TT)(a:nat),
    YTenvT (a ~ V ++ F) D T ->
    uniq (a ~ U ++ F) -> 
    YTenvT (a ~ U ++ F) D T.
  Proof.
    gunfold; eapply envT_narrow_left; eauto; solve_uniq.
  Qed.

  Lemma YTenvT_narrow_right : forall (E D:env iso1.TT)(U V:iso1.TT)(T:iso2.TT)(a:nat),
    YTenvT (E ++ a ~ V) D T ->
    uniq (E ++ a ~ U) -> 
    YTenvT (E ++ a ~ U) D T.
  Proof.
    gunfold; eapply envT_narrow_right; eauto; solve_uniq.
  Qed.

  (********************************************************************)
  (** * Well-formed environments *)
  (********************************************************************)

  Lemma uniq_from_Ywf_env : forall (E:env iso2.TT),
    Ywf_env E -> uniq E.
  Proof.
    gunfold; eapply map_uniq_2; eauto using uniq_from_wf_env.
  Qed.

  Lemma notin_app_3 : forall A (E F:env A) a b T,
    a # E -> a # F -> a <> b -> a # (E ++ b ~ T ++ F).
  Proof.
    intros.
    apply notin_app_2; auto.
    apply notin_app_2; auto.
    simpl; solve_notin.    
  Qed.

  Lemma noRepr_YHenvT : 
    noRepr iso2.RR ->
    iso1.RR <> iso2.RR ->
    forall (E:env iso2.TT)(T:iso2.TT), YHenvT E T.
  Proof.
    gunfold; auto using noRepr_envT_hetero.
  Qed.

  Hint Resolve noRepr_YHenvT.

End FWellformed.

  (**************************************************************)
  (** * Module PWellformed Definition  *)
  (**************************************************************)

Module PWellformed (MY : Iso_partial)(Import MT : Iso_full).
  Module Export M := LNTemplate MT MT.

  Hint Resolve MY.To_From.

  (**************************************************************)
  (** * Well-Formedness of terms in an environment *)
  (**************************************************************)

  Definition TenvT (E:env MY.TT)(T:TT) : Prop :=
    envT RR (map MY.From E) (From T).

    Hint Unfold TenvT.

  Ltac gunfold :=
    unfold Twf, Twf_basic in *;
    unfold gTwf, gTwf_basic, wf_basic in *;
    unfold Tfsubst, Tbsubst, Tfv, TwfT, TenvT, TSize in *;
    intros;
    repeat rewrite To_From in *;
    repeat rewrite From_To in *;
    repeat rewrite MY.To_From in *;
    simpl in *; 
    simpl_env in *.

  (**************************************************************)
  (** * Well-formedness in an environment *)
  (**************************************************************)

  (** Well-formed terms/types in an environment are well-formed. *)

  Lemma TenvT_TwfT : forall (E:env MY.TT)(T:TT), 
    TenvT E T ->
    TwfT T.
  Proof.
    gunfold; eauto using envT_wfT.
  Qed.

  Hint Resolve TenvT_TwfT.

  (** Bound variable substitution has no effect on well-formed terms/types. *)

  (* Tbsubst_on_env => TenvT_Twf *)
  Lemma TenvT_Twf : forall (E:env MY.TT)(T:TT), 
    TenvT E T -> forall (k:nat) (U:TT), T = Tbsubst T k U.
  Proof.
    intros; eauto using TenvT_TwfT, TwfT_Twf.
  Qed.

  (** Environments capture all the parameters in terms/types *)

  Lemma envT_Tfv : forall (E:env MY.TT) (T:TT) (a:atom),
    a # E -> TenvT E T -> a `notin` Tfv T.
  Proof.
    gunfold;
    apply envT_fv with (r':= MY.RR)(E:= map MY.From E); auto.
  Qed.

  Lemma TenvT_dom_subset : forall (E:env MY.TT) (T:TT),
    TenvT E T -> Tfv T [<=] dom E.
  Proof.
    gunfold; intros a H0; apply dom_map_2 with (f:=MY.From).
    generalize dependent a; apply envT_dom_subset; auto.
  Qed.

  (** Parameter substitution for a fresh parameter *)

  Lemma Tfsubst_fresh : forall (E:env MY.TT)(T U:TT)(a:nat),
    a # E -> TenvT E T -> T = Tfsubst T a U.
  Proof.
    gunfold; erewrite <- fsubst_fresh; eauto; auto.  
  Qed.

  (** Permutation of substitutions when [TenvT] holds *)
  
  Lemma Tbfsubst_permutation : forall (E:env MY.TT)(T U V:TT)(a:nat),
    TenvT E U -> 
    a `notin` (Tfv V) ->
    Tbsubst (Tfsubst T a U) 0 V = Tfsubst (Tbsubst T 0 V) a U.
  Proof.
    gunfold; f_equal; eauto using bfsubst_permutation.
  Qed.

  Lemma Tbfsubst_permutation_var : forall (E:env MY.TT)(T U:TT)(a b:nat),
    a <> b ->
    TenvT E U -> 
    Tbsubst (Tfsubst T a U) 0 (To (Var RR (inl b))) =
    Tfsubst (Tbsubst T 0 (To (Var RR (inl b)))) a U.
  Proof.
    gunfold; f_equal; eauto using bfsubst_permutation_var.
  Qed.

  (**************************************************************)
  (** * Weakening of well-formedness in an environment *)
  (**************************************************************)  

  (** Preservation of Well-Formation w.r.t. environment ext *)

  Lemma extends_TenvT : forall (E F:env MY.TT) (T:TT), 
    TenvT E T -> extends E F -> TenvT F T.
  Proof.
    gunfold; eauto using extends_env.
  Qed.

  (* Weakening environments *)
  
  Lemma TenvT_weaken : forall (E F G:env MY.TT)(T:TT),
    TenvT (E ++ G) T ->
    uniq (E ++ F ++ G) ->
    TenvT (E ++ F ++ G) T.
  Proof.

    gunfold; apply envT_weaken; intuition solve_uniq.
  Qed.

  Lemma TenvT_weaken_left : forall (E F:env MY.TT)(T:TT),
    TenvT F T ->
    uniq (E ++ F) ->
    TenvT (E ++ F) T.
  Proof.
    gunfold; apply envT_weaken_left; intuition solve_uniq.
  Qed.

  Lemma TenvT_weaken_right : forall (E F:env MY.TT)(T:TT),
    TenvT E T ->
    uniq (E ++ F) ->
    TenvT (E ++ F) T.
  Proof.
    gunfold; apply envT_weaken_right; intuition solve_uniq.
  Qed.

  (**************************************************************)
  (** * Narrowing of Environments *)
  (**************************************************************)  

  (** Well-formedness does not depend on types. *)  

  Lemma TenvT_narrow : forall (E F:env MY.TT)(U V:MY.TT)(T:TT)(a:nat),
    TenvT (E ++ a ~ V ++ F) T ->
    uniq (E ++ a ~ U ++ F) -> 
    TenvT (E ++ a ~ U ++ F) T.
  Proof.
    gunfold; eapply envT_narrow; eauto.
  Qed.

  Lemma TenvT_narrow_left : forall (F:env MY.TT)(U V:MY.TT)(T:TT)(a:nat),
    TenvT (a ~ V ++ F) T ->
    uniq (a ~ U ++ F) -> 
    TenvT (a ~ U ++ F) T.
  Proof.
    gunfold; eapply envT_narrow_left; eauto; solve_uniq.
  Qed.

  Lemma TenvT_narrow_right : forall (E:env MY.TT)(U V:MY.TT)(T:TT)(a:nat),
    TenvT (E ++ a ~ V) T ->
    uniq (E ++ a ~ U) -> 
    TenvT (E ++ a ~ U) T.
  Proof.
    gunfold; eapply envT_narrow_right; eauto; solve_uniq.
  Qed.

  (**************************************************************)
  (** * Tactics II *)
  (**************************************************************)

  (** The following tactics can be used in concrete formalizations.
     They help the end user of the DGP libraries in the way that
     the end user don't need to look into the generic library.
     - [auto_rewrite] rewrites all the basic equalities
       from the [isorew] autorewrite library.

     - [gsimpl] makes [Tfsubst], [Tbsubst], [Tsize], etc. in
       each patters behaves as if they are resursively defined
       in the object languages.

     - [gsimpl in H] simplifies the assumptions as expected.

     - [gconstructor] is useful e.g. when proving the equivalence
       of the generic and concrete version of well-formedness.

     - The other tactics are auxiliary. *)

  (** [auto_rewrite]  *)

  Ltac auto_rewrite :=
    try case_var;
    intros;
    autorewrite with isorew in *;
    simpl in *;
    auto 1.

  (** [gsimpl] *)

  Ltac gsimpl_bsubst :=
    unfold Tbsubst; 
    simpl bsubst.

  Ltac gsimpl_fsubst :=
    unfold Tfsubst; 
    simpl fsubst.

  Ltac from_freevars :=
    match goal with
      | _ : context [ freevars RR (From ?T) ] |- _ =>
        replace (freevars RR (From T)) with
          (Tfv T) in *; [idtac | auto]
      | |- context [ freevars RR (From ?T) ] =>
        replace (freevars RR (From T)) with
          (Tfv T) in *; [idtac | auto]
    end.

  Ltac gsimpl_fv :=
    unfold Tfv in *; simpl in *;
      repeat from_freevars;
        destruct_notin; try solve_notin.
  
  Ltac gsimpl_size :=
    unfold TSize;
    simpl.

  Ltac from_subst :=
    match goal with
      | _ : context [To (fsubst (From ?T) ?k (From ?U))] |- _ =>
        replace (To (fsubst (From T) k (From U))) with
          (Tfsubst T k U) in * |-; [idtac | unfold Tfsubst; reflexivity]
      | _ : context [To (bsubst (From ?T) ?k (From ?U))] |- _ =>
        replace (To (bsubst (From T) k (From U))) with
          (Tbsubst T k U) in * |-; [idtac | unfold Tbsubst; reflexivity]
    end.

  Ltac from_size :=
    match goal with
      | _ : context [ size (From ?T) ] |- _ =>
        replace (size (From T)) with
          (TSize T) in *; [idtac | unfold TSize in *; reflexivity]
    end.

  Ltac gsimpl := repeat (
    gsimpl_bsubst;
    gsimpl_fsubst;
    auto_rewrite;
    try gsimpl_fv;
    simpl_alist in *;
    try gsimpl_size;
    repeat from_subst;
    repeat from_freevars;
    destruct_notin; try solve_notin;
    repeat from_size;
    auto_rewrite);
    simpl_alist in *.

  (** [gsimpl in]  *)

  Tactic Notation "gsimpl_bsubst" "in" constr(H) :=
    unfold Tbsubst in H;
    simpl bsubst in H.

  Tactic Notation "gsimpl_fsubst" "in" constr(H) :=
    unfold Tfsubst in H;
    simpl fsubst in H.

  Tactic Notation "gsimpl_fv" "in" constr(H) :=
    unfold Tfv in H;
    simpl freevars in H.

  Tactic Notation "gsimpl_size" "in" constr(H) :=
    unfold TSize in H;
    simpl size in H.

  Tactic Notation "gsimpl" "in" constr(H) := repeat (
    gsimpl_bsubst in H;
    gsimpl_fsubst in H;
    auto_rewrite;
    try gsimpl_fv in H;
    simpl_alist in *;
    try gsimpl_size in H;
    repeat from_subst;
    repeat from_freevars;
    destruct_notin; try solve_notin;
    from_size).

  (** [gconstructor] *)

  Ltac apply_wfT :=
    match goal with
      | |- wfTRep _ (Unit) => apply wf_Unit
      | |- wfTRep _ (Const _ _) => apply wf_Const
      | |- wfTRep _ (InL _ _) => apply wf_InL
      | |- wfTRep _ (InR _ _) => apply wf_InR
      | |- wfTRep _ (Pair _ _) => apply wf_Pair
      | |- wfTRep _ (Bind _ _ _) =>
        let L := fresh "L" in
          let L := gather_atoms in
            apply wf_Bind_REC_homo with L; auto; simpl; intros; destruct_notin
      | |- wfTRep _ (Rec _) => apply wf_Rec
      | |- wfT _ (Var _ _) => apply wf_fvar; auto
      | |- wfT _ (Term _) => apply wf_Term
    end.

  Ltac gsimpl_subst :=
    unfold Tbsubst; simpl;
    unfold Tfsubst; simpl;
    try case_var; intros;
    autorewrite with isorew;
    simpl in *; auto*.

  Ltac from_wfT :=
    match goal with
      | |- wfT RR (From ?T) =>
        change (wfT RR (From T)) with (TwfT T); auto
      | |- wf RR (From ?T) =>
        change (wf RR (From T)) with (Twf T); auto
    end.

  Ltac gconstructor :=
    intros;
    unfold TwfT;
    simpl;
    repeat apply_wfT;
    gsimpl_subst;
    from_wfT. 

  (** [gconstructor with]   *)

  Tactic Notation "apply_wfT" "with" constr(L) :=
    match goal with
      | |- wfTRep _ (Unit) => apply wf_Unit
      | |- wfTRep _ (Const _ _) => apply wf_Const
      | |- wfTRep _ (InL _ _) => apply wf_InL
      | |- wfTRep _ (InR _ _) => apply wf_InR
      | |- wfTRep _ (Pair _ _) => apply wf_Pair
      | |- wfTRep _ (Bind _ _ _) =>
        apply wf_Bind_REC_homo with L; auto; simpl; intros; destruct_notin
      | |- wfTRep _ (Rec _) => apply wf_Rec
      | |- wfT _ (Var _ _) => apply wf_fvar; auto
      | |- wfT _ (Term _) => apply wf_Term
    end.

  Tactic Notation "gconstructor" "with" constr(L) :=
    intros;
    unfold TwfT;
    simpl;
    repeat (apply_wfT with L);
    gsimpl_subst; from_wfT. 


  (** Customization of [gather_atoms] which originally defined
     in [MetatheoryAtom.v]
     - [gather_atoms] collects all parameter which have occurrs
       during proof.  *)
  
  Ltac gather_atoms :=
    let A := gather_atoms_with (fun x : atoms => x) in
    let B := gather_atoms_with (fun x : atom => {{ x }}) in
    let C := gather_atoms_with (fun x : TT => Tfv x) in
    let D := gather_atoms_with (fun A : Type => fun x : env A => dom x) in
      constr:(A `union` B `union` C `union` D).

  Tactic Notation "pick" "fresh" ident(Y) :=
    let L := gather_atoms in
      pick fresh Y for L.

  Ltac pick_fresh y :=
    pick fresh y.


End PWellformed.
