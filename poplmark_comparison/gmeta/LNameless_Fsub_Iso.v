Set Implicit Arguments.

Require Export LNameless_Isomorphism.

(** * Fsub Part 1A and 2A *)

(** Reference: Chargueraud's POPL solution using Locally Nameless style
   and cofinite quantification *)

(** Language Syntax for System F with subtyping *)

(* var = nat for free variables. *)

Notation var := atom.

Inductive typ : Set :=
| typ_bvar  : nat -> typ
| typ_fvar  : var -> typ
| typ_top   : typ
| typ_arrow : typ -> typ -> typ
| typ_all   : typ -> typ -> typ.

Inductive trm : Set :=
| trm_bvar : nat -> trm
| trm_fvar : var -> trm
| trm_app  : trm -> trm -> trm
| trm_abs  : typ -> trm -> trm
| trm_tapp : trm -> typ -> trm
| trm_tabs : typ -> trm -> trm.

(** Isomorphism modules *)

Module Iso_typ <: Iso_full.

  Definition TT := typ.

  Hint Unfold TT.

  (** For the generic representation of [typ],
     [typ_all] case needs special care:

     - [PROD] should come before [BIND].
     - Otherwise, the definition of substitution would be impossible. *)
  
  Definition RR :=
    PLUS
    UNIT                            (* typ_top *)
    (PLUS
      (PROD REC REC)                (* typ_arrow *)
      (PROD REC (BIND REC REC))).   (* typ_all *)

  Fixpoint From (T : TT) : Interpret RR :=
    match T with
      | typ_bvar j      => Var _ (inr j)
      | typ_fvar n      => Var _ (inl n)
      | typ_top         => Term (InL _ Unit)
      | typ_arrow T0 T1 => Term (InR _ (InL _ (Pair (Rec (From T0)) (Rec (From T1)))))
      | typ_all T0 T1   => Term (InR _ (InR _ (Pair (Rec (From T0)) (Bind REC tt (Rec (From T1))))))
    end.

  (** The following definition using a garbage for never-appearing cases
     is simpler than other, more accurate variations. *)

  Fixpoint To_ (T : InterpretRep RR RR) : typ :=
    match T return _ with
      | InL _ _ Unit =>
        typ_top
      | InR _ _ (InL _ _ (Pair _ _ (Rec T0) (Rec T1))) =>
        typ_arrow (To T0) (To T1)
      | InR _ _ (InR _ _ (Pair _ _ (Rec T0) (Bind REC _ tt (Rec T1)))) =>
        typ_all (To T0) (To T1)
      | _ =>
        typ_fvar 0 (* garbage needed *)
    end

  with To (T : Interpret RR) : typ :=
    match T with
      | Var (inl k) => typ_fvar k
      | Var (inr j) => typ_bvar j
      | Term T0 => To_ T0
    end.

  Lemma To_From : forall (T:TT), To (From T) = T.
  Proof.
    induction T; simpl; f_equal; auto.
  Qed.

  Lemma From_inj : forall T U : TT, From T = From U -> T = U.
  Proof.
    intros T U H.
    rewrite <- (To_From T), <- (To_From U).
    rewrite H; auto.
  Qed.

  Lemma From_To_Rep : forall (T : InterpretRep RR RR), From (To_ T) = Term T
    
    with From_To : forall (T : Interpret RR), From (To T) = T.
  Proof.
    from_to_Rep T From_To.

    from_to T From_To_Rep.
  Qed.

  Lemma To_inj : forall (T U:Interpret RR), To T = To U -> T = U.
  Proof.
    intros T U H.
    rewrite <- (From_To T), <- (From_To U).
    rewrite H; auto.
  Qed.

  Definition ISO : Iso TT (Interpret RR) := (From, To).

End Iso_typ.


(** For automation *)

Hint Resolve Iso_typ.To_From.
Hint Resolve Iso_typ.From_To.

Hint Rewrite Iso_typ.To_From : iso_module.
Hint Rewrite Iso_typ.From_To : iso_module.

Module Iso_trm <: Iso_full.

  Definition TT := trm.

  (** For the generic representation of [trm],
     [trm_abs] and [trm_tabs] cases need special care:

     - [PROD] should come before [BIND].
     - Otherwise, the definition of substitution would be impossible. *)
  
  Definition RR :=
    PLUS (PROD REC REC)                                     (* trm_app  *)
    (PLUS (PROD (REPR Iso_typ.RR) (BIND REC REC))           (* trm_abs  *)
      (PLUS (PROD REC (REPR Iso_typ.RR))                    (* trm_tapp *)
        (PROD (REPR Iso_typ.RR) (BIND Iso_typ.RR REC)))).   (* trm_tabs *)

  Fixpoint From (T : TT) : Interpret RR :=
    match T return Interpret RR with
      | trm_bvar j   => Var _ (inr j)
      | trm_fvar n   => Var _ (inl n)
      | trm_app T0 T1  =>
        Term (InL _ (Pair (Rec (From T0)) (Rec (From T1))))
      | trm_abs U T0  =>
        Term (InR _ (InL _ (Pair (Repr _ (Iso_typ.From U)) (Bind REC tt (Rec (From T0))))))
      | trm_tapp T0 U =>
        Term (InR _ (InR _ (InL _ (Pair (Rec (From T0)) (Repr _ (Iso_typ.From U))))))
      | trm_tabs U T0 =>
        Term (InR _ (InR _ (InR _ (Pair (Repr _ (Iso_typ.From U)) (Bind Iso_typ.RR tt (Rec (From T0)))))))
    end.

  (** The following definition using a garbage for never-appearing cases
     is simpler than other, more accurate variations. *)

  Fixpoint To_ (T : InterpretRep RR RR) : TT :=
    match T return _ with
      | InL _ _ (Pair _ _ (Rec U) (Rec V)) =>
        trm_app (To U) (To V)
      | InR _ _ (InL _ _ (Pair _ _ (Repr (PLUS (UNIT) (PLUS (PROD REC REC) (PROD REC (BIND REC REC)))) t) (Bind REC _ _ (Rec U)))) =>
        trm_abs (Iso_typ.To t) (To U)
      | InR _ _ (InR _ _ (InL _ _ (Pair _ _ (Rec U) (Repr (PLUS (UNIT) (PLUS (PROD REC REC) (PROD REC (BIND REC REC)))) t)))) =>
        trm_tapp (To U) (Iso_typ.To t)
      | InR _ _ (InR _ _ (InR _ _ (Pair _ _ (Repr (PLUS (UNIT) (PLUS (PROD REC REC) (PROD REC (BIND REC REC)))) t) (Bind (PLUS UNIT (PLUS (PROD REC REC) (PROD REC (BIND REC REC)))) _ _ (Rec U))))) =>
        trm_tabs (Iso_typ.To t) (To U)
      | _ => trm_fvar 0
    end
  with To (T : Interpret RR) : TT :=
    match T return trm with
      | Var (inl k) => trm_fvar k
      | Var (inr l) => trm_bvar l
      | Term U => To_ U
    end.
  
  Lemma To_From : forall (T:TT), To (From T) = T.
  Proof.
    induction T; simpl; f_equal; auto.
  Qed.

  Lemma From_inj : forall T U : TT, From T = From U -> T = U.
  Proof.
    intros T U H.
    rewrite <- (To_From T), <- (To_From U).
    rewrite H; auto.
  Qed.

  Lemma From_To_Rep : forall (T : InterpretRep RR RR), From (To_ T) = Term T
    
    with From_To : forall (T : Interpret RR), From (To T) = T.
  Proof.
    from_to_Rep T From_To.
    from_to T From_To_Rep.
  Qed.

  Lemma To_inj : forall (T U:Interpret RR), To T = To U -> T = U.
  Proof.
    intros T U H.
    rewrite <- (From_To T), <- (From_To U).
    rewrite H; auto.
  Qed.

  Definition ISO : Iso TT (Interpret RR) := (From, To).

End Iso_trm.

(** Making implicit arguments *)

Implicit Arguments Iso_typ.From_inj [T U].

Implicit Arguments Iso_trm.From_inj [T U].
Implicit Arguments Iso_trm.To_inj [T U].

(** For noRepr cases *)

Lemma typ_noRepr : noRepr Iso_typ.RR.
Proof.
  firstorder.
Qed.

Lemma trm_typ : Iso_trm.RR <> Iso_typ.RR.
Proof.
red; intro Heq; discriminate.
Qed.

Lemma Iso_typ_REC : Iso_typ.RR <> REC.  
Proof.
  unfold Iso_typ.RR; congruence.
Qed.

Hint Resolve typ_noRepr trm_typ Iso_typ_REC.


