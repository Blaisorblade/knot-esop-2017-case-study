Set Implicit Arguments.

Require Export LNameless_Isomorphism.

(** * Simply Typed Lambda Calculus *)

(** Reference: Chargueraud's POPLmark solution using Locally Nameless style
   and cofinite quantification *)

(** Language Syntax for STLC *)

(** [atm] stands for the set of atomic types. *)
Notation atm := nat.

Inductive typ : Type :=
| typ_var : atm -> typ
| typ_arrow  : typ -> typ -> typ.

(* var = nat for free variables. *)

Notation var := nat.

Inductive trm : Set :=
| trm_bvar : nat -> trm
| trm_fvar : var -> trm
| trm_abs  : trm -> trm
| trm_app  : trm -> trm -> trm.


(** Isomorphism modules *)

Module Iso_typ <: Iso_partial.

  Definition TT := typ.

  Definition RR :=
    PLUS
    (CONST Iso_nat.RR)          (* typ_var *)
    (PROD REC REC).             (* typ_arrow *)

  Fixpoint From (x : TT) : Interpret RR :=
    match x with
      | typ_var k => Term (InL _ (Const _ (Iso_nat.From k)))
      | typ_arrow e1 e2 =>
        Term (InR _ (Pair (Rec (From e1)) (Rec (From e2))))
    end.

  (** The following definition using a garbage for never-appearing cases
     is simpler than other, more accurate variations. *)

  Fixpoint To_ (T : InterpretRep RR RR) : typ :=
    match T return _ with 
      | InL _ _ (Const (PLUS UNIT REC) k) =>
        typ_var (Iso_nat.To k) 
      | InR _ _ (Pair _ _ (Rec k1) (Rec k2)) =>
        typ_arrow (To k1) (To k2)
      | _ => typ_var O
    end

  with To (T : Interpret RR) : typ :=
    match T with
      | Term T0 => To_ T0
      | _ => typ_var O
    end.

  Lemma To_From : forall (T:TT), To (From T) = T.
  Proof.
    intro T; induction T; simpl; f_equal; auto.
  Qed.

  Lemma From_inj : forall T U : TT, From T = From U -> T = U.
  Proof.
    intros T U H.
    rewrite <- (To_From T), <- (To_From U).
    rewrite H; auto.
  Qed.

  Definition ISO : Iso TT (Interpret RR) := (From, To).

End Iso_typ.

(* For automation *)

Hint Resolve Iso_typ.To_From.

Hint Rewrite Iso_typ.To_From : iso_module.

Module Iso_trm <: Iso_full.

  Definition TT := trm.

  (** For the generic representation of [trm],
     [trm_abs] case needs special care:

     - [PROD] should come before [BIND].
     - Otherwise, the definition of substitution would be impossible. *)
  
  Definition RR :=
    PLUS
    (BIND REC REC)              (* trm_abs *)
    (PROD REC REC).             (* trm_app *)

  Fixpoint From (x : TT) : Interpret RR :=
    match x with
      | trm_bvar j => Var _ (inr j)
      | trm_fvar n => Var _ (inl n)
      | trm_abs e => Term (InL _ (Bind REC tt (Rec (From e))))
      | trm_app e1 e2 => 
        Term (InR _ (Pair (Rec (From e1)) (Rec (From e2))))
    end.

  (** The following definition using a garbage for never-appearing cases
     is simpler than other, more accurate variations. *)

  Fixpoint To_ (T : InterpretRep RR RR) : trm :=
    match T return _ with
      | InL _ _ (Bind REC _ _ (Rec T1)) =>
        trm_abs (To T1)
      | InR _ _ (Pair _ _ (Rec T0) (Rec T1)) =>
        trm_app (To T0) (To T1)
      | _ =>
        trm_fvar 0 (* garbage needed *)
    end

  with To (T : Interpret RR) : trm :=
    match T with
      | Var (inl k) => trm_fvar k
      | Var (inr j) => trm_bvar j
      | Term T0 => To_ T0
    end.

  Lemma To_From : forall (T:TT), To (From T) = T.
  Proof.
    intro T; induction T; simpl; f_equal; auto.
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

  Lemma To_inj : forall T U : Interpret RR, To T = To U -> T = U.
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


