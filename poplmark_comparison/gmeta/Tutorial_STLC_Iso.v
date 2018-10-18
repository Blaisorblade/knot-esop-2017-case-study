Set Implicit Arguments.

Require Export LNameless_Isomorphism.
Require Export Equality.

(* begin hide *)

(***********************************************************)
(* specialized tactics for the proof of [From_To]. *)
(***********************************************************)
(* Creation of a Rewrite Hint database  *)

Hint Rewrite refl_equal : iso_module.

Ltac from_to_Rep T H :=
  dependent destruction T;
  destruct T;
  try discriminate;
  repeat (
  match goal with
    | [H : InterpretRep _ _ |- _] => destruct H; try discriminate
  end);
  simpl;
  match goal with
    | H : PLUS _ _ = _ |- _ => inversion H; subst
  end;
  try (
  match goal with
    | q : QQ |- _ => destruct q
  end);
  match goal with
    | H : JMeq _ _ |- _ => rewrite <- (JMeq_eq H); simpl
  end; 
  try repeat rewrite H; auto;
  try autorewrite with iso_module; auto. 

Ltac from_to T H:=
  let v := fresh "v" in 
  destruct T as [v | ]; simpl;
  [destruct v | idtac]; auto using H.

(* end hide *)

(***********************************************************)
(** * Step 1. Defining syntax *)
(***********************************************************)

(** [atm] stands for the set of atomic types. *)

Notation atm := nat.

(** Grammar of pseudo-type  *)

Inductive typ : Type :=
| typ_var : atm -> typ
| typ_arrow  : typ -> typ -> typ.

(** [var] stands for the set of parameters (free variables). *)

Notation var := nat.

(** Grammar of pseudo-term *)

Inductive trm : Set :=
| trm_bvar : nat -> trm
| trm_fvar : var -> trm
| trm_abs  : trm -> trm
| trm_app  : trm -> trm -> trm.


(***********************************************************)

(** * Step 2. Defining isomorphisms *)

(***********************************************************)
(** ** Isomorphism module for natural number *)

Module Iso_nat.

  Definition TT := nat.

  Definition RR :=  PLUS UNIT REC.

  Fixpoint From (T: TT) : Interpret RR :=
    match T with
      | O => Term (InL _ Unit)
      | S n => Term (InR _ (Rec (From n)))
    end.

  Fixpoint To_ (T : InterpretRep RR RR) : TT :=
    match T return _ with
      | InL _ _ Unit => 0
      | InR _ _ (Rec U) => S (To U)
      | _  => 0
    end

  with To (T:Interpret RR) : TT :=
    match T with
      | Var _ => 0
      | Term U => To_ U
    end.

  Lemma To_From : forall (T:TT), To (From T) = T.
  Proof.
    intro T; induction T; simpl; f_equal; auto.
  Qed.

End Iso_nat.    

(***********************************************************)
(** For automation of some proofs:
   - This should be mentioned every time a iso module is used
     below in another definition using [Repr].

   - Example: [Iso_typ.RR] occurs in the defintion of
     [Iso_trm.RR] below. *)
(***********************************************************)

Hint Resolve Iso_nat.To_From.

(***********************************************************)
(***********************************************************)

(** ** Isomorphism module for type *)

(** Note that [atm] stands for atomic types, not for type variables. *)


Module Iso_typ <: Iso_partial.

  Definition TT := typ.


  Definition RR := PLUS (CONST Iso_nat.RR) (PROD REC REC).

  Fixpoint From (x : TT) : Interpret RR :=
    match x with
      | typ_var k => Term (InL _ (Const _ (Iso_nat.From k)))
      | typ_arrow e1 e2 =>
        Term (InR _ (Pair (Rec (From e1)) (Rec (From e2))))
    end.

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
  (* begin hide *)
  Proof.
    intro T; induction T; simpl; f_equal; auto.
  Qed.
  (* end hide *)

  Lemma From_inj : forall T U : TT, From T = From U -> T = U.
  Proof.
    intros T U H.
    rewrite <- (To_From T), <- (To_From U).
    rewrite H; auto.
  Qed.

  Definition ISO : Iso TT (Interpret RR) := (From, To).

End Iso_typ.

Hint Resolve Iso_typ.To_From.

(***********************************************************)

(** ** Isomorphism module for term *)

(** For the generic representation of [trm],
   the case of [abs] case needs special care:
   - [PROD] should come before [BIND],
   
   - otherwise, the definition of substitution would be impossible. *)
  
Module Iso_trm <: Iso_full.

  Definition TT := trm.

  Definition RR := PLUS (BIND REC REC) (PROD REC REC).

  Fixpoint From (x : TT) : Interpret RR :=
    match x with
      | trm_bvar j => Var _ (inr j)
      | trm_fvar n => Var _ (inl n)
      | trm_abs e => Term (InL _ (Bind REC tt (Rec (From e))))
      | trm_app e1 e2 => 
        Term (InR _ (Pair (Rec (From e1)) (Rec (From e2))))
    end.

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
  (* begin hide *)
  Proof.
    intro T; induction T; simpl; f_equal; auto.
  Qed.
  (* end hide *)

  Lemma From_inj : forall T U : TT, From T = From U -> T = U.
  (* begin hide *)
  Proof.
    intros.
    rewrite <- (To_From T), <- (To_From U).
    rewrite H; auto.
  Qed.
  (* end hide *)

  Lemma From_To_Rep : forall (T : InterpretRep RR RR), From (To_ T) = Term T
    
    with From_To : forall (T : Interpret RR), From (To T) = T.
  Proof.
    from_to_Rep T From_To.
    from_to T From_To_Rep.
  Qed.

  Lemma To_inj : forall T U : Interpret RR, To T = To U -> T = U.
  Proof.
    intros.
    rewrite <- (From_To T), <- (From_To U).
    rewrite H; auto.
  Qed.

  Definition ISO : Iso TT (Interpret RR) := (From, To).

End Iso_trm.

(** Making arguments implicit *)

Implicit Arguments Iso_typ.From_inj [T U].

Implicit Arguments Iso_trm.From_inj [T U].
Implicit Arguments Iso_trm.To_inj [T U].

