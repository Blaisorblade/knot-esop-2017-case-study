Set Implicit Arguments.

Require Export deBruijn_Isomorphism.

(** * System F with subtyping *)

(** Reference: Vouillon's POPLmark solution using de Bruijn indices *)

(** Language Syntax for Fsub *)

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

(** Isomorphism modules *)

Module Iso_typ <: Iso_full.

  Definition TT := typ.

  (** For the generic representation of [trm],
     [all] case needs special care:

     - [PROD] should come before [BIND].
     - Otherwise, the definition of substitution would be impossible. *)
  
  Definition RR := 
    PLUS 
    UNIT                          (* top *)
    (PLUS
      (PROD REC REC)              (* arrow *)
      (PROD REC (BIND REC REC))). (* all *)

  Fixpoint From (x : TT) : Interpret RR :=
    match x with
      | tvar k => Var _ k
      | top => Term (InL _ (Unit))
      | arrow e1 e2 =>
        Term (InR _ (InL _ (Pair (Rec (From e1)) (Rec (From e2)))))
      | all e1 e2 =>
        Term (InR _ (InR _ (Pair (Rec (From e1))
                                 (Bind REC tt (Rec (From e2))))))
    end.

  (** The following definition using a garbage for never-appearing cases
     is simpler than other, more accurate variations. *)

  Fixpoint To_ (T : InterpretRep RR RR) : typ :=
    match T return _ with
      | InL _ _ (Unit) => 
        top
      | InR _ _ (InL _ _ (Pair _ _ (Rec T0) (Rec T1))) =>
        arrow (To T0) (To T1)
      | InR _ _ (InR _ _ (Pair _ _ (Rec T0) (Bind REC _ _ (Rec T1)))) =>
        all (To T0) (To T1)
      | _ =>
        tvar 0 (* garbage needed *)
    end

  with To (T : Interpret RR) : typ :=
    match T with
      | Var k => tvar k
      | Term T0 => To_ T0
    end.

  Lemma To_From : forall (T:TT), To (From T) = T.
  Proof.
    induction T ; simpl; auto.
    rewrite IHT1, IHT2; reflexivity.
    rewrite IHT1, IHT2; reflexivity.
  Qed.

  Definition ISO : Iso TT (Interpret RR) := (From, To).

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

End Iso_typ.

(** For automation *)

Hint Resolve Iso_typ.To_From.
Hint Resolve Iso_typ.From_To.

Hint Rewrite Iso_typ.To_From : iso_module.
Hint Rewrite Iso_typ.From_To : iso_module.

Module Iso_trm <: Iso_full.

  Definition TT := term.

  (** For the generic representation of [trm],
     [trm_abs] and [trm_tabs] cases need special care:

     - [PROD] should come before [BIND].
     - Otherwise, the definition of substitution would be impossible. *)
  
  Definition RR := 
     PLUS
     (PROD (REPR Iso_typ.RR) (BIND REC REC))              (* trm_abs  *)
     (PLUS
       (PROD REC REC)                                     (* trm_app  *)
       (PLUS
         (PROD (REPR Iso_typ.RR) (BIND Iso_typ.RR REC))   (* trm_tabs *)
         (PROD REC (REPR Iso_typ.RR)))).                  (* trm_tapp *)

  Fixpoint From (x : TT) : Interpret RR :=
    match x with
      | var k => Var _ k
      | abs T1 t2 => 
        Term (InL _ (Pair (Repr _ (Iso_typ.From T1)) 
                          (Bind REC tt (Rec (From t2)))))
      | app t1 t2 =>
        Term (InR _ (InL _ (Pair (Rec (From t1)) (Rec (From t2)))))
      | tabs T1 t2 =>
        Term (InR _ (InR _ (InL _ (Pair 
          (Repr _ (Iso_typ.From T1))
          (Bind Iso_typ.RR tt (Rec (From t2)))))))
      | tapp t1 T2 =>
        Term (InR _ (InR _ (InR _ (Pair
          (Rec (From t1))
          (Repr _ (Iso_typ.From T2))))))
    end.

  (** The following definition using a garbage for never-appearing cases
     is simpler than other, more accurate variations. *)

  Fixpoint To_ (T : InterpretRep RR RR) : term :=
    match T return _ with
      | InL _ _ (Pair _ _ (Repr 
        (PLUS 
          UNIT                         
          (PLUS
            (PROD REC REC)             
            (PROD REC (BIND REC REC)))) t)
                                (Bind REC _ _ (Rec U)))
      => abs (Iso_typ.To t) (To U)
      | InR _ _ (InL _ _ (Pair _ _ (Rec U) (Rec V)))
        => app (To U) (To V)
      | InR _ _ (InR _ _ (InL _ _ (Pair _ _
          (Repr 
            (PLUS 
              UNIT                         
              (PLUS
                (PROD REC REC)             
                (PROD REC (BIND REC REC)))) t)
          (Bind 
            (PLUS 
              UNIT                         
              (PLUS
                (PROD REC REC)             
                (PROD REC (BIND REC REC))))
            _ _ (Rec U)))))
      => tabs (Iso_typ.To t) (To U)
      | InR _ _ (InR _ _ (InR _ _ (Pair _ _
          (Rec U)
          (Repr 
            (PLUS 
              UNIT                         
              (PLUS
                (PROD REC REC)             
                (PROD REC (BIND REC REC)))) t))))
      => tapp (To U) (Iso_typ.To t)
      | _ =>
        var 0 (* garbage needed *)
    end
  with To (T : Interpret RR) : term :=
    match T return term with
      | Var k => var k
      | Term T0 => To_ T0
    end.

  Lemma To_From : forall (T:TT), To (From T) = T.
  Proof.
    intro T; induction T; simpl; f_equal; auto.
  Qed.

  Definition ISO : Iso TT (Interpret RR) := (From, To).

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

End Iso_trm.

(** Making implicit arguments *)

Implicit Arguments Iso_typ.From_inj [T U].
Implicit Arguments Iso_typ.To_inj [T U].

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

