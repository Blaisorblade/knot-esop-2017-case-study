Set Implicit Arguments.

Require Export Max.
Require Export Equality.
Require Export Eqdep_dec.
Require Export Metatheory_Var.
Require Export Metatheory_Env.


(**********************************************************************)
(** * DGP Universe Language  *)
(**********************************************************************)

(** [Rep] is the universe of the representations of object languages *)

Inductive Rep : Type := 
| UNIT  : Rep
| CONST : Rep -> Rep
| REPR  : Rep -> Rep 
| PLUS  : Rep -> Rep -> Rep
| PROD  : Rep -> Rep -> Rep
| BIND  : Rep -> Rep -> Rep
| REC   : Rep.

(** The DGP universe is decidable. *)

Lemma Rep_dec : forall r r0 : Rep, {r = r0} + {r <> r0}.
Proof.
  decide equality.
Defined.

Lemma Rep_dec_or : forall r r0 : Rep, r = r0 \/ r <> r0.
Proof.
  intros; elim (Rep_dec r r0); tauto.
Defined.

Lemma Rep_dec_unicity : forall (r r0 : Rep)(H H0: r =r0), H = H0.
Proof.
  intros; auto using eq_proofs_unicity, Rep_dec_or.
Qed.

(** [case_rep] destructs the [Rep_dec] cases. *)

Ltac case_rep :=
  match goal with
    | |- context [Rep_dec ?r ?s]      => destruct (Rep_dec r s)
    | H: context [Rep_dec ?r ?s] |- _ => destruct (Rep_dec r s)
  end.

(** [noRepr] denotes that there are no embedded terms in the representation.
   - Examples: type classes in STLC or System F, or the term class in STLC. *)

Fixpoint noRepr (r:Rep) : Prop :=
  match r with
    | UNIT       => True
    | CONST _    => True
    | REPR _     => False
    | PLUS r0 r1 => noRepr r0 /\ noRepr r1
    | PROD r0 r1 => noRepr r0 /\ noRepr r1
    | BIND r0 r1 => if Rep_dec r0 REC then noRepr r1 else False
    | REC        => True
  end.

(**********************************************************************)
(** * Interpretation of the DGP universe *)
(**********************************************************************)

(** The module [Dgp] explains how to interpret the Dgp universe.
   - [Dgp] is parametrized with two sets of variables.

   - VSet stands for the class of variables.

   - QSet stands for the class of variables to be bound.

   - The basic requirement for VSet and QSet is decidability. *)

Module Dgp (VSet : GenericVarSig)(QSet: QuantificationVarSig).
  
  (** [VV] denotes for the class of variables
     which will be used as concrete term/type variables.
     - Locally nameless:  VV = nat + nat

     - de Bruijn stle :   VV = nat

     - Locally named:     VV = nat + nat

     - Nominal approach : VV = nat *)
   
  Definition VV := VSet.t.

  (** [QQ] denotes the class of variables intended
     for the abstraction variables.
     - Locally nameless:  QQ = unit type

     - de Bruijn stle :   QQ = unit type

     - Locally named:     QQ = nat

     - Nominal approach : QQ = nat *)
  
  Definition QQ := QSet.t.

  (** Interpretation of representations using inductive families. *)

  Inductive InterpretRep (r : Rep) : Rep -> Type :=
  | Unit   : InterpretRep r UNIT
  | Const  : forall (s : Rep), Interpret s -> InterpretRep r (CONST s)
  | Repr   : forall (s : Rep), Interpret s -> InterpretRep r (REPR s)
  | InL    : forall s s0, InterpretRep r s -> InterpretRep r (PLUS s s0)
  | InR    : forall s s0, InterpretRep r s0-> InterpretRep r (PLUS s s0)
  | Pair   : forall s s0, InterpretRep r s -> InterpretRep r s0 -> InterpretRep r (PROD s s0)
  | Bind   : forall r0 s, QQ -> InterpretRep r s -> InterpretRep r (BIND r0 s)
  | Rec    : Interpret r -> InterpretRep r REC

  with Interpret (r : Rep) : Type :=
  | Var : VV -> Interpret r
  | Term : InterpretRep r r -> Interpret r.

  Hint Constructors InterpretRep Interpret.

  Implicit Arguments Unit [r].

  (** Generic functions independent of the first-order representation styles:
     - Complexivity of a term which measures the depth of the term structure. *)
  
  Fixpoint sizeRep (r s : Rep)(T : InterpretRep r s){struct T} : nat :=
    match T with
      | Unit           => 0
      | Const _ _      => 0
      | Repr _ T0      => size T0
      | InL _ _ T0     => sizeRep T0
      | InR _ _ T0     => sizeRep T0
      | Pair _ _ T0 T1 => S (max (sizeRep T0) (sizeRep T1))
      | Bind _ _ _ T0  => S (sizeRep T0)
      | Rec T0         => size T0
    end

  with size (r : Rep)(T : Interpret r){struct T} : nat :=
    match T with
      | Var _ => 0
      | Term T0 => sizeRep T0
    end.

  (** [conv] is an automorphism.
     - [conv] is sometimes necessary to enable Coq's type checking.
     
     - [conv] is used to define heterogeneous substitutions using dependent types. *)

  Definition conv r r0 (e: r = r0) (T:Interpret r0) : Interpret r.
  Proof.  
    intros r r0 e T; rewrite e; exact T.
  Defined.

  Lemma conv_indep r r0 (e e0: r = r0) (T:Interpret r0) : conv e T = conv e0 T.
  Proof.  
    intros r r0 e; case e; clear e; intro e0.
    rewrite (Rep_dec_unicity e0 refl); auto.
  Qed.

  Lemma conv_id : forall (r : Rep)(e:r = r)(T:Interpret r), conv e T = T.
  Proof.
    intros r e T. 
    rewrite (Rep_dec_unicity e(refl_equal r)); reflexivity.
  Qed.  

  Hint Rewrite conv_id : isorew.
  
  Lemma conv_Var : forall r r0 (e:r = r0) x, Var r x = conv e (Var r0 x).
  Proof.
    intros r r0 e; case e; unfold conv; reflexivity.
  Qed.

  Lemma conv_size : forall r r0 (e:r = r0)(T:Interpret r0), size T = size (conv e T).
  Proof.
    intros r r0 e; case e; unfold conv; reflexivity.
  Qed.

End Dgp.

