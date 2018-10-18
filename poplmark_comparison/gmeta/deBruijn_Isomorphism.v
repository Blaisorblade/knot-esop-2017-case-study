Set Implicit Arguments.

Require Export Variable_Sets.
Require Export deBruijn_Meta_Env.

(** This file provides a connection between the generic level
   and many concrete type systems based on some isomorphisms.

   A concrete type system [TT] is isomorphic to the type representation [RR]
   when there is an isomorphism between [TT] and [Interpret] RR. *)

Open Scope type_scope.

(** The following section collects all the functions and predicates
   which can be defined and handled generically.
   The section can be extended when new concept is created generically.
   *)

(** Isomorphisms between a representation and a concrete types/terms. *)

Definition Iso (A B : Type) := (A -> B) * (B -> A).

(** Function injectivity *)

Definition fun_inj (A B:Type)(f:A -> B) := forall (x y: A), f x = f y -> x = y.

(* ************************************************************ *)
(** * Infrastructure for Isomorphisms *)

(** Given a type [TT] and a representation type [RR],

   - [From] : [TT] -> [Interpret RR], an one-to-one function
   - [To] : [Interpret RR] -> [TT],
     an one-to-one functioen when restricted to Image of [From]
   - [To] ([From] x) = x, hence
   - [From] ([To] ([From] x)) = [From] x
   *)

Module Type Iso_partial.

  Parameter TT : Type.

  Parameter RR : Rep.
  
  Parameter From : TT -> Interpret RR.

  Parameter From_inj : fun_inj From.

  Parameter To : Interpret RR -> TT.

  Parameter To_From : forall (T:TT), To (From T) = T.

  Definition ISO : Iso TT (Interpret RR) := (From, To).

  Hint Rewrite To_From : isorew.

  Hint Resolve To_From.

End Iso_partial.

(** If there are variables, then [From] and [To] build a real
   isomorphism between [TT] and [Interpret RR].

   - [From] and [To] are one-to-one and onto.
   - [To] ([From} x) = x.
   *)

Module Type Iso_full.

  Include Type Iso_partial.

  Parameter From_To : forall (T:Interpret RR), From (To T) = T.

  Parameter To_inj : fun_inj To.

  Hint Rewrite From_To : isorew.

  Hint Resolve From_To.

End Iso_full.

(** Isomorphism for [nat] will be the basic for other isomorphisms. *)

Module Iso_nat.

  Definition TT := nat.

  Definition RR :=
    PLUS
    UNIT                   (* 0 *)
    REC.                   (* S *)

  Fixpoint From (T: TT) : Interpret RR :=
    match T with
      | O => Term (InL _ Unit)
      | S n => Term (InR _ (Rec (From n)))
    end.

  (** The following definition using a garbage for never-appearing cases
     is simpler than other, more accurate variations. *)

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

(** For automation *)

Lemma Iso_nat_REC : Iso_nat.RR <> REC.  
Proof.
  unfold Iso_nat.RR; congruence.
Qed.

Hint Resolve Iso_nat_REC.
Hint Resolve Iso_nat.To_From.

Hint Rewrite Iso_nat.To_From : iso_module.

(** specialized tactics for the proof of [From_To]. *)

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

