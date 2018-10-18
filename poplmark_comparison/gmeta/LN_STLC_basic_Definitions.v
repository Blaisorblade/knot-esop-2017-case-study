Set Implicit Arguments.

Require Import Arith_Max_extra.
Require Import LNameless_Meta.
Require Import LNameless_Meta_Env.
Require Import LNameless_Isomorphism.
Require Import LNameless_STLC_Iso.
Require Import LN_Template_One_Sort.

(** ** Pure Lambda Calculus *)

(** Reference: Chargueraud's POPLmark contribution using Locally Nameless style
   and cofinite quantification *)

(** Many of the generic properties about substitution, environments are
   already proved in a generic
   *)

(** [typ] and [trm] are already defined in LNameless_STLC_Iso.v
<<   
Notation atm := nat.

Inductive typ : Type :=
| typ_var : atm -> typ
| typ_arrow  : typ -> typ -> typ.

Inductive trm : Set :=
| trm_bvar : nat -> trm
| trm_fvar : var -> trm
| trm_abs  : trm -> trm
| trm_app  : trm -> trm -> trm.
>> *)

(** Module for terms with typing environment for term variables *)

Notation "{ k ~> u } t" := (Tbsubst t k u) (at level 67).
Notation "t ^^ u" := (Tbsubst t 0 u) (at level 67).
Notation "t ^ x" := (Tbsubst t 0 (trm_fvar x)).

(** Typing relation *)

Reserved Notation "E |= t ~: T" (at level 69).

Inductive typing : env typ -> trm -> typ -> Prop :=
| typing_var : forall E x T,
  uniq E ->
  binds x T E ->
  E |= (trm_fvar x) ~: T
| typing_abs : forall L E U T t1,
  (forall x, x `notin` L -> 
    (x ~ U ++ E) |= t1 ^ x ~: T) ->
  E |= (trm_abs t1) ~: (typ_arrow U T)
| typing_app : forall S T E t1 t2,
  E |= t1 ~: (typ_arrow S T) -> 
    E |= t2 ~: S ->
      E |= (trm_app t1 t2) ~: T

        where "E |= t ~: T" := (typing E t T).

(** Definition of values (only abstractions are values) *)

Inductive value : trm -> Prop :=
| value_abs : forall t1, 
  TwfT (trm_abs t1) -> value (trm_abs t1).

(** Reduction relation - one step in call-by-value *)

Inductive red : trm -> trm -> Prop :=
| red_beta : forall t1 t2,
  TwfT (trm_abs t1) ->
  value t2 ->
  red (trm_app (trm_abs t1) t2) (t1 ^^ t2)
| red_app_1 : forall t1 t1' t2,
  TwfT t2 ->
  red t1 t1' ->
    red (trm_app t1 t2) (trm_app t1' t2)
| red_app_2 : forall t1 t2 t2',
  value t1 ->
  red t2 t2' ->
    red (trm_app t1 t2) (trm_app t1 t2').

Notation "t ---> t'" := (red t t') (at level 68).

(** Goal is to prove preservation and progress *)

Definition preservation := forall E t t' T,
  E |= t ~: T ->
    t ---> t' ->
    E |= t' ~: T.

Definition progress := forall t T, 
  empty_env |= t ~: T ->
    value t 
    \/ exists t', t ---> t'.

