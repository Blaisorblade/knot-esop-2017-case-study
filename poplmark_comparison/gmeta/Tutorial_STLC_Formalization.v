(** Reference: POPLmark contribution using Locally Nameless style
   and cofinite quantification by #<a href="http://www.chargueraud.org/arthur/research/2007/binders/">#Aydemir et al. 2008#</a># *)

Set Implicit Arguments.

Require Import LNameless_STLC_Iso.
Require Import LN_Template_One_Sort.

(***********************************************************)

(** * Step 3. Importing the infrastructure  *)

(** The first thing to do is to import a suitable template
    for STLC using isomorphisms for [typ] and [trm]. *)

(** [Module Export M := PWellFormed Iso_typ Iso_trm.]
   
   This is included in LN_Template_One_Sort. *)

(** In the imported template,
   some definitions and many lemmas about their properties
   are already included.

   #<table>
   <tr><th width="200px">#Aydemir et al.#<th>#GMeta Templates#</tr>
   <tr><td>#[Fixpoint open_rec]#<td>#[Fixpoint Tbsubst]#</tr>
   <tr><td>#[Fixpoint subst]#<td>#[Fixpoint Tfsubst]#</tr>
   <tr><td>#[Fixpoint fv]#<td>#[Fixpoint Tfv]#</tr>
   <tr><td>#[Lemma open_rec_term_core]#<td>#[Lemma wfT_Tbsubst_core]#</tr>
   <tr><td>#[Lemma open_rec_term]#<td>#[Lemma wfT_Tbsubst_id]#</tr>
   <tr><td>#[Lemma subst_fresh]#<td>#[Lemma Tfsubst_fresh]#</tr>
   <tr><td>#[Lemma subst_open]#<td>#[Lemma Tbfsubst_permutation_core]#</tr>
   <tr><td>#[Lemma subst_open_var]#<td>#[Lemma Tbfsubst_permutation_var_wfT]#</tr>
   <tr><td>#[Lemma subst_intro]#<td>#[Lemma Tbfsubst_var_intro]#</tr>
   <tr><td>#[Lemma subst_term]#<td>#[Lemma wfT_Tfsubst]#</tr>
   </table>#
*)
   
(***********************************************************)

(** * Step 4. Start of Formalization  *)

(***********************************************************)

(** ** 4-1. Definitions  *)

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
