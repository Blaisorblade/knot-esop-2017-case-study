Set Implicit Arguments.

Require Import Arith_Max_extra.
Require Import LNameless_Meta.
Require Import LNameless_Meta_Env.
Require Import LNameless_Isomorphism.
Require Import LNameless_Fsub_Iso.
Require Import LN_Template_Two_Sort.

(* ************************************************************ *)
(** ** Fsub Part 1A and 2A *)

(** Reference: Chargueraud's POPL solution using Locally Nameless style
   and cofinite quantification *)

(****************************************************************************)
(****************************************************************************)
(** Here begins a concrete formalization of System Fsub for part 1A and 2A. *)
(****************************************************************************)
(****************************************************************************)

(** [typ] and [trm] are already defined in LNameless_Fsub_Iso.v
<<   
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
>> *)

(** Many of the generic properties about substitution, environments are
   already proved in a generic
   *)

(** M_tt, M_yt, M_yy, and M_ty are already defined in LN_Template_Two_Sort.v *)

(** Notation for opening up binders with type or term variables *)

Notation "T 'open_tt_var' X" := (M_yy.M.Tbsubst T 0 (typ_fvar X)) (at level 67).
Notation "t 'open_te_var' X" := (M_yt.M.Tbsubst t 0 (typ_fvar X)) (at level 67).
Notation "t 'open_ee_var' x" := (M_tt.M.Tbsubst t 0 (trm_fvar x)) (at level 67).

(** Types as locally closed pre-types *)

Inductive type : typ -> Prop :=
| type_top :
  type typ_top
| type_var : forall (X:atom),
  type (typ_fvar X)
| type_arrow : forall T1 T2,
  type T1 -> 
  type T2 -> 
  type (typ_arrow T1 T2)
| type_all : forall L T1 T2,
  type T1 ->
  (forall (X:atom), X `notin` L -> type (T2 open_tt_var X)) ->
  type (typ_all T1 T2).

(** Terms as locally closed pre-terms *)

Inductive term : trm -> Prop :=
| term_var : forall (x:atom),
  term (trm_fvar x)
| term_abs : forall L V e1,
  type V ->
  (forall (x:atom), x `notin` L -> term (e1 open_ee_var x)) ->
  term (trm_abs V e1)
| term_app : forall e1 e2,
  term e1 ->
  term e2 ->
  term (trm_app e1 e2)
| term_tabs : forall L V e1,
  type V ->
  (forall (X:atom), X `notin` L -> term (e1 open_te_var X)) ->
  term (trm_tabs V e1)
| term_tapp : forall e1 V,
  term e1 ->
  type V ->
  term (trm_tapp e1 V).

(** Binding are either mapping type or term variables. 
 [X ~<: T] is a subtyping asumption and [x ~: T] is
 a typing assumption *)

Inductive bind : Set :=
| bind_sub : typ -> bind
| bind_typ : typ -> bind.

Notation "X ~<: T" := (X ~ bind_sub T) (at level 31, left associativity).

Notation "x ~: T" := (x ~ bind_typ T) (at level 31, left associativity).

(** Environment is an associative list of bindings. *)

(** Well-formedness of a pre-type T in an environment E:
  all the type variables of T must be bound via a
  subtyping relation in E. This predicates implies
  that T is a type *)


Inductive wft : env bind -> typ -> Prop :=
| wft_top : forall E, 
  wft E typ_top
| wft_var : forall U E X,
  binds X (bind_sub U) E ->
  wft E (typ_fvar X) 
| wft_arrow : forall E T1 T2,
  wft E T1 -> 
  wft E T2 -> 
  wft E (typ_arrow T1 T2)
| wft_all : forall L E T1 T2,
  wft E T1 ->
  (forall (X:atom), X `notin` L -> wft (X ~<: T1 ++ E) (T2 open_tt_var X)) ->
  wft E (typ_all T1 T2).

(** A environment E is well-formed if it contains no duplicate bindings
  and if each type in it is well-formed with respect to the environment
  it is pushed on to. *)

Inductive okt : env bind -> Prop :=
| okt_empty :
  okt empty_env
| okt_sub : forall E X T,
  okt E -> wft E T -> X # E -> okt (X ~<: T ++ E)
| okt_typ : forall E x T,
  okt E -> wft E T -> x # E -> okt (x ~: T ++ E).

(** Subtyping relation *)

Inductive sub : env bind -> typ -> typ -> Prop :=
| sub_top : forall E S,
  okt E ->
  wft E S ->
  sub E S typ_top
| sub_refl_tvar : forall E X,
  okt E ->
  wft E (typ_fvar X) ->
  sub E (typ_fvar X) (typ_fvar X)
| sub_trans_tvar : forall U E T X,
  binds X (bind_sub U) E ->
  sub E U T ->
  sub E (typ_fvar X) T
| sub_arrow : forall E S1 S2 T1 T2,
  sub E T1 S1 ->
  sub E S2 T2 ->
  sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
| sub_all : forall L E S1 S2 T1 T2,
  sub E T1 S1 ->
  (forall (X:atom), X `notin` L ->
    sub (X ~<: T1 ++ E) (S2 open_tt_var X) (T2 open_tt_var X)) ->
  sub E (typ_all S1 S2) (typ_all T1 T2).

(** Typing relation *)

Inductive typing : env bind -> trm -> typ -> Prop :=
| typing_var : forall E x T,
  okt E ->
  binds x (bind_typ T) E ->
  typing E (trm_fvar x) T
| typing_abs : forall L E V e1 T1,
  (forall (x:atom), x `notin` L ->
    typing (x ~: V ++ E) (e1 open_ee_var x) T1) ->
  typing E (trm_abs V e1) (typ_arrow V T1)
| typing_app : forall T1 E e1 e2 T2,
  typing E e1 (typ_arrow T1 T2) ->
  typing E e2 T1 ->
  typing E (trm_app e1 e2) T2
| typing_tabs : forall L E V e1 T1,
  (forall (X:atom), X `notin` L ->
    typing (X ~<: V ++ E) (e1 open_te_var X) (T1 open_tt_var X)) ->
  typing E (trm_tabs V e1) (typ_all V T1)
| typing_tapp : forall T1 E e1 T T2,
  typing E e1 (typ_all T1 T2) ->
  sub E T T1 ->
  typing E (trm_tapp e1 T) (M_yy.M.Tbsubst T2 0 T)
| typing_sub : forall S E e T,
  typing E e S ->
  sub E S T ->
  typing E e T.

(** Values *)

Inductive value : trm -> Prop :=
| value_abs  : forall V e1, term (trm_abs V e1) -> value (trm_abs V e1)
| value_tabs : forall V e1, term (trm_tabs V e1) -> value (trm_tabs V e1).

(** One-step reduction *)

Inductive red : trm -> trm -> Prop :=
| red_app_1 : forall e1 e1' e2,
  term e2 ->
  red e1 e1' ->
  red (trm_app e1 e2) (trm_app e1' e2)
| red_app_2 : forall e1 e2 e2',
  value e1 ->
  red e2 e2' ->
  red (trm_app e1 e2) (trm_app e1 e2')
| red_tapp : forall e1 e1' V,
  type V ->
  red e1 e1' ->
  red (trm_tapp e1 V) (trm_tapp e1' V)
| red_abs : forall V e1 v2,
  term (trm_abs V e1) ->
  value v2 ->
  red (trm_app (trm_abs V e1) v2) (M_tt.M.Tbsubst e1 0 v2)
| red_tabs : forall V1 e1 V2,
  term (trm_tabs V1 e1) ->
  type V2 ->
  red (trm_tapp (trm_tabs V1 e1) V2) (M_yt.M.Tbsubst e1 0 V2).

(** Our goal is to prove preservation and progress *)

Definition preservation := forall E e e' T,
  typing E e T -> 
  red e e' -> 
  typing E e' T.

Definition progress := forall e T,
  typing empty_env e T -> 
  value e \/ exists e', red e e'.

