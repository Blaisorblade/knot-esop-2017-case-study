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

(** For cases where generic and non-generic concepts are mixed,
   it is sometimes better to work with original definitions.

   - Induction on well-formed terms is a typical case.
   - Although we have to give a double definition and
   prove its equivalence to the generic one,
   it still saves a lot about the generic properties.

   - It is still possible to work with the generic definitions only,
   but some proofs would demand size induction instead of structural inductions.
   *)

(** Original definition of well-formed types. *)

Inductive type : typ -> Prop :=
  | type_top : type typ_top
  | type_var : forall X, type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 -> type T2 -> type (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 -> (forall X, X `notin` L -> type (M_yy.M.Tbsubst T2 0 (typ_fvar X))) ->
      type (typ_all T1 T2).

Hint Constructors type.
Hint Resolve type_top type_var type_var type_all.

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L V e1,
      M_yy.M.TwfT V ->
      (forall x, x `notin` L -> term (M_tt.M.Tbsubst e1 0 (trm_fvar x))) ->
      term (trm_abs V e1)
  | term_app : forall e1 e2,
      term e1 ->
      term e2 ->
      term (trm_app e1 e2)
  | term_tabs : forall L V e1,
      M_yy.M.TwfT V ->
      (forall X, X `notin` L -> term (M_yt.M.Tbsubst e1 0 (typ_fvar X))) ->
      term (trm_tabs V e1)
  | term_tapp : forall e1 V,
      term e1 ->
      M_yy.M.TwfT V ->
      term (trm_tapp e1 V).

Hint Constructors term.

Inductive wft : env typ -> env typ -> typ -> Prop :=
| wft_top : forall E F, 
  wft E F typ_top
| wft_var : forall U E F X,
  binds X U E ->
  wft E F (typ_fvar X) 
| wft_arrow : forall E F T1 T2,
  wft E F T1 -> 
  wft E F T2 -> 
  wft E F (typ_arrow T1 T2)
| wft_all : forall E F T1 T2 L V,
  wft E F T1 ->
  (forall X, X `notin` L -> wft (X ~ V ++ E) F (M_yy.M.Tbsubst T2 0 (typ_fvar X))) ->
  wft E F (typ_all T1 T2).

Hint Constructors wft.

(** The concept of "Binding" in Chargueraud's original code
   needs some adaptation

   - Instead of using mixed environments, we use two kinds of environments.
   - An environment is a pair of two disjoint environments.
   - One for subtyping variables
   - The other for term variables
   - We distinguish them by giving different names.

   - This is possible because there is no interaction between type variables
   and term variables.
   *)

(** Subtyping relation *)

Inductive sub : env typ -> env typ -> typ -> typ -> Prop :=
| sub_top : forall E F S,
  M_yy.Ywf_env E ->
  M_yy.YTenvT E F S ->
  sub E F S typ_top
| sub_refl_tvar : forall E F X,
  M_yy.Ywf_env E ->
  M_yy.YTenvT E F (typ_fvar X) ->
  sub E F (typ_fvar X) (typ_fvar X)
| sub_trans_tvar : forall U E F T X,
  binds X U E ->
  sub E F U T ->
  sub E F (typ_fvar X) T
| sub_arrow : forall E F S1 S2 T1 T2,
  sub E F T1 S1 ->
  sub E F S2 T2 ->
  sub E F (typ_arrow S1 S2) (typ_arrow T1 T2)
| sub_all : forall L E F S1 S2 T1 T2,
  sub E F T1 S1 ->
  (forall X, X `notin` L ->
    sub (X ~ T1 ++ E) F (M_yy.M.Tbsubst S2 0 (typ_fvar X)) (M_yy.M.Tbsubst T2 0 (typ_fvar X))) ->
  sub E F (typ_all S1 S2) (typ_all T1 T2).

(** Typing relation *)

Inductive typing : env typ -> env typ -> trm -> typ -> Prop :=
| typing_var : forall E F x T,
  YTwf_env E F ->
  binds x T F ->
  typing E F (trm_fvar x) T
| typing_abs : forall L E F V e1 T1,
  (forall x, x `notin` L ->
    typing E (x ~ V ++ F) (M_tt.M.Tbsubst e1 0 (trm_fvar x)) T1) ->
  typing E F (trm_abs V e1) (typ_arrow V T1)
| typing_app : forall T1 E F e1 e2 T2,
  typing E F e1 (typ_arrow T1 T2) ->
  typing E F e2 T1 ->
  typing E F (trm_app e1 e2) T2
| typing_tabs : forall L E F V e1 T1,
  (forall X, X `notin` L ->
    typing (X ~ V ++ E) F (M_yt.M.Tbsubst e1 0 (typ_fvar X)) (M_yy.M.Tbsubst T1 0 (typ_fvar X))) ->
  typing E F (trm_tabs V e1) (typ_all V T1)
| typing_tapp : forall T1 E F e1 T T2,
  typing E F e1 (typ_all T1 T2) ->
  sub E F T T1 ->
  typing E F (trm_tapp e1 T) (M_yy.M.Tbsubst T2 0 T)
| typing_sub : forall S E F e T,
  typing E F e S ->
  sub E F S T ->
  typing E F e T.

(** Values *)

Inductive value : trm -> Prop :=
| value_abs  : forall V e1, TTwfT (trm_abs V e1) ->
  value (trm_abs V e1)
| value_tabs : forall V e1, TTwfT (trm_tabs V e1) ->
  value (trm_tabs V e1).

(** One-step reduction *)

Inductive red : trm -> trm -> Prop :=
| red_app_1 : forall e1 e1' e2,
  TTwfT e2 ->
  red e1 e1' ->
    red (trm_app e1 e2) (trm_app e1' e2)
| red_app_2 : forall e1 e2 e2',
  value e1 ->
  red e2 e2' ->
    red (trm_app e1 e2) (trm_app e1 e2')
| red_tapp : forall e1 e1' V,
  M_yy.M.TwfT V ->
  red e1 e1' ->
    red (trm_tapp e1 V) (trm_tapp e1' V)
| red_abs : forall V e1 v2,
  TTwfT (trm_abs V e1) ->
  value v2 ->
  red (trm_app (trm_abs V e1) v2) (M_tt.M.Tbsubst e1 0 v2)
| red_tabs : forall V1 e1 V2,
  TTwfT (trm_tabs V1 e1) ->
  M_yy.M.TwfT V2 ->
  red (trm_tapp (trm_tabs V1 e1) V2) (M_yt.M.Tbsubst e1 0 V2).

(** Our goal is to prove preservation and progress *)

Definition preservation := forall E F e e' T,
  typing E F e T -> 
  red e e' -> 
    typing E F e' T.

Definition progress := forall e T,
  typing empty_env empty_env e T -> 
  value e \/ exists e', red e e'.

