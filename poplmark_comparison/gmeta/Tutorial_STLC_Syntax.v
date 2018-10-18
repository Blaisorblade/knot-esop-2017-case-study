(** * Step 1 and 2. Defining syntax and isomorphism *)

(** Grammar of pseudo-type  

   Add this annotation to guide the isomorphism generation tool 
   to produce the isomorphism modules for type automatically
<<
(*@Iso Iso_typ*)
>> *)

(*@Iso Iso_typ*)
Inductive typ :=
| typ_var : nat -> typ
| typ_arrow  : typ -> typ -> typ.

(** Grammar of pseudo-term 

Add this annotation to guide the isomorphism generation tool to produce the isomorphism modules for term automatically
<<
(*@Iso Iso_trm {
  Parameter trm_fvar,
  Variable  trm_bvar,
  Binder trm_abs
}*)
>> *)

(*@Iso Iso_trm {
  Parameter trm_fvar,
  Variable  trm_bvar,
  Binder trm_abs
}*)
Inductive trm :=
| trm_fvar : nat -> trm
| trm_bvar : nat -> trm
| trm_abs  : trm -> trm
| trm_app  : trm -> trm -> trm. 


(***********************************************************)
(** ** Isomorphism modules for type and term *)
(***********************************************************)
(** Isomorphism generation tool will produce isomorphism modules for type and term automatically. 

> genIsos Tutorial_STLC_Syntax.v

This command will generate [Iso_typ.v] and [Iso_trm.v] 
which contain isomorphism for type and isomorphism for term respectively.

<<
Module Iso_typ <: Iso_partial.
  ...
End Iso_typ


Module Iso_trm <: Iso_full.
  ...
End Iso_trm
>> *)
