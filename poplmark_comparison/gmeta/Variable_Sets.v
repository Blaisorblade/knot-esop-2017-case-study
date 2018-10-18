Set Implicit Arguments.

Require Import Arith.
Require Import MetatheoryAtom.
Require Import Metatheory_Var.


(* ************************************************************ *)
(** * Variable sorts *)
(* ************************************************************ *)

(** Using one sort of variables:
   - [Nat] can be used for Nominal and de Bruijn approaches *)

Module Nat <: GenericVarSig := AtomDT.

(** Using two sorts of variables:
   - [TwoNat] can be used for Locally nameless
     and Locally-named approaches *)

Module TwoNat <: GenericVarSig := DisjUnionUsualDecidableType Nat Nat.

(** Quantification variables:
   - For de Bruijn style: Any unit type can be used.
   - Otherwise, [Nat] can be used *)

Module Single <: QuantificationVarSig.

  Definition t := unit.

  Hint Unfold t.
  
  Definition eq_dec : forall a b : t, {a = b} + {a <> b}.
  Proof.
    decide equality.
  Defined.

End Single.

(* Module QNat <: QuantificationVarSig := GVar_to_Quant Nat. *)

