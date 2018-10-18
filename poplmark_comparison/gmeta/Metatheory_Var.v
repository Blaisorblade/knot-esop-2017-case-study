Set Implicit Arguments.

Require Import DecidableTypeEx.

(**************************************************)
(** * Abstract Definition of Variables *)
(**************************************************)

Module Type GenericVarSig := UsualDecidableType.

(** Decidable sets are the basis for variables used for the abstraction
   or quantification *)

Module Type QuantificationVarSig := MiniDecidableType.

Module GVar_to_Quant (M:GenericVarSig) <: QuantificationVarSig := M.

(** Disjoint union of two usually decidable sets is usually decidable.
   This kind of decidable sets will be used when two kinds of variables
   are used for the formalization. *)

Module DisjUnionUsualDecidableType(D1 D2:GenericVarSig) <: GenericVarSig.
  
  Definition t := sum D1.t D2.t.

  Definition eq := @eq t.

  Definition eq_refl := @refl_equal t.

  Definition eq_sym := @sym_eq t.

  Definition eq_trans := @trans_eq t.

  Definition eq_dec : forall x y : t, {x = y}+{x <> y}.
  Proof.
    decide equality; [apply D1.eq_dec | apply D2.eq_dec].
  Qed.

End DisjUnionUsualDecidableType.

