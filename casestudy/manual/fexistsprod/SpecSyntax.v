Require Export Coq.Unicode.Utf8.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

(******************************************************************************)
(* Representation of types.                                                   *)
(******************************************************************************)

Inductive Ty : Set :=
  | tvar (X : nat)
  | tarr (T1 T2 : Ty)
  | tall (T : Ty)
  | texist (T : Ty)
  | tprod (T1 T2 : Ty).

(******************************************************************************)
(* Representation of terms.                                                   *)
(******************************************************************************)

Inductive Pat : Set :=
  | pvar
  | pprod (p1 p2: Pat).

Inductive Tm : Set :=
  | var     (x  : nat)
  | abs     (T  : Ty) (t  : Tm)
  | app     (t1 : Tm) (t2 : Tm)
  | tabs    (t  : Tm)
  | tapp    (t  : Tm) (T  : Ty)
  | pack    (T1 : Ty) (t : Tm) (T2 : Ty)
  | unpack  (t1 : Tm) (t2 : Tm)
  | prod (t1 : Tm) (t2 : Tm)
  | case (s : Tm) (p : Pat) (t : Tm).

Inductive hnat : Set :=
  | HO  : hnat
  | HSm : hnat → hnat
  | HSy : hnat → hnat.

Fixpoint hplus (h1 h2: hnat) : hnat :=
  match h2 with
    | HO      => h1
    | HSm h2' => HSm (hplus h1 h2')
    | HSy h2' => HSy (hplus h1 h2')
  end.

Notation "h1 + h2" := (hplus h1 h2).

(* Calculates the number of cariables bound in a pattern. *)
Fixpoint bindPat (p : Pat) : hnat :=
  match p with
   | pvar        => HSm HO
   | pprod p1 p2 => bindPat p1 + bindPat p2
  end.

(******************************************************************************)
(* Representation of contexts, extensions.                                    *)
(******************************************************************************)

Inductive Env : Set :=
  | empty
  | etvar (Γ : Env)
  | evar  (Γ : Env) (T : Ty).
