Require Export SpecSyntax.
Set Implicit Arguments.

(******************************************************************************)
(* Shifting                                                                   *)
(******************************************************************************)

Fixpoint shiftIndex (c : nat) (i : nat) : nat :=
  match c with
    | O   => S i
    | S c =>
      match i with
        | O   => O
        | S i => S (shiftIndex c i)
      end
  end.

Fixpoint tshiftTy (c : nat) (T : Ty) : Ty :=
  match T with
    | tvar X     => tvar (shiftIndex c X)
    | tarr T1 T2 => tarr (tshiftTy c T1) (tshiftTy c T2)
    | tall T     => tall (tshiftTy (S c) T)
    | texist T   => texist (tshiftTy (S c) T)
  end.

Fixpoint tshiftTm (c : nat) (t : Tm) : Tm :=
  match t with
  | var x         => var x
  | abs T1 t2     => abs (tshiftTy c T1) (tshiftTm c t2)
  | app t1 t2     => app (tshiftTm c t1) (tshiftTm c t2)
  | tabs t2       => tabs (tshiftTm (S c) t2)
  | tapp t1 T2    => tapp (tshiftTm c t1) (tshiftTy c T2)
  | pack T1 t T2  => pack (tshiftTy c T1) (tshiftTm c t) (tshiftTy c T2)
  | unpack t1 t2  => unpack (tshiftTm c t1) (tshiftTm (S c) t2)
  end.

Fixpoint shiftTm (c : nat) (t : Tm) : Tm :=
  match t with
  | var x        => var (shiftIndex c x)
  | abs T1 t2    => abs T1 (shiftTm (S c) t2)
  | app t1 t2    => app (shiftTm c t1) (shiftTm c t2)
  | tabs t2      => tabs (shiftTm c t2)
  | tapp t1 T2   => tapp (shiftTm c t1) T2
  | pack T1 t T2  => pack T1 (shiftTm c t) T2
  | unpack t1 t2  => unpack (shiftTm c t1) (shiftTm (S c) t2)
  end.

(******************************************************************************)
(* Type substitution.                                                         *)
(******************************************************************************)

Fixpoint tsubstIndex (X : nat) (T' : Ty) (Y : nat) : Ty :=
  match X , Y with
    | O   , O   => T'
    | O   , S Y => tvar Y
    | S X , O   => tvar O
    | S X , S Y => tshiftTy 0 (tsubstIndex X T' Y)
  end.

Fixpoint tsubstTy (X : nat) (T' : Ty) (T : Ty) : Ty :=
  match T with
    | tvar Y     => tsubstIndex X T' Y
    | tarr T1 T2 => tarr (tsubstTy X T' T1) (tsubstTy X T' T2)
    | tall T     => tall (tsubstTy (S X) T' T)
    | texist T   => texist (tsubstTy (S X) T' T)
  end.

Fixpoint tsubstTm (X : nat) (T' : Ty) (t : Tm) : Tm :=
  match t with
  | var x         => var x
  | abs T1 t2     => abs  (tsubstTy X T' T1) (tsubstTm X T' t2)
  | app t1 t2     => app  (tsubstTm X T' t1) (tsubstTm X T' t2)
  | tabs t2       => tabs (tsubstTm (S X) T' t2)
  | tapp t1 T2    => tapp (tsubstTm X T' t1) (tsubstTy X T' T2)
  | pack T1 t T2  => pack (tsubstTy X T' T1) (tsubstTm X T' t) (tsubstTy X T' T2)
  | unpack t1 t2  => unpack (tsubstTm X T' t1) (tsubstTm (S X) T' t2)
  end.

(******************************************************************************)
(* Term substitutions.                                                        *)
(******************************************************************************)

Inductive hnat : Set :=
  | hn0 : hnat
  | hsm : hnat → hnat
  | hsy : hnat → hnat.

Fixpoint substIndex (x : hnat) (t : Tm) (y : nat) : Tm :=
  match x , y with
    | hn0   , O   => t
    | hn0   , S y => var y
    | hsm x , O   => var O
    | hsm x , S y => shiftTm O (substIndex x t y)
    | hsy x , y   => tshiftTm O (substIndex x t y)
  end.

Fixpoint substTm (x : hnat) (t' : Tm) (t : Tm) : Tm :=
  match t with
    | var y        => substIndex x t' y
    | abs T1 t2    => abs T1 (substTm (hsm x) t' t2)
    | app t1 t2    => app (substTm x t' t1) (substTm x t' t2)
    | tabs t2      => tabs (substTm (hsy x) t' t2)
    | tapp t1 T2   => tapp (substTm x t' t1) T2
    | pack T1 t T2 => pack T1 (substTm x t' t) T2
    | unpack t1 t2 => unpack (substTm x t' t1) (substTm (hsm (hsy x)) t' t2)
  end.

(******************************************************************************)
(* Context lookups.                                                           *)
(******************************************************************************)

Inductive lookup_etvar : Env → nat → Prop :=
  | lookup_etvar_here {Γ} :
      lookup_etvar (etvar Γ) O
  | lookup_etvar_there_evar {Γ T X} :
      lookup_etvar Γ X →
      lookup_etvar (evar Γ T) X
  | lookup_etvar_there_etvar {Γ X} :
      lookup_etvar Γ X →
      lookup_etvar (etvar Γ) (S X).
Hint Constructors lookup_etvar.

Inductive lookup_evar : Env → nat → Ty → Prop :=
  | lookup_evar_here {Γ T} :
      lookup_evar (evar Γ T) O T
  | lookup_evar_there_evar {Γ T T' X} :
      lookup_evar Γ X T →
      lookup_evar (evar Γ T') (S X) T
  | lookup_evar_there_etvar {Γ T X} :
      lookup_evar Γ X T →
      lookup_evar (etvar Γ) X (tshiftTy 0 T).
Hint Constructors lookup_evar.

(******************************************************************************)
(* Well-formed types.                                                         *)
(******************************************************************************)

Inductive wfTy : Env → Ty → Prop :=
  | wf_tvar {Γ X} :
      lookup_etvar Γ X → wfTy Γ (tvar X)
  | wf_tarr {Γ T1 T2} :
      wfTy Γ T1 → wfTy Γ T2 → wfTy Γ (tarr T1 T2)
  | wf_tall {Γ T} :
      wfTy (etvar Γ) T → wfTy Γ (tall T)
  | wf_texist {Γ T} :
      wfTy (etvar Γ) T → wfTy Γ (texist T).
Hint Constructors wfTy.
