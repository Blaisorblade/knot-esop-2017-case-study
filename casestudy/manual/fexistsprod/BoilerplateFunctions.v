Require Export SpecSyntax.
Set Implicit Arguments.

(******************************************************************************)
(* Shifting                                                                   *)
(******************************************************************************)

Fixpoint tshiftIndex (c : hnat) (i : nat) : nat :=
  match c , i with
    | HO    , _   => S i
    | HSm c , _   => tshiftIndex c i
    | HSy c , O   => O
    | HSy c , S i => S (tshiftIndex c i)
  end.

Fixpoint tshiftTy (c : hnat) (T : Ty) : Ty :=
  match T with
    | tvar X     => tvar (tshiftIndex c X)
    | tarr T1 T2 => tarr (tshiftTy c T1) (tshiftTy c T2)
    | tall T     => tall (tshiftTy (HSy c) T)
    | texist T   => texist (tshiftTy (HSy c) T)
    | tprod T1 T2 => tprod (tshiftTy c T1) (tshiftTy c T2)
  end.

Fixpoint tshiftTm (c : hnat) (t : Tm) : Tm :=
  match t with
  | var x         => var x
  | abs T1 t2     => abs (tshiftTy c T1) (tshiftTm (HSm c) t2)
  | app t1 t2     => app (tshiftTm c t1) (tshiftTm c t2)
  | tabs t2       => tabs (tshiftTm (HSy c) t2)
  | tapp t1 T2    => tapp (tshiftTm c t1) (tshiftTy c T2)
  | pack T1 t T2  => pack (tshiftTy c T1) (tshiftTm c t) (tshiftTy c T2)
  | unpack t1 t2  => unpack (tshiftTm c t1) (tshiftTm (HSm (HSy c)) t2)
  | prod t1 t2    => prod (tshiftTm c t1) (tshiftTm c t2)
  | case t1 p t2  => case (tshiftTm c t1) p (tshiftTm (c + bindPat p) t2)
  end.

Fixpoint shiftIndex (c : hnat) (i : nat) : nat :=
  match c , i  with
    | HO    , _   => S i
    | HSm c , O   => O
    | HSm c , S i => S (shiftIndex c i)
    | HSy c , _   => shiftIndex c i
  end.

Fixpoint shiftTm (c : hnat) (t : Tm) : Tm :=
  match t with
  | var x        => var (shiftIndex c x)
  | abs T1 t2    => abs T1 (shiftTm (HSm c) t2)
  | app t1 t2    => app (shiftTm c t1) (shiftTm c t2)
  | tabs t2      => tabs (shiftTm (HSy c) t2)
  | tapp t1 T2   => tapp (shiftTm c t1) T2
  | pack T1 t T2  => pack T1 (shiftTm c t) T2
  | unpack t1 t2  => unpack (shiftTm c t1) (shiftTm (HSm (HSy c)) t2)
  | prod t1 t2   => prod (shiftTm c t1) (shiftTm c t2)
  | case t1 p t2 => case (shiftTm c t1) p (shiftTm (hplus c (bindPat p)) t2)
  end.

Fixpoint weakenTm (t : Tm) (k : hnat) : Tm :=
  match k with
    | HO    => t
    | HSm k => shiftTm HO (weakenTm t k)
    | HSy k => tshiftTm HO (weakenTm t k)
  end.

Fixpoint weakenTy (T : Ty) (k : hnat) : Ty :=
  match k with
    | HO    => T
    | HSm k => weakenTy T k
    | HSy k => tshiftTy HO (weakenTy T k)
  end.

(******************************************************************************)
(* Type substitution.                                                         *)
(******************************************************************************)

Fixpoint tsubstIndex (X : hnat) (T' : Ty) (Y : nat) : Ty :=
  match X , Y with
    | HO    , O   => T'
    | HO    , S Y => tvar Y
    | HSm X , Y   => tsubstIndex X T' Y
    | HSy X , O   => tvar O
    | HSy X , S Y => tshiftTy HO (tsubstIndex X T' Y)
  end.

Fixpoint tsubstTy (X : hnat) (T' : Ty) (T : Ty) : Ty :=
  match T with
    | tvar Y      => tsubstIndex X T' Y
    | tarr T1 T2  => tarr (tsubstTy X T' T1) (tsubstTy X T' T2)
    | tall T      => tall (tsubstTy (HSy X) T' T)
    | texist T    => texist (tsubstTy (HSy X) T' T)
    | tprod T1 T2 => tprod (tsubstTy X T' T1) (tsubstTy X T' T2)
  end.

Fixpoint tsubstTm (X : hnat) (T' : Ty) (t : Tm) : Tm :=
  match t with
  | var x         => var x
  | abs T1 t2     => abs  (tsubstTy X T' T1) (tsubstTm (HSm X) T' t2)
  | app t1 t2     => app  (tsubstTm X T' t1) (tsubstTm X T' t2)
  | tabs t2       => tabs (tsubstTm (HSy X) T' t2)
  | tapp t1 T2    => tapp (tsubstTm X T' t1) (tsubstTy X T' T2)
  | pack T1 t T2  => pack (tsubstTy X T' T1) (tsubstTm X T' t) (tsubstTy X T' T2)
  | unpack t1 t2  => unpack (tsubstTm X T' t1) (tsubstTm (HSm (HSy X)) T' t2)
  | prod t1 t2    => prod (tsubstTm X T' t1) (tsubstTm X T' t2)
  | case t1 p t2  => case (tsubstTm X T' t1) p
                       (tsubstTm (hplus X (bindPat p)) T' t2)
  end.

(******************************************************************************)
(* Term substitutions.                                                        *)
(******************************************************************************)

Fixpoint substIndex (x : hnat) (t : Tm) (y : nat) : Tm :=
  match x , y with
    | HO    , O   => t
    | HO    , S y => var y
    | HSm x , O   => var O
    | HSm x , S y => shiftTm HO (substIndex x t y)
    | HSy x , y   => tshiftTm HO (substIndex x t y)
  end.

Fixpoint substTm (x : hnat) (t' : Tm) (t : Tm) : Tm :=
  match t with
    | var y        => substIndex x t' y
    | abs T1 t2    => abs T1 (substTm (HSm x) t' t2)
    | app t1 t2    => app (substTm x t' t1) (substTm x t' t2)
    | tabs t2      => tabs (substTm (HSy x) t' t2)
    | tapp t1 T2   => tapp (substTm x t' t1) T2
    | pack T1 t T2 => pack T1 (substTm x t' t) T2
    | unpack t1 t2 => unpack (substTm x t' t1) (substTm (HSm (HSy x)) t' t2)
    | prod t1 t2   => prod (substTm x t' t1) (substTm x t' t2)
    | case t1 p t2 => case (substTm x t' t1) p
                        (substTm (hplus x (bindPat p)) t' t2)
  end.

(******************************************************************************)
(* Context extensions.                                                        *)
(******************************************************************************)

Fixpoint append (Δ1 Δ2 : Env) : Env :=
  match Δ2 with
    | empty     => Δ1
    | evar Δ2 T => evar (append Δ1 Δ2) T
    | etvar Δ2  => etvar (append Δ1 Δ2)
  end.

Fixpoint dom (Δ : Env) : hnat :=
  match Δ with
    | empty    => HO
    | evar Δ _ => HSm (dom Δ)
    | etvar Δ  => HSy (dom Δ)
  end.

Fixpoint tshiftEnv (c : hnat) (Δ : Env) : Env :=
  match Δ with
    | empty     => empty
    | evar Δ T  => evar (tshiftEnv c Δ) (tshiftTy (c + dom Δ) T)
    | etvar Δ   => etvar (tshiftEnv c Δ)
  end.

Fixpoint tsubstEnv (X : hnat) (T' : Ty) (Δ : Env) : Env :=
  match Δ with
    | empty    => empty
    | evar Δ T => evar (tsubstEnv X T' Δ) (tsubstTy (X + dom Δ) T' T)
    | etvar Δ  => etvar (tsubstEnv X T' Δ)
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
      lookup_evar (etvar Γ) X (tshiftTy HO T).
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
