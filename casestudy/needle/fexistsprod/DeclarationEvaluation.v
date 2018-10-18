Require Export Coq.Unicode.Utf8.
Require Export FExistsProd.

(*************************************************************************)
(* Reduction relation                                                    *)
(*************************************************************************)

Fixpoint Value (t : Tm) : Prop :=
  match t with
    | abs _ _    => True
    | tabs _     => True
    | pack _ t _ => Value t
    | prod x y   => Value x ∧ Value y
    | _          => False
  end.

Inductive Match : Pat → Tm → Tm → Tm → Prop :=
  | M_Var {T v t} :
      Match (pvar T) v t (substTm X0 v t)
  | M_Prod {p1 p2 v1 v2 t t' t''} :
      Match p2 (weakenTm v2 (bindPat p1)) t t' →
      Match p1 v1 t' t'' →
      Match (pprod p1 p2) (prod v1 v2) t t''.

Inductive red : Tm → Tm → Prop :=
  | appabs {T11 t12 t2} :
      Value t2 → red (app (abs T11 t12) t2) (substTm X0 t2 t12)
  | tapptabs {T2 t11} :
      red (tapp (tabs t11) T2) (tsubstTm X0 T2 t11)
  | E_UnpackPack {T11 v12 T1 t2} :
      Value v12 →
      red (unpack (pack T11 v12 (texist T1)) t2)
          (tsubstTm X0 T11 (substTm X0 (tshiftTm C0 v12) t2))
  | appfun {t1 t1' t2} :
      red t1 t1' → red (app t1 t2) (app t1' t2)
  | apparg {t1 t2 t2'} :
      Value t1 → red t2 t2' → red (app t1 t2) (app t1 t2')
  | typefun {t1 t1' T2} :
      red t1 t1' → red (tapp t1 T2) (tapp t1' T2)
  | E_pack {T11 t12 t12' T1} :
      red t12 t12' → red (pack T11 t12 T1) (pack T11 t12' T1)
  | E_unpack {t1 t1' t2} :
      red t1 t1' → red (unpack t1 t2) (unpack t1' t2)
  | prodl {t1 t1' t2} :
      red t1 t1' → red (prod t1 t2) (prod t1' t2)
  | prodr {t1 t2 t2'} :
      Value t1 → red t2 t2' → red (prod t1 t2) (prod t1 t2')
  | casep {p t1 t1' t2} :
      red t1 t1' → red (case t1 p t2) (case t1' p t2)
  | casev {p t1 t3 t2} :
      Value t1 → Match p t1 t2 t3 → red (case t1 p t2) t3.
