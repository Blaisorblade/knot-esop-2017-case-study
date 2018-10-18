Set Implicit Arguments.

Require Export DGP_Core.
Require Export Variable_Sets.

(** Reference: #<a href="http://alliance.seas.upenn.edu/~plclub/cgi-bin/poplmark/index.php?title=Submission_by_J%C3%A9r%C3%B4me_Vouillon">#J. Vouillon's POPLmark solutions#</a># *)


(**********************************************************************)
(** * Importing Dgp for de Bruijn indices approach *)
(**********************************************************************)

(** [Single] is a unit type and denotes the empty place holder
   for binding variables which are not written directly
   in de Bruijn style representation for abstraction. *)

Module Export deBruijn := Dgp Nat Single.


(**********************************************************************)
(** * Herogeneous Variable Shifting *)
(**********************************************************************)

(** The following definition deals with heterogeneous variable shifting;
   - [r0] is the representation of the variables for which shifting is performed.
   
   - [Var] case: only the case [r = r0] is interesting.

   - [Bind] case: shifting happens only when the representation
   of bound variable has the representation [r0].
   Note that, when [r1 = REC], [r0] is compared with [r]
   because [REC] denotes the representation of the abstraction body [r]. *)

Fixpoint shiftRep (m:nat) r r0 s (T:InterpretRep r s) {struct T} : InterpretRep r s :=
  match T in InterpretRep _ s return InterpretRep r s with
    | Unit          => Unit
    | Const _ U     => Const r U
    | Repr _ U      => Repr r (shift m r0 U)
    | InL _ _ U     => InL _ (shiftRep m r0 U) 
    | InR _ _ V     => InR _ (shiftRep m r0 V)
    | Pair _ _ U V  => Pair (shiftRep m r0 U) (shiftRep m r0 V)
    | Bind r1 _ _ U =>
      match r1 with
        | REC => match Rep_dec r r0 with
                   | left _ => Bind r1 tt (shiftRep (S m) r0 U)
                   | right _ => Bind r1 tt (shiftRep m r0 U)
                 end
        | _ => match Rep_dec r1 r0 with
                 | left _ => Bind r1 tt (shiftRep (S m) r0 U)
                 | right _ => Bind r1 tt (shiftRep m r0 U)
               end
      end
    | Rec U         => Rec (shift m r0 U)
  end

with shift (m:nat) r r0 (T:Interpret r) {struct T}: Interpret r :=
  match T with
    | Var n  => match Rep_dec r r0 with
                  | left _ => Var _ (if le_gt_dec m n then (S n) else n)
                  | right _ => T
                end
    | Term U => Term (shiftRep m r0 U)
  end.


(**********************************************************************)
(** * Heterogeneous Substitution *)
(**********************************************************************)

(** The following definition deals with heterogeneous substitution;
   - [r0] is the representation of the variables to be substituted.
   
   - [Var] case: only the case [r = r0] is interesting.

   - [Bind] case: shifting happens only when the representation
   of bound variable has the representation [r0].
   Note that, when [r1 = REC], [r0] is compared with [r]
   because [REC] denotes the representation of the abstraction body [r]. *)

Fixpoint substRep r r0 s (T:InterpretRep r s)(m:nat)(U:Interpret r0) : InterpretRep r s :=
  match T in InterpretRep _ s return InterpretRep r s with
    | Unit            => Unit 
    | Const _ T0      => Const r T0
    | Repr _ T0       => Repr r (subst T0 m U)
    | InL _ _ T0      => InL _ (substRep T0 m U)
    | InR _ _ T0      => InR _ (substRep T0 m U)
    | Pair _ _ T0 T1  => Pair (substRep T0 m U) (substRep T1 m U)
    | Bind r1 _ _ T0  =>
      match r1 with
        | REC => match Rep_dec r r0 with
                   | left _ => Bind r1 tt (substRep T0 (S m) (shift 0 r0 U))
                   | _      => Bind r1 tt (substRep T0 m U)
                 end
        | _   => match Rep_dec r1 r0 with
                   | left _ => Bind r1 tt (substRep T0 (S m) (shift 0 r0 U))
                   | _      => Bind r1 tt (substRep T0 m (shift 0 r1 U))
                 end
      end
    | Rec T0          => Rec (subst T0 m U)
  end

with subst r r0 (T:Interpret r)(m:nat)(U:Interpret r0) : Interpret r :=
  match T with
    | Var n  => 
      match Rep_dec r r0 with 
        | left same => 
          match lt_eq_lt_dec n m with  
            | inleft (left _)  => Var _ n
            | inleft (right _) => conv same U
            | inright _        => Var _ (n - 1)
          end
        | right _ => T
      end
    | Term T0 => Term (substRep T0 m U)
  end.


(*************************************************************************)
(** Some tactics for case distinction *)
(*************************************************************************)

Ltac do_cases :=
  unfold shift, shiftRep;
  unfold subst, substRep;
  fold shift; fold shiftRep;
  fold subst; fold substRep;
  match goal with
    | |- context [le_gt_dec ?n ?n'] =>
      case (le_gt_dec n n')
    | |- context C [(lt_eq_lt_dec ?n ?n')] =>
      case (lt_eq_lt_dec n n'); [intro s; case s; clear s | idtac ]
    | |- context [Rep_dec ?r ?s] => destruct (Rep_dec r s); [idtac | try id_false]
  end;
  intros; try absurd_math; try congruence.

Ltac rep_destruct :=
  match goal with
    | |- context [ match ?r with 
                     | UNIT => _
                     | CONST _ => _
                     | REPR _ => _
                     | PLUS _ _ => _
                     | PROD _ _ => _ 
                     | BIND _ _ => _ 
                     | REC => _ 
                   end ]
    => destruct r; repeat (case_rep; [idtac |try id_false]);
      intros; try absurd_math; try discriminate;
      match goal with
        | q : QQ |- _ => destruct q
      end
  end;
  simpl; repeat case_rep; try absurd_math.

Tactic Notation "change_maths" constr(T) "with" constr(U) :=
  replace T with U; [ idtac | omega ].


(*************************************************************************)
(** * Homogenerous shifting and substitution *)
(*************************************************************************)

(** Commutation properties of homogeneous shifting and substitution
   - Remember that [noRepr] denotes that there are no [REPR] case. *)

Lemma noRepr_subst_shiftRep : forall r s (T : InterpretRep r s) (T' : Interpret r)(n : nat),
  noRepr r ->
  noRepr s ->
  T = substRep (shiftRep n r T) n T'

  with noRepr_subst_shift : forall r (T : Interpret r) (T' : Interpret r)(n : nat),
    noRepr r ->
    T = subst (shift n r T) n T'.
Proof.
  induction T; simpl; introv Hr Hs;
  [ reflexivity
    | reflexivity
    | absurd_math
    | inversion Hs; f_equal; apply noRepr_subst_shiftRep; assumption
    | inversion Hs; f_equal; apply noRepr_subst_shiftRep; assumption
    | inversion Hs; f_equal; apply noRepr_subst_shiftRep; assumption
    | rep_destruct; f_equal; apply noRepr_subst_shiftRep; assumption
    | f_equal; apply noRepr_subst_shift; assumption ]. 

  induction T as [ v |]; simpl; introv Hr;
    [ repeat do_cases; f_equal; auto 1 with arith
      |f_equal; apply noRepr_subst_shiftRep; assumption ].
Qed.

Hint Resolve noRepr_subst_shift noRepr_subst_shiftRep.

Local Open Scope nat_scope.

Lemma noRepr_shift_shiftRep : forall r s (T : InterpretRep r s)(n n' : nat),
  noRepr r ->
  noRepr s ->
  shiftRep n r (shiftRep (n + n') r T) = shiftRep (S (n + n')) r (shiftRep n r T)

  with noRepr_shift_shift : forall r (T : Interpret r)(n n' : nat),
    noRepr r ->
    shift n r (shift (n + n') r T) = shift (S (n + n')) r (shift n r T).
Proof.
  induction T; simpl; introv Hr Hs;
    [ reflexivity
      | reflexivity
      | inversion Hs
      | inversion Hs; func_equal; apply noRepr_shift_shiftRep; assumption
      | inversion Hs; func_equal; apply noRepr_shift_shiftRep; assumption
      | inversion Hs; func_equal; apply noRepr_shift_shiftRep; assumption
      | rep_destruct; func_equal; apply noRepr_shift_shiftRep with (n:=S n); assumption
      | func_equal; apply noRepr_shift_shift; assumption ].

  induction T as [ v |]; simpl; introv Hr;
    [repeat do_cases
      | f_equal; apply noRepr_shift_shiftRep; assumption ].
Qed.

Lemma noRepr_shift_substRep_1 : forall r s (T : InterpretRep r s) (T' : Interpret r)(n n' : nat),
  noRepr r ->
  noRepr s ->
  shiftRep n r (substRep T (n + n') T') =
  substRep (shiftRep n r T) (S (n + n')) (shift n r T')

  with noRepr_shift_subst_1 : forall r (T T' : Interpret r)(n n' : nat),
    noRepr r ->
    shift n r (subst T (n + n') T') =
    subst (shift n r T) (S (n + n')) (shift n r T').
Proof.
  induction T; simpl; introv Hr Hs;
    [ reflexivity
      | reflexivity
      | inversion Hs
      | inversion Hs; func_equal; apply noRepr_shift_substRep_1; assumption
      | inversion Hs; func_equal; apply noRepr_shift_substRep_1; assumption
      | inversion Hs; func_equal; apply noRepr_shift_substRep_1; assumption
      | rep_destruct; func_equal
      | func_equal; apply noRepr_shift_subst_1; assumption ].

  change_maths (S (n + n')) with (S n + n').
  change_maths n with (0 + n).
  rewrite noRepr_shift_shift; auto.

  induction T as [ v |]; simpl; introv Hr;
    [ repeat do_cases; func_equal; auto with arith ; repeat rewrite conv_id; auto
      | func_equal; apply noRepr_shift_substRep_1; assumption ].

  destruct v; simpl; [ absurd_math | auto with arith ].
Qed.

Lemma noRepr_shift_substRep_2 : forall r s (T : InterpretRep r s) (T' : Interpret r) (n n' : nat),
  noRepr r ->
  noRepr s ->
  (shiftRep (n + n') r (substRep T n T')) =
  (substRep (shiftRep (S (n + n')) r T) n (shift (n + n') r T'))

  with noRepr_shift_subst_2 : forall r (T T' : Interpret r) (n n' : nat),
    noRepr r ->
    (shift (n + n') r (subst T n T')) =
    (subst (shift (S (n + n')) r T) n (shift (n + n') r T')).
Proof.
  induction T; simpl; introv Hr Hs;
    [ reflexivity
      | reflexivity
      | inversion Hs
      | inversion Hs; func_equal; apply noRepr_shift_substRep_2; assumption
      | inversion Hs; func_equal; apply noRepr_shift_substRep_2; assumption
      | inversion Hs; func_equal; apply noRepr_shift_substRep_2; assumption
      | rep_destruct; func_equal
      | func_equal; apply noRepr_shift_subst_2; assumption ].

  change_maths (S (n + n')) with (S n + n').
  rewrite noRepr_shift_substRep_2; try assumption.
  change_maths (n + n') with (0 + (n + n')).
  rewrite noRepr_shift_shift; auto.

  induction T as [ v |]; introv Hr;
    [ repeat do_cases; func_equal; auto with arith; repeat rewrite conv_id; auto
      | simpl; func_equal; apply noRepr_shift_substRep_2; assumption ].  

  destruct v; simpl; [ absurd_math | auto with arith ].
Qed.

Lemma noRepr_subst_substRep : forall r s (T : InterpretRep r s) (U V: Interpret r) (n n' : nat),
  noRepr r ->
  noRepr s ->
  (substRep (substRep T n U) (n + n') V) =
  (substRep (substRep T (S (n + n')) (shift n r V)) n (subst U (n + n') V))

  with noRepr_subst_subst : forall r (T U V : Interpret r) (n n' : nat),
    noRepr r ->
    (subst (subst T n U) (n + n') V) =
    (subst (subst T (S (n + n')) (shift n r V)) n (subst U (n + n') V)).
Proof.
  induction T; simpl; introv Hr Hs;
    [ reflexivity
      | reflexivity
      | inversion Hs
      | inversion Hs; func_equal; apply noRepr_subst_substRep; assumption
      | inversion Hs; func_equal; apply noRepr_subst_substRep; assumption
      | inversion Hs; func_equal; apply noRepr_subst_substRep; assumption
      | rep_destruct; func_equal
      | func_equal; apply noRepr_subst_subst; assumption ].

  change_maths (n + n') with (0 + (n + n')).
  rewrite noRepr_shift_subst_1; simpl; try assumption.
  change_maths (n ) with (0 + n).
  rewrite noRepr_shift_shift; simpl; try assumption.
  change_maths (S (n + n')) with (S n + n').
  rewrite noRepr_subst_substRep;simpl; try assumption; reflexivity.

  induction T as [ v |]; simpl; introv Hr;
    [ repeat do_cases; func_equal; auto with arith; repeat rewrite conv_id; auto 2
      | func_equal; apply noRepr_subst_substRep; assumption ].
Qed.

Lemma noRepr_shift_preserves_sizeRep : forall r s (T : InterpretRep r s) (n : nat), 
  noRepr r ->
  noRepr s ->
  sizeRep (shiftRep n r T) = sizeRep T

  with noRepr_shift_preserves_size : forall r (T : Interpret r) (n : nat),
    noRepr r ->
    size (shift n r T) = size T.
Proof.
  induction T; simpl; introv Hr Hs;
    [ reflexivity
      | reflexivity
      | inversion Hs
      | inversion Hs; apply noRepr_shift_preserves_sizeRep; assumption
      | inversion Hs; apply noRepr_shift_preserves_sizeRep; assumption
      | inversion Hs; func_equal; auto with arith
      | rep_destruct; func_equal; apply noRepr_shift_preserves_sizeRep; assumption
      | apply noRepr_shift_preserves_size; assumption].

  induction T as [ v |]; simpl; introv Hr;
    [ repeat do_cases; auto with arith; repeat rewrite conv_id
      | apply noRepr_shift_preserves_sizeRep; assumption ]. 
Qed.

Lemma noRepr_shiftRep_hetero : forall r r' s (T: InterpretRep r s) (n: nat),
  noRepr r ->
  noRepr s ->
  r <> r' ->
  T = shiftRep n r' T

  with noRepr_shift_hetero : forall r r' (T: Interpret r) (n: nat),
    noRepr r ->
    r <> r' ->
    T = shift n r' T.
Proof.
  induction T; simpl; introv Hr Hs Hneq;
    [ reflexivity
      | reflexivity
      | inversion Hs
      | inversion Hs; func_equal; apply noRepr_shiftRep_hetero; assumption
      | inversion Hs; func_equal; apply noRepr_shiftRep_hetero; assumption
      | inversion Hs; func_equal; apply noRepr_shiftRep_hetero; assumption
      | rep_destruct; func_equal; apply noRepr_shiftRep_hetero; assumption
      | func_equal; apply noRepr_shift_hetero; assumption ].

  induction T as [ v |]; simpl; introv Hr Hneq;
    [ repeat do_cases; auto with arith; repeat rewrite conv_id
      | func_equal; apply noRepr_shiftRep_hetero; assumption ].
Qed.

Lemma noRepr_substRep_hetero : forall r r' s (T: InterpretRep r s) (U: Interpret r') (n: nat),
  noRepr r ->
  noRepr s ->
  r <> r' ->
  T = substRep T n U

  with noRepr_subst_hetero : forall r r' (T: Interpret r) (U: Interpret r') (n: nat),
    noRepr r ->
    r <> r' ->
    T = subst T n U.
Proof.
  induction T; simpl; introv Hr Hs Hneq;
    [ reflexivity
      | reflexivity
      | inversion Hs
      | inversion Hs; func_equal; apply noRepr_substRep_hetero; assumption
      | inversion Hs; func_equal; apply noRepr_substRep_hetero; assumption
      | inversion Hs; func_equal; apply noRepr_substRep_hetero; assumption
      | rep_destruct; func_equal; apply noRepr_substRep_hetero; assumption
      | func_equal; apply noRepr_subst_hetero; assumption ].

  induction T as [ v |]; simpl; introv Hr Hneq;
    [ repeat do_cases; auto with arith; repeat rewrite conv_id
      | func_equal; apply noRepr_substRep_hetero; assumption ]. 
Qed.
