Set Implicit Arguments.

Require Export deBruijn_Meta.

(** Reference: #<a href="http://alliance.seas.upenn.edu/~plclub/cgi-bin/poplmark/index.php?title=Submission_by_J%C3%A9r%C3%B4me_Vouillon">#J. Vouillon's POPLmark solutions#</a># *)


(**********************************************************************)
(** * Environments and well-formedness *)
(**********************************************************************)

(** This part is an extension of [deBruijn_Meta.v]. *)

Local Open Scope type_scope.

(** [Env] provides a generic version of environments for typing system.
   - An environment is a list of the disjoint union of [Interpret r].
   - In systems like System F,
     [inl] is used for type variable binding
     while [inr] is used for term variable binding. *)

Definition Env (A:Type) := list (A + A).

Notation ENV := (fun (r:Rep) => Env (Interpret r)).

(** [opt_map] extends a function to [option] types. *)

Definition opt_map (A B : Type) (f : A -> B) (x : option A) :=
  match x with
    | Some x => Some (f x)
    | None => None
  end.

(** [get_left] accesses the type information for type variables. *)

Fixpoint get_left r (e: ENV r) (X:atom) {struct e} : option (Interpret r) :=
  match e with
    | nil         => None
    | inl T :: e' => opt_map (shift 0 r) (match X with
                                            | O    => Some T
                                            | S X' => get_left e' X'
                                          end)
    | inr T :: e' => get_left e' X
  end.

(** [get_right] accesses the type information for term variables. *)

Fixpoint get_right r (e : ENV r) (x : atom) {struct e} : option (Interpret r) :=
  match e with
  | nil         => None
  | inl _ :: e' => opt_map (shift 0 r) (get_right e' x)
  | inr T :: e' => match x with
                     | O    => Some T
                     | S x' => get_right e' x'
                   end
  end.

(** [opt_map] relates [none] with [none]. *)

Lemma opt_map_none : forall A B (f:A -> B) (x:option A),
  opt_map f x = None -> x = None.
Proof.
  intros A B f x H; destruct x; [simpl in H; discriminate| reflexivity].
Qed.

Lemma opt_map_none_1 : forall A B (f:A -> B) (x:option A),
  x = None -> opt_map f x = None.
Proof.
  firstorder; subst; auto.
Qed.


(**********************************************************************)
(** * Well-formedness in an environment *)
(**********************************************************************)

(** [HO_wf] and [HO_wfRep] denote homogeneous form of well-formedness.
   - Note that environments are represented by natural numbers.
     This is because the type information for variables is not necessary
     to check the well-formedness.
     Furthermore, only the number of occurring free variables are important
     in checking the well-formedness.
   - The condition that all type variables mush be bound is represented
     by the length condition in the [Var] case.
   - Only the well-formedness of terms whose representation contains no [Repr].
     For example, types in System F is the case. *)

Fixpoint HO_wfRep (n:atom) r s (T:InterpretRep r s) {struct T} : Prop :=
  match T with
    | Unit           => True
    | Const _ _      => True
    | Repr _ _       => True
    | InL _ _ i      => HO_wfRep n i
    | InR _ _ i      => HO_wfRep n i
    | Pair _ _ i i0  => HO_wfRep n i /\ HO_wfRep n i0
    | Bind r1 s0 _ i => match r1 with
                          | REC => HO_wfRep (S n) i
                          | _   => True
                        end
    | Rec i          => HO_wf n i
  end

with HO_wf (n:atom) r (T:Interpret r) {struct T} : Prop :=
  match T with
    | Var v  => if le_gt_dec n v then False else True
    | Term i => HO_wfRep n i
  end.

(** The tactic [rep_destruct_wf] eliminate all uninteresting cases
   regarding well-formedness. *)

Ltac rep_destruct_wf :=
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
    => destruct r; try case_rep; simpl; try trivial
  end.

(** [lth] counts [inl] in an environment. *)

Fixpoint lth A (e :Env A) {struct e} : atom :=
  match e with
    | nil        => 0
    | inl _ :: e => S (lth e)
    | inr _ :: e => lth e
  end.      

Notation "[[ e ]]" := (lth e).

(** Well-formed environments
   - An environment is well-formed when all the types in the environment
     is well-typed in the environment. *)

Fixpoint wf_env r (e : ENV r) : Prop :=
  match e with
    | nil        => True
    | inl T :: e => HO_wf [[e]] T /\ wf_env e
    | inr T :: e => HO_wf [[e]] T /\ wf_env e
  end.

(** Weakening for well-formedness *)

Lemma HO_wfRep_weaken : forall r s (T : InterpretRep r s) (n m:atom),
  n <= m ->
  HO_wfRep n T -> HO_wfRep m T

  with HO_wf_weaken : forall r (T : Interpret r) (n m :atom),
    n <= m ->
    HO_wf n T -> HO_wf m T.
Proof.
  destruct T; simpl; introv ? Hwfn; try inversion Hwfn;
    [ exact I
      | exact I
      | exact I
      | apply HO_wfRep_weaken with n; assumption
      | apply HO_wfRep_weaken with n; assumption
      | inversion Hwfn; split; apply HO_wfRep_weaken with n; assumption
      | rep_destruct_wf; apply HO_wfRep_weaken with (S n); auto with arith
      | apply HO_wf_weaken with n; assumption ].

  induction T; simpl; introv ? Hwfn;
    [ repeat destruct (le_gt_dec); intuition (try absurd_math)
      | apply HO_wfRep_weaken with n; assumption].
Qed.

Lemma lth_preserving : forall r (e e' : ENV r),
  (forall (X : nat), get_left e' X = None -> get_left e X = None) ->
  [[e]] <= [[e']].
Proof.
  induction e as [| [a | ] e IHe]; simpl; intros e' Hget;
    [ auto with arith
      | idtac
      | auto with arith ].
  induction e' as [| [b | ] e' IHe']; simpl;
    [ generalize (Hget 0 (refl_equal None)); simpl; intros; discriminate
      | apply le_n_S; apply IHe; intros;
        apply opt_map_none with (f:= shift 0 r);
          apply (Hget (S X)); simpl; auto using opt_map_none_1
      | apply IHe'; exact Hget ].
Qed.

Hint Resolve lth_preserving.

Lemma HO_wfRep_weaken_lth : forall r s (T : InterpretRep r s) (e e' : ENV r),
  (forall (X : nat), get_left e' X = None -> get_left e X = None) ->
  HO_wfRep [[e]] T ->
  HO_wfRep [[e']] T.
Proof.
  intros; apply HO_wfRep_weaken with (n:= [[e]]); auto.
Qed.

Lemma HO_wf_weaken_lth : forall r (T : Interpret r) (e e' : ENV r),
  (forall (X : nat), get_left e' X = None -> get_left e X = None) ->
  HO_wf [[e]] T ->
  HO_wf [[e']] T.
Proof.
  intros; apply HO_wf_weaken with (n:= [[e]]); auto.
Qed.

Lemma HO_wfRep_extensionality : forall r s (T : InterpretRep r s) (e e' : ENV r),
  (forall (X : nat), get_left e X = get_left e' X) ->
  HO_wfRep [[e]] T ->
  HO_wfRep [[e']] T.
Proof.
  intros r s T e e' H H0; apply HO_wfRep_weaken_lth with e;
    [ intros X H1;rewrite <-H1; apply H
      | assumption ].
Qed.

Lemma HO_wf_extensionality : forall r (T : Interpret r) (e e' : ENV r),
  (forall (X : nat), get_left e X = get_left e' X) ->
  HO_wf [[e]] T ->
  HO_wf [[e']] T.
Proof.
  intros r T e e' H H0; apply HO_wf_weaken_lth with e;
    [ intros X H1;rewrite <-H1; apply H
      | assumption ].
Qed.


(** Removal of [x+1]th term variable binding from environments
   - In System F, this corresponds to the environment operation
     <<
     E, x : T, E'  |-->  E, E'
     >> *)

Fixpoint remove_right r (e : ENV r) (x : nat) {struct e} : ENV r :=
  match e with
    | nil         => nil
    | inl T :: e' => inl T :: remove_right e' x
    | inr T :: e' => match x with
                         | O   => e'
                         | S x => inr T :: remove_right e' x 
                       end
  end.

Lemma get_right_remove_right_lt : forall r (e : ENV r) (x x' : nat),
  x < x' ->
  get_right (remove_right e x') x = get_right e x.
Proof.
  induction e as [| [ | ] e IHe]; simpl; intros x x' H;
    [ reflexivity
      | simpl; rewrite IHe; [ reflexivity | assumption ]
      | destruct x';
        [absurd_math | destruct x; simpl; [reflexivity | apply IHe; omega] ] ].
Qed.

Lemma get_right_remove_right_ge : forall r (e : ENV r) (x x' : nat),
  x >= x' ->
  get_right (remove_right e x') x = get_right e (S x).
Proof.
  induction e as [| [ | ] e IHe]; simpl; intros x x' H;
    [ reflexivity
      | simpl;rewrite IHe; [reflexivity | assumption]
      | destruct x'; [reflexivity | destruct x; simpl;
        [inversion H | apply IHe; omega ] ] ].
Qed.

Lemma get_left_remove_right : forall r (e : ENV r) (X x': nat),
  get_left e X = get_left (remove_right e x') X.
Proof.
  induction e as [| [ | ] e IHe]; simpl; intros X x';
    [ reflexivity
      | destruct X; simpl; [reflexivity | rewrite IHe with (x':=x'); reflexivity ]
      | destruct x'; [ reflexivity | apply IHe ] ].
Qed.

Lemma HO_wfright_remove_right : forall r s (e : ENV r) (x : nat) (T : InterpretRep r s),
  HO_wfRep [[e]] T ->
  HO_wfRep [[remove_right e x]] T.
Proof.
  do 5 intro; apply HO_wfRep_extensionality.
  intro; apply get_left_remove_right.
Qed.

Lemma HO_wf_remove_right : forall r (e : ENV r) (x : nat) (T : Interpret r),
  HO_wf [[e]] T ->
  HO_wf [[remove_right e x]] T.
Proof.
  do 4 intro; apply HO_wf_extensionality.
  intro; apply get_left_remove_right.
Qed.

Lemma HO_wfRep_insert_right : forall r s (e : ENV r) (n : nat) (T : InterpretRep r s),
  HO_wfRep [[remove_right e n]] T ->
  HO_wfRep [[e]] T.
Proof.
  do 5 intro; apply HO_wfRep_extensionality.
  intro; apply sym_eq; apply get_left_remove_right.
Qed.

Lemma HO_wf_insert_right : forall r (e : ENV r) (n : nat) (T : Interpret r),
  HO_wf [[remove_right e n]] T ->
  HO_wf [[e]] T.
Proof.
  do 4 intro; apply HO_wf_extensionality.
  intro; apply sym_eq; apply get_left_remove_right.
Qed.

Lemma wf_env_remove_right : forall r (e : ENV r) (x : nat),
  wf_env e ->
  wf_env (remove_right e x).
Proof.
  induction e as [| [ | ] e IHe]; simpl; intros x H;
    [ exact I
      | inversion H; split;
        [apply HO_wf_remove_right | apply IHe ]; assumption
      | destruct H; destruct x; simpl;
        [ assumption | split;
          [ apply HO_wf_remove_right | apply IHe ]; assumption ] ].
Qed.


(** Insertion of a type variable binding in an environment
   - In System F, this corresponds to the environment operation
   <<
   E, E'  |-->  E, X <: T, E'.
   >>
   Note that all type variable in E has to be shifted. *)

Inductive insert_left  r : nat -> ENV r -> ENV r -> Prop :=
| il_here : forall (T : Interpret r) (e : ENV r),
  HO_wf [[e]] T -> insert_left 0 e ((inl T) :: e)
| il_right : forall (X : nat) (T : Interpret r) (e e' : ENV r),
  insert_left X e e' ->
  insert_left X ((inr T) :: e) ((inr (shift X r T)) :: e')
| il_left : forall (X : nat) (T : Interpret r) (e e' : ENV r),
  insert_left X e e' ->
  insert_left (S X) ((inl T) :: e) ((inl (shift X r T)) :: e').

Fixpoint insert (n: nat) (r: Rep) (e: ENV r) (T:Interpret r) (H:HO_wf 0 T) : ENV r :=
  match e with
    | nil           => (inl T) :: e
    | inr U :: e' => (inr (shift n r U)) :: insert n e' T H
    | inl U :: e' => match n with
                         | 0    => inl T :: e
                         | S n' => inl (shift n' r U) :: insert n' e' T H
                       end
  end.

Lemma insert_T_ind : forall r (e:ENV r) (T:Interpret r)(H:HO_wf 0 T),
  insert_left 0 e (insert 0 e T H).
Proof.
  induction e as [| [ | ] e IHe]; simpl; intros;
    [ apply il_here; assumption
      | apply il_here; apply HO_wf_weaken with (n:=0); [ omega | assumption ]
      | apply il_right; apply IHe ].
Qed.

Lemma insert_T : forall r (e:ENV r) (n:nat) (T:Interpret r)(H:HO_wf 0 T),
  [[e]] > 0 ->
  [[e]] >= n ->
  insert_left n e (insert n e T H).
Proof.
  induction e as [| [ | ] e IHe]; simpl; induction n as [| n]; intros;
    [ absurd_math
      | absurd_math
      | apply il_here; apply HO_wf_weaken with (n:=0); [omega | assumption]
      | apply il_left; destruct n;
        [ apply insert_T_ind | apply IHe; omega ]
      | apply il_right; apply IHe; assumption
      | apply il_right; apply IHe; assumption ].
Qed.

Lemma get_left_insert_left_ge : forall r (X X' : nat) (e e' : ENV r),
  noRepr r->
  insert_left X' e e' -> 
  X' <= X ->
  get_left e' (S X) = opt_map (shift X' r) (get_left e X).
Proof.
  intros r n n' e e' H0 H; generalize n; clear n; induction H; simpl; trivial.
  intros n' H1; induction n'; simpl;
    [ inversion H1
      | clear IHn'; rewrite IHinsert_left; try omega; case (get_left e n'); simpl;
        [ intro T''; apply f_equal; apply (noRepr_shift_shift T'' 0 X); assumption
          | reflexivity ] ].
Qed.

Lemma get_left_insert_left_lt : forall r (X X' : nat) (e e' : ENV r),
  noRepr r ->
  insert_left X' e e' ->
  X < X' ->
  get_left e' X = opt_map (shift X' r) (get_left e X).
Proof.
  intros r n n' e e' H0 H; generalize n; clear n; induction H; simpl; trivial;
    [ intros n H1; inversion H1
      | intros n' H1; induction n';
        [ simpl; apply f_equal; apply (noRepr_shift_shift T 0 X); assumption
          | clear IHn'; rewrite IHinsert_left; try omega;
            case (get_left e n'); simpl; trivial; intro T''; f_equal;
              apply (noRepr_shift_shift T'' 0 X); assumption ] ].
Qed.

Lemma get_right_insert_left : forall r (x X' : nat) (e e' : ENV r),
  noRepr r ->
  insert_left X' e e' ->
  get_right e' x = opt_map (shift X' r) (get_right e x).
Proof.
  intros r n n' e e' H0 H; generalize n; clear n; induction H; simpl; intro n';
    [ reflexivity
      | induction n'
      | rewrite IHinsert_left; case (get_right e n'); simpl; trivial;
        intro T'; apply f_equal; apply (noRepr_shift_shift T' 0 X) ];
    auto.
Qed.

Lemma insert_S : forall r (e:ENV r) (n:nat) (U:Interpret r) (H: HO_wf 0 U),
    S [[e]] = [[insert n e U H]].
Proof.
  induction e as [| [ | ] e IHe]; simpl; intros;
    [ reflexivity
      | destruct n; simpl; auto with arith
      | destruct n; simpl; auto with arith ].
Qed.

Hint Resolve insert_S.

Lemma insert_left_lth : forall r X (e e':ENV r),
  insert_left X e e' ->
  [[e']] >= S X.
Proof.
  induction 1; simpl; omega.
Qed.

Lemma insert_left_lth_1 : forall r X (e e':ENV r),
  insert_left X e e' ->
  [[e']] = S [[e]].
Proof.
  induction 1; simpl; auto.
Qed.

Lemma insert_left_HO_wfRep : forall r s (T : InterpretRep r s) (X : nat) (e e' : ENV r) (U:Interpret r),
  HO_wf 0 U ->
  insert_left X e e' ->
  HO_wfRep [[e]] T ->
  HO_wfRep [[e']] (shiftRep X r T)

  with insert_left_HO_wf : forall r (T : Interpret r) (X : nat) (e e' : ENV r) (U:Interpret r),
    HO_wf 0 U ->
    insert_left X e e' ->
    HO_wf [[e]] T ->
    HO_wf [[e']] (shift X r T).
Proof.
  destruct T; simpl; intros X e e' U Hwf0 Hins Hwfe;
    [ exact I
      | exact I
      | exact I
      | apply insert_left_HO_wfRep with e U; assumption
      | apply insert_left_HO_wfRep with e U; assumption
      | inversion Hwfe; split; apply insert_left_HO_wfRep with e U; assumption
      | rep_destruct_wf; [idtac | absurd_math ]
      | apply insert_left_HO_wf with e U; assumption ].
  
  set (e'' := insert (S X) e' U Hwf0).
  assert (S [[e']] = [[e'']]) as Heq;
    [ unfold e''; simpl; auto | idtac ]; rewrite Heq.
  apply insert_left_HO_wfRep with (e:=e') (U:=U); auto;
    [ assert ([[e']] >= S X); [apply insert_left_lth with e; auto | apply insert_T; omega ]
      | rewrite (insert_left_lth_1 Hins); assumption ].

  induction T; simpl; intros;
    [ repeat do_cases; destruct (le_gt_dec); try absurd_math;
      simpl; do_cases; rewrite (insert_left_lth_1 H0) in * |-; absurd_math
      | apply insert_left_HO_wfRep with e U; assumption ].
Qed.

Lemma insert_left_wf_env : forall r (X : nat) (e e' : ENV r) (U: Interpret r),
  HO_wf 0 U ->
  insert_left X e e' ->
  wf_env e ->
  wf_env e'.
Proof.
  intros r n e e' U I H; induction H; simpl; auto;
    intros (H1,H2); split; auto;
      apply insert_left_HO_wf with e U; auto;
        exact (insert_left_HO_wf H H1).
Qed.

Lemma HO_wfRep_weakening_left : forall r s (e : ENV r) (T : InterpretRep r s) (U U' : Interpret r),
  HO_wf 0 U' ->
  HO_wfRep [[e]] T ->
  HO_wf [[e]] U ->
  HO_wfRep [[(inl U) :: e]] (shiftRep 0 r T).
Proof.
  intros r s e T U U' I H1 H2.
  apply insert_left_HO_wfRep with (3 := H1) (U := U');auto.
  apply il_here; trivial.
Qed.

Lemma HO_wf_weakening_left : forall r (e : ENV r) (T U : Interpret r) (U' : Interpret r),
  HO_wf 0 U' ->
  HO_wf [[e]] T ->
  HO_wf [[e]] U ->
  HO_wf [[(inl U) :: e]] (shift 0 r T).
Proof.
  intros r e T U U' I H1 H2.
  apply insert_left_HO_wf with (3 := H1) (U := U');auto.
  apply il_here; trivial.
Qed.

Lemma HO_wfRep_weakening_right : forall r s (e : ENV r) (T : Interpret r) (U : InterpretRep r s),
  HO_wfRep [[e]] U ->
  HO_wfRep [[inr T :: e]] U.
Proof.
  intros r s e T U H; apply HO_wfRep_weaken_lth with (2 := H); simpl; trivial.
Qed.

Lemma HO_wf_weakening_right : forall r (e : ENV r) (T U : Interpret r),
  HO_wf [[e]] U ->
  HO_wf [[inr T :: e]] U.
Proof.
  intros r e T U H; apply HO_wf_weaken_lth with (2 := H); simpl; trivial.
Qed.

Lemma HO_wfRep_strengthening_right : forall r s (e : ENV r) (T : Interpret r) (U : InterpretRep r s),
  HO_wfRep [[ inr T :: e ]] U ->
  HO_wfRep [[ e ]] U.
Proof.
  intros r s e T U H; apply HO_wfRep_weaken_lth with (2 := H); simpl; trivial.
Qed.

Lemma HO_wf_strengthening_right : forall r (e : ENV r) (T U : Interpret r),
  HO_wf [[ inr T :: e ]] U ->
  HO_wf [[ e ]] U.
Proof.
  intros r e T U H; apply HO_wf_weaken_lth with (2 := H); simpl; trivial.
Qed.

Lemma HO_wfRep_left : forall r s (T : InterpretRep r s) (U V : Interpret r) (e : ENV r),
  HO_wfRep [[ inl U :: e ]] T ->
  HO_wfRep [[ inl V :: e ]] T.
Proof.
  intros r s T U V e; apply HO_wfRep_weaken_lth; intro X; induction X;
    [ intros; discriminate | trivial ].
Qed.

Lemma HO_wf_left : forall r (T U V : Interpret r) (e : ENV r),
  HO_wf [[ inl U :: e ]] T ->
  HO_wf [[ inl V :: e ]] T.
Proof.
  intros r T U V e; apply HO_wf_weaken_lth; intro X; induction X;
    [ intros; discriminate | trivial ].
Qed.

Lemma get_right_wf : forall r (e : ENV r) (n : nat) (T : Interpret r) (U : Interpret r),
  HO_wf 0 U ->
  wf_env e ->
  get_right e n = Some T ->
  HO_wf [[e]] T.
Proof.
  induction e as [| [ | ] e IHe]; simpl; intros n T U Hwf Henv Hget.

  discriminate.

  generalize (@IHe n); intro Hwf0.
  induction (get_right e n); [simpl in Hget | discriminate]; inversion Hget.
  apply HO_wf_weakening_left with (U:= a) (U' := U);auto;
    apply Hwf0 with U; auto; inversion Henv; auto.

  destruct n; simpl in Hget; inversion Hget; subst;
    [ inversion Henv; auto
      | apply IHe with n U; auto; inversion Henv; auto].
Qed.

Lemma get_left_gt : forall r (e: ENV r) (X:atom) (U U':Interpret r), 
  noRepr r ->
  HO_wf 0 U' ->
  get_left e X = Some U ->
  [[e]] > X.
Proof.
  induction e as [| a e IHe ]; simpl; intros X U U' Hno Hwf Hget;
    [ discriminate
      | destruct a;destruct X;
        [ omega
          | apply gt_n_S; generalize (IHe X); intro HX;
            destruct (get_left e X);
              [ apply HX with (U:=i0) (U':=U');auto
                | discriminate
              ]
          | apply IHe with (U:=U) (U':=U');auto
          | apply IHe with (U:=U) (U':=U');auto
        ] ].
Qed.
