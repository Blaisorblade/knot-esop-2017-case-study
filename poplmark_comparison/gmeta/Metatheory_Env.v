(* This contains an implementation of Environments based on
   natural numbers and Coq.List referring to AssocList.v *)


(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir
     Arthur Charg\'eraud *)

(* This file is modified and extended by Gyesik Lee *)

Require Export Coq.Arith.Arith.
Require Export Coq.FSets.FSets.
Require Export Coq.Lists.List.

Require Export AssocList.
Require Export CoqEqDec.
Require Export CoqListFacts.
Require Export LibTactics.
Require Export MetatheoryAtom.


(* ********************************************************************** *)
(** * Decidable equality *)

(*
(** We prefer that "==" refer to decidable equality at [eq], as
    defined by the [EqDec_eq] class from the CoqEqDec library. *)

Notation " x  == y " := (eq_dec x y) (at level 67) : coqeqdec_scope.

Open Scope coqeqdec_scope.
*)

(* ********************************************************************** *)
(** * Notations for finite sets of atoms *)

(** Common set operations and constants may be written using more
    convenient notations. *)

Notation "E [=] F" :=
  (AtomSetImpl.Equal E F)
  (at level 70, no associativity)
  : set_scope.

Notation "E [<=] F" :=
  (AtomSetImpl.Subset E F)
  (at level 70, no associativity)
  : set_scope.

Notation "{}" :=
  (AtomSetImpl.empty)
  : set_scope.

Notation "{{  x  }}" :=
  (AtomSetImpl.singleton x)
  : set_scope.

Notation "x `in` E" :=
  (AtomSetImpl.In x E)
  (at level 70)
  : set_hs_scope.

Notation "x `notin` E" :=
  (~ AtomSetImpl.In x E)
  (at level 70)
  : set_hs_scope.

Notation "E `union` F" :=
  (AtomSetImpl.union E F)
  (at level 65, right associativity, format "E  `union`  '/' F")
  : set_hs_scope.

(** We define some abbreviations for the empty set, singleton
    sets, and the union of two sets. *)

Notation add := AtomSetImpl.add.
Notation empty := AtomSetImpl.empty.
Notation remove := AtomSetImpl.remove.
Notation singleton := AtomSetImpl.singleton.
Notation union := AtomSetImpl.union.

(** Open the notation scopes declared above. *)

Open Scope set_scope.
Open Scope set_hs_scope.


(* ********************************************************************** *)
(** * Environments *)

(** We can use our implementation of association lists (in AssocList)
    to implement association lists whose keys are atoms.  Thanks to
    parameter inlining, the types in the instantiated functor will all
    use [atom] for the type for keys. *)

Module Export EnvImpl := AssocList.Make AtomDT AtomSetImpl.

Export AtomSetImpl.

Lemma In_atoms_dec : forall (x:atom) (s:atoms), x `in` s  \/ ~ x `in` s.
Proof.
  intros.
  destruct (Sumbool.sumbool_of_bool (mem x s)).
  left; auto using mem_2.
  right; intro; cut (mem x s = true); auto using mem_1; congruence.
Qed.


(** We provide alternative names for the tactics on association lists
    to reflect our use of association lists for environments. *)

Ltac simpl_env :=
  simpl_alist.

Tactic Notation "simpl_env" "in" hyp(H) :=
  simpl_alist in H.

Tactic Notation "simpl_env" "in" "*" :=
  simpl_alist in *.

Tactic Notation "rewrite_env" constr(E) :=
  rewrite_alist E.

Tactic Notation "rewrite_env" constr(E) "in" hyp(H) :=
  rewrite_alist E in H.

Tactic Notation "env" "induction" ident(E) :=
  alist induction E.

Tactic Notation "env" "induction" ident(E) "as" simple_intropattern(P) :=
  alist induction E as P.


(* **************************************************************** *)
(** powerful tactics for automation.  *)

Ltac func_equal := match goal with
  | [ |- (?F _ = ?F _ ) ] => apply (f_equal F)
  | [ |- (?F _ _ = ?F _ _) ] => apply (f_equal2 F)
  | [ |- (?F _ _ _ = ?F _ _ _) ] => apply (f_equal3 F)
  | [ |- (?F _ _ _ _ = ?F _ _ _ _) ] => apply (f_equal4 F)
  | _ => idtac
  end.

Tactic Notation "func_equal" "*" := 
  func_equal; auto*.

(** Useful tactics in dealing with decidability. *)
Notation "a == j" := (KeySetFacts.eq_dec a j) (at level 67).
  
Ltac case_var :=
  let destr X Y := destruct (X == Y); [try subst X | idtac] in
  match goal with
  | |- context [?X == ?Y]      => destr X Y  
  | H: context [?X == ?Y] |- _ => destr X Y 
  end.

Tactic Notation "case_var" "*" := case_var; auto*.

Ltac id_false :=
  match goal with
    | H : ?x <> ?x |- _ => elim H; reflexivity
  end.

Ltac absurd_math := first [intros; assert False; [omega | contradiction] | id_false ].

(* Ltac absurd_math := intros; assert False; [omega | contradiction]. *)

Ltac contra H := let Heq := fresh in try red; intro Heq; elim H.

(** As an alternative to the [x ~ a] notation, we also provide more
    list-like notation for writing association lists consisting of a
    single binding.

    Implementation note: The following notation overlaps with the
    standard recursive notation for lists, e.g., the one found in the
    Program library of Coq's standard library. *)

(** [#] stands for the freshness of a variable w.r.t an environment. *)

Notation "x '#' E" := (x `notin`(dom E)) (at level 60).

Notation "[ x ]" := (EnvImpl.one x).

(** We use names specific to environments based on [EnvImpl]. *)

Section Env_Definitions.

  Variable A : Type.

  Definition env := (list (atom * A)).

  Definition empty_env := (@nil (atom * A)).

  Lemma dom_empty_env : dom empty_env = {}.
  Proof.
    reflexivity.
  Qed.

  (** * Extension of Environments *)

  Definition extends (E F:env) := forall (X:atom) (U:A), binds X U E -> binds X U F.

  Hint Unfold extends.

  Lemma extends_app_L : forall (E E0 E1:env),
    extends E0 E1 -> extends (E ++ E0) (E ++ E1).
  Proof.
    intros E E0 E1 H x a Hbinds.
    elim binds_app_1 with (E:=E)(F:=E0)(x:=x)(a:=a); auto.
  Qed.

  Lemma extends_app_R : forall (E E0 E1:env),
    extends E0 E1 -> extends (E0 ++ E) (E1 ++ E).
  Proof.
    intros E E0 E1 H x a Hbinds.
    elim binds_app_1 with (E:=E0)(F:=E)(x:=x)(a:=a); auto.
  Qed.

  Lemma extends_L : forall (E E0:env),
    extends E (E0 ++ E).
  Proof.
    intros E E0 x a Hbinds; apply binds_app_3; assumption.
  Qed.

  Lemma extends_R : forall (E E0:env),
    extends E (E ++ E0).
  Proof.
    intros E E0 x a Hbinds; apply binds_app_2; assumption.
  Qed.

  Lemma extends_push : forall E F (X:atom) T, 
    extends E F -> extends (X ~ T ++ E) (X ~ T ++ F).
  Proof.
    unfold extends. intros. inversion H0; auto.
    inversion H1; intros; subst X0 T; auto.
  Qed.

  Lemma extends_swap : forall E F,
    extends (E ++ F) (F ++ E).
  Proof.
    intros E F x a Hbinds.
    elim binds_app_1 with (x:=x)(a:=a)(E:=E)(F:=F); auto.
  Qed.


End Env_Definitions.

(** Making [A] implicit for [empty_env] and [extends]. *)

Implicit Arguments empty_env [A].

Implicit Arguments extends [A].

Section Mapping_Env.

  Variable A B : Type.
  Variable f : A -> B.

  Lemma dom_map_1 : forall (E:env A),
    dom E [<=] dom (map f E).
  Proof.
    intros E a H.
    generalize dom_map; intro H0.
    assert (a `in` dom (map f E) <-> a `in` dom E).
    apply H0.
    inversion H1; auto.
  Qed.

  Lemma dom_map_2 : forall (E:env A),
    dom (map f E) [<=] dom E.
  Proof.
    intros E a H.
    generalize dom_map; intro H0.
    assert (a `in` dom (map f E) <-> a `in` dom E).
    apply H0.
    inversion H1; auto.
  Qed.

  Lemma dom_map_3 : forall (E:env A)(a:atom),
    a # E -> a # map f E.
  Proof.
    intros E a H; contra H; apply dom_map_2; auto.
  Qed.

  Lemma dom_map_4 : forall (E:env A)(a:atom),
    a # map f E -> a # E.
  Proof.
    intros E a H; contra H; apply dom_map_1; auto.
  Qed.

  Lemma map_extends_1 : forall (E F: env A),
    extends E F -> extends (map f E) (map f F).
  Proof.
    unfold extends; intros. 
    induction E as [|(a,T)]; inversion H0.
    inversion H1; subst.
    apply binds_map_2; auto using H.
    apply IHE; auto.
  Qed.

  Lemma map_extends_2 : forall (E F: env A),
    (forall x y : A, f x = f y -> x = y) ->
    extends (map f E) (map f F) -> extends E F.
  Proof.
    unfold extends; intros E F Hinj H X U H0. 
    induction E as [|(a,T)]; inversion H0.
    inversion H1; subst.
    apply binds_map_1 with (B:= B)(f:= f); auto using Hinj.
    apply IHE; auto.
    intros; apply H.
    unfold binds; simpl; tauto.
  Qed.

  Lemma map_uniq_1 : forall (E:env A),
    uniq E -> uniq (map f E).
  Proof.
    induction E as [|(a,T)]; simpl; intro H; simpl_alist; constructor.
    apply IHE; eauto using uniq_cons_1.
    apply dom_map_3; eauto using uniq_cons_2.
  Qed.
  
  Lemma map_uniq_2 : forall (E:env A),
    uniq (map f E) -> uniq E.
  Proof.
    induction E as [|(a,T)]; simpl; intro H; simpl_alist; constructor.
    apply IHE; eauto using uniq_cons_1.
    apply dom_map_4; eauto using uniq_cons_2.
  Qed.

  Lemma map_uniq_3 : forall (E F:env A)(a:nat)(T:A),
    uniq (E ++ a ~ T ++ F) -> uniq (map f E ++ a ~ f T ++ map f F).
  Proof.
    intros.
    cut (uniq (map f (E ++ a ~ T ++ F))); simpl; auto.
    rewrite map_app; simpl; tauto.
  Qed.
  
  Lemma map_uniq_4 : forall (E F:env A)(a:nat)(T:A),
    uniq (map f E ++ a ~ f T ++ map f F) -> uniq (E ++ a ~ T ++ F).
  Proof.
    intros.
    cut (uniq (map f (E ++ a ~ T ++ F))); simpl; auto using map_uniq_2;
      rewrite map_app; simpl; auto.
  Qed.

  Variable g : A -> A.

  Lemma map_uniq_5 : forall (E F:env A)(a:nat)(T:A),
    uniq (E ++ a ~ T ++ F) -> uniq ((map g E) ++ F).
  Proof.
    intros; apply uniq_map_app_1; eauto.
  Qed.


End Mapping_Env.

Hint Resolve dom_map_1 dom_map_2 dom_map_3 dom_map_4.
Hint Resolve map_extends_1 map_extends_2.
Hint Resolve uniq_dom_only uniq_dom_only_1.
Hint Resolve map_uniq_1 map_uniq_2 map_uniq_3 map_uniq_4 map_uniq_4 map_uniq_5.

Section notin_extra.

  Lemma notin_neq : forall A (E E0:env A) (T:A) (a b:atom),
    b # (E ++ a ~ T ++ E0) -> a <> b.
  Proof.
    intros; repeat rewrite dom_app in *.
    destruct_notin; simpl_alist in *; solve_notin.
  Qed.


  Lemma notin_app_1 : forall A (E F:env A) (a:atom),
    a # (E ++ F) -> a # E /\ a # F.
  Proof.
    split; induction E as [| (b,T)]; simpl in *; intros; try solve_notin.
  Qed.

  Lemma notin_app_2 : forall A (E F:env A) (a:atom),
    a # E -> a # F -> a # (E ++ F).
  Proof.
    induction E as [| (b,T)]; simpl in *; intros; auto; solve_notin.
  Qed.
End notin_extra.

Hint Resolve @notin_neq @notin_app_1 @notin_app_2.

Lemma notin_cons_mid : forall (A:Type) (x y:atom) (E F:env A)(P:A),
  x # (E ++ y ~ P ++ F) ->
  x # (E ++ F).
Proof.
  intros.
  elim (notin_app_1 A E (y ~ P ++ F) x H); intros.
  elim (notin_app_1 A (y ~ P) F x H1); intros.  
  apply notin_app_2; auto.
Qed.




