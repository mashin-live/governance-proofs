(** * Convergence: Meta-Recursive Governance Tower

    Formalizes:
    - Definition 5.5 (Governance Levels) from the paper
    - Theorem 5.7 (Governance Convergence) from the paper
    - Theorem 5.8 (Fixed Point) from the paper

    The key insight: every machine, regardless of its "level"
    in the meta-recursive tower, has the same type:
    [itree DirectiveE R]. The governed interpreter treats all
    machines uniformly. Convergence follows from type equality.

    Uses the [gov_safe] predicate from Safety.v, which is
    non-trivial: it is FALSE for bare IO trees and TRUE for
    governed interpretations. *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.
From MashinGov Require Import Safety.

From ITree Require Import
  Interp.InterpFacts.

(** ** Governance Levels

    A machine at any level is just an [itree DirectiveE R].
    The level index tracks meta-recursive depth for reasoning
    but does not affect the type or behavior. *)

Definition machine_at_level (n : nat) (R : Type) : Type :=
  itree DirectiveE R.

(** ** The Governed Property

    A machine is "governed" if its interpretation through
    [interp (Gov h)] satisfies [gov_safe false]: no bare IO
    events occur without prior governance checks.

    Unlike the previous [is_governed] (which was tautologically
    true for all trees), [gov_safe false] is:
    - FALSE for [Vis (inr1 e) k] (bare IO without governance)
    - TRUE for [interp (Gov h) t] (the main safety theorem) *)

Section Convergence.

  Variable h : base_handler.

  Definition is_governed {R : Type} (t : itree DirectiveE R) : Prop :=
    @gov_safe R false (interp (Gov h) t).

  (** Every pure executor program is governed, because
      [interp (Gov h)] wraps every directive with governance
      checks, satisfying [gov_safe false]. *)
  Lemma all_pure_executors_governed :
    forall R (t : itree DirectiveE R), is_governed t.
  Proof.
    intros R t.
    unfold is_governed.
    apply governed_interp_safe.
  Qed.

  (** Governance at Level 0. *)
  Lemma governed_level_0 :
    forall R (t : machine_at_level 0 R), is_governed t.
  Proof.
    intros R t.
    apply all_pure_executors_governed.
  Qed.

  (** If governance holds at Level n, it holds at Level n+1.

      A Level(n+1) machine introspects Level(n) machines by
      emitting directives (MemoryOp, LLMCall). But it still
      has type [itree DirectiveE R], so governance applies
      identically. *)
  Lemma governed_level_step :
    forall n R,
      (forall S (t : machine_at_level n S), is_governed t) ->
      forall (t : machine_at_level (S n) R), is_governed t.
  Proof.
    intros n R _ t.
    (* machine_at_level (S n) R = itree DirectiveE R
       = machine_at_level n R.
       Governance is independent of the level index. *)
    apply all_pure_executors_governed.
  Qed.

  (** ** Theorem 5.7: Governance Convergence

      For all n >= 0: Level(n) is governed by G.

      The proof is by induction, but the substance is that
      [machine_at_level n R] is definitionally [itree DirectiveE R]
      for all n. The uniform execution model makes governance
      independent of level. *)
  Theorem governance_convergence :
    forall n R (t : machine_at_level n R), is_governed t.
  Proof.
    intros n. induction n.
    - intros R t. apply governed_level_0.
    - intros R t. apply (governed_level_step n R IHn t).
  Qed.

  (** ** Theorem 5.8: Fixed Point

      The union Omega of all levels is governed, and adding
      another level produces no new ungoverned machines.

      Since [machine_at_level n R = itree DirectiveE R] for
      all n, Omega is just [itree DirectiveE R], which is
      already governed by [all_pure_executors_governed]. *)

  Definition machine_in_omega (R : Type) : Type := itree DirectiveE R.

  Theorem fixed_point :
    forall R (t : machine_in_omega R), is_governed t.
  Proof.
    intros R t.
    apply all_pure_executors_governed.
  Qed.

  (** ** Structural Uniformity

      The deeper result: [interp (Gov h)] distributes over
      [bind] (from Interpreter.v), which means governance
      of a composed machine follows from governance of its
      parts. A governor machine calling a governed machine
      produces a fully governed composite. *)

  Lemma governance_composition :
    forall A B (t : itree DirectiveE A) (k : A -> itree DirectiveE B),
      eq_itree eq
        (interp (Gov h) (ITree.bind t k))
        (ITree.bind (interp (Gov h) t) (fun r => interp (Gov h) (k r))).
  Proof.
    intros A B t k.
    apply interp_bind.
  Qed.

End Convergence.
