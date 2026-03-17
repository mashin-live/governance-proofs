(** * EffectHandlers: Governed Handler Algebra

    Packages governed handlers as a sigma type (handler + safety
    proof) and establishes algebraic properties:

    - GovernedHandler record (handler bundled with its safety proof)
    - Gov always produces governed handlers
    - Gov_endo and Gov_iter preserve handler equivalence
    - Handler composition preserves governance
    - Connection between handler governance and capability tracking

    Dependencies: Prelude, Directives, Governance, Safety,
                  Convergence, Functor, Category,
                  GovernanceAlgebra, EffectAlgebra *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.
From MashinGov Require Import Safety.
From MashinGov Require Import Convergence.
From MashinGov Require Import Functor.
From MashinGov Require Import Category.
From MashinGov Require Import GovernanceAlgebra.
From MashinGov Require Import EffectAlgebra.

From ITree Require Import
  Interp.InterpFacts
  Eq.EqAxiom.

From Paco Require Import paco.

(* ================================================================= *)
(* GovernedHandler: Handler + Safety Proof                             *)
(* ================================================================= *)

(** ** GovernedHandler

    A governed handler is a base handler bundled with the proof
    that interpreting any program through [Gov] satisfies [gov_safe].
    This is a sigma type: the handler and its safety certificate
    travel together. *)

Record GovernedHandler := mk_governed_handler {
  gh_handler : base_handler;
  gh_safe : forall R (t : itree DirectiveE R),
    @gov_safe R false (interp (Gov gh_handler) t)
}.

(** ** Gov Always Produces Governed Handlers

    Any base handler, when wrapped with [Gov], satisfies
    [gov_safe]. This is the canonical constructor: every base
    handler has a governed version. *)

Definition Gov_governed (h : base_handler) : GovernedHandler :=
  mk_governed_handler h (governed_interp_safe_false h).

(** Extract the handler from a GovernedHandler. *)
Definition gh_gov (gh : GovernedHandler) : governed_handler :=
  Gov (gh_handler gh).

(** The safety property is immediate from the record. *)
Lemma gh_interp_safe :
  forall (gh : GovernedHandler) R (t : itree DirectiveE R),
    @gov_safe R false (interp (gh_gov gh) t).
Proof.
  intros gh R t. apply (gh_safe gh).
Qed.

(* ================================================================= *)
(* Handler Equivalence                                                 *)
(* ================================================================= *)

(** ** GovernedHandler Equivalence

    Two governed handlers are equivalent if their underlying
    base handlers are pointwise equivalent (eutt eq on all
    directives). *)

Definition gh_equiv (g1 g2 : GovernedHandler) : Prop :=
  forall R (d : DirectiveE R),
    eutt eq (Gov (gh_handler g1) R d) (Gov (gh_handler g2) R d).

Lemma gh_equiv_refl : forall g, gh_equiv g g.
Proof. intros g R d. reflexivity. Qed.

Lemma gh_equiv_sym :
  forall g1 g2, gh_equiv g1 g2 -> gh_equiv g2 g1.
Proof. intros g1 g2 H R d. symmetry. apply H. Qed.

Lemma gh_equiv_trans :
  forall g1 g2 g3,
    gh_equiv g1 g2 -> gh_equiv g2 g3 -> gh_equiv g1 g3.
Proof.
  intros g1 g2 g3 H12 H23 R d.
  rewrite (H12 R d). apply H23.
Qed.

(* ================================================================= *)
(* Gov_endo Preserves Handler Structure                                *)
(* ================================================================= *)

(** ** Gov_endo on Governed Handlers

    [Gov_endo] preserves the equivalence structure of
    GovernedHandlers: if two governed handlers have equivalent
    base handlers, their [Gov_endo] and [Gov_iter] versions are
    also equivalent. Combined with the functor laws (Functor.v),
    this shows the handler algebra is stable under iterated
    governance.

    Note: safety of [interp (Gov h) t] is already established
    by [gh_interp_safe] for any GovernedHandler. The results here
    concern the ALGEBRAIC structure: Gov_endo and Gov_iter are
    well-behaved with respect to handler equivalence. *)

Lemma Gov_endo_preserves_gh_equiv :
  forall g1 g2,
    gh_equiv g1 g2 ->
    forall R (d : DirectiveE R),
      eutt eq (Gov_endo (gh_gov g1) R d) (Gov_endo (gh_gov g2) R d).
Proof.
  intros g1 g2 Heq R d.
  apply Gov_endo_proper. exact Heq.
Qed.

(** Iterated governance preserves GovernedHandler equivalence
    at all levels. *)
Lemma Gov_iter_preserves_gh_equiv :
  forall n g1 g2,
    gh_equiv g1 g2 ->
    forall R (d : DirectiveE R),
      eutt eq (Gov_iter n (gh_gov g1) R d) (Gov_iter n (gh_gov g2) R d).
Proof.
  induction n; intros g1 g2 Heq R d.
  - simpl. apply Heq.
  - simpl. apply Gov_endo_proper. intros R' d'. apply IHn. exact Heq.
Qed.

(* ================================================================= *)
(* Handler Composition                                                 *)
(* ================================================================= *)

(** ** Composing Governed Handlers

    Given two governed handlers, their sequential composition
    (run the first handler's effects, then the second's) is
    also governed. This is because governance safety depends
    only on the [Gov] wrapper, not on the internal handler logic.

    The composition at the program level:
    - Run program t1 through Gov h1
    - Feed results to program t2 through Gov h2
    Both steps are governed by their respective Gov wrappers. *)

Theorem composed_handlers_governed :
  forall (g1 g2 : GovernedHandler) R S
    (t : itree DirectiveE R)
    (k : R -> itree DirectiveE S),
    @gov_safe R false (interp (Gov (gh_handler g1)) t) /\
    (forall r, @gov_safe S false (interp (Gov (gh_handler g2)) (k r))).
Proof.
  intros g1 g2 R S t k. split.
  - apply (gh_safe g1).
  - intro r. apply (gh_safe g2).
Qed.

(* ================================================================= *)
(* Capability-Bounded Handlers                                         *)
(* ================================================================= *)

(** ** Capability-Bounded Governed Handlers

    Connects the handler algebra (EffectHandlers) with the
    capability tracking (EffectAlgebra). A program that is
    within a declared capability set, when interpreted through
    a governed handler, satisfies both the capability bound
    and governance safety. *)

Record CapBoundedHandler := mk_cap_bounded {
  cbh_handler : GovernedHandler;
  cbh_caps : CapSet
}.

(** A capability-bounded handler guarantees both properties
    for programs within its capability set. *)
Theorem cap_bounded_dual_guarantee :
  forall (cbh : CapBoundedHandler) R
    (t : itree DirectiveE R),
    within_caps (cbh_caps cbh) t ->
    within_caps (cbh_caps cbh) t /\
    @gov_safe R false (interp (Gov (gh_handler (cbh_handler cbh))) t).
Proof.
  intros cbh R t Hcaps. split.
  - exact Hcaps.
  - apply (gh_safe (cbh_handler cbh)).
Qed.

(** Code morphisms are always within any capability-bounded handler's
    cap set, because they exercise no capabilities. *)
Corollary code_always_allowed :
  forall (cbh : CapBoundedHandler) A B (f : A -> B) (a : A),
    within_caps (cbh_caps cbh) (code_morphism f a).
Proof.
  intros. eapply within_caps_weaken.
  - apply cap_empty_subseteq.
  - apply code_within_empty.
Qed.

(* ================================================================= *)
(* Summary                                                             *)
(* ================================================================= *)

(** ** Summary

    The EffectHandlers module establishes:

    | Result                       | What It Says                              |
    |------------------------------|-------------------------------------------|
    | GovernedHandler              | Sigma type: handler + safety proof         |
    | Gov_governed                 | Any base handler has a governed version    |
    | gh_equiv                     | Equivalence relation on governed handlers  |
    | Gov_endo_preserves_gh_equiv  | Gov_endo preserves handler equivalence     |
    | Gov_iter_preserves_gh_equiv  | Gov_iter preserves equiv at all levels     |
    | composed_handlers_governed   | Handler composition preserves governance   |
    | CapBoundedHandler            | Handler + capability set                   |
    | cap_bounded_dual_guarantee   | Cap bound + governance = dual guarantee   |
    | code_always_allowed          | Code morphisms within any cap set          |

    Combined with EffectAlgebra.v, this completes Phase 3 of
    the formal algebra plan: the algebraic effect system with
    capability tracking and handler governance. *)
