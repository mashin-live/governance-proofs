(** * GovernanceAlgebra: Abstract Governance Structure

    Packages the core governance properties as a Coq record,
    enabling theorems to be stated for ANY governance operator
    that satisfies these axioms, not just the specific [Gov]
    from Governance.v.

    The record captures three independent properties:
    - G1 (Safety): governed interpretation satisfies [gov_safe]
    - G2 (Transparency): governance preserves permitted semantics
    - G3 (Proper): governance respects handler equivalence

    From these, we derive:
    - Convergence: all meta-recursive levels are governed
    - Subsumption asymmetry: structural > content governance
    - Compositional closure: all morphism compositions are governed
    - Idempotence: iterated governance preserves safety

    Finally, we instantiate the record with the existing [Gov]
    operator, connecting all prior proofs to the abstract framework.

    Dependencies: Prelude, Directives, Governance, Safety,
                  Convergence, Transparency, Subsumption,
                  Category, Functor *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.
From MashinGov Require Import Safety.
From MashinGov Require Import Convergence.
From MashinGov Require Import Transparency.
From MashinGov Require Import Subsumption.
From MashinGov Require Import Category.
From MashinGov Require Import Functor.

From ITree Require Import
  Interp.InterpFacts.

From Paco Require Import paco.

(* ================================================================= *)
(* The Governance Algebra Record                                       *)
(* ================================================================= *)

(** ** GovernanceAlgebra

    An abstract governance algebra over the fixed directive type
    [DirectiveE] and governed event type [GovIOE]. The algebra
    is parameterized over the governance operator itself.

    Three axioms capture the essential properties:

    1. Safety (G1): For any handler and any program, the governed
       interpretation satisfies [gov_safe]. This is the core
       invariant: every effect passes through governance.

    2. Transparency (G2): Under permissive governance (all checks
       pass), the governed interpretation produces the same result
       as ungoverned interpretation. Governance restricts which
       programs run, but does not alter permitted programs.

    3. Handler Proper (G3): Equivalent handlers produce equivalent
       governed handlers. This is needed for the functor laws and
       ensures governance is structurally compositional.

    These are independent: safety does not imply transparency
    (a safe operator could alter results), transparency does not
    imply safety (an operator could be transparent but not wrap
    IO with governance), and properness is orthogonal to both. *)

Record GovernanceAlgebra := mk_gov_algebra {
  (** The governance operator: wraps a base handler with governance *)
  ga_Gov : base_handler -> governed_handler;

  (** G1: Safety (Totality)
      For any base handler, any permission level, and any program,
      the governed interpretation satisfies [gov_safe].

      Quantifying over [allowed] (not just [false]) strengthens
      the statement and simplifies coinductive proofs that need
      the hypothesis at [true]. *)
  ga_safe : forall (h : base_handler) (R : Type) (allowed : bool)
    (t : itree DirectiveE R),
    @gov_safe R allowed (interp (ga_Gov h) t);

  (** G2: Transparency (Semantic Preservation)
      Under permissive governance, the governed interpretation is
      observationally equivalent to ungoverned interpretation.

      The permissive handler resolves all GovCheck events to [true],
      so governance never denies. Under this interpretation, the
      governance events are erased and only the base handler's IO
      effects remain. *)
  ga_transparent : forall (h : base_handler) (io_h : forall X, IOE X -> X)
    (R : Type) (t : itree DirectiveE R),
    @eutt void1 R R eq
      (interp (fun X e => Ret (permissive_handler io_h X e))
              (interp (ga_Gov h) t))
      (interp (fun X e => Ret (io_h X e))
              (interp h t));

  (** G3: Handler Proper (Equivalence Preservation)
      If two base handlers are pointwise equivalent (eutt eq on
      all directives), then their governed versions are also
      pointwise equivalent.

      This is the functor morphism-preservation property, stated
      at the base_handler level. *)
  ga_proper : forall (h1 h2 : base_handler),
    (forall R (d : DirectiveE R), eutt eq (h1 R d) (h2 R d)) ->
    forall R (d : DirectiveE R), eutt eq (ga_Gov h1 R d) (ga_Gov h2 R d);
}.

(* ================================================================= *)
(* Derived Properties                                                  *)
(* ================================================================= *)

(** ** Derived: Convergence

    Governance holds uniformly at all levels of the meta-recursive
    tower. Since [machine_at_level n R = itree DirectiveE R] by
    definition, this follows directly from [ga_safe]. *)

Section Derived.

  Variable G : GovernanceAlgebra.

  Theorem ga_convergence :
    forall (h : base_handler) (n : nat) (R : Type)
      (t : machine_at_level n R),
      @gov_safe R false (interp (ga_Gov G h) t).
  Proof.
    intros h n R t.
    (* machine_at_level n R = itree DirectiveE R *)
    apply (ga_safe G).
  Qed.

  (** ** Derived: Subsumption Asymmetry

      Structural governance (via [ga_Gov G]) subsumes content
      governance: any handler, content-filtered or not, is safe.
      Content governance alone is insufficient: bare IO violates
      [gov_safe].

      The positive direction follows from [ga_safe].
      The negative direction follows from [bare_io_not_safe],
      which is a property of [gov_safe] itself, independent
      of any particular governance operator. *)

  Theorem ga_subsumption_asymmetry :
    (* Structural subsumes content *)
    (forall (h : base_handler) (R : Type) (t : itree DirectiveE R),
      @gov_safe R false (interp (ga_Gov G h) t))
    /\
    (* Content does not subsume structural *)
    (forall (R : Type) (e : IOE R) (k : R -> itree GovIOE R),
      ~ @gov_safe R false (Vis (inr1 e) k)).
  Proof.
    split.
    - intros h R t. apply (ga_safe G).
    - intros R e k. apply bare_io_not_safe.
  Qed.

  (** ** Derived: Compositional Closure

      Every morphism in Category Mashin, applied to any input,
      produces a governed interpretation under [ga_Gov G].

      This follows from [ga_safe]: the morphism's output is
      an [itree DirectiveE B], which is governed by [ga_safe]. *)

  Theorem ga_morphism_governed :
    forall (h : base_handler) (A B : Type)
      (f : mashin_morphism A B) (a : A),
      @gov_safe B false (interp (ga_Gov G h) (f a)).
  Proof.
    intros h A B f a. apply (ga_safe G).
  Qed.

  (** Compositions of morphisms are governed. *)
  Theorem ga_composed_governed :
    forall (h : base_handler) (A B C : Type)
      (f : mashin_morphism A B) (g : mashin_morphism B C) (a : A),
      @gov_safe C false (interp (ga_Gov G h) ((f >>> g) a)).
  Proof.
    intros h A B C f g a. apply (ga_safe G).
  Qed.

  (** ** Derived: Goal Reachability Preservation

      If a program reaches a goal under ungoverned interpretation
      and governance permits, the same goal value exists.
      Follows from [ga_transparent]. *)

  Theorem ga_goal_preservation :
    forall (h : base_handler) (io_h : forall X, IOE X -> X)
      (R : Type) (v : R) (t : itree DirectiveE R),
      @eutt void1 R R eq
        (interp (fun X e => Ret (io_h X e)) (interp h t))
        (Ret v) ->
      @eutt void1 R R eq
        (interp (fun X e => Ret (permissive_handler io_h X e))
                (interp (ga_Gov G h) t))
        (Ret v).
  Proof.
    intros h io_h R v t Hreach.
    rewrite (ga_transparent G h io_h R t).
    exact Hreach.
  Qed.

  (** ** Derived: Content-Governed Handlers Safe

      A content-governed handler (one with an internal content
      filter) composed with the governance operator is safe.
      The content filter is irrelevant; governance handles safety. *)

  Theorem ga_content_governed_safe :
    forall (filter : forall R, DirectiveE R -> bool)
           (raw : base_handler)
           (R : Type) (t : itree DirectiveE R),
      @gov_safe R false
        (interp (ga_Gov G (content_governed_handler filter raw)) t).
  Proof.
    intros. apply (ga_safe G).
  Qed.

  (** ** Derived: Pure Code Is Trivially Governed

      A code morphism (pure computation, no directives) is governed.
      This is a specific instance of [ga_morphism_governed] but
      worth stating explicitly: pure computation needs no governance
      checks, and the algebra confirms this. *)

  Corollary ga_code_governed :
    forall (h : base_handler) (A B : Type) (f : A -> B) (a : A),
      @gov_safe B false (interp (ga_Gov G h) (code_morphism f a)).
  Proof.
    intros. apply (ga_safe G).
  Qed.

End Derived.

(* ================================================================= *)
(* Instantiation: The Mashin Gov Operator                              *)
(* ================================================================= *)

(** ** mashin_governance

    The canonical instance of [GovernanceAlgebra] using the [Gov]
    operator from Governance.v. All three axioms are discharged by
    existing theorems:

    - G1 (Safety): [governed_interp_safe] from Safety.v
    - G2 (Transparency): [governed_transparency] from Transparency.v
    - G3 (Proper): derived from [Gov_endo_proper] via factorization *)

(** Helper: Gov preserves base handler equivalence.

    If [h1] and [h2] are pointwise equivalent base handlers,
    then [Gov h1] and [Gov h2] are pointwise equivalent governed
    handlers.

    Proof strategy: factor [Gov h] as [Gov_endo (embed_handler h)]
    via [Gov_factorization], then use [Gov_endo_proper] with the
    lifted equivalence on [embed_handler]. *)
Lemma Gov_base_proper :
  forall (h1 h2 : base_handler),
    (forall R (d : DirectiveE R), eutt eq (h1 R d) (h2 R d)) ->
    forall R (d : DirectiveE R), eutt eq (Gov h1 R d) (Gov h2 R d).
Proof.
  intros h1 h2 Heq R d.
  rewrite Gov_factorization.
  rewrite Gov_factorization.
  apply Gov_endo_proper.
  (* embed_handler h1 ≈ embed_handler h2 *)
  intros R' d'.
  unfold embed_handler, lift_io.
  apply eutt_translate_gen.
  apply Heq.
Qed.

(** The canonical Mashin governance algebra. *)
Definition mashin_governance : GovernanceAlgebra :=
  mk_gov_algebra
    Gov
    governed_interp_safe
    governed_transparency
    Gov_base_proper.

(** Verify: the instance is well-formed and computable. *)
Lemma mashin_governance_gov_is_Gov :
  ga_Gov mashin_governance = Gov.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* Algebra-Level Theorems                                              *)
(* ================================================================= *)

(** ** Theorem: Any GovernanceAlgebra Gives Subsumption

    For ANY GovernanceAlgebra (not just mashin_governance),
    structural governance strictly subsumes content governance.
    This is a theorem about the algebraic STRUCTURE, not about
    a specific operator. *)

Theorem any_governance_algebra_subsumes :
  forall (G : GovernanceAlgebra),
    (* Structural subsumes content *)
    (forall h R (t : itree DirectiveE R),
      @gov_safe R false (interp (ga_Gov G h) t))
    /\
    (* Content does not subsume structural *)
    (forall R (e : IOE R) (k : R -> itree GovIOE R),
      ~ @gov_safe R false (Vis (inr1 e) k)).
Proof.
  intro G. apply ga_subsumption_asymmetry.
Qed.

(** ** Theorem: Any GovernanceAlgebra Gives Convergence

    Governance holds at all meta-recursive levels for any
    instance of the algebra. *)

Theorem any_governance_algebra_converges :
  forall (G : GovernanceAlgebra) (h : base_handler) (n : nat)
    (R : Type) (t : machine_at_level n R),
    @gov_safe R false (interp (ga_Gov G h) t).
Proof.
  intros. apply ga_convergence.
Qed.

(** ** Theorem: Any GovernanceAlgebra Preserves Goals

    For any instance, if a program reaches a goal without governance,
    the governed version reaches the same goal (when permitted). *)

Theorem any_governance_algebra_preserves_goals :
  forall (G : GovernanceAlgebra) (h : base_handler)
    (io_h : forall X, IOE X -> X) (R : Type) (v : R)
    (t : itree DirectiveE R),
    @eutt void1 R R eq
      (interp (fun X e => Ret (io_h X e)) (interp h t))
      (Ret v) ->
    @eutt void1 R R eq
      (interp (fun X e => Ret (permissive_handler io_h X e))
              (interp (ga_Gov G h) t))
      (Ret v).
Proof.
  intros. apply (ga_goal_preservation G); assumption.
Qed.

(* ================================================================= *)
(* Summary                                                             *)
(* ================================================================= *)

(** ** Summary

    The GovernanceAlgebra record provides an abstract interface to
    governance properties. The key insight is that three axioms
    (safety, transparency, properness) are sufficient to derive
    all the major governance theorems:

    | Derived Property         | From            |
    |--------------------------|-----------------|
    | Convergence              | G1 (safety)     |
    | Subsumption asymmetry    | G1 + gov_safe   |
    | Compositional closure    | G1 (safety)     |
    | Goal preservation        | G2 (transparent)|
    | Content governance safe  | G1 (safety)     |
    | Code trivially governed  | G1 (safety)     |

    The mashin_governance instance connects this abstraction to
    the concrete Gov operator and its 166+ existing theorems.

    Future phases extend this record:
    - Phase 2: monoidal structure on morphisms
    - Phase 3: effect rows and governed handler algebra
    - Phase 4: capability-indexed composition
    - Phase 5: trace semantics and ledger connection
    - Phase 6: coterminous boundary as an algebraic theorem *)
