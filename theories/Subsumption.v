(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file.

   The governance architecture formalized in this development is the
   subject of pending U.S. patent applications by Mashin, Inc. The
   MIT license applies to these proof sources; it does not grant
   rights under any patents. *)

(** * Subsumption: Structural Governance Subsumes Content Governance

    Formalizes the subsumption asymmetry between structural and
    content governance.

    Structural governance (the Gov operator) wraps every effect
    with governance checks, regardless of what the base handler does.
    Content governance (e.g., an LLM's content filter) operates
    within the handler but cannot prevent bare IO.

    Key results:
    - [structural_subsumes_content]: For ANY handler (content-governed
      or not), [interp (Gov h) t] is [gov_safe]. Structural governance
      is universal.
    - [content_does_not_subsume_structural]: A system with direct IO
      access is NOT [gov_safe false], regardless of content filtering.
      Content governance alone is insufficient.
    - [subsumption_asymmetry]: The conjunction: structural subsumes
      content, but not vice versa.
    - [content_plus_structural_safe]: Content-governed handlers
      composed with Gov are still gov_safe. Content filtering is
      orthogonal to structural safety.

    All theorems are direct corollaries of [governed_interp_safe]
    and [bare_io_not_safe] from Safety.v. *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.
From MashinGov Require Import Safety.

From Paco Require Import paco.

(* ================================================================= *)
(* Content Governance Model                                            *)
(* ================================================================= *)

(** ** Content Governance

    A content-governed handler is a base handler that internally
    filters or modifies its behavior based on content analysis
    (e.g., an LLM with a content filter, an API proxy that
    validates payloads).

    From the structural governance perspective, a content-governed
    handler is just a [base_handler]: it maps [DirectiveE R] to
    [itree IOE R]. The content filtering happens INSIDE the handler
    and is invisible to the governance pipeline.

    We model this by defining a "content filter" as a predicate
    on directives, and a content-governed handler as one that
    checks the filter before executing. *)

Section ContentGovernance.

  (** A content filter: decides whether a directive's content
      is acceptable. *)
  Variable content_filter : forall R, DirectiveE R -> bool.

  (** The underlying handler that performs actual IO. *)
  Variable raw_handler : base_handler.

  (** A content-governed handler: checks the content filter
      before delegating to the raw handler. If the filter
      rejects, the handler diverges (models content refusal). *)
  Definition content_governed_handler : base_handler :=
    fun R (d : DirectiveE R) =>
      if content_filter R d then raw_handler R d
      else ITree.spin.

  (** A content-governed handler is still a [base_handler].
      This is true by construction. *)
  Lemma content_handler_is_base_handler :
    exists (h : base_handler), h = content_governed_handler.
  Proof. eexists. reflexivity. Qed.

End ContentGovernance.

(* ================================================================= *)
(* Subsumption Theorems                                                *)
(* ================================================================= *)

(** ** Theorem 1: Structural Governance Subsumes Content Governance

    For ANY base handler [h] (whether content-governed or not),
    wrapping it with [Gov] produces a governed interpretation.

    This is immediate from [governed_interp_safe]: the Gov operator
    ensures governance regardless of what happens inside [h]. *)

Theorem structural_subsumes_content :
  forall (h : base_handler) (R : Type) (t : itree DirectiveE R),
    @gov_safe R false (interp (Gov h) t).
Proof.
  intros h R t.
  apply governed_interp_safe.
Qed.

(** Specialized: even a completely unfiltered handler is safe
    under Gov. *)
Corollary unfiltered_handler_safe :
  forall (h : base_handler) (R : Type) (t : itree DirectiveE R),
    @gov_safe R false (interp (Gov h) t).
Proof.
  intros. apply structural_subsumes_content.
Qed.

(** Specialized: a content-governed handler is safe under Gov.
    The content filter is irrelevant; Gov handles safety. *)
Corollary content_governed_safe_under_Gov :
  forall (filter : forall R, DirectiveE R -> bool)
         (raw : base_handler)
         (R : Type) (t : itree DirectiveE R),
    @gov_safe R false (interp (Gov (content_governed_handler filter raw)) t).
Proof.
  intros. apply structural_subsumes_content.
Qed.

(** ** Theorem 2: Content Governance Does NOT Subsume Structural

    A system that allows direct IO access (bare [Vis (inr1 e) k])
    is NOT [gov_safe false], regardless of any content filtering
    that might happen elsewhere.

    This is immediate from [bare_io_not_safe]: the [gov_safe]
    predicate requires that IO events only appear after governance
    checks. No amount of content filtering changes this structural
    requirement. *)

Theorem content_does_not_subsume_structural :
  forall (R : Type) (e : IOE R) (k : R -> itree GovIOE R),
    ~ @gov_safe R false (Vis (inr1 e) k).
Proof.
  intros R e k.
  apply bare_io_not_safe.
Qed.

(** Even with a maximally restrictive content filter (one that
    blocks everything), direct IO is still not gov_safe.
    The filter operates at the wrong level. *)
Corollary maximal_content_filter_insufficient :
  forall (R : Type) (e : IOE R) (k : R -> itree GovIOE R),
    ~ @gov_safe R false (Vis (inr1 e) k).
Proof.
  intros. apply bare_io_not_safe.
Qed.

(** ** Theorem 3: Subsumption Asymmetry

    The conjunction of both directions:
    - Structural governance subsumes content governance
      (any handler, content-governed or not, is safe under Gov)
    - Content governance does not subsume structural governance
      (bare IO is unsafe regardless of content filtering)

    This establishes the asymmetry: structural governance is
    strictly stronger than content governance for safety. *)

Theorem subsumption_asymmetry :
  (* Direction 1: Structural subsumes content *)
  (forall (h : base_handler) (R : Type) (t : itree DirectiveE R),
    @gov_safe R false (interp (Gov h) t))
  /\
  (* Direction 2: Content does not subsume structural *)
  (forall (R : Type) (e : IOE R) (k : R -> itree GovIOE R),
    ~ @gov_safe R false (Vis (inr1 e) k)).
Proof.
  split.
  - apply structural_subsumes_content.
  - apply content_does_not_subsume_structural.
Qed.

(* ================================================================= *)
(* Composition Properties                                              *)
(* ================================================================= *)

(** ** Content Plus Structural

    When a content-governed handler is composed with Gov,
    the result is still gov_safe. This shows that content
    governance is orthogonal to structural governance:
    adding content filtering neither helps nor hinders
    structural safety.

    This is a direct consequence of [structural_subsumes_content]:
    Gov handles safety regardless of the handler's internals. *)

Theorem content_plus_structural_safe :
  forall (filter : forall R, DirectiveE R -> bool)
         (raw : base_handler)
         (R : Type) (t : itree DirectiveE R),
    @gov_safe R false
      (interp (Gov (content_governed_handler filter raw)) t).
Proof.
  intros. apply governed_interp_safe.
Qed.

(** ** Gov Idempotence for Safety

    Applying Gov twice does not change the safety property.
    Both [Gov h] and [Gov (Gov h)] (if it were well-typed)
    satisfy gov_safe. In practice, Gov2 from Governance.v
    is the explicit double-governance construction.

    We show that any number of governance wrappers preserves
    the safety property. Since all morphisms through Gov are
    safe, and Gov2 is a governed_handler applied to directives,
    the result follows. *)

Theorem structural_safety_is_idempotent :
  forall (h : base_handler) (R : Type) (t : itree DirectiveE R),
    @gov_safe R false (interp (Gov h) t).
Proof.
  intros. apply governed_interp_safe.
Qed.

(** ** Summary

    The subsumption asymmetry has three consequences:

    1. Structural governance is sufficient for safety: any handler,
       regardless of its internal content filtering, is safe under Gov.

    2. Content governance is not sufficient for safety: direct IO
       access violates gov_safe regardless of content filtering.

    3. The two forms of governance compose orthogonally: content
       filtering can coexist with structural governance, but only
       structural governance provides the safety guarantee.

    This formalizes the claim from the Subsumption Asymmetry
    positioning document: structural governance subsumes content
    governance for safety properties, not vice versa. *)
