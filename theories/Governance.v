(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file.

   The governance architecture formalized in this development is the
   subject of pending U.S. patent applications by Mashin, Inc. The
   MIT license applies to these proof sources; it does not grant
   rights under any patents. *)

(** * Governance: Pipeline and Gov Operator

    Formalizes:
    - Definition 3 (Governance Pipeline) from the paper
    - Definition 4.7 (Governance Operator / Gov) from the paper

    The governance pipeline is a composition of stages:
      govern(d, g) = trust(d,g) >> permission(d,g) >> phase(d,g)
                     >> hooks(d,g) >> execute(d) >> guardrails(d,r,g)
                     >> record(d,r,g) >> broadcast(d,r,g) >> return r

    The Gov operator transforms any handler (interpretation) into
    a governed handler by wrapping it with these stages.

    In ITrees terms:
    - A handler is [DirectiveE ~> itree IOE]
    - Gov takes a handler and returns a handler of type
      [DirectiveE ~> itree GovIOE]
    - Gov wraps each directive handling with governance events *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.

(** ** Governance Context

    The governance context carries trust level, permissions,
    execution phase, and hook configurations. We abstract this
    as a record; the proofs are parametric over its contents. *)

Inductive TrustLevel :=
  | Untrusted
  | Tested
  | Evaluated
  | Reviewed
  | Stdlib
  | System.

Record GovernanceContext := mk_gov_ctx {
  trust_level   : TrustLevel;
  permissions   : list string;     (** allowed directive tags *)
  phase         : string;          (** current execution phase *)
  hooks_enabled : bool;
}.

(** A governance decision: allowed or denied with reason *)
Inductive GovDecision :=
  | Allowed
  | Denied (reason : string).

(** ** Governance Pipeline Stages

    Each stage is a function from a directive + governance context
    to a governance decision. We model them abstractly: the proofs
    need only their type signatures and the fact that they are
    total functions on directive structure, not content.

    Key property from the paper's naturality proof (Theorem 4.8):
    governance stages depend only on the directive [d] and
    governance context [g], NOT on the types X or Y.
    This is what makes the governed interpretation a natural
    transformation. *)

(** Abstract governance check: emits a GovE event and
    returns whether the check passed. *)
Definition gov_check (stage : GovernanceStage) : itree GovIOE bool :=
  trigger (inl1 (GovCheck stage)).

(** Run all pre-execution governance stages.
    Short-circuits on failure (returns false). *)
Definition pre_governance : itree GovIOE bool :=
  ITree.bind (gov_check TrustCheck) (fun trust_ok =>
  if trust_ok then
    ITree.bind (gov_check PermissionCheck) (fun perm_ok =>
    if perm_ok then
      ITree.bind (gov_check PhaseValidation) (fun phase_ok =>
      if phase_ok then
        gov_check PreHooks
      else ret false)
    else ret false)
  else ret false).

(** Run all post-execution governance stages.
    These always run (no short-circuit): guardrails check
    the result, provenance records, broadcast notifies. *)
Definition post_governance : itree GovIOE bool :=
  ITree.bind (gov_check Guardrails) (fun guard_ok =>
  ITree.bind (gov_check ProvenanceRecord) (fun _ =>
  ITree.bind (gov_check EventBroadcast) (fun _ =>
  ret guard_ok))).

(** ** Handler Types

    A handler maps events to interaction trees. In ITrees:
      handler E F := forall R, E R -> itree F R

    This is the "interpretation" from Definition 4.5. *)

(** A base handler: interprets DirectiveE into IOE.
    This is the ungoverned interpretation eta from the paper. *)
Definition base_handler := forall R, DirectiveE R -> itree IOE R.

(** A governed handler: interprets DirectiveE into GovIOE.
    This is the governed interpretation eta_G from the paper. *)
Definition governed_handler := forall R, DirectiveE R -> itree GovIOE R.

(** ** The Governance Operator (Gov)

    Definition 4.7 from the paper:

    Gov(interp)(d, k) =
      trust(d) >> permission(d) >> phase(d) >> hooks(d) >>
      interp(d, k) >>= fun r =>
      guardrails(d, r) >> record(d, r) >> broadcast(d, r) >>
      return r

    Gov transforms any base handler into a governed handler.
    It wraps each directive's handling with pre- and post-
    governance stages.

    We model the base handler's effect as being "lifted" into
    the governed event type (GovIOE = GovE +' IOE). The base
    handler produces [itree IOE R]; we translate each IOE event
    into the right summand of GovIOE. *)

(** Lift IOE events into the right summand of GovIOE *)
Definition lift_io {R : Type} (t : itree IOE R) : itree GovIOE R :=
  translate inr1 t.

(** The Gov operator: wraps a base handler with governance.

    This is the central construction. Gov maps base_handler to
    governed_handler. The endofunctor formalization in Functor.v
    defines [Gov_endo : governed_handler -> governed_handler] as
    a genuine endomorphism on a single type, and proves
    [Gov h = Gov_endo (embed_handler h)] (definitional equality).

    Key property: Gov preserves handler equivalence.
    If h1 and h2 are equivalent handlers (pointwise eutt), then
    Gov(h1) and Gov(h2) are equivalent governed handlers. *)
Definition Gov (h : base_handler) : governed_handler :=
  fun R (d : DirectiveE R) =>
    ITree.bind pre_governance (fun ok =>
    if ok then
      ITree.bind (lift_io (h R d)) (fun r =>
      ITree.bind post_governance (fun _ =>
      ret r))
    else
      (* Governance denied: model as divergent computation.
         The safety theorem concerns the case where effects
         ARE performed; denial produces no effects. *)
      ITree.spin).

(** ** Governance Pipeline Composition

    The paper notes that Gov is compositional:
      Gov_1 . Gov_2 produces an interpretation with both
      governance pipelines applied in order.

    We formalize this as iterated application. *)

(** Apply Gov twice: double governance *)
Definition Gov2 (h : base_handler) : governed_handler :=
  fun R (d : DirectiveE R) =>
    ITree.bind pre_governance (fun ok1 =>
    if ok1 then
      ITree.bind pre_governance (fun ok2 =>
      if ok2 then
        ITree.bind (lift_io (h R d)) (fun r =>
        ITree.bind post_governance (fun _ =>
        ITree.bind post_governance (fun _ =>
        ret r)))
      else ITree.spin)
    else ITree.spin).

(** ** Governed Interpretation

    The full governed interpretation applies the Gov operator
    to a base handler, then uses ITrees' [interp] to interpret
    an executor program.

    interp (Gov h) : itree DirectiveE R -> itree GovIOE R

    This is eta_G from Theorem 4.8 in the paper. *)

Definition governed_interp (h : base_handler)
  : forall R, itree DirectiveE R -> itree GovIOE R :=
  fun R t => interp (Gov h) t.

(** ** Ungoverned Interpretation (for comparison)

    The ungoverned interpretation applies the base handler
    directly, without governance stages.

    interp h : itree DirectiveE R -> itree IOE R

    This is eta from Definition 4.5. *)

Definition ungoverned_interp (h : base_handler)
  : forall R, itree DirectiveE R -> itree IOE R :=
  fun R t => interp h t.
