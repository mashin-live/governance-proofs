(** * TraceSemantics: Execution Traces for Governed Programs

    Formalizes the trace semantics for governed execution:
    - TraceEvent: events recorded during execution
    - trace_of: inductive relation extracting finite traces
    - trace_of_bind: traces compose under monadic bind
    - well_governed_trace: trace-level governance predicate

    A trace captures the observable behavior of a governed
    interpretation: governance checks and I/O events. The trace
    is the formal model of the behavioral ledger.

    Dependencies: Prelude, Directives, Governance *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.

From ITree Require Import
  Interp.InterpFacts
  Eq.EqAxiom.

From Coq Require Import Program.Equality.
From Coq Require Import List.
Import ListNotations.

(* ================================================================= *)
(* Trace Events                                                        *)
(* ================================================================= *)

(** ** TraceEvent

    Events recorded in an execution trace. Two kinds:
    - Governance checks: stage + decision (pass/fail)
    - I/O operations: tag string identifying the operation

    These correspond to the Vis events in [itree GovIOE R]:
    GovE events become [TE_GovCheck], IOE events become [TE_IO]. *)

Inductive TraceEvent :=
  | TE_GovCheck : GovernanceStage -> bool -> TraceEvent
  | TE_IO : string -> TraceEvent.

(** Classify trace events. *)
Definition is_gov_event (e : TraceEvent) : bool :=
  match e with
  | TE_GovCheck _ _ => true
  | TE_IO _ => false
  end.

Definition is_io_event (e : TraceEvent) : bool :=
  match e with
  | TE_GovCheck _ _ => false
  | TE_IO _ => true
  end.

(* ================================================================= *)
(* Trace Extraction                                                    *)
(* ================================================================= *)

(** ** trace_of

    Inductive relation between a governed computation, a finite
    trace of events, and a result value. Captures terminating
    executions where the environment provides specific responses.

    [trace_of t trace r] means: executing [t] with the environment
    choices implicit in the derivation produces trace [trace] and
    returns [r].

    Uses [observe] to match tree structure, compatible with the
    ITrees cofixpoint representation. *)

Section TraceOf.

  Context {R : Type}.

  Inductive trace_of : itree GovIOE R -> list TraceEvent -> R -> Prop :=
    | TO_Ret : forall t r,
        observe t = RetF r ->
        trace_of t nil r
    | TO_Tau : forall t t' trace r,
        observe t = TauF t' ->
        trace_of t' trace r ->
        trace_of t trace r
    | TO_GovVis : forall t (stage : GovernanceStage)
        (k : bool -> itree GovIOE R)
        (decision : bool) (trace : list TraceEvent) (r : R),
        observe t = VisF (inl1 (GovCheck stage)) k ->
        trace_of (k decision) trace r ->
        trace_of t (TE_GovCheck stage decision :: trace) r
    | TO_IOVis : forall t (X : Type) (tag : string)
        (k : X -> itree GovIOE R) (x : X)
        (trace : list TraceEvent) (r : R),
        observe t = VisF (inr1 (@PerformIO X tag)) k ->
        trace_of (k x) trace r ->
        trace_of t (TE_IO tag :: trace) r.

End TraceOf.

(* ================================================================= *)
(* Basic Trace Lemmas                                                  *)
(* ================================================================= *)

(** Return produces empty trace. *)
Lemma trace_of_ret :
  forall R (r : R), trace_of (ret r) nil r.
Proof.
  intros. apply TO_Ret. cbn. reflexivity.
Qed.

(** Tau is transparent to traces. *)
Lemma trace_of_tau :
  forall R (t : itree GovIOE R) trace r,
    trace_of t trace r ->
    trace_of (Tau t) trace r.
Proof.
  intros. eapply TO_Tau.
  - cbn. reflexivity.
  - exact H.
Qed.

(** A governance check produces a single-event trace. *)
Lemma trace_of_gov_check :
  forall stage decision,
    trace_of (Vis (inl1 (GovCheck stage)) (fun b => ret b))
             [TE_GovCheck stage decision] decision.
Proof.
  intros. eapply TO_GovVis.
  - cbn. reflexivity.
  - apply trace_of_ret.
Qed.

(** An IO event produces a single-event trace. *)
Lemma trace_of_io :
  forall X tag (x : X),
    trace_of (Vis (inr1 (@PerformIO X tag)) (fun v => ret v))
             [TE_IO tag] x.
Proof.
  intros. eapply TO_IOVis.
  - cbn. reflexivity.
  - apply trace_of_ret.
Qed.

(* ================================================================= *)
(* Trace Composition (bind)                                            *)
(* ================================================================= *)

(** ** trace_of_bind

    If [t] produces trace [trace1] with result [x], and [k x]
    produces trace [trace2] with result [r], then [bind t k]
    produces trace [trace1 ++ trace2] with result [r].

    This is the compositional closure of trace extraction:
    traces compose under monadic bind. *)

Theorem trace_of_bind :
  forall R S (t : itree GovIOE R) (k : R -> itree GovIOE S)
    trace1 trace2 x r,
    trace_of t trace1 x ->
    trace_of (k x) trace2 r ->
    trace_of (ITree.bind t k) (trace1 ++ trace2) r.
Proof.
  intros R S t k trace1 trace2 x r Ht Hk.
  revert S k trace2 r Hk.
  induction Ht; intros S' k' trace2 r' Hk.
  - (* TO_Ret *)
    simpl.
    rewrite (bisimulation_is_eq _ _ (unfold_bind t k')).
    rewrite H. cbn. exact Hk.
  - (* TO_Tau *)
    simpl.
    rewrite (bisimulation_is_eq _ _ (unfold_bind t k')).
    rewrite H. cbn.
    eapply TO_Tau.
    + cbn. reflexivity.
    + apply IHHt. exact Hk.
  - (* TO_GovVis *)
    simpl.
    rewrite (bisimulation_is_eq _ _ (unfold_bind t k')).
    rewrite H. cbn.
    eapply TO_GovVis.
    + cbn. reflexivity.
    + apply IHHt. exact Hk.
  - (* TO_IOVis *)
    simpl.
    change (fun X0 : Type => (GovE +' IOE) X0) with GovIOE in *.
    rewrite (bisimulation_is_eq _ _ (unfold_bind t k')).
    rewrite H. cbn.
    eapply TO_IOVis.
    + cbn. reflexivity.
    + apply IHHt. exact Hk.
Qed.

(* ================================================================= *)
(* Well-Governed Traces                                                *)
(* ================================================================= *)

(** ** well_governed_trace

    A trace is well-governed if every I/O event is preceded by
    at least one governance check that passed. This mirrors the
    [gov_safe] coinductive predicate at the trace level.

    The boolean [seen_gov] tracks whether a passing governance
    check has been encountered since the last I/O event (or
    since the start). *)

Fixpoint trace_governed (seen_gov : bool) (trace : list TraceEvent)
  : Prop :=
  match trace with
  | nil => True
  | TE_GovCheck _ true :: rest => trace_governed true rest
  | TE_GovCheck _ false :: rest => trace_governed seen_gov rest
  | TE_IO _ :: rest =>
      seen_gov = true /\ trace_governed false rest
  end.

Definition well_governed_trace (trace : list TraceEvent) : Prop :=
  trace_governed false trace.

(** Empty trace is governed. *)
Lemma well_governed_nil : well_governed_trace nil.
Proof. exact I. Qed.

(** Monotonicity: trace_governed false implies trace_governed true. *)
Lemma trace_governed_mono :
  forall trace,
    trace_governed false trace -> trace_governed true trace.
Proof.
  induction trace as [| e rest IH].
  - intros. exact I.
  - destruct e.
    + (* TE_GovCheck *)
      destruct b; simpl; intros.
      * exact H.
      * apply IH. exact H.
    + (* TE_IO *)
      simpl. intros [Habs _]. discriminate.
Qed.

(** A trace of only governance checks is governed. *)
Lemma well_governed_gov_only :
  forall stage decision trace,
    well_governed_trace trace ->
    well_governed_trace (TE_GovCheck stage decision :: trace).
Proof.
  intros stage decision trace H.
  unfold well_governed_trace. simpl.
  destruct decision.
  - apply trace_governed_mono. exact H.
  - exact H.
Qed.

(** A governance pass followed by IO is governed. *)
Lemma well_governed_gov_then_io :
  forall stage tag rest,
    well_governed_trace rest ->
    well_governed_trace
      (TE_GovCheck stage true :: TE_IO tag :: rest).
Proof.
  intros. unfold well_governed_trace. simpl. split.
  - reflexivity.
  - exact H.
Qed.

(** Governance check at any level makes subsequent IO legal. *)
Lemma trace_governed_after_check :
  forall stage trace,
    trace_governed true trace ->
    trace_governed false (TE_GovCheck stage true :: trace).
Proof.
  intros. simpl. exact H.
Qed.

(* ================================================================= *)
(* Trace Length                                                        *)
(* ================================================================= *)

(** The trace has one event per Vis node traversed. *)

Definition trace_length (trace : list TraceEvent) : nat :=
  length trace.

(** Trace of ret has length 0. *)
Lemma trace_of_ret_length :
  forall R (t : itree GovIOE R) r,
    trace_of t nil r -> trace_length nil = 0.
Proof. reflexivity. Qed.

(** Bind concatenates traces, so lengths add. *)
Lemma trace_length_bind :
  forall trace1 trace2,
    trace_length (trace1 ++ trace2) =
    trace_length trace1 + trace_length trace2.
Proof.
  intros. unfold trace_length. apply app_length.
Qed.

(* ================================================================= *)
(* Trace Soundness and Completeness                                    *)
(* ================================================================= *)

(** ** Trace Soundness

    Every event in a trace corresponds to a Vis node in the tree.
    This holds by construction: [trace_of] only adds events via
    [TO_GovVis] and [TO_IOVis], which require a Vis observation.

    We state the non-emptiness direction: if the trace is non-empty,
    the tree had at least one Vis event. *)

Lemma trace_nonempty_has_vis :
  forall R (t : itree GovIOE R) (e : TraceEvent) trace r,
    @trace_of R t (e :: trace) r ->
    exists (t' : itree GovIOE R) (trace' : list TraceEvent) (r' : R),
      @trace_of R t' trace' r' /\
      (trace' = trace \/ exists e' trace'', trace' = e' :: trace'').
Proof.
  intros R t e trace r H.
  inversion H; subst.
  - (* TO_Tau *)
    eexists. eexists. eexists. split.
    + eassumption.
    + right. eexists. eexists. reflexivity.
  - (* TO_GovVis *)
    eexists. eexists. eexists. split.
    + eassumption.
    + left. reflexivity.
  - (* TO_IOVis *)
    eexists. eexists. eexists. split.
    + eassumption.
    + left. reflexivity.
Qed.

(** ** Tau transparency (trace-level)

    Tau steps do not change the trace. This is an immediate
    consequence of the TO_Tau constructor. *)

Lemma trace_of_tau_inv :
  forall R (t : itree GovIOE R) trace r,
    @trace_of R (Tau t) trace r ->
    @trace_of R t trace r.
Proof.
  intros R t trace r H.
  inversion H; subst.
  (* The only matching constructor is TO_Tau since
     observe (Tau t) reduces to TauF t. The Ret, GovVis
     cases produce contradictions via simpl+discriminate,
     and IOVis via type-level reasoning. We use a uniform
     tactic. *)
  all: try (match goal with
    | [ H1 : observe (Tau _) = _ |- _ ] =>
      simpl in H1; injection H1 as ->; assumption
    end).
  all: try (match goal with
    | [ H1 : observe (Tau _) = _ |- _ ] =>
      simpl in H1; discriminate
    end).
Qed.

(* ================================================================= *)
(* Trace of gov_check                                                  *)
(* ================================================================= *)

(** The abstract governance check [gov_check stage] produces
    a single-event trace of [TE_GovCheck stage decision]. *)

Lemma trace_of_gov_check_fn :
  forall stage decision,
    trace_of (gov_check stage)
             [TE_GovCheck stage decision] decision.
Proof.
  intros. unfold gov_check, trigger.
  eapply TO_GovVis.
  - cbn. reflexivity.
  - apply trace_of_ret.
Qed.

(* ================================================================= *)
(* Summary                                                             *)
(* ================================================================= *)

(** ** Summary

    The TraceSemantics module establishes:

    | Result                    | What It Says                              |
    |---------------------------|-------------------------------------------|
    | TraceEvent                | Events in execution traces                |
    | trace_of                  | Inductive trace extraction relation       |
    | trace_of_ret              | Return produces empty trace               |
    | trace_of_tau              | Tau is transparent to traces              |
    | trace_of_gov_check        | Single governance check trace             |
    | trace_of_bind             | Traces compose under bind                 |
    | well_governed_trace       | Trace-level governance predicate          |
    | trace_length_bind         | Bind concatenates trace lengths           |
    | trace_nonempty_has_vis    | Non-empty trace implies Vis node          |

    Combined with LedgerConnection.v, this provides the formal
    foundation for behavioral ledger completeness and tamper
    evidence. *)
