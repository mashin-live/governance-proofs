(** * LedgerConnection: Connecting Traces to Hash Chains

    Bridges the trace semantics (TraceSemantics.v) with the
    hash chain specification (HashChainSpec.v), establishing
    that execution traces can be recorded as tamper-evident
    hash chains.

    Key results:
    - trace_to_chain: function mapping traces to hash chains
    - trace_chain_valid: well-formed traces produce valid chains
    - trace_chain_tamper: modifying a trace event breaks the chain
    - trace_chain_length: chain length equals trace length
    - governed_trace_chain_valid: governed traces produce valid chains

    This provides the formal foundation for behavioral ledger
    completeness: every governed execution produces a tamper-evident
    record.

    Dependencies: Prelude, Directives, Governance, TraceSemantics,
                  HashChainSpec *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.
From MashinGov Require Import TraceSemantics.

From Coq Require Import List.
Import ListNotations.

(* ================================================================= *)
(* Abstract Parameters (same as HashChainSpec)                        *)
(* ================================================================= *)

(** We use the same abstract parameters as HashChainSpec.v.
    The connection module parameterizes over the hash type,
    hash function, and an encoding from TraceEvents to
    the abstract EventData type. *)

Section LedgerConnection.

  Variable Hash : Type.
  Variable hash_eqb : Hash -> Hash -> bool.
  Hypothesis hash_eqb_eq :
    forall h1 h2, hash_eqb h1 h2 = true <-> h1 = h2.
  Variable genesis_hash : Hash.
  Variable EventData : Type.
  Variable compute_hash : EventData -> Hash -> Hash.
  Hypothesis hash_injective :
    forall d1 d2 p1 p2,
      compute_hash d1 p1 = compute_hash d2 p2 ->
      d1 = d2 /\ p1 = p2.

  (** Encoding function: maps a TraceEvent to the abstract
      EventData type used by the hash chain. In the runtime,
      this corresponds to canonical encoding of step attributes. *)
  Variable encode_event : TraceEvent -> EventData.

  (** The encoding must be injective: distinct trace events
      produce distinct event data. *)
  Hypothesis encode_injective :
    forall e1 e2, encode_event e1 = encode_event e2 -> e1 = e2.

  (** Reuse ChainEvent from HashChainSpec. *)
  Record LedgerEntry := mk_ledger_entry {
    le_event     : TraceEvent;
    le_data      : EventData;
    le_prev_hash : Hash;
    le_hash      : Hash;
  }.

  (** A ledger entry is well-formed if:
      1. Its data is the encoding of its trace event
      2. Its hash is correctly computed *)
  Definition entry_well_formed (e : LedgerEntry) : Prop :=
    le_data e = encode_event (le_event e) /\
    le_hash e = compute_hash (le_data e) (le_prev_hash e).

  (* ================================================================= *)
  (* Trace to Ledger Construction                                       *)
  (* ================================================================= *)

  (** ** trace_to_ledger

      Constructs a list of ledger entries from a trace,
      threading the hash chain through. Each trace event
      becomes a ledger entry with correctly linked hashes. *)

  Fixpoint trace_to_ledger_aux (prev : Hash)
    (trace : list TraceEvent) : list LedgerEntry :=
    match trace with
    | nil => nil
    | e :: rest =>
        let data := encode_event e in
        let new_hash := compute_hash data prev in
        let entry := mk_ledger_entry e data prev new_hash in
        entry :: trace_to_ledger_aux new_hash rest
    end.

  Definition trace_to_ledger (trace : list TraceEvent) : list LedgerEntry :=
    trace_to_ledger_aux genesis_hash trace.

  (* ================================================================= *)
  (* Ledger Validity                                                     *)
  (* ================================================================= *)

  (** A ledger is well-linked if each entry's prev_hash equals
      the previous entry's hash (or genesis for the first),
      and each entry is well-formed.

      Uses cons-based structure matching trace_to_ledger_aux. *)

  Inductive ledger_linked : Hash -> list LedgerEntry -> Prop :=
    | LinkedNil : forall prev,
        ledger_linked prev nil
    | LinkedCons : forall prev e rest,
        entry_well_formed e ->
        le_prev_hash e = prev ->
        ledger_linked (le_hash e) rest ->
        ledger_linked prev (e :: rest).

  Definition ledger_valid (ledger : list LedgerEntry) : Prop :=
    ledger_linked genesis_hash ledger.

  (* ================================================================= *)
  (* Core Theorems                                                       *)
  (* ================================================================= *)

  (** ** Theorem: trace_to_ledger produces valid entries

      Every entry in the constructed ledger is well-formed. *)

  Lemma trace_to_ledger_aux_well_formed :
    forall trace prev e,
      In e (trace_to_ledger_aux prev trace) ->
      entry_well_formed e.
  Proof.
    induction trace as [| ev rest IH]; intros prev e Hin.
    - (* nil: no entries *)
      simpl in Hin. contradiction.
    - (* ev :: rest *)
      simpl in Hin.
      destruct Hin as [Heq | Hin].
      + (* e is the first entry *)
        subst. unfold entry_well_formed. simpl. split; reflexivity.
      + (* e is in the rest *)
        apply IH with (prev := compute_hash (encode_event ev) prev).
        exact Hin.
  Qed.

  (** ** Theorem: ledger preserves trace length *)

  Lemma trace_to_ledger_aux_length :
    forall trace prev,
      length (trace_to_ledger_aux prev trace) = length trace.
  Proof.
    induction trace as [| e rest IH]; intros prev.
    - reflexivity.
    - simpl. f_equal. apply IH.
  Qed.

  Theorem trace_to_ledger_length :
    forall trace,
      length (trace_to_ledger trace) = length trace.
  Proof.
    intros. unfold trace_to_ledger.
    apply trace_to_ledger_aux_length.
  Qed.

  (** ** Theorem: ledger entries recover the original trace *)

  Lemma trace_to_ledger_aux_events :
    forall trace prev,
      map le_event (trace_to_ledger_aux prev trace) = trace.
  Proof.
    induction trace as [| e rest IH]; intros prev.
    - reflexivity.
    - simpl. f_equal. apply IH.
  Qed.

  Theorem trace_to_ledger_events :
    forall trace,
      map le_event (trace_to_ledger trace) = trace.
  Proof.
    intros. unfold trace_to_ledger.
    apply trace_to_ledger_aux_events.
  Qed.

  (** ** Theorem: constructed ledger is valid

      The ledger built from any trace satisfies ledger_valid.
      This is the key soundness result: trace recording always
      produces a valid hash chain. *)

  Lemma trace_to_ledger_aux_linked :
    forall trace prev,
      ledger_linked prev (trace_to_ledger_aux prev trace).
  Proof.
    induction trace as [| ev rest IH]; intros prev.
    - (* nil *)
      simpl. constructor.
    - (* ev :: rest *)
      simpl. apply LinkedCons.
      + (* well-formed *)
        unfold entry_well_formed. simpl. split; reflexivity.
      + (* prev_hash links *)
        simpl. reflexivity.
      + (* rest is linked *)
        simpl. apply IH.
  Qed.

  Theorem trace_to_ledger_valid :
    forall trace, ledger_valid (trace_to_ledger trace).
  Proof.
    intros trace. unfold ledger_valid, trace_to_ledger.
    apply trace_to_ledger_aux_linked.
  Qed.

  (* ================================================================= *)
  (* Tamper Evidence                                                     *)
  (* ================================================================= *)

  (** ** Theorem: modifying a trace event breaks the ledger

      If we have a well-formed ledger entry for some trace event,
      changing the event (while keeping the stored hash) makes
      the entry no longer well-formed. *)

  Theorem ledger_tamper_detected :
    forall (entry : LedgerEntry) (ev' : TraceEvent),
      entry_well_formed entry ->
      ev' <> le_event entry ->
      le_hash entry <> compute_hash (encode_event ev') (le_prev_hash entry).
  Proof.
    intros entry ev' [Hdata Hhash] Hneq.
    intro Habs.
    rewrite Hhash in Habs.
    rewrite Hdata in Habs.
    apply hash_injective in Habs.
    destruct Habs as [Henc _].
    apply encode_injective in Henc.
    symmetry in Henc. contradiction.
  Qed.

  (* ================================================================= *)
  (* Governed Trace Ledger                                               *)
  (* ================================================================= *)

  (** ** Theorem: governed traces produce valid ledgers

      Combining well_governed_trace with trace_to_ledger_valid:
      a well-governed trace always produces a valid ledger. *)

  Theorem governed_trace_ledger_valid :
    forall trace,
      well_governed_trace trace ->
      ledger_valid (trace_to_ledger trace).
  Proof.
    intros trace _.
    apply trace_to_ledger_valid.
  Qed.

  (** ** Theorem: governance events are recorded in the ledger

      Every governance check in the trace appears as a ledger
      entry. Combined with well_governed_trace, this means the
      ledger contains evidence of governance for every I/O event. *)

  Theorem governance_events_recorded :
    forall trace stage decision,
      In (TE_GovCheck stage decision) trace ->
      exists entry,
        In entry (trace_to_ledger trace) /\
        le_event entry = TE_GovCheck stage decision.
  Proof.
    unfold trace_to_ledger.
    intros trace. induction trace as [| e rest IH];
      intros stage decision Hin.
    - contradiction.
    - simpl in Hin. destruct Hin as [Heq | Hin].
      + subst.
        exists (mk_ledger_entry (TE_GovCheck stage decision)
          (encode_event (TE_GovCheck stage decision))
          genesis_hash
          (compute_hash (encode_event (TE_GovCheck stage decision))
            genesis_hash)).
        simpl.
        (* The first entry matches *)
        split.
        * left. reflexivity.
        * reflexivity.
      + (* In the rest *)
        specialize (IH stage decision).
        (* Need to find in trace_to_ledger_aux starting from a
           different hash. Use the map le_event result instead. *)
        assert (Hmap : In (TE_GovCheck stage decision)
          (map le_event (trace_to_ledger_aux
            (compute_hash (encode_event e) genesis_hash) rest))).
        { rewrite trace_to_ledger_aux_events. exact Hin. }
        apply in_map_iff in Hmap.
        destruct Hmap as [entry [Hev Hin2]].
        exists entry. split.
        * right. exact Hin2.
        * exact Hev.
  Qed.

  (* ================================================================= *)
  (* Ledger Completeness                                                 *)
  (* ================================================================= *)

  (** ** Theorem: every trace event is recorded

      The ledger records exactly the trace events, in order,
      with no omissions and no additions. *)

  Theorem ledger_complete :
    forall trace ev,
      In ev trace <->
      exists entry,
        In entry (trace_to_ledger trace) /\
        le_event entry = ev.
  Proof.
    intros trace ev. split.
    - (* -> : event in trace implies entry in ledger *)
      intro Hin.
      assert (Hmap : In ev (map le_event (trace_to_ledger trace))).
      { rewrite trace_to_ledger_events. exact Hin. }
      apply in_map_iff in Hmap.
      destruct Hmap as [entry [Hev Hin2]].
      exists entry. split; [exact Hin2 | exact Hev].
    - (* <- : entry in ledger implies event in trace *)
      intros [entry [Hin Hev]].
      assert (Hmap : In (le_event entry) (map le_event (trace_to_ledger trace))).
      { apply in_map. exact Hin. }
      rewrite trace_to_ledger_events in Hmap.
      rewrite Hev in Hmap. exact Hmap.
  Qed.

End LedgerConnection.

(* ================================================================= *)
(* Summary                                                             *)
(* ================================================================= *)

(** ** Summary

    The LedgerConnection module establishes:

    | Result                           | What It Says                                    |
    |-----------------------------------|-------------------------------------------------|
    | trace_to_ledger                   | Constructs hash-chained ledger from trace       |
    | trace_to_ledger_aux_well_formed   | Every constructed entry is well-formed           |
    | trace_to_ledger_length            | Ledger length equals trace length                |
    | trace_to_ledger_events            | Ledger entries recover the original trace        |
    | trace_to_ledger_valid             | Constructed ledger satisfies ledger_valid        |
    | ledger_tamper_detected            | Modifying a trace event breaks the chain         |
    | governed_trace_ledger_valid       | Governed traces produce valid ledgers            |
    | governance_events_recorded        | Governance checks appear in the ledger           |
    | ledger_complete                   | Ledger records exactly the trace events          |

    Combined with TraceSemantics.v:
    - trace_of_bind: traces compose under monadic bind
    - well_governed_trace: every I/O preceded by governance

    This gives the end-to-end guarantee: governed execution produces
    complete, tamper-evident behavioral records. *)
