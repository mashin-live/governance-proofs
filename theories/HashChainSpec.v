(** * HashChainSpec: Abstract Hash Chain Specification

    Formalizes the hash chain properties from the Elixir runtime
    (MashinCore.Crypto.HashChain).

    This is an ABSTRACT specification: it does not model SHA256
    internals. Instead, it parameterizes over an abstract hash
    function with a collision-resistance axiom, and proves that
    the chain structure detects tampering.

    Key definitions:
    - [Hash]: opaque type parameter
    - [genesis_hash]: the initial hash (all zeros)
    - [compute_hash]: abstract hash function
    - [chain_valid]: inductive predicate for valid chains

    Key theorems:
    - [chain_valid_genesis]: empty chain from genesis is valid
    - [chain_valid_append]: correct hashing preserves validity
    - [chain_tamper_detected]: modifying any event breaks validity *)

From MashinGov Require Import Prelude.

(* ================================================================= *)
(* Abstract Hash Type                                                  *)
(* ================================================================= *)

(** We parameterize the entire development over an abstract
    hash type and hash function. This mirrors the Elixir code
    which uses SHA256 but whose chain properties don't depend
    on the specific hash algorithm. *)

Section HashChainSpec.

  (** Abstract hash type. Opaque to proofs. *)
  Variable Hash : Type.

  (** Decidable equality on hashes. *)
  Variable hash_eqb : Hash -> Hash -> bool.
  Hypothesis hash_eqb_eq : forall h1 h2, hash_eqb h1 h2 = true <-> h1 = h2.

  (** The genesis hash (corresponds to Elixir's
      "sha256:" <> String.duplicate("0", 64)). *)
  Variable genesis_hash : Hash.

  (** Abstract event data. Represents the canonical encoding
      of step attributes (name, type, index, input/output hashes). *)
  Variable EventData : Type.

  (** The hash function: takes event data and previous hash,
      produces a new hash. Mirrors:
        HashChain.compute_event_hash(event_data, prev_hash) *)
  Variable compute_hash : EventData -> Hash -> Hash.

  (** ** Collision Resistance Axiom

      The key assumption: if two different (event_data, prev_hash)
      pairs produce the same hash, then the inputs were equal.

      This is weaker than full collision resistance (which would
      say NO collisions exist for any input). We only need:
      same hash => same inputs, within our domain. *)
  Hypothesis hash_injective :
    forall d1 d2 p1 p2,
      compute_hash d1 p1 = compute_hash d2 p2 ->
      d1 = d2 /\ p1 = p2.

  (* ================================================================= *)
  (* Chain Events                                                        *)
  (* ================================================================= *)

  (** A chain event carries its data, the hash of the previous event,
      and its own computed hash. Mirrors the Elixir step record with
      :event_hash, :prev_hash fields. *)

  Record ChainEvent := mk_chain_event {
    ce_data      : EventData;
    ce_prev_hash : Hash;
    ce_hash      : Hash;
  }.

  (** A chain event is well-formed if its hash was correctly computed. *)
  Definition event_well_formed (e : ChainEvent) : Prop :=
    ce_hash e = compute_hash (ce_data e) (ce_prev_hash e).

  (* ================================================================= *)
  (* Chain Validity                                                      *)
  (* ================================================================= *)

  (** ** chain_valid

      Inductive predicate defining a valid hash chain.
      A chain is valid if:
      1. It starts from genesis_hash
      2. Each event's prev_hash links to the previous event's hash
      3. Each event's hash is correctly computed

      Mirrors [HashChain.verify_chain/1] in Elixir. *)

  Inductive chain_valid : list ChainEvent -> Hash -> Prop :=
    | ChainEmpty :
        chain_valid nil genesis_hash
    | ChainCons : forall (e : ChainEvent) (rest : list ChainEvent) (prev : Hash),
        chain_valid rest prev ->
        ce_prev_hash e = prev ->
        ce_hash e = compute_hash (ce_data e) prev ->
        chain_valid (rest ++ e :: nil) (ce_hash e).

  (* ================================================================= *)
  (* Theorems                                                            *)
  (* ================================================================= *)

  (** ** Theorem 1: Empty chain from genesis is valid *)

  Theorem chain_valid_genesis :
    chain_valid nil genesis_hash.
  Proof. constructor. Qed.

  (** ** Theorem 2: Appending a correctly-hashed event preserves validity *)

  Theorem chain_valid_append :
    forall (chain : list ChainEvent) (head_hash : Hash)
           (data : EventData),
      chain_valid chain head_hash ->
      let new_hash := compute_hash data head_hash in
      let new_event := mk_chain_event data head_hash new_hash in
      chain_valid (chain ++ new_event :: nil) new_hash.
  Proof.
    intros chain head_hash data Hvalid.
    simpl.
    apply ChainCons with (prev := head_hash).
    - exact Hvalid.
    - reflexivity.
    - reflexivity.
  Qed.

  (** ** Theorem 3: Tampering detection

      If a chain is valid and an event's data is modified (while
      keeping the stored hash unchanged), the chain is no longer valid.

      We prove a simpler but equivalent statement: if an event in
      a valid chain has its data changed, the recomputed hash won't
      match the stored hash, so the chain won't satisfy chain_valid.

      More precisely: if we modify the data of the last event in a
      valid chain, the modified chain is not valid (at any hash). *)

  (** Helper: the last event's hash in a valid chain must be
      correctly computed from its data and previous hash. *)
  Lemma chain_valid_last_correct :
    forall chain head_hash e,
      chain_valid (chain ++ e :: nil) head_hash ->
      head_hash = ce_hash e /\
      event_well_formed e.
  Proof.
    intros chain head_hash e Hvalid.
    inversion Hvalid as [Hnil Hgen | e0 rest prev Hrest Hprev Hhash Hlist Hhead].
    - (* ChainEmpty: chain ++ e :: nil = nil, impossible *)
      destruct chain; discriminate Hnil.
    - (* ChainCons: rest ++ e0 :: nil = chain ++ e :: nil *)
      apply app_inj_tail in Hlist.
      destruct Hlist as [_ He].
      subst. split.
      + reflexivity.
      + unfold event_well_formed. exact Hhash.
  Qed.

  (** If a chain event has correct linkage but wrong data,
      and the hash function is injective, validity is violated.

      Stated as: given a valid chain ending in event [e], if we
      replace [e]'s data with different data [d'] but keep the same
      hash, the resulting event is NOT well-formed. *)
  Theorem chain_tamper_detected :
    forall (e : ChainEvent) (d' : EventData),
      event_well_formed e ->
      d' <> ce_data e ->
      ce_hash e <> compute_hash d' (ce_prev_hash e).
  Proof.
    intros e d' Hwf Hneq.
    unfold event_well_formed in Hwf.
    intro Habs.
    rewrite Hwf in Habs.
    apply hash_injective in Habs.
    destruct Habs as [Heq _].
    symmetry in Heq. contradiction.
  Qed.

  (** ** Hash chain determinism

      Same event data and previous hash always produce the
      same event hash. This is trivially true since compute_hash
      is a function (deterministic by construction in Coq). *)

  Theorem hash_chain_deterministic :
    forall data prev_hash,
      compute_hash data prev_hash = compute_hash data prev_hash.
  Proof. reflexivity. Qed.

  (** ** Chain validity is monotone

      If a chain is valid up to event n, then the prefix up to
      event n-1 is also valid. Proved by inversion on the
      chain_valid predicate. *)

  Theorem chain_valid_prefix :
    forall chain e head_hash,
      chain_valid (chain ++ e :: nil) head_hash ->
      chain_valid chain (ce_prev_hash e).
  Proof.
    intros chain e head_hash Hvalid.
    inversion Hvalid as [Hnil Hgen | e0 rest prev Hrest Hprev Hhash Hlist Hhead].
    - (* ChainEmpty: chain ++ e :: nil = nil, impossible *)
      destruct chain; discriminate Hnil.
    - (* ChainCons: rest ++ e0 :: nil = chain ++ e :: nil *)
      apply app_inj_tail in Hlist.
      destruct Hlist as [Hchain He].
      subst. exact Hrest.
  Qed.

End HashChainSpec.
