(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file.

   The governance architecture formalized in this development is the
   subject of pending U.S. patent applications by Mashin, Inc. The
   MIT license applies to these proof sources; it does not grant
   rights under any patents. *)

(** * Extraction: OCaml Code Extraction for Governance Kernel

    Extracts the computational content from the Coq formalization
    to OCaml, producing a verified governance kernel that can run
    as an Erlang NIF in the production BEAM runtime.

    What gets extracted:
    - TrustSpec: capability_allowed, trust_at_least, cap_eqb,
      capability_for_directive, is_observability, cap_in_list
    - InterpreterSpec: interp_directive, interp_directives,
      InterpreterState, StepResult, DenialReason
    - EffectAlgebra: CapSet operations (cap_empty, cap_singleton,
      cap_union, cap_full, directive_in_caps)
    - CapabilityComposition: trust_max, trust_min, allowed_cap_set,
      trust_le (as bool via trust_at_least)
    - Directives: DirectiveE, all param records, directive_tag

    What does NOT get extracted (purely propositional):
    - Safety.v: gov_safe (Prop, coinductive)
    - GovernanceAlgebra.v: GovernanceAlgebra record (proof bundle)
    - MonoidalCategory.v: coherence proofs
    - CoterminousBoundary.v: boundary existence proof
    - Category.v, Functor.v, Completeness.v: category axioms

    The extracted code is the governance DECISION engine.
    Theorems proved in Coq guarantee properties of this code:
    - capability_allowed is monotone in trust level
    - interp_directive correctly checks capabilities
    - cap_union is idempotent, commutative, associative

    Dependencies: all prior modules (for consistent extraction) *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.
From MashinGov Require Import TrustSpec.
From MashinGov Require Import InterpreterSpec.
From MashinGov Require Import EffectAlgebra.
From MashinGov Require Import CapabilityComposition.

Require Coq.extraction.Extraction.
Require Coq.extraction.ExtrOcamlBasic.
Require Coq.extraction.ExtrOcamlString.
Require Coq.extraction.ExtrOcamlNatInt.

(* ================================================================= *)
(* Type Mappings                                                      *)
(* ================================================================= *)

(** Map Coq types to efficient OCaml representations.

    - nat -> int (via ExtrOcamlNatInt)
    - bool -> bool (via ExtrOcamlBasic)
    - string -> char list (via ExtrOcamlString)
    - list -> list (native)
    - option -> option (native)
    - unit -> unit (native)

    ExtrOcamlNatInt maps nat operations to OCaml int operations,
    which is sound for the small values we use (trust levels 0-5,
    capability counts < 20). *)

(* ================================================================= *)
(* Extraction Configuration                                           *)
(* ================================================================= *)

(** Inline small helper functions for performance. *)
Extraction Inline cap_eqb.
Extraction Inline cap_in_list.
Extraction Inline is_observability.
Extraction Inline directive_tag.

(** Do NOT inline these; they are the public API. *)

(* ================================================================= *)
(* Phase E1: TrustSpec Pure Functions                                  *)
(* ================================================================= *)

(** These are the primary extraction targets. All are pure functions
    with no Section parameters, no axioms, and no Prop components.
    They compute governance decisions directly. *)

(* ================================================================= *)
(* Phase E2: InterpreterSpec (Functor over Hash)                       *)
(* ================================================================= *)

(** InterpreterSpec.v uses Section variables:
      Variable Hash : Type.
      Variable genesis_hash : Hash.
      Variable compute_hash : string -> Hash -> Hash.

    These extract as an OCaml functor:
      module type HashSig = sig
        type t
        val genesis : t
        val compute : char list -> t -> t
      end

      module MakeInterpreter (H : HashSig) = struct
        type interpreter_state = { ... }
        let interp_directive = ...
      end

    The functor is instantiated with a concrete SHA-256 module
    in hash_sha256.ml (not extracted; hand-written OCaml). *)

(* ================================================================= *)
(* Phase E3: Capability Algebra                                        *)
(* ================================================================= *)

(** CapSet operations from EffectAlgebra.v.
    CapSet = Capability -> bool is a function type in OCaml.
    cap_empty, cap_singleton, cap_union, cap_full are all
    pure functions. *)

(** allowed_cap_set from CapabilityComposition.v.
    Converts trust level + declared caps to a CapSet.
    Pure function, no Section parameters. *)

(* ================================================================= *)
(* Extraction Directives                                               *)
(* ================================================================= *)

(** Extract everything into a single OCaml file.
    The file will contain:
    - Data types (Capability, TrustLevel, DirectiveE, etc.)
    - Pure functions (capability_allowed, trust_at_least, etc.)
    - InterpreterSpec as a functor
    - CapSet operations *)

(** Set the extraction language. *)
Set Extraction AccessOpaque.

(** Extract data types. *)

(* --- Directives data model --- *)
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive option => "option" ["Some" "None"].
Extract Inductive list => "list" ["[]" "(::)"].
Extract Inductive prod => "( * )" ["(,)"].
Extract Inductive unit => "unit" ["()"].
Extract Inductive sumbool => "bool" ["true" "false"].

(* --- Capability and TrustLevel as OCaml variants --- *)

(** We want clean OCaml variant types, not nested matches.
    The default extraction handles Inductive types well. *)

(* ================================================================= *)
(* The Extraction Commands                                             *)
(* ================================================================= *)

(** Separate extraction for each phase, all to the same directory. *)

(** Phase E1: TrustSpec core functions *)
Separate Extraction
  (* Types *)
  Capability
  TrustLevel
  cap_eqb
  cap_eqb_refl

  (* Directive -> Capability mapping *)
  capability_for_directive
  is_observability
  directive_tag

  (* Trust ordering *)
  trust_value
  trust_at_least

  (* Capability check *)
  cap_in_list
  untrusted_caps
  tested_caps
  capability_allowed

  (* InterpreterSpec types and functions *)
  InterpreterState
  DenialReason
  StepResult
  init_state
  interp_directive
  AnyDirective
  interp_any_directive
  interp_directives

  (* CapSet operations *)
  CapSet
  cap_empty
  cap_singleton
  cap_union
  cap_full
  cap_subseteq

  (* CapabilityComposition *)
  trust_le
  trust_max
  trust_min
  allowed_cap_set

  (* Directive data types for completeness *)
  HttpMethod
  FileOperation
  MemoryOperation
  WebSocketOperation
  GovernanceStage
  DirectiveE
  LLMCallParams
  LLMResponse
  HTTPRequestParams
  HTTPResponse
  FileOpParams
  FileResult
  CallMachineParams
  CallMachineResult
  MemoryOpParams
  MemoryResult
  DBOpParams
  DBResult
  ExecOpParams
  ExecResult
  RecordStepParams
  BroadcastParams
  EmitEventParams
  GraphQLRequestParams
  WebSocketOpParams
  WebSocketResult
  MCPCallParams
.
