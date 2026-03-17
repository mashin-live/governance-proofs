(** C-callable stubs for the governance kernel.

    These functions register OCaml callbacks that the C NIF wrapper
    can invoke via caml_callback. Each function converts between
    simple C-compatible types and the Coq-extracted governance types.

    Protocol: all arguments and results use integers and arrays.
    Trust levels are ints 0-5, capabilities are ints 0-7,
    booleans are ints 0/1. *)

open Governance_kernel

(* --- Trust level encoding --- *)

let trust_of_int = function
  | 0 -> Untrusted | 1 -> Tested | 2 -> Evaluated
  | 3 -> Reviewed  | 4 -> Stdlib  | 5 -> System
  | _ -> Untrusted

let int_of_trust = function
  | Untrusted -> 0 | Tested -> 1 | Evaluated -> 2
  | Reviewed -> 3  | Stdlib -> 4  | System -> 5

(* --- Capability encoding --- *)

let cap_of_int = function
  | 0 -> CapComputeLLMReason | 1 -> CapNetHTTP | 2 -> CapFS
  | 3 -> CapDB              | 4 -> CapMemory  | 5 -> CapMachineCall
  | 6 -> CapComputeExec     | 7 -> CapNetWebSocket
  | _ -> CapComputeLLMReason

let int_of_cap = function
  | CapComputeLLMReason -> 0 | CapNetHTTP -> 1 | CapFS -> 2
  | CapDB -> 3              | CapMemory -> 4  | CapMachineCall -> 5
  | CapComputeExec -> 6     | CapNetWebSocket -> 7

(* --- Exported callbacks --- *)

(** capability_allowed(trust_int, cap_int, declared_array) -> 0|1 *)
let capability_allowed_cb trust_int cap_int declared_ints =
  let trust = trust_of_int trust_int in
  let cap = cap_of_int cap_int in
  let declared = List.map cap_of_int declared_ints in
  if capability_allowed ~trust ~cap ~declared then 1 else 0

(** capability_for_directive(tag_string) -> cap_int | -1 *)
let capability_for_directive_cb tag =
  match capability_for_directive_tag tag with
  | Some cap -> int_of_cap cap
  | None -> -1

(** trust_at_least(has_int, requires_int) -> 0|1 *)
let trust_at_least_cb has_int requires_int =
  let has = trust_of_int has_int in
  let requires = trust_of_int requires_int in
  if trust_at_least ~has ~requires then 1 else 0

(** trust_value(trust_int) -> int *)
let trust_value_cb trust_int =
  trust_value (trust_of_int trust_int)

(** interp_directive(tag_string, trust_int, declared_array, prev_hash_string)
    -> (0, new_hash) | (1, cap_int, trust_int) | (2, -1, -1) *)
let interp_directive_cb tag trust_int declared_ints prev_hash =
  let module I = Interpreter in
  let trust = trust_of_int trust_int in
  let declared = List.map cap_of_int declared_ints in
  let st = I.init_state prev_hash trust declared in
  let st = { st with prev_hash } in
  match I.interp_directive tag st with
  | I.StepOk (hash, _st') -> (0, hash, -1, -1)
  | I.StepDenied (I.CapabilityDenied (cap, tl)) ->
    (1, "", int_of_cap cap, int_of_trust tl)
  | I.StepDenied I.DirectiveNotImplemented ->
    (2, "", -1, -1)

(* --- Register callbacks for C access --- *)
let () =
  Callback.register "mashin_capability_allowed" capability_allowed_cb;
  Callback.register "mashin_capability_for_directive" capability_for_directive_cb;
  Callback.register "mashin_trust_at_least" trust_at_least_cb;
  Callback.register "mashin_trust_value" trust_value_cb;
  Callback.register "mashin_interp_directive" interp_directive_cb
