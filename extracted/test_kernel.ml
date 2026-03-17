(** Unit tests for the governance kernel.

    These tests verify that the Coq-extracted governance functions
    produce correct results when called through the OCaml wrapper.
    Each test compares against known-good values derived from
    Coq's Compute command. *)

open Governance_kernel

let passed = ref 0
let failed = ref 0

let assert_eq name expected actual =
  if expected = actual then (
    incr passed;
    Printf.printf "  PASS: %s\n" name
  ) else (
    incr failed;
    Printf.printf "  FAIL: %s (expected %s, got %s)\n" name expected actual
  )

let assert_bool name expected actual =
  assert_eq name (string_of_bool expected) (string_of_bool actual)

let assert_int name expected actual =
  assert_eq name (string_of_int expected) (string_of_int actual)

(* --- Trust value tests --- *)

let test_trust_values () =
  Printf.printf "\n== Trust Values ==\n";
  assert_int "untrusted=0" 0 (trust_value Untrusted);
  assert_int "tested=1" 1 (trust_value Tested);
  assert_int "evaluated=2" 2 (trust_value Evaluated);
  assert_int "reviewed=3" 3 (trust_value Reviewed);
  assert_int "stdlib=4" 4 (trust_value Stdlib);
  assert_int "system=5" 5 (trust_value System)

(* --- Trust ordering tests --- *)

let test_trust_ordering () =
  Printf.printf "\n== Trust Ordering ==\n";
  assert_bool "system >= untrusted" true (trust_at_least ~has:System ~requires:Untrusted);
  assert_bool "system >= system" true (trust_at_least ~has:System ~requires:System);
  assert_bool "untrusted >= system" false (trust_at_least ~has:Untrusted ~requires:System);
  assert_bool "tested >= untrusted" true (trust_at_least ~has:Tested ~requires:Untrusted);
  assert_bool "untrusted >= tested" false (trust_at_least ~has:Untrusted ~requires:Tested);
  assert_bool "reviewed >= evaluated" true (trust_at_least ~has:Reviewed ~requires:Evaluated);
  assert_bool "evaluated >= reviewed" false (trust_at_least ~has:Evaluated ~requires:Reviewed)

(* --- Trust lattice tests --- *)

let test_trust_lattice () =
  Printf.printf "\n== Trust Lattice ==\n";
  assert_eq "max(untrusted, system)" "system"
    (string_of_trust_level (trust_max Untrusted System));
  assert_eq "min(untrusted, system)" "untrusted"
    (string_of_trust_level (trust_min Untrusted System));
  assert_eq "max(tested, reviewed)" "reviewed"
    (string_of_trust_level (trust_max Tested Reviewed));
  assert_eq "min(tested, reviewed)" "tested"
    (string_of_trust_level (trust_min Tested Reviewed));
  assert_eq "max(stdlib, stdlib)" "stdlib"
    (string_of_trust_level (trust_max Stdlib Stdlib))

(* --- Capability allowed tests --- *)

let test_capability_allowed () =
  Printf.printf "\n== Capability Allowed ==\n";
  (* Untrusted: only CapComputeLLMReason allowed *)
  assert_bool "untrusted+llm" true
    (capability_allowed ~trust:Untrusted ~cap:CapComputeLLMReason ~declared:[]);
  assert_bool "untrusted+http" false
    (capability_allowed ~trust:Untrusted ~cap:CapNetHTTP ~declared:[]);
  assert_bool "untrusted+fs" false
    (capability_allowed ~trust:Untrusted ~cap:CapFS ~declared:[]);
  assert_bool "untrusted+db" false
    (capability_allowed ~trust:Untrusted ~cap:CapDB ~declared:[]);
  assert_bool "untrusted+exec" false
    (capability_allowed ~trust:Untrusted ~cap:CapComputeExec ~declared:[]);

  (* Tested: LLM, Exec, Memory, MachineCall *)
  assert_bool "tested+llm" true
    (capability_allowed ~trust:Tested ~cap:CapComputeLLMReason ~declared:[]);
  assert_bool "tested+exec" true
    (capability_allowed ~trust:Tested ~cap:CapComputeExec ~declared:[]);
  assert_bool "tested+memory" true
    (capability_allowed ~trust:Tested ~cap:CapMemory ~declared:[]);
  assert_bool "tested+machine_call" true
    (capability_allowed ~trust:Tested ~cap:CapMachineCall ~declared:[]);
  assert_bool "tested+http" false
    (capability_allowed ~trust:Tested ~cap:CapNetHTTP ~declared:[]);
  assert_bool "tested+fs" false
    (capability_allowed ~trust:Tested ~cap:CapFS ~declared:[]);

  (* Evaluated/Reviewed: uses declared caps *)
  assert_bool "evaluated+http+declared" true
    (capability_allowed ~trust:Evaluated ~cap:CapNetHTTP
       ~declared:[CapNetHTTP; CapFS]);
  assert_bool "evaluated+db+not_declared" false
    (capability_allowed ~trust:Evaluated ~cap:CapDB
       ~declared:[CapNetHTTP; CapFS]);

  (* Stdlib/System: all allowed *)
  assert_bool "stdlib+http" true
    (capability_allowed ~trust:Stdlib ~cap:CapNetHTTP ~declared:[]);
  assert_bool "stdlib+db" true
    (capability_allowed ~trust:Stdlib ~cap:CapDB ~declared:[]);
  assert_bool "system+ws" true
    (capability_allowed ~trust:System ~cap:CapNetWebSocket ~declared:[])

(* --- Capability for directive tests --- *)

let test_capability_for_directive () =
  Printf.printf "\n== Capability for Directive ==\n";
  let check name tag expected =
    let result = capability_for_directive_tag tag in
    let actual = match result with
      | Some c -> string_of_capability c
      | None -> "none"
    in
    assert_eq name expected actual
  in
  check "llm_call" "llm_call" "compute.llm_reason";
  check "llm_call_stream" "llm_call_stream" "compute.llm_reason";
  check "http_request" "http_request" "net.http";
  check "file_op" "file_op" "fs";
  check "call_machine" "call_machine" "machine.call";
  check "memory_op" "memory_op" "memory";
  check "db_op" "db_op" "db";
  check "exec_command" "exec_command" "compute.exec";
  check "graphql_request" "graphql_request" "net.http";
  check "websocket_op" "websocket_op" "net.websocket";
  check "mcp_call" "mcp_call" "machine.call";
  (* Observability directives: no capability required *)
  check "record_step" "record_step" "none";
  check "broadcast" "broadcast" "none";
  check "emit_event" "emit_event" "none"

(* --- Interpreter tests --- *)

let test_interpreter () =
  Printf.printf "\n== Interpreter ==\n";
  let open Interpreter in

  (* Test 1: Allowed directive produces StepOk with new hash *)
  let st = init_state "genesis" Untrusted [] in
  (match interp_directive "llm_call" st with
   | StepOk (h, st') ->
     assert_bool "llm_call ok" true true;
     assert_bool "hash changed" true (h <> "genesis");
     assert_eq "trust preserved" "untrusted"
       (string_of_trust_level st'.trust_level)
   | StepDenied _ ->
     assert_bool "llm_call should not be denied for untrusted" true false);

  (* Test 2: Denied directive produces StepDenied *)
  let st = init_state "genesis" Untrusted [] in
  (match interp_directive "http_request" st with
   | StepOk _ ->
     assert_bool "http should be denied for untrusted" true false
   | StepDenied (CapabilityDenied (cap, _tl)) ->
     assert_eq "denied cap" "net.http" (string_of_capability cap)
   | StepDenied DirectiveNotImplemented ->
     assert_bool "http should be cap denied not unimplemented" true false);

  (* Test 3: Observability directives always succeed without changing hash *)
  let st = init_state "genesis" Untrusted [] in
  (match interp_directive "record_step" st with
   | StepOk (h, _) ->
     assert_eq "record_step no hash change" "genesis" h
   | StepDenied _ ->
     assert_bool "record_step should always succeed" true false);

  (* Test 4: Sequence of directives *)
  let st = init_state "genesis" Tested [] in
  (match interp_directives ["llm_call"; "exec_command"; "memory_op"] st with
   | StepOk (h, _) ->
     assert_bool "3-directive sequence ok" true true;
     assert_bool "final hash differs from genesis" true (h <> "genesis")
   | StepDenied _ ->
     assert_bool "tested should allow llm+exec+memory" true false);

  (* Test 5: Sequence fails at first denied directive *)
  let st = init_state "genesis" Untrusted [] in
  (match interp_directives ["llm_call"; "http_request"; "llm_call"] st with
   | StepOk _ ->
     assert_bool "untrusted should deny http_request in sequence" true false
   | StepDenied (CapabilityDenied (cap, _)) ->
     assert_eq "sequence denied at http" "net.http" (string_of_capability cap)
   | StepDenied DirectiveNotImplemented ->
     assert_bool "should be cap denied" true false);

  (* Test 6: Hash chain determinism *)
  let st1 = init_state "genesis" Stdlib [CapNetHTTP] in
  let st2 = init_state "genesis" Stdlib [CapNetHTTP] in
  let r1 = interp_directive "http_request" st1 in
  let r2 = interp_directive "http_request" st2 in
  (match (r1, r2) with
   | StepOk (h1, _), StepOk (h2, _) ->
     assert_eq "deterministic hash" h1 h2
   | _ ->
     assert_bool "both should succeed" true false);

  (* Test 7: Unknown directive tag *)
  let st = init_state "genesis" System [] in
  (match interp_directive "nonexistent_directive" st with
   | StepDenied DirectiveNotImplemented ->
     assert_bool "unknown tag denied" true true
   | _ ->
     assert_bool "unknown tag should be denied" true false)

(* --- CapSet tests --- *)

let test_cap_set () =
  Printf.printf "\n== CapSet Operations ==\n";
  assert_bool "empty rejects all" false (cap_empty CapNetHTTP);
  assert_bool "full accepts all" true (cap_full CapNetHTTP);
  assert_bool "singleton accepts match" true (cap_singleton CapFS CapFS);
  assert_bool "singleton rejects non-match" false (cap_singleton CapFS CapDB);

  let s = cap_union (cap_singleton CapFS) (cap_singleton CapDB) in
  assert_bool "union accepts fs" true (s CapFS);
  assert_bool "union accepts db" true (s CapDB);
  assert_bool "union rejects http" false (s CapNetHTTP);

  (* allowed_cap_set for stdlib should accept everything *)
  let stdlib_set = allowed_cap_set ~trust:Stdlib ~declared:[] in
  assert_bool "stdlib allows http" true (stdlib_set CapNetHTTP);
  assert_bool "stdlib allows fs" true (stdlib_set CapFS);

  (* allowed_cap_set for untrusted should only accept LLM *)
  let untrusted_set = allowed_cap_set ~trust:Untrusted ~declared:[] in
  assert_bool "untrusted allows llm" true (untrusted_set CapComputeLLMReason);
  assert_bool "untrusted denies http" false (untrusted_set CapNetHTTP)

(* --- Exhaustive capability x trust level matrix --- *)

let test_exhaustive_matrix () =
  Printf.printf "\n== Exhaustive Trust x Capability Matrix ==\n";
  let trust_levels = [Untrusted; Tested; Evaluated; Reviewed; Stdlib; System] in
  let caps = all_capabilities in
  (* Expected results from Coq Compute:
     Untrusted: only LLM
     Tested: LLM, Exec, Memory, MachineCall
     Evaluated/Reviewed: uses declared (empty here = nothing)
     Stdlib/System: everything *)
  let expected tl cap =
    match tl with
    | Untrusted ->
      (match cap with CapComputeLLMReason -> true | _ -> false)
    | Tested ->
      (match cap with
       | CapComputeLLMReason | CapComputeExec | CapMemory | CapMachineCall -> true
       | _ -> false)
    | Evaluated | Reviewed ->
      false (* empty declared list *)
    | Stdlib | System -> true
  in
  List.iter (fun tl ->
    List.iter (fun cap ->
      let name = Printf.sprintf "%s+%s"
        (string_of_trust_level tl) (string_of_capability cap) in
      let exp = expected tl cap in
      let actual = capability_allowed ~trust:tl ~cap ~declared:[] in
      assert_bool name exp actual
    ) caps
  ) trust_levels

(* --- Main --- *)

let () =
  Printf.printf "Mashin Governance Kernel Tests\n";
  Printf.printf "==============================\n";
  test_trust_values ();
  test_trust_ordering ();
  test_trust_lattice ();
  test_capability_allowed ();
  test_capability_for_directive ();
  test_interpreter ();
  test_cap_set ();
  test_exhaustive_matrix ();
  Printf.printf "\n==============================\n";
  Printf.printf "Results: %d passed, %d failed\n" !passed !failed;
  if !failed > 0 then exit 1
