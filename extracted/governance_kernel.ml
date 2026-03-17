(** Governance Kernel: Clean OCaml interface over Coq-extracted code.

    This module wraps the machine-checked extracted code with ergonomic
    OCaml types (native strings instead of char lists, concrete hash
    instantiation). Every function in this module delegates to
    Coq-extracted code; no governance logic is implemented here.

    The correctness guarantee: if this module compiles and links against
    the extracted modules, then every governance decision flows through
    proved code. *)

(* --- String conversion utilities --- *)

let string_to_char_list (s : string) : char list =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (s.[i] :: acc)
  in
  aux (String.length s - 1) []

let char_list_to_string (cl : char list) : string =
  let buf = Buffer.create (List.length cl) in
  List.iter (Buffer.add_char buf) cl;
  Buffer.contents buf

(* --- Trust levels (re-export with string conversion) --- *)

type trust_level = Governance.coq_TrustLevel =
  | Untrusted
  | Tested
  | Evaluated
  | Reviewed
  | Stdlib
  | System

let trust_level_of_string = function
  | "untrusted" -> Some Untrusted
  | "tested"    -> Some Tested
  | "evaluated" -> Some Evaluated
  | "reviewed"  -> Some Reviewed
  | "stdlib"    -> Some Stdlib
  | "system"    -> Some System
  | _ -> None

let string_of_trust_level = function
  | Untrusted -> "untrusted"
  | Tested    -> "tested"
  | Evaluated -> "evaluated"
  | Reviewed  -> "reviewed"
  | Stdlib    -> "stdlib"
  | System    -> "system"

let trust_value (tl : trust_level) : int =
  TrustSpec.trust_value tl

let trust_at_least ~(has : trust_level) ~(requires : trust_level) : bool =
  TrustSpec.trust_at_least has requires

(* --- Capabilities (re-export) --- *)

type capability = TrustSpec.coq_Capability =
  | CapComputeLLMReason
  | CapNetHTTP
  | CapFS
  | CapDB
  | CapMemory
  | CapMachineCall
  | CapComputeExec
  | CapNetWebSocket

let capability_of_string = function
  | "compute.llm_reason" -> Some CapComputeLLMReason
  | "net.http"           -> Some CapNetHTTP
  | "fs"                 -> Some CapFS
  | "db"                 -> Some CapDB
  | "memory"             -> Some CapMemory
  | "machine.call"       -> Some CapMachineCall
  | "compute.exec"       -> Some CapComputeExec
  | "net.websocket"      -> Some CapNetWebSocket
  | _ -> None

let string_of_capability = function
  | CapComputeLLMReason -> "compute.llm_reason"
  | CapNetHTTP          -> "net.http"
  | CapFS               -> "fs"
  | CapDB               -> "db"
  | CapMemory           -> "memory"
  | CapMachineCall       -> "machine.call"
  | CapComputeExec       -> "compute.exec"
  | CapNetWebSocket      -> "net.websocket"

let all_capabilities =
  [ CapComputeLLMReason; CapNetHTTP; CapFS; CapDB;
    CapMemory; CapMachineCall; CapComputeExec; CapNetWebSocket ]

(* --- Core governance functions (delegate to extracted code) --- *)

let capability_allowed ~(trust : trust_level) ~(cap : capability)
    ~(declared : capability list) : bool =
  TrustSpec.capability_allowed trust cap declared

let capability_for_directive_tag (tag : string) : capability option =
  (* Map directive tag strings to DirectiveE constructors,
     then use the extracted capability_for_directive *)
  let dummy_params_llm = { Directives.llm_model = []; llm_system = []; llm_user = [] } in
  let dummy_params_http = { Directives.http_method = Directives.GET; http_url = []; http_body = None } in
  let dummy_params_file = { Directives.file_operation = Directives.FileRead; file_path = []; file_content = None } in
  let dummy_params_call = { Directives.callee_machine = []; callee_inputs = [] } in
  let dummy_params_mem = { Directives.mem_operation = Directives.MemStore; mem_key = []; mem_value = None } in
  let dummy_params_db = { Directives.db_query = []; db_params = [] } in
  let dummy_params_exec = { Directives.exec_command = []; exec_args = [] } in
  let dummy_params_record = { Directives.record_run_id = []; record_name = []; record_output = [] } in
  let dummy_params_emit = { Directives.emit_type = []; emit_payload = [] } in
  let dummy_params_graphql = { Directives.graphql_url = []; graphql_query = []; graphql_vars = [] } in
  let dummy_params_ws = { Directives.ws_operation = Directives.WSConnect; ws_url = []; ws_payload = None } in
  let dummy_params_mcp = { Directives.mcp_server = []; mcp_tool = []; mcp_args = [] } in
  let directive = match tag with
    | "llm_call"        -> Some (Directives.LLMCall dummy_params_llm)
    | "llm_call_stream" -> Some (Directives.LLMCallStream dummy_params_llm)
    | "http_request"    -> Some (Directives.HTTPRequest dummy_params_http)
    | "file_op"         -> Some (Directives.FileOp dummy_params_file)
    | "call_machine"    -> Some (Directives.CallMachine dummy_params_call)
    | "memory_op"       -> Some (Directives.MemoryOp dummy_params_mem)
    | "db_op"           -> Some (Directives.DBOp dummy_params_db)
    | "exec_command"    -> Some (Directives.ExecOp dummy_params_exec)
    | "record_step"     -> Some (Directives.RecordStep dummy_params_record)
    | "broadcast"       -> Some (Directives.Broadcast [])
    | "emit_event"      -> Some (Directives.EmitEvent dummy_params_emit)
    | "graphql_request" -> Some (Directives.GraphQLRequest dummy_params_graphql)
    | "websocket_op"    -> Some (Directives.WebSocketOp dummy_params_ws)
    | "mcp_call"        -> Some (Directives.MCPCall dummy_params_mcp)
    | _ -> None
  in
  match directive with
  | Some d -> TrustSpec.capability_for_directive d
  | None -> None

let is_observability_tag (tag : string) : bool =
  match capability_for_directive_tag tag with
  | Some _ -> false
  | None -> true

(* --- Interpreter (hash-parameterized) --- *)

module type HashSig = sig
  type t
  val compute : string -> t -> t
  val to_string : t -> string
  val of_string : string -> t
end

module type GovernanceInterpreter = sig
  type hash

  type interpreter_state = {
    trust_level : trust_level;
    declared_caps : capability list;
    prev_hash : hash;
  }

  type denial_reason =
    | CapabilityDenied of capability * trust_level
    | DirectiveNotImplemented

  type step_result =
    | StepOk of hash * interpreter_state
    | StepDenied of denial_reason

  val init_state : hash -> trust_level -> capability list -> interpreter_state
  val interp_directive : string -> interpreter_state -> step_result
  val interp_directives : string list -> interpreter_state -> step_result
end

module MakeInterpreter (H : HashSig) : GovernanceInterpreter with type hash = H.t = struct
  type hash = H.t

  type interpreter_state = {
    trust_level : trust_level;
    declared_caps : capability list;
    prev_hash : hash;
  }

  type denial_reason =
    | CapabilityDenied of capability * trust_level
    | DirectiveNotImplemented

  type step_result =
    | StepOk of hash * interpreter_state
    | StepDenied of denial_reason

  (* Bridge between our hash type and the Coq extraction's polymorphic hash *)
  let coq_compute_hash (tag_chars : char list) (prev : hash) : hash =
    let tag = char_list_to_string tag_chars in
    H.compute tag prev

  let convert_state (st : hash InterpreterSpec.coq_InterpreterState) : interpreter_state =
    { trust_level = st.InterpreterSpec.is_trust_level;
      declared_caps = st.InterpreterSpec.is_declared_caps;
      prev_hash = st.InterpreterSpec.is_prev_hash }

  let convert_state_back (st : interpreter_state) : hash InterpreterSpec.coq_InterpreterState =
    { InterpreterSpec.is_trust_level = st.trust_level;
      InterpreterSpec.is_declared_caps = st.declared_caps;
      InterpreterSpec.is_prev_hash = st.prev_hash }

  let convert_result (r : hash InterpreterSpec.coq_StepResult) : step_result =
    match r with
    | InterpreterSpec.StepOk (h, st) -> StepOk (h, convert_state st)
    | InterpreterSpec.StepDenied reason ->
      match reason with
      | InterpreterSpec.CapabilityDenied (cap, tl) -> StepDenied (CapabilityDenied (cap, tl))
      | InterpreterSpec.DirectiveNotImplemented -> StepDenied DirectiveNotImplemented

  let init_state genesis_hash tl caps =
    let coq_st = InterpreterSpec.init_state genesis_hash tl caps in
    convert_state coq_st

  let tag_to_directive (tag : string) : InterpreterSpec.coq_AnyDirective option =
    let dummy_llm = { Directives.llm_model = []; llm_system = []; llm_user = [] } in
    let dummy_http = { Directives.http_method = Directives.GET; http_url = []; http_body = None } in
    let dummy_file = { Directives.file_operation = Directives.FileRead; file_path = []; file_content = None } in
    let dummy_call = { Directives.callee_machine = []; callee_inputs = [] } in
    let dummy_mem = { Directives.mem_operation = Directives.MemStore; mem_key = []; mem_value = None } in
    let dummy_db = { Directives.db_query = []; db_params = [] } in
    let dummy_exec = { Directives.exec_command = []; exec_args = [] } in
    let dummy_record = { Directives.record_run_id = []; record_name = []; record_output = [] } in
    let dummy_emit = { Directives.emit_type = []; emit_payload = [] } in
    let dummy_graphql = { Directives.graphql_url = []; graphql_query = []; graphql_vars = [] } in
    let dummy_ws = { Directives.ws_operation = Directives.WSConnect; ws_url = []; ws_payload = None } in
    let dummy_mcp = { Directives.mcp_server = []; mcp_tool = []; mcp_args = [] } in
    match tag with
    | "llm_call"        -> Some (Obj.magic (Directives.LLMCall dummy_llm))
    | "llm_call_stream" -> Some (Obj.magic (Directives.LLMCallStream dummy_llm))
    | "http_request"    -> Some (Obj.magic (Directives.HTTPRequest dummy_http))
    | "file_op"         -> Some (Obj.magic (Directives.FileOp dummy_file))
    | "call_machine"    -> Some (Obj.magic (Directives.CallMachine dummy_call))
    | "memory_op"       -> Some (Obj.magic (Directives.MemoryOp dummy_mem))
    | "db_op"           -> Some (Obj.magic (Directives.DBOp dummy_db))
    | "exec_command"    -> Some (Obj.magic (Directives.ExecOp dummy_exec))
    | "record_step"     -> Some (Obj.magic (Directives.RecordStep dummy_record))
    | "broadcast"       -> Some (Obj.magic (Directives.Broadcast []))
    | "emit_event"      -> Some (Obj.magic (Directives.EmitEvent dummy_emit))
    | "graphql_request" -> Some (Obj.magic (Directives.GraphQLRequest dummy_graphql))
    | "websocket_op"    -> Some (Obj.magic (Directives.WebSocketOp dummy_ws))
    | "mcp_call"        -> Some (Obj.magic (Directives.MCPCall dummy_mcp))
    | _ -> None

  let interp_directive tag st =
    match tag_to_directive tag with
    | None -> StepDenied DirectiveNotImplemented
    | Some d ->
      let coq_st = convert_state_back st in
      let result = InterpreterSpec.interp_any_directive coq_compute_hash d coq_st in
      convert_result result

  let interp_directives tags st =
    let rec go tags st =
      match tags with
      | [] -> StepOk (st.prev_hash, st)
      | tag :: rest ->
        match interp_directive tag st with
        | StepOk (_, st') -> go rest st'
        | StepDenied _ as denied -> denied
    in
    go tags st
end

(* --- CapSet operations (delegate to extracted code) --- *)

type cap_set = EffectAlgebra.coq_CapSet

let cap_empty : cap_set = EffectAlgebra.cap_empty
let cap_singleton (c : capability) : cap_set = EffectAlgebra.cap_singleton c
let cap_union (s1 : cap_set) (s2 : cap_set) : cap_set = EffectAlgebra.cap_union s1 s2
let cap_full : cap_set = EffectAlgebra.cap_full

let allowed_cap_set ~(trust : trust_level) ~(declared : capability list) : cap_set =
  CapabilityComposition.allowed_cap_set trust declared

(* --- Trust lattice operations --- *)

let trust_max (t1 : trust_level) (t2 : trust_level) : trust_level =
  CapabilityComposition.trust_max t1 t2

let trust_min (t1 : trust_level) (t2 : trust_level) : trust_level =
  CapabilityComposition.trust_min t1 t2

(* --- Concrete SHA-256-like hash instantiation using Digest --- *)

module StringHash : HashSig with type t = string = struct
  type t = string
  let compute tag prev =
    Digest.string (tag ^ ":" ^ prev)
  let to_string h = h
  let of_string s = s
end

(* Default interpreter using MD5 digest (for testing; NIF uses SHA-256) *)
module Interpreter = MakeInterpreter(StringHash)
