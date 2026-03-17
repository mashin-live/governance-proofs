(** * Directives: The Directive Event Type

    Formalizes Definition 2 (Directive) from the paper as an ITrees
    event type. Each directive variant declares an intended effect
    and specifies the type of result it expects.

    In the paper:
      D = LLMCall(...) | HTTPRequest(...) | FileOp(...) | ...

    In ITrees:
      An event type [E : Type -> Type] maps each event to its
      response type. [DirectiveE R] means "a directive that,
      when handled, produces a value of type R." *)

From MashinGov Require Import Prelude.

(** ** Directive Parameters

    Each directive carries structured parameters describing
    the intended effect. We abstract these as records. *)

(** LLM inference request *)
Record LLMCallParams := mk_llm_call {
  llm_model   : string;
  llm_system  : string;
  llm_user    : string;
}.

(** HTTP request *)
Inductive HttpMethod := GET | POST | PUT | DELETE | PATCH.

Record HTTPRequestParams := mk_http_request {
  http_method  : HttpMethod;
  http_url     : string;
  http_body    : option string;
}.

(** File operation *)
Inductive FileOperation := FileRead | FileWrite | FileDelete.

Record FileOpParams := mk_file_op {
  file_operation : FileOperation;
  file_path      : string;
  file_content   : option string;
}.

(** Machine call (invoke another machine) *)
Record CallMachineParams := mk_call_machine {
  callee_machine : string;
  callee_inputs  : list (string * string);
}.

(** Memory operation (semantic storage) *)
Inductive MemoryOperation := MemStore | MemRecall | MemForget.

Record MemoryOpParams := mk_memory_op {
  mem_operation : MemoryOperation;
  mem_key       : string;
  mem_value     : option string;
}.

(** Database operation *)
Record DBOpParams := mk_db_op {
  db_query  : string;
  db_params : list string;
}.

(** Shell execution *)
Record ExecOpParams := mk_exec_op {
  exec_command : string;
  exec_args    : list string;
}.

(** Step recording *)
Record RecordStepParams := mk_record_step {
  record_run_id   : string;
  record_name     : string;
  record_output   : string;
}.

(** Broadcast event *)
Record BroadcastParams := mk_broadcast {
  broadcast_event : string;
}.

(** Emit event *)
Record EmitEventParams := mk_emit_event {
  emit_type    : string;
  emit_payload : string;
}.

(** GraphQL request *)
Record GraphQLRequestParams := mk_graphql_request {
  graphql_url   : string;
  graphql_query : string;
  graphql_vars  : list (string * string);
}.

(** WebSocket operation *)
Inductive WebSocketOperation := WSConnect | WSSend | WSClose.

Record WebSocketOpParams := mk_websocket_op {
  ws_operation : WebSocketOperation;
  ws_url       : string;
  ws_payload   : option string;
}.

Record WebSocketResult := mk_websocket_result {
  ws_result_data : option string;
}.

(** MCP (Model Context Protocol) call *)
Record MCPCallParams := mk_mcp_call {
  mcp_server : string;
  mcp_tool   : string;
  mcp_args   : list (string * string);
}.

(** ** The Directive Event Type

    This is the signature functor F from the paper (Definition 4.3).
    Each constructor maps a directive to its response type.

    In the paper's notation:
      F(X) = Sum_{d in D} Params(d) x X

    In Coq/ITrees, we use a GADT-style definition where the
    index type specifies the response. *)

(** Abstract result types for each directive kind *)
Record LLMResponse := mk_llm_response {
  llm_response_text : string;
}.

Record HTTPResponse := mk_http_response {
  http_status : nat;
  http_response_body : string;
}.

Record FileResult := mk_file_result {
  file_result_data : option string;
}.

Record CallMachineResult := mk_call_machine_result {
  call_result_data : string;
}.

Record MemoryResult := mk_memory_result {
  mem_result_data : option string;
}.

Record DBResult := mk_db_result {
  db_rows : list (list string);
}.

Record ExecResult := mk_exec_result {
  exec_exit_code : nat;
  exec_stdout    : string;
}.

(** The directive event type. Each variant specifies its
    parameter type and its response type. *)
Inductive DirectiveE : Type -> Type :=
  | LLMCall       : LLMCallParams       -> DirectiveE LLMResponse
  | LLMCallStream : LLMCallParams       -> DirectiveE LLMResponse
  | HTTPRequest   : HTTPRequestParams    -> DirectiveE HTTPResponse
  | FileOp        : FileOpParams         -> DirectiveE FileResult
  | CallMachine   : CallMachineParams    -> DirectiveE CallMachineResult
  | MemoryOp      : MemoryOpParams       -> DirectiveE MemoryResult
  | DBOp          : DBOpParams           -> DirectiveE DBResult
  | ExecOp        : ExecOpParams         -> DirectiveE ExecResult
  | RecordStep    : RecordStepParams     -> DirectiveE unit
  | Broadcast     : BroadcastParams      -> DirectiveE unit
  | EmitEvent     : EmitEventParams      -> DirectiveE unit
  | GraphQLRequest : GraphQLRequestParams -> DirectiveE HTTPResponse
  | WebSocketOp   : WebSocketOpParams    -> DirectiveE WebSocketResult
  | MCPCall       : MCPCallParams        -> DirectiveE CallMachineResult.

(** ** Executor Programs

    An executor's output is an interaction tree over [DirectiveE].
    This is the free monad [Free(F, Result)] from the paper
    (Definition 4.4).

    - [Ret v] is [Pure(v)] in the paper: a pure value.
    - [Vis (d, k)] is [Op(d, params, k)]: a directive with
      a continuation. *)

Definition executor_program (R : Type) : Type := itree DirectiveE R.

(** ** Effect Events

    The target of interpretation. These represent actual I/O
    operations that the interpreter performs. We model them
    abstractly since our proofs are about the governance
    structure, not the I/O implementation. *)

Inductive IOE : Type -> Type :=
  | PerformIO : forall (R : Type), string -> IOE R.

(** ** Governance Events

    Events emitted by the governance pipeline itself:
    trust checks, permission checks, provenance recording, etc.
    These are the governance stages from Definition 3 in the paper. *)

Inductive GovernanceStage :=
  | TrustCheck
  | PermissionCheck
  | PhaseValidation
  | PreHooks
  | Guardrails
  | ProvenanceRecord
  | EventBroadcast.

Inductive GovE : Type -> Type :=
  | GovCheck : GovernanceStage -> GovE bool.

(** The combined event type for governed execution:
    governance checks + actual I/O. *)
Definition GovIOE := GovE +' IOE.

(** ** Directive Classification

    Helper to classify directives. The paper distinguishes
    directives that require governance (effect-producing) from
    those that are metadata-only. *)

Definition directive_tag {R : Type} (d : DirectiveE R) : string :=
  match d with
  | LLMCall _       => "llm_call"
  | LLMCallStream _ => "llm_call_stream"
  | HTTPRequest _   => "http_request"
  | FileOp _        => "file_op"
  | CallMachine _   => "call_machine"
  | MemoryOp _      => "memory_op"
  | DBOp _          => "db_op"
  | ExecOp _        => "exec_command"
  | RecordStep _    => "record_step"
  | Broadcast _     => "broadcast"
  | EmitEvent _     => "emit_event"
  | GraphQLRequest _ => "graphql_request"
  | WebSocketOp _   => "websocket_op"
  | MCPCall _       => "mcp_call"
  end.
