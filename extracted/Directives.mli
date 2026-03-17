
type coq_LLMCallParams = { llm_model : char list; llm_system : char list;
                           llm_user : char list }

type coq_HttpMethod =
| GET
| POST
| PUT
| DELETE
| PATCH

type coq_HTTPRequestParams = { http_method : coq_HttpMethod;
                               http_url : char list;
                               http_body : char list option }

type coq_FileOperation =
| FileRead
| FileWrite
| FileDelete

type coq_FileOpParams = { file_operation : coq_FileOperation;
                          file_path : char list;
                          file_content : char list option }

type coq_CallMachineParams = { callee_machine : char list;
                               callee_inputs : (char list * char list) list }

type coq_MemoryOperation =
| MemStore
| MemRecall
| MemForget

type coq_MemoryOpParams = { mem_operation : coq_MemoryOperation;
                            mem_key : char list; mem_value : char list option }

type coq_DBOpParams = { db_query : char list; db_params : char list list }

type coq_ExecOpParams = { exec_command : char list; exec_args : char list list }

type coq_RecordStepParams = { record_run_id : char list;
                              record_name : char list;
                              record_output : char list }

type coq_BroadcastParams =
  char list
  (* singleton inductive, whose constructor was mk_broadcast *)

type coq_EmitEventParams = { emit_type : char list; emit_payload : char list }

type coq_GraphQLRequestParams = { graphql_url : char list;
                                  graphql_query : char list;
                                  graphql_vars : (char list * char list) list }

type coq_WebSocketOperation =
| WSConnect
| WSSend
| WSClose

type coq_WebSocketOpParams = { ws_operation : coq_WebSocketOperation;
                               ws_url : char list;
                               ws_payload : char list option }

type coq_WebSocketResult =
  char list option
  (* singleton inductive, whose constructor was mk_websocket_result *)

type coq_MCPCallParams = { mcp_server : char list; mcp_tool : char list;
                           mcp_args : (char list * char list) list }

type coq_LLMResponse =
  char list
  (* singleton inductive, whose constructor was mk_llm_response *)

type coq_HTTPResponse = { http_status : int; http_response_body : char list }

type coq_FileResult =
  char list option
  (* singleton inductive, whose constructor was mk_file_result *)

type coq_CallMachineResult =
  char list
  (* singleton inductive, whose constructor was mk_call_machine_result *)

type coq_MemoryResult =
  char list option
  (* singleton inductive, whose constructor was mk_memory_result *)

type coq_DBResult =
  char list list list
  (* singleton inductive, whose constructor was mk_db_result *)

type coq_ExecResult = { exec_exit_code : int; exec_stdout : char list }

type 'x coq_DirectiveE =
| LLMCall of coq_LLMCallParams
| LLMCallStream of coq_LLMCallParams
| HTTPRequest of coq_HTTPRequestParams
| FileOp of coq_FileOpParams
| CallMachine of coq_CallMachineParams
| MemoryOp of coq_MemoryOpParams
| DBOp of coq_DBOpParams
| ExecOp of coq_ExecOpParams
| RecordStep of coq_RecordStepParams
| Broadcast of coq_BroadcastParams
| EmitEvent of coq_EmitEventParams
| GraphQLRequest of coq_GraphQLRequestParams
| WebSocketOp of coq_WebSocketOpParams
| MCPCall of coq_MCPCallParams

type coq_GovernanceStage =
| TrustCheck
| PermissionCheck
| PhaseValidation
| PreHooks
| Guardrails
| ProvenanceRecord
| EventBroadcast

val directive_tag : 'a1 coq_DirectiveE -> char list
