open Directives
open Governance

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_Capability =
| CapComputeLLMReason
| CapNetHTTP
| CapFS
| CapDB
| CapMemory
| CapMachineCall
| CapComputeExec
| CapNetWebSocket

(** val cap_eqb : coq_Capability -> coq_Capability -> bool **)

let cap_eqb c1 c2 =
  match c1 with
  | CapComputeLLMReason ->
    (match c2 with
     | CapComputeLLMReason -> true
     | _ -> false)
  | CapNetHTTP -> (match c2 with
                   | CapNetHTTP -> true
                   | _ -> false)
  | CapFS -> (match c2 with
              | CapFS -> true
              | _ -> false)
  | CapDB -> (match c2 with
              | CapDB -> true
              | _ -> false)
  | CapMemory -> (match c2 with
                  | CapMemory -> true
                  | _ -> false)
  | CapMachineCall -> (match c2 with
                       | CapMachineCall -> true
                       | _ -> false)
  | CapComputeExec -> (match c2 with
                       | CapComputeExec -> true
                       | _ -> false)
  | CapNetWebSocket -> (match c2 with
                        | CapNetWebSocket -> true
                        | _ -> false)

(** val cap_eqb_refl : __ **)

let cap_eqb_refl =
  __

(** val capability_for_directive :
    'a1 coq_DirectiveE -> coq_Capability option **)

let capability_for_directive = function
| LLMCall _ -> Some CapComputeLLMReason
| LLMCallStream _ -> Some CapComputeLLMReason
| HTTPRequest _ -> Some CapNetHTTP
| FileOp _ -> Some CapFS
| CallMachine _ -> Some CapMachineCall
| MemoryOp _ -> Some CapMemory
| DBOp _ -> Some CapDB
| ExecOp _ -> Some CapComputeExec
| GraphQLRequest _ -> Some CapNetHTTP
| WebSocketOp _ -> Some CapNetWebSocket
| MCPCall _ -> Some CapMachineCall
| _ -> None

(** val is_observability : 'a1 coq_DirectiveE -> bool **)

let is_observability d =
  match capability_for_directive d with
  | Some _ -> false
  | None -> true

(** val trust_value : coq_TrustLevel -> int **)

let trust_value = function
| Untrusted -> 0
| Tested -> Stdlib.Int.succ 0
| Evaluated -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| Reviewed -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| Stdlib ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
| System ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))

(** val trust_at_least : coq_TrustLevel -> coq_TrustLevel -> bool **)

let trust_at_least has requires =
  (<=) (trust_value requires) (trust_value has)

(** val cap_in_list : coq_Capability -> coq_Capability list -> bool **)

let rec cap_in_list c = function
| [] -> false
| x::rest ->
  (match c with
   | CapComputeLLMReason ->
     (match x with
      | CapComputeLLMReason -> true
      | _ -> cap_in_list c rest)
   | CapNetHTTP -> (match x with
                    | CapNetHTTP -> true
                    | _ -> cap_in_list c rest)
   | CapFS -> (match x with
               | CapFS -> true
               | _ -> cap_in_list c rest)
   | CapDB -> (match x with
               | CapDB -> true
               | _ -> cap_in_list c rest)
   | CapMemory -> (match x with
                   | CapMemory -> true
                   | _ -> cap_in_list c rest)
   | CapMachineCall ->
     (match x with
      | CapMachineCall -> true
      | _ -> cap_in_list c rest)
   | CapComputeExec ->
     (match x with
      | CapComputeExec -> true
      | _ -> cap_in_list c rest)
   | CapNetWebSocket ->
     (match x with
      | CapNetWebSocket -> true
      | _ -> cap_in_list c rest))

(** val untrusted_caps : coq_Capability list **)

let untrusted_caps =
  CapComputeLLMReason::[]

(** val tested_caps : coq_Capability list **)

let tested_caps =
  CapComputeLLMReason::(CapComputeExec::(CapMemory::(CapMachineCall::[])))

(** val capability_allowed :
    coq_TrustLevel -> coq_Capability -> coq_Capability list -> bool **)

let capability_allowed tl cap declared_caps =
  match tl with
  | Untrusted ->
    let rec cap_in_list0 c = function
    | [] -> false
    | x::rest ->
      (match c with
       | CapComputeLLMReason ->
         (match x with
          | CapComputeLLMReason -> true
          | _ -> cap_in_list0 c rest)
       | CapNetHTTP ->
         (match x with
          | CapNetHTTP -> true
          | _ -> cap_in_list0 c rest)
       | CapFS -> (match x with
                   | CapFS -> true
                   | _ -> cap_in_list0 c rest)
       | CapDB -> (match x with
                   | CapDB -> true
                   | _ -> cap_in_list0 c rest)
       | CapMemory ->
         (match x with
          | CapMemory -> true
          | _ -> cap_in_list0 c rest)
       | CapMachineCall ->
         (match x with
          | CapMachineCall -> true
          | _ -> cap_in_list0 c rest)
       | CapComputeExec ->
         (match x with
          | CapComputeExec -> true
          | _ -> cap_in_list0 c rest)
       | CapNetWebSocket ->
         (match x with
          | CapNetWebSocket -> true
          | _ -> cap_in_list0 c rest))
    in cap_in_list0 cap untrusted_caps
  | Tested ->
    let rec cap_in_list0 c = function
    | [] -> false
    | x::rest ->
      (match c with
       | CapComputeLLMReason ->
         (match x with
          | CapComputeLLMReason -> true
          | _ -> cap_in_list0 c rest)
       | CapNetHTTP ->
         (match x with
          | CapNetHTTP -> true
          | _ -> cap_in_list0 c rest)
       | CapFS -> (match x with
                   | CapFS -> true
                   | _ -> cap_in_list0 c rest)
       | CapDB -> (match x with
                   | CapDB -> true
                   | _ -> cap_in_list0 c rest)
       | CapMemory ->
         (match x with
          | CapMemory -> true
          | _ -> cap_in_list0 c rest)
       | CapMachineCall ->
         (match x with
          | CapMachineCall -> true
          | _ -> cap_in_list0 c rest)
       | CapComputeExec ->
         (match x with
          | CapComputeExec -> true
          | _ -> cap_in_list0 c rest)
       | CapNetWebSocket ->
         (match x with
          | CapNetWebSocket -> true
          | _ -> cap_in_list0 c rest))
    in cap_in_list0 cap tested_caps
  | Evaluated ->
    let rec cap_in_list0 c = function
    | [] -> false
    | x::rest ->
      (match c with
       | CapComputeLLMReason ->
         (match x with
          | CapComputeLLMReason -> true
          | _ -> cap_in_list0 c rest)
       | CapNetHTTP ->
         (match x with
          | CapNetHTTP -> true
          | _ -> cap_in_list0 c rest)
       | CapFS -> (match x with
                   | CapFS -> true
                   | _ -> cap_in_list0 c rest)
       | CapDB -> (match x with
                   | CapDB -> true
                   | _ -> cap_in_list0 c rest)
       | CapMemory ->
         (match x with
          | CapMemory -> true
          | _ -> cap_in_list0 c rest)
       | CapMachineCall ->
         (match x with
          | CapMachineCall -> true
          | _ -> cap_in_list0 c rest)
       | CapComputeExec ->
         (match x with
          | CapComputeExec -> true
          | _ -> cap_in_list0 c rest)
       | CapNetWebSocket ->
         (match x with
          | CapNetWebSocket -> true
          | _ -> cap_in_list0 c rest))
    in cap_in_list0 cap declared_caps
  | Reviewed ->
    let rec cap_in_list0 c = function
    | [] -> false
    | x::rest ->
      (match c with
       | CapComputeLLMReason ->
         (match x with
          | CapComputeLLMReason -> true
          | _ -> cap_in_list0 c rest)
       | CapNetHTTP ->
         (match x with
          | CapNetHTTP -> true
          | _ -> cap_in_list0 c rest)
       | CapFS -> (match x with
                   | CapFS -> true
                   | _ -> cap_in_list0 c rest)
       | CapDB -> (match x with
                   | CapDB -> true
                   | _ -> cap_in_list0 c rest)
       | CapMemory ->
         (match x with
          | CapMemory -> true
          | _ -> cap_in_list0 c rest)
       | CapMachineCall ->
         (match x with
          | CapMachineCall -> true
          | _ -> cap_in_list0 c rest)
       | CapComputeExec ->
         (match x with
          | CapComputeExec -> true
          | _ -> cap_in_list0 c rest)
       | CapNetWebSocket ->
         (match x with
          | CapNetWebSocket -> true
          | _ -> cap_in_list0 c rest))
    in cap_in_list0 cap declared_caps
  | _ -> true
