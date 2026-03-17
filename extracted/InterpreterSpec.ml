open Directives
open Governance
open TrustSpec

type __ = Obj.t

type 'hash coq_InterpreterState = { is_trust_level : coq_TrustLevel;
                                    is_declared_caps : coq_Capability list;
                                    is_prev_hash : 'hash }

(** val init_state :
    'a1 -> coq_TrustLevel -> coq_Capability list -> 'a1 coq_InterpreterState **)

let init_state genesis_hash tl caps =
  { is_trust_level = tl; is_declared_caps = caps; is_prev_hash =
    genesis_hash }

type coq_DenialReason =
| CapabilityDenied of coq_Capability * coq_TrustLevel
| DirectiveNotImplemented

type 'hash coq_StepResult =
| StepOk of 'hash * 'hash coq_InterpreterState
| StepDenied of coq_DenialReason

(** val interp_directive :
    (char list -> 'a1 -> 'a1) -> 'a2 coq_DirectiveE -> 'a1
    coq_InterpreterState -> 'a1 coq_StepResult **)

let interp_directive compute_hash d st =
  match capability_for_directive d with
  | Some cap ->
    if capability_allowed st.is_trust_level cap st.is_declared_caps
    then let new_hash =
           compute_hash
             (match d with
              | LLMCall _ ->
                'l'::('l'::('m'::('_'::('c'::('a'::('l'::('l'::[])))))))
              | LLMCallStream _ ->
                'l'::('l'::('m'::('_'::('c'::('a'::('l'::('l'::('_'::('s'::('t'::('r'::('e'::('a'::('m'::[]))))))))))))))
              | HTTPRequest _ ->
                'h'::('t'::('t'::('p'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[])))))))))))
              | FileOp _ -> 'f'::('i'::('l'::('e'::('_'::('o'::('p'::[]))))))
              | CallMachine _ ->
                'c'::('a'::('l'::('l'::('_'::('m'::('a'::('c'::('h'::('i'::('n'::('e'::[])))))))))))
              | MemoryOp _ ->
                'm'::('e'::('m'::('o'::('r'::('y'::('_'::('o'::('p'::[]))))))))
              | DBOp _ -> 'd'::('b'::('_'::('o'::('p'::[]))))
              | ExecOp _ ->
                'e'::('x'::('e'::('c'::('_'::('c'::('o'::('m'::('m'::('a'::('n'::('d'::[])))))))))))
              | RecordStep _ ->
                'r'::('e'::('c'::('o'::('r'::('d'::('_'::('s'::('t'::('e'::('p'::[]))))))))))
              | Broadcast _ ->
                'b'::('r'::('o'::('a'::('d'::('c'::('a'::('s'::('t'::[]))))))))
              | EmitEvent _ ->
                'e'::('m'::('i'::('t'::('_'::('e'::('v'::('e'::('n'::('t'::[])))))))))
              | GraphQLRequest _ ->
                'g'::('r'::('a'::('p'::('h'::('q'::('l'::('_'::('r'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))))))))))
              | WebSocketOp _ ->
                'w'::('e'::('b'::('s'::('o'::('c'::('k'::('e'::('t'::('_'::('o'::('p'::[])))))))))))
              | MCPCall _ ->
                'm'::('c'::('p'::('_'::('c'::('a'::('l'::('l'::[]))))))))
             st.is_prev_hash
         in
         let st' = { is_trust_level = st.is_trust_level; is_declared_caps =
           st.is_declared_caps; is_prev_hash = new_hash }
         in
         StepOk (new_hash, st')
    else StepDenied (CapabilityDenied (cap, st.is_trust_level))
  | None -> StepOk (st.is_prev_hash, st)

type coq_AnyDirective =
  __ coq_DirectiveE
  (* singleton inductive, whose constructor was MkAnyDirective *)

(** val interp_any_directive :
    (char list -> 'a1 -> 'a1) -> coq_AnyDirective -> 'a1 coq_InterpreterState
    -> 'a1 coq_StepResult **)

let interp_any_directive =
  interp_directive

(** val interp_directives :
    (char list -> 'a1 -> 'a1) -> coq_AnyDirective list -> 'a1
    coq_InterpreterState -> 'a1 coq_StepResult **)

let rec interp_directives compute_hash ds st =
  match ds with
  | [] -> StepOk (st.is_prev_hash, st)
  | d::rest ->
    (match interp_any_directive compute_hash d st with
     | StepOk (_, st') -> interp_directives compute_hash rest st'
     | StepDenied reason -> StepDenied reason)
