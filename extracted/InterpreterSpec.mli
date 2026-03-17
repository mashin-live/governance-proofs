open Directives
open Governance
open TrustSpec

type __ = Obj.t

type 'hash coq_InterpreterState = { is_trust_level : coq_TrustLevel;
                                    is_declared_caps : coq_Capability list;
                                    is_prev_hash : 'hash }

val init_state :
  'a1 -> coq_TrustLevel -> coq_Capability list -> 'a1 coq_InterpreterState

type coq_DenialReason =
| CapabilityDenied of coq_Capability * coq_TrustLevel
| DirectiveNotImplemented

type 'hash coq_StepResult =
| StepOk of 'hash * 'hash coq_InterpreterState
| StepDenied of coq_DenialReason

val interp_directive :
  (char list -> 'a1 -> 'a1) -> 'a2 coq_DirectiveE -> 'a1 coq_InterpreterState
  -> 'a1 coq_StepResult

type coq_AnyDirective =
  __ coq_DirectiveE
  (* singleton inductive, whose constructor was MkAnyDirective *)

val interp_any_directive :
  (char list -> 'a1 -> 'a1) -> coq_AnyDirective -> 'a1 coq_InterpreterState
  -> 'a1 coq_StepResult

val interp_directives :
  (char list -> 'a1 -> 'a1) -> coq_AnyDirective list -> 'a1
  coq_InterpreterState -> 'a1 coq_StepResult
