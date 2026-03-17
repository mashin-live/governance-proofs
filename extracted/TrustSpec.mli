open Directives
open Governance

type __ = Obj.t

type coq_Capability =
| CapComputeLLMReason
| CapNetHTTP
| CapFS
| CapDB
| CapMemory
| CapMachineCall
| CapComputeExec
| CapNetWebSocket

val cap_eqb : coq_Capability -> coq_Capability -> bool

val cap_eqb_refl : __

val capability_for_directive : 'a1 coq_DirectiveE -> coq_Capability option

val is_observability : 'a1 coq_DirectiveE -> bool

val trust_value : coq_TrustLevel -> int

val trust_at_least : coq_TrustLevel -> coq_TrustLevel -> bool

val cap_in_list : coq_Capability -> coq_Capability list -> bool

val untrusted_caps : coq_Capability list

val tested_caps : coq_Capability list

val capability_allowed :
  coq_TrustLevel -> coq_Capability -> coq_Capability list -> bool
