open TrustSpec

type __ = Obj.t

type coq_CapSet = coq_Capability -> bool

val cap_empty : coq_CapSet

val cap_singleton : coq_Capability -> coq_CapSet

val cap_union : coq_CapSet -> coq_CapSet -> coq_CapSet

val cap_full : coq_CapSet

type cap_subseteq = __
