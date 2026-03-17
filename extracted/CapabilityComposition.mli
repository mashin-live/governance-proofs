open EffectAlgebra
open Governance
open TrustSpec

type __ = Obj.t

type trust_le = __

val trust_max : coq_TrustLevel -> coq_TrustLevel -> coq_TrustLevel

val trust_min : coq_TrustLevel -> coq_TrustLevel -> coq_TrustLevel

val allowed_cap_set : coq_TrustLevel -> coq_Capability list -> coq_CapSet
