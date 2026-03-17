open EffectAlgebra
open Governance
open TrustSpec

type __ = Obj.t

type trust_le = __

(** val trust_max : coq_TrustLevel -> coq_TrustLevel -> coq_TrustLevel **)

let trust_max t1 t2 =
  if (<=) (trust_value t1) (trust_value t2) then t2 else t1

(** val trust_min : coq_TrustLevel -> coq_TrustLevel -> coq_TrustLevel **)

let trust_min t1 t2 =
  if (<=) (trust_value t1) (trust_value t2) then t1 else t2

(** val allowed_cap_set :
    coq_TrustLevel -> coq_Capability list -> coq_CapSet **)

let allowed_cap_set tl declared cap =
  capability_allowed tl cap declared
