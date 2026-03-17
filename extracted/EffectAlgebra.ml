open TrustSpec

type __ = Obj.t

type coq_CapSet = coq_Capability -> bool

(** val cap_empty : coq_CapSet **)

let cap_empty _ =
  false

(** val cap_singleton : coq_Capability -> coq_CapSet **)

let cap_singleton c c' =
  match c with
  | CapComputeLLMReason ->
    (match c' with
     | CapComputeLLMReason -> true
     | _ -> false)
  | CapNetHTTP -> (match c' with
                   | CapNetHTTP -> true
                   | _ -> false)
  | CapFS -> (match c' with
              | CapFS -> true
              | _ -> false)
  | CapDB -> (match c' with
              | CapDB -> true
              | _ -> false)
  | CapMemory -> (match c' with
                  | CapMemory -> true
                  | _ -> false)
  | CapMachineCall -> (match c' with
                       | CapMachineCall -> true
                       | _ -> false)
  | CapComputeExec -> (match c' with
                       | CapComputeExec -> true
                       | _ -> false)
  | CapNetWebSocket -> (match c' with
                        | CapNetWebSocket -> true
                        | _ -> false)

(** val cap_union : coq_CapSet -> coq_CapSet -> coq_CapSet **)

let cap_union s1 s2 c =
  (||) (s1 c) (s2 c)

(** val cap_full : coq_CapSet **)

let cap_full _ =
  true

type cap_subseteq = __
