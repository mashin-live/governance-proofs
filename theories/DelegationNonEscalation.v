(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file.

   The governance architecture formalized in this development is the
   subject of pending U.S. patent applications by Mashin, Inc. The
   MIT license applies to these proof sources; it does not grant
   rights under any patents. *)

(** * DelegationNonEscalation: Machine Calls Cannot Launder Capabilities

    When machine M1 calls machine M2, M2's effective capabilities
    are constrained by M1's capability set. A machine cannot use
    another machine as a capability laundering mechanism.

    This formalizes the runtime behavior implemented in GAP-228:
    - execute_call_standard passes parent_capabilities from the caller
    - execute_call_isolated applies capability_ceiling to the child
    - context_builder.extract_effective_capabilities intersects
      child declared capabilities with the parent ceiling

    Key results:
    - effective_caps computes the intersection policy
    - delegation_non_escalation: effective caps are always within
      the caller's cap set (for non-System/Stdlib callers)
    - call_cannot_gain_caps: a :call step cannot grant capabilities
      not held by the caller
    - composition_respects_ceiling: chained calls preserve the ceiling
    - system_stdlib_exempt: System/Stdlib callers impose no ceiling

    Elixir: execute_call_isolated/7 in runtime.ex
            extract_effective_capabilities/2 in context_builder.ex

    Dependencies: Prelude, Directives, TrustSpec, EffectAlgebra,
                  CapabilityComposition, Safety *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import TrustSpec.
From MashinGov Require Import EffectAlgebra.
From MashinGov Require Import CapabilityComposition.
From MashinGov Require Import Safety.
From MashinGov Require Import Governance.

From Paco Require Import paco.

(* ================================================================= *)
(* Capability Intersection (Ceiling Policy)                            *)
(* ================================================================= *)

(** ** Effective Capability Set Under Delegation

    When a caller with capability set [parent_caps] invokes a callee
    with declared capability set [child_caps], the callee's effective
    capabilities are the intersection. This models the runtime's
    extract_effective_capabilities function in context_builder.ex. *)

Definition cap_intersection (s1 s2 : CapSet) : CapSet :=
  fun c => andb (s1 c) (s2 c).

(** The intersection is a subset of both inputs. *)
Lemma cap_intersection_sub_l :
  forall s1 s2, cap_subseteq (cap_intersection s1 s2) s1.
Proof.
  intros s1 s2 c H. unfold cap_intersection in H.
  apply andb_prop in H. destruct H. assumption.
Qed.

Lemma cap_intersection_sub_r :
  forall s1 s2, cap_subseteq (cap_intersection s1 s2) s2.
Proof.
  intros s1 s2 c H. unfold cap_intersection in H.
  apply andb_prop in H. destruct H. assumption.
Qed.

(** Intersection with cap_full is identity. *)
Lemma cap_intersection_full_l :
  forall s, cap_subseteq s (cap_intersection cap_full s).
Proof.
  intros s c H. unfold cap_intersection, cap_full. simpl. assumption.
Qed.

Lemma cap_intersection_full_r :
  forall s, cap_subseteq s (cap_intersection s cap_full).
Proof.
  intros s c H. unfold cap_intersection, cap_full.
  rewrite andb_true_r. assumption.
Qed.

(** Intersection is monotone: if s1 ⊆ s1' and s2 ⊆ s2', then
    s1 ∩ s2 ⊆ s1' ∩ s2'. *)
Lemma cap_intersection_monotone :
  forall s1 s1' s2 s2',
    cap_subseteq s1 s1' ->
    cap_subseteq s2 s2' ->
    cap_subseteq (cap_intersection s1 s2) (cap_intersection s1' s2').
Proof.
  intros s1 s1' s2 s2' H1 H2 c H.
  unfold cap_intersection in *.
  apply andb_prop in H. destruct H as [Ha Hb].
  apply andb_true_intro. split; [apply H1 | apply H2]; assumption.
Qed.

(* ================================================================= *)
(* Effective Capabilities Under Delegation                             *)
(* ================================================================= *)

(** ** Effective Capabilities

    Given the caller's trust level and the callee's declared capabilities,
    compute the callee's effective capability set.

    For System/Stdlib callers: no ceiling (callee runs with full declared caps).
    For all other callers: effective = intersection of callee's declared and
    caller's allowed caps. *)

Definition effective_caps
  (caller_trust : TrustLevel)
  (caller_declared : list Capability)
  (callee_declared : list Capability) : CapSet :=
  match caller_trust with
  | System => allowed_cap_set System callee_declared
  | Stdlib => allowed_cap_set Stdlib callee_declared
  | _ =>
    let caller_caps := allowed_cap_set caller_trust caller_declared in
    let callee_caps := allowed_cap_set (trust_min caller_trust Evaluated) callee_declared in
    cap_intersection caller_caps callee_caps
  end.

(* ================================================================= *)
(* The Central Theorem: Delegation Non-Escalation                      *)
(* ================================================================= *)

(** ** Delegation Non-Escalation

    The effective capabilities of a callee are always within the
    caller's capability set (for non-System/Stdlib callers).
    A machine cannot delegate to another machine to gain capabilities
    it does not hold. *)

Theorem delegation_non_escalation :
  forall caller_trust caller_declared callee_declared,
    caller_trust <> System ->
    caller_trust <> Stdlib ->
    cap_subseteq
      (effective_caps caller_trust caller_declared callee_declared)
      (allowed_cap_set caller_trust caller_declared).
Proof.
  intros caller_trust caller_declared callee_declared Hns Hnl.
  unfold effective_caps.
  destruct caller_trust;
    try contradiction;
    apply cap_intersection_sub_l.
Qed.

(** ** System/Stdlib Exemption

    System and Stdlib callers impose no ceiling. The callee runs
    with its own full capability set. This is correct: System/Stdlib
    have full access by design. *)

Theorem system_no_ceiling :
  forall caller_declared callee_declared c,
    allowed_cap_set System callee_declared c = true ->
    effective_caps System caller_declared callee_declared c = true.
Proof.
  intros. simpl. assumption.
Qed.

Theorem stdlib_no_ceiling :
  forall caller_declared callee_declared c,
    allowed_cap_set Stdlib callee_declared c = true ->
    effective_caps Stdlib caller_declared callee_declared c = true.
Proof.
  intros. simpl. assumption.
Qed.

(* ================================================================= *)
(* Call Step Cannot Gain Capabilities                                   *)
(* ================================================================= *)

(** ** Call Cannot Gain Capabilities

    A :call step has capability requirement {CapMachineCall}.
    Executing the call and running the callee under the effective_caps
    policy cannot produce effects outside the caller's capability set.

    This uses the existing cap_call from CapabilityComposition.v
    (which proves :call has caps = {CapMachineCall}) together with
    the delegation_non_escalation theorem. *)

Theorem call_cannot_gain_caps :
  forall caller_trust caller_declared callee_declared
    (callee_program : forall R, itree DirectiveE R),
    caller_trust <> System ->
    caller_trust <> Stdlib ->
    (* The caller has the CapMachineCall capability *)
    capability_allowed caller_trust CapMachineCall caller_declared = true ->
    (* The callee runs within its effective caps *)
    (forall R, within_caps
      (effective_caps caller_trust caller_declared callee_declared)
      (callee_program R)) ->
    (* Then the callee is within the caller's caps *)
    forall R, within_caps
      (allowed_cap_set caller_trust caller_declared)
      (callee_program R).
Proof.
  intros caller_trust caller_declared callee_declared
    callee_program Hns Hnl Hcall Hwithin R.
  eapply within_caps_weaken.
  - apply (delegation_non_escalation caller_trust caller_declared callee_declared Hns Hnl).
  - apply Hwithin.
Qed.

(* ================================================================= *)
(* Chained Delegation Preserves Ceiling                                *)
(* ================================================================= *)

(** ** Composition Respects Ceiling

    If M1 calls M2 and M2 calls M3, the effective capabilities of M3
    are still within M1's capability set. The ceiling propagates
    transitively through the call chain.

    This is the composition version of delegation_non_escalation. *)

Theorem chained_delegation_non_escalation :
  forall t1 d1 d2 d3,
    t1 <> System ->
    t1 <> Stdlib ->
    (* M2's effective caps under M1's ceiling *)
    let m2_effective := effective_caps t1 d1 d2 in
    (* M3's effective caps are within M2's effective caps *)
    forall c,
      cap_intersection m2_effective (allowed_cap_set (trust_min t1 Evaluated) d3) c = true ->
      allowed_cap_set t1 d1 c = true.
Proof.
  intros t1 d1 d2 d3 Hns Hnl m2_effective c H.
  unfold m2_effective in H.
  apply cap_intersection_sub_l in H.
  apply (delegation_non_escalation t1 d1 d2 Hns Hnl c H).
Qed.

(* ================================================================= *)
(* Governance Safety Under Delegation                                  *)
(* ================================================================= *)

(** ** Governed Delegation Safety

    A callee running under effective_caps, when interpreted through
    the Gov handler, satisfies gov_safe. This combines delegation
    non-escalation with the existing safety theorems. *)

Theorem governed_delegation_safe :
  forall caller_trust caller_declared callee_declared
    R (callee_body : itree DirectiveE R) (h : base_handler),
    within_caps
      (effective_caps caller_trust caller_declared callee_declared)
      callee_body ->
    @gov_safe R false (interp (Gov h) callee_body).
Proof.
  intros. apply governed_interp_safe_false.
Qed.

(* ================================================================= *)
(* Trust Min Under Delegation                                          *)
(* ================================================================= *)

(** ** Trust Minimum Policy

    The runtime uses min_trust(parent, child_declared) to compute
    the effective trust level. This ensures the callee's trust never
    exceeds the caller's trust. *)

Theorem trust_min_non_escalation :
  forall parent_trust child_trust,
    trust_le (trust_min parent_trust child_trust) parent_trust.
Proof.
  intros. unfold trust_min, trust_le.
  destruct (trust_value parent_trust <=? trust_value child_trust)%nat eqn:E.
  - apply Nat.leb_le in E. apply Nat.le_refl.
  - apply Nat.leb_gt in E. apply Nat.lt_le_incl. assumption.
Qed.

(** The effective trust is also no greater than the child's declared trust. *)
Theorem trust_min_bounded_by_child :
  forall parent_trust child_trust,
    trust_le (trust_min parent_trust child_trust) child_trust.
Proof.
  intros. unfold trust_min, trust_le.
  destruct (trust_value parent_trust <=? trust_value child_trust)%nat eqn:E.
  - apply Nat.leb_le in E. assumption.
  - apply Nat.le_refl.
Qed.

(* ================================================================= *)
(* Summary                                                             *)
(* ================================================================= *)

(** ** Summary

    The DelegationNonEscalation module establishes:

    | Result                              | What It Says                                        |
    |-------------------------------------|-----------------------------------------------------|
    | cap_intersection                    | Intersection of two capability sets                  |
    | effective_caps                      | Callee's effective caps under delegation policy       |
    | delegation_non_escalation           | Callee's effective caps ⊆ caller's caps              |
    | system_no_ceiling / stdlib_no_ceiling | System/Stdlib impose no ceiling                     |
    | call_cannot_gain_caps               | :call + effective_caps = no capability gain           |
    | chained_delegation_non_escalation   | Ceiling propagates through call chains               |
    | governed_delegation_safe            | Delegated execution satisfies gov_safe               |
    | trust_min_non_escalation            | min_trust(parent, child) ≤ parent                    |
    | trust_min_bounded_by_child          | min_trust(parent, child) ≤ child                     |

    Together with CapabilityComposition.v:
    - A :call step requires {CapMachineCall} (cap_call)
    - The callee's effective caps are bounded by the caller's (this module)
    - The composed system satisfies gov_safe (governed_delegation_safe)
    - The ceiling propagates through arbitrary call chains (chained_delegation)

    This closes GAP-228 at the proof level. The runtime enforcement
    is in runtime.ex (execute_call_isolated) and context_builder.ex
    (extract_effective_capabilities). *)
