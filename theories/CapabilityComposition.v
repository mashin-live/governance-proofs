(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file.

   The governance architecture formalized in this development is the
   subject of pending U.S. patent applications by Mashin, Inc. The
   MIT license applies to these proof sources; it does not grant
   rights under any patents. *)

(** * CapabilityComposition: Capability-Indexed Composition

    Formalizes how capability requirements compose when programs
    compose. Connects the capability model (TrustSpec.v) with
    the algebraic effect system (EffectAlgebra.v) and categorical
    composition (Category.v, MonoidalCategory.v).

    Key results:
    - Trust levels form a bounded total order (lattice)
    - CapMorphism: morphism bundled with capability requirement
    - Primitive CapMorphisms for code, reason, memory, call
    - Sequential composition: caps = union (from bind)
    - Parallel composition (tensor): caps = union
    - Branch composition: caps = union of branches
    - Capability preservation: code contributes nothing
    - Principal capability: code has minimal (empty) requirement
    - Dual guarantee: within_caps + gov_safe simultaneously

    Dependencies: Prelude, Directives, Governance, Safety,
                  TrustSpec, Category, MonoidalCategory, EffectAlgebra *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.
From MashinGov Require Import Safety.
From MashinGov Require Import TrustSpec.
From MashinGov Require Import Category.
From MashinGov Require Import MonoidalCategory.
From MashinGov Require Import EffectAlgebra.

From Paco Require Import paco.

(* ================================================================= *)
(* CapSet Helpers                                                      *)
(* ================================================================= *)

(** Additional CapSet lemmas for composition proofs. *)

Lemma cap_union_empty_r :
  forall s, cap_subseteq (cap_union s cap_empty) s.
Proof.
  intros s c H. unfold cap_union, cap_empty in H.
  rewrite Bool.orb_false_r in H. exact H.
Qed.

Lemma cap_union_empty_l :
  forall s, cap_subseteq (cap_union cap_empty s) s.
Proof.
  intros s c H. unfold cap_union, cap_empty in H.
  simpl in H. exact H.
Qed.

Lemma cap_union_comm :
  forall s1 s2, cap_subseteq (cap_union s1 s2) (cap_union s2 s1).
Proof.
  intros s1 s2 c H. unfold cap_union in *.
  rewrite Bool.orb_comm. exact H.
Qed.

Lemma cap_union_assoc :
  forall s1 s2 s3,
    cap_subseteq (cap_union (cap_union s1 s2) s3)
                 (cap_union s1 (cap_union s2 s3)).
Proof.
  intros s1 s2 s3 c H. unfold cap_union in *.
  rewrite Bool.orb_assoc. exact H.
Qed.

Lemma cap_union_idem :
  forall s, cap_subseteq (cap_union s s) s.
Proof.
  intros s c H. unfold cap_union in H.
  rewrite Bool.orb_diag in H. exact H.
Qed.

(* ================================================================= *)
(* Trust Lattice                                                       *)
(* ================================================================= *)

(** ** Trust Levels as a Bounded Total Order

    Trust levels are ordered by [trust_value] in TrustSpec.v:
    Untrusted(0) < Tested(1) < Evaluated(2) < Reviewed(3) <
    Stdlib(4) < System(5). Here we make the lattice structure
    explicit. *)

Definition trust_le (t1 t2 : TrustLevel) : Prop :=
  trust_value t1 <= trust_value t2.

Lemma trust_le_refl : forall t, trust_le t t.
Proof. intros. unfold trust_le. apply Nat.le_refl. Qed.

Lemma trust_le_trans :
  forall t1 t2 t3,
    trust_le t1 t2 -> trust_le t2 t3 -> trust_le t1 t3.
Proof.
  intros t1 t2 t3 H1 H2. unfold trust_le in *.
  eapply Nat.le_trans; eassumption.
Qed.

Lemma trust_value_injective :
  forall t1 t2, trust_value t1 = trust_value t2 -> t1 = t2.
Proof.
  destruct t1; destruct t2; simpl; intro H;
    try reflexivity; discriminate.
Qed.

Lemma trust_le_antisym :
  forall t1 t2, trust_le t1 t2 -> trust_le t2 t1 -> t1 = t2.
Proof.
  intros t1 t2 H1 H2. apply trust_value_injective.
  unfold trust_le in *. apply Nat.le_antisymm; assumption.
Qed.

Lemma trust_le_total :
  forall t1 t2, trust_le t1 t2 \/ trust_le t2 t1.
Proof.
  intros t1 t2. unfold trust_le.
  destruct (le_lt_dec (trust_value t1) (trust_value t2)).
  - left. exact l.
  - right. apply Nat.lt_le_incl. exact l.
Qed.

Lemma trust_bottom : forall t, trust_le Untrusted t.
Proof. destruct t; unfold trust_le; simpl; auto with arith. Qed.

Lemma trust_top : forall t, trust_le t System.
Proof. destruct t; unfold trust_le; simpl; auto with arith. Qed.

(** Join (least upper bound) and meet (greatest lower bound). *)

Definition trust_max (t1 t2 : TrustLevel) : TrustLevel :=
  if Nat.leb (trust_value t1) (trust_value t2) then t2 else t1.

Definition trust_min (t1 t2 : TrustLevel) : TrustLevel :=
  if Nat.leb (trust_value t1) (trust_value t2) then t1 else t2.

Lemma trust_max_le_l : forall t1 t2,
  trust_le t1 (trust_max t1 t2).
Proof.
  intros. unfold trust_max, trust_le.
  destruct (Nat.leb (trust_value t1) (trust_value t2)) eqn:E.
  - apply Nat.leb_le. exact E.
  - apply Nat.le_refl.
Qed.

Lemma trust_max_le_r : forall t1 t2,
  trust_le t2 (trust_max t1 t2).
Proof.
  intros. unfold trust_max, trust_le.
  destruct (Nat.leb (trust_value t1) (trust_value t2)) eqn:E.
  - apply Nat.le_refl.
  - apply Nat.leb_gt in E. apply Nat.lt_le_incl. exact E.
Qed.

Lemma trust_max_least :
  forall t1 t2 t3,
    trust_le t1 t3 -> trust_le t2 t3 ->
    trust_le (trust_max t1 t2) t3.
Proof.
  intros. unfold trust_max, trust_le in *.
  destruct (Nat.leb (trust_value t1) (trust_value t2));
    assumption.
Qed.

Lemma trust_min_le_l : forall t1 t2,
  trust_le (trust_min t1 t2) t1.
Proof.
  intros. unfold trust_min, trust_le.
  destruct (Nat.leb (trust_value t1) (trust_value t2)) eqn:E.
  - apply Nat.le_refl.
  - apply Nat.leb_gt in E. apply Nat.lt_le_incl. exact E.
Qed.

Lemma trust_min_le_r : forall t1 t2,
  trust_le (trust_min t1 t2) t2.
Proof.
  intros. unfold trust_min, trust_le.
  destruct (Nat.leb (trust_value t1) (trust_value t2)) eqn:E.
  - apply Nat.leb_le. exact E.
  - apply Nat.le_refl.
Qed.

Lemma trust_min_greatest :
  forall t1 t2 t3,
    trust_le t3 t1 -> trust_le t3 t2 ->
    trust_le t3 (trust_min t1 t2).
Proof.
  intros. unfold trust_min, trust_le in *.
  destruct (Nat.leb (trust_value t1) (trust_value t2));
    assumption.
Qed.

(* ================================================================= *)
(* CapMorphism: Capability-Indexed Morphisms                           *)
(* ================================================================= *)

(** ** CapMorphism

    A capability-indexed morphism bundles a program (mashin_morphism)
    with its capability requirement (CapSet) and a proof that the
    program stays within those capabilities.

    This is the type-theoretic statement of "this program needs
    exactly these permissions to run." *)

Record CapMorphism (A B : Type) := mk_cap_morphism {
  cm_morph : mashin_morphism A B;
  cm_caps : CapSet;
  cm_within : forall a, within_caps cm_caps (cm_morph a)
}.

Arguments mk_cap_morphism {A B}.
Arguments cm_morph {A B}.
Arguments cm_caps {A B}.
Arguments cm_within {A B}.

(* ================================================================= *)
(* Primitive CapMorphisms                                              *)
(* ================================================================= *)

(** ** The Four Primitives as CapMorphisms

    Each primitive has a known, tight capability profile:
    - code: empty (pure computation, no effects)
    - reason: {CapComputeLLMReason}
    - memory: {CapMemory}
    - call: {CapMachineCall} *)

Definition cap_code {A B : Type} (f : A -> B) : CapMorphism A B :=
  mk_cap_morphism (code_morphism f) cap_empty (code_within_empty A B f).

Definition cap_reason {A B : Type}
  (build : A -> LLMCallParams)
  (extract : LLMResponse -> B) : CapMorphism A B :=
  mk_cap_morphism
    (reason_morphism build extract)
    (cap_singleton CapComputeLLMReason)
    (reason_within_llm A B build extract).

Definition cap_memory {A B : Type}
  (build : A -> MemoryOpParams)
  (extract : MemoryResult -> B) : CapMorphism A B :=
  mk_cap_morphism
    (memory_morphism build extract)
    (cap_singleton CapMemory)
    (memory_within_mem A B build extract).

Definition cap_call {A B : Type}
  (build : A -> CallMachineParams)
  (extract : CallMachineResult -> B) : CapMorphism A B :=
  mk_cap_morphism
    (call_morphism build extract)
    (cap_singleton CapMachineCall)
    (call_within_call A B build extract).

(** Identity CapMorphism: mashin_id with empty caps. *)
Definition cap_id {A : Type} : CapMorphism A A.
Proof.
  refine (mk_cap_morphism mashin_id cap_empty _).
  intro a. unfold mashin_id. apply ret_within_caps.
Defined.

(* ================================================================= *)
(* Sequential Composition                                              *)
(* ================================================================= *)

(** ** Sequential Composition of CapMorphisms

    The capability requirement of a sequential composition is
    the union of the component requirements. This follows from
    [bind_within_caps] (EffectAlgebra.v). *)

Definition cap_seq_compose {A B C : Type}
  (f : CapMorphism A B) (g : CapMorphism B C) : CapMorphism A C.
Proof.
  refine (mk_cap_morphism
    (cm_morph f >>> cm_morph g)
    (cap_union (cm_caps f) (cm_caps g))
    _).
  intro a. apply seq_comp_caps.
  - apply (cm_within f).
  - intro b. apply (cm_within g).
Defined.

(** The caps of the composition are exactly the union. *)
Lemma cap_seq_compose_caps :
  forall A B C (f : CapMorphism A B) (g : CapMorphism B C),
    cm_caps (cap_seq_compose f g) = cap_union (cm_caps f) (cm_caps g).
Proof. reflexivity. Qed.

(* ================================================================= *)
(* Parallel Composition (Tensor)                                       *)
(* ================================================================= *)

(** ** Tensor Composition of CapMorphisms

    The tensor product [f ⊗ g] runs f then g (independent
    sequential). Its capability requirement is the union of
    the component requirements.

    Proof: [f ⊗ g] unfolds to [bind (f a) (fun b => bind (g c)
    (fun d => ret (b,d)))]. Apply [bind_within_caps] twice,
    noting that [ret] is within [cap_empty]. *)

Theorem tensor_within_caps :
  forall (A B C D : Type) (caps1 caps2 : CapSet)
    (f : mashin_morphism A B) (g : mashin_morphism C D)
    (a : A) (c : C),
    within_caps caps1 (f a) ->
    within_caps caps2 (g c) ->
    within_caps (cap_union caps1 caps2) ((f ⊗ g) (a, c)).
Proof.
  intros A B C D caps1 caps2 f g a c Hf Hg.
  unfold mashin_tensor.
  apply bind_within_caps.
  - exact Hf.
  - intro b.
    eapply within_caps_weaken.
    + apply cap_union_empty_r.
    + apply bind_within_caps.
      * exact Hg.
      * intro d. apply ret_within_caps.
Qed.

Definition cap_tensor {A B C D : Type}
  (f : CapMorphism A B) (g : CapMorphism C D)
  : CapMorphism (A * C) (B * D).
Proof.
  refine (mk_cap_morphism
    (cm_morph f ⊗ cm_morph g)
    (cap_union (cm_caps f) (cm_caps g))
    _).
  intros [a c].
  apply tensor_within_caps.
  - apply (cm_within f).
  - apply (cm_within g).
Defined.

Lemma cap_tensor_caps :
  forall A B C D (f : CapMorphism A B) (g : CapMorphism C D),
    cm_caps (cap_tensor f g) = cap_union (cm_caps f) (cm_caps g).
Proof. reflexivity. Qed.

(* ================================================================= *)
(* Branch Composition                                                  *)
(* ================================================================= *)

(** ** Branch Composition

    Branching runs one of two morphisms depending on a predicate.
    The capability requirement is the union of both branches,
    since either branch may execute. *)

Lemma branch_within_caps :
  forall (A B : Type) (caps1 caps2 : CapSet)
    (pred : A -> bool)
    (on_true : mashin_morphism A B)
    (on_false : mashin_morphism A B) (a : A),
    within_caps caps1 (on_true a) ->
    within_caps caps2 (on_false a) ->
    within_caps (cap_union caps1 caps2) (mashin_branch pred on_true on_false a).
Proof.
  intros. unfold mashin_branch. destruct (pred a).
  - eapply within_caps_weaken.
    + apply cap_union_subseteq_l.
    + exact H.
  - eapply within_caps_weaken.
    + apply cap_union_subseteq_r.
    + exact H0.
Qed.

Definition cap_branch {A B : Type}
  (pred : A -> bool)
  (on_true : CapMorphism A B)
  (on_false : CapMorphism A B) : CapMorphism A B.
Proof.
  refine (mk_cap_morphism
    (mashin_branch pred (cm_morph on_true) (cm_morph on_false))
    (cap_union (cm_caps on_true) (cm_caps on_false))
    _).
  intro a. apply branch_within_caps.
  - apply (cm_within on_true).
  - apply (cm_within on_false).
Defined.

(* ================================================================= *)
(* Capability Preservation                                             *)
(* ================================================================= *)

(** ** Capability Preservation Theorems

    Composition never escalates beyond the union of component
    capabilities. Code contributes nothing to the requirement. *)

(** Code on the left contributes no capabilities. *)
Theorem code_contributes_nothing_left :
  forall A B C (f : A -> B) (g : CapMorphism B C),
    cap_subseteq
      (cm_caps (cap_seq_compose (cap_code f) g))
      (cm_caps g).
Proof.
  intros. simpl. apply cap_union_empty_l.
Qed.

(** Code on the right contributes no capabilities. *)
Theorem code_contributes_nothing_right :
  forall A B C (f : CapMorphism A B) (g : B -> C),
    cap_subseteq
      (cm_caps (cap_seq_compose f (cap_code g)))
      (cm_caps f).
Proof.
  intros. simpl. apply cap_union_empty_r.
Qed.

(** Composing two morphisms with the same caps stays within
    those caps (no escalation). *)
Theorem same_caps_no_escalation :
  forall A B C (f : CapMorphism A B) (g : CapMorphism B C),
    cm_caps f = cm_caps g ->
    cap_subseteq
      (cm_caps (cap_seq_compose f g))
      (cm_caps f).
Proof.
  intros A B C f g Heq. simpl. rewrite Heq.
  apply cap_union_idem.
Qed.

(** Sequential composition capabilities are bounded by the union. *)
Theorem seq_caps_bounded :
  forall A B C (f : CapMorphism A B) (g : CapMorphism B C) caps,
    cap_subseteq (cm_caps f) caps ->
    cap_subseteq (cm_caps g) caps ->
    cap_subseteq (cm_caps (cap_seq_compose f g)) caps.
Proof.
  intros. simpl. apply cap_union_least; assumption.
Qed.

(** Tensor composition capabilities are bounded by the union. *)
Theorem tensor_caps_bounded :
  forall A B C D (f : CapMorphism A B) (g : CapMorphism C D) caps,
    cap_subseteq (cm_caps f) caps ->
    cap_subseteq (cm_caps g) caps ->
    cap_subseteq (cm_caps (cap_tensor f g)) caps.
Proof.
  intros. simpl. apply cap_union_least; assumption.
Qed.

(* ================================================================= *)
(* Trust-Capability Connection                                         *)
(* ================================================================= *)

(** ** Trust-Based Capability Sets

    Connects the trust level model (TrustSpec.v) with capability
    sets (EffectAlgebra.v). The [allowed_cap_set] function converts
    a trust level and declared capabilities into a CapSet.

    Note: trust-capability monotonicity is NOT unconditional across
    all levels. Tested allows a fixed set of 4 capabilities while
    Evaluated/Reviewed check the declared list, so a machine could
    lose capabilities when promoted from Tested to Evaluated if its
    declaration is restrictive. Monotonicity holds unconditionally
    to System/Stdlib (which allow everything). *)

Definition allowed_cap_set
  (tl : TrustLevel) (declared : list Capability) : CapSet :=
  fun cap => capability_allowed tl cap declared.

(** System trust allows all capabilities. *)
Lemma system_allows_all_caps :
  forall declared c,
    allowed_cap_set System declared c = true.
Proof.
  intros. unfold allowed_cap_set. apply system_allows_all.
Qed.

(** Stdlib trust allows all capabilities. *)
Lemma stdlib_allows_all_caps :
  forall declared c,
    allowed_cap_set Stdlib declared c = true.
Proof.
  intros. unfold allowed_cap_set. apply stdlib_allows_all.
Qed.

(** Any program runs at System trust: System allows everything. *)
Corollary system_within_any :
  forall R (declared : list Capability) (t : itree DirectiveE R),
    within_caps (allowed_cap_set System declared) t.
Proof.
  intros. eapply within_caps_weaken.
  - intros c _. apply system_allows_all_caps.
  - apply within_full.
Qed.

(** Any program runs at Stdlib trust. *)
Corollary stdlib_within_any :
  forall R (declared : list Capability) (t : itree DirectiveE R),
    within_caps (allowed_cap_set Stdlib declared) t.
Proof.
  intros. eapply within_caps_weaken.
  - intros c _. apply stdlib_allows_all_caps.
  - apply within_full.
Qed.

(** Untrusted trust allows only LLM capability. *)
Lemma untrusted_only_llm :
  forall declared,
    cap_subseteq
      (allowed_cap_set Untrusted declared)
      (cap_singleton CapComputeLLMReason).
Proof.
  intros declared c H. unfold allowed_cap_set in H.
  unfold cap_singleton.
  destruct c; simpl in *; try discriminate; auto.
Qed.

(** Monotonicity: any trust level's caps are within System's. *)
Theorem trust_monotone_to_system :
  forall tl declared,
    cap_subseteq (allowed_cap_set tl declared)
                 (allowed_cap_set System declared).
Proof.
  intros tl declared c _. apply system_allows_all_caps.
Qed.

(* ================================================================= *)
(* Principal Capability                                                *)
(* ================================================================= *)

(** ** Principal Capability

    A CapMorphism has PRINCIPAL capabilities if its declared cap
    set is minimal: any cap set that works must include the
    declared caps.

    This is the type-theoretic version of "this is the machine's
    exact capability footprint." *)

Definition is_principal {A B : Type} (cm : CapMorphism A B) : Prop :=
  forall caps',
    (forall a, within_caps caps' (cm_morph cm a)) ->
    cap_subseteq (cm_caps cm) caps'.

(** Code morphisms have principal capabilities: cap_empty is
    the smallest CapSet, so any working caps trivially include it. *)
Theorem code_principal :
  forall A B (f : A -> B), is_principal (cap_code f).
Proof.
  intros A B f caps' _. simpl. apply cap_empty_subseteq.
Qed.

(** Identity has principal capabilities. *)
Theorem id_principal :
  forall A, is_principal (@cap_id A).
Proof.
  intros A caps' _. simpl. apply cap_empty_subseteq.
Qed.

(* ================================================================= *)
(* Dual Guarantee                                                      *)
(* ================================================================= *)

(** ** Dual Guarantee: Capabilities + Governance

    Any CapMorphism, when interpreted through a governed handler,
    satisfies BOTH the static capability bound AND the dynamic
    governance safety predicate simultaneously.

    This is the complete picture: capabilities tell you WHAT the
    program does; governance tells you it PASSES THROUGH governance
    before doing it. *)

Theorem cap_morphism_governed :
  forall A B (cm : CapMorphism A B)
    (h : base_handler) (a : A),
    within_caps (cm_caps cm) (cm_morph cm a) /\
    @gov_safe B false (interp (Gov h) (cm_morph cm a)).
Proof.
  intros. split.
  - apply cm_within.
  - apply governed_interp_safe_false.
Qed.

(** Tensor composition preserves the dual guarantee. *)
Theorem tensor_dual_guarantee :
  forall A B C D
    (f : CapMorphism A B) (g : CapMorphism C D)
    (h : base_handler) (a : A) (c : C),
    within_caps (cap_union (cm_caps f) (cm_caps g))
      ((cm_morph f ⊗ cm_morph g) (a, c)) /\
    @gov_safe (B * D) false
      (interp (Gov h) ((cm_morph f ⊗ cm_morph g) (a, c))).
Proof.
  intros. split.
  - apply tensor_within_caps; apply cm_within.
  - apply governed_interp_safe_false.
Qed.

(** Sequential composition preserves the dual guarantee. *)
Theorem seq_dual_guarantee :
  forall A B C
    (f : CapMorphism A B) (g : CapMorphism B C)
    (h : base_handler) (a : A),
    within_caps (cap_union (cm_caps f) (cm_caps g))
      ((cm_morph f >>> cm_morph g) a) /\
    @gov_safe C false
      (interp (Gov h) ((cm_morph f >>> cm_morph g) a)).
Proof.
  intros. split.
  - apply seq_comp_caps; [apply cm_within | intro; apply cm_within].
  - apply governed_interp_safe_false.
Qed.

(* ================================================================= *)
(* Summary                                                             *)
(* ================================================================= *)

(** ** Summary

    The CapabilityComposition module establishes:

    | Result                         | What It Says                              |
    |--------------------------------|-------------------------------------------|
    | trust_le                       | Trust levels form a bounded total order    |
    | trust_max / trust_min          | Join and meet on trust levels              |
    | CapMorphism                    | Morphism + capability requirement + proof  |
    | cap_code/reason/memory/call    | Primitives as CapMorphisms                 |
    | cap_seq_compose                | Sequential composition: caps = union       |
    | tensor_within_caps             | Tensor composition: caps = union           |
    | cap_tensor                     | Tensor as CapMorphism                      |
    | cap_branch                     | Branch: caps = union of branches           |
    | code_contributes_nothing_*     | Code adds zero to capability requirement   |
    | same_caps_no_escalation        | Same caps compose without escalation       |
    | allowed_cap_set                | Trust level -> CapSet conversion           |
    | system_within_any              | System trust runs any program              |
    | untrusted_only_llm             | Untrusted allows only LLM                 |
    | is_principal / code_principal  | Code has minimal (empty) requirement       |
    | cap_morphism_governed          | Dual: within_caps AND gov_safe             |
    | tensor/seq_dual_guarantee      | Dual guarantee for compositions            |

    This completes Phase 4 of the formal algebra plan:
    capability-indexed composition connecting the effect system
    (Phase 3) with the categorical structure (Phase 2) and
    trust model (TrustSpec.v). *)
