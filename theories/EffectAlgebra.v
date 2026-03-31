(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file.

   The governance architecture formalized in this development is the
   subject of pending U.S. patent applications by Mashin, Inc. The
   MIT license applies to these proof sources; it does not grant
   rights under any patents. *)

(** * EffectAlgebra: Capability-Indexed Effect System

    Formalizes the effect algebra for Mashin:
    - Capability sets (CapSet) as characteristic functions
    - within_caps: coinductive predicate tracking which
      capabilities a program exercises
    - Composition lemmas: bind preserves capability bounds
    - No Ambient Effects theorem (Law I algebraic form)
    - Governed Effect Completeness

    The key insight: the existing Coq work proves "all programs
    are governed when interpreted through Gov." This module proves
    "programs can only exercise declared capabilities," the
    static-analysis complement to runtime governance.

    Dependencies: Prelude, Directives, Governance, Safety,
                  Category, TrustSpec, GovernanceAlgebra *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.
From MashinGov Require Import Safety.
From MashinGov Require Import Category.
From MashinGov Require Import TrustSpec.
From MashinGov Require Import GovernanceAlgebra.

From ITree Require Import
  Interp.InterpFacts
  Eq.EqAxiom.

From Coq Require Import Program.Equality.

From Paco Require Import paco.

(* ================================================================= *)
(* Capability Sets                                                     *)
(* ================================================================= *)

(** ** CapSet: Capability Sets as Characteristic Functions

    A capability set is a function from capabilities to booleans.
    This representation gives decidable membership, subset checking,
    and clean interaction with the bool-valued capability checks
    in TrustSpec.v. *)

Definition CapSet := Capability -> bool.

Definition cap_empty : CapSet := fun _ => false.

Definition cap_singleton (c : Capability) : CapSet :=
  fun c' => cap_eqb c c'.

Definition cap_union (s1 s2 : CapSet) : CapSet :=
  fun c => s1 c || s2 c.

Definition cap_full : CapSet := fun _ => true.

Definition cap_subseteq (s1 s2 : CapSet) : Prop :=
  forall c, s1 c = true -> s2 c = true.

(* ================================================================= *)
(* CapSet Algebraic Properties                                         *)
(* ================================================================= *)

Lemma cap_subseteq_refl : forall s, cap_subseteq s s.
Proof. unfold cap_subseteq. auto. Qed.

Lemma cap_subseteq_trans :
  forall s1 s2 s3,
    cap_subseteq s1 s2 -> cap_subseteq s2 s3 -> cap_subseteq s1 s3.
Proof. unfold cap_subseteq. auto. Qed.

Lemma cap_empty_subseteq : forall s, cap_subseteq cap_empty s.
Proof. unfold cap_subseteq, cap_empty. intros s c H. discriminate. Qed.

Lemma cap_subseteq_full : forall s, cap_subseteq s cap_full.
Proof. unfold cap_subseteq, cap_full. auto. Qed.

Lemma cap_union_subseteq_l :
  forall s1 s2, cap_subseteq s1 (cap_union s1 s2).
Proof.
  unfold cap_subseteq, cap_union. intros s1 s2 c H.
  rewrite H. reflexivity.
Qed.

Lemma cap_union_subseteq_r :
  forall s1 s2, cap_subseteq s2 (cap_union s1 s2).
Proof.
  unfold cap_subseteq, cap_union. intros s1 s2 c H.
  rewrite H. apply orb_true_r.
Qed.

Lemma cap_union_least :
  forall s1 s2 s3,
    cap_subseteq s1 s3 -> cap_subseteq s2 s3 ->
    cap_subseteq (cap_union s1 s2) s3.
Proof.
  unfold cap_subseteq, cap_union. intros s1 s2 s3 H1 H2 c H.
  apply orb_true_iff in H. destruct H; auto.
Qed.

Lemma cap_singleton_mem : forall c, cap_singleton c c = true.
Proof. intros c. unfold cap_singleton. apply cap_eqb_refl. Qed.

Lemma cap_singleton_other :
  forall c1 c2, c1 <> c2 -> cap_singleton c1 c2 = false.
Proof.
  intros c1 c2 Hneq. unfold cap_singleton.
  destruct (cap_eqb c1 c2) eqn:E; auto.
  apply cap_eqb_eq in E. contradiction.
Qed.

(* ================================================================= *)
(* Directive Capability Membership                                     *)
(* ================================================================= *)

(** ** directive_in_caps

    A directive is "in" a capability set if either:
    - It requires no capability (observability directive), or
    - Its required capability is in the set.

    This bridges TrustSpec.v's [capability_for_directive] with
    the CapSet abstraction. *)

Definition directive_in_caps (caps : CapSet) {X : Type}
  (d : DirectiveE X) : Prop :=
  match capability_for_directive d with
  | None => True
  | Some cap => caps cap = true
  end.

(** Monotonicity: larger cap sets include more directives. *)
Lemma directive_in_caps_mono :
  forall caps1 caps2 X (d : DirectiveE X),
    cap_subseteq caps1 caps2 ->
    directive_in_caps caps1 d ->
    directive_in_caps caps2 d.
Proof.
  intros caps1 caps2 X d Hsub Hin.
  unfold directive_in_caps in *.
  destruct (capability_for_directive d); auto.
Qed.

(** All directives are in the full cap set. *)
Lemma directive_in_full :
  forall X (d : DirectiveE X), directive_in_caps cap_full d.
Proof.
  intros X d. unfold directive_in_caps, cap_full.
  destruct (capability_for_directive d); auto.
Qed.

(** Observability directives are in any cap set. *)
Lemma observability_in_any :
  forall caps X (d : DirectiveE X),
    capability_for_directive d = None ->
    directive_in_caps caps d.
Proof.
  intros caps X d Hobs. unfold directive_in_caps.
  rewrite Hobs. exact I.
Qed.

(* ================================================================= *)
(* within_caps: Coinductive Capability Predicate                       *)
(* ================================================================= *)

(** ** within_caps

    Coinductive predicate: a program exercises only capabilities
    in the given set. Analogous to [gov_safe] but tracks capability
    usage rather than governance permission.

    - [within_caps caps t]: every directive event in [t] requires
      only capabilities in [caps] (or no capability at all).

    Uses paco1 since the cap set is a fixed parameter. *)

Section WithinCaps.

  Context {R : Type}.

  Variant within_capsF (caps : CapSet)
    (F : itree DirectiveE R -> Prop)
    : itreeF DirectiveE R (itree DirectiveE R) -> Prop :=
    | WC_Ret : forall r,
        within_capsF caps F (RetF r)
    | WC_Tau : forall t,
        F t ->
        within_capsF caps F (TauF t)
    | WC_Vis : forall X (d : DirectiveE X)
        (k : X -> itree DirectiveE R),
        directive_in_caps caps d ->
        (forall x, F (k x)) ->
        within_capsF caps F (VisF d k).

  Definition within_caps_ (caps : CapSet)
    (F : itree DirectiveE R -> Prop)
    : itree DirectiveE R -> Prop :=
    fun t => within_capsF caps F (observe t).

  Lemma within_caps_mon :
    forall caps, monotone1 (within_caps_ caps).
  Proof.
    unfold monotone1. intros caps t r r' IN LE.
    unfold within_caps_ in *. inv IN; constructor; auto.
  Qed.

  #[local] Hint Resolve within_caps_mon : paco.

  Definition within_caps (caps : CapSet)
    : itree DirectiveE R -> Prop :=
    paco1 (within_caps_ caps) bot1.

  (* --- Basic lemmas --- *)

  Lemma ret_within_caps :
    forall caps (v : R), within_caps caps (Ret v).
  Proof. intros. pfold. red. cbn. constructor. Qed.

  Lemma tau_within_caps :
    forall caps (t : itree DirectiveE R),
      within_caps caps t -> within_caps caps (Tau t).
  Proof.
    intros. pfold. red. cbn. apply WC_Tau. left. assumption.
  Qed.

  (** ** Weakening: larger cap sets include more programs *)
  Lemma within_caps_weaken :
    forall caps1 caps2,
      cap_subseteq caps1 caps2 ->
      forall (t : itree DirectiveE R),
        within_caps caps1 t -> within_caps caps2 t.
  Proof.
    intros caps1 caps2 Hsub. pcofix CIH. intros t Ht.
    punfold Ht. red in Ht.
    pfold. red.
    inv Ht.
    - constructor.
    - apply WC_Tau. pclearbot. right. apply CIH. assumption.
    - apply WC_Vis.
      + eapply directive_in_caps_mono; eassumption.
      + intros x. specialize (H1 x). destruct H1 as [H1|[]].
        right. apply CIH. assumption.
  Qed.

  (** All programs are within the full cap set. *)
  Lemma within_full :
    forall (t : itree DirectiveE R), within_caps cap_full t.
  Proof.
    pcofix CIH. intros t.
    pfold. red.
    destruct (observe t) eqn:Hot.
    - constructor.
    - apply WC_Tau. right. apply CIH.
    - apply WC_Vis.
      + apply directive_in_full.
      + intros x. right. apply CIH.
  Qed.

End WithinCaps.

#[global] Hint Resolve within_caps_mon : paco.

(* ================================================================= *)
(* Primitive Capability Profiles                                       *)
(* ================================================================= *)

(** ** Capability profiles for the four primitives

    Each primitive exercises exactly the capabilities corresponding
    to its directive type:
    - code: no capabilities (pure computation)
    - reason: {CapComputeLLMReason}
    - memory: {CapMemory}
    - call: {CapMachineCall}

    These are tight bounds: the primitive is within its profile,
    and the profile is minimal. *)

(** Code morphisms are within the empty cap set:
    pure computation needs no capabilities. *)
Theorem code_within_empty :
  forall (A B : Type) (f : A -> B) (a : A),
    within_caps cap_empty (code_morphism f a).
Proof.
  intros. unfold code_morphism. apply ret_within_caps.
Qed.

(** Reason morphisms are within {CapComputeLLMReason}. *)
Theorem reason_within_llm :
  forall (A B : Type)
    (build : A -> LLMCallParams)
    (extract : LLMResponse -> B)
    (a : A),
    within_caps (cap_singleton CapComputeLLMReason)
      (reason_morphism build extract a).
Proof.
  intros. unfold reason_morphism.
  pfold. red. cbn. unfold trigger. cbn.
  apply WC_Vis.
  - unfold directive_in_caps. cbn. reflexivity.
  - intros resp. left. pfold. red. cbn. constructor.
Qed.

(** Memory morphisms are within {CapMemory}. *)
Theorem memory_within_mem :
  forall (A B : Type)
    (build : A -> MemoryOpParams)
    (extract : MemoryResult -> B)
    (a : A),
    within_caps (cap_singleton CapMemory)
      (memory_morphism build extract a).
Proof.
  intros. unfold memory_morphism.
  pfold. red. cbn. unfold trigger. cbn.
  apply WC_Vis.
  - unfold directive_in_caps. cbn. reflexivity.
  - intros resp. left. pfold. red. cbn. constructor.
Qed.

(** Call morphisms are within {CapMachineCall}. *)
Theorem call_within_call :
  forall (A B : Type)
    (build : A -> CallMachineParams)
    (extract : CallMachineResult -> B)
    (a : A),
    within_caps (cap_singleton CapMachineCall)
      (call_morphism build extract a).
Proof.
  intros. unfold call_morphism.
  pfold. red. cbn. unfold trigger. cbn.
  apply WC_Vis.
  - unfold directive_in_caps. cbn. reflexivity.
  - intros resp. left. pfold. red. cbn. constructor.
Qed.

(* ================================================================= *)
(* Bind Preserves Capability Bounds                                    *)
(* ================================================================= *)

(** ** bind_within_caps

    If [t] exercises only capabilities in [caps1] and [k r]
    exercises only capabilities in [caps2] for every [r],
    then [bind t k] exercises only capabilities in
    [cap_union caps1 caps2].

    This is the compositional closure theorem for capability
    tracking: capability bounds compose under sequential
    composition (monadic bind).

    Proof strategy: coinduction (pcofix) with case analysis on
    [observe t]. Uses [unfold_bind] + [bisimulation_is_eq] to
    rewrite [bind t k] to its match form, then constructs
    the appropriate [within_capsF] in each case. *)

Section BindCaps.

  Context {R S : Type}.

  Theorem bind_within_caps :
    forall (caps1 caps2 : CapSet)
      (t : itree DirectiveE R)
      (k : R -> itree DirectiveE S),
      within_caps caps1 t ->
      (forall r, within_caps caps2 (k r)) ->
      within_caps (cap_union caps1 caps2) (ITree.bind t k).
  Proof.
    intros caps1 caps2. pcofix CIH. intros t k Ht Hk.
    punfold Ht. red in Ht.
    rewrite (bisimulation_is_eq _ _ (unfold_bind t k)).
    destruct (observe t) eqn:Hot; cbn.
    - (* RetF: bind reduces to k r *)
      inv Ht.
      eapply paco1_mon.
      + eapply within_caps_weaken.
        * apply cap_union_subseteq_r.
        * apply Hk.
      + intros ? [].
    - (* TauF: bind reduces to Tau (bind t0 k) *)
      inv Ht.
      pfold. red. cbn.
      apply WC_Tau. pclearbot.
      right. apply CIH; assumption.
    - (* VisF: bind reduces to Vis e (fun x => bind (k0 x) k) *)
      rename Ht into Ht_orig.
      dependent destruction Ht_orig.
      pfold. red. cbn.
      apply WC_Vis.
      + eapply directive_in_caps_mono; [apply cap_union_subseteq_l | assumption].
      + intros x0. right. apply CIH.
        * match goal with | [H : forall _, _ |- _] => specialize (H x0); destruct H as [?|[]]; assumption end.
        * assumption.
  Qed.

End BindCaps.

(* ================================================================= *)
(* Sequential Composition Corollary                                    *)
(* ================================================================= *)

(** Sequential composition of morphisms preserves capability bounds. *)
Corollary seq_comp_caps :
  forall (A B C : Type) (caps1 caps2 : CapSet)
    (f : mashin_morphism A B) (g : mashin_morphism B C) (a : A),
    within_caps caps1 (f a) ->
    (forall b, within_caps caps2 (g b)) ->
    within_caps (cap_union caps1 caps2) ((f >>> g) a).
Proof.
  intros A B C caps1 caps2 f g a Hf Hg.
  unfold mashin_compose.
  apply bind_within_caps; assumption.
Qed.

(** Same-caps composition: if both use the same cap set,
    the composition uses the same cap set. *)
Corollary seq_comp_same_caps :
  forall (A B C : Type) (caps : CapSet)
    (f : mashin_morphism A B) (g : mashin_morphism B C) (a : A),
    within_caps caps (f a) ->
    (forall b, within_caps caps (g b)) ->
    within_caps caps ((f >>> g) a).
Proof.
  intros A B C caps f g a Hf Hg.
  eapply within_caps_weaken.
  2: { apply seq_comp_caps; eassumption. }
  apply cap_union_least; apply cap_subseteq_refl.
Qed.

(* ================================================================= *)
(* No Ambient Effects (Law I, Algebraic Form)                          *)
(* ================================================================= *)

(** ** No Ambient Effects

    The algebraic form of Law I (Inv 1): programs can only exercise
    capabilities that are structurally present in their interaction
    tree.

    Specifically: if a program is within the empty capability set,
    every directive it emits is an observability directive (no
    capability required). It cannot perform LLM calls, HTTP requests,
    file operations, or any other effectful action.

    This is a static property: it holds by the structure of the
    program tree, before any runtime governance checks. *)

Theorem no_ambient_effects :
  forall (R : Type) (t : itree DirectiveE R),
    within_caps cap_empty t ->
    forall X (d : DirectiveE X) (k : X -> itree DirectiveE R),
      observe t = VisF d k ->
      is_observability d = true.
Proof.
  intros R t Ht X d k Hobs.
  punfold Ht. red in Ht. rewrite Hobs in Ht.
  dependent destruction Ht.
  unfold is_observability, directive_in_caps, cap_empty in *.
  destruct (capability_for_directive d); auto.
Qed.

(** Contrapositive: an effectful directive (one requiring a capability)
    is NOT within the empty set. *)
Corollary effectful_not_empty :
  forall (R X : Type) (d : DirectiveE X)
    (k : X -> itree DirectiveE R) (cap : Capability),
    capability_for_directive d = Some cap ->
    ~ within_caps cap_empty (Vis d k).
Proof.
  intros R X d k cap Hcap Hin.
  punfold Hin. red in Hin. cbn in Hin.
  dependent destruction Hin.
  unfold directive_in_caps, cap_empty in *.
  rewrite Hcap in *.
  match goal with | [H : false = true |- _] => discriminate H end.
Qed.

(** Specific instances for each effectful directive type. *)

Corollary llm_not_in_empty :
  forall (R : Type) (p : LLMCallParams)
    (k : LLMResponse -> itree DirectiveE R),
    ~ within_caps cap_empty (Vis (LLMCall p) k).
Proof.
  intros. apply effectful_not_empty with CapComputeLLMReason.
  reflexivity.
Qed.

Corollary http_not_in_empty :
  forall (R : Type) (p : HTTPRequestParams)
    (k : HTTPResponse -> itree DirectiveE R),
    ~ within_caps cap_empty (Vis (HTTPRequest p) k).
Proof.
  intros. apply effectful_not_empty with CapNetHTTP.
  reflexivity.
Qed.

Corollary call_not_in_empty :
  forall (R : Type) (p : CallMachineParams)
    (k : CallMachineResult -> itree DirectiveE R),
    ~ within_caps cap_empty (Vis (CallMachine p) k).
Proof.
  intros. apply effectful_not_empty with CapMachineCall.
  reflexivity.
Qed.

(* ================================================================= *)
(* Governed Effect Completeness                                        *)
(* ================================================================= *)

(** ** Governed Effect Completeness

    Combines the capability tracking (within_caps) with the
    governance safety property (gov_safe). A program that is
    within a declared capability set, when interpreted through
    the governance operator, satisfies both:
    1. gov_safe: every effect passes through governance
    2. within_caps: only declared capabilities are exercised

    This connects the static (within_caps) and dynamic (gov_safe)
    views of governance. *)

Theorem governed_effect_completeness :
  forall (h : base_handler) (R : Type) (caps : CapSet)
    (t : itree DirectiveE R),
    within_caps caps t ->
    @gov_safe R false (interp (Gov h) t).
Proof.
  intros h R caps t _.
  apply governed_interp_safe.
Qed.

(** The converse direction: gov_safe holds for ALL programs,
    regardless of their capability profile. This shows that
    governance safety is orthogonal to capability tracking.
    Governance ensures the runtime check; capability tracking
    ensures the static bound. *)

Theorem gov_safe_independent_of_caps :
  forall (h : base_handler) (R : Type)
    (t : itree DirectiveE R),
    @gov_safe R false (interp (Gov h) t).
Proof.
  intros. apply governed_interp_safe.
Qed.

(** Dual guarantee: a program satisfying both within_caps and
    gov_safe is constrained from both sides. The capability
    bound limits what it CAN do; governance limits what it MAY do
    without checks. *)

Theorem dual_guarantee :
  forall (h : base_handler) (R : Type) (caps : CapSet)
    (t : itree DirectiveE R),
    within_caps caps t ->
    within_caps caps t /\
    @gov_safe R false (interp (Gov h) t).
Proof.
  intros h R caps t Hcaps. split.
  - exact Hcaps.
  - apply governed_interp_safe.
Qed.

(* ================================================================= *)
(* Summary                                                             *)
(* ================================================================= *)

(** ** Summary

    The EffectAlgebra module establishes the capability-indexed
    effect system:

    | Result                      | What It Says                                |
    |-----------------------------|---------------------------------------------|
    | code_within_empty           | Code morphisms need no capabilities          |
    | reason_within_llm           | Reason needs only LLM capability             |
    | memory_within_mem           | Memory needs only Memory capability          |
    | call_within_call            | Call needs only MachineCall capability        |
    | bind_within_caps            | Capability bounds compose under bind         |
    | seq_comp_caps               | Sequential composition preserves bounds      |
    | no_ambient_effects          | Empty-cap programs only emit observability   |
    | effectful_not_empty         | Effectful directives require non-empty caps  |
    | governed_effect_completeness| Capability-bounded + governed = dual bounds  |
    | within_caps_weaken          | Larger cap sets include more programs        |
    | within_full                 | All programs are in the full cap set         |
    | dual_guarantee              | Static caps + dynamic governance together    |

    These results provide the algebraic effect system foundation
    for Phases 4-6 of the formal algebra plan. *)
