(* Copyright (c) 2026 Alan Lawrence McCann, mashin, Inc.
   Licensed under MIT. See LICENSE file. *)

(** * Lambda^intent Composition Semantics

    Capability narrowing under composition: when module A invokes
    module B, B's effective capabilities are the intersection of
    A's and B's declared capabilities. Capabilities can only narrow
    through composition, never widen.

    Reference: OSI paper, Section 7 (Composition Semantics). *)

From Coq Require Import
  Lists.List
  Strings.String
  Bool.Bool
  Arith.Arith.

From MashinGov.lambda_intent Require Import Syntax Typing Semantics Metatheory.

Import ListNotations.
Open Scope list_scope.

(* ================================================================== *)
(** ** Capability-Bounded Modules *)
(* ================================================================== *)

(** A module is a collection of terms with a declared capability bound.
    All exported terms must have capabilities within the bound. *)

Record module : Type := mk_module {
  mod_name : string;
  mod_cap_bound : cap_set;
  mod_exports : list (string * tm * ty * cap_set);
}.

(** Module well-formedness: all exports respect the capability bound *)
Definition module_well_formed (Gamma : context) (m : module) : Prop :=
  forall name e T kap,
    In (name, e, T, kap) (mod_exports m) ->
    has_type Gamma e T kap /\
    cap_subset kap (mod_cap_bound m).

(* ================================================================== *)
(** ** Capability Narrowing *)
(* ================================================================== *)

(** When module A invokes module B, B's effective capability is
    the intersection of A's bound and B's bound. *)

Definition effective_cap (caller callee : module) : cap_set :=
  cap_intersect (mod_cap_bound caller) (mod_cap_bound callee).

(** The effective capability is a subset of the caller's bound *)
(** Helper: filter preserves membership of the original list *)
Lemma filter_In_orig : forall (A : Type) (f : A -> bool) (l : list A) (x : A),
  In x (filter f l) -> In x l.
Proof.
  intros A f l x. induction l as [| a l' IH]; simpl.
  - intro H. exact H.
  - destruct (f a) eqn:Ef.
    + simpl. intros [H | H]; auto.
    + intro H. right. apply IH. exact H.
Qed.

(** Helper: filter membership implies predicate holds *)
Lemma filter_In_pred : forall (A : Type) (f : A -> bool) (l : list A) (x : A),
  In x (filter f l) -> f x = true.
Proof.
  intros A f l x. induction l as [| a l' IH]; simpl.
  - intro H. contradiction.
  - destruct (f a) eqn:Ef.
    + simpl. intros [H | H].
      * subst. exact Ef.
      * apply IH. exact H.
    + intro H. apply IH. exact H.
Qed.

(** cap_intersect membership implies membership in both operands *)
Lemma cap_intersect_subset_l : forall ks1 ks2 k,
  cap_mem k (cap_intersect ks1 ks2) = true ->
  cap_mem k ks1 = true.
Proof.
  intros ks1 ks2 k H.
  unfold cap_intersect in H. unfold cap_mem in *.
  apply existsb_exists in H. destruct H as [x [Hin Heq]].
  apply filter_In_orig in Hin.
  apply existsb_exists. exists x. split; auto.
Qed.

Lemma cap_intersect_subset_r : forall ks1 ks2 k,
  cap_mem k (cap_intersect ks1 ks2) = true ->
  cap_mem k ks2 = true.
Proof.
  intros ks1 ks2 k H.
  unfold cap_intersect in H. unfold cap_mem in *.
  apply existsb_exists in H. destruct H as [x [Hin Heq]].
  (* Heq tells us cap_class_eq_dec k x = left _, so k = x *)
  destruct (cap_class_eq_dec k x) as [Hkx | Hkx].
  - subst. apply filter_In_pred in Hin.
    (* Hin : cap_mem x ks2 = true, and k = x *)
    exact Hin.
  - discriminate.
Qed.

Lemma effective_cap_subset_caller :
  forall caller callee,
    cap_subset (effective_cap caller callee) (mod_cap_bound caller).
Proof.
  unfold cap_subset, effective_cap. intros caller callee k H.
  apply cap_intersect_subset_l in H. exact H.
Qed.

Lemma effective_cap_subset_callee :
  forall caller callee,
    cap_subset (effective_cap caller callee) (mod_cap_bound callee).
Proof.
  unfold cap_subset, effective_cap. intros caller callee k H.
  apply cap_intersect_subset_r in H. exact H.
Qed.

(* ================================================================== *)
(** ** Monotone Narrowing *)
(* ================================================================== *)

(** In a composition chain A1 -> A2 -> ... -> An, the effective
    capability at each depth is a subset of the previous depth.
    Capabilities can only narrow, never widen. *)

Fixpoint chain_effective_cap (chain : list module) : cap_set :=
  match chain with
  | nil => nil
  | m :: nil => mod_cap_bound m
  | m :: rest => cap_intersect (mod_cap_bound m) (chain_effective_cap rest)
  end.

Theorem chain_subset_first :
  forall m rest,
    cap_subset (chain_effective_cap (m :: rest)) (mod_cap_bound m).
Proof.
  intros m rest. destruct rest as [| m2 rest'].
  - (* singleton: chain_effective_cap [m] = mod_cap_bound m *)
    simpl. apply cap_subset_refl.
  - (* m :: m2 :: rest': cap_intersect (mod_cap_bound m) (...) *)
    simpl. unfold cap_subset. intros k H.
    apply cap_intersect_subset_l in H. exact H.
Qed.

Theorem monotone_narrowing :
  forall chain m,
    chain <> nil ->
    In m chain ->
    cap_subset (chain_effective_cap chain) (mod_cap_bound m).
Proof.
  intros chain. induction chain as [| m0 chain' IH].
  - (* empty chain: contradiction *) intros m Hne. exfalso. apply Hne. reflexivity.
  - intros m _ Hin. simpl in Hin. destruct Hin as [Heq | Hin].
    + (* m = m0: first element *)
      subst. apply chain_subset_first.
    + (* m in chain': chain_effective_cap (m0 :: chain') subset of
         chain_effective_cap chain' subset of mod_cap_bound m *)
      destruct chain' as [| m1 chain''].
      * (* chain' = nil: In m nil is false *) contradiction.
      * (* chain' = m1 :: chain'' *)
        simpl. unfold cap_subset. intros k Hmem.
        apply cap_intersect_subset_r in Hmem.
        apply IH with (m := m); auto.
        intro Habs. discriminate.
Qed.

(* ================================================================== *)
(** ** Governance Under Arbitrary Depth *)
(* ================================================================== *)

(** Governance soundness and capability confinement hold at every
    depth in a composition chain. *)

Theorem governance_at_depth :
  forall chain e T kap ps ledger tr c',
    chain <> nil ->
    cap_subset kap (chain_effective_cap chain) ->
    has_type nil e T kap ->
    multi_step (mk_config e ps ledger tr) c' ->
    (* Governance soundness holds *)
    (forall k v,
      In (LEff k v) (cfg_trace c') ->
      ~ In (LEff k v) tr ->
      exists r,
        In (LGov k GovAllow r) (cfg_trace c')) /\
    (* Capability confinement holds *)
    (forall k d r,
      In (LGov k d r) (cfg_trace c') ->
      ~ In (LGov k d r) tr ->
      cap_mem k (chain_effective_cap chain) = true).
Proof.
  intros chain e T kap ps ledger tr c' Hne Hsub Htype Hmulti.
  split.
  - (* Governance soundness: directly from Metatheory *)
    intros k v Heff Hnotin.
    eapply governance_soundness; eauto.
  - (* Capability confinement: from Metatheory + cap_subset *)
    intros k d r Hgov Hnotin.
    assert (Hk : cap_mem k kap = true).
    { eapply capability_confinement; eauto. }
    apply Hsub. exact Hk.
Qed.
