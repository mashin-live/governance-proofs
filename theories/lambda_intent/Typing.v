(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file. *)

(** * Lambda^intent Type-and-Effect System

    Typing judgments: Gamma |- e : tau ! kappa
    where kappa is a capability set.

    Reference: OSI paper, Section 3 (Type-and-Effect System). *)

From Coq Require Import
  Lists.List
  Strings.String
  Bool.Bool
  Arith.Arith.

From MashinGov.lambda_intent Require Import Syntax.

Import ListNotations.

(* ================================================================== *)
(** ** Typing Contexts *)
(* ================================================================== *)

(** A typing context is a list of types, indexed by de Bruijn level. *)
Definition context := list ty.

Definition ctx_lookup (Gamma : context) (x : nat) : option ty :=
  nth_error Gamma x.

(* ================================================================== *)
(** ** Typing Judgment *)
(* ================================================================== *)

(** Gamma |- e : tau ! kappa

    kappa is the capability set: which capability classes the term
    may exercise during evaluation. kappa = [] means pure. *)

Inductive has_type : context -> tm -> ty -> cap_set -> Prop :=

  (* --- Values (all pure) --- *)

  | T_Int : forall Gamma n,
      has_type Gamma (tint n) TInt cap_empty

  | T_Bool : forall Gamma b,
      has_type Gamma (tbool b) TBool cap_empty

  | T_Str : forall Gamma s,
      has_type Gamma (tstr s) TString cap_empty

  | T_Var : forall Gamma x T,
      ctx_lookup Gamma x = Some T ->
      has_type Gamma (tvar x) T cap_empty

  | T_Denied : forall Gamma k,
      has_type Gamma tdenied (TResponse k) cap_empty

  | T_Suspended : forall Gamma k,
      has_type Gamma tsuspended (TResponse k) cap_empty

  | T_Nil : forall Gamma T,
      has_type Gamma tnil (TList T) cap_empty

  (* --- Abstraction: body's capability becomes the abs's capability --- *)

  | T_Abs : forall Gamma T1 T2 body kap,
      has_type (T1 :: Gamma) body T2 kap ->
      has_type Gamma (tabs T1 body) (TArrow T1 T2) kap

  (* --- Application: union of capabilities --- *)

  | T_App : forall Gamma e1 e2 T1 T2 kap1 kap2,
      has_type Gamma e1 (TArrow T1 T2) kap1 ->
      has_type Gamma e2 T1 kap2 ->
      has_type Gamma (tapp e1 e2) T2 (cap_union kap1 kap2)

  (* --- Let binding: union --- *)

  | T_Let : forall Gamma e1 e2 T1 T2 kap1 kap2,
      has_type Gamma e1 T1 kap1 ->
      has_type (T1 :: Gamma) e2 T2 kap2 ->
      has_type Gamma (tlet e1 e2) T2 (cap_union kap1 kap2)

  (* --- Conditional: union --- *)

  | T_If : forall Gamma e1 e2 e3 T kap1 kap2 kap3,
      has_type Gamma e1 TBool kap1 ->
      has_type Gamma e2 T kap2 ->
      has_type Gamma e3 T kap3 ->
      has_type Gamma (tif e1 e2 e3) T (cap_union kap1 (cap_union kap2 kap3))

  (* --- Pairs --- *)

  | T_Pair : forall Gamma e1 e2 T1 T2 kap1 kap2,
      has_type Gamma e1 T1 kap1 ->
      has_type Gamma e2 T2 kap2 ->
      has_type Gamma (tpair e1 e2) (TProd T1 T2) (cap_union kap1 kap2)

  | T_Fst : forall Gamma e T1 T2 kap,
      has_type Gamma e (TProd T1 T2) kap ->
      has_type Gamma (tfst e) T1 kap

  | T_Snd : forall Gamma e T1 T2 kap,
      has_type Gamma e (TProd T1 T2) kap ->
      has_type Gamma (tsnd e) T2 kap

  (* --- List cons --- *)

  | T_Cons : forall Gamma e1 e2 T kap1 kap2,
      has_type Gamma e1 T kap1 ->
      has_type Gamma e2 (TList T) kap2 ->
      has_type Gamma (tcons e1 e2) (TList T) (cap_union kap1 kap2)

  (* --- Fixed point --- *)

  | T_Fix : forall Gamma body T kap,
      has_type (T :: Gamma) body T kap ->
      has_type Gamma (tfix T body) T kap

  (* --- THE KEY RULE: ask_k introduces exactly {k} --- *)

  | T_Ask : forall Gamma k a tgt p,
      value p ->
      has_type Gamma (task k a tgt p)
        (TResponse k)
        (cap_singleton k)

  (* --- Subsumption: capabilities can widen --- *)

  | T_Sub : forall Gamma e T kap kap',
      has_type Gamma e T kap ->
      cap_subset kap kap' ->
      has_type Gamma e T kap'.

(* ================================================================== *)
(** ** Static Capability Confinement *)
(* ================================================================== *)

(** If a term is typed with capability set kappa and k is not in
    kappa, then the term contains no ask_k subexpression. *)

Theorem static_capability_confinement :
  forall Gamma e T kap k,
    has_type Gamma e T kap ->
    cap_mem k kap = false ->
    contains_ask_k e k = false.
Proof.
  intros Gamma e T kap k Htype.
  induction Htype; intros Hnotin; simpl.
  - (* T_Int *) reflexivity.
  - (* T_Bool *) reflexivity.
  - (* T_Str *) reflexivity.
  - (* T_Var *) reflexivity.
  - (* T_Denied *) reflexivity.
  - (* T_Suspended *) reflexivity.
  - (* T_Nil *) reflexivity.
  - (* T_Abs *) reflexivity.
  - (* T_App *)
    apply Bool.orb_false_iff. split.
    + apply IHHtype1. destruct (cap_mem_union_false _ _ _ Hnotin). exact H.
    + apply IHHtype2. destruct (cap_mem_union_false _ _ _ Hnotin). exact H0.
  - (* T_Let *)
    apply Bool.orb_false_iff. split.
    + apply IHHtype1. destruct (cap_mem_union_false _ _ _ Hnotin). exact H.
    + apply IHHtype2. destruct (cap_mem_union_false _ _ _ Hnotin). exact H0.
  - (* T_If *)
    repeat rewrite Bool.orb_false_iff. repeat split.
    + apply IHHtype1. destruct (cap_mem_union_false _ _ _ Hnotin) as [Hk1 _]. exact Hk1.
    + apply IHHtype2. destruct (cap_mem_union_false _ _ _ Hnotin) as [_ Hk23].
      destruct (cap_mem_union_false _ _ _ Hk23) as [Hk2 _]. exact Hk2.
    + apply IHHtype3. destruct (cap_mem_union_false _ _ _ Hnotin) as [_ Hk23].
      destruct (cap_mem_union_false _ _ _ Hk23) as [_ Hk3]. exact Hk3.
  - (* T_Pair *)
    apply Bool.orb_false_iff. split.
    + apply IHHtype1. destruct (cap_mem_union_false _ _ _ Hnotin). exact H.
    + apply IHHtype2. destruct (cap_mem_union_false _ _ _ Hnotin). exact H0.
  - (* T_Fst *) apply IHHtype. exact Hnotin.
  - (* T_Snd *) apply IHHtype. exact Hnotin.
  - (* T_Cons *)
    apply Bool.orb_false_iff. split.
    + apply IHHtype1. destruct (cap_mem_union_false _ _ _ Hnotin). exact H.
    + apply IHHtype2. destruct (cap_mem_union_false _ _ _ Hnotin). exact H0.
  - (* T_Fix: contains_ask_k returns false for tfix *) reflexivity.
  - (* T_Ask: k is in {k0}, but k is not in kap -- if k=k0 contradiction *)
    destruct (cap_class_eq_dec k k0) as [Heq | Hneq].
    + subst. rewrite cap_mem_singleton in Hnotin. discriminate.
    + reflexivity.
  - (* T_Sub: kap subset kap', k not in kap' implies k not in kap *)
    apply IHHtype.
    destruct (cap_mem k kap) eqn:E; auto.
    apply H in E. congruence.
Qed.

(** Corollary: pure terms contain no ask at all *)
Corollary purity_no_ask :
  forall Gamma e T k,
    has_type Gamma e T cap_empty ->
    contains_ask_k e k = false.
Proof.
  intros Gamma e T k H.
  apply (static_capability_confinement Gamma e T cap_empty k H).
  apply cap_mem_empty.
Qed.
