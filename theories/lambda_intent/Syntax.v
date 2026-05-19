(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file.

   The governance architecture formalized in this development is the
   subject of pending U.S. patent applications by Mashin, Inc. The
   MIT license applies to these proof sources; it does not grant
   rights under any patents. *)

(** * Lambda^intent Syntax

    Defines the syntax of the lambda^intent calculus:
    capability classes, types with capability annotations,
    terms, values, labels, traces, and configurations.

    Reference: OSI paper, Section 2 (Syntax). *)

From Coq Require Import
  Lists.List
  Strings.String
  Bool.Bool
  Arith.Arith
  Logic.FunctionalExtensionality.

Import ListNotations.
Open Scope list_scope.

(* ================================================================== *)
(** ** Capability Classes *)
(* ================================================================== *)

(** Capability classes categorize external interactions.
    Each [ask_k] expression is annotated with its class. *)

Inductive cap_class : Type :=
  | CapNetwork
  | CapFile
  | CapDatabase
  | CapEmail
  | CapExec
  | CapPayment
  | CapLLM
  | CapMemory.

(** Decidable equality on capability classes *)
Lemma cap_class_eq_dec : forall (k1 k2 : cap_class), {k1 = k2} + {k1 <> k2}.
Proof. decide equality. Defined.

(** A capability set is a predicate on capability classes.
    We represent it as a list for computability. *)
Definition cap_set := list cap_class.

Definition cap_empty : cap_set := [].

Definition cap_singleton (k : cap_class) : cap_set := [k].

Definition cap_union (ks1 ks2 : cap_set) : cap_set := ks1 ++ ks2.

Definition cap_mem (k : cap_class) (ks : cap_set) : bool :=
  existsb (fun k' =>
    match cap_class_eq_dec k k' with
    | left _ => true
    | right _ => false
    end) ks.

Definition cap_subset (ks1 ks2 : cap_set) : Prop :=
  forall k, cap_mem k ks1 = true -> cap_mem k ks2 = true.

Definition cap_intersect (ks1 ks2 : cap_set) : cap_set :=
  filter (fun k => cap_mem k ks2) ks1.

(* ================================================================== *)
(** ** Capability Set Lemmas *)
(* ================================================================== *)

(** Helper: the match in cap_mem reflects equality *)
Lemma cap_class_eq_dec_refl : forall k,
  cap_class_eq_dec k k = left eq_refl.
Proof.
  intros k. destruct (cap_class_eq_dec k k).
  - f_equal. apply Eqdep_dec.UIP_dec. exact cap_class_eq_dec.
  - exfalso. apply n. reflexivity.
Qed.

Lemma cap_mem_singleton : forall k,
  cap_mem k (cap_singleton k) = true.
Proof.
  intros k. unfold cap_mem, cap_singleton. simpl.
  rewrite cap_class_eq_dec_refl. simpl. reflexivity.
Qed.

Lemma cap_mem_singleton_neq : forall k k',
  k <> k' -> cap_mem k (cap_singleton k') = false.
Proof.
  intros k k' Hneq. unfold cap_mem, cap_singleton. simpl.
  destruct (cap_class_eq_dec k k').
  - exfalso. apply Hneq. exact e.
  - simpl. reflexivity.
Qed.

Lemma cap_mem_empty : forall k,
  cap_mem k cap_empty = false.
Proof.
  intros k. unfold cap_mem, cap_empty. simpl. reflexivity.
Qed.

Lemma cap_mem_union : forall k ks1 ks2,
  cap_mem k (cap_union ks1 ks2) = cap_mem k ks1 || cap_mem k ks2.
Proof.
  intros k ks1 ks2. unfold cap_union, cap_mem.
  induction ks1 as [| k' ks1' IH].
  - simpl. reflexivity.
  - simpl. destruct (cap_class_eq_dec k k'); simpl.
    + reflexivity.
    + exact IH.
Qed.

Lemma cap_mem_union_false : forall k ks1 ks2,
  cap_mem k (cap_union ks1 ks2) = false ->
  cap_mem k ks1 = false /\ cap_mem k ks2 = false.
Proof.
  intros k ks1 ks2 H.
  rewrite cap_mem_union in H.
  apply Bool.orb_false_iff in H. exact H.
Qed.

Lemma cap_mem_union_true_l : forall k ks1 ks2,
  cap_mem k ks1 = true ->
  cap_mem k (cap_union ks1 ks2) = true.
Proof.
  intros k ks1 ks2 H.
  rewrite cap_mem_union. rewrite H. simpl. reflexivity.
Qed.

Lemma cap_mem_union_true_r : forall k ks1 ks2,
  cap_mem k ks2 = true ->
  cap_mem k (cap_union ks1 ks2) = true.
Proof.
  intros k ks1 ks2 H.
  rewrite cap_mem_union. rewrite H.
  rewrite Bool.orb_comm. simpl. reflexivity.
Qed.

Lemma cap_subset_refl : forall ks, cap_subset ks ks.
Proof. unfold cap_subset. auto. Qed.

Lemma cap_subset_trans : forall ks1 ks2 ks3,
  cap_subset ks1 ks2 -> cap_subset ks2 ks3 -> cap_subset ks1 ks3.
Proof. unfold cap_subset. auto. Qed.

Lemma cap_subset_empty : forall ks, cap_subset cap_empty ks.
Proof.
  unfold cap_subset. intros ks k H.
  rewrite cap_mem_empty in H. discriminate.
Qed.

Lemma cap_subset_union_l : forall ks1 ks2,
  cap_subset ks1 (cap_union ks1 ks2).
Proof.
  unfold cap_subset. intros ks1 ks2 k H.
  apply cap_mem_union_true_l. exact H.
Qed.

Lemma cap_subset_union_r : forall ks1 ks2,
  cap_subset ks2 (cap_union ks1 ks2).
Proof.
  unfold cap_subset. intros ks1 ks2 k H.
  apply cap_mem_union_true_r. exact H.
Qed.

Lemma cap_subset_union_both : forall ks1 ks2 ks,
  cap_subset ks1 ks -> cap_subset ks2 ks ->
  cap_subset (cap_union ks1 ks2) ks.
Proof.
  unfold cap_subset. intros ks1 ks2 ks H1 H2 k Hmem.
  rewrite cap_mem_union in Hmem.
  apply Bool.orb_true_iff in Hmem.
  destruct Hmem as [Hmem | Hmem].
  - apply H1. exact Hmem.
  - apply H2. exact Hmem.
Qed.

(* ================================================================== *)
(** ** Types *)
(* ================================================================== *)

(** Types with capability annotations on function arrows. *)

Inductive ty : Type :=
  | TInt : ty
  | TBool : ty
  | TString : ty
  | TArrow : ty -> ty -> ty              (** tau1 -> tau2 *)
  | TProd : ty -> ty -> ty
  | TList : ty -> ty
  | TResponse : cap_class -> ty.         (** Response indexed by class *)

(** Decidable equality on types *)
Lemma cap_set_eq_dec : forall (ks1 ks2 : cap_set), {ks1 = ks2} + {ks1 <> ks2}.
Proof. apply List.list_eq_dec. apply cap_class_eq_dec. Defined.

Lemma ty_eq_dec : forall (t1 t2 : ty), {t1 = t2} + {t1 <> t2}.
Proof.
  intro t1. induction t1; destruct t2;
    try (right; intro H; discriminate H);
    try (left; reflexivity).
  - (* TArrow vs TArrow *)
    destruct (IHt1_1 t2_1); destruct (IHt1_2 t2_2); subst;
      try (left; reflexivity);
      right; intro H; injection H; intros; contradiction.
  - (* TProd vs TProd *)
    destruct (IHt1_1 t2_1); destruct (IHt1_2 t2_2); subst;
      try (left; reflexivity);
      right; intro H; injection H; intros; contradiction.
  - (* TList vs TList *)
    destruct (IHt1 t2); subst;
      try (left; reflexivity);
      right; intro H; injection H; intros; contradiction.
  - (* TResponse vs TResponse *)
    destruct (cap_class_eq_dec c c0); subst;
      try (left; reflexivity);
      right; intro H; injection H; intros; contradiction.
Defined.

(* ================================================================== *)
(** ** Terms *)
(* ================================================================== *)

(** De Bruijn indices for variables. *)

Inductive tm : Type :=
  (* Values *)
  | tint : nat -> tm
  | tbool : bool -> tm
  | tstr : string -> tm
  | tabs : ty -> tm -> tm               (** lambda x:tau. e *)
  | tpair : tm -> tm -> tm
  | tnil : tm                           (** empty list *)
  | tcons : tm -> tm -> tm              (** list cons *)
  (* Eliminated values *)
  | tdenied : tm
  | tsuspended : tm
  (* Variables and computation *)
  | tvar : nat -> tm                    (** de Bruijn index *)
  | tapp : tm -> tm -> tm
  | tlet : tm -> tm -> tm              (** let x = e1 in e2 *)
  | tif : tm -> tm -> tm -> tm
  | tfst : tm -> tm
  | tsnd : tm -> tm
  | tfix : ty -> tm -> tm              (** fix f:tau. e *)
  (* Intent production: the ONLY effectful primitive *)
  | task : cap_class -> string -> string -> tm -> tm.
  (** ask_k(action, target, params) *)

(** Intent values are finite data structures. *)
Record intent_val : Type := mk_intent {
  intent_class  : cap_class;
  intent_action : string;
  intent_target : string;
  intent_params : tm;       (** parameter expression (a value) *)
}.

(* ================================================================== *)
(** ** Values *)
(* ================================================================== *)

(** Syntactic value predicate *)
Inductive value : tm -> Prop :=
  | v_int    : forall n, value (tint n)
  | v_bool   : forall b, value (tbool b)
  | v_str    : forall s, value (tstr s)
  | v_abs    : forall T e, value (tabs T e)
  | v_pair   : forall v1 v2, value v1 -> value v2 -> value (tpair v1 v2)
  | v_nil    : value tnil
  | v_cons   : forall v1 v2, value v1 -> value v2 -> value (tcons v1 v2)
  | v_denied : value tdenied
  | v_susp   : value tsuspended.

(* ================================================================== *)
(** ** Governance Decisions and Records *)
(* ================================================================== *)

Inductive gov_decision : Type :=
  | GovAllow
  | GovDeny
  | GovEscalate.

(** A decision record captures everything about a governance decision *)
Record decision_record : Type := mk_record {
  rec_intent    : intent_val;
  rec_decision  : gov_decision;
  rec_policy_id : string;        (** which policy applied *)
  rec_prev_hash : string;        (** hash chain link *)
}.

(* ================================================================== *)
(** ** Labels and Traces *)
(* ================================================================== *)

(** Labels are the observable events in execution traces. *)

Inductive label : Type :=
  | LSilent : label                                (** pure reduction *)
  | LGov : cap_class -> gov_decision -> decision_record -> label
      (** governance decision *)
  | LEff : cap_class -> tm -> label.               (** realized effect *)

Definition trace := list label.

(* ================================================================== *)
(** ** Decidable Equality for Terms and Labels *)
(* ================================================================== *)

Lemma tm_eq_dec : forall (t1 t2 : tm), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality;
    try apply Nat.eq_dec; try apply Bool.bool_dec;
    try apply String.string_dec; try apply ty_eq_dec;
    try apply cap_class_eq_dec.
Defined.

Lemma gov_decision_eq_dec : forall (d1 d2 : gov_decision),
  {d1 = d2} + {d1 <> d2}.
Proof. decide equality. Defined.

Lemma intent_val_eq_dec : forall (i1 i2 : intent_val),
  {i1 = i2} + {i1 <> i2}.
Proof.
  decide equality;
    try apply cap_class_eq_dec; try apply String.string_dec;
    try apply tm_eq_dec.
Defined.

Lemma decision_record_eq_dec : forall (r1 r2 : decision_record),
  {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality;
    try apply intent_val_eq_dec; try apply gov_decision_eq_dec;
    try apply String.string_dec.
Defined.

Lemma label_eq_dec : forall (l1 l2 : label), {l1 = l2} + {l1 <> l2}.
Proof.
  decide equality;
    try apply cap_class_eq_dec; try apply gov_decision_eq_dec;
    try apply decision_record_eq_dec; try apply tm_eq_dec.
Defined.

(* ================================================================== *)
(** ** Policies *)
(* ================================================================== *)

(** A policy is a decidable predicate on intents.
    We model policies as functions from intents to decisions. *)

Definition policy := intent_val -> gov_decision.

(** A policy set is a list of policies combined with deny-overrides. *)
Definition policy_set := list policy.

(** Evaluate a policy set: deny overrides allow, escalate overrides allow *)
Fixpoint eval_policy_set (ps : policy_set) (i : intent_val) : gov_decision :=
  match ps with
  | [] => GovAllow  (** default: allow if no policy applies *)
  | p :: rest =>
    match p i with
    | GovDeny => GovDeny         (** deny overrides everything *)
    | GovEscalate =>
      match eval_policy_set rest i with
      | GovDeny => GovDeny       (** deny still overrides *)
      | _ => GovEscalate
      end
    | GovAllow => eval_policy_set rest i
    end
  end.

(** Policy evaluation always terminates (it is a fixpoint over a finite list) *)
Lemma eval_policy_set_total :
  forall ps i, exists d, eval_policy_set ps i = d.
Proof.
  intros ps i. exists (eval_policy_set ps i). reflexivity.
Qed.

(* ================================================================== *)
(** ** Configurations *)
(* ================================================================== *)

(** An execution configuration: term, policy set, ledger, trace *)
Record config : Type := mk_config {
  cfg_term   : tm;
  cfg_policy : policy_set;
  cfg_ledger : list decision_record;
  cfg_trace  : trace;
}.

(* ================================================================== *)
(** ** Substitution *)
(* ================================================================== *)

(** Shift de Bruijn indices *)
Fixpoint shift (d : nat) (c : nat) (t : tm) : tm :=
  match t with
  | tvar n => if Nat.leb c n then tvar (n + d) else tvar n
  | tabs T body => tabs T (shift d (S c) body)
  | tapp e1 e2 => tapp (shift d c e1) (shift d c e2)
  | tlet e1 e2 => tlet (shift d c e1) (shift d (S c) e2)
  | tif e1 e2 e3 => tif (shift d c e1) (shift d c e2) (shift d c e3)
  | tfst e => tfst (shift d c e)
  | tsnd e => tsnd (shift d c e)
  | tfix T body => tfix T (shift d (S c) body)
  | tpair e1 e2 => tpair (shift d c e1) (shift d c e2)
  | tcons e1 e2 => tcons (shift d c e1) (shift d c e2)
  | task k a tgt p => task k a tgt (shift d c p)
  | tint _ | tbool _ | tstr _ | tnil | tdenied | tsuspended => t
  end.

(** Substitution: [x := s] t *)
Fixpoint subst (x : nat) (s : tm) (t : tm) : tm :=
  match t with
  | tvar n =>
    if Nat.eqb n x then s
    else if Nat.ltb x n then tvar (pred n)
    else tvar n
  | tabs T body => tabs T (subst (S x) (shift 1 0 s) body)
  | tapp e1 e2 => tapp (subst x s e1) (subst x s e2)
  | tlet e1 e2 => tlet (subst x s e1) (subst (S x) (shift 1 0 s) e2)
  | tif e1 e2 e3 => tif (subst x s e1) (subst x s e2) (subst x s e3)
  | tfst e => tfst (subst x s e)
  | tsnd e => tsnd (subst x s e)
  | tfix T body => tfix T (subst (S x) (shift 1 0 s) body)
  | tpair e1 e2 => tpair (subst x s e1) (subst x s e2)
  | tcons e1 e2 => tcons (subst x s e1) (subst x s e2)
  | task k a tgt p => task k a tgt (subst x s p)
  | tint _ | tbool _ | tstr _ | tnil | tdenied | tsuspended => t
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20, left associativity).

(** Convenience: substitute index 0 and shift *)
Definition subst_top (s t : tm) : tm := subst 0 s t.

(** Shifting preserves value-ness *)
Lemma shift_preserves_value : forall d c v, value v -> value (shift d c v).
Proof.
  intros d c v Hval. induction Hval; simpl; constructor; auto.
Qed.

(* ================================================================== *)
(** ** Utility: contains_ask_k *)
(* ================================================================== *)

(** Check whether a term contains an [ask] of a given capability class. *)
(** Check whether a term contains a top-level [ask] of a given
    capability class. Does NOT descend into lambda or fix bodies
    because those asks only execute when the function is called,
    not during evaluation of the abstraction itself. *)
Fixpoint contains_ask_k (e : tm) (k : cap_class) : bool :=
  match e with
  | task k' _ _ _ =>
    match cap_class_eq_dec k k' with
    | left _ => true
    | right _ => false  (* params are values, cannot contain top-level asks *)
    end
  | tabs _ _ => false   (* asks inside lambdas are latent *)
  | tfix _ _ => false   (* asks inside fix are latent *)
  | tapp e1 e2 => contains_ask_k e1 k || contains_ask_k e2 k
  | tlet e1 e2 => contains_ask_k e1 k || contains_ask_k e2 k
  | tif e1 e2 e3 =>
    contains_ask_k e1 k || contains_ask_k e2 k || contains_ask_k e3 k
  | tfst e => contains_ask_k e k
  | tsnd e => contains_ask_k e k
  | tpair e1 e2 => contains_ask_k e1 k || contains_ask_k e2 k
  | tcons e1 e2 => contains_ask_k e1 k || contains_ask_k e2 k
  | _ => false
  end.
