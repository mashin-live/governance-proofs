(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file.

   The governance architecture formalized in this development is the
   subject of pending U.S. patent applications by Mashin, Inc. The
   MIT license applies to these proof sources; it does not grant
   rights under any patents. *)

(** * Functor: Governance Endofunctor on the Category of Interpretations

    Formalizes the categorical claim that governance is an endofunctor
    on the category of interpretations.

    The category Interp:
    - Objects: governed handlers [forall R, DirectiveE R -> itree GovIOE R]
    - Morphisms: handler equivalences [forall R d, eutt eq (h1 R d) (h2 R d)]
    - Identity: reflexivity of [eutt]
    - Composition: transitivity of [eutt]

    The endofunctor [Gov_endo : Interp -> Interp]:
    - On objects: wraps a governed handler with pre/post governance
    - On morphisms: preserves handler equivalence ([Gov_endo_proper])
    - Preserves identity ([Gov_endo_preserves_id])
    - Preserves composition ([Gov_endo_preserves_comp])

    Unlike [Gov] (which maps [base_handler] to [governed_handler],
    crossing type boundaries), [Gov_endo] is a genuine endomorphism
    on a single type. The connection is:
    [Gov h = Gov_endo (embed_handler h)] definitionally.

    This formalization resolves the paper's original caveat that
    "a full functorial treatment would require defining a category
    of interpretations." The category is defined, the functor laws
    are proved, and the construction is machine-checked. *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.

From ITree Require Import
  Interp.InterpFacts.

(* ================================================================= *)
(* The Category of Interpretations (Interp)                            *)
(* ================================================================= *)

(** ** Category Structure

    Objects are governed handlers: [forall R, DirectiveE R -> itree GovIOE R].
    Morphisms between [h1] and [h2] are proofs of pointwise [eutt]
    equivalence. This forms a setoid (groupoid, in fact: every
    morphism is invertible via symmetry). *)

Section InterpCategory.

  (** Morphisms in Interp: pointwise eutt equivalence between
      governed handlers. Two handlers are equivalent if they
      produce bisimilar trees for every directive. *)
  Definition gov_handler_equiv (h1 h2 : governed_handler) : Prop :=
    forall R (d : DirectiveE R), eutt eq (h1 R d) (h2 R d).

  (** Identity morphism: reflexivity of eutt. *)
  Lemma gov_handler_equiv_refl :
    forall h, gov_handler_equiv h h.
  Proof. intros h R d. reflexivity. Qed.

  (** Inverse morphism: symmetry of eutt.
      This makes Interp a groupoid (all morphisms invertible). *)
  Lemma gov_handler_equiv_sym :
    forall h1 h2,
      gov_handler_equiv h1 h2 ->
      gov_handler_equiv h2 h1.
  Proof. intros h1 h2 H R d. symmetry. apply H. Qed.

  (** Composition of morphisms: transitivity of eutt. *)
  Lemma gov_handler_equiv_trans :
    forall h1 h2 h3,
      gov_handler_equiv h1 h2 ->
      gov_handler_equiv h2 h3 ->
      gov_handler_equiv h1 h3.
  Proof.
    intros h1 h2 h3 H12 H23 R d.
    rewrite (H12 R d). apply H23.
  Qed.

End InterpCategory.

(* ================================================================= *)
(* The Governance Endofunctor (Gov_endo)                               *)
(* ================================================================= *)

(** ** Definition

    [Gov_endo : governed_handler -> governed_handler]

    Same pipeline structure as [Gov], but operating on governed
    handlers directly (no [lift_io] needed, since the handler
    already produces [itree GovIOE R]). This makes [Gov_endo]
    a genuine endomorphism on the type of governed handlers. *)

Definition Gov_endo (g : governed_handler) : governed_handler :=
  fun R (d : DirectiveE R) =>
    ITree.bind pre_governance (fun ok =>
    if ok then
      ITree.bind (g R d) (fun r =>
      ITree.bind post_governance (fun _ =>
      ret r))
    else
      ITree.spin).

(** ** Embedding Base Handlers

    [embed_handler] lifts a base handler (producing [itree IOE R])
    into a governed handler (producing [itree GovIOE R]) by
    translating IOE events into the right summand of [GovIOE].

    The key connection: [Gov h = Gov_endo (embed_handler h)]
    definitionally, because [embed_handler h R d = lift_io (h R d)]. *)

Definition embed_handler (h : base_handler) : governed_handler :=
  fun R (d : DirectiveE R) => lift_io (h R d).

(** Gov factors through embed_handler and Gov_endo.
    This holds by definitional equality: both sides unfold
    to the same term. *)
Lemma Gov_factorization :
  forall (h : base_handler) R (d : DirectiveE R),
    Gov h R d = Gov_endo (embed_handler h) R d.
Proof.
  intros h R d.
  unfold Gov, Gov_endo, embed_handler.
  reflexivity.
Qed.

(** The factorization lifts to handler equivalence. *)
Corollary Gov_factorization_equiv :
  forall (h : base_handler),
    gov_handler_equiv (Gov h) (Gov_endo (embed_handler h)).
Proof.
  intros h R d.
  rewrite Gov_factorization.
  reflexivity.
Qed.

(* ================================================================= *)
(* Functor Laws                                                        *)
(* ================================================================= *)

(** ** Law 1: Gov_endo Preserves Morphisms

    If [h1 ≈ h2] in Interp (pointwise eutt), then
    [Gov_endo h1 ≈ Gov_endo h2].

    This is the substantive functor property: the governance
    pipeline respects handler equivalence. The proof uses the
    congruence of [bind] under [eutt]. *)

Theorem Gov_endo_proper :
  forall (h1 h2 : governed_handler),
    gov_handler_equiv h1 h2 ->
    gov_handler_equiv (Gov_endo h1) (Gov_endo h2).
Proof.
  intros h1 h2 Heq R d.
  unfold Gov_endo.
  (* Outer bind over pre_governance: identical on both sides *)
  apply eutt_clo_bind with (UU := eq).
  - reflexivity.
  - intros ok1 ok2 Hok. subst.
    destruct ok2.
    + (* Governance passed: inner handler differs *)
      apply eutt_clo_bind with (UU := eq).
      * (* h1 R d ≈ h2 R d by hypothesis *)
        apply Heq.
      * (* post_governance >> ret: identical *)
        intros r1 r2 Hr. subst.
        apply eutt_clo_bind with (UU := eq).
        -- reflexivity.
        -- intros u1 u2 Hu. subst. reflexivity.
    + (* Governance denied: both sides are spin *)
      reflexivity.
Qed.

(** ** Law 2: Gov_endo Preserves Identity Morphisms

    The identity morphism on [h] is [gov_handler_equiv_refl h].
    Applying Gov_endo to both sides yields the identity morphism
    on [Gov_endo h]. Since identity is reflexivity and Gov_endo
    maps [h] to a fixed [Gov_endo h], preservation is immediate. *)

Lemma Gov_endo_preserves_id :
  forall h, gov_handler_equiv (Gov_endo h) (Gov_endo h).
Proof.
  intros. apply gov_handler_equiv_refl.
Qed.

(** ** Law 3: Gov_endo Preserves Morphism Composition

    If [f : h1 ≈ h2] and [g : h2 ≈ h3], then
    [Gov_endo(g . f) = Gov_endo(g) . Gov_endo(f)].

    In Interp, morphism composition is transitivity of [eutt].
    This law states that applying Gov_endo to a composed
    equivalence yields the composition of the individual
    Gov_endo equivalences. *)

Lemma Gov_endo_preserves_comp :
  forall h1 h2 h3,
    gov_handler_equiv h1 h2 ->
    gov_handler_equiv h2 h3 ->
    gov_handler_equiv (Gov_endo h1) (Gov_endo h3).
Proof.
  intros h1 h2 h3 H12 H23.
  apply gov_handler_equiv_trans with (h2 := Gov_endo h2).
  - apply Gov_endo_proper. exact H12.
  - apply Gov_endo_proper. exact H23.
Qed.

(* ================================================================= *)
(* Summary Theorem                                                     *)
(* ================================================================= *)

(** ** Theorem: Gov_endo Is an Endofunctor on Interp

    Packages all three functor laws into a single statement.
    [Gov_endo] maps governed handlers to governed handlers
    (endomorphism on objects), preserves handler equivalence
    (functor on morphisms), and satisfies the identity and
    composition laws.

    Combined with [Gov_factorization], this establishes that
    the original [Gov] operator factors as:
      Gov = Gov_endo . embed_handler
    where [Gov_endo] is a genuine endofunctor and [embed_handler]
    is a faithful embedding of base handlers into governed handlers. *)

Theorem Gov_is_endofunctor :
  (* Morphism preservation *)
  (forall h1 h2,
    gov_handler_equiv h1 h2 ->
    gov_handler_equiv (Gov_endo h1) (Gov_endo h2))
  /\
  (* Identity preservation *)
  (forall h, gov_handler_equiv (Gov_endo h) (Gov_endo h))
  /\
  (* Composition preservation *)
  (forall h1 h2 h3,
    gov_handler_equiv h1 h2 ->
    gov_handler_equiv h2 h3 ->
    gov_handler_equiv (Gov_endo h1) (Gov_endo h3)).
Proof.
  split; [| split].
  - exact Gov_endo_proper.
  - exact Gov_endo_preserves_id.
  - exact Gov_endo_preserves_comp.
Qed.

(* ================================================================= *)
(* Iterated Governance                                                 *)
(* ================================================================= *)

(** ** Meta-Recursive Governance as Iterated Application

    Because [Gov_endo] is an endomorphism on a single type,
    it can be applied any number of times. [Gov_endo^n(g)]
    produces a handler with n layers of governance wrapping.

    This is the categorical content of the meta-recursive
    governance tower: the tower exists because [Gov_endo]
    is an endofunctor, so iterated application is well-typed. *)

Fixpoint Gov_iter (n : nat) (g : governed_handler) : governed_handler :=
  match n with
  | O => g
  | S m => Gov_endo (Gov_iter m g)
  end.

(** Iterated governance preserves handler equivalence. *)
Lemma Gov_iter_proper :
  forall n h1 h2,
    gov_handler_equiv h1 h2 ->
    gov_handler_equiv (Gov_iter n h1) (Gov_iter n h2).
Proof.
  induction n; intros h1 h2 Heq.
  - (* n = 0: identity *) exact Heq.
  - (* n = S m: Gov_endo preserves equiv by induction *)
    simpl. apply Gov_endo_proper. apply IHn. exact Heq.
Qed.

(** The governance tower stabilizes in the sense that every
    level has the same type and the same functor properties.
    Level n+1 is Gov_endo applied to level n. *)
Lemma Gov_iter_step :
  forall n g,
    gov_handler_equiv
      (Gov_iter (S n) g)
      (Gov_endo (Gov_iter n g)).
Proof.
  intros. simpl. apply gov_handler_equiv_refl.
Qed.

(** Embedding base handlers and iterating governance:
    [Gov_iter n (embed_handler h)] gives n layers of governance
    over the base handler h. For n=1, this is [Gov h]. *)
Lemma Gov_iter_1_is_Gov :
  forall h,
    gov_handler_equiv
      (Gov_iter 1 (embed_handler h))
      (Gov h).
Proof.
  intros h R d.
  simpl. rewrite <- Gov_factorization. reflexivity.
Qed.
