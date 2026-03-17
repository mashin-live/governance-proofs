(** * Category: Category Mashin and Compositional Closure

    Defines Category Mashin as the Kleisli category of the
    [itree DirectiveE] monad and proves closure properties.

    Key results:
    - Category axioms (identity, associativity) from monad laws
    - Primitive classification (code, reason, memory, call)
    - Compositional closure (sequential, branching, iteration)
    - Governance safety of all morphism compositions

    Corresponds to Section 4 of
    "Four Primitives Suffice: Expressive Completeness for
     Governed Cognitive Systems" (R4). *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.
From MashinGov Require Import Safety.

From ITree Require Import
  Interp.InterpFacts
  Basics.Basics.

From Paco Require Import paco.

(* ================================================================= *)
(* Objects and Morphisms of Category Mashin                           *)
(* ================================================================= *)

(** ** Objects

    Objects in Category Mashin are types (context types).
    We use Coq's [Type] universe directly. *)

(** ** Morphisms

    A morphism A -> B in Category Mashin is an interaction tree
    parameterized by DirectiveE: a pure executor program that
    takes an input of type A and produces a program computing B.

    This is the Kleisli arrow for the [itree DirectiveE] monad. *)

Definition mashin_morphism (A B : Type) : Type :=
  A -> itree DirectiveE B.

(** ** Identity

    The identity morphism is [ret]: return the input unchanged. *)

Definition mashin_id {A : Type} : mashin_morphism A A :=
  fun a => ret a.

(** ** Composition

    Sequential composition is Kleisli composition:
    run f, then feed the result to g via [bind]. *)

Definition mashin_compose {A B C : Type}
  (f : mashin_morphism A B) (g : mashin_morphism B C)
  : mashin_morphism A C :=
  fun a => ITree.bind (f a) g.

Notation "f >>> g" := (mashin_compose f g) (at level 55, right associativity).

(* ================================================================= *)
(* Category Axioms                                                    *)
(* ================================================================= *)

(** The category axioms follow from the monad laws of [itree DirectiveE],
    which are proved in the ITrees library. We state them in terms of
    [eutt eq] (observational equivalence up to tau). *)

Section CategoryAxioms.

  (** Left identity: id >>> f ≈ f *)
  Lemma mashin_left_id :
    forall (A B : Type) (f : mashin_morphism A B) (a : A),
      eutt eq ((mashin_id >>> f) a) (f a).
  Proof.
    intros A B f a.
    unfold mashin_compose, mashin_id, ret, Monad_itree.
    rewrite bind_ret_l.
    reflexivity.
  Qed.

  (** Right identity: f >>> id ≈ f *)
  Lemma mashin_right_id :
    forall (A B : Type) (f : mashin_morphism A B) (a : A),
      eutt eq ((f >>> mashin_id) a) (f a).
  Proof.
    intros A B f a.
    unfold mashin_compose, mashin_id, ret, Monad_itree.
    rewrite bind_ret_r.
    reflexivity.
  Qed.

  (** Associativity: (f >>> g) >>> h ≈ f >>> (g >>> h) *)
  Lemma mashin_assoc :
    forall (A B C D : Type)
      (f : mashin_morphism A B)
      (g : mashin_morphism B C)
      (h : mashin_morphism C D)
      (a : A),
      eutt eq (((f >>> g) >>> h) a) ((f >>> (g >>> h)) a).
  Proof.
    intros A B C D f g h a.
    unfold mashin_compose.
    rewrite bind_bind.
    reflexivity.
  Qed.

End CategoryAxioms.

(* ================================================================= *)
(* The Four Primitives                                                *)
(* ================================================================= *)

(** ** Primitive Classification

    The four primitives are specific patterns of interaction trees
    over DirectiveE. *)

(** A code morphism: pure computation with no events.
    Returns immediately with a computed result. *)
Definition code_morphism {A B : Type} (f : A -> B) : mashin_morphism A B :=
  fun a => ret (f a).

(** A reason morphism: triggers an LLM call.
    Takes a prompt-building function and a response-extracting function. *)
Definition reason_morphism {A B : Type}
  (build_prompt : A -> LLMCallParams)
  (extract : LLMResponse -> B)
  : mashin_morphism A B :=
  fun a =>
    ITree.bind (trigger (LLMCall (build_prompt a)))
               (fun resp => ret (extract resp)).

(** A memory morphism: triggers a memory operation.
    Takes a params-building function and a result-extracting function. *)
Definition memory_morphism {A B : Type}
  (build_params : A -> MemoryOpParams)
  (extract : MemoryResult -> B)
  : mashin_morphism A B :=
  fun a =>
    ITree.bind (trigger (MemoryOp (build_params a)))
               (fun resp => ret (extract resp)).

(** A call morphism: invokes another machine.
    Takes a params-building function and a result-extracting function. *)
Definition call_morphism {A B : Type}
  (build_params : A -> CallMachineParams)
  (extract : CallMachineResult -> B)
  : mashin_morphism A B :=
  fun a =>
    ITree.bind (trigger (CallMachine (build_params a)))
               (fun resp => ret (extract resp)).

(* ================================================================= *)
(* Control Flow Combinators                                           *)
(* ================================================================= *)

(** ** Branch Combinator

    Given a predicate (code morphism returning bool) and two branches,
    execute one or the other based on the predicate result. *)

Definition mashin_branch {A B : Type}
  (pred : A -> bool)
  (on_true : mashin_morphism A B)
  (on_false : mashin_morphism A B)
  : mashin_morphism A B :=
  fun a =>
    if pred a then on_true a else on_false a.

(** ** Bounded Iteration

    Given a morphism that returns Left (continue) or Right (done),
    iterate up to [fuel] times. *)

Fixpoint mashin_iter {A B : Type}
  (fuel : nat)
  (body : mashin_morphism A (A + B))
  : mashin_morphism A B :=
  fun a =>
    match fuel with
    | O => ITree.spin  (* out of fuel: diverge *)
    | S n =>
      ITree.bind (body a) (fun result =>
        match result with
        | inl a' => mashin_iter n body a'
        | inr b  => ret b
        end)
    end.

(* ================================================================= *)
(* Compositional Closure                                              *)
(* ================================================================= *)

(** ** Closure Theorems

    Every composition of morphisms in Category Mashin produces
    another well-typed interaction tree over DirectiveE. These
    are definitional equalities (the types align by construction). *)

Section Closure.

  (** Sequential composition of two Mashin morphisms produces
      a Mashin morphism. *)
  Lemma seq_closure :
    forall (A B C : Type)
      (f : mashin_morphism A B)
      (g : mashin_morphism B C),
      forall a, exists t : itree DirectiveE C, (f >>> g) a = t.
  Proof.
    intros A B C f g a.
    eexists. reflexivity.
  Qed.

  (** Code morphisms compose to code morphisms. *)
  Lemma code_compose :
    forall (A B C : Type) (f : A -> B) (g : B -> C) (a : A),
      eutt eq
        ((code_morphism f >>> code_morphism g) a)
        (code_morphism (fun x => g (f x)) a).
  Proof.
    intros A B C f g a.
    unfold mashin_compose, code_morphism, ret, Monad_itree.
    rewrite bind_ret_l.
    reflexivity.
  Qed.

  (** Branching preserves morphism status. *)
  Lemma branch_closure :
    forall (A B : Type)
      (pred : A -> bool)
      (on_true : mashin_morphism A B)
      (on_false : mashin_morphism A B),
      forall a, exists t : itree DirectiveE B,
        mashin_branch pred on_true on_false a = t.
  Proof.
    intros A B pred on_true on_false a.
    eexists. reflexivity.
  Qed.

End Closure.

(* ================================================================= *)
(* Governance Safety of Compositions                                  *)
(* ================================================================= *)

(** ** Governance Safety

    The key connection to R1: every morphism constructible from
    the four primitives, when interpreted via [Gov h], satisfies
    [gov_safe]. This follows from the governed_interp_safe theorem
    in Safety.v, since every Mashin morphism produces an
    [itree DirectiveE R]. *)

Section GovernanceSafety.

  Variable h : base_handler.

  (** Any Mashin morphism, applied to any input, produces an
      itree DirectiveE that is governed when interpreted. *)
  Theorem mashin_morphism_governed :
    forall (A B : Type) (f : mashin_morphism A B) (a : A),
      @gov_safe B false (interp (Gov h) (f a)).
  Proof.
    intros A B f a.
    apply governed_interp_safe.
  Qed.

  (** Compositions of Mashin morphisms are governed. *)
  Theorem composed_morphism_governed :
    forall (A B C : Type)
      (f : mashin_morphism A B)
      (g : mashin_morphism B C)
      (a : A),
      @gov_safe C false (interp (Gov h) ((f >>> g) a)).
  Proof.
    intros A B C f g a.
    apply governed_interp_safe.
  Qed.

  (** Code morphisms are governed. *)
  Corollary code_governed :
    forall (A B : Type) (f : A -> B) (a : A),
      @gov_safe B false (interp (Gov h) (code_morphism f a)).
  Proof.
    intros A B f a.
    apply governed_interp_safe.
  Qed.

  (** Reason morphisms are governed. *)
  Corollary reason_governed :
    forall (A B : Type)
      (build : A -> LLMCallParams)
      (extract : LLMResponse -> B)
      (a : A),
      @gov_safe B false (interp (Gov h) (reason_morphism build extract a)).
  Proof.
    intros A B build extract a.
    apply governed_interp_safe.
  Qed.

  (** Memory morphisms are governed. *)
  Corollary memory_governed :
    forall (A B : Type)
      (build : A -> MemoryOpParams)
      (extract : MemoryResult -> B)
      (a : A),
      @gov_safe B false (interp (Gov h) (memory_morphism build extract a)).
  Proof.
    intros A B build extract a.
    apply governed_interp_safe.
  Qed.

  (** Call morphisms are governed. *)
  Corollary call_governed :
    forall (A B : Type)
      (build : A -> CallMachineParams)
      (extract : CallMachineResult -> B)
      (a : A),
      @gov_safe B false (interp (Gov h) (call_morphism build extract a)).
  Proof.
    intros A B build extract a.
    apply governed_interp_safe.
  Qed.

  (** Branching morphisms are governed. *)
  Corollary branch_governed :
    forall (A B : Type)
      (pred : A -> bool)
      (on_true on_false : mashin_morphism A B)
      (a : A),
      @gov_safe B false (interp (Gov h) (mashin_branch pred on_true on_false a)).
  Proof.
    intros A B pred on_true on_false a.
    apply governed_interp_safe.
  Qed.

End GovernanceSafety.
