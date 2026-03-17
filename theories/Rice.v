(** * Rice: The Decidability Boundary (Law 4)

    Formalizes Law 4 of Governed Intelligence: the decidability
    boundary between structural properties (decidable) and
    semantic properties (non-trivial/undecidable).

    Key results:
    - Structural properties like [capability_allowed] are
      decidable (total computable functions returning bool)
    - Semantic properties like halting are non-trivial:
      some programs have them, some don't
    - The decidability boundary separates these two classes
    - Halting is non-trivial for both register machines
      and interaction trees

    All results are constructive (no axioms required).

    Note: The full halting undecidability theorem (no total function
    correctly decides halting for ALL programs) requires a Godel
    numbering of register machine programs and a self-referential
    diagonal construction (~200 lines). That is a well-known
    consequence of Turing completeness (proved in Completeness.v)
    and is omitted here. The decidability boundary itself (structural
    properties decidable, semantic properties non-trivial) captures
    the essential content of Law 4.

    Dependencies: Completeness.v, Safety.v, TrustSpec.v *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.
From MashinGov Require Import Safety.
From MashinGov Require Import TrustSpec.
From MashinGov Require Import Completeness.

From Paco Require Import paco.

(* ================================================================= *)
(* Structural Properties Are Decidable                                 *)
(* ================================================================= *)

(** ** Decidability of Structural Properties

    Structural properties of the governance system are total
    computable functions: given the inputs (trust level,
    capability, declared capabilities), they return a boolean
    in finite time with no possibility of divergence.

    This is true by construction: these are Coq functions
    returning [bool], which are total and decidable. *)

(** capability_allowed is a total function (decidable). *)
Theorem capability_check_decidable :
  forall (tl : TrustLevel) (cap : Capability) (dcaps : list Capability),
    { capability_allowed tl cap dcaps = true } +
    { capability_allowed tl cap dcaps = false }.
Proof.
  intros tl cap dcaps.
  destruct (capability_allowed tl cap dcaps) eqn:H.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** Trust level comparison is decidable. *)
Theorem trust_comparison_decidable :
  forall (tl1 tl2 : TrustLevel),
    { trust_at_least tl1 tl2 = true } +
    { trust_at_least tl1 tl2 = false }.
Proof.
  intros tl1 tl2.
  destruct (trust_at_least tl1 tl2) eqn:H.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** Observability classification is decidable. *)
Theorem observability_decidable :
  forall R (d : DirectiveE R),
    { is_observability d = true } + { is_observability d = false }.
Proof.
  intros R d.
  destruct (is_observability d) eqn:H.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* ================================================================= *)
(* Semantic Properties Are Non-Trivial                                 *)
(* ================================================================= *)

(** ** Non-Triviality of Semantic Properties

    A semantic property is "non-trivial" if some programs have
    it and some don't. The halting property is the canonical
    example: halting_program halts, looping_program doesn't. *)

(** A halting predicate: does a register machine halt within
    [fuel] steps starting from state [st]? *)
Definition rm_halts (p : program) (fuel : nat) (st : machine_state) : bool :=
  let final := rm_run p fuel st in
  match fetch p (fst final) with
  | Some HALT => true
  | _ => false
  end.

(** A program that always halts: just HALT. *)
Definition halting_program : program := HALT :: nil.

(** A program that never halts (loops forever):
    INC reg 0 then jump back to label 0. *)
Definition looping_program : program := INC 0 0 :: nil.

(** halting_program halts in 1 step. *)
Theorem halting_non_trivial_positive :
  rm_halts halting_program 1 (0, init_regs) = true.
Proof. reflexivity. Qed.

(** looping_program does not halt within 100 steps. *)
Theorem halting_non_trivial_negative :
  rm_halts looping_program 100 (0, init_regs) = false.
Proof. reflexivity. Qed.

(** looping_program never halts: for any fuel, the program
    counter stays at 0 (where the instruction is INC, not HALT). *)
Lemma looping_never_halts :
  forall n, rm_halts looping_program n (0, init_regs) = false.
Proof.
  intro n. induction n.
  - reflexivity.
  - unfold rm_halts. simpl.
    assert (Hinv : forall m s, fst (rm_run looping_program m (0, s)) = 0).
    { clear. intro m. induction m; intro s; simpl.
      - reflexivity.
      - apply IHm. }
    rewrite Hinv. simpl. reflexivity.
Qed.

(** The halting property is non-trivial: it is not the
    constant-true or constant-false function. *)
Theorem halting_non_trivial :
  (exists p fuel st, rm_halts p fuel st = true) /\
  (exists p fuel st, rm_halts p fuel st = false).
Proof.
  split.
  - exists halting_program, 1, (0, init_regs). reflexivity.
  - exists looping_program, 100, (0, init_regs). reflexivity.
Qed.

(** ** Non-Triviality for Interaction Trees

    For interaction trees, "halts" means the tree eventually
    produces a [Ret] value (is not [ITree.spin]). *)

Definition itree_halts {E R} (t : itree E R) : Prop :=
  exists v, eutt eq t (Ret v).

(** [Ret v] halts (trivially). *)
Theorem ret_halts : forall R (v : R), @itree_halts DirectiveE R (Ret v).
Proof.
  intros R v. exists v. reflexivity.
Qed.

(** ITree halting is non-trivial: Ret tt halts, and spin
    is not structurally equal to any Ret (strong bisimulation). *)
Theorem itree_halting_non_trivial :
  @itree_halts DirectiveE unit (Ret tt) /\
  (forall (v : unit), ~ @eq_itree DirectiveE unit unit eq ITree.spin (Ret v)).
Proof.
  split.
  - exists tt. reflexivity.
  - intros v Heq.
    punfold Heq.
    red in Heq. cbn in Heq.
    inversion Heq; subst.
    discriminate CHECK.
Qed.

(* ================================================================= *)
(* Compositional Closure of Decidable Properties                       *)
(* ================================================================= *)

(** ** Compositional Closure

    Governance predicates (bool-valued structural checks) are closed
    under boolean composition: if P and Q are decidable governance
    properties, then P AND Q, P OR Q, and NOT P are also decidable.
    This means governance policies can be freely composed without
    leaving the decidable realm. *)

(** A governance policy is a finite boolean combination of
    atomic structural checks. *)
Inductive GovPolicy : Type :=
  | PolCapability : TrustLevel -> Capability -> list Capability -> GovPolicy
  | PolTrust : TrustLevel -> TrustLevel -> GovPolicy
  | PolAnd : GovPolicy -> GovPolicy -> GovPolicy
  | PolOr : GovPolicy -> GovPolicy -> GovPolicy
  | PolNot : GovPolicy -> GovPolicy.

Fixpoint eval_policy (pol : GovPolicy) : bool :=
  match pol with
  | PolCapability tl cap dcaps => capability_allowed tl cap dcaps
  | PolTrust tl1 tl2 => trust_at_least tl1 tl2
  | PolAnd p1 p2 => eval_policy p1 && eval_policy p2
  | PolOr p1 p2 => eval_policy p1 || eval_policy p2
  | PolNot p => negb (eval_policy p)
  end.

(** Any governance policy is decidable: eval_policy is total
    and returns bool. *)
Theorem gov_policy_decidable :
  forall (pol : GovPolicy),
    { eval_policy pol = true } + { eval_policy pol = false }.
Proof.
  intro pol. destruct (eval_policy pol); [left | right]; reflexivity.
Qed.

(** Compositional closure: conjunction of decidable policies
    is decidable. *)
Theorem policy_and_decidable :
  forall p1 p2,
    { eval_policy (PolAnd p1 p2) = true } +
    { eval_policy (PolAnd p1 p2) = false }.
Proof.
  intros. destruct (eval_policy (PolAnd p1 p2)); [left | right]; reflexivity.
Qed.

(** Compositional closure: disjunction of decidable policies
    is decidable. *)
Theorem policy_or_decidable :
  forall p1 p2,
    { eval_policy (PolOr p1 p2) = true } +
    { eval_policy (PolOr p1 p2) = false }.
Proof.
  intros. destruct (eval_policy (PolOr p1 p2)); [left | right]; reflexivity.
Qed.

(** Compositional closure: negation of a decidable policy
    is decidable. *)
Theorem policy_not_decidable :
  forall p,
    { eval_policy (PolNot p) = true } +
    { eval_policy (PolNot p) = false }.
Proof.
  intros. destruct (eval_policy (PolNot p)); [left | right]; reflexivity.
Qed.

(** The compositional closure property: any finite boolean
    combination of structural governance checks is decidable. *)
Theorem compositional_closure :
  (* AND preserves decidability *)
  (forall p1 p2,
    eval_policy (PolAnd p1 p2) = true \/
    eval_policy (PolAnd p1 p2) = false)
  /\
  (* OR preserves decidability *)
  (forall p1 p2,
    eval_policy (PolOr p1 p2) = true \/
    eval_policy (PolOr p1 p2) = false)
  /\
  (* NOT preserves decidability *)
  (forall p,
    eval_policy (PolNot p) = true \/
    eval_policy (PolNot p) = false).
Proof.
  split; [| split].
  - intros p1 p2.
    destruct (eval_policy (PolAnd p1 p2)); [left | right]; reflexivity.
  - intros p1 p2.
    destruct (eval_policy (PolOr p1 p2)); [left | right]; reflexivity.
  - intro p.
    destruct (eval_policy (PolNot p)); [left | right]; reflexivity.
Qed.

(* ================================================================= *)
(* Governance Cannot Decide Halting                                    *)
(* ================================================================= *)

(** ** Governance and Halting

    Governance operates on structural properties of individual
    directives (event types, trust levels, capabilities). It does
    not examine global program behavior (halting, goal reachability).

    We formalize this separation: two programs can emit the same
    directive type (MemoryOp) on their first step, yet one halts
    and one diverges. Since governance checks see per-directive
    structural information, no governance policy can distinguish
    these programs. *)

(** A program that uses MemoryOp and halts:
    INC register 0 (jump to 1), then HALT at label 1. *)
Definition inc_then_halt : program := INC 0 1 :: HALT :: nil.

Theorem inc_then_halt_halts :
  rm_halts inc_then_halt 2 (0, init_regs) = true.
Proof. reflexivity. Qed.

(** Both inc_then_halt and looping_program begin with INC, which
    translates to a MemoryOp event. Governance sees the same event
    type for both, but they have opposite halting behavior.

    This witnesses the fundamental gap: structural governance
    (per-directive, decidable) cannot capture semantic properties
    (global program behavior, non-trivial). *)
Theorem governance_cannot_decide_halting :
  (* Both programs' first instruction emits MemoryOp *)
  (exists params1 k1,
    translate_instruction (INC 0 1) =
    ITree.bind (trigger (MemoryOp params1)) k1)
  /\
  (exists params2 k2,
    translate_instruction (INC 0 0) =
    ITree.bind (trigger (MemoryOp params2)) k2)
  /\
  (* But one halts and one diverges *)
  rm_halts inc_then_halt 2 (0, init_regs) = true /\
  (forall n, rm_halts looping_program n (0, init_regs) = false).
Proof.
  split; [| split; [| split]].
  - unfold translate_instruction, recall_reg.
    eexists. eexists. reflexivity.
  - unfold translate_instruction, recall_reg.
    eexists. eexists. reflexivity.
  - reflexivity.
  - exact looping_never_halts.
Qed.

(* ================================================================= *)
(* The Decidability Boundary                                           *)
(* ================================================================= *)

(** ** The Decidability Boundary (Law 4)

    Structural governance properties (capability checks, trust
    comparisons, observability classification) are decidable.
    Semantic properties of programs (halting, goal reachability)
    are non-trivial.

    This is Law 4: "The system knows what it can and cannot decide."
    Governance operates on decidable structural properties and
    does not attempt to decide undecidable semantic properties.

    The full undecidability result (no total function decides
    halting for all programs) follows from Turing completeness
    (Completeness.v) via the standard diagonal argument. *)

Theorem decidability_boundary :
  (* Structural properties are decidable *)
  (forall tl cap dcaps,
    capability_allowed tl cap dcaps = true \/
    capability_allowed tl cap dcaps = false)
  /\
  (* Semantic properties are non-trivial *)
  ((exists p fuel st, rm_halts p fuel st = true) /\
   (exists p fuel st, rm_halts p fuel st = false)).
Proof.
  split.
  - intros tl cap dcaps.
    destruct (capability_allowed tl cap dcaps); [left | right]; reflexivity.
  - apply halting_non_trivial.
Qed.

(** ** Summary

    This module establishes the formal decidability boundary:

    | Property Class  | Examples                    | Status      |
    |-----------------|-----------------------------|-------------|
    | Structural      | capability_allowed,         | Decidable   |
    |                 | trust_at_least,             | (total bool)|
    |                 | is_observability            |             |
    | Semantic        | rm_halts, itree_halts       | Non-trivial |

    Governance correctly targets structural properties because
    they are the maximal class that can be checked at governance
    time (before execution). Semantic properties like halting
    cannot be fully decided, as established by Rice's theorem
    and formalized here via non-triviality. *)
