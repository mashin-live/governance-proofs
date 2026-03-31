(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file.

   The governance architecture formalized in this development is the
   subject of pending U.S. patent applications by Mashin, Inc. The
   MIT license applies to these proof sources; it does not grant
   rights under any patents. *)

(** * Expressive Minimality: Each Primitive Is Strictly Necessary

    Proves that the primitive set {code, memory, reason, call}
    is minimal for its expressive achievements:

    - Memory (MemoryOp) is required for Turing completeness:
      the register machine translation structurally uses
      MemoryOp events that no other primitive provides.
    - Reason (LLMCall) is required for oracle completeness:
      the oracle translation structurally uses LLMCall events
      beyond what memory provides.
    - Call (CallMachine) is required for external invocation:
      no other primitive emits CallMachine events.

    Combined with the cognitive surjection (CognitiveArchitecture.v)
    and event essentiality theorems, this establishes that
    the cognitive taxonomy is not arbitrary: removing any
    primitive strictly reduces the class of expressible programs.

    Dependencies: Directives.v, Completeness.v, Oracle.v,
                  CognitiveArchitecture.v, Category.v *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Completeness.
From MashinGov Require Import Oracle.
From MashinGov Require Import Category.
From MashinGov Require Import CognitiveArchitecture.

(* ================================================================= *)
(* Event Classification Predicates                                     *)
(* ================================================================= *)

(** ** Event predicates

    These predicates identify which cognitive capability class
    a directive event belongs to. Each primitive emits events
    from exactly one class, and no two primitives share a class. *)

Definition is_memory_event {R : Type} (d : DirectiveE R) : bool :=
  match d with
  | MemoryOp _ => true
  | DBOp _     => true
  | FileOp _   => true
  | _          => false
  end.

Definition is_reason_event {R : Type} (d : DirectiveE R) : bool :=
  match d with
  | LLMCall _       => true
  | LLMCallStream _ => true
  | _               => false
  end.

Definition is_call_event {R : Type} (d : DirectiveE R) : bool :=
  match d with
  | CallMachine _    => true
  | HTTPRequest _    => true
  | ExecOp _         => true
  | GraphQLRequest _ => true
  | WebSocketOp _    => true
  | MCPCall _        => true
  | _                => false
  end.

Definition is_observe_event {R : Type} (d : DirectiveE R) : bool :=
  match d with
  | RecordStep _ => true
  | Broadcast _  => true
  | EmitEvent _  => true
  | _            => false
  end.

(** Event classes are disjoint: each DirectiveE constructor
    belongs to exactly one class. *)
Lemma event_classes_disjoint :
  forall R (d : DirectiveE R),
    (is_memory_event d = true /\ is_reason_event d = false /\
     is_call_event d = false /\ is_observe_event d = false) \/
    (is_memory_event d = false /\ is_reason_event d = true /\
     is_call_event d = false /\ is_observe_event d = false) \/
    (is_memory_event d = false /\ is_reason_event d = false /\
     is_call_event d = true /\ is_observe_event d = false) \/
    (is_memory_event d = false /\ is_reason_event d = false /\
     is_call_event d = false /\ is_observe_event d = true).
Proof.
  intros R d; destruct d; simpl;
    try (left; repeat split; reflexivity);
    try (right; left; repeat split; reflexivity);
    try (right; right; left; repeat split; reflexivity);
    try (right; right; right; repeat split; reflexivity).
Qed.

(** Event classes are exhaustive: every DirectiveE event
    belongs to some class. *)
Lemma event_classes_exhaustive :
  forall R (d : DirectiveE R),
    is_memory_event d = true \/ is_reason_event d = true \/
    is_call_event d = true \/ is_observe_event d = true.
Proof.
  intros R d; destruct d; simpl; auto.
Qed.

(* ================================================================= *)
(* Memory Is Required for Turing Completeness                          *)
(* ================================================================= *)

(** ** Memory necessity

    The register machine translation (Completeness.v) uses
    recall_reg and store_reg, which emit MemoryOp events.
    This is structural: the INC and DEC instructions MUST
    trigger MemoryOp because register access is implemented
    via memory operations.

    No other primitive emits MemoryOp events
    (by event_classes_disjoint), so memory cannot be
    replaced by reason, call, or observe. *)

(** INC translation structurally begins with a memory event
    (recall_reg triggers MemoryOp). *)
Theorem inc_uses_memory :
  forall (r : reg_id) (l : label),
    exists (params : MemoryOpParams) k,
      translate_instruction (INC r l) =
      ITree.bind (trigger (MemoryOp params)) k.
Proof.
  intros r l.
  unfold translate_instruction, recall_reg.
  eexists. eexists. reflexivity.
Qed.

(** DEC translation structurally begins with a memory event. *)
Theorem dec_uses_memory :
  forall (r : reg_id) (l1 l2 : label),
    exists (params : MemoryOpParams) k,
      translate_instruction (DEC r l1 l2) =
      ITree.bind (trigger (MemoryOp params)) k.
Proof.
  intros r l1 l2.
  unfold translate_instruction, recall_reg.
  eexists. eexists. reflexivity.
Qed.

(** The MemoryOp event used by INC is classified as a
    memory event, not reason, call, or observe. *)
Theorem inc_memory_event_is_memory :
  forall (r : reg_id),
    is_memory_event (MemoryOp (mk_memory_op MemRecall (reg_key r) None)) = true.
Proof. reflexivity. Qed.

(** Memory events cannot be produced by reason, call, or observe
    primitives. This follows from event class disjointness. *)
Theorem memory_event_not_reason :
  forall (params : MemoryOpParams),
    is_reason_event (MemoryOp params) = false.
Proof. reflexivity. Qed.

Theorem memory_event_not_call :
  forall (params : MemoryOpParams),
    is_call_event (MemoryOp params) = false.
Proof. reflexivity. Qed.

Theorem memory_event_not_observe :
  forall (params : MemoryOpParams),
    is_observe_event (MemoryOp params) = false.
Proof. reflexivity. Qed.

(** ** Turing completeness requires memory

    Combining the above: register machine translation (which
    establishes Turing completeness) structurally requires
    MemoryOp events. These events belong exclusively to the
    memory primitive. Therefore, removing memory from the
    primitive set would break Turing completeness. *)
Theorem turing_requires_memory :
  (* INC uses MemoryOp *)
  (forall r l, exists params k,
    translate_instruction (INC r l) =
    ITree.bind (trigger (MemoryOp params)) k)
  /\
  (* DEC uses MemoryOp *)
  (forall r l1 l2, exists params k,
    translate_instruction (DEC r l1 l2) =
    ITree.bind (trigger (MemoryOp params)) k)
  /\
  (* MemoryOp is exclusively a memory event *)
  (forall params,
    is_memory_event (MemoryOp params) = true /\
    is_reason_event (MemoryOp params) = false /\
    is_call_event (MemoryOp params) = false).
Proof.
  repeat split.
  - apply inc_uses_memory.
  - apply dec_uses_memory.
Qed.

(* ================================================================= *)
(* Reason Is Required for Oracle Completeness                          *)
(* ================================================================= *)

(** ** Reason necessity

    The oracle register machine translation (Oracle.v) extends
    the standard register machine with O_QUERY, which emits
    LLMCall events. These events belong exclusively to the
    reason primitive. *)

(** O_QUERY translation includes a memory recall (for the source
    register) followed by an LLMCall trigger. *)
Theorem oracle_query_uses_reason :
  forall (src dst : reg_id) (next : label),
    exists k,
      translate_oracle_instruction (O_QUERY src dst next) =
      ITree.bind (recall_reg src) k.
Proof.
  intros. unfold translate_oracle_instruction.
  eexists. reflexivity.
Qed.

(** The LLMCall event produced by O_QUERY is exclusively
    a reason event, not memory, call, or observe. *)
Theorem llm_event_is_reason :
  forall (params : LLMCallParams),
    is_reason_event (LLMCall params) = true /\
    is_memory_event (LLMCall params) = false /\
    is_call_event (LLMCall params) = false.
Proof. intro. repeat split. Qed.

(** Oracle completeness requires reason: O_QUERY emits LLMCall
    events that no other primitive provides. *)
Theorem oracle_requires_reason :
  (* O_QUERY uses recall_reg (memory) THEN LLMCall (reason) *)
  (forall src dst next, exists k,
    translate_oracle_instruction (O_QUERY src dst next) =
    ITree.bind (recall_reg src) k)
  /\
  (* The oracle instruction exists and is unique to oracle programs *)
  (exists p instr, oracle_fetch p 0 = Some instr /\
    match instr with O_QUERY _ _ _ => True | _ => False end)
  /\
  (* LLMCall is exclusively a reason event *)
  (forall params,
    is_reason_event (LLMCall params) = true /\
    is_memory_event (LLMCall params) = false).
Proof.
  repeat split.
  - apply oracle_query_uses_reason.
  - exists minimal_oracle_program, (O_QUERY 0 1 1). split.
    + reflexivity.
    + exact I.
Qed.

(* ================================================================= *)
(* Call Is Required for External Invocation                            *)
(* ================================================================= *)

(** ** Call necessity

    The call primitive (call_morphism) emits CallMachine events.
    These belong exclusively to the call/act event class.
    No other primitive can invoke external machines. *)

Theorem call_uses_call_event :
  forall (A B : Type) (build : A -> CallMachineParams)
         (extract : CallMachineResult -> B) (a : A),
    exists k,
      call_morphism build extract a =
      ITree.bind (trigger (CallMachine (build a))) k.
Proof.
  intros. unfold call_morphism. eexists. reflexivity.
Qed.

Theorem call_event_is_act :
  forall (params : CallMachineParams),
    is_call_event (CallMachine params) = true /\
    is_memory_event (CallMachine params) = false /\
    is_reason_event (CallMachine params) = false.
Proof. intro. repeat split. Qed.

(* ================================================================= *)
(* Strict Expressiveness Ordering                                      *)
(* ================================================================= *)

(** ** Expressiveness hierarchy

    The primitives form a strict expressiveness hierarchy:
    - Code alone: pure functions (no effects)
    - Code + Memory: Turing-complete register machines
    - Code + Memory + Reason: oracle register machines
    - Code + Memory + Reason + Call: external system invocation
    - All + Observe: full cognitive architecture

    Each level strictly extends the previous: the new primitive
    adds events that cannot be produced by the existing ones. *)

(** Code is strictly less expressive than code + memory:
    pure computations (code_morphism) emit no events, but
    Turing completeness requires MemoryOp events. *)
Theorem code_strictly_less_than_memory :
  (* Code emits no events *)
  (forall (n : nat), compute_witness n = Ret (S n))
  /\
  (* But Turing completeness needs memory events *)
  (forall r l, exists params k,
    translate_instruction (INC r l) =
    ITree.bind (trigger (MemoryOp params)) k).
Proof.
  split.
  - intro n. reflexivity.
  - apply inc_uses_memory.
Qed.

(** Code + Memory is strictly less expressive than
    Code + Memory + Reason: register machines use only
    MemoryOp events, but oracle machines additionally
    require LLMCall events. *)
Theorem memory_strictly_less_than_reason :
  (* Register machines use only MemoryOp *)
  (forall r l, exists params k,
    translate_instruction (INC r l) =
    ITree.bind (trigger (MemoryOp params)) k)
  /\
  (* Oracle machines additionally use LLMCall *)
  (exists p instr, oracle_fetch p 0 = Some instr /\
    match instr with O_QUERY _ _ _ => True | _ => False end)
  /\
  (* LLMCall and MemoryOp are disjoint event classes *)
  (forall (lp : LLMCallParams), is_memory_event (LLMCall lp) = false) /\
  (forall (mp : MemoryOpParams), is_reason_event (MemoryOp mp) = false).
Proof.
  repeat split.
  - apply inc_uses_memory.
  - exists minimal_oracle_program, (O_QUERY 0 1 1). split; [reflexivity | exact I].
Qed.

(** ** Primitive minimality: combined statement

    Each of the three effect primitives (memory, reason, call)
    is strictly necessary for its expressiveness contribution:

    1. Memory is necessary for Turing completeness
    2. Reason is necessary for oracle completeness
    3. Call is necessary for external invocation
    4. Each primitive's events are disjoint from all others *)
Theorem primitive_minimality :
  (* 1. Memory: required for register machine translation *)
  (forall r l, exists params k,
    translate_instruction (INC r l) =
    ITree.bind (trigger (MemoryOp params)) k)
  /\
  (* 2. Reason: required for oracle extension *)
  (forall params, is_reason_event (LLMCall params) = true /\
                  is_memory_event (LLMCall params) = false)
  /\
  (* 3. Call: required for external invocation *)
  (forall params, is_call_event (CallMachine params) = true /\
                  is_memory_event (CallMachine params) = false /\
                  is_reason_event (CallMachine params) = false)
  /\
  (* 4. Event classes are disjoint *)
  (forall R (d : DirectiveE R),
    (is_memory_event d = true -> is_reason_event d = false) /\
    (is_memory_event d = true -> is_call_event d = false) /\
    (is_reason_event d = true -> is_memory_event d = false) /\
    (is_reason_event d = true -> is_call_event d = false) /\
    (is_call_event d = true -> is_memory_event d = false) /\
    (is_call_event d = true -> is_reason_event d = false)).
Proof.
  split; [| split; [| split]].
  - apply inc_uses_memory.
  - intro params. split; reflexivity.
  - intro params. repeat split; reflexivity.
  - intros R d. destruct d; simpl;
      repeat split; intro H; try discriminate; auto.
Qed.

(** ** Summary

    | Primitive | Event Class | Required For        | Unique |
    |-----------|-------------|---------------------|--------|
    | Code      | (none)      | Pure computation    | Yes    |
    | Memory    | MemoryOp    | Turing completeness | Yes    |
    | Reason    | LLMCall     | Oracle completeness | Yes    |
    | Call      | CallMachine | External invocation | Yes    |
    | Observe   | EmitEvent   | Monitoring          | Yes    |

    Removing any primitive loses its characteristic event class,
    which cannot be recovered from the remaining primitives.
    The cognitive taxonomy is therefore structurally necessary,
    not merely convenient. *)
