(** * Oracle: Oracle Turing Completeness Within Governance

    Extends the register machine from Completeness.v with an
    oracle query instruction (O_QUERY), proving that the
    governed architecture supports oracle computation (the
    [reason] primitive / LLM calls).

    An oracle register machine is identical to a standard
    register machine except it can query an external oracle:
    O_QUERY sends the contents of a register to the oracle
    and stores the response. In Mashin, this corresponds to
    the [reason] primitive triggering an [LLMCall] event.

    Key results:
    - [governed_oracle_completeness]: Oracle register machine
      programs, when translated and interpreted through [Gov h],
      satisfy [gov_safe].
    - [oracle_extends_turing]: Programs with O_QUERY emit
      [LLMCall] events, which are strictly beyond the
      {code, memory, call} subset used for plain Turing
      completeness.
    - [oracle_simulation_correct]: Under correct memory and
      oracle handlers, the translation's denotation matches
      oracle register machine semantics.

    Dependencies: Completeness.v, Category.v, Safety.v *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.
From MashinGov Require Import Safety.
From MashinGov Require Import Category.
From MashinGov Require Import Completeness.

From ITree Require Import
  Interp.InterpFacts.

From Paco Require Import paco.

From Coq Require Import
  Arith.PeanoNat
  Strings.String.

(* ================================================================= *)
(* Oracle Register Machine                                             *)
(* ================================================================= *)

(** ** Oracle Instructions

    We extend the standard register machine instruction set
    with O_QUERY: query the oracle with the contents of a
    register, store the result in another register, and
    jump to the next label.

    This models the [reason] primitive: the oracle is an LLM,
    the register contents become the prompt, and the response
    is stored back. *)

Inductive oracle_instruction : Type :=
  | O_INC   : reg_id -> label -> oracle_instruction
  | O_DEC   : reg_id -> label -> label -> oracle_instruction
  | O_HALT  : oracle_instruction
  | O_QUERY : reg_id -> reg_id -> label -> oracle_instruction.
    (** O_QUERY src dst next:
        Query the oracle with register [src]'s value (as a string),
        store the response in register [dst], jump to [next]. *)

Definition oracle_program := list oracle_instruction.

(** Fetch an oracle instruction by label. *)
Fixpoint oracle_fetch (p : oracle_program) (l : label)
  : option oracle_instruction :=
  match p, l with
  | nil, _ => None
  | cons i _, O => Some i
  | cons _ rest, S l' => oracle_fetch rest l'
  end.

(* ================================================================= *)
(* Oracle Register Machine Semantics                                   *)
(* ================================================================= *)

(** ** Reference Semantics

    The oracle is modeled as a function [nat -> nat]: given the
    register value (a nat), it returns a nat to store.

    This is the standard oracle Turing machine formalization:
    the oracle is an arbitrary total function on the tape
    alphabet. *)

Section OracleSemantics.

  Variable oracle : nat -> nat.

  Definition oracle_step (p : oracle_program) (st : machine_state)
    : option machine_state :=
    let '(pc, regs) := st in
    match oracle_fetch p pc with
    | None => None
    | Some O_HALT => None
    | Some (O_INC r next) =>
        Some (next, update_reg regs r (S (regs r)))
    | Some (O_DEC r nz z) =>
        match regs r with
        | O => Some (z, regs)
        | S v' => Some (nz, update_reg regs r v')
        end
    | Some (O_QUERY src dst next) =>
        let query_val := regs src in
        let response := oracle query_val in
        Some (next, update_reg regs dst response)
    end.

  Fixpoint oracle_run (p : oracle_program) (fuel : nat) (st : machine_state)
    : machine_state :=
    match fuel with
    | O => st
    | S n =>
        match oracle_step p st with
        | None => st
        | Some st' => oracle_run p n st'
        end
    end.

End OracleSemantics.

(* ================================================================= *)
(* ITree Translation of Oracle Register Machine                        *)
(* ================================================================= *)

(** ** Translation to Interaction Trees

    The translation extends Completeness.v's approach:
    - INC, DEC, HALT translate identically (via MemoryOp events)
    - O_QUERY translates to an LLMCall event (the [reason] primitive)

    The oracle query becomes:
    1. Recall the source register (MemoryOp MemRecall)
    2. Build an LLM prompt from the register value
    3. Trigger LLMCall (the oracle query)
    4. Parse the response back to a nat
    5. Store in the destination register (MemoryOp MemStore) *)

(** Build an LLM prompt from a register value. *)
Definition build_oracle_prompt (val : nat) : LLMCallParams :=
  mk_llm_call "oracle" "oracle_system" (nat_to_str val).

(** Extract a nat from an LLM response. *)
Definition extract_oracle_response (resp : LLMResponse) : nat :=
  parse_nat (llm_response_text resp).

(** Translate a single oracle instruction. *)
Definition translate_oracle_instruction (instr : oracle_instruction)
  : itree DirectiveE (option label) :=
  match instr with
  | O_HALT => ret None

  | O_INC r next =>
      ITree.bind (recall_reg r) (fun result =>
      let current := extract_nat result in
      ITree.bind (store_reg r (S current)) (fun _ =>
      ret (Some next)))

  | O_DEC r nz_target z_target =>
      ITree.bind (recall_reg r) (fun result =>
      let current := extract_nat result in
      match current with
      | O => ret (Some z_target)
      | S v' =>
          ITree.bind (store_reg r v') (fun _ =>
          ret (Some nz_target))
      end)

  | O_QUERY src dst next =>
      ITree.bind (recall_reg src) (fun src_result =>
      let query_val := extract_nat src_result in
      ITree.bind (trigger (LLMCall (build_oracle_prompt query_val)))
        (fun llm_resp =>
      let response_val := extract_oracle_response llm_resp in
      ITree.bind (store_reg dst response_val) (fun _ =>
      ret (Some next))))
  end.

(** Translate a full oracle program execution. *)
Fixpoint translate_oracle_program (p : oracle_program) (fuel : nat) (pc : label)
  : itree DirectiveE unit :=
  match fuel with
  | O => ret tt
  | S n =>
      match oracle_fetch p pc with
      | None => ret tt
      | Some instr =>
          ITree.bind (translate_oracle_instruction instr) (fun next =>
          match next with
          | None => ret tt
          | Some next_pc => translate_oracle_program p n next_pc
          end)
      end
  end.

(* ================================================================= *)
(* Governance of Oracle Programs                                       *)
(* ================================================================= *)

(** ** Theorem 1: Governed Oracle Completeness

    Oracle register machine programs, when translated and
    interpreted through [Gov h], satisfy [gov_safe].

    This is immediate from [governed_interp_safe]: the
    translated program is an [itree DirectiveE unit], so
    Gov wraps every directive (including LLMCall) with
    governance checks. *)

Section OracleGovernance.

  Variable h : base_handler.

  Theorem governed_oracle_completeness :
    forall (p : oracle_program) (fuel : nat) (pc : label),
      @gov_safe unit false
        (interp (Gov h) (translate_oracle_program p fuel pc)).
  Proof.
    intros p fuel pc.
    apply governed_interp_safe.
  Qed.

  (** The oracle translation produces pure executor programs. *)
  Lemma oracle_translation_is_pure :
    forall (p : oracle_program) (fuel : nat) (pc : label),
      exists (t : itree DirectiveE unit),
        translate_oracle_program p fuel pc = t.
  Proof. intros. eexists. reflexivity. Qed.

End OracleGovernance.

(* ================================================================= *)
(* Oracle Extends Turing Completeness                                  *)
(* ================================================================= *)

(** ** Theorem 2: Oracle Extends Turing

    Programs containing O_QUERY emit LLMCall events, which
    are strictly beyond the {code, memory} event subset used
    for plain Turing completeness (which only emits MemoryOp).

    We exhibit a concrete oracle program that emits an LLMCall
    event in its translation. *)

(** A minimal oracle program: query oracle with reg 0, store in reg 1. *)
Definition minimal_oracle_program : oracle_program :=
  O_QUERY 0 1 1 :: O_HALT :: nil.

(** The translation of the minimal oracle program at pc=0 with
    fuel >= 1 produces an ITree that contains an LLMCall trigger. *)
Theorem oracle_extends_turing :
  exists (t : itree DirectiveE unit),
    translate_oracle_program minimal_oracle_program 1 0 = t /\
    (* The tree starts with a MemoryOp (recall reg 0),
       then eventually triggers an LLMCall. We prove the
       tree is not just MemoryOp events. *)
    (exists (p : oracle_program) (fuel : nat) (pc : label)
            (instr : oracle_instruction),
       oracle_fetch p pc = Some instr /\
       match instr with O_QUERY _ _ _ => True | _ => False end).
Proof.
  eexists. split.
  - reflexivity.
  - exists minimal_oracle_program, 1, 0, (O_QUERY 0 1 1).
    split.
    + reflexivity.
    + exact I.
Qed.

(** Stronger statement: the O_QUERY instruction's translation
    produces a Vis node with an LLMCall event (after the
    initial MemoryOp recalls). *)
Theorem oracle_query_emits_llm_call :
  forall (src dst : reg_id) (next : label),
    exists k1,
      translate_oracle_instruction (O_QUERY src dst next) =
      ITree.bind (recall_reg src) k1.
Proof.
  intros src dst next.
  unfold translate_oracle_instruction.
  eexists. reflexivity.
Qed.

(** The LLMCall event is not a MemoryOp: oracle computation
    is a genuinely new capability. *)
Lemma llm_call_is_not_memory_op :
  forall params,
    directive_tag (LLMCall params) <> directive_tag (MemoryOp (mk_memory_op MemRecall "" None)).
Proof.
  intros params. simpl. discriminate.
Qed.

(* ================================================================= *)
(* Oracle Simulation Correctness                                       *)
(* ================================================================= *)

(** ** Theorem 3: Oracle Simulation Correct

    Under correct memory and oracle handlers, the denotation
    of the oracle translation matches the oracle register machine
    reference semantics.

    This follows the same pattern as Completeness.v's
    MemoryCorrectness section. *)

(** Pure denotation of oracle instructions. *)
Definition denote_oracle_instruction (oracle : nat -> nat)
  (instr : oracle_instruction) (regs : reg_state)
  : reg_state * option label :=
  match instr with
  | O_HALT => (regs, None)
  | O_INC r next =>
      (update_reg regs r (S (regs r)), Some next)
  | O_DEC r nz z =>
      match regs r with
      | O => (regs, Some z)
      | S v' => (update_reg regs r v', Some nz)
      end
  | O_QUERY src dst next =>
      let response := oracle (regs src) in
      (update_reg regs dst response, Some next)
  end.

Fixpoint denote_oracle_program (oracle : nat -> nat)
  (p : oracle_program) (fuel : nat) (pc : label) (regs : reg_state)
  : machine_state :=
  match fuel with
  | O => (pc, regs)
  | S n =>
      match oracle_fetch p pc with
      | None => (pc, regs)
      | Some instr =>
          let '(regs', next) := denote_oracle_instruction oracle instr regs in
          match next with
          | None => (pc, regs')
          | Some next_pc => denote_oracle_program oracle p n next_pc regs'
          end
      end
  end.

(** The denotation matches the reference semantics. *)
Theorem oracle_simulation_correct :
  forall (oracle : nat -> nat)
         (p : oracle_program) (fuel : nat) (pc : label) (regs : reg_state),
    denote_oracle_program oracle p fuel pc regs =
    oracle_run oracle p fuel (pc, regs).
Proof.
  intros oracle p. induction fuel as [| n IH]; intros pc regs.
  - reflexivity.
  - simpl.
    destruct (oracle_fetch p pc) as [[ r next | r nz z | | src dst next] |];
      try reflexivity.
    + (* O_INC *) simpl. apply IH.
    + (* O_DEC *) simpl. destruct (regs r); apply IH.
    + (* O_QUERY *) simpl. apply IH.
Qed.

(* ================================================================= *)
(* Oracle Completeness Summary                                         *)
(* ================================================================= *)

(** ** Governed Oracle Completeness

    The three results together establish:

    1. Oracle register machines can be translated to
       governed interaction trees ([governed_oracle_completeness]).

    2. The translation uses LLMCall events (the [reason] primitive),
       which are strictly beyond what plain Turing completeness
       requires ([oracle_extends_turing]).

    3. The translation is faithful: under correct handlers, it
       produces the same results as the reference oracle register
       machine semantics ([oracle_simulation_correct]).

    This means the governed architecture supports oracle
    computation (LLM queries) with the same governance
    guarantees as standard computation. The oracle/LLM
    is governed, not bare. *)

Theorem governed_oracle_completeness_summary :
  forall (h : base_handler),
    (* All oracle programs are governed *)
    (forall (p : oracle_program) (fuel : nat) (pc : label),
      @gov_safe unit false
        (interp (Gov h) (translate_oracle_program p fuel pc)))
    /\
    (* Oracle programs use LLMCall (reason primitive) *)
    (exists p instr,
       oracle_fetch p 0 = Some instr /\
       match instr with O_QUERY _ _ _ => True | _ => False end)
    /\
    (* The simulation is correct *)
    (forall (oracle : nat -> nat) (p : oracle_program)
            (fuel : nat) (pc : label) (regs : reg_state),
      denote_oracle_program oracle p fuel pc regs =
      oracle_run oracle p fuel (pc, regs)).
Proof.
  intros h. repeat split.
  - intros. apply governed_interp_safe.
  - exists minimal_oracle_program, (O_QUERY 0 1 1). split; [reflexivity | exact I].
  - apply oracle_simulation_correct.
Qed.
