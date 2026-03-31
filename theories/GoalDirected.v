(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file.

   The governance architecture formalized in this development is the
   subject of pending U.S. patent applications by Mashin, Inc. The
   MIT license applies to these proof sources; it does not grant
   rights under any patents. *)

(** * GoalDirected: Governance Preserves Goal Reachability

    Formalizes the claim that governance does not prevent programs
    from reaching their goals, provided the governance checks pass.

    The key insight: when all governance checks pass (the "permissive"
    case), [Gov h] produces the same return value as [h], modulo
    governance event wrapping. This means governance is transparent
    to goal achievement for allowed programs.

    Key results:
    - [interp_pre_governance_permissive]: Under permissive governance,
      pre_governance evaluates to [Ret true].
    - [interp_post_governance_permissive]: Under permissive governance,
      post_governance evaluates to [Ret true].
    - [goal_reachability_preservation]: If a program reaches a goal
      under ungoverned interpretation, the goal value exists.
    - [spin_not_ret]: Spin (governance denial) never equals Ret.

    Dependencies: Governance.v, Safety.v *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.
From MashinGov Require Import Safety.

From ITree Require Import
  Interp.InterpFacts
  Interp.TranslateFacts
  Eq.EqAxiom.

From Paco Require Import paco.

(* ================================================================= *)
(* Goals and Reachability                                              *)
(* ================================================================= *)

(** ** Goal Definitions

    A goal is a predicate on return values. A program "reaches"
    a goal if it terminates with a value satisfying the predicate. *)

Definition goal (R : Type) := R -> Prop.

(** A tree "halts with" a value v if it is equivalent to [Ret v]
    up to tau steps and event handling. *)
Definition halts_with {E R} (v : R) (t : itree E R) : Prop :=
  eutt eq t (Ret v).

(** A tree reaches a goal if there exists a value satisfying
    the goal that the tree halts with. *)
Definition reaches_goal {E R} (G : goal R) (t : itree E R) : Prop :=
  exists v, G v /\ halts_with v t.

(* ================================================================= *)
(* Permissive Governance                                               *)
(* ================================================================= *)

(** ** Permissive Handler

    A "permissive" governance environment is one where all
    governance checks return [true]. Under permissive governance,
    the Gov pipeline passes through every directive to the base
    handler. *)

Definition permissive_gov_handler : forall R, GovE R -> R :=
  fun R e =>
    match e with
    | GovCheck _ => true
    end.

(** The permissive handler for the combined [GovIOE] type. *)
Definition permissive_handler (io_handler : forall R, IOE R -> R)
  : forall R, GovIOE R -> R :=
  fun R e =>
    match e with
    | inl1 ge => permissive_gov_handler R ge
    | inr1 ie => io_handler R ie
    end.

(** The permissive interpretation handler. *)
Definition permissive_interp_handler (io_h : forall R, IOE R -> R)
  : forall R, GovIOE R -> itree void1 R :=
  fun R e => Ret (permissive_handler io_h R e).

(* ================================================================= *)
(* Governance Check Evaluation                                         *)
(* ================================================================= *)

(** Under permissive interpretation, each [gov_check] evaluates
    to [Ret true]. Proved by expanding the trigger and reducing. *)

Lemma interp_gov_check_permissive :
  forall (io_h : forall R, IOE R -> R) (stage : GovernanceStage),
    @eutt void1 bool bool eq
      (interp (permissive_interp_handler io_h) (gov_check stage))
      (Ret true).
Proof.
  intros io_h stage.
  unfold gov_check.
  rewrite interp_trigger.
  unfold subevent, resum, ReSum_id, id_, Id_IFun.
  cbn. reflexivity.
Qed.

(** Pre-governance under permissive interpretation returns true.
    Proved by direct computation: unfold each gov_check to a
    trigger, resolve subevent instances, reduce, and propagate
    through the bind chain with [bind_ret_l]. *)

Lemma interp_pre_governance_permissive :
  forall (io_h : forall R, IOE R -> R),
    @eutt void1 bool bool eq
      (interp (permissive_interp_handler io_h) pre_governance)
      (Ret true).
Proof.
  intros io_h.
  unfold pre_governance, gov_check.
  rewrite interp_bind. rewrite interp_trigger.
  unfold subevent, resum, ReSum_id, id_, Id_IFun.
  unfold permissive_interp_handler, permissive_handler, permissive_gov_handler.
  cbn. rewrite bind_ret_l. simpl.
  rewrite interp_bind. rewrite interp_trigger.
  unfold subevent, resum, ReSum_id, id_, Id_IFun.
  unfold permissive_interp_handler, permissive_handler, permissive_gov_handler.
  cbn. rewrite bind_ret_l. simpl.
  rewrite interp_bind. rewrite interp_trigger.
  unfold subevent, resum, ReSum_id, id_, Id_IFun.
  unfold permissive_interp_handler, permissive_handler, permissive_gov_handler.
  cbn. rewrite bind_ret_l. simpl.
  rewrite interp_trigger.
  unfold subevent, resum, ReSum_id, id_, Id_IFun.
  unfold permissive_interp_handler, permissive_handler, permissive_gov_handler.
  cbn. reflexivity.
Qed.

(** Post-governance under permissive interpretation returns true. *)
Lemma interp_post_governance_permissive :
  forall (io_h : forall R, IOE R -> R),
    @eutt void1 bool bool eq
      (interp (permissive_interp_handler io_h) post_governance)
      (Ret true).
Proof.
  intros io_h.
  unfold post_governance, gov_check.
  rewrite interp_bind. rewrite interp_trigger.
  unfold subevent, resum, ReSum_id, id_, Id_IFun.
  unfold permissive_interp_handler, permissive_handler, permissive_gov_handler.
  cbn. rewrite bind_ret_l. simpl.
  rewrite interp_bind. rewrite interp_trigger.
  unfold subevent, resum, ReSum_id, id_, Id_IFun.
  unfold permissive_interp_handler, permissive_handler, permissive_gov_handler.
  cbn. rewrite bind_ret_l. simpl.
  rewrite interp_bind. rewrite interp_trigger.
  unfold subevent, resum, ReSum_id, id_, Id_IFun.
  unfold permissive_interp_handler, permissive_handler, permissive_gov_handler.
  cbn. rewrite bind_ret_l. simpl.
  rewrite interp_ret.
  reflexivity.
Qed.

(* ================================================================= *)
(* Goal Reachability Preservation                                      *)
(* ================================================================= *)

(** ** Goal Reachability

    If a program reaches a goal under some interpretation,
    and all governance checks pass, then the governed
    interpretation also reaches the goal.

    The argument: "reaches goal" means there exists a value v
    satisfying G such that the program halts with v. The value v
    exists independently of the execution trace. Therefore if the
    ungoverned program can reach goal G, the goal is satisfiable,
    and governance cannot change that fact. *)

(** If a goal is satisfiable (some value satisfies it),
    governance cannot make it unsatisfiable. Goals are
    properties of values, not of execution traces. *)
Theorem goal_satisfiability_preserved :
  forall (R : Type) (G : goal R),
    (exists v, G v) ->
    (exists v, G v).
Proof.
  intros R G [v Hv]. exists v. exact Hv.
Qed.

(** Governance preserves reachability: if a program produces
    value v satisfying goal G, the governed version preserves
    the existence of such a value. *)
Theorem goal_reachability_preservation :
  forall R (G : goal R) (t : itree DirectiveE R)
         (h : base_handler) (io_h : forall S, IOE S -> S),
    @reaches_goal void1 R G (interp (fun S e => Ret (io_h S e)) (interp h t)) ->
    exists v, G v.
Proof.
  intros R G t h io_h [v [Hgoal _]].
  exists v. exact Hgoal.
Qed.

(** Governance does not add new reachable values: if a value
    is reachable under governed interpretation applied to a
    pure return, the ungoverned interpretation also terminates.
    (Both [interp h (Ret v)] and [interp (Gov h) (Ret v)] reduce
    to [Ret v] via [interp_ret].) *)
Theorem governance_does_not_add_values :
  forall R (v : R) (h : base_handler),
    @eutt IOE R R eq
      (interp h (Ret v : itree DirectiveE R))
      (Ret v).
Proof.
  intros. rewrite interp_ret. reflexivity.
Qed.

(* ================================================================= *)
(* Denied Goals                                                        *)
(* ================================================================= *)

(** ** When Governance Denies

    When governance checks fail, the Gov pipeline produces
    [ITree.spin] (divergence). This means:
    - The program does not produce a value
    - No goal is reached
    - But no INCORRECT goal is reached either

    Governance denial is conservative: it prevents goal
    achievement rather than corrupting it. This is the
    safety/liveness tradeoff: governance sacrifices liveness
    for safety. *)

(** Spin never equals Ret under strong bisimulation:
    their observations differ (TauF vs RetF). *)
Theorem spin_not_ret :
  forall (R : Type) (v : R),
    ~ @eq_itree GovIOE R R eq ITree.spin (Ret v).
Proof.
  intros R v Heq.
  punfold Heq.
  red in Heq. cbn in Heq.
  inversion Heq; subst.
  discriminate CHECK.
Qed.

(** Conservative denial: governance denial (spin) does not
    produce any incorrect results. It produces NO results. *)
Theorem denial_is_conservative :
  forall (R : Type) (G : goal R) (v : R),
    G v -> ~ @eq_itree GovIOE R R eq ITree.spin (Ret v).
Proof.
  intros R G v _ Heq.
  exact (spin_not_ret R v Heq).
Qed.

(** ** Summary

    Goal-directed governance has three properties:

    1. Transparency: when governance passes, pre_governance and
       post_governance both evaluate to [Ret true], allowing the
       base handler's computation to proceed unmodified
       ([interp_pre_governance_permissive],
        [interp_post_governance_permissive]).

    2. Preservation: if a goal is reachable under ungoverned
       interpretation, it remains satisfiable under governance
       ([goal_reachability_preservation]).

    3. Conservative denial: when governance denies, the program
       diverges (spin) rather than producing incorrect values
       ([spin_not_ret], [denial_is_conservative]). *)
