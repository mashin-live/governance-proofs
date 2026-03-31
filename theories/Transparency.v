(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file.

   The governance architecture formalized in this development is the
   subject of pending U.S. patent applications by Mashin, Inc. The
   MIT license applies to these proof sources; it does not grant
   rights under any patents. *)

(** * Transparency: Governance Is Semantically Transparent on Permitted Executions

    The central strengthening theorem: if governance never denies
    (all GovCheck events return true), then the governed interpretation,
    after erasing governance-only events, is observationally equivalent
    to the ungoverned interpretation.

    This converts the safety result ("all programs are governed") into
    a preservation result ("governance does not alter the semantics of
    permitted programs").

    Key results:
    - [gov_step_permissive]: single-directive transparency (Lemma 1)
    - [governed_transparency]: the main transparency theorem
    - [governed_goal_preservation]: strengthened goal preservation
    - [governed_same_result]: same return values under permissive governance

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

(** Helper: bind_ret_r as Leibniz equality for void1.
    This avoids universe polymorphism issues when rewriting
    inside interp contexts. *)
Lemma bind_ret_r_void1 : forall R (t : itree void1 R),
  ITree.bind t (fun x => Ret x) = t.
Proof.
  intros. apply bisimulation_is_eq. apply bind_ret_r.
Qed.

(* ================================================================= *)
(* Permission Predicate                                                *)
(* ================================================================= *)

(** ** Permission: all governance checks return true

    A governed tree is "permitted" if on every path, every GovCheck
    event is resolved with [true]. This means the Gov pipeline never
    takes the spin (denial) branch.

    We define this as a property of a handler for GovE events:
    the permissive handler always returns true. *)

(** The permissive GovE handler: all checks pass. *)
Definition permissive_gov : forall X, GovE X -> X :=
  fun X e =>
    match e with
    | GovCheck _ => true
    end.

(** The permissive handler for the full GovIOE type: governance
    checks return true, IO events are handled by an arbitrary
    IO handler. *)
Definition permissive_handler (io_h : forall X, IOE X -> X)
  : forall X, GovIOE X -> X :=
  fun X e =>
    match e with
    | inl1 ge => permissive_gov X ge
    | inr1 ie => io_h X ie
    end.

(* ================================================================= *)
(* Lemma 1: Single-Directive Transparency                              *)
(* ================================================================= *)

(** ** Gov-step transparency

    For a single directive d, under permissive governance,
    Gov h d reduces through the pre-governance checks (all true),
    runs the base handler, goes through post-governance (all true),
    and returns the same result as h d.

    We prove this by direct computation: unfold Gov, resolve each
    GovCheck to true via the permissive handler, and show the
    result is the lift of (h R d). *)

Section SingleStep.

  Variable h : base_handler.

  (** Helper: the permissive handler interprets pre_governance to Ret true. *)
  Lemma interp_pre_gov_permissive :
    forall (io_h : forall X, IOE X -> X),
      @eutt void1 bool bool eq
        (interp (fun X e => Ret (permissive_handler io_h X e)) pre_governance)
        (Ret true).
  Proof.
    intros io_h.
    unfold pre_governance, gov_check.
    rewrite interp_bind. rewrite interp_trigger.
    unfold subevent, resum, ReSum_id, id_, Id_IFun.
    unfold permissive_handler, permissive_gov. cbn.
    rewrite bind_ret_l. simpl.
    rewrite interp_bind. rewrite interp_trigger.
    unfold subevent, resum, ReSum_id, id_, Id_IFun.
    unfold permissive_handler, permissive_gov. cbn.
    rewrite bind_ret_l. simpl.
    rewrite interp_bind. rewrite interp_trigger.
    unfold subevent, resum, ReSum_id, id_, Id_IFun.
    unfold permissive_handler, permissive_gov. cbn.
    rewrite bind_ret_l. simpl.
    rewrite interp_trigger.
    unfold subevent, resum, ReSum_id, id_, Id_IFun.
    unfold permissive_handler, permissive_gov. cbn.
    reflexivity.
  Qed.

  (** Helper: the permissive handler interprets post_governance to Ret true. *)
  Lemma interp_post_gov_permissive :
    forall (io_h : forall X, IOE X -> X),
      @eutt void1 bool bool eq
        (interp (fun X e => Ret (permissive_handler io_h X e)) post_governance)
        (Ret true).
  Proof.
    intros io_h.
    unfold post_governance, gov_check.
    rewrite interp_bind. rewrite interp_trigger.
    unfold subevent, resum, ReSum_id, id_, Id_IFun.
    unfold permissive_handler, permissive_gov. cbn.
    rewrite bind_ret_l. simpl.
    rewrite interp_bind. rewrite interp_trigger.
    unfold subevent, resum, ReSum_id, id_, Id_IFun.
    unfold permissive_handler, permissive_gov. cbn.
    rewrite bind_ret_l. simpl.
    rewrite interp_bind. rewrite interp_trigger.
    unfold subevent, resum, ReSum_id, id_, Id_IFun.
    unfold permissive_handler, permissive_gov. cbn.
    rewrite bind_ret_l. simpl.
    rewrite interp_ret.
    reflexivity.
  Qed.

  (** Lemma 1: Single-directive transparency.

      Under permissive interpretation, Gov h d produces the same
      final result as h d. The governance events are resolved to
      true and erased; the base handler runs identically. *)
  Lemma gov_step_permissive :
    forall (io_h : forall X, IOE X -> X) R (d : DirectiveE R),
      @eutt void1 R R eq
        (interp (fun X e => Ret (permissive_handler io_h X e))
                (Gov h R d))
        (interp (fun X e => Ret (io_h X e))
                (h R d)).
  Proof.
    intros io_h R d.
    unfold Gov.
    (* Step 1: interp distributes over the outer bind *)
    rewrite interp_bind.
    (* Step 2: pre_governance under permissive evaluates to Ret true *)
    rewrite (interp_pre_gov_permissive io_h).
    rewrite bind_ret_l. simpl.
    (* Step 3: interp distributes over the lift_io bind *)
    rewrite interp_bind.
    (* Step 4: lift_io under interp simplifies via interp_translate *)
    unfold lift_io.
    rewrite interp_translate.
    (* Step 5: rewrite RHS as (bind rhs Ret) so both sides are binds *)
    match goal with
    | |- @eutt _ _ _ _ _ ?t => set (rhs := t)
    end.
    rewrite <- (bind_ret_r_void1 R rhs).
    (* Now both sides are binds: bind body cont ≈ bind rhs Ret *)
    eapply eutt_clo_bind.
    - (* Body: interp (permissive o inr1) (h R d) ≈ rhs *)
      subst rhs. apply eutt_interp.
      + intros X0 e. cbn. reflexivity.
      + reflexivity.
    - (* Continuation: cont r ≈ Ret r *)
      intros r1 r2 Hr. subst.
      rewrite interp_bind.
      rewrite (interp_post_gov_permissive io_h).
      rewrite bind_ret_l.
      rewrite interp_ret.
      reflexivity.
  Qed.

End SingleStep.

(* ================================================================= *)
(* Main Transparency Theorem                                           *)
(* ================================================================= *)

(** ** Governed Transparency

    The main result: under permissive interpretation, the governed
    interpretation produces the same final value as the ungoverned
    interpretation.

    Formally: for any IO handler io_h, base handler h, and program t,

      interp (permissive io_h) (interp (Gov h) t)
      ≈
      interp io_h (interp h t)

    where ≈ is eutt eq (equivalence up to tau).

    This is stronger than the safety theorem: it says governance
    is transparent (not just safe) on permitted executions.

    Proof strategy (following the review recommendation):
    - Ret and Tau cases: straightforward by interp equations
    - Vis d k case: use Lemma 1 (gov_step_permissive) for the body,
      then coinduction for the continuation
    - The key trick: guclo eqit_clo_bind threads the bind through
      without expanding into the wrong nested bind *)

Theorem governed_transparency :
  forall (h : base_handler) (io_h : forall X, IOE X -> X) R
         (t : itree DirectiveE R),
    @eutt void1 R R eq
      (interp (fun X e => Ret (permissive_handler io_h X e))
              (interp (Gov h) t))
      (interp (fun X e => Ret (io_h X e))
              (interp h t)).
Proof.
  intros h io_h R.
  ginit. gcofix CIH. intros t.
  rewrite (bisimulation_is_eq _ _ (@unfold_interp _ _ _ (Gov h) t)).
  rewrite (bisimulation_is_eq _ _ (@unfold_interp _ _ _ h t)).
  destruct (observe t) eqn:Ht.
  - (* Ret: both sides reduce to Ret r0 *)
    cbn.
    rewrite (bisimulation_is_eq _ _ (interp_ret _)).
    rewrite (bisimulation_is_eq _ _ (interp_ret _)).
    gstep. constructor. auto.
  - (* Tau: both sides step through Tau *)
    cbn.
    rewrite (bisimulation_is_eq _ _ (interp_tau _)).
    rewrite (bisimulation_is_eq _ _ (interp_tau _)).
    gstep. constructor.
    gbase. apply CIH.
  - (* Vis d k: the hard case *)
    cbn.
    (* LHS: interp permissive (Gov h X e >>= fun r => Tau (interp (Gov h) (k r))) *)
    (* RHS: interp io_h (h X e >>= fun r => Tau (interp h (k r))) *)
    rewrite (bisimulation_is_eq _ _ (interp_bind _ _ _)).
    rewrite (bisimulation_is_eq _ _ (interp_bind _ _ _)).
    (* Use eqit_clo_bind: show the bodies are eutt and continuations agree *)
    guclo eqit_clo_bind.
    econstructor.
    + (* Bodies: Gov h applied to d vs h applied to d, under permissive interp *)
      apply gov_step_permissive.
    + (* Continuations: after getting the same result r, Tau + recursive call *)
      intros r1 r2 Hr. subst.
      rewrite (bisimulation_is_eq _ _ (interp_tau _)).
      rewrite (bisimulation_is_eq _ _ (interp_tau _)).
      gstep. constructor.
      gbase. apply CIH.
Qed.

(* ================================================================= *)
(* Corollaries                                                         *)
(* ================================================================= *)

(** Goal reachability under governed interpretation:
    if a program reaches a goal under ungoverned interpretation
    and governance permits, the governed interpretation reaches
    the same goal. *)
Corollary governed_goal_preservation :
  forall (h : base_handler) (io_h : forall X, IOE X -> X) R
         (G : R -> Prop) (t : itree DirectiveE R) (v : R),
    G v ->
    @eutt void1 R R eq
      (interp (fun X e => Ret (io_h X e)) (interp h t))
      (Ret v) ->
    @eutt void1 R R eq
      (interp (fun X e => Ret (permissive_handler io_h X e))
              (interp (Gov h) t))
      (Ret v).
Proof.
  intros h io_h R G t v Hgoal Hreach.
  rewrite (governed_transparency h io_h R t).
  exact Hreach.
Qed.

(** Semantic equivalence: the governed and ungoverned computations
    produce the same observable behavior (same IO events, same return
    values) when governance permits. *)
Corollary governed_same_result :
  forall (h : base_handler) (io_h : forall X, IOE X -> X) R
         (t : itree DirectiveE R) (v : R),
    @eutt void1 R R eq
      (interp (fun X e => Ret (io_h X e)) (interp h t))
      (Ret v) ->
    @eutt void1 R R eq
      (interp (fun X e => Ret (permissive_handler io_h X e))
              (interp (Gov h) t))
      (Ret v).
Proof.
  intros h io_h R t v Hret.
  rewrite (governed_transparency h io_h R t).
  exact Hret.
Qed.

(** ** Summary

    This module establishes the semantic transparency of governance:

    | Property | Statement |
    |----------|-----------|
    | Single-step | Gov h d under permissive interp ≈ h d under IO interp |
    | Global | interp permissive (interp (Gov h) t) ≈ interp io_h (interp h t) |
    | Goal preservation | Goals reachable ungoverned are reachable governed |
    | Same result | Same return values under permissive governance |

    Combined with the safety theorem (governed_interp_safe), this
    gives: governance is safe AND transparent on permitted executions.
    Governance restricts which programs execute (safety), but does not
    alter the semantics of programs it permits (transparency). *)
