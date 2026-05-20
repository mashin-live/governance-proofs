(* Copyright (c) 2026 Alan Lawrence McCann, mashin, Inc.
   Licensed under MIT. See LICENSE file. *)

(** * DirectiveTotality: Every Effectful Form Maps to a Directive

    Dependencies: Prelude, Directives, TrustSpec, InterpreterSpec *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import TrustSpec.
From MashinGov Require Import InterpreterSpec.

From Coq Require Import Bool.

Section DirectiveTotalityProofs.

  Variable Hash : Type.
  Variable compute_hash : string -> Hash -> Hash.
  Variable genesis_hash : Hash.

  Notation ISt := (InterpreterState Hash).

  (* Use a local definition rather than notation to avoid implicit arg issues *)
  Local Definition idir {R : Type} (d : DirectiveE R) (st : InterpreterState Hash)
    := @interp_directive Hash compute_hash R d st.

  (* ================================================================= *)
  (* Directive Totality                                                  *)
  (* ================================================================= *)

  Theorem directive_totality :
    forall R (d : DirectiveE R),
      (exists cap, capability_for_directive d = Some cap) \/
      (capability_for_directive d = None).
  Proof. intros R d. destruct d; simpl; eauto. Qed.

  Theorem effectful_has_capability :
    forall R (d : DirectiveE R),
      is_observability d = false ->
      exists cap, capability_for_directive d = Some cap.
  Proof.
    intros R d H. unfold is_observability in H.
    destruct (capability_for_directive d) eqn:E;
      [eexists; reflexivity | discriminate].
  Qed.

  Theorem observability_no_capability :
    forall R (d : DirectiveE R),
      is_observability d = true ->
      capability_for_directive d = None.
  Proof.
    intros R d H. unfold is_observability in H.
    destruct (capability_for_directive d); [discriminate | reflexivity].
  Qed.

  (* ================================================================= *)
  (* Capability Soundness (Bidirectional)                                *)
  (* ================================================================= *)

  (** If interp_directive allows, the required capability is allowed
      at the given trust level. *)
  Theorem soundness_forward :
    forall R (d : DirectiveE R) (st : ISt) cap,
      capability_for_directive d = Some cap ->
      (exists h st', idir d st = StepOk Hash h st') ->
      capability_allowed (@is_trust_level Hash st) cap (@is_declared_caps Hash st) = true.
  Proof.
    intros R d st cap Hcap [h [st' H]].
    unfold idir, interp_directive in H. rewrite Hcap in H.
    destruct (capability_allowed (@is_trust_level Hash st) cap (@is_declared_caps Hash st)) eqn:E.
    - auto.
    - discriminate.
  Qed.

  (** If the capability is not allowed, interp_directive denies. *)
  Theorem soundness_reverse :
    forall R (d : DirectiveE R) (st : ISt) cap,
      capability_for_directive d = Some cap ->
      capability_allowed (@is_trust_level Hash st) cap (@is_declared_caps Hash st) = false ->
      exists reason, idir d st = StepDenied Hash reason.
  Proof.
    intros R d st cap Hcap Hdenied.
    unfold idir, interp_directive. rewrite Hcap. rewrite Hdenied.
    eexists. reflexivity.
  Qed.

  (** Bidirectional: allowed iff capability entailed. *)
  Theorem capability_soundness_iff :
    forall R (d : DirectiveE R) (st : ISt) cap,
      capability_for_directive d = Some cap ->
      ((exists h st', idir d st = StepOk Hash h st') <->
       capability_allowed (@is_trust_level Hash st) cap (@is_declared_caps Hash st) = true).
  Proof.
    intros R d st cap Hcap. split.
    - intros [h [st' H]]. unfold idir, interp_directive in H. rewrite Hcap in H.
      destruct (capability_allowed (@is_trust_level Hash st) cap (@is_declared_caps Hash st)) eqn:E;
        [auto | discriminate].
    - intros H. unfold idir, interp_directive. rewrite Hcap. rewrite H.
      eexists. eexists. reflexivity.
  Qed.

  (* ================================================================= *)
  (* Keyword Closure                                                     *)
  (* ================================================================= *)

  Theorem directive_tag_total :
    forall R (d : DirectiveE R),
      exists tag, directive_tag d = tag.
  Proof. intros R d. eexists. reflexivity. Qed.

  Theorem tag_determines_capability :
    forall R1 R2 (d1 : DirectiveE R1) (d2 : DirectiveE R2),
      directive_tag d1 = directive_tag d2 ->
      capability_for_directive d1 = capability_for_directive d2.
  Proof.
    intros R1 R2 d1 d2 Htag.
    destruct d1, d2; simpl in *; try reflexivity; try discriminate.
  Qed.

  (* ================================================================= *)
  (* No Hidden Escape Hatch                                              *)
  (* ================================================================= *)

  Theorem no_escape_hatch :
    forall R (d : DirectiveE R) (st : ISt),
      is_observability d = false ->
      (exists h st', idir d st = StepOk Hash h st') \/
      (exists reason, idir d st = StepDenied Hash reason).
  Proof.
    intros R d st Heff.
    unfold idir, interp_directive.
    destruct (capability_for_directive d) eqn:Ecap.
    - destruct (capability_allowed (@is_trust_level Hash st) c (@is_declared_caps Hash st)).
      + left. eexists. eexists. reflexivity.
      + right. eexists. reflexivity.
    - unfold is_observability in Heff. rewrite Ecap in Heff. discriminate.
  Qed.

End DirectiveTotalityProofs.
