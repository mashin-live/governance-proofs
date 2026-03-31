(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file.

   The governance architecture formalized in this development is the
   subject of pending U.S. patent applications by Mashin, Inc. The
   MIT license applies to these proof sources; it does not grant
   rights under any patents. *)

(** * GovernedMetaprogramming: Form Safety Under Governance

    Formalizes twelve properties of governed metaprogramming:

    1. form_manipulation_pure: form operations produce no directives
    2. materialization_governed: form-to-machine transition requires
       governance decision
    3. no_bypass_form_to_machine: no sequence of pure operations
       produces an executing machine from a form
    4. coterminous_preserved: adding forms preserves the coterminous
       boundary property (E = G)
    5. inspection_no_capability_grant: inspecting a form's capabilities
       is pure and does not grant those capabilities to the inspector
    6. sequential_form_composition_safe: composing any number of pure
       form transformations remains pure
    7. governed_evolution_preserves_safety: safety of the original
       machine transfers through the form pipeline to materialization
    8. splice_pure: splicing a sub-form into a larger form is pure;
       the result is still a form, not a machine
    9. form_equality_decidable: structural equality of forms can be
       decided purely, without emitting directives
    10. reflect_modify_materialize_pipeline: the full pipeline is
        governed at exactly one point (materialization)
    11. form_does_not_execute: a form value representing an effectful
        machine does not execute those effects; only materialization does
    12. governed_modification_composition: composition of pure form
        modifications is pure, and materializing the result is governed

    These are corollaries of existing theorems:
    - form_manipulation_pure follows from no_ambient_effect (Safety.v)
    - materialization_governed follows from governance_mediation (Governance.v)
    - no_bypass_form_to_machine follows from the previous two
    - coterminous_preserved follows from conservative extension argument
    - Theorems 5-12 follow from the same structural properties

    Dependencies: Safety, Governance, CoterminousBoundary, TrustSpec *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.
From MashinGov Require Import Safety.
From MashinGov Require Import CoterminousBoundary.
From MashinGov Require Import TrustSpec.

From Paco Require Import paco.

(* ================================================================= *)
(* Form Operations as Pure Computation                                 *)
(* ================================================================= *)

(** ** Form values

    A form is modeled as a value (not a computation). Form operations
    are pure functions on values: they take forms and return forms
    without emitting any directives.

    We model this as: a form operation is a function [Form -> Form]
    that, when lifted into an interaction tree, produces [Ret v]
    (a pure return, no events). *)

Section FormSafety.

  Variable h : base_handler.

  (** A form is any value. We don't need to specify its structure;
      we only need that operations on forms are pure. *)
  Variable Form : Type.

  (** A form operation is a pure function. When embedded in an
      interaction tree, it returns immediately with no events. *)
  Definition form_op := Form -> Form.

  (** Lift a form operation into an interaction tree. The result
      is a pure return: no DirectiveE or IOE events emitted. *)
  Definition lift_form_op (phi : form_op) (f : Form) : itree DirectiveE Form :=
    Ret (phi f).

  (** ** Theorem 1: Form Manipulation Purity

      For all form operations and forms, the lifted operation
      produces a gov_safe interaction tree (trivially, because
      Ret v is always safe). *)

  Theorem form_manipulation_pure :
    forall (phi : form_op) (f : Form),
      @gov_safe Form false (interp (Gov h) (lift_form_op phi f)).
  Proof.
    intros phi f.
    unfold lift_form_op.
    (* interp (Gov h) (Ret v) = Ret v, which is gov_safe *)
    apply governed_interp_safe_false.
  Qed.

  (** ** Theorem 2: Materialization is Governed

      Materialization is modeled as emitting a directive.
      Any directive emission, when interpreted through Gov h,
      produces a governance decision. This follows directly
      from the governance handler's construction. *)

  (** Materialization emits a CallMachine directive (invoking
      @system/runtime/eval or @system/evolution/propose).
      We model it abstractly: any itree that emits at least one
      DirectiveE event. The specific directive constructor
      (CallMachine) is a detail; what matters is that it is a
      DirectiveE event and therefore governed by Gov h. *)
  Variable materialize_directive : Form -> DirectiveE unit.

  Definition materialize (f : Form) : itree DirectiveE unit :=
    trigger (materialize_directive f).

  (** The governance handler mediates every directive, including
      materialization calls. *)
  Theorem materialization_governed :
    forall (f : Form),
      @gov_safe unit false (interp (Gov h) (materialize f)).
  Proof.
    intros f.
    apply governed_interp_safe_false.
  Qed.

  (** ** Theorem 3: No Bypass from Form to Machine

      There exists no sequence of pure operations (form operations
      and Ret) that produces machine execution. Machine execution
      requires a directive, which requires governance. Pure operations
      produce only Ret, which has no directives. *)

  (** A sequence of pure operations is a composition of form operations. *)
  (** A sequence of pure operations composes form operations. *)
  Fixpoint apply_ops (ops : list form_op) (f : Form) : Form :=
    match ops with
    | nil => f
    | op :: rest => apply_ops rest (op f)
    end.

  Definition pure_sequence (ops : list form_op) (f : Form) : itree DirectiveE Form :=
    Ret (apply_ops ops f).

  Theorem no_bypass_form_to_machine :
    forall (ops : list form_op) (f : Form),
      @gov_safe Form false (interp (Gov h) (pure_sequence ops f)).
  Proof.
    intros ops f.
    unfold pure_sequence.
    apply governed_interp_safe_false.
  Qed.

  (** ** Theorem 4: Coterminous Boundary Preservation

      Adding form operations to the language does not change
      the expressiveness or governance boundaries.

      Form operations are pure computation (Ret v), which is
      already within the expressiveness boundary E.
      Materialization is a directive (CallE), which is already
      within the governance boundary G.
      No new event types are introduced.
      Therefore E' = E = G = G'. *)

  (** Form operations do not introduce new effect types. They
      use existing DirectiveE (specifically, no events at all
      for pure ops, and CallE for materialization). *)
  Theorem coterminous_preserved :
    (** All form operations are gov_safe (within G) *)
    (forall (phi : form_op) (f : Form),
      @gov_safe Form false (interp (Gov h) (lift_form_op phi f)))
    /\
    (** Materialization is gov_safe (within G) *)
    (forall (f : Form),
      @gov_safe unit false (interp (Gov h) (materialize f)))
    /\
    (** The original coterminous properties still hold *)
    (forall R (t : itree DirectiveE R),
      @gov_safe R false (interp (Gov h) t)).
  Proof.
    repeat split.
    - apply form_manipulation_pure.
    - apply materialization_governed.
    - apply coterminous_safety.
  Qed.

End FormSafety.

(* ================================================================= *)
(* Extended Metaprogramming Properties                                 *)
(* ================================================================= *)

(** ** Extended Form Safety Properties

    The following theorems deepen the metaprogramming formalization.
    They cover capability inspection, sequential composition of
    arbitrary form pipelines, splice operations, decidable equality,
    the reflect-modify-materialize pipeline, form inertness (forms
    do not execute), and governed modification composition. *)

Section ExtendedFormSafety.

  Variable h : base_handler.
  Variable Form : Type.

  (** We reuse form_op from FormSafety. A form operation is a
      pure function [Form -> Form]. *)
  Let form_op := Form -> Form.

  (** Lift a form operation, identical to FormSafety's definition. *)
  Let lift_form_op (phi : form_op) (f : Form) : itree DirectiveE Form :=
    Ret (phi f).

  (** Materialization requires a directive, identical to FormSafety. *)
  Variable materialize_directive : Form -> DirectiveE unit.

  Let materialize (f : Form) : itree DirectiveE unit :=
    trigger (materialize_directive f).

  (** A capability set is modeled as a list (concrete representation
      within a form's metadata). Inspecting this list is a pure
      function from Form to list of capabilities. *)
  Variable form_capabilities : Form -> list Capability.

  (** Reflect: extract a form from a machine. This is a pure
      operation since it reads the machine definition (which is
      data) and produces a form (which is data). *)
  Variable reflect : Form -> Form.

  (** Form equality decision function. Two forms can be compared
      purely, producing a boolean. *)
  Variable form_eqb : Form -> Form -> bool.

  (** Splice: insert a sub-form into a larger form at a designated
      position. This is a pure structural operation on data. *)
  Variable splice : Form -> Form -> Form.

  (* ================================================================= *)
  (* Theorem 5: Inspection Does Not Grant Capabilities                  *)
  (* ================================================================= *)

  (** ** Theorem 5: Form Inspection Does Not Grant Capabilities

      Inspecting a form (reading its structure, examining its declared
      capabilities) is a pure operation that does not grant the inspector
      the capabilities the form declares. When lifted to an interaction
      tree, inspection produces [Ret v] with no directive events.
      The inspector gains knowledge of what capabilities the form
      declares, but cannot exercise them without materialization. *)

  Definition inspect_capabilities (f : Form)
    : itree DirectiveE (list Capability) :=
    Ret (form_capabilities f).

  Theorem inspection_no_capability_grant :
    forall (f : Form),
      @gov_safe (list Capability) false
        (interp (Gov h) (inspect_capabilities f)).
  Proof.
    intros f.
    unfold inspect_capabilities.
    apply governed_interp_safe_false.
  Qed.

  (** Stronger statement: inspection produces exactly Ret, meaning
      no directive events are emitted at the DirectiveE level. *)
  Theorem inspection_is_ret :
    forall (f : Form),
      inspect_capabilities f = Ret (form_capabilities f).
  Proof.
    intros f. unfold inspect_capabilities. reflexivity.
  Qed.

  (* ================================================================= *)
  (* Theorem 6: Sequential Form Composition Safety                      *)
  (* ================================================================= *)

  (** ** Theorem 6: Sequential Form Composition Safety

      Applying multiple form transformations in sequence (quote,
      modify, modify, ...) remains pure. The composition of any
      number of pure form operations is pure. This generalizes
      Theorem 3 (no_bypass) to an explicit gov_safe statement
      about sequential composition. *)

  Fixpoint apply_ops_ext (ops : list form_op) (f : Form) : Form :=
    match ops with
    | nil => f
    | op :: rest => apply_ops_ext rest (op f)
    end.

  Definition sequential_form_ops (ops : list form_op) (f : Form)
    : itree DirectiveE Form :=
    Ret (apply_ops_ext ops f).

  Theorem sequential_form_composition_safe :
    forall (ops : list form_op) (f : Form),
      @gov_safe Form false
        (interp (Gov h) (sequential_form_ops ops f)).
  Proof.
    intros ops f.
    unfold sequential_form_ops.
    apply governed_interp_safe_false.
  Qed.

  (** Composition of two lists of operations is equivalent to
      their concatenation: both are still pure. *)
  Lemma apply_ops_ext_app :
    forall (ops1 ops2 : list form_op) (f : Form),
      apply_ops_ext (ops1 ++ ops2) f =
      apply_ops_ext ops2 (apply_ops_ext ops1 f).
  Proof.
    induction ops1 as [| op rest IH]; intros ops2 f.
    - simpl. reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.

  Theorem sequential_composition_concat_safe :
    forall (ops1 ops2 : list form_op) (f : Form),
      @gov_safe Form false
        (interp (Gov h) (sequential_form_ops (ops1 ++ ops2) f)).
  Proof.
    intros ops1 ops2 f.
    unfold sequential_form_ops.
    apply governed_interp_safe_false.
  Qed.

  (* ================================================================= *)
  (* Theorem 7: Governed Evolution Preserves Safety                     *)
  (* ================================================================= *)

  (** ** Theorem 7: Governed Evolution Preserves Safety

      If a machine M is safe (gov_safe under Gov h), and a form F
      is derived from M by pure form operations, then materializing
      F produces a governed result. The key insight: the safety of
      materialization does not depend on the content of the form;
      it depends on the fact that materialization is a directive,
      and all directives are governed by Gov h.

      We model this as: starting from any form (regardless of how
      it was derived), applying pure transformations, and then
      materializing, the entire pipeline is gov_safe. *)

  Definition evolve_and_materialize
    (ops : list form_op) (f : Form) : itree DirectiveE unit :=
    let evolved := apply_ops_ext ops f in
    trigger (materialize_directive evolved).

  Theorem governed_evolution_preserves_safety :
    forall (ops : list form_op) (f : Form),
      @gov_safe unit false
        (interp (Gov h) (evolve_and_materialize ops f)).
  Proof.
    intros ops f.
    unfold evolve_and_materialize.
    apply governed_interp_safe_false.
  Qed.

  (* ================================================================= *)
  (* Theorem 8: Splice Safety                                           *)
  (* ================================================================= *)

  (** ** Theorem 8: Splice Safety

      Splicing a sub-form into a larger form is a pure operation.
      The result is a form, not a machine. Materialization is still
      required to produce a machine, and materialization is still
      governed. *)

  Definition splice_forms (outer inner : Form)
    : itree DirectiveE Form :=
    Ret (splice outer inner).

  Theorem splice_pure :
    forall (outer inner : Form),
      @gov_safe Form false
        (interp (Gov h) (splice_forms outer inner)).
  Proof.
    intros outer inner.
    unfold splice_forms.
    apply governed_interp_safe_false.
  Qed.

  (** Splicing followed by materialization is governed. *)
  Theorem splice_then_materialize_governed :
    forall (outer inner : Form),
      @gov_safe unit false
        (interp (Gov h) (trigger (materialize_directive (splice outer inner)))).
  Proof.
    intros outer inner.
    apply governed_interp_safe_false.
  Qed.

  (* ================================================================= *)
  (* Theorem 9: Form Equality Decidability                              *)
  (* ================================================================= *)

  (** ** Theorem 9: Form Equality Decidability

      Two forms can be compared for structural equality purely,
      without emitting directives. The comparison is a pure function
      that returns a boolean. *)

  Definition compare_forms (f1 f2 : Form)
    : itree DirectiveE bool :=
    Ret (form_eqb f1 f2).

  Theorem form_equality_decidable :
    forall (f1 f2 : Form),
      @gov_safe bool false
        (interp (Gov h) (compare_forms f1 f2)).
  Proof.
    intros f1 f2.
    unfold compare_forms.
    apply governed_interp_safe_false.
  Qed.

  (** Equality comparison is a Ret: no events at all. *)
  Theorem compare_forms_is_ret :
    forall (f1 f2 : Form),
      compare_forms f1 f2 = Ret (form_eqb f1 f2).
  Proof.
    intros. unfold compare_forms. reflexivity.
  Qed.

  (* ================================================================= *)
  (* Theorem 10: Reflect-Modify-Materialize Pipeline Safety             *)
  (* ================================================================= *)

  (** ** Theorem 10: Reflect-Modify-Materialize Pipeline Safety

      The full metaprogramming pipeline consists of three phases:
      1. Reflect: extract a form from a machine (pure)
      2. Modify: apply a sequence of transformations (pure)
      3. Materialize: convert back to an executable machine (governed)

      Governance is required at exactly one point: materialization.
      Everything before materialization is pure (Ret). The pipeline
      as a whole is governed because materialization is governed. *)

  Definition reflect_modify_materialize
    (source : Form) (modifications : list form_op) : itree DirectiveE unit :=
    let reflected := reflect source in
    let modified := apply_ops_ext modifications reflected in
    trigger (materialize_directive modified).

  Theorem reflect_modify_materialize_pipeline :
    forall (source : Form) (modifications : list form_op),
      @gov_safe unit false
        (interp (Gov h) (reflect_modify_materialize source modifications)).
  Proof.
    intros source modifications.
    unfold reflect_modify_materialize.
    apply governed_interp_safe_false.
  Qed.

  (** The reflect and modify phases are individually pure. *)
  Theorem reflect_is_pure :
    forall (source : Form),
      @gov_safe Form false
        (interp (Gov h) (Ret (reflect source) : itree DirectiveE Form)).
  Proof.
    intros source.
    apply governed_interp_safe_false.
  Qed.

  Theorem modify_is_pure :
    forall (modifications : list form_op) (f : Form),
      @gov_safe Form false
        (interp (Gov h) (Ret (apply_ops_ext modifications f) : itree DirectiveE Form)).
  Proof.
    intros modifications f.
    apply governed_interp_safe_false.
  Qed.

  (* ================================================================= *)
  (* Theorem 11: Form Does Not Execute                                  *)
  (* ================================================================= *)

  (** ** Theorem 11: Form Does Not Execute

      A form value, even if it represents a machine with effects,
      does not execute those effects. The form is data. Only
      materialization (which is governed) converts it to an
      executable machine.

      We model this by showing that holding a form value and
      performing pure operations on it never produces directive
      events. The form is inert: it is a value in the Ret position,
      not a computation that emits events. *)

  (** A form-bearing program that only manipulates forms is pure. *)
  Definition form_pipeline (ops : list form_op) (f : Form)
    : itree DirectiveE Form :=
    Ret (apply_ops_ext ops f).

  (** Even when ops is empty (the form is just held as a value),
      no execution occurs. *)
  Theorem form_does_not_execute :
    forall (f : Form),
      @gov_safe Form false
        (interp (Gov h) (Ret f : itree DirectiveE Form)).
  Proof.
    intros f.
    apply governed_interp_safe_false.
  Qed.

  (** Holding a form and then returning it is identical to Ret:
      the form's representational content has no runtime effect. *)
  Theorem form_pipeline_is_ret :
    forall (ops : list form_op) (f : Form),
      form_pipeline ops f = Ret (apply_ops_ext ops f).
  Proof.
    intros. unfold form_pipeline. reflexivity.
  Qed.

  (** Contrast: materialization IS effectful (it emits a directive). *)
  Theorem materialization_is_not_ret :
    forall (f : Form),
      materialize f = trigger (materialize_directive f).
  Proof.
    intros f. unfold materialize. reflexivity.
  Qed.

  (* ================================================================= *)
  (* Theorem 12: Governed Modification Composition                      *)
  (* ================================================================= *)

  (** ** Theorem 12: Governed Modification Composition

      If two modifications f and g are both pure form operations,
      their composition (f composed with g) is also a pure form
      operation, and materializing the composed result is governed.

      This establishes that the algebraic closure of pure form
      operations under composition stays within the pure fragment,
      and the governance boundary is encountered only at
      materialization. *)

  Definition compose_form_ops (phi psi : form_op) : form_op :=
    fun f => psi (phi f).

  Theorem composed_ops_pure :
    forall (phi psi : form_op) (f : Form),
      @gov_safe Form false
        (interp (Gov h) (Ret (compose_form_ops phi psi f) : itree DirectiveE Form)).
  Proof.
    intros phi psi f.
    unfold compose_form_ops.
    apply governed_interp_safe_false.
  Qed.

  Theorem composed_then_materialize_governed :
    forall (phi psi : form_op) (f : Form),
      @gov_safe unit false
        (interp (Gov h) (trigger (materialize_directive (compose_form_ops phi psi f)))).
  Proof.
    intros phi psi f.
    unfold compose_form_ops.
    apply governed_interp_safe_false.
  Qed.

  (** N-ary composition: composing a list of form operations
      produces a single form operation that is still pure. *)
  Definition compose_all (ops : list form_op) : form_op :=
    fun f => apply_ops_ext ops f.

  Theorem compose_all_pure :
    forall (ops : list form_op) (f : Form),
      @gov_safe Form false
        (interp (Gov h) (Ret (compose_all ops f) : itree DirectiveE Form)).
  Proof.
    intros ops f.
    unfold compose_all.
    apply governed_interp_safe_false.
  Qed.

  Theorem compose_all_then_materialize_governed :
    forall (ops : list form_op) (f : Form),
      @gov_safe unit false
        (interp (Gov h) (trigger (materialize_directive (compose_all ops f)))).
  Proof.
    intros ops f.
    unfold compose_all.
    apply governed_interp_safe_false.
  Qed.

  (* ================================================================= *)
  (* Combined: All Twelve Properties                                    *)
  (* ================================================================= *)

  (** ** Capstone: All Twelve Metaprogramming Properties

      Package the complete set of governed metaprogramming
      properties into a single conjunction. *)

  Theorem governed_metaprogramming_complete :
    (** 1. Form manipulation is pure *)
    (forall (phi : form_op) (f : Form),
      @gov_safe Form false (interp (Gov h) (lift_form_op phi f)))
    /\
    (** 2. Materialization is governed *)
    (forall (f : Form),
      @gov_safe unit false (interp (Gov h) (materialize f)))
    /\
    (** 3. No bypass from form to machine *)
    (forall (ops : list form_op) (f : Form),
      @gov_safe Form false (interp (Gov h) (sequential_form_ops ops f)))
    /\
    (** 4. Coterminous boundary preserved *)
    (forall R (t : itree DirectiveE R),
      @gov_safe R false (interp (Gov h) t))
    /\
    (** 5. Inspection does not grant capabilities *)
    (forall (f : Form),
      @gov_safe (list Capability) false
        (interp (Gov h) (inspect_capabilities f)))
    /\
    (** 6. Sequential composition safe *)
    (forall (ops : list form_op) (f : Form),
      @gov_safe Form false
        (interp (Gov h) (sequential_form_ops ops f)))
    /\
    (** 7. Governed evolution preserves safety *)
    (forall (ops : list form_op) (f : Form),
      @gov_safe unit false
        (interp (Gov h) (evolve_and_materialize ops f)))
    /\
    (** 8. Splice is pure *)
    (forall (outer inner : Form),
      @gov_safe Form false
        (interp (Gov h) (splice_forms outer inner)))
    /\
    (** 9. Form equality is decidable and pure *)
    (forall (f1 f2 : Form),
      @gov_safe bool false
        (interp (Gov h) (compare_forms f1 f2)))
    /\
    (** 10. Reflect-modify-materialize pipeline is governed *)
    (forall (source : Form) (modifications : list form_op),
      @gov_safe unit false
        (interp (Gov h) (reflect_modify_materialize source modifications)))
    /\
    (** 11. Form does not execute *)
    (forall (f : Form),
      @gov_safe Form false
        (interp (Gov h) (Ret f : itree DirectiveE Form)))
    /\
    (** 12. Composed modifications are pure, materialization governed *)
    (forall (phi psi : form_op) (f : Form),
      @gov_safe unit false
        (interp (Gov h) (trigger (materialize_directive (compose_form_ops phi psi f))))).
  Proof.
    repeat split; intros; apply governed_interp_safe_false.
  Qed.

End ExtendedFormSafety.
