(** * Safety: All Effects Are Governed

    Formalizes Theorem 4.12 (Safety) from the paper:

    "Properties 4.1-4.3 hold for all programs expressible
     in the system."

    The safety theorem states that under the pure module
    constraint, every effect performed by the system passes
    through the governance pipeline.

    The key insight is structural: [Gov h] is defined so that
    every invocation of the base handler [h] is bracketed by
    governance events. The pure module constraint ensures that
    executor programs can only emit [DirectiveE] events, which
    are all handled by [Gov h]. Therefore every effect passes
    through governance.

    This module also defines [gov_safe], a coinductive predicate
    that captures governance safety as a semantic property of
    interaction trees. Unlike the structural proofs above,
    [gov_safe] is non-trivial: it is FALSE for bare IO events
    (Vis (inr1 e) k) at the [false] level, and TRUE for any
    tree produced by [interp (Gov h)]. *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.

From ITree Require Import
  Interp.InterpFacts
  Interp.TranslateFacts
  Eq.EqAxiom.

From Paco Require Import paco.

(** ** The Pure Module Constraint

    Definition 4.8 from the paper.

    An executor satisfies the pure module constraint if its
    output is an [itree DirectiveE R]: it can only emit
    DirectiveE events, not IOE events directly. *)

Definition pure_executor (R : Type) :=
  itree DirectiveE R.

(** An executor is a function from config and context to
    a pure executor program. *)
Definition executor_fn (Config Context Result : Type) :=
  Config -> Context -> pure_executor Result.

(** ** Structural Safety

    The core observation: [Gov h d] structurally decomposes as
    governance checks followed by the base handler followed by
    more governance checks. This is true by definition of [Gov]. *)

Section SafetyTheorem.

  Variable h : base_handler.

  (** Gov always runs pre-governance before the base handler.

      For any directive [d], [Gov h d] is equivalent to
      binding pre_governance and then conditionally running
      the handler. This is literally the definition of Gov. *)
  Lemma Gov_unfold :
    forall R (d : DirectiveE R),
      Gov h R d =
      ITree.bind pre_governance (fun ok =>
      if ok then
        ITree.bind (lift_io (h R d)) (fun r =>
        ITree.bind post_governance (fun _ =>
        ret r))
      else
        ITree.spin).
  Proof.
    intros R d.
    unfold Gov.
    reflexivity.
  Qed.

  (** ** Property 4.1: Governance Completeness (Structural Form)

      "If an effect is performed, governance was checked."

      Structural form: every IOE event in [Gov h d] is
      preceded by GovE events (from pre_governance) in the
      interaction tree. This follows from the bind structure:
      [pre_governance] runs first, then [lift_io (h R d)].

      We prove this by showing that [Gov h d] unfolds to a
      [Vis] node containing a governance check (TrustCheck),
      up to strong bisimulation. *)

  Lemma gov_starts_with_governance :
    forall R (d : DirectiveE R),
      eq_itree eq
        (Gov h R d)
        (Vis (inl1 (GovCheck TrustCheck))
             (fun (trust_ok : bool) =>
              ITree.bind
                (if trust_ok then
                   ITree.bind (gov_check PermissionCheck) (fun perm_ok =>
                   if perm_ok then
                     ITree.bind (gov_check PhaseValidation) (fun phase_ok =>
                     if phase_ok then gov_check PreHooks
                     else ret false)
                   else ret false)
                 else ret false)
                (fun ok =>
                 if ok then
                   ITree.bind (lift_io (h R d)) (fun r =>
                   ITree.bind post_governance (fun _ =>
                   ret r))
                 else ITree.spin))).
  Proof.
    intros R d.
    unfold Gov, pre_governance, gov_check.
    rewrite bind_bind.
    rewrite bind_trigger.
    apply eqit_Vis.
    intros u.
    reflexivity.
  Qed.

  (** ** Property 4.2: Provenance Completeness (Structural Form)

      "If an effect is performed, provenance was recorded."

      In the branch where governance passes (ok = true),
      [post_governance] runs after [lift_io (h R d)].
      [post_governance] includes [gov_check ProvenanceRecord].

      We prove this by showing post_governance unfolds to
      include a ProvenanceRecord check. *)

  Lemma post_governance_includes_provenance :
    eq_itree eq
      post_governance
      (ITree.bind (gov_check Guardrails) (fun guard_ok =>
       ITree.bind (gov_check ProvenanceRecord) (fun _ =>
       ITree.bind (gov_check EventBroadcast) (fun _ =>
       ret guard_ok)))).
  Proof.
    unfold post_governance.
    reflexivity.
  Qed.

  (** ** Property 4.3: No Ungoverned Effects (Type-Level Form)

      "It is never the case that an effect is performed
       without governance."

      This is the strongest form of the safety property.
      It follows from the TYPE of executor programs:

      A pure executor has type [itree DirectiveE R].
      It can ONLY emit [DirectiveE] events.
      It CANNOT emit [IOE] events.

      Therefore the only way IO happens is through
      [interp (Gov h)], which handles every [DirectiveE]
      event via [Gov h], which wraps every handler call
      with governance. *)

  (** The main safety theorem.

      The governed interpretation of any pure executor program
      satisfies: for every DirectiveE event in the original
      program, the interpretation applies [Gov h], which
      structurally wraps the handler with governance stages.

      We prove the structural form: [interp (Gov h) (Vis d k)]
      unfolds to [Gov h d >>= fun r => interp (Gov h) (k r)],
      which by [gov_starts_with_governance] begins with
      governance checks.

      This means no DirectiveE event can be handled without
      passing through governance. And since pure executors
      can ONLY emit DirectiveE events (by type), ALL effects
      are governed. *)
  Theorem safety_structural :
    forall R (d : DirectiveE R) (k : R -> itree DirectiveE R),
      eq_itree eq
        (interp (Gov h) (Vis d k))
        (ITree.bind (Gov h R d) (fun r => Tau (interp (Gov h) (k r)))).
  Proof.
    intros R d k.
    apply interp_vis.
  Qed.

  (** The safety theorem combined with Gov_unfold shows that
      every DirectiveE event in the executor program results
      in governance checks before any IO effect is performed.

      For completeness, we also show that pure values pass
      through without any effects. *)
  Theorem safety_ret :
    forall R (v : R),
      eq_itree eq
        (interp (Gov h) (Ret v : itree DirectiveE R))
        (Ret v).
  Proof.
    intros R v.
    apply interp_ret.
  Qed.

End SafetyTheorem.

(** ** The Pure Module Constraint Is Essential

    Without the pure module constraint, an executor could
    emit IOE events directly, bypassing governance. *)

(** A "cheating" executor type that can emit IO directly *)
Definition impure_executor (R : Type) := itree (DirectiveE +' IOE) R.

(** Example: an impure executor that performs IO directly *)
Definition cheating_executor : impure_executor unit :=
  ITree.bind (trigger (inr1 (PerformIO unit "direct_io_bypass")))
             (fun _ => ret tt).

(** The cheating executor's IO event is NOT governed.
    In the real system, this corresponds to an executor that
    calls [requests.post()] directly instead of returning
    an HTTPRequest directive. The type system prevents this:
    executors return [itree DirectiveE R], which cannot
    contain IOE events. *)


(* ================================================================= *)
(* gov_safe: Coinductive Governance Safety Predicate                  *)
(* ================================================================= *)

(** ** Semantic Safety: [gov_safe]

    The structural safety theorems above show that [Gov h] wraps
    every directive with governance checks. But a reviewer might
    ask: what does "governed" really mean as a semantic property
    of the resulting interaction tree?

    [gov_safe] answers this with a coinductive predicate over
    [itree GovIOE R] that tracks IO permissions:

    - [gov_safe false t]: t never performs bare IO without
      first going through a governance event
    - [gov_safe true t]: t is allowed to perform IO (governance
      has already been checked on this path)

    GovE events (governance checks) grant IO permission: they
    transition from [false] to [true]. IOE events (actual IO)
    require permission: they can only appear under [true].

    This predicate is non-trivial:
    - [Vis (inr1 e) k] does NOT satisfy [gov_safe false]
      (no matching constructor: GS_IOE requires [true])
    - [interp (Gov h) t] DOES satisfy [gov_safe false]
      for any t (the main theorem below) *)

Section GovSafe.

  Context {R : Type}.

  (** The generating functor for gov_safe, indexed by a bool
      that tracks whether IO permission has been granted. *)
  Variant gov_safeF (F : bool -> itree GovIOE R -> Prop)
      : bool -> itreeF GovIOE R (itree GovIOE R) -> Prop :=
    | GS_Ret : forall allowed r,
        gov_safeF F allowed (RetF r)
    | GS_Tau : forall allowed t,
        F allowed t ->
        gov_safeF F allowed (TauF t)
    | GS_GovE : forall allowed (s : GovernanceStage) k,
        (forall b : bool, F true (k b)) ->
        gov_safeF F allowed (VisF (inl1 (GovCheck s)) k)
    | GS_IOE : forall (X : Type) (e : IOE X) (k : X -> itree GovIOE R),
        (forall x : X, F true (k x)) ->
        gov_safeF F true (VisF (inr1 e) k).

  Definition gov_safe_ (F : bool -> itree GovIOE R -> Prop)
      : bool -> itree GovIOE R -> Prop :=
    fun allowed t => gov_safeF F allowed (observe t).

  Lemma gov_safe_mon : monotone2 gov_safe_.
  Proof.
    unfold monotone2. intros allowed t r r' IN LE.
    unfold gov_safe_ in *. inv IN; constructor; auto.
  Qed.

  #[local] Hint Resolve gov_safe_mon : paco.

  Definition gov_safe : bool -> itree GovIOE R -> Prop :=
    paco2 gov_safe_ bot2.

  (* --- Basic lemmas --- *)

  (** Divergence is vacuously safe at any permission level. *)
  Lemma spin_gov_safe : forall allowed, gov_safe allowed ITree.spin.
  Proof.
    intros. pcofix CIH. pfold. red. cbn. apply GS_Tau. right. apply CIH.
  Qed.

  (** Pure values are trivially safe. *)
  Lemma ret_gov_safe : forall allowed v, gov_safe allowed (Ret v).
  Proof. intros. pfold. red. cbn. constructor. Qed.

  (** Negative test: bare IO is NOT gov_safe at permission level [false].
      This is the key non-triviality result: [gov_safe false] rejects
      ungoverned trees. *)
  Lemma bare_io_not_safe :
    forall (e : IOE R) (k : R -> itree GovIOE R),
      ~ gov_safe false (Vis (inr1 e) k).
  Proof. intros e k H. punfold H. red in H. cbn in H. inv H. Qed.

  (** gov_safe is upward closed: [false] implies [true].
      If a tree never does bare IO, it is also safe when IO is permitted. *)
  Lemma gov_safe_weaken :
    forall (t : itree GovIOE R), gov_safe false t -> gov_safe true t.
  Proof.
    pcofix CIH. intros t Hsafe.
    punfold Hsafe. red in Hsafe.
    pfold. red.
    inv Hsafe.
    - constructor.
    - apply GS_Tau. pclearbot. right. apply CIH. assumption.
    - apply GS_GovE. intros b. left.
      specialize (H1 b). destruct H1 as [H1|[]].
      eapply paco2_mon; eauto. intros ? ? [].
  Qed.

  (** Binding a continuation to a divergent tree is safe.
      Used for denied governance branches where [spin] blocks progress. *)
  Lemma bind_spin_gov_safe : forall S (k : S -> itree GovIOE R) allowed,
    gov_safe allowed (ITree.bind ITree.spin k).
  Proof.
    intros S k. pcofix CIH. intros allowed.
    pfold. red. cbn.
    apply GS_Tau. right. apply CIH.
  Qed.

End GovSafe.

#[global] Hint Resolve gov_safe_mon : paco.

(* ================================================================= *)
(* Main Semantic Safety Theorem                                       *)
(* ================================================================= *)

(** ** Theorem: Governed Interpretation is gov_safe

    This is the central semantic safety result: for any pure executor
    program [t : itree DirectiveE R] and any base handler [h],
    the governed interpretation [interp (Gov h) t] satisfies
    [gov_safe false].

    The proof proceeds by parameterized coinduction (paco) on the
    structure of [t]:

    - [Ret]: trivially safe (GS_Ret)
    - [Tau]: one Tau step, then coinduction (GS_Tau + CIH)
    - [Vis d k]: the Gov pipeline unfolds as:
      1. Four pre-governance GovE events (TrustCheck, PermissionCheck,
         PhaseValidation, PreHooks), each granting IO permission
      2. If all pass: the base handler [h] runs via [translate inr1],
         which produces IOE events (allowed because permission = true)
      3. Three post-governance GovE events (Guardrails, ProvenanceRecord,
         EventBroadcast)
      4. Finally [Tau (interp (Gov h) (k result))], where coinduction
         applies

    Denied branches (any governance check returns false) result in
    [ITree.spin], which is vacuously safe.

    The theorem is strengthened to quantify over [allowed] so the
    coinductive hypothesis works at both [true] and [false]. *)

Section MainSafetyTheorem.

  Variable h : base_handler.

  Theorem governed_interp_safe :
    forall R allowed (t : itree DirectiveE R),
      @gov_safe R allowed (interp (Gov h) t).
  Proof.
    intros R. pcofix CIH. intros allowed t.
    rewrite (bisimulation_is_eq _ _ (@unfold_interp DirectiveE GovIOE R (Gov h) t)).
    destruct (observe t) eqn:Ht.
    - (* RetF *) cbn. pfold. red. cbn. constructor.
    - (* TauF *) cbn. pfold. red. cbn. apply GS_Tau. right. apply CIH.
    - (* VisF e k0: Gov h pipeline bound to interp continuation *)
      cbn.
      (* Protect the continuation so [unfold Gov] doesn't expand
         the [Gov h] inside [interp (Gov h) (k x)]. *)
      set (K_cont := fun x : X => Tau (interp (Gov h) (k x))).
      unfold Gov, pre_governance, post_governance, gov_check, lift_io.
      (* Normalize bind associations and expose trigger as Vis *)
      repeat rewrite (bisimulation_is_eq _ _ (bind_bind _ _ _)).
      rewrite (bisimulation_is_eq _ _ (bind_trigger _ _ _)).
      (* Pre-governance event 1: TrustCheck *)
      pfold. red. cbn.
      apply GS_GovE. intros trust_ok.
      destruct trust_ok.
      + (* Trust passed *)
        left.
        repeat rewrite (bisimulation_is_eq _ _ (bind_bind _ _ _)).
        rewrite (bisimulation_is_eq _ _ (bind_trigger _ _ _)).
        pfold. red. cbn.
        (* Pre-governance event 2: PermissionCheck *)
        apply GS_GovE. intros perm_ok.
        destruct perm_ok.
        * (* Permission passed *)
          left.
          repeat rewrite (bisimulation_is_eq _ _ (bind_bind _ _ _)).
          rewrite (bisimulation_is_eq _ _ (bind_trigger _ _ _)).
          pfold. red. cbn.
          (* Pre-governance event 3: PhaseValidation *)
          apply GS_GovE. intros phase_ok.
          destruct phase_ok.
          -- (* Phase passed *)
             left.
             repeat rewrite (bisimulation_is_eq _ _ (bind_bind _ _ _)).
             rewrite (bisimulation_is_eq _ _ (bind_trigger _ _ _)).
             pfold. red. cbn.
             (* Pre-governance event 4: PreHooks *)
             apply GS_GovE. intros hooks_ok.
             destruct hooks_ok.
             ++ (* === All pre-governance passed: IO + post-governance === *)
                left.
                repeat rewrite (bisimulation_is_eq _ _ (bind_bind _ _ _)).
                repeat rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
                (* Nested coinduction on the IO tree (translate inr1 (h _ e)) *)
                generalize (h _ e) as t_io.
                pcofix CIH2. intros t_io.
                (* Replace translate with translateF to enable case analysis *)
                replace (@translate IOE GovIOE (@inr1 GovE IOE) X t_io) with
                  (@translateF IOE GovIOE X (@inr1 GovE IOE)
                    (fun t0 => translate inr1 t0) (observe t_io))
                  by (symmetry; apply bisimulation_is_eq; apply unfold_translate).
                destruct (observe t_io) eqn:Htio; cbn.
                ** (* IO tree returns: step through post-governance *)
                   repeat rewrite (bisimulation_is_eq _ _ (bind_bind _ _ _)).
                   rewrite (bisimulation_is_eq _ _ (bind_trigger _ _ _)).
                   pfold. red. cbn.
                   (* Post-governance event 1: Guardrails *)
                   apply GS_GovE. intros guard_ok. left.
                   repeat rewrite (bisimulation_is_eq _ _ (bind_bind _ _ _)).
                   rewrite (bisimulation_is_eq _ _ (bind_trigger _ _ _)).
                   pfold. red. cbn.
                   (* Post-governance event 2: ProvenanceRecord *)
                   apply GS_GovE. intros prov_ok. left.
                   repeat rewrite (bisimulation_is_eq _ _ (bind_bind _ _ _)).
                   rewrite (bisimulation_is_eq _ _ (bind_trigger _ _ _)).
                   pfold. red. cbn.
                   (* Post-governance event 3: EventBroadcast *)
                   apply GS_GovE. intros event_ok. left.
                   repeat rewrite (bisimulation_is_eq _ _ (bind_bind _ _ _)).
                   repeat rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
                   (* Unfold K_cont to expose interp (Gov h) (k r0) *)
                   subst K_cont.
                   pfold. red. cbn.
                   (* Tau step back to main coinduction *)
                   apply GS_Tau. right. apply CIH.
                ** (* IO tree taus: GS_Tau + inner coinduction *)
                   pfold. red. cbn.
                   apply GS_Tau. right. apply CIH2.
                ** (* IO tree performs IO: GS_IOE (allowed=true) + inner coinduction *)
                   pfold. red. cbn.
                   apply GS_IOE. intros x. right. apply CIH2.
             ++ (* Pre-hooks denied: spin *)
                left.
                repeat rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
                cbn.
                eapply paco2_mon.
                apply (@bind_spin_gov_safe _ _ _ true).
                intros ? ? [].
          -- (* Phase denied: spin *)
             left.
             repeat rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
             cbn.
             eapply paco2_mon.
             apply (@bind_spin_gov_safe _ _ _ true).
             intros ? ? [].
        * (* Permission denied: spin *)
          left.
          repeat rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
          cbn.
          eapply paco2_mon.
          apply (@bind_spin_gov_safe _ _ _ true).
          intros ? ? [].
      + (* Trust denied: spin *)
        left.
        repeat rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
        cbn.
        eapply paco2_mon.
        apply (@bind_spin_gov_safe _ _ _ true).
        intros ? ? [].
  Qed.

  (** Corollary: the standard statement with [false]. *)
  Corollary governed_interp_safe_false :
    forall R (t : itree DirectiveE R),
      @gov_safe R false (interp (Gov h) t).
  Proof. intros. apply governed_interp_safe. Qed.

End MainSafetyTheorem.
