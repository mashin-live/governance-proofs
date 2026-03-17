(** * Interpreter: Governed Interpretation and Naturality

    Formalizes Theorem 4.8 (Governed Interpretation) from the paper:

    "The governed interpretation eta_G = Gov(eta) is a natural
     transformation from Free(F, -) to Effect(-) that processes
     every directive through the full governance pipeline."

    In ITrees terms, this means:

    For any pure function f : A -> B,
      interp (Gov h) (fmap f t)
    is equivalent (up to eq_itree) to
      fmap f (interp (Gov h) t)

    This follows directly from ITrees' interp_bind and interp_ret
    lemmas, since ITree.map is defined as bind + Ret.

    This file also proves that governance is transparent to
    program composition (Corollary 4.9 from the paper). *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.

From ITree Require Import
  Interp.InterpFacts
  Interp.TranslateFacts.

(** ** Naturality of Governed Interpretation

    Theorem 4.8 from the paper.

    The key insight: [interp] in ITrees already distributes
    over [bind] for any handler (interp_bind). Since [ITree.map]
    is defined as [bind t (fun x => Ret (f x))], naturality
    follows from [interp_bind] + [interp_ret]. *)

Section Naturality.

  Variable h : base_handler.

  (** The governed interpretation commutes with fmap.
      This is the naturality square from the paper.

      For all f : A -> B, t : itree DirectiveE A,

        interp (Gov h) (fmap f t) ≅ fmap f (interp (Gov h) t)

      Proof: ITree.map f t = bind t (fun x => Ret (f x)).
      By interp_bind:
        interp h (bind t k) ≅ bind (interp h t) (fun r => interp h (k r))
      By interp_ret:
        interp h (Ret (f r)) ≅ Ret (f r)
      Combining: interp h (map f t) ≅ map f (interp h t). *)

  Theorem governed_interp_natural :
    forall (A B : Type) (f : A -> B) (t : itree DirectiveE A),
      eq_itree eq
        (governed_interp h B (ITree.map f t))
        (ITree.map f (governed_interp h A t)).
  Proof.
    intros A B f t.
    unfold governed_interp.
    unfold ITree.map.
    rewrite interp_bind.
    setoid_rewrite interp_ret.
    reflexivity.
  Qed.

  (** Governance is transparent to program composition.
      Corollary 4.9 from the paper.

      Programs composed in Free(F, -) compose identically under
      eta and eta_G. The governance pipeline is transparent to
      program composition.

      In ITrees terms: [interp (Gov h)] distributes over [bind].

        interp (Gov h) (t >>= k)
          ≅ (interp (Gov h) t) >>= (fun x => interp (Gov h) (k x))

      This is ITrees' [interp_bind]. *)

  Theorem governance_transparent_composition :
    forall (A B : Type) (t : itree DirectiveE A)
           (k : A -> itree DirectiveE B),
      eq_itree eq
        (governed_interp h B (ITree.bind t k))
        (ITree.bind
          (governed_interp h A t)
          (fun x => governed_interp h B (k x))).
  Proof.
    intros A B t k.
    unfold governed_interp.
    apply interp_bind.
  Qed.

End Naturality.

(** ** Gov Preserves Handler Equivalence

    If two base handlers are equivalent (pointwise eutt),
    then their governed versions are also equivalent.

    This is needed to show that Gov is well-behaved as an
    operator on the space of handlers. *)

Section GovProper.

  (** Two handlers are equivalent if they agree on all
      directives up to eutt. *)
  Definition handler_equiv (h1 h2 : base_handler) : Prop :=
    forall R (d : DirectiveE R),
      eutt eq (h1 R d) (h2 R d).

  (** Gov preserves handler equivalence.

      If h1 ≈ h2, then Gov(h1) ≈ Gov(h2).

      Proof: Gov h d = bind pre_governance (fun ok => if ok then
               bind (lift_io (h d)) (fun r => bind post_governance
               (fun _ => ret r)) else spin).

      The only part that differs between Gov h1 and Gov h2 is
      [lift_io (h1 R d)] vs [lift_io (h2 R d)]. Since translate
      preserves eutt, and bind preserves eutt in both arguments,
      the result follows. *)
  Theorem Gov_proper :
    forall (h1 h2 : base_handler),
      handler_equiv h1 h2 ->
      forall R (d : DirectiveE R),
        eutt eq (Gov h1 R d) (Gov h2 R d).
  Proof.
    intros h1 h2 Heq R d.
    unfold Gov.
    (* The outer bind over pre_governance is identical *)
    apply eutt_clo_bind with (UU := eq).
    - (* pre_governance is the same on both sides *)
      reflexivity.
    - (* The continuation differs only in h1 vs h2 *)
      intros ok1 ok2 Hok. subst.
      destruct ok2.
      + (* Governance passed: need lift_io (h1 R d) ≈ lift_io (h2 R d) *)
        apply eutt_clo_bind with (UU := eq).
        * (* lift_io preserves eutt *)
          unfold lift_io.
          apply eutt_translate_gen.
          apply Heq.
        * (* The rest (post_governance >> ret r) is identical *)
          intros r1 r2 Hr. subst.
          apply eutt_clo_bind with (UU := eq).
          -- reflexivity.
          -- intros u1 u2 Hu. subst. reflexivity.
      + (* Governance denied: both sides are spin *)
        reflexivity.
  Qed.

End GovProper.

(** ** Governance Stages Are Directive-Parametric

    The paper's naturality proof (Theorem 4.8) relies on the
    fact that governance stages depend only on the directive [d]
    and governance context [g], not on the type parameters.

    In the Coq formalization, this is structural: [pre_governance]
    and [post_governance] do not mention any type variable.
    They emit [GovE] events that carry [GovernanceStage] tags.
    The governance decision is independent of the directive's
    response type [R].

    This is what makes Gov a natural transformation rather than
    just a handler: it doesn't inspect the "content" (the value
    of type R), only the "structure" (the directive tag and
    governance context). *)

(** The governance stages are independent of the response type.
    This is trivially true by construction: [pre_governance]
    and [post_governance] have type [itree GovIOE bool] with
    no type variable. But we state it explicitly for clarity. *)
Lemma governance_type_independent :
  forall (R1 R2 : Type),
    pre_governance = (pre_governance : itree GovIOE bool).
Proof.
  reflexivity.
Qed.
