(* Copyright (c) 2026 Alan Lawrence McCann, mashin, Inc.
   Licensed under MIT. See LICENSE file. *)

(** * Lambda^intent Metatheory

    Five metatheoretic results:
    1. Progress
    2. Preservation
    3. Governance Soundness
    4. Mandatory Mediation
    5. Capability Confinement

    Reference: OSI paper, Section 5 (Metatheory). *)

From Coq Require Import
  Lists.List
  Bool.Bool
  Arith.Arith
  PeanoNat
  Lia.

From MashinGov.lambda_intent Require Import Syntax Typing Semantics.

(** Axiom: realize returns a well-typed value of the response type.
    This models the external oracle's correctness. The realize function
    is external to the calculus; this axiom states our assumption
    about its behavior. *)
Axiom realize_well_typed : forall i,
  has_type nil (realize i) (TResponse (intent_class i)) cap_empty.

Import ListNotations.
Open Scope list_scope.

(* ================================================================== *)
(** ** Auxiliary Lemmas *)
(* ================================================================== *)

(** Canonical forms: well-typed values have predictable shapes *)

(** Canonical forms lemmas: well-typed values have predictable shapes.
    These are standard and proved by inversion on the value and typing
    derivations, with case analysis on T_Sub. *)

(** We need a helper: inversion on typing through T_Sub chains.
    A value typed at a specific type via T_Sub must have a derivation
    without T_Sub at some point (the "canonical" derivation). *)

Lemma canonical_forms_bool :
  forall v,
    value v ->
    has_type nil v TBool cap_empty ->
    v = tbool true \/ v = tbool false.
Proof.
  intros v Hval Htype.
  (* The difficulty is T_Sub: has_type nil v TBool kap for some
     kap subset cap_empty, then subsumption to cap_empty.
     Since cap_empty has no elements, kap subset cap_empty
     means kap is effectively empty too.

     We proceed by induction on the typing derivation, noting
     that only T_Bool and T_Sub can produce TBool. *)
  inversion Hval; subst;
    inversion Htype; subst; try (destruct b; auto; fail).
  - (* T_Sub on tbool *) admit.
  - (* T_Sub on tint - impossible type *) admit.
  - (* etc *)
Abort.

(** The canonical forms proofs require careful handling of T_Sub
    chains. We use a simpler approach: prove that values of a given
    type have the expected shape, handling T_Sub by noting that
    subsumption only changes capabilities, not types. *)

Lemma value_typed_bool_shape :
  forall v kap,
    value v ->
    has_type nil v TBool kap ->
    v = tbool true \/ v = tbool false.
Proof.
  intros v kap Hval Htype.
  remember (@nil ty) as Gamma. remember TBool as T.
  induction Htype; subst;
    try discriminate;
    try (exfalso; inversion Hval; fail).
  - destruct b; auto.
  - apply IHHtype; auto.
Qed.

Lemma canonical_forms_bool :
  forall v,
    value v ->
    has_type nil v TBool cap_empty ->
    v = tbool true \/ v = tbool false.
Proof.
  intros. eapply value_typed_bool_shape; eauto.
Qed.

Lemma value_typed_arrow_shape :
  forall v T1 T2 kap,
    value v ->
    has_type nil v (TArrow T1 T2) kap ->
    exists body, v = tabs T1 body.
Proof.
  intros v T1 T2 kap Hval Htype.
  remember (@nil ty) as Gamma. remember (TArrow T1 T2) as T.
  induction Htype; subst;
    try discriminate;
    try (exfalso; inversion Hval; fail).
  - injection HeqT; intros; subst. exists body. reflexivity.
  - apply IHHtype; auto.
Qed.

Lemma canonical_forms_arrow :
  forall v T1 T2,
    value v ->
    has_type nil v (TArrow T1 T2) cap_empty ->
    exists body, v = tabs T1 body.
Proof.
  intros. eapply value_typed_arrow_shape; eauto.
Qed.

Lemma value_typed_prod_shape :
  forall v T1 T2 kap,
    value v ->
    has_type nil v (TProd T1 T2) kap ->
    exists v1 v2, v = tpair v1 v2 /\ value v1 /\ value v2.
Proof.
  intros v T1 T2 kap Hval Htype.
  remember (@nil ty) as Gamma. remember (TProd T1 T2) as T.
  induction Htype; subst;
    try discriminate;
    try (exfalso; inversion Hval; fail).
  - exists e1, e2. inversion Hval. auto.
  - apply IHHtype; auto.
Qed.

Lemma canonical_forms_prod :
  forall v T1 T2,
    value v ->
    has_type nil v (TProd T1 T2) cap_empty ->
    exists v1 v2, v = tpair v1 v2 /\ value v1 /\ value v2.
Proof.
  intros. eapply value_typed_prod_shape; eauto.
Qed.

(** Typing inversion for specific value forms *)

Lemma typing_int_type : forall n T kap, has_type nil (tint n) T kap -> T = TInt.
Proof. intros. remember (@nil ty) as G. remember (tint n) as e. induction H; subst; try discriminate; auto. Qed.
Lemma typing_bool_type : forall b T kap, has_type nil (tbool b) T kap -> T = TBool.
Proof. intros. remember (@nil ty) as G. remember (tbool b) as e. induction H; subst; try discriminate; auto. Qed.
Lemma typing_str_type : forall s T kap, has_type nil (tstr s) T kap -> T = TString.
Proof. intros. remember (@nil ty) as G. remember (tstr s) as e. induction H; subst; try discriminate; auto. Qed.
Lemma typing_nil_type : forall T kap, has_type nil tnil T kap -> exists T1, T = TList T1.
Proof. intros. remember (@nil ty) as G. remember tnil as e. induction H; subst; try discriminate; eauto. Qed.
Lemma typing_denied_type : forall T kap, has_type nil tdenied T kap -> exists k, T = TResponse k.
Proof. intros. remember (@nil ty) as G. remember tdenied as e. induction H; subst; try discriminate; eauto. Qed.
Lemma typing_suspended_type : forall T kap, has_type nil tsuspended T kap -> exists k, T = TResponse k.
Proof. intros. remember (@nil ty) as G. remember tsuspended as e. induction H; subst; try discriminate; eauto. Qed.
Lemma typing_abs_type : forall T1 body T kap, has_type nil (tabs T1 body) T kap ->
  exists kf T2, T = TArrow T1 T2 /\ has_type (T1 :: nil) body T2 kf.
Proof. intros. remember (@nil ty) as G. remember (tabs T1 body) as e.
  induction H; subst; try discriminate.
  - injection Heqe as Ha Hb. subst. exists kap, T2. auto.
  - destruct (IHhas_type eq_refl eq_refl) as [kf2 [T2' [Heq Hb]]]. exists kf2, T2'. auto.
Qed.
Lemma typing_pair_inv : forall v1 v2 T kap, has_type nil (tpair v1 v2) T kap ->
  exists T1 T2 k1 k2, T = TProd T1 T2 /\ has_type nil v1 T1 k1 /\ has_type nil v2 T2 k2.
Proof. intros. remember (@nil ty) as G. remember (tpair v1 v2) as e.
  induction H; subst; try discriminate.
  - injection Heqe as Ha Hb. subst. exists T1, T2, kap1, kap2. auto.
  - destruct (IHhas_type eq_refl eq_refl) as [T1 [T2 [k1 [k2 H']]]]. exists T1, T2, k1, k2. auto.
Qed.
Lemma typing_cons_inv : forall v1 v2 T kap, has_type nil (tcons v1 v2) T kap ->
  exists T1 k1 k2, T = TList T1 /\ has_type nil v1 T1 k1 /\ has_type nil v2 (TList T1) k2.
Proof. intros. remember (@nil ty) as G. remember (tcons v1 v2) as e.
  induction H; subst; try discriminate.
  - injection Heqe as Ha Hb. subst. exists T, kap1, kap2. auto.
  - destruct (IHhas_type eq_refl eq_refl) as [T1 [k1 [k2 H']]]. exists T1, k1, k2. auto.
Qed.

Lemma typing_app_inv : forall e1 e2 T kap, has_type nil (tapp e1 e2) T kap ->
  exists T1 k1 k2, has_type nil e1 (TArrow T1 T) k1 /\ has_type nil e2 T1 k2.
Proof. intros. remember (@nil ty) as G. remember (tapp e1 e2) as e.
  induction H; subst; try discriminate. injection Heqe as. subst. eauto 6. auto. Qed.
Lemma typing_let_inv : forall e1 e2 T kap, has_type nil (tlet e1 e2) T kap ->
  exists T1 k1 k2, has_type nil e1 T1 k1 /\ has_type (T1 :: nil) e2 T k2.
Proof. intros. remember (@nil ty) as G. remember (tlet e1 e2) as e.
  induction H; subst; try discriminate. injection Heqe as. subst. eauto 6. auto. Qed.
Lemma typing_if_inv : forall e1 e2 e3 T kap, has_type nil (tif e1 e2 e3) T kap ->
  exists k1 k2 k3, has_type nil e1 TBool k1 /\ has_type nil e2 T k2 /\ has_type nil e3 T k3.
Proof. intros. remember (@nil ty) as G. remember (tif e1 e2 e3) as e.
  induction H; subst; try discriminate. injection Heqe as. subst. eauto 8. auto. Qed.
Lemma typing_fix_inv : forall T0 body T kap, has_type nil (tfix T0 body) T kap ->
  T = T0 /\ exists k0, has_type (T0 :: nil) body T0 k0.
Proof. intros. remember (@nil ty) as G. remember (tfix T0 body) as e.
  induction H; subst; try discriminate. injection Heqe as. subst. split; eauto. auto. Qed.
Lemma typing_fst_inv : forall e0 T kap, has_type nil (tfst e0) T kap ->
  exists T2 k0, has_type nil e0 (TProd T T2) k0.
Proof. intros. remember (@nil ty) as G. remember (tfst e0) as e.
  induction H; subst; try discriminate. injection Heqe as. subst. eauto. auto. Qed.
Lemma typing_snd_inv : forall e0 T kap, has_type nil (tsnd e0) T kap ->
  exists T1 k0, has_type nil e0 (TProd T1 T) k0.
Proof. intros. remember (@nil ty) as G. remember (tsnd e0) as e.
  induction H; subst; try discriminate. injection Heqe as. subst. eauto. auto. Qed.
Lemma typing_ask_inv : forall k a tgt p T kap, has_type nil (task k a tgt p) T kap ->
  T = TResponse k /\ value p.
Proof. intros. remember (@nil ty) as G. remember (task k a tgt p) as e.
  induction H; subst; try discriminate. injection Heqe as. subst. auto. auto. Qed.

(** Note: value_cap_empty (values always have cap_empty) does NOT hold
    in the capability-indexed system where TArrow T1 T2 carries no
    embedded capability. Lambda values carry their body's capability
    as their own effect, which may be non-empty. For preservation,
    we use subst_gen_top which handles arbitrary capabilities. *)

(** Substitution preserves typing.

    The full proof requires weakening (shift preserves typing) and
    a general substitution lemma at arbitrary positions. These are
    standard for de Bruijn formulations but require ~150 lines of
    infrastructure (shift/subst interaction lemmas, context
    insertion lemma, etc.).

    We factor the proof into:
    1. A context insertion (weakening) lemma
    2. The general substitution lemma at position x
    3. The top-level substitution as a special case

    For now we prove the statement and admit the body, noting that
    the proof follows exactly the template from Software Foundations
    (StlcProp chapter) and Pierce's TAPL Chapter 6. The statement
    is correct and all downstream governance theorems that use it
    are architecturally sound. *)

(** Weakening: inserting a type into the context preserves typing.
    This is the key lemma for the substitution proof. *)
(** General weakening: inserting a type at an arbitrary position
    in the context, with appropriate shifting. *)

Lemma shift_preserves_typing_gen :
  forall Gamma e T kap,
    has_type Gamma e T kap ->
    forall (Gamma1 Gamma2 : context) (U : ty),
    Gamma = Gamma1 ++ Gamma2 ->
    has_type (Gamma1 ++ (U :: Gamma2)) (shift 1 (length Gamma1) e) T kap.
Proof.
  intros Gamma e T kap Htype.
  induction Htype; intros Gamma1 Gamma2 U HG; subst; simpl.
  - constructor. - constructor. - constructor.
  - unfold ctx_lookup in *.
    destruct (Nat.leb (length Gamma1) x) eqn:Eleb.
    + apply T_Var. unfold ctx_lookup.
      apply Nat.leb_le in Eleb.
      rewrite nth_error_app2 in H by lia.
      rewrite nth_error_app2 by (simpl; lia).
      replace (x + 1 - length Gamma1) with (S (x - length Gamma1)) by lia.
      simpl. exact H.
    + apply T_Var. unfold ctx_lookup.
      apply PeanoNat.Nat.leb_nle in Eleb.
      rewrite nth_error_app1 in H by lia.
      rewrite nth_error_app1 by (simpl; lia). exact H.
  - constructor. - constructor. - constructor.
  - apply T_Abs. simpl.
    apply (IHHtype (T1 :: Gamma1) Gamma2 U). simpl. reflexivity.
  - eapply T_App;
    [apply (IHHtype1 Gamma1 Gamma2 U); auto |
     apply (IHHtype2 Gamma1 Gamma2 U); auto].
  - eapply T_Let;
    [apply (IHHtype1 Gamma1 Gamma2 U); auto |
     simpl; apply (IHHtype2 (T1 :: Gamma1) Gamma2 U); simpl; reflexivity].
  - eapply T_If;
    [apply (IHHtype1 Gamma1 Gamma2 U); auto |
     apply (IHHtype2 Gamma1 Gamma2 U); auto |
     apply (IHHtype3 Gamma1 Gamma2 U); auto].
  - eapply T_Pair;
    [apply (IHHtype1 Gamma1 Gamma2 U); auto |
     apply (IHHtype2 Gamma1 Gamma2 U); auto].
  - eapply T_Fst. apply (IHHtype Gamma1 Gamma2 U); auto.
  - eapply T_Snd. apply (IHHtype Gamma1 Gamma2 U); auto.
  - eapply T_Cons;
    [apply (IHHtype1 Gamma1 Gamma2 U); auto |
     apply (IHHtype2 Gamma1 Gamma2 U); auto].
  - apply T_Fix. simpl.
    apply (IHHtype (T :: Gamma1) Gamma2 U). simpl. reflexivity.
  - apply T_Ask. apply shift_preserves_value. exact H.
  - eapply T_Sub;
    [apply (IHHtype Gamma1 Gamma2 U); auto | exact H].
Qed.

(** Corollary: inserting a type at position 0 *)
Lemma shift_preserves_typing :
  forall Gamma e T kap U,
    has_type Gamma e T kap ->
    has_type (U :: Gamma) (shift 1 0 e) T kap.
Proof.
  intros.
  change (has_type (nil ++ (U :: Gamma))
    (shift 1 (length (@nil ty)) e) T kap).
  apply (shift_preserves_typing_gen Gamma e T kap H nil Gamma U).
  reflexivity.
Qed.

(** The substitution lemma requires a general version at arbitrary
    position x (not just 0) to handle binders. Under [tabs T1 body],
    subst at position 0 becomes subst at position 1 in the body,
    with the substitutee shifted. The general form uses context
    splitting: Gamma1 ++ T_s :: Gamma2, with length Gamma1 = x.

    The proof follows the standard POPLmark/Software Foundations
    template and requires:
    - shift_preserves_typing (PROVED above)
    - shift/subst commutation lemma
    - context splitting/reconstitution

    The T_Var case: if x = position, substitute and weaken.
    If x < position, variable index shifts down. If x > position,
    variable is unchanged.

    Binder cases (T_Abs, T_Let, T_Fix): IH at position (S x)
    with shifted substitutee, using shift_preserves_typing.

    All other cases: IH distributes over subterms.

    This is the ONE remaining standard infrastructure lemma.
    All governance-specific theorems are proved independently. *)
Lemma subst_preserves_value :
  forall n s v, value v -> value (subst n s v).
Proof.
  intros n s v Hval. induction Hval; simpl; constructor; auto.
Qed.

Lemma substitution_at_pos :
  forall Gamma e T kap,
    has_type Gamma e T kap ->
    forall (Gpre Gpost : list ty) T_s s,
      Gamma = Gpre ++ (T_s :: Gpost) ->
      has_type (Gpre ++ Gpost) s T_s cap_empty ->
      has_type (Gpre ++ Gpost) (subst (length Gpre) s e) T kap.
Proof.
  intros Gamma e T kap Htype.
  induction Htype; intros Gpre Gpost T_s0 s0 HG Hs; subst; simpl.
  - constructor. - constructor. - constructor.
  - unfold ctx_lookup in H.
    destruct (Nat.eqb x (length Gpre)) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      rewrite nth_error_app2 in H by lia.
      replace (length Gpre - length Gpre) with 0 in H by lia.
      simpl in H. injection H as Heq. subst. exact Hs.
    + destruct (Nat.ltb (length Gpre) x) eqn:Hlt.
      * apply Nat.ltb_lt in Hlt. apply T_Var. unfold ctx_lookup.
        rewrite nth_error_app2 in H by lia.
        replace (x - length Gpre) with (S (x - length Gpre - 1)) in H by lia.
        simpl in H. rewrite nth_error_app2 by lia.
        replace (pred x - length Gpre) with (x - length Gpre - 1) by lia.
        exact H.
      * apply Nat.ltb_nlt in Hlt. apply Nat.eqb_neq in Heq.
        assert (x < length Gpre) by lia. apply T_Var. unfold ctx_lookup.
        rewrite nth_error_app1 in H by lia.
        rewrite nth_error_app1 by lia. exact H.
  - constructor. - constructor. - constructor.
  - apply T_Abs.
    apply (IHHtype (T1 :: Gpre) Gpost T_s0 (shift 1 0 s0)).
    simpl. reflexivity. apply shift_preserves_typing. exact Hs.
  - eapply T_App;
    [apply (IHHtype1 Gpre Gpost T_s0 s0); auto |
     apply (IHHtype2 Gpre Gpost T_s0 s0); auto].
  - eapply T_Let.
    + apply (IHHtype1 Gpre Gpost T_s0 s0); auto.
    + apply (IHHtype2 (T1 :: Gpre) Gpost T_s0 (shift 1 0 s0)).
      simpl. reflexivity. apply shift_preserves_typing. exact Hs.
  - eapply T_If;
    [apply (IHHtype1 Gpre Gpost T_s0 s0); auto |
     apply (IHHtype2 Gpre Gpost T_s0 s0); auto |
     apply (IHHtype3 Gpre Gpost T_s0 s0); auto].
  - eapply T_Pair;
    [apply (IHHtype1 Gpre Gpost T_s0 s0); auto |
     apply (IHHtype2 Gpre Gpost T_s0 s0); auto].
  - eapply T_Fst. apply (IHHtype Gpre Gpost T_s0 s0); auto.
  - eapply T_Snd. apply (IHHtype Gpre Gpost T_s0 s0); auto.
  - eapply T_Cons;
    [apply (IHHtype1 Gpre Gpost T_s0 s0); auto |
     apply (IHHtype2 Gpre Gpost T_s0 s0); auto].
  - apply T_Fix.
    apply (IHHtype (T :: Gpre) Gpost T_s0 (shift 1 0 s0)).
    simpl. reflexivity. apply shift_preserves_typing. exact Hs.
  - apply T_Ask. apply subst_preserves_value. exact H.
  - eapply T_Sub;
    [apply (IHHtype Gpre Gpost T_s0 s0); auto | exact H].
Qed.

Lemma substitution_preserves_typing :
  forall Gamma e T_e kap_e s T_s,
    has_type (T_s :: Gamma) e T_e kap_e ->
    has_type Gamma s T_s cap_empty ->
    has_type Gamma (subst_top s e) T_e kap_e.
Proof.
  intros Gamma e T_e kap_e s T_s Htype Hs.
  unfold subst_top.
  apply (substitution_at_pos (T_s :: Gamma) e T_e kap_e Htype
    (@nil ty) Gamma T_s s eq_refl).
  simpl. exact Hs.
Qed.

(** Generalized substitution allowing non-empty kap_s.
    Needed for E_Fix in preservation (tfix is not a value). *)
(* fix_subst_typing removed: replaced by subst_gen_top + substitution_at_pos_gen *)

(* ================================================================== *)
(** ** Theorem 1: Progress *)
(* ================================================================== *)

(** A well-typed closed term is either a value or can step
    under any policy set and ledger. *)

Theorem progress :
  forall e T kap,
    has_type nil e T kap ->
    value e \/
    (forall ps ledger tr,
      exists c', step (mk_config e ps ledger tr) c').
Proof.
  intros e T kap Htype.
  remember (@nil ty) as Gamma.
  induction Htype; subst.
  - left. constructor.
  - left. constructor.
  - left. constructor.
  - destruct x; simpl in H; discriminate.
  - left. constructor.
  - left. constructor.
  - left. constructor.
  - left. constructor.
  - (* T_App *)
    right. intros ps ledger tr.
    destruct IHHtype1 as [Hv1 | Hs1]; auto.
    + destruct IHHtype2 as [Hv2 | Hs2]; auto.
      * destruct (value_typed_arrow_shape _ _ _ _ Hv1 Htype1) as [bdy Heq].
        subst. eexists. apply E_App. exact Hv2.
      * destruct (Hs2 ps ledger tr) as [[e' ps' l' t'] Hstep].
        eexists. eapply E_Ctx with (E := EC_AppR e1 EC_Hole).
        discriminate. exact Hstep.
    + destruct (Hs1 ps ledger tr) as [[e' ps' l' t'] Hstep].
      eexists. eapply E_Ctx with (E := EC_AppL EC_Hole e2).
      discriminate. exact Hstep.
  - (* T_Let *)
    right. intros ps ledger tr.
    destruct IHHtype1 as [Hv1 | Hs1]; auto.
    + eexists. apply E_Let. exact Hv1.
    + destruct (Hs1 ps ledger tr) as [[e' ps' l' t'] Hstep].
      eexists. eapply E_Ctx with (E := EC_LetBind EC_Hole e2).
      discriminate. exact Hstep.
  - (* T_If *)
    right. intros ps ledger tr.
    destruct IHHtype1 as [Hv1 | Hs1]; auto.
    + destruct (value_typed_bool_shape _ _ Hv1 Htype1) as [Heq | Heq]; subst.
      * eexists. apply E_IfTrue.
      * eexists. apply E_IfFalse.
    + destruct (Hs1 ps ledger tr) as [[e' ps' l' t'] Hstep].
      eexists. eapply E_Ctx with (E := EC_IfCond EC_Hole e2 e3).
      discriminate. exact Hstep.
  - (* T_Pair *)
    destruct IHHtype1 as [Hv1 | Hs1]; auto.
    + destruct IHHtype2 as [Hv2 | Hs2]; auto.
      * left. constructor; assumption.
      * right. intros ps ledger tr.
        destruct (Hs2 ps ledger tr) as [[e' ps' l' t'] Hstep].
        eexists. eapply E_Ctx with (E := EC_PairR e1 EC_Hole).
        discriminate. exact Hstep.
    + right. intros ps ledger tr.
      destruct (Hs1 ps ledger tr) as [[e' ps' l' t'] Hstep].
      eexists. eapply E_Ctx with (E := EC_PairL EC_Hole e2).
      discriminate. exact Hstep.
  - (* T_Fst *)
    right. intros ps ledger tr.
    destruct IHHtype as [Hv | Hs]; auto.
    + destruct (value_typed_prod_shape _ _ _ _ Hv Htype)
        as [v1 [v2 [Heq [Hv1 Hv2]]]]. subst.
      eexists. apply E_Fst; assumption.
    + destruct (Hs ps ledger tr) as [[e' ps' l' t'] Hstep].
      eexists. eapply E_Ctx with (E := EC_Fst EC_Hole).
      discriminate. exact Hstep.
  - (* T_Snd *)
    right. intros ps ledger tr.
    destruct IHHtype as [Hv | Hs]; auto.
    + destruct (value_typed_prod_shape _ _ _ _ Hv Htype)
        as [v1 [v2 [Heq [Hv1 Hv2]]]]. subst.
      eexists. apply E_Snd; assumption.
    + destruct (Hs ps ledger tr) as [[e' ps' l' t'] Hstep].
      eexists. eapply E_Ctx with (E := EC_Snd EC_Hole).
      discriminate. exact Hstep.
  - (* T_Cons *)
    destruct IHHtype1 as [Hv1 | Hs1]; auto.
    + destruct IHHtype2 as [Hv2 | Hs2]; auto.
      * left. constructor; assumption.
      * right. intros ps ledger tr.
        destruct (Hs2 ps ledger tr) as [[e' ps' l' t'] Hstep].
        eexists. eapply E_Ctx with (E := EC_ConsR e1 EC_Hole).
        discriminate. exact Hstep.
    + right. intros ps ledger tr.
      destruct (Hs1 ps ledger tr) as [[e' ps' l' t'] Hstep].
      eexists. eapply E_Ctx with (E := EC_ConsL EC_Hole e2).
      discriminate. exact Hstep.
  - (* T_Fix *) right. intros ps ledger tr. eexists. apply E_Fix.
  - (* T_Ask: value p is now a premise of T_Ask *)
    right. intros ps ledger tr.
    destruct (gov_interpret_total ps
      (mk_intent k a tgt p) (ledger_hash ledger)) as [d [r Hgov]].
    destruct d.
    + eexists. eapply E_Allow; eauto.
    + eexists. eapply E_Deny; eauto.
    + eexists. eapply E_Escalate; eauto.
  - (* T_Sub *) apply IHHtype. reflexivity.
Qed.

(* ================================================================== *)
(** ** Infrastructure for Preservation *)
(* ================================================================== *)

(** Generalized substitution at position: allows non-empty kap_s.
    Returns existential kap_out (type preserved, caps may change). *)
Lemma substitution_at_pos_gen :
  forall Gamma e T kap,
    has_type Gamma e T kap ->
    forall (Gpre Gpost : list ty) T_s s kap_s,
      Gamma = Gpre ++ (T_s :: Gpost) ->
      has_type (Gpre ++ Gpost) s T_s kap_s ->
      exists kap_out, has_type (Gpre ++ Gpost) (subst (length Gpre) s e) T kap_out.
Proof.
  intros Gamma e T kap Htype.
  induction Htype; intros Gpre Gpost T_s0 s0 kap_s HG Hs; subst; simpl.
  - eauto using T_Int. - eauto using T_Bool. - eauto using T_Str.
  - unfold ctx_lookup in H.
    destruct (Nat.eqb x (length Gpre)) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      rewrite nth_error_app2 in H by lia.
      replace (length Gpre - length Gpre) with 0 in H by lia.
      simpl in H. injection H as. subst. eauto.
    + destruct (Nat.ltb (length Gpre) x) eqn:Hlt.
      * apply Nat.ltb_lt in Hlt. eexists. apply T_Var. unfold ctx_lookup.
        rewrite nth_error_app2 in H by lia.
        replace (x - length Gpre) with (S (x - length Gpre - 1)) in H by lia.
        simpl in H. rewrite nth_error_app2 by lia.
        replace (pred x - length Gpre) with (x - length Gpre - 1) by lia. exact H.
      * apply Nat.ltb_nlt in Hlt. apply Nat.eqb_neq in Heq.
        assert (x < length Gpre) by lia. eexists. apply T_Var. unfold ctx_lookup.
        rewrite nth_error_app1 in H by lia.
        rewrite nth_error_app1 by lia. exact H.
  - eauto using T_Denied. - eauto using T_Suspended. - eauto using T_Nil.
  - (* T_Abs *)
    destruct (IHHtype (T1 :: Gpre) Gpost T_s0 (shift 1 0 s0) kap_s eq_refl
      (shift_preserves_typing _ _ _ _ _ Hs)) as [ko Hko].
    eexists. eapply T_Abs. exact Hko.
  - destruct (IHHtype1 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko1 Hko1].
    destruct (IHHtype2 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko2 Hko2].
    eexists. eapply T_App; eassumption.
  - (* T_Let *)
    destruct (IHHtype1 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko1 Hko1].
    destruct (IHHtype2 (T1 :: Gpre) Gpost T_s0 (shift 1 0 s0) kap_s eq_refl
      (shift_preserves_typing _ _ _ _ _ Hs)) as [ko2 Hko2].
    eexists. eapply T_Let. exact Hko1. exact Hko2.
  - destruct (IHHtype1 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko1 Hko1].
    destruct (IHHtype2 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko2 Hko2].
    destruct (IHHtype3 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko3 Hko3].
    eexists. eapply T_If; eassumption.
  - destruct (IHHtype1 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko1 Hko1].
    destruct (IHHtype2 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko2 Hko2].
    eexists. eapply T_Pair; eassumption.
  - destruct (IHHtype Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko Hko].
    eexists. eapply T_Fst; eassumption.
  - destruct (IHHtype Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko Hko].
    eexists. eapply T_Snd; eassumption.
  - destruct (IHHtype1 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko1 Hko1].
    destruct (IHHtype2 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko2 Hko2].
    eexists. eapply T_Cons; eassumption.
  - (* T_Fix *)
    destruct (IHHtype (T :: Gpre) Gpost T_s0 (shift 1 0 s0) kap_s eq_refl
      (shift_preserves_typing _ _ _ _ _ Hs)) as [ko Hko].
    eexists. eapply T_Fix. exact Hko.
  - eexists. apply T_Ask. apply subst_preserves_value. exact H.
  - destruct (IHHtype Gpre Gpost T_s0 s0 kap_s) as [ko Hko]; auto.
    eauto using T_Sub.
Qed.

(** Generalized substitution for E_Fix (non-value substitutee). *)
Lemma subst_gen_top :
  forall e T kap s T_s kap_s,
    has_type (T_s :: nil) e T kap ->
    has_type nil s T_s kap_s ->
    exists kap', has_type nil (subst_top s e) T kap'.
Proof.
  intros e T kap s T_s kap_s Htype Hs. unfold subst_top.
  eapply (substitution_at_pos_gen (T_s :: nil) e T kap Htype
    (@nil ty) nil T_s s kap_s eq_refl).
  simpl. exact Hs.
Qed.

(** Context typing: if plug E e is well-typed and e preserves types
    when stepping, then plug E e' is well-typed. *)
Lemma plug_pres :
  forall E e e',
    (forall T kap, has_type nil e T kap -> exists kap', has_type nil e' T kap') ->
    forall T kap, has_type nil (plug E e) T kap ->
    exists kap', has_type nil (plug E e') T kap'.
Proof.
  induction E; intros e0 e0' IH T0 kap0 Htype; simpl in *.
  - apply IH with (kap := kap0). exact Htype.
  - destruct (typing_app_inv _ _ _ _ Htype) as [T1 [k1 [k2 [H1 H2]]]].
    destruct (IHE _ _ IH _ _ H1) as [k1' H1']. eauto 6 using T_App.
  - destruct (typing_app_inv _ _ _ _ Htype) as [T1 [k1 [k2 [H1 H2]]]].
    destruct (IHE _ _ IH _ _ H2) as [k2' H2']. eauto 6 using T_App.
  - destruct (typing_let_inv _ _ _ _ Htype) as [T1 [k1 [k2 [H1 H2]]]].
    destruct (IHE _ _ IH _ _ H1) as [k1' H1']. eauto 6 using T_Let.
  - destruct (typing_if_inv _ _ _ _ _ Htype) as [k1 [k2 [k3 [H1 [H2 H3]]]]].
    destruct (IHE _ _ IH _ _ H1) as [k1' H1']. eauto 8 using T_If.
  - destruct (typing_fst_inv _ _ _ Htype) as [T2 [k0 Hp]].
    destruct (IHE _ _ IH _ _ Hp) as [k0' Hp']. eauto using T_Fst.
  - destruct (typing_snd_inv _ _ _ Htype) as [T1 [k0 Hp]].
    destruct (IHE _ _ IH _ _ Hp) as [k0' Hp']. eauto using T_Snd.
  - destruct (typing_pair_inv _ _ _ _ Htype) as [T1 [T2 [k1 [k2 [Heq [H1 H2]]]]]]. subst.
    destruct (IHE _ _ IH _ _ H1) as [k1' H1']. eauto 6 using T_Pair.
  - destruct (typing_pair_inv _ _ _ _ Htype) as [T1 [T2 [k1 [k2 [Heq [H1 H2]]]]]]. subst.
    destruct (IHE _ _ IH _ _ H2) as [k2' H2']. eauto 6 using T_Pair.
  - destruct (typing_cons_inv _ _ _ _ Htype) as [T1 [k1 [k2 [Heq [H1 H2]]]]]. subst.
    destruct (IHE _ _ IH _ _ H1) as [k1' H1']. eauto 6 using T_Cons.
  - destruct (typing_cons_inv _ _ _ _ Htype) as [T1 [k1 [k2 [Heq [H1 H2]]]]]. subst.
    destruct (IHE _ _ IH _ _ H2) as [k2' H2']. eauto 6 using T_Cons.
Qed.

(* ================================================================== *)
(** ** Theorem 2: Preservation *)
(* ================================================================== *)

Theorem preservation :
  forall e T kap ps ledger tr c',
    has_type nil e T kap ->
    step (mk_config e ps ledger tr) c' ->
    exists kap', has_type nil (cfg_term c') T kap'.
Proof.
  intros e T kap ps ledger tr c' Htype Hstep.
  remember (mk_config e ps ledger tr) as c.
  revert e ps ledger tr Heqc T kap Htype.
  induction Hstep; intros e0 ps0 ledger0 tr0 Heqc T0 kap0 Htype0;
    inversion Heqc; subst; clear Heqc; simpl.
  - (* E_App: tapp (tabs T body) v -> subst_top v body *)
    destruct (typing_app_inv _ _ _ _ Htype0) as [T1 [k1 [k2 [Ha Hv]]]].
    destruct (typing_abs_type _ _ _ _ Ha) as [kf [T2 [Heq Hbody]]].
    inversion Heq; subst. eapply subst_gen_top; eauto.
  - (* E_Let: tlet v e2 -> subst_top v e2 *)
    destruct (typing_let_inv _ _ _ _ Htype0) as [T1 [k1 [k2 [H1 H2]]]].
    eapply subst_gen_top; eauto.
  - (* E_IfTrue *)
    destruct (typing_if_inv _ _ _ _ _ Htype0) as [k1 [k2 [k3 [_ [H2 _]]]]].
    eauto.
  - (* E_IfFalse *)
    destruct (typing_if_inv _ _ _ _ _ Htype0) as [k1 [k2 [k3 [_ [_ H3]]]]].
    eauto.
  - (* E_Fix: tfix T body -> subst_top (tfix T body) body *)
    destruct (typing_fix_inv _ _ _ _ Htype0) as [Heq [k0 Hbody]]. subst.
    eapply subst_gen_top. exact Hbody. exact Htype0.
  - (* E_Fst *)
    destruct (typing_fst_inv _ _ _ Htype0) as [T2 [k0 Hp]].
    destruct (typing_pair_inv _ _ _ _ Hp) as [T1 [T2' [k1 [k2 [Heq [H1' H2']]]]]].
    inversion Heq; subst. eauto.
  - (* E_Snd *)
    destruct (typing_snd_inv _ _ _ Htype0) as [T1 [k0 Hp]].
    destruct (typing_pair_inv _ _ _ _ Hp) as [T1' [T2 [k1 [k2 [Heq [H1' H2']]]]]].
    inversion Heq; subst. eauto.
  - (* E_Allow: task k a tgt p -> realize i *)
    subst. destruct (typing_ask_inv _ _ _ _ _ _ Htype0) as [Heq _]. subst.
    exists cap_empty. apply realize_well_typed.
  - (* E_Deny: task k a tgt p -> tdenied *)
    destruct (typing_ask_inv _ _ _ _ _ _ Htype0) as [Heq _]. subst.
    exists cap_empty. apply T_Denied.
  - (* E_Escalate: task k a tgt p -> tsuspended *)
    destruct (typing_ask_inv _ _ _ _ _ _ Htype0) as [Heq _]. subst.
    exists cap_empty. apply T_Suspended.
  - (* E_Ctx: plug E e -> plug E e' *)
    eapply plug_pres; try exact Htype0.
    intros T1 kap1 Ht1.
    eapply (IHHstep _ _ _ _ eq_refl). exact Ht1.
Qed.


(* ================================================================== *)
(** ** Theorem 3: Governance Soundness *)
(* ================================================================== *)

(** Every LEff label in the trace was preceded by a LGov Allow label
    for the same capability class. *)

(* label_eq_dec is now proved in Syntax.v *)

(** Trace monotonicity: traces only grow during execution. *)
Lemma trace_monotone_step :
  forall c c',
    step c c' ->
    exists suffix, cfg_trace c' = cfg_trace c ++ suffix.
Proof.
  intros c c' Hstep. induction Hstep; simpl;
    try (eexists; reflexivity).
  - (* E_Ctx *) destruct IHHstep as [suf Hsuf].
    exists suf. exact Hsuf.
Qed.

Lemma trace_monotone :
  forall c c',
    multi_step c c' ->
    exists suffix, cfg_trace c' = cfg_trace c ++ suffix.
Proof.
  intros c c' Hmulti. induction Hmulti.
  - exists nil. rewrite app_nil_r. reflexivity.
  - destruct (trace_monotone_step _ _ H) as [s1 Hs1].
    destruct IHHmulti as [s2 Hs2].
    exists (s1 ++ s2). rewrite Hs2, Hs1. rewrite app_assoc. reflexivity.
Qed.

Lemma in_trace_persists :
  forall c c' l,
    multi_step c c' ->
    In l (cfg_trace c) ->
    In l (cfg_trace c').
Proof.
  intros c c' l Hmulti Hin.
  destruct (trace_monotone _ _ Hmulti) as [suf Hsuf].
  rewrite Hsuf. apply in_app_iff. left. exact Hin.
Qed.

Theorem governance_soundness :
  forall c c',
    multi_step c c' ->
    forall k v,
      In (LEff k v) (cfg_trace c') ->
      ~ In (LEff k v) (cfg_trace c) ->
      exists r, In (LGov k GovAllow r) (cfg_trace c').
Proof.
  intros c c' Hmulti. induction Hmulti; intros k v Hin Hnotin.
  - (* MS_Refl *) exfalso. apply Hnotin. exact Hin.
  - (* MS_Step: c1 -> c2 ->* c3 *)
    destruct (In_dec label_eq_dec (LEff k v) (cfg_trace c2)) as [Hin2 | Hnotin2].
    + (* LEff k v was introduced in c1 -> c2 *)
      destruct (eff_label_only_from_allow _ _ H k v Hin2 Hnotin) as [r Hr].
      exists r. eapply in_trace_persists; eauto.
    + (* LEff k v was NOT in c2: introduced later *)
      apply (IHHmulti k v); auto.
Qed.

(* ================================================================== *)
(** ** Theorem 4: Mandatory Mediation *)
(* ================================================================== *)

(** Every reduction path from an ask_k term to a realized effect
    contains exactly one governance transition. The governance
    transition and effect realization are atomic (same step). *)

Theorem mandatory_mediation :
  forall k a tgt p ps ledger tr c',
    step (mk_config (task k a tgt p) ps ledger tr) c' ->
    (* Exactly one LGov label is added, and if LEff appears,
       LGov Allow preceded it. *)
    (exists d r,
      cfg_trace c' = List.app tr (LGov k d r :: nil) \/
      cfg_trace c' = List.app tr (LGov k d r :: LEff k (cfg_term c') :: nil)) /\
    (forall v, In (LEff k v) (cfg_trace c') ->
               ~ In (LEff k v) tr ->
               exists r, In (LGov k GovAllow r) (cfg_trace c')).
Proof.
  intros k a tgt p ps ledger tr c' Hstep.
  inversion Hstep; subst; simpl.
  - (* E_Allow *)
    split.
    + exists GovAllow, r. right. reflexivity.
    + intros v0 Hin Hnotin.
      apply List.in_app_iff in Hin. destruct Hin as [Hin | Hin].
      * exfalso. apply Hnotin. exact Hin.
      * simpl in Hin. destruct Hin as [Hin | Hin].
        -- inversion Hin. (* LGov <> LEff *)
        -- destruct Hin as [Hin | Hin].
           ++ exists r. apply List.in_app_iff. right. simpl. left. reflexivity.
           ++ contradiction.
  - (* E_Deny *)
    split.
    + exists GovDeny, r. left. reflexivity.
    + intros v0 Hin Hnotin.
      apply List.in_app_iff in Hin. destruct Hin as [Hin | Hin].
      * exfalso. apply Hnotin. exact Hin.
      * simpl in Hin. destruct Hin as [Hin | Hin].
        -- inversion Hin. (* LGov <> LEff *)
        -- contradiction.
  - (* E_Escalate *)
    split.
    + exists GovEscalate, r. left. reflexivity.
    + intros v0 Hin Hnotin.
      apply List.in_app_iff in Hin. destruct Hin as [Hin | Hin].
      * exfalso. apply Hnotin. exact Hin.
      * simpl in Hin. destruct Hin as [Hin | Hin].
        -- inversion Hin.
        -- contradiction.
  - (* E_Ctx: by task_not_pluggable, E = Hole. But E <> Hole
       is a premise of E_Ctx. Contradiction. *)
    exfalso. apply H4. apply task_not_pluggable in H. destruct H. exact H.
Qed.

(* ================================================================== *)
(** ** Infrastructure for Capability Confinement *)
(* ================================================================== *)

(** A capability set with no members is nil. *)
Lemma cap_all_false_nil :
  forall kap, (forall k, cap_mem k kap = false) -> kap = nil.
Proof.
  induction kap; intros; auto.
  exfalso. specialize (H a). unfold cap_mem in H. simpl in H.
  rewrite cap_class_eq_dec_refl in H. simpl in H. discriminate.
Qed.

Lemma cap_subset_empty_nil :
  forall kap, cap_subset kap cap_empty -> kap = nil.
Proof.
  unfold cap_subset. intros kap H. apply cap_all_false_nil. intros k.
  destruct (cap_mem k kap) eqn:E; auto.
  apply H in E. rewrite cap_mem_empty in E. discriminate.
Qed.

(** Strengthened typing inversions with capability subset bounds. *)

Lemma typing_abs_type_sub : forall T1 body T kap, has_type nil (tabs T1 body) T kap ->
  exists kf T2, T = TArrow T1 T2 /\ has_type (T1 :: nil) body T2 kf /\ cap_subset kf kap.
Proof. intros. remember (@nil ty) as G. remember (tabs T1 body) as e.
  induction H; subst; try discriminate.
  - injection Heqe as Ha Hb. subst. exists kap, T2. repeat split; auto. apply cap_subset_refl.
  - destruct (IHhas_type eq_refl eq_refl) as [kf2 [T2' [Heq [Hb Hsub]]]].
    exists kf2, T2'. repeat split; auto. eapply cap_subset_trans; eauto.
Qed.

Lemma typing_app_inv_sub : forall e1 e2 T kap, has_type nil (tapp e1 e2) T kap ->
  exists T1 k1 k2, has_type nil e1 (TArrow T1 T) k1 /\ has_type nil e2 T1 k2 /\
    cap_subset k1 kap /\ cap_subset k2 kap.
Proof. intros. remember (@nil ty) as G. remember (tapp e1 e2) as e.
  induction H; subst; try discriminate.
  - injection Heqe as; subst.
    exists T1, kap1, kap2. repeat split; auto; [apply cap_subset_union_l | apply cap_subset_union_r].
  - destruct (IHhas_type eq_refl eq_refl) as [T1 [k1 [k2 [H1 [H2 [Hs1 Hs2]]]]]].
    exists T1, k1, k2. repeat split; auto; eapply cap_subset_trans; eauto.
Qed.

Lemma typing_let_inv_sub : forall e1 e2 T kap, has_type nil (tlet e1 e2) T kap ->
  exists T1 k1 k2, has_type nil e1 T1 k1 /\ has_type (T1 :: nil) e2 T k2 /\
    cap_subset k1 kap /\ cap_subset k2 kap.
Proof. intros. remember (@nil ty) as G. remember (tlet e1 e2) as e.
  induction H; subst; try discriminate.
  - injection Heqe as; subst.
    exists T1, kap1, kap2. repeat split; auto; [apply cap_subset_union_l | apply cap_subset_union_r].
  - destruct (IHhas_type eq_refl eq_refl) as [T1 [k1 [k2 [H1 [H2 [Hs1 Hs2]]]]]].
    exists T1, k1, k2. repeat split; auto; eapply cap_subset_trans; eauto.
Qed.

Lemma typing_if_inv_sub : forall e1 e2 e3 T kap, has_type nil (tif e1 e2 e3) T kap ->
  exists k1 k2 k3, has_type nil e1 TBool k1 /\ has_type nil e2 T k2 /\ has_type nil e3 T k3 /\
    cap_subset k1 kap /\ cap_subset k2 kap /\ cap_subset k3 kap.
Proof. intros. remember (@nil ty) as G. remember (tif e1 e2 e3) as e.
  induction H; subst; try discriminate.
  - injection Heqe as; subst.
    exists kap1, kap2, kap3. repeat split; auto.
    + eapply cap_subset_trans. apply cap_subset_union_l. apply cap_subset_refl.
    + eapply cap_subset_trans. apply cap_subset_union_l.
      eapply cap_subset_trans. 2: apply cap_subset_union_r. apply cap_subset_refl.
    + eapply cap_subset_trans. apply cap_subset_union_r.
      eapply cap_subset_trans. 2: apply cap_subset_union_r. apply cap_subset_refl.
  - destruct (IHhas_type eq_refl eq_refl) as [k1 [k2 [k3 [? [? [? [? [? ?]]]]]]]].
    exists k1, k2, k3. repeat split; auto; eapply cap_subset_trans; eauto.
Qed.

Lemma typing_pair_inv_sub : forall v1 v2 T kap, has_type nil (tpair v1 v2) T kap ->
  exists T1 T2 k1 k2, T = TProd T1 T2 /\ has_type nil v1 T1 k1 /\ has_type nil v2 T2 k2 /\
    cap_subset k1 kap /\ cap_subset k2 kap.
Proof. intros. remember (@nil ty) as G. remember (tpair v1 v2) as e.
  induction H; subst; try discriminate.
  - injection Heqe as Ha Hb. subst.
    exists T1, T2, kap1, kap2. repeat split; auto; [apply cap_subset_union_l | apply cap_subset_union_r].
  - destruct (IHhas_type eq_refl eq_refl) as [T1 [T2 [k1 [k2 [? [? [? [? ?]]]]]]]].
    exists T1, T2, k1, k2. repeat split; auto; eapply cap_subset_trans; eauto.
Qed.

Lemma typing_cons_inv_sub : forall v1 v2 T kap, has_type nil (tcons v1 v2) T kap ->
  exists T1 k1 k2, T = TList T1 /\ has_type nil v1 T1 k1 /\ has_type nil v2 (TList T1) k2 /\
    cap_subset k1 kap /\ cap_subset k2 kap.
Proof. intros. remember (@nil ty) as G. remember (tcons v1 v2) as e.
  induction H; subst; try discriminate.
  - injection Heqe as Ha Hb. subst.
    exists T, kap1, kap2. repeat split; auto; [apply cap_subset_union_l | apply cap_subset_union_r].
  - destruct (IHhas_type eq_refl eq_refl) as [T1 [k1 [k2 [? [? [? [? ?]]]]]]].
    exists T1, k1, k2. repeat split; auto; eapply cap_subset_trans; eauto.
Qed.

Lemma typing_fst_inv_sub : forall e0 T kap, has_type nil (tfst e0) T kap ->
  exists T2 k0, has_type nil e0 (TProd T T2) k0 /\ cap_subset k0 kap.
Proof. intros. remember (@nil ty) as G. remember (tfst e0) as e.
  induction H; subst; try discriminate.
  - injection Heqe as. subst. eauto using cap_subset_refl.
  - destruct (IHhas_type eq_refl eq_refl) as [T2 [k0 [? ?]]].
    exists T2, k0. split; auto. eapply cap_subset_trans; eauto.
Qed.

Lemma typing_snd_inv_sub : forall e0 T kap, has_type nil (tsnd e0) T kap ->
  exists T1 k0, has_type nil e0 (TProd T1 T) k0 /\ cap_subset k0 kap.
Proof. intros. remember (@nil ty) as G. remember (tsnd e0) as e.
  induction H; subst; try discriminate.
  - injection Heqe as. subst. eauto using cap_subset_refl.
  - destruct (IHhas_type eq_refl eq_refl) as [T1 [k0 [? ?]]].
    exists T1, k0. split; auto. eapply cap_subset_trans; eauto.
Qed.

Lemma typing_fix_inv_sub : forall T0 body T kap, has_type nil (tfix T0 body) T kap ->
  T = T0 /\ exists k0, has_type (T0 :: nil) body T0 k0 /\ cap_subset k0 kap.
Proof. intros. remember (@nil ty) as G. remember (tfix T0 body) as e.
  induction H; subst; try discriminate.
  - injection Heqe as. subst. split; auto. eauto using cap_subset_refl.
  - destruct (IHhas_type eq_refl eq_refl) as [? [k0 [? ?]]].
    split; auto. exists k0. split; auto. eapply cap_subset_trans; eauto.
Qed.

(** A task term cannot have empty capability. *)
Lemma pure_not_ask :
  forall k a tgt p T,
    ~ has_type nil (task k a tgt p) T cap_empty.
Proof.
  intros k a tgt p T H.
  pose proof (purity_no_ask nil (task k a tgt p) T k H) as Hno.
  simpl in Hno. rewrite cap_class_eq_dec_refl in Hno. discriminate.
Qed.

(** Inner term of a pure plug is pure. *)
Lemma plug_pure_inner_pure :
  forall E e T,
    has_type nil (plug E e) T cap_empty ->
    exists T', has_type nil e T' cap_empty.
Proof.
  induction E; intros e0 T0 Htype; simpl in *.
  - exists T0. exact Htype.
  - destruct (typing_app_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [H1 [_ [Hs _]]]]]].
    apply cap_subset_empty_nil in Hs. subst. apply (IHE _ _ H1).
  - destruct (typing_app_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [_ [H2 [_ Hs]]]]]].
    apply cap_subset_empty_nil in Hs. subst. apply (IHE _ _ H2).
  - destruct (typing_let_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [H1 [_ [Hs _]]]]]].
    apply cap_subset_empty_nil in Hs. subst. apply (IHE _ _ H1).
  - destruct (typing_if_inv_sub _ _ _ _ _ Htype) as [k1 [k2 [k3 [H1 [_ [_ [Hs _]]]]]]].
    apply cap_subset_empty_nil in Hs. subst. apply (IHE _ _ H1).
  - destruct (typing_fst_inv_sub _ _ _ Htype) as [T2 [k0 [Hp Hs]]].
    apply cap_subset_empty_nil in Hs. subst. apply (IHE _ _ Hp).
  - destruct (typing_snd_inv_sub _ _ _ Htype) as [T1 [k0 [Hp Hs]]].
    apply cap_subset_empty_nil in Hs. subst. apply (IHE _ _ Hp).
  - destruct (typing_pair_inv_sub _ _ _ _ Htype) as [T1 [T2 [k1 [k2 [_ [H1 [_ [Hs _]]]]]]]].
    apply cap_subset_empty_nil in Hs. subst. apply (IHE _ _ H1).
  - destruct (typing_pair_inv_sub _ _ _ _ Htype) as [T1 [T2 [k1 [k2 [_ [_ [H2 [_ Hs]]]]]]]].
    apply cap_subset_empty_nil in Hs. subst. apply (IHE _ _ H2).
  - destruct (typing_cons_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [_ [H1 [_ [Hs _]]]]]]].
    apply cap_subset_empty_nil in Hs. subst. apply (IHE _ _ H1).
  - destruct (typing_cons_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [_ [_ [H2 [_ Hs]]]]]]].
    apply cap_subset_empty_nil in Hs. subst. apply (IHE _ _ H2).
Qed.

(** Exact capability preservation for plug at cap_empty. *)
Lemma plug_pres_exact_empty :
  forall E e e',
    (forall T, has_type nil e T cap_empty -> has_type nil e' T cap_empty) ->
    forall T, has_type nil (plug E e) T cap_empty ->
    has_type nil (plug E e') T cap_empty.
Proof.
  induction E; intros e0 e0' IH T0 Htype; simpl in *.
  - apply IH. exact Htype.
  - destruct (typing_app_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [H1 [H2 [Hs1 Hs2]]]]]].
    apply cap_subset_empty_nil in Hs1. apply cap_subset_empty_nil in Hs2. subst.
    change (has_type nil (tapp (plug E e0') t) T0 (cap_union cap_empty cap_empty)).
    eapply T_App. apply (IHE e0 e0' IH _ H1). exact H2.
  - destruct (typing_app_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [H1 [H2 [Hs1 Hs2]]]]]].
    apply cap_subset_empty_nil in Hs1. apply cap_subset_empty_nil in Hs2. subst.
    change (has_type nil (tapp t (plug E e0')) T0 (cap_union cap_empty cap_empty)).
    eapply T_App. exact H1. apply (IHE e0 e0' IH _ H2).
  - destruct (typing_let_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [H1 [H2 [Hs1 Hs2]]]]]].
    apply cap_subset_empty_nil in Hs1. apply cap_subset_empty_nil in Hs2. subst.
    change (has_type nil (tlet (plug E e0') t) T0 (cap_union cap_empty cap_empty)).
    eapply T_Let. apply (IHE e0 e0' IH _ H1). exact H2.
  - destruct (typing_if_inv_sub _ _ _ _ _ Htype) as [k1 [k2 [k3 [H1 [H2 [H3 [Hs1 [Hs2 Hs3]]]]]]]].
    apply cap_subset_empty_nil in Hs1. apply cap_subset_empty_nil in Hs2.
    apply cap_subset_empty_nil in Hs3. subst.
    change (has_type nil (tif (plug E e0') t t0) T0
      (cap_union cap_empty (cap_union cap_empty cap_empty))).
    eapply T_If. apply (IHE e0 e0' IH _ H1). exact H2. exact H3.
  - destruct (typing_fst_inv_sub _ _ _ Htype) as [T2 [k0 [Hp Hs]]].
    apply cap_subset_empty_nil in Hs. subst.
    eapply T_Fst. apply (IHE e0 e0' IH _ Hp).
  - destruct (typing_snd_inv_sub _ _ _ Htype) as [T1 [k0 [Hp Hs]]].
    apply cap_subset_empty_nil in Hs. subst.
    eapply T_Snd. apply (IHE e0 e0' IH _ Hp).
  - destruct (typing_pair_inv_sub _ _ _ _ Htype) as [T1 [T2 [k1 [k2 [Heq [H1 [H2 [Hs1 Hs2]]]]]]]].
    subst. apply cap_subset_empty_nil in Hs1. apply cap_subset_empty_nil in Hs2. subst.
    change (has_type nil (tpair (plug E e0') t) (TProd T1 T2) (cap_union cap_empty cap_empty)).
    eapply T_Pair. apply (IHE e0 e0' IH _ H1). exact H2.
  - destruct (typing_pair_inv_sub _ _ _ _ Htype) as [T1 [T2 [k1 [k2 [Heq [H1 [H2 [Hs1 Hs2]]]]]]]].
    subst. apply cap_subset_empty_nil in Hs1. apply cap_subset_empty_nil in Hs2. subst.
    change (has_type nil (tpair t (plug E e0')) (TProd T1 T2) (cap_union cap_empty cap_empty)).
    eapply T_Pair. exact H1. apply (IHE e0 e0' IH _ H2).
  - destruct (typing_cons_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [Heq [H1 [H2 [Hs1 Hs2]]]]]]].
    subst. apply cap_subset_empty_nil in Hs1. apply cap_subset_empty_nil in Hs2. subst.
    change (has_type nil (tcons (plug E e0') t) (TList T1) (cap_union cap_empty cap_empty)).
    eapply T_Cons. apply (IHE e0 e0' IH _ H1). exact H2.
  - destruct (typing_cons_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [Heq [H1 [H2 [Hs1 Hs2]]]]]]].
    subst. apply cap_subset_empty_nil in Hs1. apply cap_subset_empty_nil in Hs2. subst.
    change (has_type nil (tcons t (plug E e0')) (TList T1) (cap_union cap_empty cap_empty)).
    eapply T_Cons. exact H1. apply (IHE e0 e0' IH _ H2).
Qed.

(** Pure terms preserve typing at cap_empty across reduction steps. *)
Theorem preservation_pure :
  forall e T ps ledger tr c',
    has_type nil e T cap_empty ->
    step (mk_config e ps ledger tr) c' ->
    has_type nil (cfg_term c') T cap_empty.
Proof.
  intros e T ps ledger tr c' Htype Hstep.
  remember (mk_config e ps ledger tr) as c.
  revert e ps ledger tr Heqc T Htype.
  induction Hstep; intros e0 ps0 ledger0 tr0 Heqc T0 Htype0;
    inversion Heqc; subst; clear Heqc; simpl.
  - (* E_App *)
    destruct (typing_app_inv_sub _ _ _ _ Htype0) as [T1 [k1 [k2 [Ha [Hv [Hs1 Hs2]]]]]].
    apply cap_subset_empty_nil in Hs1. apply cap_subset_empty_nil in Hs2. subst.
    destruct (typing_abs_type_sub _ _ _ _ Ha) as [kf [T2 [Heq [Hbody Hsf]]]].
    apply cap_subset_empty_nil in Hsf. subst.
    inversion Heq; subst.
    eapply substitution_preserves_typing; eauto.
  - (* E_Let *)
    destruct (typing_let_inv_sub _ _ _ _ Htype0) as [T1 [k1 [k2 [H1 [H2 [Hs1 Hs2]]]]]].
    apply cap_subset_empty_nil in Hs1. apply cap_subset_empty_nil in Hs2. subst.
    eapply substitution_preserves_typing; eauto.
  - (* E_IfTrue *)
    destruct (typing_if_inv_sub _ _ _ _ _ Htype0) as [k1 [k2 [k3 [_ [H2 [_ [_ [Hs2 _]]]]]]]].
    apply cap_subset_empty_nil in Hs2. subst. exact H2.
  - (* E_IfFalse *)
    destruct (typing_if_inv_sub _ _ _ _ _ Htype0) as [k1 [k2 [k3 [_ [_ [H3 [_ [_ Hs3]]]]]]]].
    apply cap_subset_empty_nil in Hs3. subst. exact H3.
  - (* E_Fix *)
    destruct (typing_fix_inv_sub _ _ _ _ Htype0) as [Heq [k0 [Hbody Hsk]]].
    apply cap_subset_empty_nil in Hsk. subst.
    eapply substitution_preserves_typing; eauto.
  - (* E_Fst *)
    destruct (typing_fst_inv_sub _ _ _ Htype0) as [T2 [k0 [Hp Hs]]].
    apply cap_subset_empty_nil in Hs. subst.
    destruct (typing_pair_inv_sub _ _ _ _ Hp) as [T1 [T2' [k1 [k2 [Heq [H1 [H2 [Hs1 Hs2]]]]]]]].
    injection Heq as; subst. apply cap_subset_empty_nil in Hs1. subst. exact H1.
  - (* E_Snd *)
    destruct (typing_snd_inv_sub _ _ _ Htype0) as [T1 [k0 [Hp Hs]]].
    apply cap_subset_empty_nil in Hs. subst.
    destruct (typing_pair_inv_sub _ _ _ _ Hp) as [T1' [T2 [k1 [k2 [Heq [H1 [H2 [Hs1 Hs2]]]]]]]].
    injection Heq as; subst. apply cap_subset_empty_nil in Hs2. subst. exact H2.
  - (* E_Allow: impossible for pure term *)
    exfalso. exact (pure_not_ask k a tgt p T0 Htype0).
  - (* E_Deny: impossible for pure term *)
    exfalso. exact (pure_not_ask k a tgt p T0 Htype0).
  - (* E_Escalate: impossible for pure term *)
    exfalso. exact (pure_not_ask k a tgt p T0 Htype0).
  - (* E_Ctx *)
    eapply plug_pres_exact_empty; try exact Htype0.
    intros T1 Ht1.
    destruct (plug_pure_inner_pure E e T0 Htype0) as [T' Ht'].
    (* Need: has_type nil e T1 cap_empty.
       We have Ht' : has_type nil e T' cap_empty and
       Ht1 : has_type nil e T1 cap_empty.
       Use IH directly. *)
    eapply (IHHstep _ _ _ _ eq_refl). exact Ht1.
Qed.

(** Pure step preserves ledger: governance steps can't occur on pure terms. *)
Lemma pure_step_preserves_ledger :
  forall e T ps ledger tr c',
    has_type nil e T cap_empty ->
    step (mk_config e ps ledger tr) c' ->
    cfg_ledger c' = ledger.
Proof.
  intros e T ps ledger tr c' Htype Hstep.
  remember (mk_config e ps ledger tr) as c.
  revert e ps ledger tr Heqc T Htype.
  induction Hstep; intros e0 ps0 ledger0 tr0 Heqc T0 Htype0;
    inversion Heqc; subst; clear Heqc; simpl; auto.
  - exfalso. exact (pure_not_ask k a tgt p T0 Htype0).
  - exfalso. exact (pure_not_ask k a tgt p T0 Htype0).
  - exfalso. exact (pure_not_ask k a tgt p T0 Htype0).
  - destruct (plug_pure_inner_pure E e T0 Htype0) as [T' Ht'].
    eapply (IHHstep _ _ _ _ eq_refl). exact Ht'.
Qed.

(** Pure step adds no governance labels to the trace. *)
Lemma pure_step_no_new_gov :
  forall e T ps ledger tr c',
    has_type nil e T cap_empty ->
    step (mk_config e ps ledger tr) c' ->
    forall k d r,
      In (LGov k d r) (cfg_trace c') ->
      In (LGov k d r) tr.
Proof.
  intros e T ps ledger tr c' Htype Hstep.
  remember (mk_config e ps ledger tr) as c.
  revert e ps ledger tr Heqc T Htype.
  induction Hstep; intros e0 ps0 ledger0 tr0 Heqc T0 Htype0;
    inversion Heqc; subst; clear Heqc;
    intros k0 d0 r0 Hin; simpl in *.
  - apply in_app_iff in Hin. destruct Hin as [|[|[]]]; auto; discriminate.
  - apply in_app_iff in Hin. destruct Hin as [|[|[]]]; auto; discriminate.
  - apply in_app_iff in Hin. destruct Hin as [|[|[]]]; auto; discriminate.
  - apply in_app_iff in Hin. destruct Hin as [|[|[]]]; auto; discriminate.
  - apply in_app_iff in Hin. destruct Hin as [|[|[]]]; auto; discriminate.
  - apply in_app_iff in Hin. destruct Hin as [|[|[]]]; auto; discriminate.
  - apply in_app_iff in Hin. destruct Hin as [|[|[]]]; auto; discriminate.
  - exfalso. exact (pure_not_ask k a tgt p T0 Htype0).
  - exfalso. exact (pure_not_ask k a tgt p T0 Htype0).
  - exfalso. exact (pure_not_ask k a tgt p T0 Htype0).
  - destruct (plug_pure_inner_pure E e T0 Htype0) as [T' Ht'].
    eapply (IHHstep _ _ _ _ eq_refl). exact Ht'. exact Hin.
Qed.

(* ================================================================== *)
(** ** Theorem 5: Capability Confinement *)
(* ================================================================== *)

(** Helper: subset is compatible with union *)
Lemma cap_subset_union_compat :
  forall a b c d,
    cap_subset a c -> cap_subset b d ->
    cap_subset (cap_union a b) (cap_union c d).
Proof.
  intros. apply cap_subset_union_both.
  - eapply cap_subset_trans; eauto. apply cap_subset_union_l.
  - eapply cap_subset_trans; eauto. apply cap_subset_union_r.
Qed.

(** Strengthened substitution at arbitrary position with subset bound. *)
Lemma substitution_at_pos_gen_sub :
  forall Gamma e T kap,
    has_type Gamma e T kap ->
    forall (Gpre Gpost : list ty) T_s s kap_s,
      Gamma = Gpre ++ (T_s :: Gpost) ->
      has_type (Gpre ++ Gpost) s T_s kap_s ->
      exists kap_out, has_type (Gpre ++ Gpost) (subst (length Gpre) s e) T kap_out /\
        cap_subset kap_out (cap_union kap kap_s).
Proof.
  intros Gamma e T kap Htype.
  induction Htype; intros Gpre Gpost T_s0 s0 kap_s HG Hs; subst; simpl.
  - eexists; split; [apply T_Int | apply cap_subset_empty].
  - eexists; split; [apply T_Bool | apply cap_subset_empty].
  - eexists; split; [apply T_Str | apply cap_subset_empty].
  - (* T_Var *)
    unfold ctx_lookup in H.
    destruct (Nat.eqb x (length Gpre)) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      rewrite nth_error_app2 in H by lia.
      replace (length Gpre - length Gpre) with 0 in H by lia.
      simpl in H. injection H as. subst.
      eexists; split; [exact Hs | simpl; apply cap_subset_refl].
    + destruct (Nat.ltb (length Gpre) x) eqn:Hlt.
      * apply Nat.ltb_lt in Hlt. eexists; split.
        -- apply T_Var. unfold ctx_lookup.
           rewrite nth_error_app2 in H by lia.
           replace (x - length Gpre) with (S (x - length Gpre - 1)) in H by lia.
           simpl in H. rewrite nth_error_app2 by lia.
           replace (pred x - length Gpre) with (x - length Gpre - 1) by lia. exact H.
        -- apply cap_subset_empty.
      * apply Nat.ltb_nlt in Hlt. apply Nat.eqb_neq in Heq.
        assert (x < length Gpre) by lia. eexists; split.
        -- apply T_Var. unfold ctx_lookup.
           rewrite nth_error_app1 in H by lia.
           rewrite nth_error_app1 by lia. exact H.
        -- apply cap_subset_empty.
  - eexists; split; [apply T_Denied | apply cap_subset_empty].
  - eexists; split; [apply T_Suspended | apply cap_subset_empty].
  - eexists; split; [apply T_Nil | apply cap_subset_empty].
  - (* T_Abs *)
    destruct (IHHtype (T1 :: Gpre) Gpost T_s0 (shift 1 0 s0) kap_s eq_refl
      (shift_preserves_typing _ _ _ _ _ Hs)) as [ko [Hko Hsub]].
    eexists; split; [eapply T_Abs; exact Hko | exact Hsub].
  - (* T_App *)
    destruct (IHHtype1 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko1 [Hko1 Hs1]].
    destruct (IHHtype2 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko2 [Hko2 Hs2]].
    eexists; split; [eapply T_App; eassumption |].
    apply cap_subset_union_both.
    + eapply cap_subset_trans. exact Hs1. apply cap_subset_union_both.
      * eapply cap_subset_trans. apply cap_subset_union_l. apply cap_subset_union_l.
      * apply cap_subset_union_r.
    + eapply cap_subset_trans. exact Hs2. apply cap_subset_union_both.
      * eapply cap_subset_trans. apply cap_subset_union_r. apply cap_subset_union_l.
      * apply cap_subset_union_r.
  - (* T_Let *)
    destruct (IHHtype1 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko1 [Hko1 Hs1]].
    destruct (IHHtype2 (T1 :: Gpre) Gpost T_s0 (shift 1 0 s0) kap_s eq_refl
      (shift_preserves_typing _ _ _ _ _ Hs)) as [ko2 [Hko2 Hs2]].
    eexists; split; [eapply T_Let; eassumption |].
    apply cap_subset_union_both.
    + eapply cap_subset_trans. exact Hs1. apply cap_subset_union_both.
      * eapply cap_subset_trans. apply cap_subset_union_l. apply cap_subset_union_l.
      * apply cap_subset_union_r.
    + eapply cap_subset_trans. exact Hs2. apply cap_subset_union_both.
      * eapply cap_subset_trans. apply cap_subset_union_r. apply cap_subset_union_l.
      * apply cap_subset_union_r.
  - (* T_If *)
    destruct (IHHtype1 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko1 [Hko1 Hs1]].
    destruct (IHHtype2 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko2 [Hko2 Hs2]].
    destruct (IHHtype3 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko3 [Hko3 Hs3]].
    eexists; split; [eapply T_If; eassumption |].
    apply cap_subset_union_both.
    + eapply cap_subset_trans. exact Hs1. apply cap_subset_union_both.
      * eapply cap_subset_trans. apply cap_subset_union_l. apply cap_subset_union_l.
      * apply cap_subset_union_r.
    + apply cap_subset_union_both.
      * eapply cap_subset_trans. exact Hs2. apply cap_subset_union_both.
        -- eapply cap_subset_trans. apply cap_subset_union_l.
           eapply cap_subset_trans. apply cap_subset_union_r. apply cap_subset_union_l.
        -- apply cap_subset_union_r.
      * eapply cap_subset_trans. exact Hs3. apply cap_subset_union_both.
        -- eapply cap_subset_trans. apply cap_subset_union_r.
           eapply cap_subset_trans. apply cap_subset_union_r. apply cap_subset_union_l.
        -- apply cap_subset_union_r.
  - (* T_Pair *)
    destruct (IHHtype1 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko1 [Hko1 Hs1]].
    destruct (IHHtype2 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko2 [Hko2 Hs2]].
    eexists; split; [eapply T_Pair; eassumption |].
    apply cap_subset_union_both.
    + eapply cap_subset_trans. exact Hs1. apply cap_subset_union_both.
      * eapply cap_subset_trans. apply cap_subset_union_l. apply cap_subset_union_l.
      * apply cap_subset_union_r.
    + eapply cap_subset_trans. exact Hs2. apply cap_subset_union_both.
      * eapply cap_subset_trans. apply cap_subset_union_r. apply cap_subset_union_l.
      * apply cap_subset_union_r.
  - (* T_Fst *)
    destruct (IHHtype Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko [Hko Hsub]].
    eexists; split; [eapply T_Fst; eassumption | exact Hsub].
  - (* T_Snd *)
    destruct (IHHtype Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko [Hko Hsub]].
    eexists; split; [eapply T_Snd; eassumption | exact Hsub].
  - (* T_Cons *)
    destruct (IHHtype1 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko1 [Hko1 Hs1]].
    destruct (IHHtype2 Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko2 [Hko2 Hs2]].
    eexists; split; [eapply T_Cons; eassumption |].
    apply cap_subset_union_both.
    + eapply cap_subset_trans. exact Hs1. apply cap_subset_union_both.
      * eapply cap_subset_trans. apply cap_subset_union_l. apply cap_subset_union_l.
      * apply cap_subset_union_r.
    + eapply cap_subset_trans. exact Hs2. apply cap_subset_union_both.
      * eapply cap_subset_trans. apply cap_subset_union_r. apply cap_subset_union_l.
      * apply cap_subset_union_r.
  - (* T_Fix *)
    destruct (IHHtype (T :: Gpre) Gpost T_s0 (shift 1 0 s0) kap_s eq_refl
      (shift_preserves_typing _ _ _ _ _ Hs)) as [ko [Hko Hsub]].
    eexists; split; [eapply T_Fix; exact Hko | exact Hsub].
  - (* T_Ask *)
    eexists; split; [apply T_Ask; apply subst_preserves_value; exact H |].
    change (cap_subset (cap_singleton k) (cap_union (cap_singleton k) kap_s)).
    apply cap_subset_union_l.
  - (* T_Sub *)
    destruct (IHHtype Gpre Gpost T_s0 s0 kap_s eq_refl Hs) as [ko [Hko Hsub]].
    eexists; split; [exact Hko |].
    eapply cap_subset_trans. exact Hsub.
    apply cap_subset_union_compat; [| apply cap_subset_refl]. exact H.
Qed.

(** Top-level wrapper for strengthened substitution. *)
Lemma subst_gen_top_sub :
  forall e T kap s T_s kap_s,
    has_type (T_s :: nil) e T kap ->
    has_type nil s T_s kap_s ->
    exists kap', has_type nil (subst_top s e) T kap' /\
      cap_subset kap' (cap_union kap kap_s).
Proof.
  intros. unfold subst_top.
  eapply (substitution_at_pos_gen_sub (T_s :: nil) e T kap H
    (@nil ty) nil T_s s kap_s eq_refl).
  simpl. exact H0.
Qed.

(** Plug preserves typing with capability subset tracking. *)
Lemma plug_pres_sub :
  forall E e e',
    (forall T kap, has_type nil e T kap ->
      exists kap', has_type nil e' T kap' /\ cap_subset kap' kap) ->
    forall T kap, has_type nil (plug E e) T kap ->
    exists kap', has_type nil (plug E e') T kap' /\ cap_subset kap' kap.
Proof.
  induction E; intros e0 e0' IH T0 kap0 Htype; simpl in *.
  - apply IH. exact Htype.
  - destruct (typing_app_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [H1 [H2 [Hs1 Hs2]]]]]].
    destruct (IHE _ _ IH _ _ H1) as [k1' [H1' Hk1]].
    eexists. split. eapply T_App; eassumption.
    apply cap_subset_union_both.
    + eapply cap_subset_trans; eauto.
    + auto.
  - destruct (typing_app_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [H1 [H2 [Hs1 Hs2]]]]]].
    destruct (IHE _ _ IH _ _ H2) as [k2' [H2' Hk2]].
    eexists. split. eapply T_App; eassumption.
    apply cap_subset_union_both.
    + auto.
    + eapply cap_subset_trans; eauto.
  - destruct (typing_let_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [H1 [H2 [Hs1 Hs2]]]]]].
    destruct (IHE _ _ IH _ _ H1) as [k1' [H1' Hk1]].
    eexists. split. eapply T_Let; eassumption.
    apply cap_subset_union_both.
    + eapply cap_subset_trans; eauto.
    + auto.
  - destruct (typing_if_inv_sub _ _ _ _ _ Htype) as [k1 [k2 [k3 [H1 [H2 [H3 [Hs1 [Hs2 Hs3]]]]]]]].
    destruct (IHE _ _ IH _ _ H1) as [k1' [H1' Hk1]].
    eexists. split. eapply T_If; eassumption.
    apply cap_subset_union_both.
    + eapply cap_subset_trans; eauto.
    + apply cap_subset_union_both; auto.
  - destruct (typing_fst_inv_sub _ _ _ Htype) as [T2 [k0 [Hp Hs]]].
    destruct (IHE _ _ IH _ _ Hp) as [k0' [Hp' Hk]].
    eexists. split. eapply T_Fst; eassumption. eapply cap_subset_trans; eauto.
  - destruct (typing_snd_inv_sub _ _ _ Htype) as [T1 [k0 [Hp Hs]]].
    destruct (IHE _ _ IH _ _ Hp) as [k0' [Hp' Hk]].
    eexists. split. eapply T_Snd; eassumption. eapply cap_subset_trans; eauto.
  - destruct (typing_pair_inv_sub _ _ _ _ Htype) as [T1 [T2 [k1 [k2 [Heq [H1 [H2 [Hs1 Hs2]]]]]]]].
    subst. destruct (IHE _ _ IH _ _ H1) as [k1' [H1' Hk1]].
    eexists. split. eapply T_Pair; eassumption.
    apply cap_subset_union_both.
    + eapply cap_subset_trans; eauto.
    + auto.
  - destruct (typing_pair_inv_sub _ _ _ _ Htype) as [T1 [T2 [k1 [k2 [Heq [H1 [H2 [Hs1 Hs2]]]]]]]].
    subst. destruct (IHE _ _ IH _ _ H2) as [k2' [H2' Hk2]].
    eexists. split. eapply T_Pair; eassumption.
    apply cap_subset_union_both.
    + auto.
    + eapply cap_subset_trans; eauto.
  - destruct (typing_cons_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [Heq [H1 [H2 [Hs1 Hs2]]]]]]].
    subst. destruct (IHE _ _ IH _ _ H1) as [k1' [H1' Hk1]].
    eexists. split. eapply T_Cons; eassumption.
    apply cap_subset_union_both.
    + eapply cap_subset_trans; eauto.
    + auto.
  - destruct (typing_cons_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [Heq [H1 [H2 [Hs1 Hs2]]]]]]].
    subst. destruct (IHE _ _ IH _ _ H2) as [k2' [H2' Hk2]].
    eexists. split. eapply T_Cons; eassumption.
    apply cap_subset_union_both.
    + auto.
    + eapply cap_subset_trans; eauto.
Qed.

(** Strengthened preservation: result cap is subset of original cap. *)
Theorem preservation_subset :
  forall e T kap ps ledger tr c',
    has_type nil e T kap ->
    step (mk_config e ps ledger tr) c' ->
    exists kap', has_type nil (cfg_term c') T kap' /\ cap_subset kap' kap.
Proof.
  intros e T kap ps ledger tr c' Htype Hstep.
  remember (mk_config e ps ledger tr) as c.
  revert e ps ledger tr Heqc T kap Htype.
  induction Hstep; intros e0 ps0 ledger0 tr0 Heqc T0 kap0 Htype0;
    inversion Heqc; subst; clear Heqc; simpl.
  - (* E_App *)
    destruct (typing_app_inv_sub _ _ _ _ Htype0) as [T1 [k1 [k2 [Ha [Hv [Hs1 Hs2]]]]]].
    destruct (typing_abs_type_sub _ _ _ _ Ha) as [kf [T2 [Heq [Hbody Hsf]]]].
    inversion Heq; subst.
    destruct (subst_gen_top_sub _ _ _ _ _ _ Hbody Hv) as [ko [Hko Hsub]].
    exists ko. split; auto.
    eapply cap_subset_trans. exact Hsub.
    apply cap_subset_union_both.
    + eapply cap_subset_trans. exact Hsf. exact Hs1.
    + exact Hs2.
  - (* E_Let *)
    destruct (typing_let_inv_sub _ _ _ _ Htype0) as [T1 [k1 [k2 [H1 [H2 [Hs1 Hs2]]]]]].
    destruct (subst_gen_top_sub _ _ _ _ _ _ H2 H1) as [ko [Hko Hsub]].
    exists ko. split; auto.
    eapply cap_subset_trans. exact Hsub.
    apply cap_subset_union_both.
    + exact Hs2.
    + exact Hs1.
  - (* E_IfTrue *)
    destruct (typing_if_inv_sub _ _ _ _ _ Htype0) as [k1 [k2 [k3 [_ [H2 [_ [_ [Hs2 _]]]]]]]].
    eauto.
  - (* E_IfFalse *)
    destruct (typing_if_inv_sub _ _ _ _ _ Htype0) as [k1 [k2 [k3 [_ [_ [H3 [_ [_ Hs3]]]]]]]].
    eauto.
  - (* E_Fix *)
    destruct (typing_fix_inv_sub _ _ _ _ Htype0) as [Heq [k0 [Hbody Hsk]]]. subst.
    destruct (subst_gen_top_sub _ _ _ _ _ _ Hbody Htype0) as [ko [Hko Hsub]].
    exists ko. split; auto.
    eapply cap_subset_trans. exact Hsub.
    apply cap_subset_union_both; auto. apply cap_subset_refl.
  - (* E_Fst *)
    destruct (typing_fst_inv_sub _ _ _ Htype0) as [T2 [k0 [Hp Hs]]].
    destruct (typing_pair_inv_sub _ _ _ _ Hp) as [T1 [T2' [k1 [k2 [Heq [H1 [H2 [Hs1 Hs2]]]]]]]].
    injection Heq as; subst. exists k1. split; auto.
    eapply cap_subset_trans; eauto.
  - (* E_Snd *)
    destruct (typing_snd_inv_sub _ _ _ Htype0) as [T1 [k0 [Hp Hs]]].
    destruct (typing_pair_inv_sub _ _ _ _ Hp) as [T1' [T2 [k1 [k2 [Heq [H1 [H2 [Hs1 Hs2]]]]]]]].
    injection Heq as; subst. exists k2. split; auto.
    eapply cap_subset_trans; eauto.
  - (* E_Allow *)
    destruct (typing_ask_inv _ _ _ _ _ _ Htype0) as [Heq _]. subst.
    exists cap_empty. split. apply realize_well_typed. apply cap_subset_empty.
  - (* E_Deny *)
    destruct (typing_ask_inv _ _ _ _ _ _ Htype0) as [Heq _]. subst.
    exists cap_empty. split. apply T_Denied. apply cap_subset_empty.
  - (* E_Escalate *)
    destruct (typing_ask_inv _ _ _ _ _ _ Htype0) as [Heq _]. subst.
    exists cap_empty. split. apply T_Suspended. apply cap_subset_empty.
  - (* E_Ctx *)
    eapply plug_pres_sub; try exact Htype0.
    intros T1 kap1 Ht1. eapply (IHHstep _ _ _ _ eq_refl); eauto.
Qed.

(** A task term's capability class is always in its typing cap set. *)
Lemma typing_ask_cap : forall k a tgt p T kap,
  has_type nil (task k a tgt p) T kap -> cap_mem k kap = true.
Proof.
  intros. remember (@nil ty) as G. remember (task k a tgt p) as e.
  induction H; subst; try discriminate.
  - injection Heqe as; subst. apply cap_mem_singleton.
  - apply H0. apply IHhas_type; auto.
Qed.

(** Inner term of a plugged expression has capability bounded by outer. *)
Lemma plug_typing_bounded :
  forall E e T kap,
    has_type nil (plug E e) T kap ->
    exists T' kap', has_type nil e T' kap' /\ cap_subset kap' kap.
Proof.
  induction E; intros e0 T0 kap0 Htype; simpl in *.
  - exists T0, kap0. auto using cap_subset_refl.
  - destruct (typing_app_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [H1 [_ [Hs1 _]]]]]].
    destruct (IHE _ _ _ H1) as [T' [kap' [Ht Hs]]].
    exists T', kap'. split; auto. eapply cap_subset_trans; eauto.
  - destruct (typing_app_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [_ [H2 [_ Hs2]]]]]].
    destruct (IHE _ _ _ H2) as [T' [kap' [Ht Hs]]].
    exists T', kap'. split; auto. eapply cap_subset_trans; eauto.
  - destruct (typing_let_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [H1 [_ [Hs1 _]]]]]].
    destruct (IHE _ _ _ H1) as [T' [kap' [Ht Hs]]].
    exists T', kap'. split; auto. eapply cap_subset_trans; eauto.
  - destruct (typing_if_inv_sub _ _ _ _ _ Htype) as [k1 [k2 [k3 [H1 [_ [_ [Hs1 _]]]]]]].
    destruct (IHE _ _ _ H1) as [T' [kap' [Ht Hs]]].
    exists T', kap'. split; auto. eapply cap_subset_trans; eauto.
  - destruct (typing_fst_inv_sub _ _ _ Htype) as [T2 [k0 [Hp Hs]]].
    destruct (IHE _ _ _ Hp) as [T' [kap' [Ht Hs']]].
    exists T', kap'. split; auto. eapply cap_subset_trans; eauto.
  - destruct (typing_snd_inv_sub _ _ _ Htype) as [T1 [k0 [Hp Hs]]].
    destruct (IHE _ _ _ Hp) as [T' [kap' [Ht Hs']]].
    exists T', kap'. split; auto. eapply cap_subset_trans; eauto.
  - destruct (typing_pair_inv_sub _ _ _ _ Htype) as [T1 [T2 [k1 [k2 [_ [H1 [_ [Hs1 _]]]]]]]].
    destruct (IHE _ _ _ H1) as [T' [kap' [Ht Hs]]].
    exists T', kap'. split; auto. eapply cap_subset_trans; eauto.
  - destruct (typing_pair_inv_sub _ _ _ _ Htype) as [T1 [T2 [k1 [k2 [_ [_ [H2 [_ Hs2]]]]]]]].
    destruct (IHE _ _ _ H2) as [T' [kap' [Ht Hs]]].
    exists T', kap'. split; auto. eapply cap_subset_trans; eauto.
  - destruct (typing_cons_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [_ [H1 [_ [Hs1 _]]]]]]].
    destruct (IHE _ _ _ H1) as [T' [kap' [Ht Hs]]].
    exists T', kap'. split; auto. eapply cap_subset_trans; eauto.
  - destruct (typing_cons_inv_sub _ _ _ _ Htype) as [T1 [k1 [k2 [_ [_ [H2 [_ Hs2]]]]]]].
    destruct (IHE _ _ _ H2) as [T' [kap' [Ht Hs]]].
    exists T', kap'. split; auto. eapply cap_subset_trans; eauto.
Qed.

(** Single-step capability confinement: any new LGov k label
    has cap_mem k kap = true for the current term's typing. *)
Lemma step_gov_cap :
  forall e T kap ps ledger tr c',
    has_type nil e T kap ->
    step (mk_config e ps ledger tr) c' ->
    forall k d r,
      In (LGov k d r) (cfg_trace c') ->
      ~ In (LGov k d r) tr ->
      cap_mem k kap = true.
Proof.
  intros e T kap ps ledger tr c' Htype Hstep.
  remember (mk_config e ps ledger tr) as c.
  revert e ps ledger tr Heqc T kap Htype.
  induction Hstep; intros e0 ps0 ledger0 tr0 Heqc T0 kap0 Htype0;
    inversion Heqc; subst; clear Heqc;
    intros k0 d0 r0 Hin Hnotin.
  (* Pure steps: only LSilent added, no LGov possible *)
  - apply in_app_iff in Hin; destruct Hin as [|[|[]]]; auto; try discriminate; contradiction.
  - apply in_app_iff in Hin; destruct Hin as [|[|[]]]; auto; try discriminate; contradiction.
  - apply in_app_iff in Hin; destruct Hin as [|[|[]]]; auto; try discriminate; contradiction.
  - apply in_app_iff in Hin; destruct Hin as [|[|[]]]; auto; try discriminate; contradiction.
  - apply in_app_iff in Hin; destruct Hin as [|[|[]]]; auto; try discriminate; contradiction.
  - apply in_app_iff in Hin; destruct Hin as [|[|[]]]; auto; try discriminate; contradiction.
  - apply in_app_iff in Hin; destruct Hin as [|[|[]]]; auto; try discriminate; contradiction.
  (* E_Allow *)
  - apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + contradiction.
    + simpl in Hin. destruct Hin as [Hin | [Hin | Hin]].
      * injection Hin as; subst. eapply typing_ask_cap; eauto.
      * discriminate.
      * contradiction.
  (* E_Deny *)
  - apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + contradiction.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * injection Hin as; subst. eapply typing_ask_cap; eauto.
      * contradiction.
  (* E_Escalate *)
  - apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + contradiction.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * injection Hin as; subst. eapply typing_ask_cap; eauto.
      * contradiction.
  (* E_Ctx *)
  - destruct (plug_typing_bounded E e T0 kap0 Htype0) as [T' [kap' [Ht' Hsub]]].
    apply Hsub. eapply (IHHstep _ _ _ _ eq_refl _ _ Ht'); eauto.
Qed.

(** Capability confinement: every governance label in the trace
    has its capability class in the typing's capability set. *)
Theorem capability_confinement :
  forall e T kap ps ledger tr c',
    has_type nil e T kap ->
    multi_step (mk_config e ps ledger tr) c' ->
    forall k d r,
      In (LGov k d r) (cfg_trace c') ->
      ~ In (LGov k d r) tr ->
      cap_mem k kap = true.
Proof.
  intros e T kap ps ledger tr c' Htype Hmulti.
  remember (mk_config e ps ledger tr) as c.
  revert e ps ledger tr Heqc T kap Htype.
  induction Hmulti; intros e0 ps0 ledger0 tr0 Heqc T0 kap0 Htype0 k0 d0 r0 Hin Hnotin.
  - subst. contradiction.
  - subst.
    destruct (In_dec label_eq_dec (LGov k0 d0 r0) (cfg_trace c2)) as [Hin2 | Hnotin2].
    + eapply step_gov_cap; eauto.
    + destruct c2 as [e2 ps2 l2 t2].
      destruct (preservation_subset _ _ _ _ _ _ _ Htype0 H) as [kap' [Htype' Hsub]].
      simpl in *.
      apply Hsub. eapply (IHHmulti _ _ _ _ eq_refl _ _ Htype'); eauto.
Qed.

(** Helper: multi-step with pure typing propagation. *)
Lemma pure_multi_no_new_gov :
  forall c c',
    multi_step c c' ->
    (exists T, has_type nil (cfg_term c) T cap_empty) ->
    forall k d r, In (LGov k d r) (cfg_trace c') -> In (LGov k d r) (cfg_trace c).
Proof.
  intros c c' Hmulti. induction Hmulti; intros [T0 Htype] k0 d0 r0 Hin.
  - exact Hin.
  - destruct c1 as [e1 ps1 l1 t1]. simpl in *.
    eapply pure_step_no_new_gov; eauto.
    apply IHHmulti; auto.
    exists T0. eapply preservation_pure; eauto.
Qed.

Corollary pure_no_governance :
  forall e T ps ledger tr c',
    has_type nil e T cap_empty ->
    multi_step (mk_config e ps ledger tr) c' ->
    forall k d r,
      ~ In (LGov k d r) (cfg_trace c') \/
      In (LGov k d r) tr.
Proof.
  intros e T ps ledger tr c' Htype Hmulti k d r.
  destruct (In_dec label_eq_dec (LGov k d r) (cfg_trace c')) as [Hin | Hnotin].
  - right. apply (pure_multi_no_new_gov _ _ Hmulti (ex_intro _ T Htype) _ _ _ Hin).
  - left. exact Hnotin.
Qed.

Lemma pure_multi_preserves_ledger :
  forall c c',
    multi_step c c' ->
    (exists T, has_type nil (cfg_term c) T cap_empty) ->
    cfg_ledger c' = cfg_ledger c.
Proof.
  intros c c' Hmulti. induction Hmulti; intros [T0 Htype].
  - reflexivity.
  - destruct c1 as [e1 ps1 l1 t1]. simpl in *.
    transitivity (cfg_ledger c2).
    + apply IHHmulti. exists T0. eapply preservation_pure; eauto.
    + eapply pure_step_preserves_ledger; eauto.
Qed.

Corollary pure_preserves_ledger :
  forall e T ps ledger tr c',
    has_type nil e T cap_empty ->
    multi_step (mk_config e ps ledger tr) c' ->
    cfg_ledger c' = ledger.
Proof.
  intros e T ps ledger tr c' Htype Hmulti.
  change ledger with (cfg_ledger (mk_config e ps ledger tr)).
  apply (pure_multi_preserves_ledger _ _ Hmulti (ex_intro _ T Htype)).
Qed.
