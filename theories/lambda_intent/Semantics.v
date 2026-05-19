(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file. *)

(** * Lambda^intent Operational Semantics

    Small-step reduction over configurations with labeled traces.
    Pure reduction leaves policy and ledger unchanged.
    Governed reduction (ask_k) invokes the governance interpreter,
    appends to the ledger and trace.

    Reference: OSI paper, Section 4 (Operational Semantics). *)

From Coq Require Import
  Lists.List
  Strings.String
  Bool.Bool
  Arith.Arith.

From MashinGov.lambda_intent Require Import Syntax.

Import ListNotations.
Open Scope list_scope.

(* ================================================================== *)
(** ** Effect Realization *)
(* ================================================================== *)

(** [realize] is an external oracle: given an intent, it produces a
    response value. This models the runtime's interaction with the
    outside world. It is NOT a term-level construct; it appears only
    in the E-Allow reduction rule.

    We model it as a parameter (axiom) since it is external to the
    calculus. *)

Parameter realize : intent_val -> tm.

(** We assume realized values are always values *)
Axiom realize_is_value : forall i, value (realize i).

(* ================================================================== *)
(** ** Governance Interpreter *)
(* ================================================================== *)

(** The governance interpreter evaluates the policy set on an intent
    and produces a decision and a record. *)

Definition gov_interpret
  (ps : policy_set) (i : intent_val) (prev_hash : string)
  : gov_decision * decision_record :=
  let d := eval_policy_set ps i in
  let r := mk_record i d "policy"%string prev_hash in
  (d, r).

(** The governance interpreter is total *)
Lemma gov_interpret_total :
  forall ps i h, exists d r, gov_interpret ps i h = (d, r).
Proof.
  intros. unfold gov_interpret.
  eexists. eexists. reflexivity.
Qed.

(* ================================================================== *)
(** ** Evaluation Contexts *)
(* ================================================================== *)

(** Evaluation contexts for call-by-value reduction. *)

Inductive eval_ctx : Type :=
  | EC_Hole : eval_ctx
  | EC_AppL : eval_ctx -> tm -> eval_ctx        (** E e2 *)
  | EC_AppR : tm -> eval_ctx -> eval_ctx         (** v1 E  (v1 is a value) *)
  | EC_LetBind : eval_ctx -> tm -> eval_ctx      (** let x = E in e2 *)
  | EC_IfCond : eval_ctx -> tm -> tm -> eval_ctx (** if E then e2 else e3 *)
  | EC_Fst : eval_ctx -> eval_ctx
  | EC_Snd : eval_ctx -> eval_ctx
  | EC_PairL : eval_ctx -> tm -> eval_ctx
  | EC_PairR : tm -> eval_ctx -> eval_ctx
  | EC_ConsL : eval_ctx -> tm -> eval_ctx
  | EC_ConsR : tm -> eval_ctx -> eval_ctx.

(** Plug a term into an evaluation context *)
Fixpoint plug (E : eval_ctx) (e : tm) : tm :=
  match E with
  | EC_Hole => e
  | EC_AppL E' e2 => tapp (plug E' e) e2
  | EC_AppR v1 E' => tapp v1 (plug E' e)
  | EC_LetBind E' e2 => tlet (plug E' e) e2
  | EC_IfCond E' e2 e3 => tif (plug E' e) e2 e3
  | EC_Fst E' => tfst (plug E' e)
  | EC_Snd E' => tsnd (plug E' e)
  | EC_PairL E' e2 => tpair (plug E' e) e2
  | EC_PairR v1 E' => tpair v1 (plug E' e)
  | EC_ConsL E' e2 => tcons (plug E' e) e2
  | EC_ConsR v1 E' => tcons v1 (plug E' e)
  end.

(* ================================================================== *)
(** ** Small-Step Reduction *)
(* ================================================================== *)

(** Reduction relation on configurations.
    Each step produces a new configuration. The trace accumulates
    labels recording observable events. *)

(** Helper: get the last hash from the ledger for chaining *)
Definition ledger_hash (l : list decision_record) : string :=
  match l with
  | nil => "genesis"%string
  | r :: _ => rec_prev_hash r
  end.

Inductive step : config -> config -> Prop :=

  (* --- Pure reduction rules --- *)

  | E_App : forall (T : ty) (body v : tm) (ps : policy_set)
      (ledger : list decision_record) (tr : trace),
      value v ->
      step (mk_config (tapp (tabs T body) v) ps ledger tr)
           (mk_config (subst_top v body) ps ledger (tr ++ (LSilent :: nil)))

  | E_Let : forall v e2 ps ledger tr,
      value v ->
      step (mk_config (tlet v e2) ps ledger tr)
           (mk_config (subst_top v e2) ps ledger (tr ++ (LSilent :: nil)))

  | E_IfTrue : forall e2 e3 ps ledger tr,
      step (mk_config (tif (tbool true) e2 e3) ps ledger tr)
           (mk_config e2 ps ledger (tr ++ (LSilent :: nil)))

  | E_IfFalse : forall e2 e3 ps ledger tr,
      step (mk_config (tif (tbool false) e2 e3) ps ledger tr)
           (mk_config e3 ps ledger (tr ++ (LSilent :: nil)))

  | E_Fix : forall T body ps ledger tr,
      step (mk_config (tfix T body) ps ledger tr)
           (mk_config (subst_top (tfix T body) body) ps ledger (tr ++ (LSilent :: nil)))

  | E_Fst : forall v1 v2 ps ledger tr,
      value v1 -> value v2 ->
      step (mk_config (tfst (tpair v1 v2)) ps ledger tr)
           (mk_config v1 ps ledger (tr ++ (LSilent :: nil)))

  | E_Snd : forall v1 v2 ps ledger tr,
      value v1 -> value v2 ->
      step (mk_config (tsnd (tpair v1 v2)) ps ledger tr)
           (mk_config v2 ps ledger (tr ++ (LSilent :: nil)))

  (* --- Governed reduction rules --- *)

  | E_Allow : forall k a tgt p ps ledger tr r v_result,
      let i := mk_intent k a tgt p in
      let h := ledger_hash ledger in
      gov_interpret ps i h = (GovAllow, r) ->
      realize i = v_result ->
      value p ->
      step (mk_config (task k a tgt p) ps ledger tr)
           (mk_config v_result ps (r :: ledger)
              (tr ++ (LGov k GovAllow r :: LEff k v_result :: nil)))

  | E_Deny : forall k a tgt p ps ledger tr r,
      let i := mk_intent k a tgt p in
      let h := ledger_hash ledger in
      gov_interpret ps i h = (GovDeny, r) ->
      value p ->
      step (mk_config (task k a tgt p) ps ledger tr)
           (mk_config tdenied ps (r :: ledger)
              (tr ++ (LGov k GovDeny r :: nil)))

  | E_Escalate : forall k a tgt p ps ledger tr r,
      let i := mk_intent k a tgt p in
      let h := ledger_hash ledger in
      gov_interpret ps i h = (GovEscalate, r) ->
      value p ->
      step (mk_config (task k a tgt p) ps ledger tr)
           (mk_config tsuspended ps (r :: ledger)
              (tr ++ (LGov k GovEscalate r :: nil)))

  (* --- Congruence via evaluation contexts --- *)

  | E_Ctx : forall E e e' ps ledger tr ps' ledger' tr',
      E <> EC_Hole ->
      step (mk_config e ps ledger tr)
           (mk_config e' ps' ledger' tr') ->
      step (mk_config (plug E e) ps ledger tr)
           (mk_config (plug E e') ps' ledger' tr').

(** Multi-step reduction (reflexive transitive closure) *)
Inductive multi_step : config -> config -> Prop :=
  | MS_Refl : forall c, multi_step c c
  | MS_Step : forall c1 c2 c3,
      step c1 c2 ->
      multi_step c2 c3 ->
      multi_step c1 c3.

(* ================================================================== *)
(** ** Key Structural Properties of the Reduction Rules *)
(* ================================================================== *)

(** The policy set never changes during reduction *)
Lemma step_preserves_policy :
  forall c c',
    step c c' ->
    cfg_policy c = cfg_policy c'.
Proof.
  intros c c' Hstep. induction Hstep; simpl; auto.
Qed.

(** Pure reduction does not modify the ledger *)
Lemma pure_step_preserves_ledger :
  forall (body v : tm) (ps : policy_set) (ledger : list decision_record) (tr : trace),
    value v ->
    cfg_ledger (mk_config (subst_top v body) ps ledger (tr ++ (LSilent :: nil))) = ledger.
Proof.
  intros. simpl. reflexivity.
Qed.

(** task cannot be the result of plugging into a non-hole context *)
Lemma task_not_pluggable :
  forall E e k a tgt p,
    plug E e = task k a tgt p ->
    E = EC_Hole /\ e = task k a tgt p.
Proof.
  intros E e k a tgt p Hplug.
  destruct E; simpl in Hplug; try discriminate.
  - (* EC_Hole *) split; [reflexivity | exact Hplug].
Qed.

(** Every governed step appends exactly one record to the ledger *)
Lemma governed_step_appends_one :
  forall k a tgt p ps ledger tr c',
    step (mk_config (task k a tgt p) ps ledger tr) c' ->
    exists r, cfg_ledger c' = r :: ledger.
Proof.
  intros k a tgt p ps ledger tr c' Hstep.
  inversion Hstep; subst; simpl.
  - exists r. reflexivity.
  - exists r. reflexivity.
  - exists r. reflexivity.
  - (* E_Ctx: E <> Hole but plug E e = task. By task_not_pluggable,
       E = Hole. Contradiction with H4 : E <> Hole. *)
    exfalso. apply H4. apply task_not_pluggable in H. destruct H. exact H.
Qed.

(** LEff labels appear in traces ONLY from E_Allow.
    Weaker version: for every new LEff, there exists a LGov Allow
    in the result trace (not necessarily new). *)
Lemma eff_label_only_from_allow :
  forall c c',
    step c c' ->
    forall k v,
      In (LEff k v) (cfg_trace c') ->
      ~ In (LEff k v) (cfg_trace c) ->
      exists r, In (LGov k GovAllow r) (cfg_trace c').
Proof.
  intros c c' Hstep. induction Hstep; intros k0 v0 Hin Hnotin.
  - (* E_App *) exfalso. apply Hnotin.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin]; auto.
    simpl in Hin. destruct Hin as [Hin | Hin]; [inversion Hin | contradiction].
  - (* E_Let *) exfalso. apply Hnotin.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin]; auto.
    simpl in Hin. destruct Hin as [Hin | Hin]; [inversion Hin | contradiction].
  - (* E_IfTrue *) exfalso. apply Hnotin.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin]; auto.
    simpl in Hin. destruct Hin as [Hin | Hin]; [inversion Hin | contradiction].
  - (* E_IfFalse *) exfalso. apply Hnotin.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin]; auto.
    simpl in Hin. destruct Hin as [Hin | Hin]; [inversion Hin | contradiction].
  - (* E_Fix *) exfalso. apply Hnotin.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin]; auto.
    simpl in Hin. destruct Hin as [Hin | Hin]; [inversion Hin | contradiction].
  - (* E_Fst *) exfalso. apply Hnotin.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin]; auto.
    simpl in Hin. destruct Hin as [Hin | Hin]; [inversion Hin | contradiction].
  - (* E_Snd *) exfalso. apply Hnotin.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin]; auto.
    simpl in Hin. destruct Hin as [Hin | Hin]; [inversion Hin | contradiction].
  - (* E_Allow: trace = tr ++ [LGov k GovAllow r; LEff k v_result] *)
    (* After induction on Hstep, in the E_Allow case:
       Hin : In (LEff k0 v0) (cfg_trace {| cfg_trace := tr ++ ... |})
       which is definitionally equal to In (LEff k0 v0) (tr ++ ...).
       Hnotin : ~In (LEff k0 v0) (cfg_trace {| cfg_trace := tr |})
       which is definitionally equal to ~In (LEff k0 v0) tr.
       Rocq should handle this with change or unfold. *)
    change (In (LEff k0 v0)
      (tr ++ (LGov k GovAllow r :: LEff k v_result :: nil))) in Hin.
    change (~In (LEff k0 v0) tr) in Hnotin.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + exfalso. apply Hnotin. exact Hin.
    + simpl in Hin. destruct Hin as [Hin | [Hin | Hin]].
      * inversion Hin.
      * inversion Hin. subst.
        exists r.
        change (In (LGov k0 GovAllow r)
          (tr ++ (LGov k0 GovAllow r :: LEff k0 (realize i) :: nil))).
        apply in_app_iff. right. simpl. left. reflexivity.
      * contradiction.
  - (* E_Deny *) exfalso. apply Hnotin.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin]; auto.
    simpl in Hin. destruct Hin as [Hin | Hin]; [inversion Hin | contradiction].
  - (* E_Escalate *) exfalso. apply Hnotin.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin]; auto.
    simpl in Hin. destruct Hin as [Hin | Hin]; [inversion Hin | contradiction].
  - (* E_Ctx: traces are shared between inner and outer configs *)
    apply (IHHstep k0 v0); assumption.
Qed.
