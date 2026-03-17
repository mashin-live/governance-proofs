(** * MonoidalCategory: Symmetric Monoidal Structure on Category Mashin

    Extends Category.v with:
    - Monoidal product (tensor of morphisms via bind)
    - Unit object (unit type)
    - Structural morphisms (associator, unitors, braiding)
    - Isomorphism proofs (round-trip)
    - Coherence conditions (pentagon, triangle, hexagon)
    - Governance safety of all tensor compositions

    The tensor product is defined as sequential-independent
    composition: f ⊗ g runs f then g with no shared state.
    Since the structural morphisms (α, λ, ρ, σ) are all pure
    (no effects), coherence conditions hold by computation.

    Dependencies: Prelude, Directives, Governance, Safety,
                  Category, GovernanceAlgebra *)

From MashinGov Require Import Prelude.
From MashinGov Require Import Directives.
From MashinGov Require Import Governance.
From MashinGov Require Import Safety.
From MashinGov Require Import Category.
From MashinGov Require Import GovernanceAlgebra.

From ITree Require Import
  Interp.InterpFacts
  Eq.EqAxiom.

From Paco Require Import paco.

(* ================================================================= *)
(* Monoidal Product                                                    *)
(* ================================================================= *)

(** ** Tensor Product of Morphisms

    Given f : A -> B and g : C -> D in Category Mashin,
    f ⊗ g : (A * C) -> (B * D) runs f then g and pairs results.

    This is sequential-independent: f's effects complete before
    g's effects begin. The two computations share no state.
    True concurrent interleaving would require a more complex
    construction; we note this as future work. *)

Definition mashin_tensor {A B C D : Type}
  (f : mashin_morphism A B) (g : mashin_morphism C D)
  : mashin_morphism (A * C) (B * D) :=
  fun p =>
    let (a, c) := p in
    ITree.bind (f a) (fun b => ITree.bind (g c) (fun d => ret (b, d))).

Notation "f ⊗ g" := (mashin_tensor f g) (at level 40, left associativity).

(** ** Bifunctor Identity Law

    id ⊗ id = id

    The tensor of two identities is the identity on pairs. *)

Lemma tensor_id :
  forall (A C : Type) (p : A * C),
    eutt eq ((mashin_id ⊗ mashin_id) p) (mashin_id p).
Proof.
  intros A C [a c].
  unfold mashin_tensor, mashin_id, ret, Monad_itree.
  rewrite bind_ret_l. rewrite bind_ret_l.
  reflexivity.
Qed.

(** ** Tensor of Pure Morphisms Is Pure

    code_morphism f ⊗ code_morphism g = code_morphism (fun (a,c) => (f a, g c))

    This means the pure fragment is closed under tensor. *)

Lemma tensor_pure :
  forall (A B C D : Type) (f : A -> B) (g : C -> D) (p : A * C),
    eutt eq ((code_morphism f ⊗ code_morphism g) p)
            (code_morphism (fun q : A * C => let (a, c) := q in (f a, g c)) p).
Proof.
  intros A B C D f g [a c].
  unfold mashin_tensor, code_morphism, ret, Monad_itree.
  rewrite bind_ret_l. rewrite bind_ret_l.
  reflexivity.
Qed.

(* ================================================================= *)
(* Unit Object                                                         *)
(* ================================================================= *)

(** The unit object in the monoidal category is [unit].
    I ⊗ A ≅ A ≅ A ⊗ I via the unitors below. *)

(* ================================================================= *)
(* Structural Morphisms                                                *)
(* ================================================================= *)

(** ** Associator

    α : (A ⊗ B) ⊗ C -> A ⊗ (B ⊗ C)

    Pure re-association of nested pairs. No effects. *)

Definition mashin_assoc {A B C : Type}
  : mashin_morphism ((A * B) * C) (A * (B * C)) :=
  fun p => let (ab, c) := p in let (a, b) := ab in ret (a, (b, c)).

Definition mashin_assoc_inv {A B C : Type}
  : mashin_morphism (A * (B * C)) ((A * B) * C) :=
  fun p => let (a, bc) := p in let (b, c) := bc in ret ((a, b), c).

(** ** Left Unitor

    λ : I ⊗ A -> A *)

Definition mashin_lunit {A : Type}
  : mashin_morphism (unit * A) A :=
  fun p => let (_, a) := p in ret a.

Definition mashin_lunit_inv {A : Type}
  : mashin_morphism A (unit * A) :=
  fun a => ret (tt, a).

(** ** Right Unitor

    ρ : A ⊗ I -> A *)

Definition mashin_runit {A : Type}
  : mashin_morphism (A * unit) A :=
  fun p => let (a, _) := p in ret a.

Definition mashin_runit_inv {A : Type}
  : mashin_morphism A (A * unit) :=
  fun a => ret (a, tt).

(** ** Braiding (Symmetry)

    σ : A ⊗ B -> B ⊗ A *)

Definition mashin_braid {A B : Type}
  : mashin_morphism (A * B) (B * A) :=
  fun p => let (a, b) := p in ret (b, a).

(* ================================================================= *)
(* Isomorphism Proofs                                                  *)
(* ================================================================= *)

(** The structural morphisms are isomorphisms:
    composing a morphism with its inverse yields identity. *)

Section Isomorphisms.

  (** Associator round-trip *)
  Lemma assoc_iso_lr :
    forall (A B C : Type) (p : (A * B) * C),
      eutt eq ((mashin_assoc >>> mashin_assoc_inv) p) (mashin_id p).
  Proof.
    intros A B C [[a b] c].
    unfold mashin_compose, mashin_assoc, mashin_assoc_inv, mashin_id.
    unfold ret, Monad_itree. rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma assoc_iso_rl :
    forall (A B C : Type) (p : A * (B * C)),
      eutt eq ((mashin_assoc_inv >>> mashin_assoc) p) (mashin_id p).
  Proof.
    intros A B C [a [b c]].
    unfold mashin_compose, mashin_assoc, mashin_assoc_inv, mashin_id.
    unfold ret, Monad_itree. rewrite bind_ret_l. reflexivity.
  Qed.

  (** Left unitor round-trip *)
  Lemma lunit_iso_lr :
    forall (A : Type) (p : unit * A),
      eutt eq ((mashin_lunit >>> mashin_lunit_inv) p) (mashin_id p).
  Proof.
    intros A [[] a].
    unfold mashin_compose, mashin_lunit, mashin_lunit_inv, mashin_id.
    unfold ret, Monad_itree. rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma lunit_iso_rl :
    forall (A : Type) (a : A),
      eutt eq ((mashin_lunit_inv >>> mashin_lunit) a) (mashin_id a).
  Proof.
    intros A a.
    unfold mashin_compose, mashin_lunit, mashin_lunit_inv, mashin_id.
    unfold ret, Monad_itree. rewrite bind_ret_l. reflexivity.
  Qed.

  (** Right unitor round-trip *)
  Lemma runit_iso_lr :
    forall (A : Type) (p : A * unit),
      eutt eq ((mashin_runit >>> mashin_runit_inv) p) (mashin_id p).
  Proof.
    intros A [a []].
    unfold mashin_compose, mashin_runit, mashin_runit_inv, mashin_id.
    unfold ret, Monad_itree. rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma runit_iso_rl :
    forall (A : Type) (a : A),
      eutt eq ((mashin_runit_inv >>> mashin_runit) a) (mashin_id a).
  Proof.
    intros A a.
    unfold mashin_compose, mashin_runit, mashin_runit_inv, mashin_id.
    unfold ret, Monad_itree. rewrite bind_ret_l. reflexivity.
  Qed.

  (** Braiding is self-inverse *)
  Lemma braid_iso :
    forall (A B : Type) (p : A * B),
      eutt eq ((mashin_braid >>> mashin_braid) p) (mashin_id p).
  Proof.
    intros A B [a b].
    unfold mashin_compose, mashin_braid, mashin_id.
    unfold ret, Monad_itree. rewrite bind_ret_l. reflexivity.
  Qed.

End Isomorphisms.

(* ================================================================= *)
(* Coherence Conditions                                                *)
(* ================================================================= *)

(** ** Pentagon Diagram

    ((A ⊗ B) ⊗ C) ⊗ D
          |                            \
      α ⊗ id                        α
          |                            \
    (A ⊗ (B ⊗ C)) ⊗ D         (A ⊗ B) ⊗ (C ⊗ D)
          |                            |
          α                            α
          |                            |
    A ⊗ ((B ⊗ C) ⊗ D)         A ⊗ (B ⊗ (C ⊗ D))
          |                        /
        id ⊗ α                /
          |                 /
    A ⊗ (B ⊗ (C ⊗ D))

    Both paths from top-left to bottom yield the same morphism. *)

Theorem pentagon :
  forall (A B C D : Type)
    (p : ((A * B) * C) * D),
    eutt eq
      (((mashin_assoc ⊗ mashin_id) >>> mashin_assoc >>> (mashin_id ⊗ mashin_assoc)) p)
      ((mashin_assoc >>> mashin_assoc) p).
Proof.
  intros A B C D [[[a b] c] d].
  unfold mashin_compose, mashin_tensor, mashin_assoc, mashin_id.
  unfold ret, Monad_itree.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.

(** ** Triangle Diagram

    (A ⊗ I) ⊗ B ---α---> A ⊗ (I ⊗ B)
         |                      |
      ρ ⊗ id              id ⊗ λ
         |                      |
       A ⊗ B ============ A ⊗ B *)

Theorem triangle :
  forall (A B : Type)
    (p : (A * unit) * B),
    eutt eq
      ((mashin_assoc >>> (mashin_id ⊗ mashin_lunit)) p)
      ((mashin_runit ⊗ mashin_id) p).
Proof.
  intros A B [[a []] b].
  unfold mashin_compose, mashin_tensor, mashin_assoc, mashin_id.
  unfold mashin_lunit, mashin_runit.
  unfold ret, Monad_itree.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.

(** ** Hexagon Diagram (Braiding Coherence)

    (A ⊗ B) ⊗ C ---α---> A ⊗ (B ⊗ C) ---σ---> (B ⊗ C) ⊗ A
         |                                           |
      σ ⊗ id                                       α
         |                                           |
    (B ⊗ A) ⊗ C ---α---> B ⊗ (A ⊗ C) --id ⊗ σ--> B ⊗ (C ⊗ A) *)

Theorem hexagon :
  forall (A B C : Type)
    (p : (A * B) * C),
    eutt eq
      ((mashin_assoc >>> mashin_braid >>> mashin_assoc) p)
      (((mashin_braid ⊗ mashin_id) >>> mashin_assoc >>> (mashin_id ⊗ mashin_braid)) p).
Proof.
  intros A B C [[a b] c].
  unfold mashin_compose, mashin_tensor, mashin_assoc, mashin_braid, mashin_id.
  unfold ret, Monad_itree.
  repeat rewrite bind_ret_l.
  reflexivity.
Qed.

(* ================================================================= *)
(* Governance Safety of Tensor Compositions                            *)
(* ================================================================= *)

(** ** All Tensor Compositions Are Governed

    Any morphism built from tensor, sequential composition,
    structural morphisms, and primitives produces a governed
    interpretation. This follows from [governed_interp_safe]:
    every such morphism outputs an [itree DirectiveE R]. *)

Section TensorGovernance.

  Variable h : base_handler.

  (** Tensor of governed morphisms is governed. *)
  Theorem tensor_governed :
    forall (A B C D : Type)
      (f : mashin_morphism A B) (g : mashin_morphism C D)
      (p : A * C),
      @gov_safe (B * D) false (interp (Gov h) ((f ⊗ g) p)).
  Proof.
    intros. apply governed_interp_safe.
  Qed.

  (** Associator is governed. *)
  Corollary assoc_governed :
    forall (A B C : Type) (p : (A * B) * C),
      @gov_safe (A * (B * C)) false (interp (Gov h) (mashin_assoc p)).
  Proof.
    intros. apply governed_interp_safe.
  Qed.

  (** Braiding is governed. *)
  Corollary braid_governed :
    forall (A B : Type) (p : A * B),
      @gov_safe (B * A) false (interp (Gov h) (mashin_braid p)).
  Proof.
    intros. apply governed_interp_safe.
  Qed.

  (** All structural morphisms composed with tensor are governed. *)
  Theorem monoidal_composition_governed :
    forall (A B : Type) (f : mashin_morphism A B) (a : A),
      @gov_safe B false (interp (Gov h) (f a)).
  Proof.
    intros. apply governed_interp_safe.
  Qed.

End TensorGovernance.

(** ** Governance Distributes Over Tensor (for the GovernanceAlgebra)

    For any GovernanceAlgebra instance, tensor compositions
    are governed. This is the abstract form. *)

Theorem ga_tensor_governed :
  forall (G : GovernanceAlgebra) (A B C D : Type)
    (f : mashin_morphism A B) (g : mashin_morphism C D)
    (h : base_handler) (p : A * C),
    @gov_safe (B * D) false (interp (ga_Gov G h) ((f ⊗ g) p)).
Proof.
  intros. apply (ga_safe G).
Qed.

(* ================================================================= *)
(* Interpretation Distributes Over Tensor                              *)
(* ================================================================= *)

(** ** Tensor-Interp Distribution

    interp (Gov h) ((f ⊗ g) (a, c))
    ≈
    bind (interp (Gov h) (f a)) (fun b =>
    bind (interp (Gov h) (g c)) (fun d =>
    ret (b, d)))

    This follows from interp_bind (interp distributes over bind).
    The governed interpretation of a tensor product decomposes into
    the governed interpretations of the components. Governance of
    the whole follows from governance of the parts. *)

Theorem interp_tensor_distribute :
  forall (h : base_handler) (A B C D : Type)
    (f : mashin_morphism A B) (g : mashin_morphism C D)
    (a : A) (c : C),
    eq_itree eq
      (interp (Gov h) ((f ⊗ g) (a, c)))
      (ITree.bind (interp (Gov h) (f a))
                   (fun b => interp (Gov h)
                     (ITree.bind (g c) (fun d => ret (b, d))))).
Proof.
  intros h A B C D f g a c.
  unfold mashin_tensor.
  apply interp_bind.
Qed.

(* ================================================================= *)
(* Summary                                                             *)
(* ================================================================= *)

(** ** Summary

    Category Mashin is a symmetric monoidal category:

    | Structure           | Definition                       |
    |---------------------|----------------------------------|
    | Objects             | Types (A, B, C, ...)             |
    | Morphisms           | A -> itree DirectiveE B          |
    | Identity            | ret                              |
    | Composition (∘)     | Kleisli bind                     |
    | Tensor (⊗)          | Sequential-independent bind      |
    | Unit (I)            | unit                             |
    | Associator (α)      | Pure pair re-association         |
    | Left unitor (λ)     | Pure pair projection             |
    | Right unitor (ρ)    | Pure pair projection             |
    | Braiding (σ)        | Pure pair swap                   |

    Coherence conditions verified:

    | Condition    | Theorem        |
    |--------------|----------------|
    | Pentagon     | [pentagon]     |
    | Triangle     | [triangle]     |
    | Hexagon      | [hexagon]      |

    Isomorphisms verified: associator, both unitors, braiding.

    Governance safety: all tensor compositions are governed
    (for the concrete [Gov] and for any [GovernanceAlgebra]).

    Compositional property: [interp_tensor_distribute] shows
    governance of tensor products decomposes into governance of
    components. *)
