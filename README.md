# Mechanized Foundations of Structural Governance

[![Build Coq Proofs](https://github.com/mashin-live/governance-proofs/actions/workflows/build.yml/badge.svg)](https://github.com/mashin-live/governance-proofs/actions/workflows/build.yml)

Coq formalization of the core theorems from:

- McCann, A.L. "The Two Boundaries: Why Behavioral AI Governance Fails Structurally." arXiv preprint, 2026.
- McCann, A.L. "Mechanized Foundations of Structural Governance: Machine-Checked Proofs for Governed Intelligence." arXiv preprint, 2026.
- McCann, A.L. "Effect-Transparent Governance for AI Workflow Architectures." arXiv preprint, 2026.
- McCann, A.L. "Algebraic Semantics of Governed Execution: Monoidal Categories, Effect Algebras, and Coterminous Boundaries." arXiv preprint, 2026.
- McCann, A.L. "Certified Purity for Cognitive Workflow Executors." arXiv preprint, 2026.
- McCann, A.L. "Cryptographic Registry Provenance: Structural Defense Against Dependency Confusion in AI Package Ecosystems." arXiv preprint, 2026.

Uses the Interaction Trees library to model programs as coinductive trees of
events, the governance pipeline as a handler transformer, and the four
primitives as specific event patterns.

## Summary

- **32 modules**, approximately 12,000 lines of Coq, **548 theorems**
- **Zero admitted lemmas** (every theorem fully proved)
- **Coq 8.19.2** with Interaction Trees 5.2.1, paco 4.2.3, ExtLib 0.13.0
- Capstone: **Governed Cognitive Completeness** theorem combining six properties in one result

## What Is Proved

### Governance Safety

| Theorem | File | What It Says |
|---------|------|-------------|
| Directive functor + free monad | `Directives.v` | Programs are interaction trees over directive events |
| Governance pipeline composition | `Governance.v` | The Gov operator wraps every handler with pre/post governance |
| Naturality of governed interpretation | `Interpreter.v` | Governance distributes over composition (transparent to program structure) |
| Gov endofunctor + functor laws | `Functor.v` | Gov preserves handler equivalence and satisfies functor laws |
| Safety (`gov_safe`) | `Safety.v` | **No governed program can execute I/O without passing through governance.** Coinductive proof: 213 lines, nested pcofix, provably FALSE for bare I/O, TRUE for governed interpretation |
| Convergence + fixed point | `Convergence.v` | Governance at level N+1 = governance at level N. The tower converges immediately |

### Expressive Completeness

| Theorem | File | What It Says |
|---------|------|-------------|
| Category Mashin (Kleisli category) | `Category.v` | The four primitives form a category: identity, associativity, composition all verified |
| Primitive classification | `Category.v` | code = Ret-terminated trees, reason = LLMCall trigger, memory = MemoryOp trigger, call = CallMachine trigger |
| Compositional closure | `Category.v` | Sequential, branching, iteration all produce valid morphisms |
| **Governance safety of all compositions** | `Category.v` | Every morphism built from the four primitives, when interpreted via Gov, satisfies gov_safe |
| Register machine encoding | `Completeness.v` | Register machine instructions map to memory + code + call primitives |
| Simulation correctness | `Completeness.v` | Pure denotation of translation equals reference register machine interpreter (`simulation_correct`) |
| Behavioral equivalence | `Completeness.v` | Under abstract handler hypotheses, ITree translation faithful to rm_run (`translation_faithful`) |
| Turing completeness | `Completeness.v` | The translation is constructive: exhibit the simulation as interaction trees |
| **Governed Turing completeness** | `Completeness.v` | All translated register machine programs satisfy gov_safe. Turing-complete AND governed. |

### Verified Interpreter Specification

| Theorem | File | What It Says |
|---------|------|-------------|
| Trust level specification | `TrustSpec.v` | Trust level ordering, promotion rules, and capability derivation |
| Hash chain specification | `HashChainSpec.v` | Cryptographic hash chain integrity, append-only property, tamper detection |
| Interpreter specification | `InterpreterSpec.v` | Directive interpreter correctness against the formal governance model |

The interpreter specification was tested with property-based testing: 70,000+ random directive sequences with zero disagreements between the Coq specification and the production BEAM runtime. This testing discovered a latent capability-tree bug (on the 188th random input).

### Governed Cognitive Completeness (Capstone)

| Theorem | File | What It Says |
|---------|------|-------------|
| Structural subsumes content | `Subsumption.v` | Any handler composed with Gov satisfies gov_safe, regardless of content filtering |
| Content does not subsume structural | `Subsumption.v` | Direct I/O access is NOT gov_safe, regardless of content governance |
| Subsumption asymmetry | `Subsumption.v` | Structural governance strictly subsumes content governance (one direction only) |
| Cognitive surjection | `CognitiveArchitecture.v` | Every cognitive capability (Compute, Remember, Reason, Act, Observe) is realized by a Mashin primitive |
| Primitive essentiality | `CognitiveArchitecture.v` | Each primitive emits a unique event type; removing any loses a capability |
| Oracle completeness | `Oracle.v` | Oracle register machine programs (with LLM queries) satisfy gov_safe when interpreted through Gov |
| Oracle extends Turing | `Oracle.v` | Programs with O_QUERY emit LLMCall events, strictly beyond the {code, memory, call} subset |
| Goal reachability preservation | `GoalDirected.v` | If a program reaches a goal under ungoverned interpretation, the goal value exists |
| Conservative denial | `GoalDirected.v` | Governance denial (spin) never produces incorrect results; it produces no results |
| Decidability boundary | `Rice.v` | Structural properties (capability checks) are decidable; semantic properties (halting) are non-trivial |
| Halting non-triviality | `Rice.v` | Some programs halt, some don't; halting is not constant-true or constant-false |
| **Governed Cognitive Completeness** | `GovernedCognitiveCompleteness.v` | **A single architecture simultaneously achieves Turing completeness, oracle integration, decidability self-awareness, goal reachability, cognitive architecture completeness, and subsumption of content governance. All governed.** |

## Setup

### Prerequisites

```bash
# Install opam (OCaml package manager)
brew install opam    # macOS
# apt install opam   # Ubuntu/Debian
opam init
eval $(opam env)

# Create a switch for Coq 8.19
opam switch create coq-8.19 ocaml-base-compiler.4.14.2
eval $(opam env --switch=coq-8.19)

# Install Coq and dependencies
opam pin add coq 8.19.2
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-itree coq-paco coq-ext-lib
```

### Build

```bash
eval $(opam env --switch=coq-8.19)
make
```

Expected output: each `.v` file compiles without errors. No warnings except
notation overrides (suppressed by `_CoqProject` flags).

### Clean

```bash
make clean
```

## Project Structure

```
theories/
  Prelude.v                        -- Common imports: ITree, ExtLib, Coq stdlib
  Directives.v                     -- DirectiveE event type (14 constructors), response types
  Governance.v                     -- Gov operator, pre/post governance, handler types
  Interpreter.v                    -- Naturality, governance transparency
  Functor.v                        -- Gov endofunctor, handler equivalence, functor laws
  Safety.v                         -- gov_safe coinductive predicate, main safety theorem
  Convergence.v                    -- Governance levels, convergence by induction, fixed point
  Category.v                       -- Category Mashin, four primitives, closure, governance safety
  Completeness.v                   -- Register machine encoding, Turing completeness
  TrustSpec.v                      -- Trust level model: ordering, promotion, capability derivation
  HashChainSpec.v                  -- Hash chain integrity: append-only, tamper detection
  InterpreterSpec.v                -- Directive interpreter: formal spec matching runtime
  Subsumption.v                    -- Structural/content governance asymmetry
  CognitiveArchitecture.v         -- Cognitive capability surjection, primitive essentiality
  Oracle.v                         -- Oracle register machines, LLM-augmented completeness
  GoalDirected.v                   -- Goal reachability preservation, conservative denial
  Rice.v                           -- Decidability boundary (Law 4), halting non-triviality
  GovernedCognitiveCompleteness.v -- Capstone: six properties in one theorem
  Transparency.v                  -- Semantic transparency of permissive governance
  ExpressiveMinimality.v          -- Minimality of the four-primitive set
  GovernanceAlgebra.v             -- Governance algebra record, five axioms, instantiation
  MonoidalCategory.v              -- Symmetric monoidal category, coherence, Gov distributes
  EffectAlgebra.v                 -- Capability sets, effect rows, No Ambient Effects theorem
  EffectHandlers.v                -- Governed handler algebra, capability-bounded handlers
  CapabilityComposition.v         -- Capability-indexed composition, trust lattice, dual guarantee
  TraceSemantics.v                -- Execution traces, trace_of relation, trace_of_bind
  LedgerConnection.v              -- Traces to hash chains, tamper evidence, ledger completeness
  CoterminousBoundary.v           -- Expressiveness = governance boundary, algebraic capstone
  TemporalPolicyEvolution.v       -- Policy changes governed, safety preservation, rollback
  Extraction.v                    -- Coq-to-OCaml extraction directives
```

## Key Technical Ideas

### Interaction Trees (ITrees)

Programs are represented as coinductive trees:
- `Ret v`: pure value, no effects
- `Tau t`: silent computational step, then continue with `t`
- `Vis e k`: visible event `e`, then continue with `k(response)`

The governance pipeline transforms a tree of directive events into a tree of
governed events, wrapping each visible event with pre-governance checks
(TrustCheck, PermissionCheck, PhaseValidation, PreHooks) and post-governance
recording (Guardrails, ProvenanceRecord, EventBroadcast).

### Coinduction via paco

Programs run forever. Governance must hold forever. You cannot prove
properties about infinite behaviors with ordinary induction.

Coinduction works in the opposite direction: prove a property holds for one
step, then show that holding-for-one-step implies holding-for-the-next-step.
The `paco` library (parameterized coinduction) provides the proof framework.

### Category Mashin as Kleisli Category

Category Mashin is the Kleisli category of the `itree DirectiveE` monad:
- **Objects**: Types (context types in the paper)
- **Morphisms**: Kleisli arrows `A -> itree DirectiveE B`
- **Composition**: monadic bind (`ITree.bind`)
- **Identity**: monadic return (`Ret`)

The category axioms are the monad laws, already proved in the ITrees library:
- Left identity: `bind (ret x) k ≅ k x`
- Right identity: `bind t ret ≅ t`
- Associativity: `bind (bind t k1) k2 ≅ bind t (fun x => bind (k1 x) k2)`

### The Safety Predicate (`gov_safe`)

A coinductive predicate indexed by a boolean permission flag:
- `gov_safe false t`: tree `t` never does bare I/O without governance
- `gov_safe true t`: tree `t` is allowed to do I/O (governance already checked)

Governance events (`GovCheck`) flip the flag from `false` to `true`.
I/O events require `true`. The predicate is:
- **Provably FALSE** for bare I/O (`bare_io_not_safe`)
- **Provably TRUE** for governed interpretations (`governed_interp_safe`)

This non-triviality is the mathematical content of structural governance.

### Register Machine Simulation

A register machine (counter machine) is Turing-equivalent. The encoding:
- **Registers** -> memory operations (MemoryOp with MemStore/MemRecall)
- **Arithmetic** -> pure computation (code morphisms)
- **Branch on zero** -> case analysis (branch combinator)
- **Instruction jump** -> recursive program structure (call primitive)

Since register machines are Turing-complete (Minsky, 1967), and the
translation produces interaction trees over DirectiveE, the primitive
subset {code, memory, call} is Turing-complete.

The key additional result: all translated programs satisfy `gov_safe`.
Turing completeness is achieved *within* the governed architecture.

## References

- Xia et al., "Interaction Trees: Representing Recursive and Impure Programs
  in Coq", POPL 2020
- Zakowski et al., "An Interaction Tree Approach to Verified Compilation",
  Vellvm project (ICFP 2021)
- Minsky, "Computation: Finite and Infinite Machines", 1967 (register machines)
- Mac Lane, "Categories for the Working Mathematician", 1971
- Hur et al., "The Power of Parameterization in Coinductive Proof", POPL 2013

## License

MIT. See [LICENSE](LICENSE).
