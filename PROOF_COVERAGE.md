# Proof Coverage Summary

**As of:** April 2026
**Total:** 454 machine-checked theorems across 36 Rocq modules
**Admitted lemmas:** 0
**Build:** `eval $(opam env --switch=coq-8.19) && coqc -Q theories MashinGov theories/<Module>.v`

---

## Theorem Taxonomy

| Category | Count | Description | Key Files |
|----------|------:|-------------|-----------|
| **Safety** | 13 | All effects mediated by governance | Safety.v |
| **Capability** | 67 | Authorization correctness, trust ordering, capability composition | TrustSpec.v (20), CapabilityComposition.v (38), DirectiveTotality.v (9) |
| **Composition** | 26 | Governance preserved under composition, delegation non-escalation | CapabilityComposition.v (partial), DelegationNonEscalation.v (13), CoterminousBoundary.v (13) |
| **Ledger** | 35 | Hash chain integrity, ledger completeness, evolution events | HashChainSpec.v (6), LedgerCompleteness.v (18), LedgerConnection.v (11) |
| **Materialization** | 25 | No execution without governance, form purity | GovernedMetaprogramming.v (25) |
| **Effect algebra** | 41 | Capability sets, within_caps, effect handlers | EffectAlgebra.v (32), EffectHandlers.v (9) |
| **Cognitive architecture** | 36 | Step type completeness, goal-directed execution | CognitiveArchitecture.v (19), Completeness.v (16), GovernedCognitiveCompleteness.v (1) |
| **Decidability** | 17 | Rice's theorem application, expressive minimality | Rice.v (17) |
| **Expressive minimality** | 17 | Minimal directive vocabulary | ExpressiveMinimality.v (17) |
| **Category theory** | 43 | Monoidal category coherence, functors | MonoidalCategory.v (18), Category.v (13), Functor.v (12) |
| **Governance algebra** | 12 | Algebraic structure of governance | GovernanceAlgebra.v (12) |
| **Network** | 15 | Cross-boundary governance | NetworkGovernance.v (15) |
| **Trace semantics** | 15 | Execution traces, well-governed traces | TraceSemantics.v (15) |
| **Temporal** | 14 | Policy evolution over time | TemporalPolicyEvolution.v (14) |
| **Source correspondence** | 17 | Target behavioral model, parsing, localization, serialization | SourceTraceCorrespondence.v (17) |
| **Subsumption** | 9 | Structural subsumes content governance | Subsumption.v (9) |
| **Oracle** | 7 | Oracle-parameterized execution | Oracle.v (7) |
| **Transparency** | 7 | Semantic transparency under governance | Transparency.v (7) |
| **Convergence** | 6 | Fixed-point convergence | Convergence.v (6) |
| **Goal-directed** | 8 | Goal reachability | GoalDirected.v (8) |
| **Interpreter** | 4 | Concrete interpreter model | Interpreter.v (4) |
| **Auxiliary** | 0 | Definitions, extraction directives | Prelude.v, Directives.v, Governance.v, Extraction.v |

---

## Module List (36 files)

| Module | Theorems | Role |
|--------|----------|------|
| CapabilityComposition.v | 38 | Trust lattice, capability morphisms, composition bounds |
| EffectAlgebra.v | 32 | Capability sets, within_caps, no ambient effects |
| GovernedMetaprogramming.v | 25 | Form safety, materialization governance |
| TrustSpec.v | 20 | Capability-directive mapping, trust levels |
| InterpreterSpec.v | 20 | Functional interpreter, bridge theorems |
| CognitiveArchitecture.v | 19 | Five cognitive primitives, essentiality |
| MonoidalCategory.v | 18 | Pentagon, triangle, hexagon coherence |
| LedgerCompleteness.v | 18 | Ledger events, chain integrity, evolution |
| SourceTraceCorrespondence.v | 17 | Target model, parsing, localization, registry |
| Rice.v | 17 | Undecidability, governance motivation |
| ExpressiveMinimality.v | 17 | Minimal directive vocabulary |
| Completeness.v | 16 | Turing completeness under governance |
| TraceSemantics.v | 15 | Trace events, well-governed traces |
| NetworkGovernance.v | 15 | Cross-boundary, relay governance |
| TemporalPolicyEvolution.v | 14 | Policy changes, monotonicity |
| Safety.v | 13 | gov_safe, governed_interp_safe |
| DelegationNonEscalation.v | 13 | Capability ceiling, chained delegation |
| CoterminousBoundary.v | 13 | E = G within behavioral model |
| Category.v | 13 | Category axioms |
| GovernanceAlgebra.v | 12 | Algebraic governance structure |
| Functor.v | 12 | Functorial composition |
| LedgerConnection.v | 11 | Ledger-interpreter connection |
| Subsumption.v | 9 | Structural > content governance |
| EffectHandlers.v | 9 | Handler composition |
| DirectiveTotality.v | 9 | Totality, soundness, no escape hatch |
| GoalDirected.v | 8 | Goal reachability preservation |
| Transparency.v | 7 | Semantic transparency |
| Oracle.v | 7 | Oracle parameterization |
| HashChainSpec.v | 6 | Abstract hash chain properties |
| Convergence.v | 6 | Fixed-point convergence |
| Interpreter.v | 4 | Concrete interpreter |
| GovernedCognitiveCompleteness.v | 1 | Grand theorem (19 conjuncts) |
| Prelude.v | 0 | Common imports |
| Directives.v | 0 | DirectiveE type definition |
| Governance.v | 0 | Gov handler definition |
| Extraction.v | 0 | OCaml extraction directives |

---

## What the Proofs Cover

- **All effects governed**: every syntactic form that produces an effect does so through DirectiveE, interpreted by Gov (Safety.v)
- **Capability authorization**: Gov allows iff capability is in the declared set for the trust level (TrustSpec.v, DirectiveTotality.v)
- **Delegation non-escalation**: callee capabilities bounded by caller's capability set (DelegationNonEscalation.v)
- **Composition invariance**: governance holds at every depth of machine composition, by coinduction (CompositionPreserves via CapabilityComposition.v)
- **Compute purity**: programs with empty capability set emit only observability directives (EffectAlgebra.v)
- **Materialization governance**: forms are inert until materialized through governance (GovernedMetaprogramming.v)
- **Ledger completeness**: every directive produces a governance decision; hash chains are tamper-evident (LedgerCompleteness.v, HashChainSpec.v)
- **Coterminous boundary**: E_B = G_B within the target behavioral model (CoterminousBoundary.v, SourceTraceCorrespondence.v)
- **Subsumption asymmetry**: structural governance strictly subsumes content governance (Subsumption.v)
- **Cognitive completeness**: five cognitive primitives are realized and essential (CognitiveArchitecture.v, GovernedCognitiveCompleteness.v)

## What the Proofs Do NOT Cover

- Elixir runtime additional stages: consent checks, denial history, retry logic, audit-only override
- C NIF marshaling wrapper correctness
- SHA-256 collision resistance (standard cryptographic assumption)
- External system behavior (LLM responses, HTTP endpoints)
- Liveness properties (proofs are safety, not liveness)
- Elixir code purity inside :compute blocks (proof assumes executor honesty)

## Extraction

The governance kernel is extracted to OCaml via Rocq's standard extraction pipeline (Extraction.v). Extracted functions: `capability_allowed`, `capability_for_directive`, `trust_at_least`, `trust_value`, `interp_directive`, `interp_directives`, `compute_event_hash`, `cap_in_list`, `allowed_cap_set`, `cap_empty`, `cap_singleton`, `cap_union`, `cap_full`, `cap_subseteq`.

The extracted code is compiled as a NIF and loaded into the BEAM runtime. The trusted computing base: Rocq extraction pipeline, OCaml runtime, C NIF wrapper.

---

## Verification

To verify these counts independently:

```bash
cd coq/governance-proofs
eval $(opam env --switch=coq-8.19)

# Count named theorems
grep -c "^Theorem\|^Lemma\|^Corollary\|^  Theorem\|^  Lemma\|^  Corollary" theories/*.v | awk -F: '{sum+=$2} END {print "Named theorems:", sum}'

# Count completed proofs
grep -c "Qed\." theories/*.v | awk -F: '{sum+=$2} END {print "Completed proofs:", sum}'

# Verify zero admitted
grep -l "Admitted\." theories/*.v  # should produce no output

# Count modules
ls theories/*.v | wc -l

# Compile all
for f in theories/*.v; do coqc -Q theories MashinGov $f || echo "FAIL: $f"; done
```
