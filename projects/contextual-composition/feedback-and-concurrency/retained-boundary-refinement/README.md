# Retained-boundary refinement and correlation-aware composition

This tranche asks what information must survive abstraction for subsequent interaction to remain sound. It complements [the native first results](../native-first-results/README.md), rather than declaring the general feedback/concurrency contract complete.

Read [the self-contained TeX manuscript](Retained_Boundary_Refinement_and_Correlation.tex). Compilation is not required. Its four parts form a chain:

1. **Composition:** exact separator sufficiency and an optimal total-variation defect against a declared unrestricted mathematical partner class.
2. **Adaptive contexts:** retained-boundary coupling simulation, coherent target-kernel quantifiers, and the cost of discarding persistent dependence.
3. **Uniform witnesses:** a kernel-aware causal comparison; a distinct kernel-blind feasibility criterion; small missing-information witnesses and a finite-tag characterization.
4. **Quantitative integration:** local full-boundary defects propagate to finite-horizon adaptive trace bounds.

The probability constructions are explicit. Conditional independence, rectangular adversaries, visibility of kernel tags, and the permitted context class are assumptions, not facts inferred from marginal behavior. A coupling span is not automatically a directed native cell. Raw zero-probability paths and liveness need additional hypotheses.

## Verification and literature

Written proofs were independently cross-reviewed. Exact finite diagnostics exercise representative identities and boundary counterexamples; they are not proof certificates or exhaustive verification. No Lean formalization or TeX compilation is claimed.

Run from this directory:

```sh
python3 checks/check_refinement.py
python3 checks/check_separator.py
sha256sum -c MANIFEST.sha256
```

The manuscript credits primary literature on probabilistic simulation, robust rectangularity, junction-tree gluing, and approximate trace bounds. No historical novelty claim is made.
