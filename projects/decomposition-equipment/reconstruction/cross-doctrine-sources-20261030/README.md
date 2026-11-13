# Cross-doctrine reconstruction: sources and exact finite checks

Research checkpoint — 30 October 2026.

## Reading order

1. `cross_doctrine_comparison_theorem.md`: exact free Isbell transport; native adequate-CFS comparison spans; signed contexts and honest fixed-port wiring; local exactness and formal strictness examples.
2. `qualitative_divergence_translation.md`: finite substochastic support-plus-deficit quotient, exact direct-sum first-exit feedback, normalized admission, no functorial stochastic section, noncontinuity, and the countable-state boundary. Its final section connects the operational translation to formal Int and free Isbell completions.
3. `prior_art.md`: primary-source baselines and positioning. Established infrastructure and elementary derived consequences are distinguished; novelty is not claimed.
4. `proof_review.txt`: concise mathematical review and the scope of the executable evidence.

The seven structural dependencies are included unchanged:

- `isbell_external_product.md`
- `compact_boundary_cfs_wiring.md`
- `isbell_comparison_span_coherence.md`
- `mixed_context_wiring_interchange.md`
- `general_adequate_cfs_span_criterion.md`
- `traced_isbell_completion.md`
- `partial_trace_cfs_completion.md`

## Reproduce the exact finite checks

Python 3 and its standard library suffice. From a fresh extracted directory:

```sh
sha256sum -c SHA256SUMS
python3 verify_cross_doctrine.py > replay.log
cmp replay.log verification.log
cmp replay.log verification_results.json
sha256sum -c SHA256SUMS
```

The script uses exact rational arithmetic, prints JSON, and writes the identical JSON to `verification_results.json` beside the script. `verification.log` is the expected stdout. No network access, nonstandard packages, or data downloads are required. The checked output covers 66,729 feedback kernels, 10,000 composition pairs, 8,000 simultaneous-versus-successive trace eliminations, 16 direct sums, and explicit boundary examples. Within the feedback enumeration, 2,993 qualitative input groups have distinct numerical trace values but identical qualitative trace values.

`SHA256SUMS` covers every other included file; the archive contains only the 16 listed source, review, verification, documentation, and checksum files.

## What this checkpoint does and does not establish

The concrete operational result is finite-state and uses disjoint-union first-exit execution, not Cartesian-product compact matrix trace. It preserves whole-kernel support and the positive deficit bit per input, not probabilities or expected times. Its no-section and countable-state counterexamples concern different, explicitly stated extension questions.

The native span theorem requires specified adequate cylinder factorisation systems and honest class-preserving assembly. The free construction is established Isbell machinery. Formal Int/Isbell completion does not infer a native CFS on either operational category, operationally implementable or finite canonical states, or admission reflection for arbitrary formal objects. Neither novelty nor completion of the broader reconstruction problem is claimed.

Executable finite checks are reproducible regression evidence, not proofs of categorical coherence, all finite cases, or the countable-state limit. The mathematical source arguments carry those claims.
