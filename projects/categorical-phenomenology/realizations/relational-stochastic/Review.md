# Independent mathematical and reproducibility review

**Disposition: PASS for the stated finite, normalized, phase-tagged two-stage scope.**

Reviewed 2 November 2026. This is an independent agent review of the source arguments and executable checks, not formal proof-assistant verification, peer-review acceptance, or novelty certification.

## Exact reviewed source

The main source was reviewed under the working filename `Native_Relational_Stochastic_Construction.tex`; the delivery package may name the identical bytes `Native_Relational_Stochastic_Construction.tex`.

| File | SHA-256 |
|---|---|
| Main TeX source | `719bcc02612c3053e28afff4e808e78cd35b4a18170d4f3a18f15b6d0e02fe4f` |
| `checks/verify.py` | `3b5d733d9744e020da1c79a30f6d250a22338e977189d143ba7f27af2d55abb2` |
| `checks/expected_results.json` | `ddb00891c23ececcbc278b4e89a46ffc752719030c6b30e283075400331eac00` |
| `checks/reproduce.py` | `1f734cfb8eeba76a9dc44d9b3e80929c2af6c30eced1dcdb9f9b9ab80e33f78f` |

## Mathematical checks

The review read the full main source and the supplementary lifting, stress-test and prior-art notes. In particular it checked:

- Normalization of arbitrary factors over a nontrivial commutative zero-sum-free semifield. Zero right-factor rows may be deleted; all remaining row sums are nonzero and invertible.
- Extraction from an arbitrary native generator, rather than only a preselected normal form. Nonzero reaching weights, absence of zero divisors, and absence of cancellation force the three disjoint phase supports. The restricted middle link remains normalized and yields a feasible coupling. Together with the explicit construction this proves the stated exact cost formula, including mixed initial states and counted phase memory.
- The deterministic-link lower bound from coverage of every positive-mass coarse middle state.
- The actual category of factorized native witnesses, including both arrow equations and their preservation of the full coupling. Its cost is not claimed monotone along all internal simulations.
- The explicit input-comparison functor, coefficient-change functor, strict composition, and the optimized cost inequality. Strict composition excludes arbitrary support-trimming choices. Stochastic coarse-state maps do not automatically retain deterministic links.
- The maximal admissible Boolean relation test, independently of a factor-rank guess.
- The product-of-simplices image, the exact-support relative-interior criterion, the sign of its dual inequality, and its handling of lower-dimensional and singleton images. Constant functionals require equality rather than a false all-strict inequality.
- The distinction between lifting a coupling support and lifting an entire prescribed Boolean factorization at its original size.
- The one-middle-state criterion, identity-Q reduction to nonnegative rank, binary full-support examples, unbounded full-support resource gap, and strict observation-garbling effects.
- Equality of feasible sets under simultaneous recovery of Q and R, and the resulting identity of factorization categories without identifying their differently labelled readout generators.
- The finite Blackwell reversal and the limited role of Hall/Strassen criteria. The report credits the standard convex and factorization machinery and does not claim a new general realization theory.

During review the author clarified finite-cylinder semantics, supplied the explicit native extraction equation, made the generic support argument explicit, and separated trimming from strict composition. The final empty-word normalization and finite-word matrix-product formulas were also checked, as was the explicit restriction to nonzero-coefficient support rather than independent possibility data permitting zero-weight branches. These clarifications are present in the hashed source. No unresolved substantive issue was identified within its declared scope.

## Executable checks

The reviewer inspected `verify.py` and `reproduce.py` and independently ran `python checks/reproduce.py`. It copied the source checker and frozen expected JSON to a fresh temporary directory and passed under ordinary Python and `python -O`, with identical output and no stderr. Validation uses explicit `require` calls, not assertions disabled by optimization.

The reproduced results include all 81 row-total Boolean 2-by-2 input pairs (29 feasible, 52 infeasible, 63 feasible couplings); four exact rational binary controls; the explicit dual violation; 96 interface comparison squares; 96 sequential-composition identities; 3 coarse-state collapse comparisons; and 9 factorization-arrow transports. The executable counts match the report. These tests supplement, not prove, the general theorems; they do not solve arbitrary nonnegative-rank optimization.

## Acceptance boundaries

The result is a substantive common finite relational/stochastic fragment, not arbitrary-stream primitive discovery, arbitrary multistage realization, unrestricted diagram lifting, preservation of qualitative optimal factors, or a proof of physical implementability. The literature audit is focused rather than exhaustive; this review does not certify priority or publication novelty. No empirical benchmark or external application was validated. The TeX is intentionally uncompiled; no PDF layout or rendering is certified.
