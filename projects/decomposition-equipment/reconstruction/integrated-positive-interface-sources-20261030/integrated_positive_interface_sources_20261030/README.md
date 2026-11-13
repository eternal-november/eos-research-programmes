# Integrated positive interface source bundle

30 October 2026

This bundle contains a scoped constructive stochastic compatibility theorem,
a positive instrument realization lemma, their finite exact example checks,
and the structural comparison results used by the theorem. The theorem connects
permitted calibration, a positive joint-source interface, contextual adequacy,
resource accounting, and a sufficient capability-matching witness under an
explicit operational doctrine.

The partial-pair family in Section H does not identify the full source law.
It preserves the admitted one-route mission contexts while leaving cross-route
dependence unresolved. The result does not discover source boundaries, safe
calibration, noninvasiveness, calibration-to-service transport, or the physical
gate and drain laws. It is not a claim of novelty or completion of unrestricted
discovery and compatibility.

## Reading order

1. `positive_contextual_interface_theorem.md` states the operational doctrine,
   theorem, categorical bridge, and growing mission families.
2. `positive_instrument_quotient_lemma.md` gives the known-instrument positive
   realization result and the obstructions to stronger section requirements.
3. `proof_review.txt` explains the mathematical review, finite test coverage,
   dependencies, and remaining assumptions.
4. `prior_art.md` places the ingredients alongside relevant published results.
5. `structural_dependencies/` contains six unchanged mathematical notes on the
   CFS and Isbell comparisons used in the main theorem. These are dependencies,
   not results re-established by the finite example tests. The compact-boundary
   note also mentions a separate quantale-module specialization; that optional
   illustration is not needed for the stated bridge and is not bundled here.

## Reproduce the finite checks

Use Python 3 with its standard library. No additional package is required.
From this directory run:

```sh
python3 verify_positive_interface_examples.py
```

The script uses exact rational arithmetic in its assertions. It writes
`positive_interface_example_results.json` next to itself and prints the same
JSON to standard output. `positive_interface_example_check.log` is the retained
output of the checked run. Decimal displays are derived after exact rational
calculations; they are not assertion tolerances.

The tests cover finite examples and formulas, not the general theorem,
statistical concentration, physical premises, capability compilation, or
categorical coherence. The mathematical review is not machine-checked proof.

## Integrity

`SHA256SUMS` records every other bundled file with a relative path. On systems
with the standard utility, run `sha256sum -c SHA256SUMS` before reproducing the
checks. The theorem, lemma, script, saved results, saved log, and six structural
dependencies are byte-for-byte copies of their reviewed source versions.
The bibliography and review are user-facing summaries rather than private
working reports.
