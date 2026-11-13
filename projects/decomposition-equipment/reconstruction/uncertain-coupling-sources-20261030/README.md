# Uncertain coupling source package

30 October 2026

This package records a scoped theorem for safely learning a mission-sufficient
interface when a finite-memory binary linear noise source has unknown source
grouping, coefficients, and delays. It includes the mathematical argument,
classical prior-art context, exact finite checks, and the unchanged categorical
comparison dependencies used by the argument.

## Main result

Read `uncertain_coupling_mission_theorem.md` first. Under the stated physical
and source assumptions, local projected-support learning supplies a positive
uniform block interface and an exact set-union criterion for determining new
linear output laws over the relaxed compatible subspace family. The theorem
combines that certificate with charged acquisition, checking, and service costs.

The concrete positive family learns local XOR-chain relations and a useful
delayed load slot without recovering the full source coupling. The negative
family consists of two physically realizable memoryless source laws whose
permitted two-coordinate calibration observations agree, but for which the
best uniform route-selection failure probability is exactly one quarter.

This is an application and integration of classical algebra, probability,
identification, and the supplied comparison machinery. It is not a novelty
claim or completion of an unrestricted discovery or realization contract.

## Files

- `uncertain_coupling_mission_theorem.md` — the finite-memory source model,
  acquisition and mission theorem, learned chain and delay examples, physical
  impossibility example, and restricted external-cylinder comparison.
- `obtainability_challenge.md` — the underlying finite-field criterion,
  affine extension, acquisition bounds, and observation-regime obstructions.
- `prior_art.md` — primary-source context and limitations of the comparison.
- `proof_review.txt` — mathematical checks and the limits of finite verification.
- `verify_subspace_coupling.py` — exact GF(2) verification using the Python
  standard library only.
- `subspace_coupling_results.json` — the expected machine-readable output.
- `subspace_coupling_check.log` — the expected standard output, byte-identical
  to the JSON result.
- `dependencies/` — six unchanged source notes supporting the categorical
  comparison construction.
- `SHA256SUMS` — SHA-256 hashes of every other file in this package.

The six dependency notes are `compact_boundary_cfs_wiring.md`,
`isbell_external_product.md`, `isbell_comparison_span_coherence.md`,
`mixed_context_wiring_interchange.md`, `traced_isbell_completion.md`, and
`partial_trace_cfs_completion.md`. Their inclusion does not assert that all
their ambient algebraic operations are physical operations in this mission.

## Reproduce the finite checks

From the extracted package directory, with Python 3.10 or newer:

```sh
sha256sum -c SHA256SUMS
python3 verify_subspace_coupling.py > replay.log
cmp replay.log subspace_coupling_check.log
cmp replay.log subspace_coupling_results.json
sha256sum -c SHA256SUMS
```

The script overwrites `subspace_coupling_results.json` beside itself with its
deterministic result and also prints that result. A successful run reports
`"status": "PASS"`. The optional `replay.log` is not part of the package.
The tests use exhaustive finite sets and exact rational arithmetic, not
Monte Carlo trials or observations of a physical system.

The checks include 154,973 full-ambient query cases, 35,203 restricted query
cases, 124,063 invisible hyperplane witnesses, 38,883 ordered sample tuples,
five learned-chain fixtures, 550 source-time lag-support cases, and the
two-world negative example with exact budgeted decision calculations.

## Scope that must be retained

Uniform fresh independent innovations, a valid memory bound, stationarity,
accurate observations, isolation, noninterference, physical draining, and
source-complete hazard tests are supplied premises, not learned conclusions.
The full fresh-start interval is charged even across the final calibration to
first service transition. A delayed physical load is enabled only at the
selected certified slot; other slots remain isolated.

The dual condition uses the union of individual probe row spaces, not their
linear span. Joint reads on one source block and separate reads on fresh
blocks are different experiments. The positive representative must retain
one shared block throughout its delayed uses.

The maximal compatible subspace need not have a stationary Toeplitz-filter
realization. Its exactness is stated for the relaxed block model; physical
soundness follows by inclusion, while a physical lower bound needs witnesses
inside the physical class. Equality and comparison are asserted only for the
proved restricted external preparation and test cylinder. No arbitrary
feedback, full-state equivalence, or executable formal completion is inferred.

Finite verification corroborates the enumerated cases. It is not formal proof
checking, empirical validation of physical premises, or an all-dimension test.
