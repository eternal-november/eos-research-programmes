FINAL PROTOCOL WORKSTREAM — SOURCE PACKAGE
31 October 2026

This package closes the bounded variable-duration protocol workstream: actual
charged-step substitution, coherent reconstruction at cuts, derived progress
for a growing nested-call family, and explicit boundary counterexamples.
It does not accept, amend, adopt, or complete the full research contract.
The contract-progress companion distinguishes the completed scoped result
from the remaining same-family integration and retained contract duties.

START HERE

- variable_duration_closure.md: operational language, normalized microstep
  semantics, actual path maps, cut/substitution coherence, and boundaries.
- progress_witness.md: displayed nested-call programs, resource discipline,
  unbounded durations, derived tail/mean bounds, and failure cases.
- proof_review.txt: final four-gate verdict and exact limits of the review.
- Contract_progress_and_next_retained_target.txt: clean contract coverage
  review and the next retained target. The original contract remains a
  separate existing checkpoint; it is not silently replaced by this review.
- verify_final_protocol.py, verification_results.json, verification.log:
  standalone finite regression program and its exact saved results.
- SHA256SUMS: SHA-256 of every payload file except the manifest itself.

REPRODUCTION

Use Python 3 with only its standard library. From this package directory:

    python3 -m py_compile verify_final_protocol.py
    python3 verify_final_protocol.py > replay.log
    cmp replay.log verification.log

The program writes verification_results.json beside itself. To compare that
output with the supplied result, copy the supplied JSON to a temporary path
before running, then compare the two byte-for-byte. The result is 58,900 NEW
finite assertions in this verifier, including repeated per-step invariants,
not 58,900 independent theorem instances. Earlier verifier totals are not
added. The general mathematical results remain hand proofs, not machine-
checked infinite-state, categorical, or arbitrary-tree theorems.

The supplied package was checked using a fresh extracted copy: compilation,
complete replay, exact JSON/log equality, manifest hashes, ZIP member
allowlist, and ZIP CRC checks. The final verifier has no nonstandard imports.

DEPENDENCY MAP

All dependency files below are byte-exact copies of the earlier source
versions used here. Their hashes appear in SHA256SUMS. They are retained
mathematical provenance, not a claim that each earlier package was rerun.

dependencies/cylinder_audit/
  compact_boundary_cfs_wiring.md
    Actual fixed-port joint cylinders and compatible CFS wiring spans.
  isbell_external_product.md
    Monoidal Isbell construction and tensor/class preservation.
  isbell_comparison_span_coherence.md
    Source-changing normalizer comparisons and coherent span composition.
  mixed_context_wiring_interchange.md
    Variance-aware context and wiring compatibility.
  general_adequate_cfs_span_criterion.md
    Abstract adequate-CFS sufficient criterion and exact span orientation.
  traced_isbell_completion.md
    Traced-to-compact structural completion and its declared scope.
  partial_trace_cfs_completion.md
    Partial-trace admission/completion and domain qualifications.

dependencies/protocol_contexts_20261031/
  protocol_context_substitution_theorem.md
    Prior token-context substitution and actual reconstruction at tree cuts.
  polling_envelope_progress_theorem.md
    Prior polling-envelope/work conversion and its clock qualifications.

dependencies/concurrent_progress_20261031/
  ordered_lock_progress_theorem.md
    Ordered-lock service, conditional intrinsic episodes and work bounds.
  composition_challenge.md
    Controlled-prefix reconstruction with actual current context state and
    an explicit same-cylinder realization arrow.

dependencies/progress_feedback_20261031/
  excursion_progress_transport.md
    Conditional excursion/P-G bounds, random-walk derivation and prior
    distinction between almost-sure completion and finite expectation.

OMISSIONS AND SCOPE

The compact-boundary source mentions quantale_module_joint_wiring.md as a
concrete example of its general cup/cap formula. That example is illustrative
here, not a dependency of the abstract theorem or final protocol proof, and
is omitted. Other earlier discovery/contract checkpoint titles in the clean
coverage review are coverage evidence, not premises needed to replay this
verifier or prove the final protocol theorem; their existing source packages
remain authoritative. Standard primary-paper references are cited within
the preserved mathematical sources; no paper copies are bundled.

No optional spawn extension or undelivered extension is included. Raw audit
chronology, internal crosswalk working notes, the duplicate contract source,
private continuation notes, transfer data and helper programs are excluded.
The clean proof review summarizes the final verdict rather than shipping
obsolete draft-hash or awaiting-construction audit states.

The source language fixes countable state and declared countable experiment/
test families, a finite decomposition tree, independent private innovations
conditional on retained public preparation, boundary-only information flow,
one authoritative resource manager, and a positive instruction clock.
The positive progress family has arbitrary finite parameters, but each
instance has finite routine depth and no spawning or cross-worker joins.
The formal canonical CFS/Isbell apex is not claimed to be an executable
stochastic manager. No empirical discovery, unrestricted intervention,
arbitrary physical real-time, or whole-contract acceptance claim is made.
