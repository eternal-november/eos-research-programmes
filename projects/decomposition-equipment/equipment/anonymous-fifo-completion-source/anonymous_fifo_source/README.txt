Anonymous FIFO acquisition and safe completion source package
31 October 2026

Start with REPORT.txt for the result, scope and limitations. Read
safe_anonymous_completion_theorem.md for the integrated conditional theorem.
The complete imported proofs are queue_acquisition_draft.md,
binding_certificate_draft.md and deadline_obstruction_draft.md. The retained
word "draft" in those filenames is a filename convention, not a claim that
unresolved proof issues remain at the stated conditional scope.

Requirements

Python 3 with the standard library only. This package was replayed using
Python 3.12.14. No network access or installed third-party packages are needed.
Extract the whole source directory so every sibling file remains together.

Reproduce

    cd anonymous_fifo_source
    python3 reproduce.py

The runner first verifies SHA256SUMS.txt, then uses an isolated temporary copy
to execute all seven scripts listed below. It compares regenerated reference
JSON byte for byte with the included result. It leaves the extracted source
and its manifest unchanged. For a checksum-only check:

    python3 reproduce.py --manifest-only

Individual commands, runnable from this directory, are:

    python3 test_binding_checker.py
    python3 reference_baseline.py
    python3 reference_pipeline.py
    python3 audit_dynamic_binding.py
    python3 audit_report_permutations.py
    python3 audit_runtime_deadline.py
    python3 deadline_obstruction_exactcheck.py

Running reference_pipeline.py directly rewrites reference_pipeline_results.json
with the deterministic model results. The isolated runner avoids modifying
the packaged copy. Do not use Python's optimization flag -O: assertions form
part of these finite regression checks.

Contents

REPORT.txt                          Substantive result and interpretation
safe_anonymous_completion_theorem.md Integrated model, theorem and proof chain
queue_acquisition_draft.md           Anonymous timing acquisition and schedule
binding_certificate_draft.md         Exact all-matchings parity theorem/proof
deadline_obstruction_draft.md        Adaptive two-world proof and slack repair
mathematical_review.txt              Clean review and evidence limits
comparison_delta.md                 Exact predecessor and selected-API delta
baseline_comparison.md              Bounded primary-source baseline comparison
reference_pipeline_note.md          Executable boundary and cost explanation
binding_checker.py                  Polynomial checker and positive verifier
test_binding_checker.py             Exhaustive and seeded matching validation
reference_pipeline.py               Public-input controller and private plant
reference_pipeline_results.json     Exact model output, including public traces
reference_baseline.py               Partition-free comparators and hull checks
audit_dynamic_binding.py            1000 exact-rational integration cases
audit_report_permutations.py        2000 report-row permutation cases
audit_runtime_deadline.py           Three current-clock/headroom boundary cases
deadline_obstruction_exactcheck.py  Exact reduced decision-rule enumeration
reproduce.py                       Manifest verification and complete replay
REPLAY_RESULTS.txt                 Packaged replay record
PORTABILITY_NOTES.txt              Exact nature of publication/portability edits
SOURCE_PROVENANCE.json             Original and delivered source checksums
SHA256SUMS.txt                     Checksums for every other packaged file

The results file contains simulated hidden-world validation fields explicitly
separated from public controller inputs. These are generated fixture truth,
not private user data. The full proofs establish general mathematical scope;
the finite replays do not certify real hardware or measured execution bounds.
No raw development history, private review archive or predecessor archive is
part of this package.
