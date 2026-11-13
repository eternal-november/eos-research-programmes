# Verification scope

Written proofs, finite diagnostics and Lean proofs are different evidence levels.
No fresh Lean replay or full mathematical audit is claimed for this collection.

Each formal package keeps its own Lean toolchain and dependency lock. The
witnessed-calculus package is the initial formal development; the later equipment
packages contain narrower formal cores. These do not certify every discovery,
assurance, reconstruction or full-unital statement.

For finite checks, run a selected script from its containing directory. Equipment
`run_e2_checks.py` through `run_e5_checks.py` require `--output PATH`. Their
`source_scope_manifest.json` files are functional integrity inputs, not optional
archive metadata. Keep them with the corresponding scripts and mathematical
sources.

The full-unital `verify_full_unital.py` accepts `--max-k`, `--product-max-k` and
`--typed-max-k`. Any result covers only the explicitly enumerated parameters.
The symbolic proofs are separate.

Older reproduction wrappers may assume an original archive layout. Use the
specific standalone mathematical check rather than treating a historical archive
replay script as a repository-wide test command. Cross-package linkage and a
single integrated build remain separate work.

## Saved numeric evidence

The compact reusable-environment example retains the n=12 records and its public manifest. From that package's `examples/`, run `python check_saved_artifacts.py runs/n12`. Larger listed runs are summaries; regenerate their records with `check_growing_memory_environment.py` before requesting saved-record verification.

The composable-assurance example retains the twelve compressed decoded-observation arrays and paired JSON evidence consumed by `review/independent_execution_audit.py`. These are numeric fixtures, not additional independent observations.

The evidence-efficient-discovery example retains its compressed training/holdout records and exact prediction certificates, consumed by `tests/review_final_monitor_certificate.py`. Its repeated training snapshot is not a new acquisition. NumPy is required for these three checks. All three saved-evidence checks passed during preparation.

These bounded checks supplement the selected equipment, unital-repair and application checks; they are not a single integrated proof certificate.
