# Finite evidence for mixture monodromy

Two independently reviewed mathematical notes, frozen on 4 November 2026.

## Read first

- `finite_cover_recovery/finite_cover_recovery.pdf` (7 pages): constructive recovery of the full circle monodromy from finitely many independent restarted trajectories, with explicit confidence, mesh, mass, separation and regularity assumptions. Includes a randomized-offset periodic extension and a modular local-estimator replacement lemma.
- `evidence_limits/evidence_limits.pdf` (10 pages): unknown-modulus impossibility, known-modulus query bounds, short-group obstructions, and statistical/resource lower bounds with their exact scope.
- The matching `.tex` files are the final reviewed sources. They are not edited for this archive.

The notes use different circle normalizations and notation. Compare assumptions before comparing constants. In particular, short-group lower bounds are not lower bounds for unrestricted long trajectories. The reconstruction guarantees are conditional on supplied model promises, not finite-data validation of those promises. Neither note claims a general optimality or novelty result.

## Reviews, prior work and dependencies

- `finite_cover_recovery/independent_math_review.md`: exact-source mathematical review and final heading-only correction approval.
- `finite_cover_recovery/checks/independent_review.md`: computational/adversarial review.
- `evidence_limits/Independent_Review.md`: exact-source review of the evidence-limits note, including attribution checks.
- `finite_cover_recovery/prior_art_audit.md`: primary-source comparison, including Fan–Li's established local mixture recovery and the distinction between local identifiability and monodromy recovery.
- `background_sources/`: unchanged earlier proof drafts invoked by the width corollary and discussion. These are background dependencies, not additional newly claimed results.

All included files except the manifest itself have SHA-256 entries in `MANIFEST.sha256`. The final two TeX hashes are also hard-coded in `replay_checks.py`. PDFs are supplied as rendered artifacts; regeneration can change PDF metadata bytes without changing the TeX source or mathematics.

## Replay

Requires Python 3.10+ and NumPy 1.24+:

    python3 replay_checks.py

This first verifies the complete archive manifest, then reruns the seeded finite-cover checks, confirms their source binding and success, and reports whether the current run exactly matches the recorded results after excluding version strings. It writes new outputs only to `replay_outputs/`. The script asserts the mathematical/algebraic tests; simulation is not a proof of a theorem or a finite-data certificate of model promises. The evidence-limits note is checked by its analytic proofs and independent mathematical review; no separate numerical suite is represented as a proof of its lower bounds.

To regenerate both PDFs with an ordinary TeX Live installation containing pdfLaTeX, lmodern, AMS packages, mathtools, enumitem, geometry and hyperref:

    bash build_notes.sh

Outputs go to `rebuild/`, leaving the reviewed sources and supplied PDFs unchanged. For the current restricted environment only, an already installed writable pdfLaTeX format may be supplied with `TEX_FALLBACK_FORMAT=/path/to/pdflatex.fmt`; the script then enables explicit installed font/search paths. No format binaries or third-party articles are bundled.

`CLEAN_REPLAY_REPORT.json` records the actual clean-extraction replay performed for this delivery. The review files disclose the minor wording/scope corrections made before the final source freeze.
