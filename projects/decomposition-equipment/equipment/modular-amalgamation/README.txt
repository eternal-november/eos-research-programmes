I1 conservative modular amalgamation source package
31 October 2026

Read I1_conservative_modular_amalgamation_results.txt first. The principal proof
is conservative_amalgamation_theorem.md; its four proof companions are
interface_pushout_theorem.md, twisted_normal_forms.md, refinement_coherence.md
and cut_transport.md. baseline_comparison.md preserves the pre-proof mathematical baseline
comparison. Its forward-looking bridge requirements are addressed by the
current proof companions named above; generic baseline constructions do not
automatically provide those bridges. null_ideal_obstruction.md is an optional
additional bare-amalgamation obstruction, not the central partial-map family.

The scope is a selected original-I1 realization, not arbitrary graph amalgams,
a two-dimensional pushout of raw path presentations, or acceptance of any
unrelated obligation. The full Q_J multiplication-table completion is chosen
explicitly. Negative coefficient visibility requires a nonempty graph color.

DEPENDENCIES
The dependencies directory contains exact prior mathematical source files.
Their bytes and narrowly stated roles are in dependency_manifest.json and
its readable companion. Historical prior_math/THEOREM.md,
prior_math/Completion_Comparison.md and prior_math/Semantics_Transport_Factorization.md
resolve to the same basenames in dependencies. The historical
workstream_A/rewrite/A3_LOCAL_COMPARISON.md reference likewise resolves there.
No imported source is claimed to prove new coefficient critical joins.
A3 sections 1–6 supply the original signature, typing and inverse comparison;
its located-term example and acceptance-gate references are contextual.
Integrated_Targets and old review-gate files are provenance, not additional
premises of the selected proof. The I5 repair and monoid examples are included
as contextual predecessors; their optimum-reflection claims are not imported
into the semidirect setting. This package does not reproduce an old Lean build.

REVIEW AND VERIFICATION
proof_review.md and scope_review.md give separate correctness and scope checks.
These are automated AI reviews, not human peer review or proof-assistant/kernel
certification; reviewers can share correlated model failure modes.
The analytic critical-peak and full-occurrence-forest argument is the proof.
The finite checks include actual six-vertex typed path instances, but do not
exhaustively enumerate all proof paths or establish all-context coherence.
See verification_note_i1.md for precise finite bounds and limitations.

Run with Python 3, using only its standard library:
    python replay_verify_i1.py
This checks delivered source pins, creates and extracts a temporary snapshot,
compiles its Python scripts, runs the independent verifier and four supporting
checks, and compares every JSON result field. It writes
verify_i1_replay_report.json. No network access or installation is required.
verify_i1_sourcepins.json pins reviewed source and imported dependency bytes;
SHA256SUMS.txt covers all other delivered members. Replay archives and caches
are intentionally not shipped.
