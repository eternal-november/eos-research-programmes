I5 simultaneous observational repair
31 October 2026

Read I5_simultaneous_repair_results.txt for the results, then
 i5_joint_repair_theorem.md for the exact statement and proof map.

This package establishes the selected graph-linked active-label result relative
 to its stated old-calculus dependencies. It does not close the whole original
 completion contract, unrestricted I1, crossing-cut I4, or physical acquisition
 and implementation questions. No literature-priority claim is made.

Mathematical sources
  concrete_model_gate.md             Declared model and observation scope
  model_and_core_comparison.md        Model laws and relative presentation
  monoid_repair_theorem.md            Analytic transformation-monoid family
  profile_schemata_theorem.md         Full-profile necessity and bounds
  repair_calculus.md                 Repair existence and synchronized criteria
  modular_repair_theorem.md          Scoped local/global comparison and failures
  baseline_comparison.md             Primary-source baselines and limitations
  proof_review.md                    Independent mathematical review
  scope_review.md                    Selected I5 obligation coverage
  verification_note.md               Executable results and coverage boundaries

The prior_math directory contains the byte-preserved old mathematical sources
 identified in model_and_core_comparison.md section 7. Their use is limited to
 that stated dependency scope; they do not prove the new coefficient relations.

Reproduction commands (portable examples; run in this directory)
  python3 -m py_compile verify_i5.py verify_modular_bridge.py
  python3 verify_i5.py > verify_results_replay.json
  cmp verify_results.json verify_results_replay.json
  python3 verify_modular_bridge.py
  sha256sum -c SHA256SUMS.txt

Only the Python standard library is required. The executable checks are finite:
 they do not enumerate all old profiles, establish unbounded theorems by sampling,
 or measure the full two-channel rank-two simultaneous repair. Source hashes in
 verify_results.json identify the mathematical files accompanying these runs.

Distinguish branch correlation from channel independence: the M4 rank-two C-only
 label-template repair has 38 classes, not the 16 coordinate-index classes.
 Independent coefficient channels do admit the stated fixed-source fibre product.
 The shared-coefficient locally complete counterexample is N=1 only.

SHA256SUMS.txt covers every bundled file except itself. Archive integrity and
 extracted-script replay were checked before delivery. Source filenames ending
 in .md contain UTF-8 mathematical text; Markdown software is optional.
