SAME-OBJECT PROOF INDEX AND ACCEPTANCE CHECKPOINT — 31 October 2026

This is a new bounded delivery. Earlier crossing/protocol deliveries remain
unchanged. Start with Same_object_proof_index_and_acceptance_checkpoint.txt,
then c5_controller_instantiation.md and the clean proof_review.md.
parity_baseline_comparison.md states the fair-comparison limits.

Reproduction uses Python 3.12 and its standard library only, with no network.
From this directory:
  python -m py_compile verify_crossing_certificate.py compile_crossing_certificate.py verify_c5_instantiation.py
  python verify_crossing_certificate.py > replay_crossing.stdout.txt
  python compile_crossing_certificate.py > replay_compiler.stdout.txt
  python verify_c5_instantiation.py > replay_c5.stdout.txt
  cmp replay_crossing.stdout.txt verification_crossing_certificate.stdout.txt
  cmp replay_compiler.stdout.txt verification_crossing_compiler.stdout.txt
  cmp replay_c5.stdout.txt verification_c5_instantiation.stdout.txt
Each script also regenerates its corresponding supplied JSON. Preserve copies
if comparing before/after; all JSON and console bytes must match exactly.
Expected: 112676 crossing assertions; 12 compiler positives/8 rejections;
9725 C5 assertions. The normalized compiler core ledger is 445n+597, with
admission/provenance/physical verification and optional C5 work separate.

prior_math includes exact source bytes for the uncertain-coupling mission,
common-response/discovery and witnessed-C5 compiler, original C5 THEOREM,
faithful regular finite-set representation (GraphSpanModel section 6),
fixed-cylinder Isbell comparison and adequate-CFS criterion, and contextual
first-loss assurance. Short source references resolve inside that tree.
Historical/background citations and retained private review filenames are
provenance references, not dependencies of the supplied executable replay.
The clean proof_review summarizes scoped review without private process logs.

Historical foundational Lean work is credited in the report with its archive
identities. No fresh Lean run is claimed. The historical full Lean source tree
and dependency environment are not bundled, and this package does not itself
independently reproduce that earlier entire project. This checkpoint is not
whole RC7/RC9 or all-36 closure, adoption, or physical certification.

SHA256SUMS covers every included file except itself. Source mathematics and
executables retain exact bytes; crossing verification notes only use portable
commands and omit an internal agent identifier. ZIP entries have deterministic
order, timestamps and permissions. No raw internal audits, private workspace
paths, recovery files or caches are included.
