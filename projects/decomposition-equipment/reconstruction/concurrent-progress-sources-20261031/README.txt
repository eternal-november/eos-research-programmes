Concurrent progress and reconstruction: source package
31 October 2026

Start with ordered_lock_progress_theorem.md for the fixed-worker P/G service-tail
bound under ordered locks and an explicit cyclic scheduler. Read
composition_challenge.md for the serial-interface obstruction, positive local
controlled-history realization, and actual finite-joint-path map q in Fact(r).

The reconstruction closure condition includes the actual current context state
and private memory, not only visible history. Terminal padding means actual
declared halt, not recoverable blocking. Coherence retains the SAME scheduler,
resource manager and primitive tick granularity; nested round-robin is different.
No general concurrency novelty, spawning theorem or full physical reconstruction
contract is claimed. prior_art.md records research context and prospective
acceptance criteria, not a replacement for the delivered statements.

Contents

  ordered_lock_progress_theorem.md  Final scoped progress theorem.
  composition_challenge.md          Final controlled-history/joint-cylinder result.
  prior_art.md                      Primary-source context and scope notes.
  proof_review.txt                  Mathematical review and finite-check limits.
  verify_concurrent_progress.py     Reproducible exact finite regressions.
  verification_results.json         Saved structured result.
  verification.log                  Saved stdout, identical to the JSON bytes.
  SHA256SUMS                        SHA-256 for every other packaged file.

Unchanged earlier dependencies

  progress_feedback_20261031/excursion_progress_transport.md
  cylinder_audit/compact_boundary_cfs_wiring.md
  cylinder_audit/isbell_external_product.md
  cylinder_audit/isbell_comparison_span_coherence.md
  cylinder_audit/mixed_context_wiring_interchange.md
  cylinder_audit/general_adequate_cfs_span_criterion.md
  cylinder_audit/traced_isbell_completion.md
  cylinder_audit/partial_trace_cfs_completion.md

These are included as unchanged mathematical dependencies; their broader
formal constructions do not enlarge the operational scope of this checkpoint.
The prior-art and review notes are presentation summaries. The two final source
files, verifier, saved results, and all eight dependencies are unchanged copies.

Reproduce with Python 3 (standard library only)

  python3 verify_concurrent_progress.py > reproduced_stdout.log

The script rewrites verification_results.json alongside itself. The fresh result
must match the saved verification.log exactly; reproduced_stdout.log must also
match it. Probability calculations use exact rational arithmetic. A PASS records
only the finite regression scope described in proof_review.txt, not a formal
proof of the infinite/general theorem. No network connection is required.

Integrity check from the extracted directory, where available:

  sha256sum -c SHA256SUMS
