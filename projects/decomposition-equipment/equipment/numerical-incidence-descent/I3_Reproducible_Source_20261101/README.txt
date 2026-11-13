I3 Reproducible Source Package
1 November 2026

Read I3_Completion_Report_20261101.txt for the results-first account, full
reviewed proof, independent review, source comparison and original I3 text.
Scoped_I3_Acceptance.txt records local technical acceptance only. No broad
novelty, external human certification or whole-program completion is claimed.

Quick replay

  python3 reproduce.py

Requirements: Python 3.10 or later, standard library only. Verified package
replay uses Python 3.12.14. No network, Lean installation, compiled artifact,
private cache, third-party Python module or historical path is required.
Allow a few minutes for the three complete baseline runs and eight semantic
mutations. The replay uses a fresh temporary directory, which is removed
on success or failure, and leaves the delivered tree unchanged.

reproduce.py checks the complete manifest allowlist and hashes, exact direct
dependency copies, author/review pins and the verbatim I3 excerpt. It then
copies only the two checker scripts to the fresh directory, replays normal,
-O and PYTHONOPTIMIZE=1 modes, rejects all eight mutant runs, and checks
results.json and guard_results.json byte-for-byte against the frozen files.
The executable tests are finite C evidence, not a proof of all-parameter
mathematics or a kernel verification.

Direct checker commands

  cd checks
  python3 verify_i3.py --output results.json
  python3 run_guards.py

These direct commands regenerate the result files and additional positive
stdout receipts. For an unmodified-tree identity check and deterministic
ZIP rebuild, use reproduce.py instead or work in a copy.

Source layout

- I3_Objective_and_Numerical_Incidence_Descent.txt is the exact reviewed proof.
- checks contains the independent verifier, optimization/mutation runner,
  explicit finite domains, expected mathematical results and guard results.
- review contains the final non-author mathematical review, source comparison,
  source pins and the exact independent replay source/result copies.
- I3_Original_Clauses_Verbatim.txt is an exact contiguous excerpt of the full
  unchanged original contract included under dependencies.
- dependencies contains an explicit allowlist of 17 exact-byte research
  source copies: the 16 author-pinned sources plus the checker's E5 theorem.
- source_locator_map.json maps historical research references to those
  packaged relative copies. Historical absolute source locators appearing
  in unchanged old research documents are not runtime dependencies.
- source_hashes.json and the review pins identify inherited evidence without
  changing its historical status. The author freeze record is the preserved
  pre-review identity snapshot, not a substitute for the final review.
- MANIFEST_SHA256.json hashes every payload file except itself. Its exact
  bytes are covered by the final ZIP digest supplied with the deliverables.

The direct dependency allowlist is bounded. It does not recursively package
all older research archives, formal builds, source references or public
papers. Public paper URLs and reviewed locations are supplied in the source
comparison. The package contains no compiler caches, scratch drafts, private
assistant memory, task transcripts, or raw failure logs. Expected mutation
rejection diagnostics remain in guard_results.json as positive evidence
that the negative controls work.

Deterministic ZIP rebuild

From the unmodified extracted source directory, choose an output path
outside that directory:

  python3 rebuild_zip.py ../I3_Reproducible_Source_20261101.rebuilt.zip

The rebuild uses the manifest's sorted allowlist, a fixed top-level folder,
fixed 2026-11-01 timestamp, Unix regular-file mode 0644, DEFLATE level 9,
and no archive comment. Rebuilding twice with the same Python/zlib runtime
must produce identical bytes. Across different zlib implementations, the
source file hashes and replay results are the portable identity criterion;
compressed ZIP bytes are not promised invariant across implementations.
