B4 C4 and G1 to G3 source and evidence package
1 November 2026

Read first

B4_C4_G1_G3_Completion_Report.txt gives the consolidated result and boundaries.
The exact local acceptance and independent review records are indexed there.
This archive preserves original mathematical source bytes and final evidence;
it does not amend the original contract or close the whole program or I3.

Package map

  b4/          Raw and semantic refinement recovery proof, finite checker,
               exact Lean audit modules, source freeze, portable final logs.
  c4/          Full-information baseline comparisons, five ablations, B4
               input comparison, independent proof/literature/finite review.
  g/           G1 to G3 typed hierarchy, exact coding results, synthetic audit,
               verbatim clauses, finite checker and original reference copies.
  review/      Independent B4/G proof review and independently written checks,
               bounded final replay receipts and logs, exact reviewed pins.
  originals/   Additional unchanged B4 reference copies with source mapping.
  tools/       Package verifier, isolated finite replayer, deterministic ZIP
               rebuilder. These helpers do not modify author source files.

MANIFEST.sha256 pins every other file in this directory. provenance.json maps
byte-preserved copies to their origins. Authored file-local manifests remain
unchanged and retain their own scopes. They are custody records, not proofs.
Absolute paths inside original receipts are historical run locations, not
portable prerequisites; portable equivalent logs and source copies are mapped
by b4/formal/evidence/log_locations.json,
review/b4_formal_evidence/log_locations.json and the package source index.

Verify all packaged bytes

From this directory, using Python 3 standard library only:

  python3 tools/verify_package.py

Or, with a system SHA256 utility:

  sha256sum -c MANIFEST.sha256

Checks detect changed, missing, extra and symlink files. An independently
trusted manifest hash is needed to defend against replacement of both the
package and its manifest. No cryptographic authorship signature is claimed.

Replay finite checks without altering frozen evidence

  python3 tools/replay_finite.py

The wrapper copies five checkers to a temporary directory, runs them and
compares their JSON results with the final receipts. It excludes only elapsed
seconds and Python optimization mode from B4's otherwise exact comparison.
The other four receipts must match every JSON field. It also verifies that
the assertion-based G and independent B4/G checkers reject Python -O.
The wrapper also reruns B4 with -O and -OO, both C4 suites with -O, and
B4 frozen-source guards in all three modes. All five mathematical suites
and these runner checks require only the Python standard library and no network.
The wrapper deletes its temporary outputs after checking and prints a receipt.
These finite checks do not establish unrestricted mathematical quantifiers.

For direct inspection or replay, first copy the relevant directory to a fresh
writable location because author scripts write results beside themselves:

  python3 b4/checks/verify_b4.py
  python3 c4/checks/verify_c4.py
  python3 c4/audit/independent_c4/independent_falsification.py
  python3 g/verify_g_observation_recovery.py
  python3 review/independent_recovery_checks.py

The last checker prints JSON to stdout; it does not save the result file.
B4 and both C4 checkers use explicit runtime checks. G and the independent
B4/G checker intentionally reject optimized Python before assertions run.

Replay Lean source closure with external public prerequisites

The ZIP includes every project source input and both audit modules. It does
NOT include the compiler, public compiled libraries, .lake caches, .olean
objects or temporary build directories. A separately provisioned toolchain
is therefore necessary. This is a source/evidence package, not a standalone
compiler distribution and not a new universal H1 or H2 reproduction verdict.

Provide a directory TOOLCHAIN containing:

  lean-4.35.0-linux/bin/lean
  lean-4.35.0-linux/bin/lake
  project/.lake/packages/<each pinned package, with Git metadata and builds>

Compiler: official Lean 4.35.0, commit
  eb6cafb7290e8bd5f2937522d8d804f58f02bafc
Compiler binary SHA256:
  bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38
Exact dependency revisions: b4/formal/original_source/lake-manifest.json.
The runner checks the compiler hash and version, the lock, all source hashes,
all upstream Git revisions and clean tracked dependency worktrees. It reuses
public upstream objects but compiles project objects fresh from source.
Public compiler/library objects are trusted, not rebuilt independently.

Set absolute paths and choose a new writable OUTPUT directory outside the
frozen package and outside its original_source subtree:

  python3 b4/formal/verify_b4_lean.py \
    --source-root /absolute/package/b4/formal/original_source \
    --toolchain-root /absolute/TOOLCHAIN \
    --output-dir /absolute/new/OUTPUT

The historical workspace toolchain path in the receipt is optional context,
not required as a pathname. The runner performs no network downloads. It
prints 23 exact axiom closures, rejects two deliberately false growth proof
mutations, then checks the restored original. Positive B4 closure uses only
propext and Quot.sound; G1's quotient factorization additionally uses
Classical.choice. The occurrence equivalence itself is axiom-free. There is
no sorry axiom or native computation oracle. See the exact per-declaration
lists rather than extrapolating to the whole proof manuscript.

To test altered-source rejection and stale-PASS replacement without compiling,
first copy b4/ to a new writable directory and run there:

  python3 formal/test_runner_guards.py

These tests reject modified frozen source under normal, -O and -OO Python.
Their deliberate failure receipts are successful negative controls, not an
unresolved failed mathematical result. The original author receipt is not
rewritten by the isolated packaging verification.

Rebuild the identical ZIP

  python3 tools/rebuild_zip.py /absolute/path/outside/package/rebuilt.zip

The rebuilder verifies the manifest before writing. It uses a fixed top-level
name, sorted POSIX paths, fixed timestamp 2026-11-01 00:00:00, fixed regular-file
permissions and uncompressed ZIP storage. ZIP_STORED avoids compression-library
version differences. Every source byte is unchanged. With the same package
files, this produces the same archive bytes and SHA256 hash. No compiler or
cache is included. Output must be outside the frozen package tree.

Bounded exclusions

Temporary formal/runs, guard_runs, independent compiled projects, Python
caches, private notes and internal failure registers are intentionally absent.
The original b4/source_hashes.json is preserved unchanged. Its context-only
TOOLCHAIN_RESTORATION entry is not copied: that historical infrastructure
receipt contains internal setup notes and is not a mathematical source or
replay input. Compiler identity, dependency pins, exact source freeze, final
closure receipts and portable logs ARE included. No source checksum is
silently rewritten to conceal this exclusion.

Literature evidence consists of the separately authored applicability audit
and its primary-source locators, not rehosted full publications. This bounded
source closure supports the current local results; it is not a mirror of every
transitively mentioned older program artifact or a new re-execution of them.
