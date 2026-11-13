D1 source bundle reproduction

Start here

report.txt is the standalone result report. theorem.md is the frozen mathematical
source. acceptance_review.md gives the independent local disposition and scope.
source_obligation_map.md maps the original D1 clauses to proof sections. The
original contract and inherited proof dependencies are under original_sources;
the reference ledger maps historical paths to these bundled files. Original Lean
sources needed by the bridge and its baseline build are in formal/upstream_source.

Evidence levels

P is the general mathematical proof. L is the separate finite Lean representative
and original Signature/Assignment/path bridge. C is the Python finite computation.
The formal README states the exact limits; no full generic D1 mechanization is
claimed. Imported historical proofs and upstream compiler/libraries are credited,
not independently re-proved by the package replay.

Integrity

source_manifest.json contains SHA256 values of all content files except itself
and packager_replay_receipt.json. That receipt reports the replay outcomes, not a
self-authenticating proof. The outer SHA256SUMS.txt authenticates the final TXT and
ZIP bytes. Archive entries are sorted, time-stamped 2026-10-31 00:00:00, mode 0644,
and compressed deterministically. No symlinks or compiled objects are shipped.

Replay with a restored pinned environment

Use Python 3.12 or compatible Python 3 and the official Lean 4.35.0 Linux binary.
Restore the nine exact public dependency revisions in
formal/upstream_source/lake-manifest.json, with their matching upstream precompiled
libraries. Do not run lake update. toolchain_provenance.json gives official URLs,
commit pins, trusted archive/binary hashes and the precompiled-cache provenance.

Run from any working directory:

    --lean /path/to/lean-4.35.0-linux/bin/lean \
    --packages /path/to/pinned/project/.lake/packages

The replay checks every bundled hash and all nine dependency revisions and
origins, then uses disposable copies. It runs Python normally and optimized,
checks the frozen domain/counts, runs the standalone Lean file and deliberate
wrong-coordinate mutant, and rebuilds the original project from the bundled
sources before checking the bridge. Only upstream compiled dependencies are
reused. No D1 or original-project compiled objects are reused. Its two principal
axiom-closure logs must equal the bundled checked logs byte-for-byte. It rechecks
source hashes after execution. Temporary compiler outputs and mutant diagnostics
are discarded. The script never downloads automatically.

Smaller checks

For only the core finite representative, use:
  LEAN=/path/to/lean-4.35.0-linux/bin/lean bash formal/verify_d1.sh
For the original bridge, use a disposable copy of formal, then:
  LEAN=/path/to/lean-4.35.0-linux/bin/lean \
  D1_ORIGINAL_PROJECT=/path/to/fresh/upstream_source \
  bash formal/verify_original_bridge.sh
These lower-level author scripts write logs/results beside their source. Prefer

Restoring the public dependencies

The compiler archive is available at the official URL in
formal/toolchain_provenance.json. Verify its SHA256 before extracting. Its bin
folder must be first on PATH. Populate a working project with the bundled
upstream_source files. For each lake-manifest.json package, clone its recorded
URL and check out exactly its recorded rev into .lake/packages/<name>. Verify
all revisions. Run lake exe cache get from the pinned project to retrieve matching
upstream precompiled libraries; use MATHLIB_CACHE_DIR for a writable local cache.
The original source library build and original C2 module are then rebuilt by the
bridge runner. Public network access and substantial disk space are required.

The delivered ZIP intentionally excludes the roughly 594 MB compiler archive,
large compiler/library installation and caches, .olean outputs, private audit
failure registers, intermediate attempts, and raw failed-mutant diagnostics.
A pathless clean mutation receipt records that the expected negative check passed;
the mutation-generating script makes that check reproducible without shipping a
failed source version. The unmodified formal_manifest.json records the formal
worker's broader freeze; bundle_manifest_exclusions.json identifies its omitted
diagnostic entries and two unused original example/smoke files. The exact retained
original-source subset is listed in formal/bundled_upstream_source_sha256.json. source_manifest.json is the delivered file allowlist.

Original-reference handling

Frozen mathematical/original sources were copied without algebraic or path
substitutions. A historical reference may therefore name an old absolute path.
Use original_reference_ledger.json to resolve it to a bundle-relative file. The
ledger records original and bundled hashes. This is a source provenance mapping,
not a claim that the original filesystem will exist on another machine.

Verification scope: use the standalone mathematical checks identified in the project VERIFICATION.md. The original archive replay is not a supported repository command. No fresh Lean replay is claimed.
