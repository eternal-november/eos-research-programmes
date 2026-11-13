Reproduction evidence and source locators

Start with H2_reproduction_and_trust_review.txt. It distinguishes successful
recorded-scope reproduction from the unresolved unit-inclusive I1 I2 I5 claims.
The final independent unit report is in the peer unit_boundary directory.

Verify this review bundle without running mathematical tests:
  python3 -B verify_review_artifacts.py

Optional verification of all separate earlier archives:
  python3 -B verify_review_artifacts.py --archives /path/to/source-archives

The 21 exact archive filenames and SHA256 values are listed in
archive_member_locator_index.json. Its members_by_sha256 dictionary is the
global resolver for exact source hashes used by any review folder. locators
maps research provenance locations to those member hashes or retained evidence
in this bundle. Preserved research paths are provenance, not a required layout.
The earlier archives are not nested or duplicated in this review package.

reproduction_entrypoints.json gives each clean extraction root, supported
command, exact public dependency pins and runtime requirements. Only public
compiler/library objects may be reused; project proof objects must be fresh.
Use clean_environment.sh before old assertion-based replay commands to clear
PYTHONOPTIMIZE, PYTHONPATH and LEAN_PATH. Mathematical tests themselves are not
rerun by verify_review_artifacts.py.

The D1 confirmation runner has no fixed workspace requirement:
  python3 -B reproduce_d1_core.py \
    --original-source /path/to/witnessed_decompositions \
    --d1-source /path/to/D1-source/formal \
    --toolchain-root /path/to/public-toolchain \
    --output-dir /path/to/new-output

The public-toolchain directory contains lean-4.35.0-linux and
project/.lake/packages at the exact recorded public revisions. This additional
final confirmation is not repair of an uncovered delivered-version gap: the
final earlier D1 source package already had a clean source-only replay.
The retained d1_final_confirmation/result.json is an immutable execution
receipt; its runner hash identifies the executed original runner. The supplied
public runner has only disclosed explanation/receipt-reason metadata changes.
Its build, source-copy, axiom-check and mathematical mutation logic is unchanged.

PUBLIC_DERIVATION_MANIFEST.json identifies original and public-copy hashes.
No original proof or log was overwritten. Reviewer task labels are generalized
only in public review metadata. A transient directory name in a public
mathematical diagnostic may be replaced by a portable placeholder; such copies
have distinct explicitly recorded hashes. The immutable original source hash
is never presented as the changed copy's hash. Previously delivered
metadata/locator derivatives are resolved to their exact delivered members.
Raw evidence filenames containing a historical private suffix are renamed
for clarity without changing their mathematical diagnostics.
