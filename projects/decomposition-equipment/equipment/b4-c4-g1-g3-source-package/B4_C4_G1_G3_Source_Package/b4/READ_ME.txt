B4 scoped evidence package

Read B4_Refinement_Invariants_and_Recovery.txt first. It proves the original
B4 recovery criteria and distinguishes fixed/unknown raw source, raw versus
evaluated final operation, exact semantic arrows and chronology. It does not
change historical acceptance or assert scientific novelty.

Verified evidence

- Author finite check: 31,512 fixed endpoint pairs against independent direct
  tuple enumeration, 30,724 arrows, 1,868 source operations and 5,783
  nontrivial fibres. Exhaustive simple graphs through two vertices; K=[2];
  source arity at most three, target arity at most two; two scalar monoids.
- Exact original six-vertex A4 fixture, with graph edges {0,5},{1,2},{2,3},
  {3,4}, blocks {0},{1,2},{3,4},{5}, and grades a,id_1,id_1,b. Repeated
  nonempty components, distinct unary replacements, a nullary unit, four
  ordered leaves, actual graph/partition labels and cross-edge loss are tested.
- Fresh source-only Lean build of the 12-module B4/G1 original dependency
  closure. Thirteen B4 axiom closures and ten G1 core closures printed.
  Two invalid source mutants rejected and original source rechecked.
- Frozen original-source checks reject altered input and replace stale PASS
  with FAIL under normal, -O and -OO Python. Public upstream objects are reused;
  no inherited project object is reused. See formal/result.json.
- Independent reviewer-owned raw-tree/schedule and semantic/graph evidence
  resides under the parent package's review directory, with its own manifest.
  Do not treat this author readme as the review verdict.

Run finite checks

  python3 checks/verify_b4.py

The finite runner is standard-library-only and uses explicit checks rather
than Python assert. Its scope is bounded and does not prove unrestricted P
claims. Its result is checks/result.json. A failed run writes FAIL.

Run formal checks

  python3 formal/verify_b4_lean.py \
    --source-root formal/original_source \
    --toolchain-root /path/to/restored/toolchain \
    --output-dir /path/to/new/evidence

Run from the b4 package directory, or use absolute paths. The default source
root is resolved relative to the runner, so it also works from another cwd.
The toolchain root must contain lean-4.35.0-linux and project/.lake/packages.
It is the official Lean 4.35.0 release, commit
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
The runner pins the compiler binary hash, original lake-manifest.json, all
upstream Git revisions and tracked-source cleanliness. The exact dependency
lock is bundled. It requires preexisting public upstream compiled libraries;
this package does not download them or bundle the approximately 600 MB compiler.
The provided restored root in this workspace is
 /workspace/shared/d1_equivariant_transport_20261031/formal/toolchain.

The original source set is frozen in formal/source_freeze.json and copied
byte-for-byte under formal/original_source. The freeze additionally pins the
audit modules and runner. Output goes to an isolated temporary project below
the supplied output directory. Project .olean files are created there from
source. External public dependency directories are symlinked read-only by
convention and no dependency source is modified. Public compiler/library
object correctness is trusted; it is not independently rebuilt from source.

Run runner failure checks

  python3 formal/test_runner_guards.py

Formal original run logs are copied under formal/evidence for portability.
formal/evidence/log_locations.json maps historical absolute log paths in the
receipt to the bundled relative logs. Temporary formal/runs and guard_runs,
all .lake directories and compiler objects are NOT needed in a delivery ZIP.

Sources and delivery pins

source_hashes.json and source_hashes.sha256 identify original contract,
mathematical proofs, formal sources, historical audits and later scope context.
DELIVERY_SHA256SUMS pins this directory's intended delivery files, excluding
run caches and the checksum file itself. A delivery checksum is not independent
mathematical acceptance. No uploads or original-ledger writes occurred.
