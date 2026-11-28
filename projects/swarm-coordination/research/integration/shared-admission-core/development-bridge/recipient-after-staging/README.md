# Staging cut with a post-partition recipient change

Run `set -o pipefail; node staging_cut.js ../development.js | cmp - EXPECTED.json` in the repository. The archive contains the pinned development.js beside staging_cut.js, so pass `./development.js` there. The executable checks the blob of the full model before extracting the unchanged two-cut checker. No packages beyond Node and Git. Use AXLE Lean 4.36.0 with Mathlib for Staging_Cut.lean.

This is an authored model and candidate operating envelope, not a mission or protocol freeze. See Staging_Cut.tex for the exact dependency, cost accounting, strong-comparator gap and next native check.
