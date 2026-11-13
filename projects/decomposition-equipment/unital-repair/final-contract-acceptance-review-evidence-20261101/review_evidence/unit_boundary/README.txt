Unit boundary review standalone release

Read Unit_Boundary_Independent_Report.txt first.

Replay with Python 3 using only its standard library:
    python check_unit_boundary.py

The default provenance source root is the bundled sources directory.
An external copy with the same relative research paths can be supplied:
    python check_unit_boundary.py --source-root /path/to/snapshots

The checker overwrites only unit_boundary_results.json beside itself.
It never edits source snapshots. Mathematical checks do not depend on
source text parsing; source hashes record the evidence inspected.

source_snapshot_manifest.json maps six byte-exact research inputs and one
disclosed attribution-only public derivative of concrete_model_gate.md
to portable paths, original-source hashes and public-copy hashes.
provenance/gate_public_derivative_note.json records the single attribution
change and checks that every mathematical line is unchanged.
The working I5 sources and I2's
historical delivered-I5 dependency pins are explicitly distinguished there.
The original files were not modified; no theorem was repaired or
scope narrowed in this release.

provenance/checker_derivative_note.json records the locator-only change
from the retained original checker. All five mathematical test function
ASTs were compared and are identical. Fresh-extraction replay and semantic
result equality are recorded in portable_replay_receipt.json.

The report adds the distinction between preserving and reflecting identity.
It does not assert failure of E2 universal-unit preservation or the checked
I3/F4 structural unit squares. The selected cut-grammar decision remains open.
