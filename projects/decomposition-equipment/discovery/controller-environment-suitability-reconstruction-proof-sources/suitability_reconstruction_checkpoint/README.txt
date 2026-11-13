Controller environment suitability reconstruction proof sources

This source checkpoint collects the mathematical notes, finite examples and
standalone Python checks accompanying Controller environment suitability
reconstruction results, dated 27 October 2026. Start with the report in delivery/.
The notes concern reconstruction with actual environmental correlations and
one physically permitted controller, not independently redesigned local ones.

The package preserves the authored proof notes and checker sources unchanged.
The Python checks are finite supporting evidence and regression tests. They do
not establish the general proofs by computation, certify scientific novelty,
prove an unrestricted synthesis theorem, or provide new Lean-checked theorems.

Reproduce the checks

1. Extract the ZIP into a new directory.
2. Open a terminal in suitability_reconstruction_checkpoint/.
3. Run:

       python3 verify.py

Python 3.10 or newer and its standard library are sufficient. No installation,
network access, Lean binary, original workspace, or large baseline archive is
needed. The verified release was replayed using the Python version recorded in
verification/Checkpoint_Verification_Receipt.json. The complete finite suite
may take several minutes; the verifier prints a PASS line after each checker.
Do not use Python's -O flag when running a checker directly: its assertions
are part of the tests. The entry point launches non-optimized isolated child
processes, regardless of the parent interpreter's optimization setting.

The verifier checks every packaged file against MANIFEST.json, enforces the
required member list, rejects altered or missing sources, then copies the
package into a fresh temporary tree. It runs every mandatory author and
independent checker there. Expected result JSON must be newly created and
report terminal PASS. The verifier also checks that no input source changed.
The fresh tree is removed afterward; the original extraction remains unchanged.

For a fresh curated receipt saved outside the extracted package, run:

       python3 verify.py --receipt ../fresh_verification_receipt.json

For integrity checks without rerunning the mathematical checks, run:

       python3 verify.py --integrity-only

The same verifier can safely validate and freshly extract the original ZIP:

       python3 verify.py --archive "../Controller environment suitability reconstruction proof sources.zip"

The archive check rejects traversal, absolute and backslash paths, duplicates,
case collisions, nonregular members including symlinks, and unexpected members
before extraction. Adversarial packaging controls run with the full suite.
SHA256 checks detect missing or changed files relative to the manifest; they
are not an authenticity signature. Keep the independently supplied ZIP digest
if you need to bind this entire release, including its verifier and manifest.

Contents and reading order

  delivery/Controller environment suitability reconstruction results.txt
      The readable research report, including results, assumptions and limits.

  theory/Typed_Persistent_Completion.md
  theory/Causal_Descent.md
      Finite persistent world reconstruction and the causal controller layer.

  theory/Typed_Causal_Presentation_Closure.md
  theory/Operational_Cut_Capability.md
      Original typed presentation, retained physical resources and actual cuts.

  theory/Causal_Constraint_Descent.md
  theory/Parametric_Causal_Descent.md
      Code-assignment descent, then stronger descent retaining the same tables.

  theory/Operational_Semantic_Profile_Recognition.md
      Finite-language recognition of unbounded permitted profiles and unknown
      common refinements, with actual support and shared physical constraints.

  theory/Coupled_Target_Index_Capability.md
  examples/Causal_Interlock_and_Telemetry_Families.md
      Parameterized capability separations and constructive controller families.

  scripts/check*.py
  theory/check_typed_causal_closure.py
      Seven author checkers and five independent checkers. The exact invocation
      list and result paths are in verify.py; their source hashes are in the
      manifest and curated receipt. All are mandatory for the full replay.

  verification/Checkpoint_Verification_Receipt.json
      Curated source-bound PASS results and counts from a clean replay. This is
      not an internal review transcript or a general machine-checked proof.

  references/Original_Calculus_Dynamic_Interpretation.md
      Exact unchanged prior mathematical interpretation of the original typed
      calculus. Historical source archive and Lean filenames cited there are
      provenance references, not bundled dependencies of this finite replay.

  references/CompletionContract.md
      Exact unchanged proposed baseline research contract. It is not an updated
      acceptance ledger. Copying it discharges none of its obligations and does
      not assert that the full original research program is complete.

  MANIFEST.json
  verify.py
      Checksums, roles, source fingerprint and the standard-library entry point.

Checker outputs and source preservation

The original standalone checkers write JSON beside some sources or into review/.
That directory is created only inside the fresh replay tree. No raw internal
review notes, coordination logs, stale result JSON, exploratory search script,
bytecode cache, helper upload file, or external binary is included. To invoke a
checker manually, first copy the extracted package elsewhere and create an
empty review/ directory there; retain the existing theory/, examples/ and
scripts/ layout. Generated JSON is evidence of that run, not a new proof.

Author and independent mean separate implementations supplied with this
research checkpoint. Independence is not a claim of anonymous external peer
review or institutional certification. Read each source's stated finite scope.
The all-size and all-generated conclusions rest on the supplied mathematical
arguments and their explicit hypotheses, not extrapolation from small tests.
