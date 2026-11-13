# Portable assurance-interface source and evidence archive

## Entry points and scope
Read `example/README.md`, `example/PROTOCOL.md`, `example/LINEAGE.md`, and the final independent reviews before interpreting results. Canonical theory is `theory/Canonical_Assurance_Interface_Theorem.md`, with predictable charging proof in `theory/Predictable_Source_Charging_Theorem_DRAFT.md` and canonical numerical witness in `design/Joint_Prospective_Witness.md`. Filenames ending DRAFT are retained mathematical development sources, not a draft final report. `Discovered_Assurance_Frame_Theorem_DRAFT.md` is a **superseded seed**, not the canonical theorem. The one-frame strictness witness is a secondary regression only. The structured discovery lemmas and design files record assumptions and prospective gate.

This archive preserves final frozen evidence, selected reviews and the explicitly labeled pre-validation result snapshot. It does NOT preserve all transient calibration drafts, development runs or a complete immutable preregistration trail. Logs and Python cache files are omitted. See LINEAGE for model-faithfulness corrections and reruns. No claim of independent replication is made for development runs.

## Exact environment and no-resampling validation
Recorded environment: CPython 3.12.14; NumPy 2.3.5; only NumPy is required beyond the standard library. From the extracted archive root, optionally create an isolated environment and install dependencies:

```sh
python3.12 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python verify_archive.py
```

`verify_archive.py` verifies every archived hash, copies the archive into a fresh temporary directory, then runs the independent implementation-free acquisition/arithmetic audit, exact composition proof regression, exact raw residual/category regeneration, negative tests, online regressions changed-interface regression and actual split-request FIFO regression, and repaired physical-guard counterexample/trajectory/frozen-decision regression. It compares regenerated JSON with frozen JSON and never executes `experiment.py` as a main program. Importing it for deterministic fixtures does not resample acquisition. All audit writes occur only in the temporary copy. The temporary copy is removed after verification. The original final evidence is never overwritten.

For a NEW acquisition reproduction only, explicitly copy the directory somewhere disposable and run `cd example && python experiment.py`. This resamples deterministically under the frozen seed/protocol and overwrites that copy's result files; it is not necessary for archived-evidence validation and was not run during packaging. Wall-clock fields need not match.

## Calibration retention and raw replay recipe
Each `example/results/*_categories.npz` losslessly retains the decoded observable averaged residual matrix. Each paired `*_evidence.json` ends with a calibration record containing sample count, decoded-byte SHA256, exact NumPy bit-generator state, raw residual SHA256 and decoded filename. `results.json` gives n, world seed and audit-only sharing family. `replay_observations.py` and the independently written `review/independent_execution_audit.py` are executable exact recipes: recreate the seeded channel permutation/source blocks; restore stored bit-generator state; generate binomial(2,.02) counts and two bounded uniform reference-error arrays; broadcast by source block; form residuals; round/decode; verify both raw and decoded hashes. Hidden truth appears only in generation/audit, not inference. NumPy version is pinned for exact RNG replay. Raw arrays need not be stored redundantly.

Calibration is **compressed batch simulation of a logical acquisition schedule**, not millions of individually executed wall-clock physical frames or hardware measurements. Reference errors are generated per source block and broadcast to channels; the logical reference count is not an independently sampled per-channel error-trace count. Confidence exclusions are .004 per artifact, and .05 is a separate illustrative operational allowance for one counterfactual mission. Variants are not a sequential deployment campaign with a free risk-account reset.

## Integrity
`ARCHIVE_MANIFEST.json` hashes every payload file except itself. Its verification script is itself hashed. `example/FINAL_MANIFEST.json` is the author's earlier frozen acquisition-run source/result identifier, preserved unchanged: its experiment hash matches `example/versions/experiment_before_inactive_guard.py`, NOT the repaired current checker. `example/SEMANTIC_GUARD_REPAIR_MANIFEST.json` identifies the current repaired checker, old source, repair regression and unchanged primary results. `SUPPLEMENTAL_SPLIT_MANIFEST.json` identifies supplemental causal split-request traces. See LINEAGE for the post-freeze inactive-zone safety defect and sufficient guard repair; this did not rerun acquisition. Packaging verification logs outside this source tree record fresh-extraction checks; they are not outcome evidence. The root `Composable assurance interface results.txt` is the final plain-text report, not an intermediate authoring draft.
