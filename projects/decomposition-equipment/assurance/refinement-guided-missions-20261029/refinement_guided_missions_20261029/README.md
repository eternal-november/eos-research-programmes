# Refinement-guided delayed-resource missions: reproducible source archive

This archive preserves a fixed synthetic study, including all successes, refusals,
rejected proposals and solver timeouts. No favorable-seed filtering is used.

## Environment and dependencies

The retained run and extraction replay used CPython 3.12.14, NumPy 2.3.5,
SciPy 1.17.0 on Linux x86_64 (glibc 2.41). Python standard-library modules
supply exact integer and rational arithmetic. Dependencies are pinned in
`requirements.txt`; no proprietary package, service, secret or absolute source
path is required. Installation (network/package access required):

```sh
python3.12 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
```

## Verify the frozen archive

From the extracted archive root:

```sh
python verify_manifest.py
python reproduce_checks.py
```

`reproduce_checks.py` replays the retained trajectories/certificates and regenerates
deterministic numerical summaries in an isolated temporary copy. It compares JSON
objects, not formatting or wall-clock timing. It does not launch a new mission
solver sweep, overwrite frozen results, or equate successful replay with solver
optimality. The archive manifest hashes every payload file except the manifest
itself; the sidecar SHA-256 hashes the compressed archive.

## Optional full solver regeneration (not required for exact replay)

Make a writable separate copy first; never overwrite archival evidence:

```sh
cd ..  # parent of the extracted archive root
cp -a refinement_guided_missions_20261029 regeneration
cd regeneration/example
python -u delayed_missions.py --output mission_results.json > mission_run.log 2>&1
python summarize_results.py mission_results.json
```

The full fixed sweep uses 3 dimensions × 2 seeds × 2 regimes × 6 methods,
with 6 sequential mission batches per stream. Each MILP proposal has a ten-second
wall-clock limit. Runtime measurements necessarily vary. Timing cutoffs, solver
versions/platforms and tie selection can also change proposed schedules, timeout
statuses and scientific aggregate outcomes; identical seed/configuration is not
an assertion of byte-identical or numerically identical solver regeneration.
Every regenerated result requires fresh independent certificate replay. Frozen
results remain the primary evidence for reported numerical findings. The
packaging process ran exact retained-result replay, not a second timed sweep.

## Contents

- `theory/`: target, proof details and executable law checks.
- `design/`, `TARGET_GATE.md`, `review/Prospective_Target_Gate.md`: prospective
  task design and target-selection commitments.
- `example/`: preregistration, executable implementations, regression tests,
  complete raw results/traces, logs and descriptive summaries.
- `review/`: independently implemented exact checks and substantive audits.
- Final report and packaging verification evidence are included in this bundle.

See the final report for the scope of the claims and the protocol correction
record for version history. Sparse certificate counts are not a resident-memory
separation; timed solver failures are not mathematical infeasibility proofs.

## Implementation correction and source provenance

The original six-method sweep is retained unchanged as `example/mission_results.json`
and in `example/v1/`, with its original source/configuration. A diagnosed cached-
rehearsal defect caused needless physical rehearsal of some schedules whose
unsafety was already exactly inferable. The explicitly disclosed correction
reran only that method with unchanged instances/budgets. Corrected method results
are retained separately; `example/final_results.json` combines them with unchanged
original results for the other five methods and records per-method/per-stream
source provenance. Its top-level source hash is null: it is not a single-source
rerun. See the included correction record and independent audit.

For full regeneration, `delayed_missions.py` is the corrected implementation.
After running the optional command above, use explicit input arguments:

```sh
python summarize_results.py mission_results.json
python analyze_matched.py mission_results.json
```

The default summary input is the preserved mixed-provenance `final_results.json`;
regeneration must pass its new file explicitly. Repeating only the corrected
method is supported with `--method cached_rehearsal`. No full solver regeneration
is claimed to reproduce the original timing-dependent outcomes identically.

## Direct independent replay commands

```sh
python review/independent_execution_checks.py --results example/final_results.json --output /tmp/final_replay.json
python review/independent_execution_checks.py --results example/v1/mission_results.json --output /tmp/v1_replay.json
python review/independent_summary_checks.py
```

The original-v1 replay uses the v1 directory so its source hash resolves to
the original implementation. The final composite replay additionally checks all
72 coarse fixed-schedule witnesses. Exact replay requires only standard Python;
NumPy/SciPy are needed for the author regression tests and optional solver runs.
