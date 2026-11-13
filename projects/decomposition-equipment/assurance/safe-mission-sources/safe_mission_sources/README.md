# Safe discovery and mission completion — portable evidence package

This package contains the theoretical argument, executable synthetic examples,
frozen configurations, raw result records and traces, independent reviews,
prior-art assessment, and final report. It supports **conditional safe completion
under declared finite-model and physical contracts**, not unconditional task
success for every initial mechanism or a hardware validation claim. Read the
report and `example/IMPLEMENTATION_CORRECTIONS.md` before interpreting counts.

## Main result (including the negative finding)

The richer sequential benchmark certifies **12 of 48 roots for both exact
relational and same-data rectangular methods**. The same 12 roots have minimum
worst-case completion time **168 ticks for both**; the other 36 have no policy
within the supplied three-leg grammar. Thus this experiment does **not** establish
a mission feasibility or cost advantage from retained relations. The independent
frontier check verifies 120 decisions. Earlier partial-acquisition diagnostics
show 874 versus 373 successful certificates (501 exact-only) among 2,376 separate
continuations, but that gap must not be transferred into a mission advantage.
Explicit all-low controls safely abstain instead of falsely claiming completion.

## Environment and exact reproduction

Tested with CPython 3.12.14 and NumPy 2.3.5 on Linux. No third-party dependency
other than NumPy; no network, secret, service, hardware, or source-tree location
is required at runtime. Installing dependencies may require network access.

```sh
tar -xzf safe_mission_sources.tar.gz
cd safe_mission_sources
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python reproduce.py --output reproduction_outcomes.json
```

`reproduce.py` first validates all payload SHA-256 values in `MANIFEST.json`,
then runs the commands below in a fresh disposable copy, leaving archived raw
records unchanged. It saves every exit status and stdout/stderr, selected negative
and corrected outcomes, and semantic comparisons for changed JSON records.
Only runtime measurements (`seconds`, `elapsed_seconds`,
`growing_engine_smoke_seconds`) are ignored when comparing JSON; scientific
counts, policies, traces and configurations are not ignored. For independent
sequential/frontier audit records, changed input hashes are accepted only after verifying
both hashes against their raw files and confirming those inputs are identical
except runtime measurements; this check is recorded explicitly. A passing
rerun is supplementary finite evidence, not a machine-checked proof of the
mathematical theorem. The manifest excludes itself; the enclosing archive has
its own separately delivered SHA-256 checksum.

Commands run from the extracted package root, in this order:

```sh
python theory/check_relational_discovery.py
python theory/check_selective_completion.py
python review/independent_theory_tests.py
python example/test_relational_engine.py
python example/reproduce_engine_smoke.py
python example/sequential_mission_cost_diagnostic.py
python example/run_constructed_missions.py
python example/partial_acquisition_probe.py
python example/partial_acquisition_reference_check.py
python example/sequential_mission_compiler_v1.py
python example/sequential_mission_compiler.py --config sequential_mission_corrected_config.json --output-prefix sequential_mission_corrected
python example/sequential_mission_negative_check.py
python review/independent_execution_check.py
python review/independent_sequential_check.py example/sequential_mission_results.json
python review/independent_sequential_check.py example/sequential_mission_corrected_results.json
python review/independent_frontier_check.py
```

The exploratory cost diagnostic must run **before** regenerating the sequential
root records: its frozen specification hashes the exact original raw root file,
which includes non-deterministic elapsed-time metadata. This is a provenance
check, not a dependency on an absolute path. The documented order preserves it
without changing code, configs or archived records.

## Evidence map and preservation of corrections

- `Safe mission completion results.txt`: final self-contained technical report.

- `theory/`: theorem/proofs, author finite checker and recorded checks.
- `example/frozen_experiment.json`: original constructed-family specification.
- `example/constructed_results.json`, `constructed_n*_trace.json`: corrected
  fixed-cap constructed runs. `safe_abstention_results.json` records the explicit
  all-low negative control.
- `example/constructed_results_before_fixed_cap.json`: preserved **historical**
  pre-fixed-cap output; its exact old runner was not preserved. It cannot be
  separately regenerated from this package and is not presented as a final
  validated experiment. The correction and its effect are documented openly.
- `example/partial_acquisition_*`: fixed partial-knowledge diagnostic, raw trials,
  independent small-world reference, summary and scope qualifications. The
  alternative continuations are not a single long robot execution.
- `example/sequential_mission_compiler_v1.py`, `sequential_mission_config.json`,
  `sequential_mission_results.json`: preserved original one-tick-transfer variant.
- `example/sequential_mission_compiler.py`,
  `sequential_mission_corrected_config.json`, `sequential_mission_corrected_*`:
  explicitly corrected ten-tick transfer with original seeds, action grammar,
  deadline and energy budget retained.
- `example/sequential_mission_negative_*`: all-low initial-class member; safe
  refusal is expected, not goal completion. A successful test exit means the
  negative outcome was correctly established.
- `example/sequential_mission_cost_diagnostic_*`: separately marked exploratory
  post-result diagnosis; does not replace the frozen primary outcome.
- `review/`: independent theory/execution audit prose, executable independent
  checks and raw check outcomes. Independence is about implementation, not an
  independent laboratory or external empirical replication.
- `prior_art/`, `RESEARCH_GATE.md`: significance, prior-art and target-gate scope.

`relational_engine_qa.json` is supplementary smoke metadata, not a primary
experimental result; its supplied `reproduce_engine_smoke.py` is rerun along with
the engine unit tests.

## Packaging

No semantic code edits or path adapters were made. Scripts resolve inputs and
outputs relative to their own files or supplied relative arguments. Python bytecode
caches and redundant original console logs are excluded; raw JSON records and
full traces are included and losslessly gzip-compressed. Fresh reproduction logs
are retained in the separately delivered reproduction outcome record. Timing and
compressed-byte reproducibility are distinct: scientific values should reproduce,
wall-clock times need not. The tar members use normalized metadata.
