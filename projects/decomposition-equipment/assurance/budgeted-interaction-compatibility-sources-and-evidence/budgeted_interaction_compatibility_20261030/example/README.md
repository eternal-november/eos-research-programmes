# Exact budgeted interaction benchmark

This executable specialization uses a known ladder superscope and known lag-one
response law. Static incoming parents are unknown. Exact full load measurements
arrive at the end of a slot. Useful actions reveal delayed evidence, and no
state/evidence reset occurs between job releases.

## Files and semantics

- `ladder_model.py`: integer physical/mission semantics and width-two relational DP.
- `exact_search.py`: robust finite-horizon AND/OR search, WIN/LOSE certificates and
  immediate UNKNOWN on the repaired cooperative search budget.
- `check_certificate.py`: author-side replay. This reuses model semantics and is
  not the independent audit. Independent scripts are in `../review/`.
- `workloads.py`: fixed 72 pair-route cases and separate 16 richer three-stage cases.
- `FROZEN_PROTOCOL.json`: numerical protocol and initial source hashes.
- `CAP_REPAIR_MANIFEST.json`: explicit post-freeze cap-enforcement source repair.
- `results/`: final repaired-source run, all offered statuses and certificates.
- `results_v1_before_cap_repair/`, `results_v2_cap_repair_intermediate/`: preserved
  partial superseded runs, not final evidence.
- `versions/`: pre-repair source and supplementary gate outputs.

`LOSE` means no uniform causal observation-based completion policy in the exact
finite action/model class from the given evidence and remaining physical budget.
It is not a universal claim about all representations and not actual-world
impossibility. `UNKNOWN` is not LOSE. A delayed all-zero flush is part of a WIN.

Three checker labels do not represent three independently developed algorithms.
`local` and `smart_global` intentionally share the same sparse row algebra,
relational DP and caches. Equality is a control; it does not establish a distinct
algorithmic advantage. `full_scope` is an unoptimized diagnostic comparator.

`frozen=True` preserves original parent knowledge, ignores all physical readout
information, and uses the same physical/mission action grammar. It remains a
coherent robust controller, but its policy class cannot exploit observations.

## Reproduce

Run tests in this directory:

    python -m unittest -v test_exact_search.py test_ladder_semantics.py test_certificate_corruption.py
    python strict_pair_gate.py
    python diagnosis_gate.py

To repeat the measured run without overwriting evidence, copy the Python files,
`FROZEN_PROTOCOL.json`, and `CAP_REPAIR_MANIFEST.json` into a fresh directory,
then run:

    python run_benchmark.py > benchmark_run.log 2>&1
    python summarize_results.py

`run_benchmark.py` resumes existing per-case summaries in its local `results/`.
Thus running it inside this preserved evidence directory does NOT perform a
fresh experiment. A fresh output directory is required for a fresh run.

Search has 5000 expanded-node and 20-second cooperative wall limits. The wall
check occurs before/after model queries, but does not preempt a single model
call or operating-system scheduling pause. Certification and exhaustive physical
replay are measured separately and are not subject to the search cap. CPU time
is not charged to simulated physical slots; no real-time deployment claim follows.

All initial worlds are physically replayed for every certified main WIN.
The three sampled oracle roots per configuration are supplementary, not exhaustive
pointwise feasibility classifications. Means in replay statistics are arithmetic
means over enumerated finite worlds, not learned probabilities.

Peak process memory was not measured per configuration. Certificate byte counts,
finite-world counts and operation counts are representation proxies only.

The diagnosis gate is separate from the main ladder workload. It distinguishes
pure completion, full mechanism classification, and diagnosis that preserves the
initially feasible worlds' completion options. It is a small semantic test, not
an independent scaling achievement.

## Supplemental executable interface

`policy_interface.py` validates one WIN certificate and exposes a single runtime
handle with `issue()` and `observe()` operations. Returned commands, state
snapshots and observation records are immutable values. Ordinary copying of
observation data is allowed; the API rejects copying the live handle.

Each observation envelope must carry the pending command's sequence number.
A stale sequence is rejected without advancing state, leaving the pending call
available for a valid response. An unexpected value at the current sequence
permanently rejects this continuation. Duplicate issue/consume calls are rejected.
These are Python API checks, not a formal linear type system or an authenticated
physical channel. A host can fabricate plausible values with a fresh sequence;
no spoof detection, source authentication or post-violation physical safety is
claimed. Exactly-once actuation and fresh faithful measurements remain assumptions.

The supplement was added after the numerical experiment. Its separate manifest
and 47-world regression do not change any of the 88 measured decisions.
