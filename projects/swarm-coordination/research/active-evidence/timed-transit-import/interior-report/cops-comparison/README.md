# Native cave-planner comparison for the interior event

This check runs the unchanged [COPS flow formulation at `67d2e5d`](https://github.com/FilipKlaesson/cops/tree/67d2e5dd4534b3f3eec95b6cfda9d4c9c1746ef0) using the prior [#600 HiGHS bridge](https://github.com/eternal-november/eos-research-programmes/pull/600).
The standard model sees time-expanded, fixed positions for a candidate
launch. An explicit restriction removes each send slot inadmissible in
that source history, including a decode deadline or the selected debit
law. The worker starts without the plan; both master and report flows
must reach it before its assigned movement. The prior bridge keeps
original variable kinds and native row/decoder checks. Neither the
flow formulation nor the code generates the input RF or physical law.

The run tests 32 fixed launch/history subproblems, seven feasible. For
a prelaunch observation class a common choice still needs separate
intersection of each history's feasible launches. Per-history COPS
answers are evaluator results, not oracle inputs for the actors.
The independent worker from the parent case is factored out: its route,
packet debit and notional task are disjoint. This is a tie at the
matched fixed-history planning interface, not a test of the full TRACE
executive or proof of what the native planner can express without the
explicit adapters. No holdout or I2 acceptance.

Stage the five exact COPS inputs in `SOURCE.tsv` in `INPUTS` (with
their `cops/` prefixes). The bridge is included for replay. Run with
NumPy and SciPy (checked with SciPy 1.17.0):

```sh
OPENBLAS_NUM_THREADS=1 python3 -B compare.py INPUTS .. | cmp expected.json -
```

The backup includes both the staged source and the exact parent replay.
