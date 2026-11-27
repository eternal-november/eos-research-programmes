# Native development replays on Cave Circuit 01

[Technical note](Native_Replays_And_Their_Kernels.tex). The two replays share
a pinned published cave graph, not a joint clock, robot trajectory, or mission
state. They strengthen two separate components of the I2 baseline. The layout
and profiles were inspected during development; this is not the independently
selected holdout.

- **COPS motion comparator.** The original COPS flow model generator and
  decoder, with a separate HiGHS solver seam, agree with full-graph
  time-expanded reachability in 96 known-plant leaf checks. Six additional
  leaves check feasible continuations at their declared deadlines. In each
  receipt-absent pair the two continued trajectories share the forced prefix
  through entry into the local gate-observation tile. The policy-level
  comparison is a separate exact causal search with named SQLite receipt
  queries; this is not native COPS multirobot, communication, or belief
  synthesis. The full comparator with actual communication/control and the
  independent mission both remain open.
- **SubT radio and broker.** Extracts the pinned visibility rebuild,
  route/range computation, send gate, dispatch and application callback.
  Checks 504 sends (280 lifecycle checks and 224 sends across 112 fresh
  ordered schedules); 30 schedules deliver both reports at their two
  respective opportunities. At the chosen 72 m cutoff, a near relay can
  deliver both only if it becomes effective between old and new sends, in
  that order. A far relay preserves the old route and need only become
  effective before the new one. The two reports use distinct senders and
  one callback destination. This is a delivery observation at the tested
  callback seam, not a persistent receipt, field data, a stock 72 m setting,
  or verified passage clearance.

## Replay

From this directory, fetch exact inputs (Git blob hashes in each
`INPUTS.tsv`), then run:

```sh
python3 -B prepare.py cops
sh cops/run.sh | cmp cops/expected_cops.json -
python3 -B prepare.py radio
sh radio/run.sh | cmp radio/expected.txt -
```

Existing inputs are checked rather than overwritten. Offline verification
uses `prepare.py <part> --offline` with inputs already present. Tested with
Python 3.12.14, NumPy 2.3.5, SciPy 1.17.0 and GCC 14.2.0. The [research
checkpoint](https://chatgpt.com/space/page_f5a09a52f6b881919b10d91ecf2caa80)
contains separate source-complete archives, each runnable from its extracted
root without network. Do not disable Python or C++ assertions.
