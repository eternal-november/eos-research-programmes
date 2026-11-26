# Return-to-contact with an ACK-retained but settled obligation

**I1 development only.** The same carried sender queue can mean the
base has already applied a report or that it still needs a rescue.
The finite model separates observed receipt, physical/application
completion, and committed staging cost. It models one published
movement trigger, not the whole ACHORD stack. A direct planner using
the same terminal receipt and route menu ties the common checker.

[Model, costs and comparison](Return_Commitment.tex) ·
[Development scope](FREEZE.txt) · [Lean kernels](Reserve.lean).

Python 3.10+, Git and C++17. Use the SubT input layout and source paths
in [the native timed source producer](../../subt-relay-debit/pending-scope/timed-source-producer/README.md).
This directory's SOURCE.tsv lists its used SubT files; there is no
need to fetch the warehouse side of that manifest.

    R=/path/to/eos-research-programmes/projects/swarm-coordination/research
    sh replay.sh /path/to/subt-source-parent \
      "$R/integration/subt-relay-debit/pending-scope/timed-source-producer" \
      "$R/integration/shared-admission-core" | cmp expected.json -

Actual native packet attempts and receipts are checked. Routes,
terminal application code, sensor truth, and reserve costs are
declared civil simulation conditions, not a field experiment.
