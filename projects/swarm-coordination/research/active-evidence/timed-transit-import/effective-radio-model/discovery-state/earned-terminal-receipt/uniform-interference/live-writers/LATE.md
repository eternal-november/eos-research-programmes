# Live primary and scoped pre-enqueue fencing

[Assumptions, replay and proof correspondence](Late_Writers.tex).
Copy the exact parent gate_budget.cpp file and pinned imports as for the
parent replay. The archive is self-contained.

    sh run_late.sh | cmp expected_late.json -
