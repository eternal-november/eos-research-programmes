# Adaptive receipt parallelism

Receipt-preserving serial re-execution is characterized under deterministic pure read-then-write tasks, a closed common snapshot, exclusive unique writers and buffered commits. Task-tagged receipts are not ordered logs; cycles need not obstruct weaker final-state equivalence.

Read the [manuscript](Adaptive_Receipt_Parallelism.tex). Run the exact finite diagnostics with Python 3 (standard library only):

```sh
python3 checks.py
```

This is a scoped worked example using established mathematics, not a novelty claim or a completed general contextad enrichment. The manuscript received independent mathematical review; the executable checks are finite diagnostics, not formal proof. No Lean formalization or replay is claimed.
