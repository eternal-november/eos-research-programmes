# One-edge formation admission

Adding a new formation bound can invalidate a safe-stop proof beyond the two robots named in the change. Two directed distance profiles and two line envelopes give the exact admission threshold without enumerating every impacted pair. For a small simultaneous batch, shortest-path closure on just the proposed edges detects interactions. Two proposals that pass separately on the old graph can fail together.

[Proof and limits](Incremental_Braking_Admission.tex) · [Lean scalar checks](EnvelopeArithmetic.lean) · [Exact replay](replay.py) · [Recorded results](results.json)

Run python3 replay.py and compare its output with results.json. The test assumes one common state snapshot; it does not implement a distributed commit mechanism.

[Selecting a maximum admissible subset](selection/) is harder than checking a fixed batch; even individually valid bounds can have minimal conflicts of unbounded size.
