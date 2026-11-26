# Braking with a delayed report

A fast rear robot needs the middle block to accelerate; a slow front robot needs it to brake. When the block cannot distinguish those cases until a report, the exact additional clearance depends on report delay. A single sum of the two gaps does not determine feasibility.

[Proof and scope](Braking_Under_Blind_Prefix.tex) · [Lean scalar checks](DelayArithmetic.lean) · [Rational replay](replay.py) · [Recorded results](results.json)

Run python3 replay.py and compare the output to results.json. The information delay is modeled, not inferred from a particular sensor or network.

[Joint risk at the physical cutoff](joint-risk/) connects delayed, noisy, or missing reports with previous exposures in the same episode.
