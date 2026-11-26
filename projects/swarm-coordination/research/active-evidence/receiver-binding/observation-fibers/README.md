# Restrict a run, not just its installed law

An observation can distinguish realized probe effects even when the
installed binding is already known. In the native selected-code test,
a qualified negative can certify the next delivery and a qualified
positive can refute it. A missing status certifies neither. See
[claim, proof and residuals](Observation_Fibers.tex).

The native driver and source verification manifest are pinned to the
merge of #574 (`35e9192a28aa4901c53047490331c48f3ed39bba`), under
`projects/swarm-coordination/research/active-evidence/receiver-binding/qualified-next`.
Prepare the files from that manifest in an upstream directory, then
run with Python 3 and C++17:

    sh replay.sh ../qualified-next /path/to/upstream | diff expected.json -

`Fiber.lean` was checked in Lean 4.35.0 with AXLE (default Mathlib
header); the three audited results have no axioms. The independent direct
conditional check has the same information and result. Observation-report
erasure is a model above the pinned callbacks. No live or independently
selected tests, statistical estimates, or credit for I1/I2 are claimed.
