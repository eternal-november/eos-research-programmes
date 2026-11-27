# Timing-aware replacement in the paced corridor

Unequal local duration bounds give exact port conflicts and a
pace-versus-latency frontier. The old Boolean interface loses exact
deadline substitution even at the same corridor length. A fixed deadline
cap admits a bounded weighted interface.

[Proof, constructive class, lower bound and comparator](Weighted_Handoff.tex).

    python3 -B replay.py | cmp expected.json -

Lean checked the overlap and capped-addition kernels (4.35, no `sorryAx`).
This inherits the earlier locally qualified latch and fixed-mode limits.
