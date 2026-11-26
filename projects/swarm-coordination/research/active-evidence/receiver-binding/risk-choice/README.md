# Risk-limited active acquisition

Replays actual native no-probe and charged-probe outcomes, then checks
an authored family of fixed installed joint laws with two explicitly
different risk caps. Old mandatory callbacks remain paid. Probability
weights are not inferred from row counts.

Place SOURCE.tsv upstream inputs at the named paths. C++17 and Python:

    sh replay.sh /path/to/upstream | cmp results.json -

The exact rational comparison may take a few seconds. RiskChoice.lean
checks the reduced optimization bounds with Lean 4.35 and Mathlib.
See Acquisition_Risk.tex for the exact scope of the risk and cost laws.
