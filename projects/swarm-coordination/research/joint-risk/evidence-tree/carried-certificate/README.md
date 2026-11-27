# Risk-certificate reuse through a named receipt

Two provisioned senders can report the same current native completion
without changing the carried proof. A supplier that returns a previous
completion can instead break the proof even with the same declared
local risk marginals. The current-case check is consequential.

[Proof, exact rebuild counts and source scope](Carried_Risk.tex).
Use the pinned files in [SOURCE.tsv](SOURCE.tsv):

    sh replay.sh /path/to/inputs | cmp expected.json -

Requires Git, Python and C++17. The Lean kernel uses Lean 4.35 with Mathlib.
Node counts are for qualified edits, not discovery from an unknown source.
No empirical risk, independent holdout, or general live synthesis claim.
