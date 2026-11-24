# Query authority and private exposure history

[Statement, exact bound and comparison](Scoped_Advice_And_Amendment.tex). A correct change of permission can authorize a query whose answer the old confidentiality-preserving report did not retain.

- `python3 replay.py | cmp replay.txt`: check exact existing and expanded singleton profiles.
- `python3 batch.py | cmp batch.txt`: verify the exact supplemental size for added batch scope.
- `lake env lean ScopedAdvice.lean` (Lean 4.35.0 with Mathlib): checks profile refinement and impossibility of answer recovery, with no `sorryAx`.

See the [fixed mission law and admission model](../../joint-risk/exposure-profiles/README.md). This covers truthful limited disclosure, not the other R5 regimes.
