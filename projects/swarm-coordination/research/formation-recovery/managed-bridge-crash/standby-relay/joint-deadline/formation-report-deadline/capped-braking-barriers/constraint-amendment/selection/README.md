# Selecting formation amendments

Checking a proposed set of bounds is polynomial. Choosing the largest safe subset is NP-hard even when every proposal is safe alone. The proof embeds directed length-bounded cut in the exact braking rule and gives minimal conflicts of arbitrarily large size.

[Proof and complete bounded search](Selecting_Formation_Amendments.tex) · [Lean arithmetic](SelectionArithmetic.lean) · [Exact replay](replay.py) · [Recorded results](results.json)

Run python3 replay.py and compare its output to results.json. The test is on one fixed state, not a model of staggered execution.
