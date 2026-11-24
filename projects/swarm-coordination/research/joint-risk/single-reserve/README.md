# One reserve, two mandatory dispatches

Run `python3 -B pilot.py --json | cmp results.json` under Python 3.12, without optimization. [Proof and scope](Risk_Intervention_With_Degraded_Reports.tex).

The earlier two-report law stays fixed. This study changes the dispatch geometry: the two receivers admit opposite orientations of one support. One reserve can protect either, but not both. The report-only minimax loss is 1/4 after two misses, even with randomization. A timely shared parity measurement permits one fixed evidence-based policy with worst conditional loss 175/1024, below 1/5, and ex-ante loss 287/2048. Neither branch cancels a dispatch. A late bit cannot change the allocation.

Truthfully revealing only the first local state does not suffice. An independently flipped timely parity measurement still meets the bound exactly up to error probability 3427/84730. The checker compares rational forward filtering, direct path sums and the finite minimax envelope. This is a bounded illustration of the value of joint information, not a validated sensor, physical risk estimate, or advance over direct robust Bayes.
