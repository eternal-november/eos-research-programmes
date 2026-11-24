# Joint risk under degraded reports

Run `python3 -B pilot.py --json | cmp results.json` with Python 3.12, without optimization. The executable is standard-library only. See [the proof note](Joint_Risk_Under_Degraded_Reports.tex) for the model, theorems, and primary comparisons.

Two fixed laws with independent component motions have identical distributions of the two observed reports and identical local posterior health marginals. After two misses their two-dispatch risks differ: 57611/149504 versus 34661/149504. Their ex-ante physical mission risks are both 79/256. The product posterior gives the wrong conditional answer even though it gives the right ex-ante answer here.

A nonzero observation likelihood preserves a product posterior exactly when it is rank one on the prior's active support. Binary marginals plus the signed interaction recover the exact posterior when that test fails. The executable compares rational forward filtering and first-loss mass against direct world paths. A factorized reporting interface or a truthful extra reading can repair part of the estimation problem; neither changes physical loss here. Survival is a separate, nonseparable event.

This is a finite diagnostic and exact elementary filtering criterion, not a claim of novelty over factored Bayes, a risk estimate for a physical system, or a new policy that meets a failed bound.
