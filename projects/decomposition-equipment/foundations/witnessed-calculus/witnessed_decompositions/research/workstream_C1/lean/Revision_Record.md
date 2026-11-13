# C1 Lean-fragment author revision record

Contract v0.1 / 47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e;
C1 target remains 7a5d4bb8dd3aa0715c82b73b8c169def2935b98f41addfd0eaaf03a606be244e.

1. Implementation/elaboration attempts 01–08 are preserved under
   `../evidence/lean/`. Attempts 03,05,07,08 succeeded at their development
   stages. Earlier errors concerned structure field syntax, signature
   elaboration, dependent occurrence case splits, and list-membership
   simplification. No false mathematical theorem or admitted proof survived.
2. Independent L reviewer requested a P adapter precision improvement:
   the evaluation-image induction must assert EACH output block LIST is
   strictly increasing, not merely that its underlying sets partition the
   vertices. This is necessary for literal canonical-list equality.
3. Original adapter retained at
   `../evidence/lean/AdapterComparison_pre_review.md`, SHA-256
   e1414b0bfaa623feff865d80e3e8a1bd1979d874534b526bc9c70c65a70e930e.
   Revised adapter SHA-256
   42d7507d71314f785b65d56af3c8c674be7ac06e40e5c84c58925156f2777a0a.
   Added the explicit sorted-list invariant, strictly increasing range base
   case, and preservation by increasing parent-list lookup on valid child
   indices. No Lean code or target changed; no new assumption was added.
4. Source remains GraphCutFragment.lean SHA-256
   344502c147e8d387d6da577725bffbb8d1d2ad452537430d09e66ee93c97442e.
   This is author reporting, not independent acceptance. The all-tree image
   proof is P; all-parameter semantic Calc laws remain P; full C1 use gates
   C5/F2 stay OPEN.
