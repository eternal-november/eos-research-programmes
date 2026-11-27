# Constrained audits after a change of authority

[Technical note](Audit_Authority_And_Timing.tex).
Fixed terms and finite public missed-duty classes. Known role uses a
capacitated cut; choosing subjects before the role is recognized uses
common matchable sets. Proof-side and runtime access stay separate.
No actual enforcement or physical authorization is claimed.

    OPENBLAS_NUM_THREADS=1 python3 -B audits.py | cmp expected.json -

SciPy is used for independent direct LP comparisons. Lean 4.35.0 with
Mathlib checks the three stated arithmetic witnesses in AuditCuts.lean.

[Archived receipt frontiers](archived-receipt-frontiers/README.md): complete
prefixes admit an exact common-role reduction; native archived gaps do not.
