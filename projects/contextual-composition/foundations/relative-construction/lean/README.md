# Contextad constructor formalization

Lean 4.35.0, mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake exe cache get Mathlib/CategoryTheory/Monad/Kleisli.lean Mathlib/Algebra/Group/Defs.lean
python3 verify.py
```

Read `SOURCE_CROSSWALK.md` before using the declarations as evidence for a manuscript. This package supplies initial constructor-level verification, not a certificate for the whole relative construction or contextad programme. `AxiomAudit.lean` audits every named theorem in `TheoremIndex.json`; no project axioms or incomplete proofs are admitted.
