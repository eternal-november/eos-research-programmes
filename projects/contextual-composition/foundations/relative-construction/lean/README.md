# Contextad constructor formalization

Lean 4.35.0, mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake exe cache get Mathlib.CategoryTheory.Monad.Kleisli Mathlib.Algebra.Group.Defs Mathlib.CategoryTheory.Types.Basic Mathlib.CategoryTheory.Comma.Basic Mathlib.CategoryTheory.Discrete.Basic Mathlib.CategoryTheory.Localization.Predicate
python3 verify.py
```

Read `SOURCE_CROSSWALK.md` before using the declarations as evidence for a manuscript. This package supplies constructor-level verification of fixed effects, the supplied-law mixed category, Type reader/writer transpositions cartesian-Type Para, terminal-fibre comma recovery, general-grade factorization localization, and exact primitive-balance localization, not a certificate for the whole relative construction or contextad programme. `AxiomAudit.lean` audits every indexed theorem and construction in `TheoremIndex.json`; no project axioms or incomplete proofs are admitted.
