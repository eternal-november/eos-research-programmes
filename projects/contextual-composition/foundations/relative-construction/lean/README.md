# Contextad constructor formalization

Lean 4.35.0, mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
# Set MATHLIB_CACHE_DIR to a writable directory if the default home cache is read-only.
export MATHLIB_CACHE_DIR="${MATHLIB_CACHE_DIR:-$PWD/.lake/cache}"
lake exe cache get Mathlib.CategoryTheory.Monad.Kleisli Mathlib.Algebra.Group.Defs Mathlib.CategoryTheory.Types.Basic Mathlib.CategoryTheory.Comma.Basic Mathlib.CategoryTheory.Discrete.Basic Mathlib.CategoryTheory.Localization.Predicate Mathlib.CategoryTheory.Comma.StructuredArrow.Basic Mathlib.CategoryTheory.Products.Basic
python3 verify.py
```

Read `SOURCE_CROSSWALK.md` before using the declarations as evidence for a manuscript. This package supplies constructor-level verification of fixed effects, the supplied-law mixed category, Type reader/writer transpositions cartesian-Type Para, terminal-fibre comma recovery, general-grade factorization localization, exact primitive-balance localization, and the fixed-target equivalence of independent source cocones with primitive-inverting and comma functors, not a certificate for the whole relative construction or contextad programme. `AxiomAudit.lean` audits every indexed theorem and construction in `TheoremIndex.json`; no project axioms or incomplete proofs are admitted.

The source cocone comparison now derives arbitrary-cocone extension functor laws, product/balance recovery and essential surjectivity from the independent source relations. It gives a categorical equivalence for fixed extension functors and fixed target category. Global endpoint pseudonaturality, cleavage comparison and iterated tensor/multiplication coherence remain open.
