# Contextad constructor formalization

Lean 4.35.0, mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
# Set MATHLIB_CACHE_DIR to a writable directory if the default home cache is read-only.
export MATHLIB_CACHE_DIR="${MATHLIB_CACHE_DIR:-$PWD/.lake/cache}"
lake exe cache get Mathlib.CategoryTheory.Monad.Kleisli Mathlib.Algebra.Group.Defs Mathlib.CategoryTheory.Types.Basic Mathlib.CategoryTheory.Comma.Basic Mathlib.CategoryTheory.Discrete.Basic Mathlib.CategoryTheory.Localization.Predicate Mathlib.CategoryTheory.Comma.StructuredArrow.Basic Mathlib.CategoryTheory.Products.Basic
python3 verify.py
```

Read `SOURCE_CROSSWALK.md` before using the declarations as evidence for a manuscript. This package supplies constructor-level verification of fixed effects, the supplied-law mixed category, Type reader/writer transpositions cartesian-Type Para, terminal-fibre comma recovery, general-grade factorization localization, exact primitive-balance localization, and the fixed-target equivalence of independent source cocones with primitive-inverting and comma functors, not a certificate for the whole relative construction or contextad programme. `AxiomAudit.lean` audits every indexed theorem and construction in `TheoremIndex.json`; no project axioms or incomplete proofs are admitted.

The source cocone comparison now derives arbitrary-cocone extension functor laws, product/balance recovery and essential surjectivity from the independent source relations. It gives a categorical equivalence for fixed extension functors and fixed target category. Target-change compatibility is supplied by actual postcomposition functors, target natural transformations, coherent comparison squares in both directions, and compatible explicit unit/counit data. A second presentation equivalence uses the explicit extension inverse and a directly proved triangle. Endpoint lift data now induce actual factor/comma transports with identity/composition/associativity comparisons, compatible weak-choice isomorphisms, the specific primitive section balance, and localized normalization/section squares. These are unbundled local endpoint interfaces, not an installed global indexed weak-cleavage pseudofunctor; coherent descent of all chosen-localization routes and iterated tensor/multiplication coherence remain open.

Endpoint–target interchange is proved for the explicit independent-cocone pullback obtained by restriction of endpoint transport followed by the derived extension. The natural target square respects target identity/composition, endpoint identity/composition comparisons, weak-choice changes, and extension recovery. Global indexed-cleavage packaging and coherent localization descent remain separate.

The previously chosen primitive-localization transports now have explicit descended identity/composite/weak-choice isomorphisms, exact component formulas, vertical choice laws, and two unit plus triple-associativity equations. These retain actual localization factorization isomorphisms. Full indexed-cleavage and horizontal weak-choice/pentagon packaging, coherence of all normalization/section squares, and iterated tensor/multiplication remain separate.

The existing endpoint-data choices now support derived horizontal whiskering/composition, vertical interchange, canonical unit/associator naturality and pentagon/triangle equations. Their selected-localization images and the localized compositor's horizontal naturality retain actual comparison maps. This is not an installed global indexed cleavage or bundled bicategory/pseudofunctor, and it does not assert coherence for arbitrary independently supplied cleavage constraints.
