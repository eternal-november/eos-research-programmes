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

The existing localized normalization comparison and a section comparison using the chosen localized transports now satisfy actual identity/composition/weak-choice equations, with component formulas retaining all factorization isomorphisms and the source-lift balance. Compatibility with source-cocone target routes and global indexed-cleavage/iterated composition structure remains separate.

the actual packaged equivalence counit and its adjointified unit now satisfy the endpoint comparison equations in `EquivalenceCoherence.lean`. This discharges that specific residual without changing the equivalence or either endpoint square. Independent fresh own-source replay passed all 359 indexed declarations using pinned cached dependencies; source-cocone/target-route compatibility, global indexed cleavage, and iterated composition remain separate.

The chosen-localization functor presentation now has a forward comparison with independent cocones that respects endpoint identity/composition/compatible choices, target identity/composition and transformations, and the previously defined endpoint–target interchange. The independently replayed package has 375 indexed declarations; dependency binaries were reused. It does not yet give recovery-map modifications for that composite equivalence or identify every comma/normalization route; global indexed cleavage and iterated composition remain separate.

The independently reviewed 387-declaration package derives the inverse endpoint and target squares for the actual composite localization-to-cocone equivalences. Their actual unit and counit satisfy the two recovery equations for each individual change. The counit equation determines the inverse transformation uniquely. Inverse-square composition/interchange and compatibility with distinct comma/normalization routes remain separate.

The independently reviewed recovery-modification module proves that the actual inverse recovery squares respect compatible endpoint choices and arbitrary transformations between target functors. It also proves a general vertical-pasting law for transformations between parallel transports. This differs from pasting successive transport functors; inverse transport identity/composition and mixed endpoint–target interchange remain open.

The independent #105 telescope branch starts with discrete spans over arbitrary discrete state types. Finite chains retain every actual endpoint-indexed grade. The package proves substitution unit/associativity, the payload-natural length-tagged comparison with sequential extension iterates, the distinction between length-one and length-zero units, and compatibility of categorical arrow accumulation with flattening. This is not the full split-fibrant Cat-valued or strict Tel-algebra theorem.
Independent statement review and isolated own-source replay passed for this specialization (442 distinct indexed declarations; dependency binaries reused).

TelescopeMorphisms now equips the original finite chains with actual morphisms from arbitrary categories of grades at each pair of discrete base states. Singleton is fully faithful on grade arrows, flattening is a functor, and the two telescope unit laws and triple substitution hold on morphisms after the original object identifications. This does not yet extend the coproduct-of-iterates equivalence to Cat-valued payloads or introduce nontrivial base reindexing.

The Cat-valued telescope extension candidate proves the length-tagged comparison on actual grade and payload morphisms at each discrete base state. The two comparison functors are inverse as functors and commute in both directions with arbitrary families of payload-change functors. This is not the general split-fibration theorem over a nondiscrete base.

The discrete-base telescope comparison now respects arbitrary families of natural transformations between payload-change functors. Both directions commute as functors on the parameter hom-category. One starting state detects precisely the components at the endpoints of its actual chains; all starting states together detect every component through empty chains. No nondiscrete base reindexing is inferred.
Independent scoped review passed; see evidence/telescope-payload-cells-independent/REVIEW.md and its fresh own-project build and 543-declaration axiom audit. The nine pinned dependency build caches were reused.

The reviewed #105 tranche proves the telescope extension comparison as an isomorphism of Type-valued presheaves on an arbitrary base category with selected split one-step grade lifts. A concrete base arrow changes an inhabited successor to an empty one, and a second test distinguishes induced payload maps even with identical successor types. This does not combine the earlier discrete-base Cat-valued theorem with arbitrary base reindexing.

Independent review passed for the bounded Type-valued reindexing result. See evidence/telescope-reindex-independent/Independent_Telescope_Reindex_Review.tex and the fresh build/audit logs there. Dependencies were cached. The general categorical and strict-algebra obligations remain open.

For one Grothendieck extension step, joint reindexing now preserves native grade and payload arrows over a nondiscrete base. A payload map into a reindexed target, rather than a map between unrelated successor fibres, is essential. This derives single-base-arrow restriction as a functor; coherence of successive outer restrictions and the all-length categorical telescope comparison remain open.

Independent evidence: `evidence/grothendieck-step-independent/Review.tex`, fresh project build and 629 declaration audits.

After #172, GrothendieckCoherence derives a Cat-valued one-step extension presheaf from split endpoint comparisons; see the final SOURCE_CROSSWALK section for the direction of pasting and the strictness boundary. Fifteen new exports (644 total), author and independent replays passed.

Independent scoped pass: see `evidence/grothendieck-coherence-independent/Review.tex` and adjacent fresh project replay records (cached external dependencies).

GrothendieckIterates constructs the length-graded presheaf of finite iterates for each fixed Cat-valued payload, with recursive native hom decoding, restriction and a depth-two dependent witness. This is the right-hand construction of eq:telescope, not yet the comparison. See the final source crosswalk and scoped evidence. Independent scoped pass: see `evidence/grothendieck-iterates-independent/Review.tex` and the adjacent isolated project replay (664 indexed audits; cached external dependencies).

TelescopeSquares builds payload-independent chains, their squares over arbitrary base maps, and the terminal endpoint map. It proves object and hom-type comparisons with the iterates, not yet a categorical equivalence. 683 indexed declarations; separate review pending.

Independent scoped pass: see `evidence/telescope-squares-independent/Review.tex` and adjacent fresh own-project replay (683 distinct audits; cached external dependencies). Independent chain-square identity and composition, and comparison preservation of both, remain open.

SquarePasting constructs independent finite-chain identity/pasting and proves preservation by the terminal endpoint map. Only head and zero-length comparisons are claimed, not categorical equivalence. Independent scoped pass: 702 audited declarations; see evidence/square-pasting-independent/Review.tex.

TailPasting verifies arbitrary-length tail transport and a full length-one composite in the dependent-sum model. General tail recursion is distinguished from full outer composition equality in the final source crosswalk. Independent scoped pass: 713 indexed declarations; see `evidence/tail-pasting-independent/Review.tex`.
