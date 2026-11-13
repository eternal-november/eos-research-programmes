# Independent review: typed cover descent and mixed presentation criterion

29 October 2026. Non-author adversarial proof review, with independent finite checks. This is AI review, not Lean or external human verification.

## Plain-language verdict

The two notes support a correct conditional construction: when several descriptions retain the same component types and ordered positions, an explicit relation test tells whether compatible descriptions determine one joint *equivalence class* of witnesses. The construction respects the supplied assembly operations. Extra tests allow supplied cuts and interface operations to descend. It does not automatically find an original witness, lift a refinement between prescribed original endpoints, or make the original crossing-decomposition contract complete.

The proof has been reconstructed independently. Two precision defects were reported and corrected. No remaining mathematical counterexample to the stated conditional theorems was found. The principal remaining limitation is substantive, not a hidden proof bug: an actual unbounded original-presentation application with genuine crossing still needs to be established.

## Reviewed versions

- `main/Typed_Cover_Descent.md`, SHA256 `2d378380df291c14a3ff5774386955748b8951161a0edba70e599011888b1605`.
- `main/Mixed_Presentation_Criterion.md`, SHA256 `cc4354295e9117f70fd1997b738470f69022a7c4d4c0bab5e2cdf42d03272e5e`.
- Contract audit `audit/Contract_Reconciliation.md` and exact boundary source/checker.

Later substantive edits require renewed review; hashes identify this review's scope.

## 1. Reconstruction proof

For a fibre W, injectivity of the comparison from W/intersection(E_i) is immediate and uses no surjectivity. To prove hereditary surjectivity from CR, reconstruct a subtuple at a and represent its additional coordinate at b. The overlap conditions give a in each join relation with b; CR yields a simultaneous adjustment c. Conversely, the tuple using a on S and b at j is pairwise compatible whenever the right-hand CR relation holds, so its realization proves the reverse inclusion. This verifies the exact stated quantifiers: all nonempty subfamilies, all outside added views, every operation fibre.

A full-cover-only theorem would be false with these quantifiers. The identity-view masking example correctly isolates that distinction. No permutability assumption is needed for the exact criterion. The sufficient distributive/permutable lattice subclass correctly includes the generated meets, not just pairwise commutation of the named kernels.

Componentwise substitution preserves the overlap equations because the overlap maps are quotient calculus morphisms. Therefore the comparison is a calculus morphism; its bijective fibre maps make its inverse a calculus morphism. Arbitrary finite substitution diagrams follow without choosing representatives. This is a valid identity-on-base result: full profiles, root component, occurrences, order, and nullary profiles are supplied anchors. It does not infer those anchors.

## 2. Refinements and witness recovery

The semantic refinement theorem reconstructs Ref(M/K), where K is the common kernel. The exact forest equation can be checked after the injective comparison because all quotient views agree on it. This is not Ref(M) with arbitrary fixed endpoint representatives. The text now correctly keeps that distinction and retains the actual equation fibre.

The max-monoid counterexample refutes unconditional fixed-endpoint lifting. The class-image condition c_a([u])=[c_a(u)] is precisely the additional condition needed. Its generator certificate is valid: each target zigzag edge lifts within the current forest class, so finite iteration stays in the original class. Composition of saturated congruent maps is valid on matched domains; partial maps require domain saturation. Shared forest parameters belong to the joint domain U. Independent slotwise tests do not establish reconstruction of U or solve a crossing diagram.

The Z/4 to Z/2 example independently refutes a substitution-preserving section despite nonempty fibres and saturated fixed-outer translations. These are distinct limitations. Keeping pairs (quotient class, actual witness) is a faithful repackaging of M, not an algorithm discovering the witness from quotient data.

Nullary clauses correctly distinguish a true singleton forest domain from an empty horizontal forest carrying variable common vertical boundary data. Saturation for a singleton domain forces the target class singleton; the claim is not extended to a varying-boundary domain.

## 3. Cut, partial-domain and transport checks

Domain saturation plus output congruence is the appropriate forward descent condition for a deterministic partial operation. Meets and joins preserve this condition: along every join chain, availability remains fixed and output coordinates remain related. Typed intermediate profiles must be retained along those chains.

The isomorphism of partial structures follows because all views reflect domain membership, and joint reconstruction supplies a representative for a compatible tuple. This transfers existing mixed identities; it does not prove those identities for an independently presented calculus.

Two review corrections are now incorporated:

1. The reverse implication from related cut outputs to related roots requires exact reassembly, subst(cut(a))=a. Substitution congruence alone does not supply it for an arbitrary designated partial operation. The corrected note states this explicitly.
2. Restriction to diagonal points {00,11} only shows that retaining the old overlap yields false compatibility; recomputed pullback overlaps actually reconstruct. The corrected note adds the L-shape {00,01,10}. Its row/column join is total but row1/column1 has no witness, so this is an actual failure of reconstruction after recomputing overlaps.

Surjective maps preserve inverse-image joins and relational composition by lifting intermediate witnesses. Non-surjective restrictions need their own checks. This does not establish cartesian equipment exactness merely from a bare map.

## 4. Mixed-presentation proof

The domain algebra makes domain equality propagate through constructor contexts. At a root equation, symbolic residual equality can be instantiated with the actual residual outputs of the identical substitution. Surrounding-context induction, simultaneously for all reachable residual states, then propagates this equality. A finite equation zigzag finishes the proof. Subsequent composite operations preserve domain reflection and output equivalence by computation induction.

The distinction between sufficient and necessary is correctly made. Independent symbolic variables for different residual outputs can impose stronger requirements than correlated actual outputs. Failure of the symbolic test is not a semantic impossibility theorem. Also a finite number of proof obligations does not imply decidable presentation equality; the note requires proof certificates or a separate normalizer.

The typed-path example genuinely treats unbounded path length through integer-indexed schemes. Associativity is controlled by interval intersections, unit equations by zero-length intervals, and edge equations by a positional case split. Cuts retain empty factors and their named vertices. It is a credible unbounded calibration, not a genuine nonlaminar crossing example or an application to original C5. Nodewise class-image saturation only lifts trees with independent branch data; shared-variable crossing compatibility remains additional.

## 5. Independent computation

I re-ran `tests/check_reconstruction_boundaries.py`: PASS, 711 pairwise-permutable triples, 705 successful and 6 failed reconstructions; all 610 congruent finite factor-map generator checks pass.

I additionally wrote and ran `review/check_hereditary_crt.py`, independently implementing partition generation, relation joins, compatible-tuple realization, and CR. It checks **all 3,375 triples** of equivalence relations on four points, including nonpermutable triples. Hereditary reconstruction and the full CR family coincide in every case; 705 pass. It separately verifies the three-point L-shape failure. Exact output is `review/check_hereditary_crt.json`. These exhaustive small checks support, but do not replace, the general proofs.

## 6. Contract and significance gate

The two notes do not discharge original F3 or I4. Their own limitation statements are correct and should survive into the report abstract and acceptance ledger, not merely an appendix. CRT and structural-recursion congruence descent are standard ingredients. The typed integration and explicit original-refinement fibres are useful framework bookkeeping, but the following substantive work remains:

- Concrete kernels and a verified residual table for the original unbounded C5 mixed cut/graft/interface presentation, or a separately justified model comparison.
- Genuine crossing positive reconstruction with named occurrence correspondences, not a silent row/column permutation.
- The original mixed comparison and its invertibility criterion; descent alone is not invertibility.
- Joint equation-domain lifting where shared parameters couple branches, not independent object/slot lifting.
- Any groupoid version, unknown-profile/whole discovery, or efficient certificate claim requires further results.

Thus the recommendation is **accept the stated conditional tools and corrected boundary results as mathematically supported; do not mark the promised general crossing target or original contract obligations complete on these notes alone**.

Reviewed addendum: the explicit parallel-edge relabeling h(a)=h(b)=a with a R b correctly demonstrates descent without class-image saturation within the positive path class itself. The extended seven-scheme discussion is a provenance pointer, not a claimed residual-table verification.
