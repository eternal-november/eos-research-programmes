# I4 direct baseline comparison

31 October 2026. Independent literature comparison, not a mathematical acceptance certificate. Inputs: exact Original_Completion_Contract_v0.1_VERBATIM.md, I4; theorem_candidate.md (including §3B semantic refinement correction). The original floor requires direct comparison, an equivalent criterion in a declared class, all-tree extension, frozen output and P+C; a generic operadic incidence citation does not discharge it.

## 1. Verified primary-source baseline: Baez–Dolan/free operad

Joachim Kock, *The incidence comodule bialgebra of the Baez–Dolan construction*, arXiv:1912.11320v2 (30 March 2021), [primary text](https://arxiv.org/html/1912.11320v2), Theorem 3.2.1: the free-operad bar incidence bialgebra is a left comodule bialgebra over the Baez–Dolan bar incidence bialgebra, objectively on groupoid slices. §§2.1–2.2 distinguish leaf grafting from node substitution. Lemma 2.1.4 explicitly decomposes active refinements nodewise; §2.1.5 gives active–inert refactorization. Lemma 3.2.3 and §§3.2.4–3.2.7 prove coproduct compatibility by pullbacks, with counit compatibility in Lemma 3.2.8. Thus coherent cut/substitution compatibility, supplied decorations, and occurrence-sensitive refinement already belong to this baseline.

The operads of §1.6.4 are coloured symmetric operads, represented by polynomial monads; §1.5.5 includes planar trees through the list monad. Crucially §3.2.7 uses node-indexed, not linearly ordered, forest monomials. Its equality cannot license exchange of a planar input word. Section 4 supplies the reduced, locally finite repair: one cannot simply take homotopy cardinality of the unrestricted theorem.

**Direct mapping to this candidate (analysis).** The old tree/forest data correspond to decorated operadic occurrence data, not to a new replacement for them. The candidate's `Xi_old K_rows = K_columns Xi_new` has the same structural role as a cut/refinement compatibility, but its arrows are specified finite coefficient functions in the opposite direction to refinement, not the incidence spans of Theorem 3.2.1. Consequently neither construction is literally identified with the other by the present proof. A comparison functor preserving the relevant structure has not been constructed. In particular, the candidate must not advertise its concrete double category as a new comodule theorem or claim that the established comodule gives its pointwise invertibility criterion automatically.

## 2. Verified primary-source baseline: directed hereditary species

Alex Cebrian and Wilson Forero, *Directed hereditary species and decomposition spaces*, [arXiv:2211.07721v2 primary text](https://arxiv.org/html/2211.07721v2). Definition 2.3 requires a contraction to be monotone surjective, have connected convex fibres, and lift covers. Lemma 2.6 proves pullback stability along convex maps. Definitions 2.7 and 2.9 encode a connected directed hereditary species as a groupoid-valued functor on partial contractions: covariant for contractions, contravariant for convex maps. The nonconnected extension is in §9.

Section 7 supplies the cut/contraction comparison: Lemma 7.6 proves coproduct compatibility using chains consisting of a contraction followed by a cut, with pullback squares; Lemma 7.7 handles the counit; Proposition 7.8 concludes a left comodule bialgebra. Section 7.10 compares its rooted-tree example with Kock's reduced Baez–Dolan construction via tree cores. This is already an explicit mixed compatibility theorem, not merely two unrelated incidence structures. Poset direction and convexity are not a planar total ordering of every frontier; groupoid-valued structures retain isomorphisms. Version note: older search-indexed text calls the comodule result Proposition 7.7; **v2 uses Proposition 7.8**.

**Direct mapping to this candidate (analysis).** The candidate's induced restrictions and contractions resemble the two variances of a hereditary species, but the finite span-apex maps and arbitrary interface functions are different input data from the required contraction/convex maps. To derive the candidate from this theorem would require exhibiting a species on those partial contractions, verifying its functoriality and matching its cut records. The candidate does not do this, and it should not pretend that any arbitrary graph witness decoration is thereby admissible. Conversely its fixed ordered graph partitions need not supply the connected convex fibres or cover lifting needed to invoke that source. No equivalence or generalization of directed hereditary species is established here.

## 3. Precisely what the candidate additionally specifies

These are differences in the **question and supplied data**, not proofs of historical novelty or scientific significance.

| Candidate datum/result | Exact extra obligation in this manuscript |
|---|---|
| O, typed named frontier | Decide whether row/column intersections produce the *same ordered occurrence word*, including grade arrows, interfaces and retained empty slots. A crossing is nonparallel, not an invertible symmetry or a failed function. |
| Supplied proper certificates beta | Construct `k_v = beta_v P(k_children) (beta'_v)^(-1)` and the conjugated flattening map Xi between the **fixed actual carriers**, not merely establish that some equivalent factorization exists. |
| W versus W_sem | A raw presentation forest retains primitive stages; original B3 semantic arrows retain each evaluated occurrence operation with its segmentation, not a primitive factorization. Per-stage fibre-one tests are exact only for staged retention. W_sem counts fibres of each evaluated original occurrence map; neither may be replaced by a root-only test. |
| B | For each requested run, the lax change-of-interface comparison forgets internal lifts; its fibre cardinality is the product of the internal lift cardinalities. At arity zero the diagonal into `A' ×_A A'` instead requires injectivity. All requested runs, not only adjacent pairs, must be tested. |
| R and quotient choice | Availability of the fixed actual tables is separated from existence of an intrinsic orbit comparison. Multiple actual lifts mean undetermined actual comparison, not automatically noninvertibility. |
| Units/scalars | Ambient unit scalar inverses and the normalized scalar-1 action are different conclusions; no arbitrary monoid decoration is certified cut-compatible. |

The theorem's iff is therefore about a deliberately large **retained diagram**. Its necessity partly follows because every tested map is a component of that diagram. The independent cut-change Xi itself may be invertible even while W or B fails elsewhere. This distinction is mathematically legitimate only if explicitly preserved in the final claim; it is not a characterization of invertibility of Xi alone.

The singleton → two-point → singleton example is essential: its composite is bijective while neither stage is. It refutes an attempt to assign per-stage necessity to the original semantic refinement. The candidate §3B repairs precisely that issue. Similarly, coefficient isomorphism does not invert the forest-bearing arrow: the construction must retain its stated variance and evaluation distinction.

## 4. Generic double-category baseline

Grandis–Paré, *Limits in double categories* (1999), [primary paper](https://www.numdam.org/article/CTGDC_1999__40_3_162_0.pdf), §1.1 specifies the two categorical compositions and interchange. The introduction, p.164, already gives structured maps with commuting squares as cells. This is the appropriate ordinary baseline, not a claim that the candidate has invented double categories.

Here is the direct elementary comparison, independently of that citation. For a category C, objects and arrows of C with commuting squares form the square double category. Pasting is composition; middle-four interchange follows from associativity and equality of the resulting boundary composites. Likewise, restricting a natural transformation to surviving tree edges commutes with its componentwise composition. The candidate's equation `restriction(l k) = restriction(l) restriction(k)` is this standard mechanism. Forest labels and exact-cut restrictions require a genuine *closure and typing* proof, but adding such labels does not make the general interchange mechanism novel. Its useful content, if validated, is that these specific beta-certified objects, actual labelled forest arrows and contractions are closed under the claimed operations, with the rejected crossing inputs still absent.

## 5. Monotone-coupling baseline and the original quotient theorem

Theorem B's interval-intersection formula is the finite atomic monotone/quantile coupling, also known algorithmically as the northwest-corner construction. The following elementary proof identifies the baseline without relying on a bibliographic novelty inference. Given row and column masses with cumulative totals a_p and b_q, a joint table supported on a product-order chain must have cumulative northwest mass `min(a_p,b_q)`: a smaller value forces positive mass in both opposite off-diagonal rectangles, violating chain support. Double differences then force every cell. Equivalently couple the two cumulative interval partitions of `[0,total)` by their overlaps. This proves existence and uniqueness for each individual pair of one-dimensional marginals. No atomless hypothesis and no uniqueness of a Monge map is being claimed.

The candidate applies that construction **separately to each clique** and adds the necessary union-of-supports chain condition across cliques plus the full O type check. This is an elementary multicolour compatibility test, not a new monotone transport uniqueness theorem. Its application-specific obligation is the F3 quotient and B3 occurrence-arrow connection: the occupancy table must be a complete orbit invariant for the stated group, valid original cut representatives must exist, and equalities must hold for the full occurrence tuples rather than only their composite. These are not consequences of the marginal formula by itself.

The K2 example isolates the boundary correctly: two fixed labelled cuts in reverse order have no named planar common refinement, while their identical occupancy orbits admit the diagonal table. Orbit existence does not choose a valid common refinement of the *prescribed* representatives. This is a quotient/representative distinction, not an inferred planar permutation.

## 6. Assessment and residual blockers

The candidate properly reuses, rather than supplants, standard decorated operadic substitution, objective cut/refinement compatibility, commuting-square double-category pasting, finite fibre bijectivity and monotone coupling. The potential contribution left for review is the **combined exact criterion on the explicitly chosen actual/orbit graph-span doctrine**, its truthful semantic-versus-staged refinement handling, and its interface-lift and normalized-decoration boundaries.

This comparison meets the requested direct-baseline research step but does not certify I4 acceptance. In particular:

1. The sources do not validate the candidate's exact fixed-carrier diagrams or prove their closure; independent proof review must check those statements.
2. No structure-preserving comparison functor to either literature construction has been supplied. Do not claim one or count a new comodule result.
3. A scientific-scope reviewer must decide whether the combined model-specific compatibility has enough substance beyond its elementary component mechanisms. Absence of this exact formulation in the checked sources proves no novelty.
4. The original contract additionally requires C evidence and non-author acceptance. This literature note neither substitutes for them nor changes the frozen output.

External work was read-only. No external mutation occurred.
