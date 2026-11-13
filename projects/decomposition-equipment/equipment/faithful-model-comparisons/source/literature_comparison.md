# Primary literature and inherited model comparison for original E3

Prepared 31 October 2026 for the E3 author and independent auditor. The scope is original E3, `Original_Completion_Contract_v0.1_VERBATIM.md`, lines 450–466. This is a bounded attribution and scope check against the already available primary source and accepted E1/E2 baselines, not an exhaustive novelty search or acceptance of the new E3 proof.

## Main conclusion

The finite-span machinery, contextual universality, normal functors, and coherent restriction choices are established infrastructure. The groupoid grade formula is elementary invertible transport, not a new categorical construction. The inherited `GraphSpanModel.md` already establishes a full witnessed, nonreconstructive virtual equipment with all finite functions vertically, full original-profile recovery, and genuine graph-path nonrepresentability. E3 should credit that work and add the explicit finite-groupoid graph-grade model, its witness-level restrictions and normal coherent comparison, the separate noninvertible model comparison, and the required typed tests. Merely repeating Span or its standard representability theorem would not meet the contract.

## Verified primary locators

G. S. H. Cruttwell and Michael A. Shulman, *A unified framework for generalized multicategories*, Theory and Applications of Categories **24** (2010), no. 21, 580–655. Inspected version: [arXiv:0907.2460v3](https://arxiv.org/pdf/0907.2460v3), dated 9 December 2010. Page numbers below are this PDF's printed pages, **not journal pagination**.

| Locator | Relevant baseline |
| --- | --- |
| Example 2.7, p. 12 | Span multicells, including identity-span empty source. |
| Definition 3.1, pp. 15–16 | Cell-natural transformations and their 2-category. |
| Definition 5.1, pp. 28–29 | Contextual opcartesianness and universal units. |
| Theorem 5.2, p. 29 | All finite paths representable exactly when the virtual structure comes from a pseudo double category. |
| Example 5.4, p. 30 | Span composites are pullbacks; units are identity spans. |
| Remark 5.8, p. 31 | Context-free universality is weaker. |
| Paragraph before Example 5.9, p. 31 | Normality preserves universal units coherently. |
| Definition 7.1 and Example 7.3, p. 37 | All-arity restrictions, coherent choices, span pullbacks. |
| Definition 7.6 and Example 7.7, p. 38 | Virtual equipments and the Span example. |
| Theorem 7.24 and following paragraph, p. 42 | Equipment functors preserve restrictions; unit preservation remains separate. |

The source PDF and extracted text are retained, unchanged, in `/workspace/shared/e1_equipment_core_20261031/references/cruttwell_shulman_0907.2460v3.{pdf,txt}`. The named sections were rechecked in that text and the versioned primary PDF was opened online. No additional literature search was needed.

## The groupoid restriction is an elementary specialization

Let `K` be a finite groupoid, `h:A→B`, `f:A'→A`, and `g:B'→B`. A grade `k:A'→B'` compatible with the boundary square satisfies

    g k = h f.

Since `g` is invertible, its unique solution is

    k = g^(-1) h f.

This is direct groupoid algebra. No claim is made that the primary source prints this particular graph-grade formula. The appropriate attribution is that it is the elementary invertible-boundary specialization of the standard restriction mechanism, with E3 responsible for the additional retained-witness proof.

For a source path with composite grade `q`, and further boundaries `u,v`, the required factorization equivalence is

    (g v) q = h (f u)    iff    v q = (g^(-1) h f) u.

The witness lift must retain the actual ordered graph partition and its scalar; the displayed equivalence only establishes its grade typing. Uniqueness must therefore be proved in those retained coordinates, including the empty-source case. Coherence of the grade choices is the elementary equality

    v^(-1) (g^(-1) h f) u = (g v)^(-1) h (f u).

The graph-grade equipment cannot acquire genuinely noninvertible vertical arrows merely by changing notation. For an arbitrary finite category, the same square need not have a unique graph grade, or any graph grade at all. An extension requires an explicitly supplied restriction envelope or the larger span universe. The inherited arbitrary-category **core embedding** is not a proof that the arbitrary-category graph-grade calculus is already a virtual equipment.

## Faithful realization is not a full Yoneda embedding

The inherited realization is

    F(A) = {(A,C,t) : t:C→A in K},
    F(h)(A,C,t) = (B,C,ht).

Ignoring object tags, this is the disjoint union over `C` of the covariant representables `K(C,-)`. Its faithful-representation argument is elementary: evaluating at `(A,A,id_A)` distinguishes parallel arrows. The tags distinguish interface names. For finite `K` the sets are finite; for groupoid `K`, each `F(h)` is a bijection with inverse `F(h^(-1))`.

This should not be called a fully faithful embedding into finite sets: `F` is generally not full, and arbitrary finite-set functions are additional vertical data. Nor does it recover the entire ambient finite-set category from the bare original core. Those qualifications are explicit in the inherited source, lines 160–175 and 208, and retained in accepted E2, `reconstruction_theorem.md`, §1 and §5.1.

The comparison on graph grades is

    (G,h:A→B) ↦ (G, Γ(Fh)),
    Γ(Fh) = (FA ←id FA →Fh FB).

For groupoid boundary maps, the ambient chosen restriction is a pullback-triple span, whereas the image of the graph-grade restriction is a graph span. Their apex sets need not be literally equal. The canonical comparison from the graph span to the pullback-triple span is

    x ↦ (x, Ff(x), F(g^(-1)hf)(x)).

Its inverse projects to `x`; the last coordinate is forced because `Fg` is bijective. Both retain the same graph, use the full unary graph block, and have scalar one. Iterated comparison maps agree by deleting the same forced coordinates. This is the explicit coherent comparison E3 should use, rather than asserting strict preservation of chosen pullback objects. Unit preservation still needs to be stated and checked; here the empty graph with identity grade maps to the empty graph with identity span.

## Exact inherited proof coverage

The following line references are to `/workspace/shared/contract_revision_20261028/structural_extracted/GraphSpanModel.md`, abbreviated SPAN.

| SPAN locator | Already proved content |
| --- | --- |
| Lines 11–35 | Finite graph bound, finite commutative scalar monoid, actual finite spans, and tuple regrouping including empty paths. |
| Lines 37–94 | All cell sets and substitution, with retained wholes, actual ordered partitions, witness functions, scalars, and shared vertical maps. |
| Lines 96–130, Theorem 4.1 | All-arity cartesian restriction along arbitrary finite functions, unique witness lifts, and coherent changes of choice. |
| Lines 132–156, Theorem 5.1 | Units universal in every surrounding context, not merely unit equations. |
| Lines 158–212 | Tagged faithful realization, exact original-profile fibre bijections, nullaries, and actual occurrence-refinement recovery. |
| Lines 214–222 | Three interfaces, repeated nonempty components, distinct refinements, different retained wholes, and nontrivial grade changes. |
| Lines 224–254, Theorem 7.1 and Corollary 7.2 | Actual graph-family representability obstruction and positive exact-cell classification. |
| Sections 8–9 | Nontrivial scalar factorization fibres and the noninvertible-middle-map witness-multiplicity calculation. |

These are proof-source locators, not a fresh global acceptance decision. SPAN's opening scope statement already disclaims stand-alone acceptance of E1–E5.

Accepted E1 further supplies the marked equipment/morphism/choice framework. In `e1_equipment_core_20261031/theorem.md`, §§4–5 distinguish normal functors, selected marking preservation, and coherent chosen comparisons; §9.1 distinguishes the normalized genuine exact marking `Ex_op^0` from the larger coefficient-only mark. Accepted E2, `e2_presentation_reconstruction_20261031/reconstruction_theorem.md`, §§2–5 supplies the reusable local presentation, full reconstruction, and original-profile comparison of this **same** witnessed graph/span model. Thus it is already doing substantive work in E2 rather than being an unrelated decorated example. E3 should point to that connection; it need not rerun E2 or claim E4 is thereby completed.

## The nonrepresentability belongs to the graph family

SPAN's obstruction is stronger than failure of a chosen finite composite: a path with at least two nonempty graph components has no weakly opcartesian cell. If its total vertices exceed `N`, there is no possible target. If its total vertices are at most `N`, choose two whole graphs with the prescribed induced input blocks, differing only by a cross edge. A purported universal target would need unary cells to both wholes. Unary graph cuts force equality of the complete graphs, giving a contradiction. This argument retains the unchanged horizontal-object universe and does not depend on a nonunit scalar, empty witness set, or absence of pullbacks.

It is **not** a nonrepresentability statement about standard `Span(FinSet)`. Its witness tuples do compose. The obstruction comes from the extra retained whole graph and its unary-cell condition. For `N≥2`, two singleton graph components already give a genuine cross-edge example over a one-point interface; the `N=1` failure is only the size-bound case. The full ordinary graph family, or the explicit cross-edge variability assumption, must be retained in the theorem. An arbitrary hereditary graph class need not satisfy that assumption.

For a path with at most one nonempty graph component, SPAN proves genuine contextual composites. Its intrinsic exact cells are precisely those with a bijective tuple map and an invertible scalar. Accepted E1 deliberately selects the smaller scalar-one exact marking. E3 must say which of these markings it uses: neither a bijective witness map alone nor scalar one alone makes a multi-nonempty graph cut opcartesian.

## Comparison claims that must remain distinct

1. **Core faithfulness.** The inherited graph-span comparison is bijective on each complete original identity-boundary profile. It also reflects each occurrence-indexed refinement entry and the refinement equation. This is not fullness on arbitrary ambient horizontals or arbitrary vertical maps.
2. **Restriction and unit comparisons.** Preserve the universal properties and exhibit the concrete comparison isomorphisms. Do not replace coherent comparison by equality of differently encoded apex sets.
3. **Forgetting witnesses.** Any comparison to a posetal relation must identify exactly what it forgets. Distinct ordered cuts, scalar labels, apex functions, or whole graphs must not silently become equality in the source. Retaining this loss analysis is why a posetal model alone does not pass E3.
4. **Exactness.** An explicitly declared exact marking and intrinsic opcartesianness are different assertions. Forgetting graph/scalar data can send a nonuniversal graph-cut witness to a universal span cell. Consequently exactness reflection requires its own proof and is not a consequence of normality.
5. **Independent requirement.** Full finite spans supply noninvertible vertical maps. Groupoid transport alone does not. The already witnessed ambient graph/span model may be reused, but the contract still needs the actual primary groupoid model and comparisons to be stated.

## Verification record and stopping condition

This bounded pass checked the original E3 clauses, the named primary definitions/examples/theorems, the inherited graph/span proof, the accepted E1 marking distinction, and the accepted E2 reconstruction/core comparison. It did not search for unrelated literature, mutate inherited artifacts, upload files, certify the new model proof, or begin E4/E5.

Source custody checks:

- CS versioned PDF SHA256: `dba00051473c5d172078b8dcf680bb3ffd7399641374a80e61e9c7eb5138c27d`.
- SPAN SHA256: `e60be747d342fab54276900cb810ff9d9648384cb983bfe1357659838cbf4a7c`.

**Status:** bounded comparison complete. **Blockers:** none. **Action target:** the E3 author and independent auditor should use these locators and preserve the stated distinctions in the new model/comparison theorem and typed evidence. This note does not itself change E3 acceptance status.
