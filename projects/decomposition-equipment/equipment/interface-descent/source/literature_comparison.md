# D2–D3: bounded comparison with standard transport and descent

31 October 2026. Scope: the original completion contract, D2–D3, lines 382–412 of `../contract_revision_20261028/final_artifacts/Original_Completion_Contract_v0.1_VERBATIM.md`. This is a primary-source comparison, not an acceptance certificate or an exhaustive novelty search. All page numbers below are **printed pages of the linked, versioned PDFs**. The relevant PDF text was inspected directly.

## 1. Conclusion and attribution boundary

The mechanisms needed here are established: inverse image and existential composition; pullback/dependent-sum base change; category-of-elements constructions; weak pullbacks retaining seam isomorphisms; and action groupoids retaining stabilizers. They should not be presented as new descent constructions.

The task-specific result is instead a checked application to **the actual presented C5 witness family and B3 occurrence-refinement arrows**, including its equations, empty/nullary cases, and all-tree compatibility. Standard descent cannot supply an interface action on primitive witnesses that has not been defined, cannot make a non-invariant equation invariant without changing the quotient, and cannot identify a semantic refinement arrow with a chosen primitive-stage factorization.

The earlier `../original_mixed_criterion_20261029/main/KernelPair_Provenance_Repair.md` is already an explicit groupoid-valued repair. Reusing it is appropriate, but it is a changed semantic doctrine and must not be counted as a new discovery in D3 or silently substituted for the original discrete-span theory.

## 2. Verified primary-source anchors

### 2.1 Ordinary base change: equality is not the same as witness bijection

Nicola Gambino and Joachim Kock, *Polynomial functors and polynomial monads*, [arXiv:0906.4931v2](https://arxiv.org/pdf/0906.4931v2).

- §1.1, p. 5: pullback `Δ_f`, dependent sum `Σ_f`, and dependent product `Π_f`, with their adjunctions and indexed-family formulas.
- §1.2, p. 5: Beck–Chevalley **isomorphisms for a cartesian square**; pp. 5–6 distinguish distributivity.
- §1.12, pp. 8–9: composition of polynomial functors using those isomorphisms.

This supplies the ordinary change-of-base baseline. It does **not** say that an arbitrary comparison arising from three unrelated interface maps is invertible. For D2 the displayed comparison must be calculated; its exact fibres determine what is true. In particular, the source's cartesian-square hypothesis cannot be replaced by an unqualified appeal to “Beck–Chevalley.”

### 2.2 Homotopy pullback and retained symmetry

Joachim Kock, *Data types with symmetries and polynomial functors over groupoids*, [arXiv:1210.0828v1](https://arxiv.org/pdf/1210.0828v1).

- §2.1, p. 5: homotopy slices and limits, unique up to equivalence.
- §2.2, p. 6: the explicit pullback objects `(x,y,φ)` with `φ:f(x)→g(y)`; morphisms are pairs satisfying the seam square. Ordinary pullback is equivalent to this model when one leg is a fibration.
- §2.3, pp. 6–7: action-groupoid/homotopy quotients; the example `1/G` retains the vertex group `G`; decomposition into homotopy fibres with automorphism actions.
- §2.5, p. 8: homotopy Beck–Chevalley gives **natural equivalences**.
- §2.7, p. 8: spans of groupoids as a special case of groupoid polynomials.

These are direct baselines for retained seam certificates and stabilizers. Nothing in these constructions identifies a graph partition, coefficient witness, or local scalar merely because its image under evaluation agrees with another's.

### 2.3 Explicit equivalence and reassociation, not unspecified coherence

John C. Baez, Alexander E. Hoffnung, and Christopher D. Walker, *Higher Dimensional Algebra VII: Groupoidification*, [arXiv:0908.4305v3](https://arxiv.org/pdf/0908.4305v3).

- Introduction, p. 3: action groupoid of a group acting on a set.
- Proposition 43, pp. 53–55: reassociation of weakly composed spans. The object formula appears on p. 54 and the morphism/inverse verification on p. 55. For the chosen models the apex reassociation is an **isomorphism**; the proposition is framed as equivalence of spans.
- Appendix A, Definitions 56–59, p. 59: equivalence and the fully-faithful/essentially-surjective criterion.
- Lemma 65, pp. 62–64: equivalent cospans have equivalent weak pullbacks, with an explicit functor and verification of all three properties.

This supports the standard comparison mechanism. Proposition 43 alone is not a proof of the candidate's arbitrary-tree equations: the candidate must specify its actual records and show that every route in its coherence diagrams has the same coordinate action. Finite groupoids fall within the cited setting; no cardinality theorem is needed for the proposed descent result.

### 2.4 The refinement category need not be a groupoid

Mitchell Buckley, *Fibred 2-Categories and Bicategories*, [arXiv:1212.6283v2](https://arxiv.org/pdf/1212.6283v2), §1.1, p. 4.

The ordinary Grothendieck construction is recalled before the higher-dimensional results: a contravariant `Cat`-valued pseudofunctor gives a category of elements with objects `(a,x)` and arrows `(f,u)` where `u:x→F(f)y`. The covariant dual gives arrows `u:F(f)x→y`, as used for a transported refinement category. No higher bicategorical theorem from this paper is required here.

This is the correct generic baseline for `∫ Ref(P)`: its fibre refinements can be noninvertible. Calling that whole category a groupoid would lose part of B3. One may separately take its core or use set-valued witness families to obtain genuine groupoids.

## 3. Direct comparison of the three exactness levels

The following calculations are elementary analysis of the declared D2 data, not attributions of these exact criteria to the papers.

Let `R⊆A×B`, `S⊆B×C`, and `f:A'→A`, `g:B'→B`, `h:C'→C`. Put

`W(a',c') = { b∈B | R(f(a'),b) and S(b,h(c')) }`.

For fixed endpoints, composing the restricted relations asserts that `W(a',c')∩im(g)` is nonempty. Restricting the composite asserts only that `W(a',c')` is nonempty. Therefore:

- the first relation is included in the second;
- equality requires **some** available middle witness for each feasible endpoint pair, not that every old witness lift;
- surjectivity of `g` suffices uniformly;
- the uniform converse must allow `A'=∅` or `C'=∅`, when both relations are empty regardless of `g`.

This is an existential-support criterion in a hom-poset, where invertible inclusion means equality. It says nothing about retaining the number or identity of middle witnesses.

For actual spans `A←E→B←D→C`, with lifted endpoints fixed, the corresponding apex map forgets the lifted seam value:

`(a', e, b', d, c') ↦ (a', e, d, c')`.

Over a feasible old witness pair `(e,d)` with middle value `b`, the fibre is `g⁻¹(b)`. Consequently surjectivity gives coverage, whereas an apex **bijection** requires exactly one lift for every relevant old pair. Repeated original witnesses are distinct coordinates, even if they have identical endpoint values. A bijective comparison yields a span isomorphism, not literal equality of the two chosen apex sets.

The provenance repair changes this fibre to the thin groupoid on the possible names, with a unique arrow between names of the same old value. Such a fibre is empty or contractible. Thus nonempty multiple lifts cease to obstruct an **equivalence**, while absent lifts still obstruct it. The old witnesses themselves remain fixed by these arrows. This is different from merely quotienting their supports.

At arity zero, the old discrete comparison is the diagonal `A'→A'×_A A'`, so injection is a separate issue. The repair changes the identity doctrine: the relevant diagonal becomes an equivalence of groupoids, not a set bijection. It does not prove that noninjective changes strongly preserve the original discrete units.

These three conclusions must remain separately labelled:

| Doctrine | Data retained | Exactness test on a fixed relevant fibre |
|---|---|---|
| `Rel` | existence | at least one usable witness per feasible endpoint pair |
| actual `Span(Set)` | each old witness and lift | exactly one lift of each retained old witness tuple |
| provenance groupoids | old witness plus isomorphisms of lift names | nonempty contractible lift groupoid |

## 4. What the D3 application must check

For a strict D1 diagram `P:H→Calc` and its actual refinement diagram `Ref(P):H→Cat`, an equivalence `e:G→H` has the standard candidate comparison

`∫_G Ref(P∘e) → ∫_H Ref(P)`,

sending `(x,a)` to `(e(x),a)` and `(g,u)` to `(e(g),u)`. Its generic proof uses full faithfulness of `e` on the base-arrow coordinate and essential surjectivity together with transport on the fibre coordinate. Merely writing that formula does not establish that the following actual witness diagram exists.

The contract-specific checks are:

1. **Primitive data and equations:** define transport on the actual C5 generators, typed carriers and retained witnesses, and verify every defining equation. Descent of the existing quotient uses invariance; adding transported equations would define a potentially different quotient.
2. **Full B3 arrows:** transport the original occurrence-indexed tuple, its segmentation, and source/target equations. Preserve the actual semantic constituent operations; do not strengthen necessity to every stage of a selected primitive factorization.
3. **Composition and arbitrary trees:** write identity, substitution, contraction, and comparison maps on the records. Prove equality of the resulting coordinate maps, including nested and disjoint operations and empty slots, rather than invoking an unnamed higher coherence result.
4. **Quasi-inverse choices:** exhibit the counit/representative transports and the induced natural isomorphisms. Changing representatives must give the specified conjugated base arrow and transported refinement component, not arbitrary identification of witnesses.
5. **Actual principal model:** instantiate this action on a principal model admitted by C5; an arbitrary newly declared diagram whose arrows preserve everything by definition does not meet the application requirement.
6. **Repeated components:** a stabilizer of a repeated occurrence-indexed word is not permission to exchange its planar slots. Interface-carrier relabeling and occurrence permutation are distinct actions unless an interaction law has separately been supplied.

These are proof obligations inferred from the original contract and the chosen constructions, not claims that no literature contains broader results.

## 5. The precise set/groupoid limitation

A nontrivial finite group `H` gives the decisive calculation

`1 ×^h_(BH) 1 ≅ H_discrete`,

because its objects are the seam arrows of `BH` and its only morphisms come from identity arrows in the two endpoint groupoids. Taking isomorphism classes **after** forming this pullback yields the set `H`. Taking isomorphism classes **before** forming the ordinary set pullback yields a singleton. The resulting comparison forgets distinct seam certificates.

Likewise, in an action groupoid the automorphisms at a witness are its stabilizer. Replacing the groupoid by its orbit set keeps the orbit but removes these arrows. Thus D3 may establish invariance of orbit sets as a separate consequence of equivalence, while it must not describe orbit sets as preserving witness lifting, uniqueness, or refinement arrows. This is a limitation of this forgetful operation, not an impossibility of every imaginable set-valued encoding of arrow data.

The thin kernel-pair provenance groupoids and these nontrivial stabilizer groupoids solve related but different bookkeeping problems. The former identify duplicate names of the **same fixed old witness** and have no nontrivial automorphisms. The latter retain genuinely distinct symmetries. They must not be conflated.

## 6. Recommended report wording and verification status

“The transport and descent mechanisms reuse standard base change, Grothendieck constructions, and homotopy pullbacks. The result establishes their compatibility with this presentation's actual witnesses, equations, and full occurrence-refinement arrows, with separate existential, discrete-witness, and retained-symmetry conclusions.”

The four primary PDF texts and the locators above were verified on 2026-10-31. Web PDF screenshot retrieval returned cache-miss errors, so this note does not claim visual screenshot verification; the text includes the cited formulas, proposition statements and proof steps. No missing source blocks the bounded comparison. No external state was changed and nothing was uploaded.

This note does not certify mathematical acceptance, completed tests, originality, or that every C5/B3 check has been discharged. Those require the separate proof and audit artifacts.
