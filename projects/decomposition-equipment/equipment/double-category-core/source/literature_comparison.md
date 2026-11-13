# Primary literature comparison for original E1

Prepared 31 October 2026 for the author of the E1 completion. This note concerns the **original E1** in `Original_Completion_Contract_v0.1_VERBATIM.md`, lines 414–434, not E2. It checks a deliberately narrow literature baseline and the actual inherited equipment proofs. It makes no priority or exhaustive-novelty claim, and it does not independently certify the new E1 proof.

## Main conclusion

The classical equipment infrastructure should be imported and credited. The inherited dossier already contains substantial proofs of contextual units, all-arity restrictions, concrete core and refinement recovery, transformation extension, and coherent universal choices. The outstanding E1 contribution is the **integration** of this infrastructure with declared witness, admissibility, exactness, presentation, refinement, and morphism conventions. An equipment definition plus a concrete model would merely repeat part of the available input.

## Verified primary references and locators

Page numbers below refer to the explicitly versioned arXiv PDFs, whose printed pages agree with PDF page numbers. They are **not journal page numbers**.

1. G. S. H. Cruttwell and Michael A. Shulman, *A unified framework for generalized multicategories*, Theory and Applications of Categories **24** (2010), no. 21, 580–655. Inspected version: [arXiv:0907.2460v3](https://arxiv.org/pdf/0907.2460v3), dated 9 December 2010.

   | Locator | Baseline used in E1 |
   | --- | --- |
   | Definition 2.1, pp. 10–11 | Classical cells have arbitrary finite horizontal source, including empty source, and one horizontal target. |
   | Example 2.7, p. 12 | Span multicells provide the standard span coordinate. |
   | Section 3 and Definition 3.1, pp. 15–16 | Structure-preserving functors and cell-natural transformations form `vDbl`. |
   | Definition 5.1, pp. 28–29; Remark 5.8, p. 31 | Opcartesianness is contextual; context-free universality is weaker. |
   | Paragraph preceding Example 5.9, p. 31 | Normality preserves universal units, not literal choices. |
   | Definition 7.1, p. 37 | Cartesian restriction factors cells of every arity; choices are coherently isomorphic. |
   | Definition 7.6, p. 38 | A virtual equipment has all restrictions and units. |
   | Theorem 7.24, p. 42 | Every functor between virtual equipments preserves restrictions; normality is not required. |

   Theorem 7.24 states: “Any functor F between virtual equipments preserves restriction.” Its following paragraph retains the independent unit-preservation condition. Thus the restriction requirement initially listed in Definition 7.6 is redundant for full equipment-to-equipment functors. This is not a preservation theorem for arbitrary witness markings. [Primary theorem](https://arxiv.org/pdf/0907.2460v3#page=42).

2. Michael Shulman, *Framed bicategories and monoidal fibrations*, Theory and Applications of Categories **20** (2008), no. 18, 650–738. Inspected version: [arXiv:0706.1286v2](https://arxiv.org/pdf/0706.1286v2), dated 9 January 2009. Its **Proposition 6.8, pp. 25–27**, proves preservation of cartesian cells by lax double functors between framed bicategories. This is the ordinary double-category precursor of CS Theorem 7.24. Be version-sensitive: CS cites `[Shu08, Theorem 6.4]`, but in this inspected arXiv version Example 6.4 concerns `Span(F)`, whereas the relevant preservation proof is Proposition 6.8. Do not copy the former locator onto the latter PDF. This supporting reference is not an E2 completion theorem.

3. Seerp Roald Koudenburg, *Augmented virtual double categories*, Theory and Applications of Categories **35** (2020), no. 10, 261–325. Inspected version: [arXiv:1910.11189v4](https://arxiv.org/pdf/1910.11189v4), dated 3 March 2025; its acknowledgments explicitly record corrections to Definition 1.2 and Example 1.6. Introduction pp. 2–3 and Definition 1.2, pp. 10–12 distinguish **empty horizontal targets** from the already classical empty sources. Definitions 3.1–3.2 and Proposition 3.3, pp. 24–25 give functors, transformations, and their 2-category; the empty-path naturality convention retains the object component. Section 10, pp. 60–62, especially Theorem 10.1 on p. 61, compares the unital augmented theory with classical unital virtual double categories and **normal** functors. Therefore E1 need not import augmented cells, and must not rename its arbitrary source-nullary primitives as augmented target-nullary cells.

## What the inherited source already establishes

The following are direct locators in `/workspace/shared/contract_revision_20261028/structural_extracted`. They record what the submitted proofs actually contain, not a fresh global acceptance decision. Their own scope restrictions remain operative.

### GraphSpanModel

* **Lines 11–35, Section 1:** actual ordered graphs, actual finite spans, boundary-marked path tuples, retained empty paths, and coherent tuple regrouping. This avoids quotienting apex witnesses or silently identifying nested pullbacks.
* **Lines 37–94, Sections 2–3:** cells retain an ordered graph partition, an actual witness function, and a global scalar. Substitution retains the full family of shared vertical maps. Its zero-outer-arity case still has a vertical map, and associativity checks empty subpaths explicitly.
* **Lines 96–130, Section 4:** Theorem 4.1 proves cartesianness for every source arity, including zero. The displayed lift retains partition and scalar. The subsequent paragraphs prove restriction naturality, compositional comparisons, identity comparisons, and coherent change of cartesian choice.
* **Lines 132–156, Section 5:** Theorem 5.1 proves the insertion/removal bijection in every prefix and suffix. It separates the designated universal nullary from other nullary scalar witnesses. This is already full contextual universality, not just a unit equation.
* **Lines 158–212, Section 6:** the tagged faithful interface realization and graph spans give an exact description of the identity-boundary image on complete old profiles. Lines 204–210 check nullaries, substitution, and entrywise refinement recovery. Fullness is confined to those fibres; it is not fullness of the vertical realization or of a free envelope.
* **Lines 214–222:** the mixed-interface instance retains two composable nonidentity interface arrows, repeated equal component types, different retained wholes, and parallel refinement tuples.
* **Lines 224–254, Section 7:** a representability boundary is already proved for this concrete graph model. It is not a claim that E1 requires all nonempty composites.

The source itself credits the span baseline and the CS definitions at line 156. Its opening scope paragraph expressly does not treat the model alone as discharge of E1–E5.

### Conservative Equipment Envelope

* **Lines 5–26:** sizes, a small full category of tagged finite sets, fixed vertical data, faithful realization, and the exact interpretation-category strength are explicit. A small vertical category is not a claim that its induced vertical 2-category is locally discrete.
* **Lines 28–78, Sections 2–3:** a typed term construction adds fresh units and restrictions, without covert equalities of horizontal expressions. It retains nullary vertical whiskering. All-context factor constructors and beta/eta schemes are part of the syntax.
* **Lines 80–90, Section 4:** the displayed inverse laws prove actual all-arity restrictions and contextual units. Restriction comparison coherence follows by uniqueness. The separately described ordinary-envelope construction is a stronger, distinct result.
* **Lines 92–127, Sections 5–6:** interpretation extension is proved on objects, cell terms, and Cruttwell–Shulman transformations. In particular, equation (6.2) retains the vertical whiskering of a nullary unit; the naturality proof treats all factor constructors.
* **Lines 129–135, Section 7:** alternate universal choices yield unique invertible comparison transformations with a cocycle law. The strictification claim applies to interpretations **out of this free syntax**. It must not be upgraded without proof to strictification of every chosen-equipment morphism while fixing every named horizontal image.
* **Lines 151–163, Section 9:** semantic fibre recovery, old equality conservation, and occurrence-wise refinement faithfulness are already supplied. The proof explicitly does not establish fullness of the free-envelope unit.

Line 13 already disclaims novelty for the standard categorical infrastructure. E1 should preserve this attribution rather than present these ingredients as newly invented.

## Focused corrections and integration requirements

1. **Restriction preservation is not an additional obstruction for full equipments.** `Extended_Local_Presentation.md`, Section 6, especially line 283, warns jointly that images of `kappa` and `c0` need not be universal in extra target cells. Read in the already-established full-equipment-to-full-equipment setting, the `kappa` half is too strong: apply CS Theorem 7.24. The `c0`/normality warning survives. Likewise literal preservation of chosen expressions remains stronger than preservation of their universal properties. This note records a scoped correction; it does not modify the inherited file.

2. **Declare the witness-sensitive layers separately.** The contract distinguishes all cells, an optional admissible decomposition family, and an exact/opcartesian marked family. These should not collapse by definition. The existing nonuniversal graph witnesses are legitimate cells; neither a restriction nor a normal functor automatically preserves an arbitrarily chosen exact marking. A morphism convention must say which extra data are preserved, reflected, or forgotten.

3. **Type the core comparison at each categorical level.** A general equipment transformation has nonidentity vertical boundary components. Consequently its horizontal components need not belong to the identity-boundary core. This is a direct typing observation: an ordinary core 2-functor requires vertical-identity transformations, or a target that explicitly retains or transports those boundary components. Naming the object-level core does not solve this issue.

4. **Do not generalize the choice theorem past its hypotheses.** The inherited recursive comparison is strong evidence for the chosen/unchosen bridge in its free presentation. A new global package must state its own size, choice, strictness, and allowed marked-comparison conventions. In particular, transporting an extra marking across an isomorphism needs an explicit invariance convention if it is used.

5. **Separate E1 from E2 and the ordinary strengthening.** This pass supplies no global reconstruction theorem, no general exactness classification for every presentation, and no theorem making every finite path representable. The relevant new claim is a coherent witness-sensitive axiomatic and morphism package with its precisely stated core/refinement image.

## Verification and stopping record

The three versioned primary PDFs were opened and their named definitions/theorems checked; local PDF and text copies are retained in `references/` for audit. The designated E1 contract and both requested inherited proofs were read. The narrow `Extended_Local_Presentation.md` passage was inspected only to resolve the restriction-preservation correction raised during review. No inherited file was changed and nothing was uploaded.

**Status:** bounded comparison complete. **Blocker:** none. **Action target:** author and independent auditor of the new E1 package. **Required use:** credit the inherited theory, incorporate the scoped preservation correction, and verify the new marking/core/refinement integration in the new proof. This note alone does not change E1's acceptance status.
