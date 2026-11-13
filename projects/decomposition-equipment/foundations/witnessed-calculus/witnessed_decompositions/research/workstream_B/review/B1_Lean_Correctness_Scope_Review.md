# Independent B1 Lean correctness and scope review

**Verdict: PASS for B1-R and B1-O, including their mandatory L floor.** No blocking correctness, hidden-hypothesis, or mathematical-scope defect was found in the reviewed Lean slice. This is not acceptance of B1-P, B2, or the overall research program. The independent prefix/all-history P review remains a separate acceptance input.

Reviewer: `/root/audit_refinement_lean_correctness`, 2026-10-24 UTC. Review-owned evidence directory: `reviews/B1_Lean_Independent/` (paths below relative to `/workspace/shared/witnessed_B_20261024`). No author source or build output was edited. The only author-side change observed during this review was the author appending a supplemental regression-index section; the actual implementation and audit stayed unchanged.

## Authority and exact reviewed bytes

The complete B1 acceptance clause, §3.4 of the unchanged contract, and the complete frozen B1/B2 target were read, including the forbidden shortcuts and minimum passing floor. This is a positive-only M review; no theorem was weakened, no obstruction substituted, and no premise asserting an intended conclusion was accepted.

| File | SHA256 |
|---|---|
| `research/CompletionContract.md` | `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e` |
| `research/workstream_B/B1_B2_Targets.md` | `37912984dfcd045bb504e738823f8194e933975d5d94e043da50253cf94c8092` |
| `WitnessedDecompositions/RawRefinement.lean` | `7de14174296acdc507dc078eb5a57bf4d6cba18d4964d143b33e648ee3b8f059` |
| `audit/WorkstreamB1Axioms.lean` | `f4e4b820ef74793d9c485f795ad5143dc5f91f280522e2729737ec60bd2a3eec` |
| `research/workstream_B/B1_Lean_Index.md`, originally assigned | `7348a794154c67aa508b41fcfc19a558a9a942cc801c856e62b7f743294dff34` |
| Same index, supplemental test section reviewed | `4a22d0f59ec82146609235d2e1fa621524bfd054eb43555a5c39967cda7acf34` |
| `tests/B1RawRefinementAudit.lean` | `a83a4d2a54c64e3cedf60dd44c4bbbee4c9bdfda36041eeead4937f8409a81f3` |

Both index versions are preserved under `B1_Lean_Independent/frozen_sources/`; removing the appended supplemental section reproduces the assigned index hash exactly. The new section does not change mathematical claims or hypotheses.

## 1. Actual raw forest arrows and category

**B1-R passes.** `Raw.Arrow` (314–315) is precisely the subtype of `Tree.Substitution t` with retained-tree graft endpoint `u`. It is not a proposition, a trace category, or a quotient by evaluation. `Raw.id` uses the actual identity forest. `Raw.comp` (322–326) performs equality elimination on the first endpoint and applies the accepted structural `Tree.compose`; `Raw.comp_val` states the exact retained forest with the required equality transport.

`Tree.graft_injective` (25–34) is independently proved by structural induction: graft is the identity on the sole leaf entry; constructor injectivity recovers all child grafts at a node, and their induction hypotheses recover the entire dependent product. No prefix assumption, uniqueness assumption, decidable equality, or equation on tree syntax is supplied as a premise.

Only after that theorem, `Raw.hom_subsingleton` derives thinness. The arrow unit/associativity equalities then legitimately use this proved subsingleton instance. They are equalities of the original forest subtypes, not laws after erasure. The actual `CategoryTheory.Category (Tree S c)` instance (350–356) uses these arrows, identities, and composition. This is exactly the permitted fibrewise construction for arbitrary output `c`; no arrow changes its output component.

`Tree.graft_no_cycle` (37–51) proves literal-tree antisymmetry structurally. It does not use a strictly increasing leaf count (which would fail for unary/nullary witnesses). At a leaf, an inserted node cannot subsequently become a leaf. At a node, all original child subtrees are recovered inductively. `Raw.antisymm`, `Refines`, and the named `partialOrder` therefore establish a genuine poset on literal trees. The independent address-prefix characterization and categorical identification with that independently defined prefix relation belong to B1-P, not to a disguised definition of `Refines` here.

## 2. Typed occurrence correspondence, composition, and three coordinates

**B1-O passes.** `Tree.graftLeaf` and `ungraftLeaf` recursively insert/recover actual occurrence positions and have both inverse laws. `graftLeafEquiv` is the required equivalence

`Leaf (graft t σ) ≃ Σ l : Leaf t, Leaf (atLeaf t σ l)`.

The value `leafComponent` is an entire directed component (source, target, and edge), not a label, color, or count. `graftLeaf_component` and `graftLeafEquiv_component` prove preservation at that level.

`innerAtLeaf` restricts the actual second forest at the structural original occurrence. `atLeaf_compose` proves the required replacement-tree equality for every original leaf, and `atLeaf_innerAtLeaf` ties that restriction to the nested occurrence map, including the full-component equality transport. Thus composition is not verified only on a flattened profile.

For reassociation, `graftLeafTriple_eq` identifies the defined triple map with the actual sequential graft map, using `innerLeaf` solely to resolve the dependent third-leaf type. `graftLeaf_assoc` then proves equality after the canonical tree-graft associator and local replacement equality. Its three coordinates are the original leaf, the leaf in its inserted tree, and the final leaf inserted there. All remain independently quantified. This is not two selected swaps or a condition imposed on a purported associator by definition. The reviewer additionally proved, by induction, that `innerLeaf` preserves its input occurrence by heterogeneous equality; this rules out treating that reindexing as an unspecified coordinate choice.

The A1 bridge is substantive: `atLeaf_profileSubstitutionEquiv` reads each actual profile-family entry through `frontierLeafEquiv`, and `profileGraftLeafEquiv_component` preserves its complete component. `collect_frontierLeafEquiv` explicitly invokes A1's `Path.collect_expand_slots`/`slotExpand` traversal. Together with `collect_graftLeaf`, `collect_profileGraftLeaf` establishes the exact ordered block traversal for arbitrary list-valued occurrence tests, including singleton tests whose values are the actual occurrences themselves. Hence equal-labelled leaves cannot be silently permuted. The reviewer instantiated this exact occurrence-identity traversal in Lean. Finally, `profileSubstitutionEquiv_compose` proves equality of the entire retained structural forest with A1's full-profile `CalcData.composeFamily` forest; it uses separately established graft injectivity, not an assumed forest-composition law.

The bridge is distributed across component, traversal, and forest-composition theorems rather than packaged as one large dependent commuting-square declaration. Those facts do establish the requested link and do not lose occurrence data. No additional direct-square lemma is required for this scoped verdict.

## 3. Generality, degeneracies, and discriminating tests

The implementation quantifies over arbitrary interface type, arbitrary quiver component family, arbitrary signature, arbitrary fixed output, and arbitrary finite source/replacement trees. There is no finiteness or decidable-equality assumption on those types, no one-color restriction, no positive-arity condition, and no nonempty frontier hypothesis. Existing A1 path slots are finite ordered positions, and the accepted tree constructors admit nullary and unary nodes.

Independent reproduction covered:

* Author Lean regressions: actual independent two-step raw arrows in both orders; equality of their retained composite forest; unequal replacements at equal labels; rejection of changing an existing primitive root; inability to undo a unary expansion; nullary removal and unique nullary self-refinement.
* Review-only Lean checks in `IndependentB1Checks.lean`: every arbitrary no-leaf source has exactly its identity forest and every outgoing raw arrow fixes the target; exact ordered occurrence-identity traversal; preservation of the third occurrence by `innerLeaf`; repeated-label forest inequality; and a concrete nullary graft whose sole surviving occurrence recovers precisely the original right leaf.
* The author's Python finite regression suite, independently rerun without modifying its report: 24,649 prefix/reconstruction/antisymmetry pairs; 1,237 forest-recovery cases; 4,122 moving-rank checks; 1,237 chronology cases and 4,309 histories; and a six-event mixed-interface context with 80 linear extensions. It includes a genuinely illegal child-before-parent attempt, existing-vertex rejection, nullary deletion/rank shifts, and three-layer typed address composition.

These finite checks are C evidence only. They are not substituted for unrestricted Lean statements or the separate all-history P proof. In particular, the Lean theorem named `cannot_reverse_dependent_event` checks undoing a unary expansion, not reversing two insertions. The supplemental index now describes it accurately; the actual dependent-insertion reversal test is in the Python suite and the general issue is addressed by B1-P. This naming/documentation distinction is not an outstanding blocker.

## 4. Independent build, dependencies, and trust boundary

The direct project import is `FreeCalculus`. Its complete project dependency closure is exactly A1: `Core`, `Collections`, `PathOccurrences`, `TreeOccurrences`, `Calculus`, `FreeCalculus`. All six were recompiled from source into a review-owned module root, followed by `RawRefinement`. The same rebuilt modules were then used for both axiom audits. `Examples`, needed only for regressions, was separately rebuilt into that review root. No acceptance relied on a potentially stale author `.olean`.

Every one of those seven baseline source files (the six A1 files plus `Examples`) was compared byte-for-byte with the original supplied ZIP, SHA256 `4425884ab0287dd627d91585dd373edffc850e6db3c8d6215783292db4cb3f2c`; all match. Details are in `baseline_dependency_hashes.json`. Neither A2, A3, A4, nor semantic/quotient modules enter the B1 implementation closure.

The supplied 22-principal-declaration audit passed. The reviewer also generated and ran `AllB1Axioms.lean` covering **all 43 declarations**, including definitions, inverse laws, the category instance, reachability, and partial order. The total axiom union is exactly **`propext`, `Quot.sound`**. No `Classical.choice`, custom axiom, `sorryAx`, `admit`, or unchecked-computation oracle occurs. Full source inspection found no assumptions asserting desired B1 conclusions. Standard quotient soundness here is used through foundational extensionality infrastructure; the raw arrows/trees themselves are not quotiented.

Pinned environment: Lean 4.35.0; project mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. Reproduction script: `B1_Lean_Independent/reproduce.sh`. Logs: `closure_compile.log`, `axioms.log`, `all_axioms.log`, `examples_compile.log`, `author_regressions.log`, `independent_checks.log`, `chronology_checks.json`. Final source hashes are in `final_source_hashes.txt`.

One initial audit invocation failed at module lookup, before checking any theorem: putting a review-only `RawRefinement.olean` in a new top-level namespace root made Lean seek `FreeCalculus.olean` in that root. The exact error is preserved in `axioms_initial_path_setup_failure.log`. Recompiling the entire A1 closure into the review root fixed this setup issue; subsequent source/audit/test runs passed. This was neither a source proof failure nor an authorization block.

## 5. Acceptance boundary

The Lean slice reaches the promised B1-R/B1-O depth: actual forest category; independently established unique recovery, thinness, and antisymmetry; arbitrary typed nested occurrences; full retained-forest composition; and non-erasing three-coordinate coherence linked to the accepted full-profile calculus. The cheapest excluded shortcuts are absent. This infrastructure should not be advertised as a new integrated recognition theorem or as progress on still-open A4/B3/B4/C obligations.

**Recommendation:** accept the mandatory B1 Lean slice at the bound source hash, with the separate B1-P substantive review and overall evidence inventory still required before marking B1 itself accepted. No code revision is requested by this review.
