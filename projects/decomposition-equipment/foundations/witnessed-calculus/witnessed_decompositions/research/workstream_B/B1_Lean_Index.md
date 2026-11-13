# B1 Lean slice: source and dependency index

Author-local verification, 2026-10-24. This file does not grant independent
acceptance. Governing target is `B1_B2_Targets.md`, pre-proof reviewed at SHA256
`37912984dfcd045bb504e738823f8194e933975d5d94e043da50253cf94c8092`.
Contract SHA256 remains
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.

## Stable source

`WitnessedDecompositions/RawRefinement.lean`, SHA256
`7de14174296acdc507dc078eb5a57bf4d6cba18d4964d143b33e648ee3b8f059`.
All declarations quantify over arbitrary interfaces `V`, arbitrary directed
component family, signature `S`, and fixed arbitrary output component `c`.
There is no signature finiteness, component decidable equality, positivity,
nonempty-profile, or target-model assumption. Nullary/unary nodes are admitted.
The fixed-output categories together are the disjoint-union raw category.

## Theorem map

| Frozen clause | Definitions / verified declarations | Lines |
|---|---|---:|
| Actual forest arrows and typed composition | `Raw.Arrow`, `Raw.id`, `Raw.comp`, `Raw.comp_val` | 314–334 |
| Unique recovery of all inserted trees | `Tree.graft_injective` | 25–34 |
| Thinness derived from recovery | `Raw.hom_subsingleton` | 336–337 |
| Actual category laws and instance | `Raw.id_comp`, `Raw.comp_id`, `Raw.comp_assoc`, `Raw.instCategoryTree` | 339–356 |
| Antisymmetry, not just a preorder | `Tree.graft_no_cycle`, `Raw.antisymm`, `Raw.refines_antisymm`, `Raw.partialOrder` | 37–51, 359–386 |
| Actual nested occurrence equivalence | `Tree.graftLeaf`, `ungraftLeaf`, `graftLeafEquiv` with both inverse proofs | 54–94 |
| Preservation of the whole typed component | `graftLeaf_component`, `graftLeafEquiv_component` | 97–110 |
| Component-correct second-layer restriction | `innerAtLeaf`, `atLeaf_innerAtLeaf` | 113–136 |
| Independent composition at each original leaf | `atLeaf_compose` | 119–126 |
| Three-coordinate occurrence coherence | `graftLeafTriple_eq`, `graftLeaf_assoc` | 155–203 |
| Full-profile/structural forest bridge | `atLeaf_profileSubstitutionEquiv`, `profileGraftLeafEquiv`, `profileGraftLeafEquiv_component` | 207–228 |
| Ordered rather than label-only correspondence | `collect_frontierLeafEquiv`, `collect_graftLeaf`, `collect_profileGraftLeaf` | 231–286 |
| Actual structural/profile forest composition agrees | `profileSubstitutionEquiv_compose` | 296–306 |

`graftLeaf_assoc` retains the triple `(original leaf, inserted leaf, third-stage
leaf)` and transports only along the already proved tree-graft associativity
and local replacement equality. `graftLeafTriple_eq` proves its left map is the
actual sequential graft-occurrence map, not an unrelated map stipulated to
satisfy associativity.

`collect_frontierLeafEquiv` uses `Path.collect_expand_slots`, whose correspondence
is the accepted `Path.slotExpand`; `collect_graftLeaf` expresses precisely the
ordered concatenation of every replacement's leaves. The combined theorem
holds for arbitrary list-valued tests, including singleton tests that name the
actual occurrence. It therefore detects any permutation of equal-labelled
occurrences. No label injectivity assumption is used.

The independent address-prefix criterion and all-history/linear-extension
comparison are P evidence in the separate B1 mathematical dossier, not claimed
to be fully mechanized here.

## Dependency closure and trust

The sole direct project import is `WitnessedDecompositions.FreeCalculus`.
Its project closure is exactly the accepted A1 implementation:
`Core`, `Collections`, `PathOccurrences`, `TreeOccurrences`, `Calculus`,
`FreeCalculus`. Neither A2/A3/A4 nor any semantic/quotient example is imported.
External dependencies are the pinned Lean/mathlib base.

`audit/WorkstreamB1Axioms.lean` and `evidence/B1_axioms.log` audit the principal
claims. The union of printed axiom closures is **`propext`, `Quot.sound`**.
No `Classical.choice`, custom axiom, `sorryAx`, or unchecked-computation oracle
appears. Several occurrence and pointwise-composition claims are axiom-free.
The category laws use the proved uniqueness of retained forests; this is valid
because category composition was independently defined with `Tree.compose`,
not with propositional reachability or chosen unique arrows.

## Reproduction

From the project root in the pinned environment:

```
lake build
lake env lean -o .lake/build/lib/lean/WitnessedDecompositions/RawRefinement.olean WitnessedDecompositions/RawRefinement.lean
lake env lean audit/WorkstreamB1Axioms.lean
```

The accepted aggregator does not yet import the new module; the explicit second
command is therefore necessary. The successful stable-source output is
`evidence/B1_sixth_elaboration.log` (empty compiler output, exit 0), and the audit
output is `evidence/B1_axioms.log` (exit 0). Earlier elaboration attempts are
retained: first/second failed during dependent-pattern/transport formulation;
third/fourth passed earlier smaller drafts; fifth failed during the additional
ordered-traversal bridge; sixth passed the stabilized complete file. They are
not conflated with the final verification.

A duplicate baseline build was inadvertently launched within roughly one second
of the parent build. When the collision was reported, a cancellation was sent,
but the duplicate had already exited successfully. It changed no source and
produced the same accepted module outputs. No new proof was counted as verified
by either baseline build; the explicit module/audit runs above provide that
verification.

## Supplemental kernel regression examples

`tests/B1RawRefinementAudit.lean` constructs actual two-step independent-graft
arrows in both orders and checks equality of their retained composite forest;
it checks different repeated-label substitutions, nullary consumption at one
position, and the impossibility of changing an existing primitive root or
undoing a dependent unary insertion. `evidence/B1_regression_verified.log`
records the successful kernel run. The displayed theorem axiom union is only
`Quot.sound`; the rejection and nullary examples are axiom-free. Two earlier
elaboration failures are explicitly preserved in `B1_regression_initial.log`
and `B1_regression_second_failed.log`. This is supplemental coverage, not the
unrestricted history-interchange proof or the mixed-interface principal model.
