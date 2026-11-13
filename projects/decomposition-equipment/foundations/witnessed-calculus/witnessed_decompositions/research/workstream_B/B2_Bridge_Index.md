# B2 raw/evaluated comparison bridge — implementation index

Author-local kernel evidence, 24 October 2026. This is not an acceptance decision.
Contract v0.1 SHA256 `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
Approved target SHA256 `37912984dfcd045bb504e738823f8194e933975d5d94e043da50253cf94c8092`.

## Frozen files and theorem scope

`WitnessedDecompositions/RefinementComparison.lean` SHA256
`5e588ef5b301d2787cd45518659309750724bad2b46ba73cb76a127895ce37f6`.

All declarations quantify over arbitrary interfaces/quiver/signature and arbitrary
fixed output, with no finite-signature, positivity, decidable-equality or target
cancellation assumption. Target operation universe may differ from the syntax
universe. Empty profiles and nullary operations are admitted.

- `rawToFreeArrow`, `freeToRawArrow`: explicit conversions between structural
  raw forests and free-calculus profile tuples using A1's occurrence equivalence.
- `freeToRaw_rawToFree`, `rawToFree_freeToRaw`, `arrowEquiv`: both inverse laws
  for the complete retained arrow data.
- `free_hom_subsingleton`: raw unique forest recovery transported along that
  actual hom equivalence, not imposed or obtained by quotienting tuples.
- `rawToFree_id`, `rawToFree_comp`, `freeToRaw_id`, `freeToRaw_comp`: identity
  and composition preservation as equality of whole forest/tuple arrows.
- `rawToFree`, `freeToRaw`: actual category-theoretic functors, identity on the
  underlying tree objects; the free semantic side uses its harmless object wrapper.
- `rawToFree_freeToRaw_functor`, `freeToRaw_rawToFree_functor`: literal equalities
  of their composites with the identity functors, so the claimed category
  identification is not merely a bijection of objects or reachability relations.
- `rawFunctor`, `rawFunctor_map_val`: actual interpretation functor for every
  strict free-calculus morphism, with its exact entrywise forest interpretation
  and full-profile equality transport exposed.
- `evaluationFunctor`, `evaluation_map_id`, `evaluation_map_comp`: the A2
  assignment extension induces a raw evaluation functor, preserving identities
  and composition at the complete tuple level.
- `rawFunctor_map_injective`: automatic fixed-hom injectivity from raw thinness;
  explicitly no claim of object recovery or fullness follows.
- `unique_raw_lift_of_family`: supplied entrywise lifts plus operation injectivity
  at the fixed whole give a unique actual raw arrow. Its endpoint is derived,
  not assumed in the lift premise. It specializes the independently proved
  general `SemanticRefinement.liftArrow_of_family`.

The comparison functor laws use the already proved unique recovery of free
forests to establish equality of full tuples. This is not the forbidden shortcut
of erasing positions or defining arrows by reachability: both compositions
already contain the actual typed substitution data, and the explicit inverse
maps retain and recover every entry. B1's separate profile/structural composition
theorem supplies the direct occurrence-level identification as well.

## Trust boundary

`audit/WorkstreamB2BridgeAxioms.lean`, SHA256
`a0b52f41e1329a0598402eff60ac7abb4f708c56dc114903e0719656509282e2`,
and `evidence/B2-bridge-axioms.log` print 20 axiom closures.

The actual forest/tuple conversions, their inverse laws, both functors, raw and
A2 evaluation functors, their laws, automatic hom injection, and unique supplied
raw lifting use **only `propext`, `Quot.sound`**. The two literal inverse-functor
packaging equalities additionally contain standard `Classical.choice` through
Mathlib's `Functor.comp` implementation in their statements. This dependency is
separately disclosed; no custom axiom, admission, or unchecked oracle is present.
The supplied-lift theorem itself makes no choice; optional collecting of
individually existing lifts is a distinct theorem in `RefinementLifting.lean`.

The direct project imports are RawRefinement, SemanticRefinement and
RefinementLifting. Their accepted dependencies are A1/A2; actual-A3 quotient
examples are not imported into the general bridge. B3/B4/C are not activated.

## Direct evaluation-functor negative regression

`tests/B2RawEvaluationAudit.lean` imports the frozen actual A3 quotient examples
and proves:

- `RefinementComparisonChecks.right_arrow_not_in_raw_functor_image`;
- `RefinementComparisonChecks.mixed_right_arrow_not_in_raw_functor_image`.

These exclude preimages under the **actual rawFunctor hom map**, both for the
loop example and the genuine mixed-interface context. They do not merely reject
one guessed representative tuple. Their audit includes standard `Classical.choice`
from the accepted quotient implementation, alongside `propext` and `Quot.sound`.
Successful output: `evidence/B2-raw-evaluation-regression.log`.

## Reproduce and failures retained

```
lake env lean -o .lake/build/lib/lean/WitnessedDecompositions/RefinementComparison.olean WitnessedDecompositions/RefinementComparison.lean
lake env lean audit/WorkstreamB2BridgeAxioms.lean
lake env lean tests/B2RawEvaluationAudit.lean
```

Dependencies must first be compiled in the pinned Lean 4.35.0 environment; the
aggregate B reproduction driver performs fresh-source closure compilation.
`evidence/B2-bridge-final.log` records the final successful source run (empty
compiler output, exit 0). `B2-bridge-first.log` records the initial elaboration
failure; `B2-bridge-second.log` passed the first complete version with broader
standard-choice packaging. `B2-bridge-choice-cleanup.log` records a failed
incidental trust-dependency reduction attempt; its correction passed in
`B2-bridge-choice-cleanup-second.log` before the final run. These development
failures are not counted as passing evidence and did not alter baseline sources.
