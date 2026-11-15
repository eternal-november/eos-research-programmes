# Directed shared-index synchronization

This general categorical result integrates the existing native state assembly with shared-index synchronization. It uses the actual module-completion and native-square constructions, not a concrete store/channel model.

## Result

[The theorem and proof](Directed_Shared_Index_Assembly_from_Native_Cones.tex) construct the directed native comparison

`assembly(sync X, sync Y) → sync(assembly(X, Y))`

without requiring assembly to preserve same-index lax bilimits. Its process square is invertible under the stated pseudo-projection hypotheses, but the state map need not be an equivalence. The comparison is not silently reversed.

The construction extends to finite operations, substitution and admitted directed operation comparisons. With fixed external interfaces, pointwise diagram hom bicategories assemble globally; synchronization has derived sequential, unit and parallel comparisons and their coherence. The unit comparison need not be invertible.

## Fixed-state feedback bridge

[Canonical flattened feedback](Fixed_State_Canonical_Feedback_and_Synchronization.tex) commutes with the selected synchronization cones for each fixed pure outer state. Its underlying state operation is fixed-side tensor, whose preservation is derived directly in the pure module completion. Canonical joining and units respect these comparisons. This is stronger than the general directed comparison, but does not apply to raw state insertion or simultaneously varying outer states.

## Changing interaction shapes

[Shape restriction](Shape_Restriction_of_Native_Synchronization.tex) derives directed comparison cells for natural transformations of shape maps, with operation and fixed-state feedback compatibility. It reuses established restriction, rather than claiming new Kan transport.

[Variable-shape diagrams](Variable_Shape_Native_Diagrams_and_Diagonal_Synchronization.tex) retain the complete native diagram cells in a reverse-shape total bicategory. Synchronization is a pseudofunctor on this total construction. Shared-index assembly factors as independent product-shape assembly followed by diagonal restriction. This locates the possible failure of strong shared synchronization without discarding its directed comparison.

[Global assembly](Global_Variable_Shape_Assembly.tex) lifts the supplied native process tricategory and its admitted parallel/interchange structure to varying internal shapes. Terminal-shape diagrams recover the original process structure. Evaluation has derived directed assembly comparisons; its terminal-shape unit comparison is an equivalence. This differs from the arbitrary fixed-shape constant-unit comparison above.

## Prerequisites

- [Bicategorical synchronization and assembly](../bicategorical-synchronization/README.md): native cone creation and pure-boundary lifting.
- [Native state assembly](../native-state-assembly/README.md): global hom structure and derived fixed-interface synchronization in the relative module completion.
- [Conditional higher native evaluation](../higher-native-evaluation/README.md): canonical flattened feedback and its full native joining laws.
- [Generated native state towers](../generated-native-state-towers/README.md): the separate higher state/closure setting; this result does not assume all its closure operations preserve synchronization.

## Exact boundaries

External interfaces remain fixed in each diagram. Directed process interchange must first be admitted as an actual native operation comparison; a process-level cell alone does not supply that admission. The included fixed-state canonical-feedback theorem derives its own selected cone preservation; raw closure and varying shared states still need their actual cone conditions, and no general inverse is inferred.

The reverse-shape construction is distinct from the earlier forward-shape totalization of the presented context/content theory. It does not automatically preserve that presentation’s coends or mixed crossing. Further feedback equations transfer only when supplied as admitted native operation data.

A module comparison can be relational or have empty fibers. Thus this is not a physical totality/admission guarantee, a chosen stochastic coupling, unrestricted instantaneous feedback, or a completed theory of all interfering systems. It preserves native witnesses rather than identifying separately synchronized and jointly synchronized states.

## Verification and attribution

Independent written-proof review covers the binary construction, finite-operation substitution and global diagram assembly, plus the fixed-state canonical-feedback bridge, reverse-shape total bicategory, diagonal factorization and global variable-shape coherence. No TeX compilation, mechanized proof or CI certification is claimed.

The ordinary lax-monoidal limit construction is established background, linked in the manuscript. The enriched result is proved using the previously constructed native cone equivalences, rather than attributed to that ordinary implementation. No novelty claim is made. `MANIFEST.json` checks file integrity only.
