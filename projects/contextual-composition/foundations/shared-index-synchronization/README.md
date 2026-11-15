# Directed shared-index synchronization

This general categorical result integrates the existing native state assembly with shared-index synchronization. It uses the actual module-completion and native-square constructions, not a concrete store/channel model.

## Result

[The theorem and proof](Directed_Shared_Index_Assembly_from_Native_Cones.tex) construct the directed native comparison

`assembly(sync X, sync Y) → sync(assembly(X, Y))`

without requiring assembly to preserve same-index lax bilimits. Its process square is invertible under the stated pseudo-projection hypotheses, but the state map need not be an equivalence. The comparison is not silently reversed.

The construction extends to finite operations, substitution and admitted directed operation comparisons. With fixed external interfaces, pointwise diagram hom bicategories assemble globally; synchronization has derived sequential, unit and parallel comparisons and their coherence. The unit comparison need not be invertible.

## Prerequisites

- [Bicategorical synchronization and assembly](../bicategorical-synchronization/README.md): native cone creation and pure-boundary lifting.
- [Native state assembly](../native-state-assembly/README.md): global hom structure and derived fixed-interface synchronization in the relative module completion.
- [Generated native state towers](../generated-native-state-towers/README.md): the separate higher state/closure setting; this result does not assume all its closure operations preserve synchronization.

## Exact boundaries

External interfaces remain fixed in each diagram. Directed process interchange must first be admitted as an actual native operation comparison; a process-level cell alone does not supply that admission. Fixed-wire feedback and joining need their actual cone conditions to obtain preservation, and no general inverse is inferred.

A module comparison can be relational or have empty fibers. Thus this is not a physical totality/admission guarantee, a chosen stochastic coupling, unrestricted instantaneous feedback, or a completed theory of all interfering systems. It preserves native witnesses rather than identifying separately synchronized and jointly synchronized states.

## Verification and attribution

Independent written-proof review covers the binary construction, finite-operation substitution and global diagram assembly. No TeX compilation, mechanized proof or CI certification is claimed.

The ordinary lax-monoidal limit construction is established background, linked in the manuscript. The enriched result is proved using the previously constructed native cone equivalences, rather than attributed to that ordinary implementation. No novelty claim is made. `MANIFEST.json` checks file integrity only.
