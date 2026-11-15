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

## Presented grades and varying-state evaluation

[Retained comma presentation](Retained_Comma_Presentation_of_Variable_Shapes.tex) identifies the exact context diagram, content diagram, body and native grade maps of variable-shape processes. It reuses normalization over the common diagram pure base, including its whole-diagram balance. Independently shaped factors do not automatically normalize to the shared-index object: their diagonal comparison need not invert.

[Join-then-synchronize](Join_Then_Synchronize_Varying_State_Towers.tex) evaluates coherent varying-state finite towers by joining first and synchronizing the resulting full native diagram. It is compatible with consecutive-block joining, changing internal shapes and global directed assembly. The output retains the joint synchronized state; it is not identified with a tensor of separately synchronized coordinates. This does not assume synchronization exists at higher tower depths or prove that joining preserves those hypothetical limits.

## A universal property for synchronization

[Lax-body diagrams and coreflection](Lax_Body_Diagrams_and_Synchronization_Coreflection.tex) enlarges diagram bodies from pseudonatural to correctly directed lax transformations, retaining their native cells. This admits the actual universal lax cone as a diagram arrow. The singleton embedding then has synchronization as right biadjoint, provided the selected lax bilimits exist. Its counit derives the directed assembly comparisons by taking mates, and recovers the existing comparisons through their cone legs.

The original pseudo-body construction alone does not supply this adjunction: its singleton arrows encode pseudocones rather than all lax cones. The enlargement coincides with it on the original locally discrete comma-category presentation. Admitted global operations and fixed-state feedback remain compatible, using full naturality on noninvertible body cells. This is an evaluation universal property in a doctrine already possessing the selected cones, not their free creation or a new instantaneous feedback law.

## Actual varying interfaces and pure endpoint maps

[Native dialgebra diagram presentation](Native_Dialgebra_Diagrams_and_Varying_Interface_Bodies.tex) identifies the state diagram and its directed lax transition body, including every native square and higher witness. Invertible diagram compositors do not make the transition squares invertible. This verifies the connection to actual changing loop interfaces, rather than merely packaging unrelated processes.

[Relative pure-endpoint laws](Relative_Pure_Endpoint_Laws_for_Synchronization.tex) derive strong compatibility with the original pure endpoint changes from the existing native cone-creation criterion. The endpoint-map components need not be invertible and their realization need not be faithful. Mixed sequential/parallel compatibility uses the original admitted action comparisons; it does not manufacture them.

## Shared state is not independent closure

[Shared-state chronological assembly](Shared_State_Chronological_Assembly_and_Synchronization.tex) retains one state, one state map and one native witness through a finite ordered chain. It composes the original process bodies without copying the state. Under the stated output-preservation hypotheses, this shared-state operation commutes strongly with native synchronization, since its state-base functor is the identity.

This differs from composing independently closed machines, which retain separate state coordinates. The theorem does not identify these operations or supply a same-state parallel schedule. It requires actual ordered process bodies and native squares; simultaneous sharing still needs an admitted joint law.

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

Independent written-proof review covers the binary construction, finite-operation substitution and global diagram assembly, plus the fixed-state canonical-feedback bridge, reverse-shape total bicategory, diagonal factorization global variable-shape coherence, the retained comma bridge, finite-depth join-then-synchronize evaluation, and lax-body synchronization coreflection with its counit-mate operation comparisons. No TeX compilation, mechanized proof or CI certification is claimed.

The ordinary lax-monoidal limit construction is established background, linked in the manuscript. The enriched result is proved using the previously constructed native cone equivalences, rather than attributed to that ordinary implementation. No novelty claim is made. `MANIFEST.json` checks file integrity only.
