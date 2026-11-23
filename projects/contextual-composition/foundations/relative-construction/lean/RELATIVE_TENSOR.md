# Relative tensors of weak Cat actions

This crosswalk follows the weak relative tensor theorem and the comma normalization lemma at manuscript revision `458ff36a`. Lean names are under `ContextualComposition`.

## Weak factors, universal property and representable units

The weak relative tensor theorem in the [relative-construction manuscript](../delivery/One_relative_construction_for_context_content_and_effects.tex) takes covariant and contravariant weak Cat actions over the same middle category. At fixed outer endpoints, `RelativeTensor.universalProperty` identifies functors and natural transformations out of the quotient with independently specified pseudobalanced cocones and their maps. The quotient retains native product-category arrows and inverts the designated middle balances subject to the weak compositor and unit laws. In the explicit collapsing action, `RelativeTensor.Collapse.product_noniso` and `inserted_iso` separate invertibility before and after insertion.

`RelativeTensor.LeftUnit.equivalence` and `RelativeTensor.RightUnit.equivalence` give the two representable unit comparisons at fixed outer endpoints. Their contractions compute on both native arrows and balances. `RelativeTensor.factor_order` identifies the two orders of changing strong factors on the whole quotient functor. `RelativeTensor.bifunctor` packages the joint action on strong factor transformations and their directed modifications. The declarations and their defining files are registered in the package theorem index.

## The actual tensor of the presented factors

For the comma normalization lemma in the [independent interaction criterion](../../../interaction/independent-criterion/General_Independent_Interaction_Criterion.tex), `RelativeTensor.Presented.equivalence` compares the actual generic quotient of the two presented factors with the normalized target at fixed endpoints. Its two comparison functors act on native arrows and on the invertible balances. The independently defined endpoint diagrams extend these comparisons to endpoint changes. The indexed result uses the generic weak tensor and the strong comparison squares of these presented factors.

`PseudonaturalInverse.equivalence` constructs an adjoint equivalence of Cat-valued pseudofunctors from a strong transformation whose component functors are equivalences. It preserves the original forward transformation. The unit, counit and triangle are constructed at the indexed level. Applying this result to the comparison gives the indexed adjoint equivalence recorded in the theorem index under the RelativeTensorIndexedEquivalence module. Arbitrary weak factors still require their own hypotheses to satisfy a comma normalization formula.
