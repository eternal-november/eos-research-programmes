# Homogeneous polynomial substitution and joint feedback

[The manuscript](Homogeneous_Polynomial_Joint_Feedback.tex) constructs a native joint-substitution bicategory for homogeneous polynomial content: every global content grade has one fixed finite arity, while its shape and output values can depend on the actual preceding witness. Composition uses all compatible joint laws and actual coefficient limits, with a universal native-cone characterization. The whole global shape family and its coefficient arrows remain present, including unused labels.

The source is an explicit class of the [original independent interaction criterion](../../interaction/independent-criterion/General_Independent_Interaction_Criterion.tex): the product of the discrete nonnegative scalar rig with a cocartesian-additive symmetric rig, together with independently specified homogeneous polynomial content. Augmented vector spaces give nonfaithful native coefficients. A locally faithful oplax bridge selects the original conditional independent law inside the joint assembly; its comparison is generally not invertible and is not claimed locally full.

Shared-state feedback equates one input state with every output state. On positive-degree state-bearing hom categories, its retained-endpoint version is a homwise coreflection onto the full subcategory with equal state legs. Nested state equalities commute, and composition of retained closed processes maps directionally into closure of their composite. Separately hiding state before composition loses matching information and has no general projection-preserving comparison. Nullary state deletion is treated as hiding, not feedback.

This construction extends the [global-writer coupling-span bridge](../native-feedback-and-joint-assembly/Joint_Coupling_Span_Bridge_With_Global_Writer.tex) and uses the [native multilimit machinery](../native-multilimits/README.md). It does not cover global grades mixing different arities, arbitrary original contentads, infinite recurrence, or the complete [v0.2 extension target](../../contracts/Native_Feedback_and_Interaction_Extension_Contract_v0_2.tex). Variable arity can create outcome-dependent occurrence routing; finite limits alone do not supply its missing admission/comprehension law. No symmetric monoidal structure on all varying-degree homs is asserted. Finite recursive unfoldings can have different numbers of external leaves even when the original degree is fixed and greater than one, so this homogeneous target is not automatically closed under recursive grade construction; integration with that construction is not claimed.

## Checks

Run the standard-library exact rational regression with:

```sh
python check_homogeneous_substitution.py
```

It checks conditional witness weights under two binary-tree bracketings, distinct independent and shared binary laws, the directed branching feedback separation, nested state equalities, the nullary probability case, and the kernel of the augmented-vector coefficient comparison. These finite diagnostics do not replace the general native coefficient and coherence proofs. The written argument was independently reviewed; no proof-assistant certification or TeX compilation is claimed.
