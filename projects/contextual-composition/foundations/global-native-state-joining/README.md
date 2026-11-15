# Global native state joining and directed parallel

This general categorical continuation extends [native state assembly](../native-state-assembly/README.md). The process input remains a bicategory with the stated strong pure actions; the state base is a symmetric monoidal bicategory. The results retain native state maps and state two-cells rather than quotienting them away.

## Results

- [Two-level normalization](Two_Level_Native_State_Normalization.tex): the actual inner witness of a nested native three-cell is retained as a second state two-cell. Unit-framed nested homs are biequivalent to explicit two-state-list homs, yielding local flattening.
- [Global joining](State_Base_Change_and_Global_Finite_Joining.tex): a strong symmetric monoidal change of state base induces a trihomomorphism. Reversed finite tensor gives global finite-depth joining; monoidal equivalences supply correctly unit-whiskered and body-conjugated block-joining comparisons.
- [Directed parallel compatibility](Higher_Directed_Parallel_and_State_Base_Change.tex): under the separate pure-time-layer exactness assumption, the specified parallel operation lifts as a lax functor of tricategories, compatible with state-base change. Its effectful compositor need not be invertible. Its coherence uses the original directed interchange equations, not structural state coherence alone.

## Scope

These are independently reviewed written proofs, not a mechanization. The finite-depth presentations are built directly over the original bicategorical process doctrine. They do not establish unrestricted state iteration on arbitrary process tricategories, a general higher state pseudomonad or feedback evaluation universal property. Neither arbitrary shared-diagonal synchronization nor instantaneous feedback follows. The directed-parallel theorem is not a claim to have specified every additional coherence of a symmetric monoidal tricategory.

The hypotheses distinguish strong pure-strand actions from pure-time-layer exactness. Native three-cell witnesses cannot be discarded when the process input itself has nontrivial three-cells. Concrete operational examples are not premises of the construction.

## Verification and literature

The source references the prior native-state construction and the exact Gurski/Caviglia conventions for trihomomorphisms, transformations and lax functors. Ordinary state-flattening and monadic feedback strategies are established background, not novelty claims. TeX compilation is not required. `MANIFEST.json` provides source integrity hashes, not proof verification.
