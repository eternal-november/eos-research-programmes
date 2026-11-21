# Issue 92: finite distributor grids and uniform continuation

The braiding gives the canonical middle swap in the additive monoidal
structure. The two finite rectangular expansion routes agree on actual
coefficient arrows through the addressed transpose, with both empty axes
included. The uniform-continuation lemma applies to an arbitrary whole-fibre
aggregate map. The opposite-Types probes use finite underlying types and
exercise a missing coproduct injection, unequal arrows with repeated
coefficients, exact tagged computations, and empty grids and fibres.

[Source and scope crosswalk](Source_Crosswalk.tex). The overall augmented
family category, arbitrary carrier partition coherence, and bundled dependent
Fubini remain open at this generality. The existing matrix instance is unchanged.

Run the project axiom audit with `python3 verify.py`. To verify this slice
with the pinned dependencies and run the focused probes:

```sh
lake build +ContextualComposition.RigGridMonoidal
lake env lean checks/RigGrid.lean
```
