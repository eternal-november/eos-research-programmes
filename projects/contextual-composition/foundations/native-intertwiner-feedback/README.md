# Native-intertwiner lifting of state feedback

[Manuscript](Native_Intertwiner_Lift_of_State_Feedback.tex).

The construction uses all permitted state intertwiners with native transition 2-cells, rather than requiring comparisons to factor through directed slides. Coherent pure actions give sequential composition and retained-state feedback. An explicit pure-layer exactness condition lifts directed parallel composition; a relative-quintet lax-functor calculation derives its coherence. Monoidal pseudomonad unit laws supply that exactness in the concurrent-pseudomonad Kleisli construction, with the remaining symmetry and pure-interface assumptions stated separately.

## Dependencies and scope

- [Coherent pure-action state extension](../action-state-feedback/README.md) supplies the held-body assembly conventions and typed feedback comparisons.
- [Directed state and relative parallel constructions](../directed-state-and-relative-parallel/README.md) supply the smaller directed-balance comparison.
- Ordinary KSW state machines and initialized effectful Mealy homomorphisms are recovered and credited to the established literature. Their existing ordinary universal properties are not claimed as new.
- This does not transfer the old directed-slide universal property to the larger hom categories, solve arbitrary shared-interface admission, or establish instantaneous trace/yanking.

## Verification

Written categorical proofs and source comparisons only. No proof-assistant certification or executable semantic test is claimed. TeX compilation is not required. `MANIFEST.json` records SHA-256 hashes of the two source files.
