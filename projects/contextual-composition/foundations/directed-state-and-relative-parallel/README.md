# Directed state and relative parallel constructions

These are **separate conditional categorical tools**, not a completed feedback/concurrency unifier. They extend the [structured native interaction work](../structured-native-interaction/README.md) while retaining directed native comparisons.

## Results

- [Directed balance](Directed_State_Balance_Universal_Property.tex): a category-valued directed dinatural universal property, without identifying or inverting noninvertible state maps.
- [Native state completion](Native_Directed_State_Completion.tex): sequential composition and its weak coherence for a specified symmetric monoidal process bicategory and state action. The unit-state inclusion is faithful, not generally full. An arbitrary relative pseudomonad is not silently assumed monoidal.
- [Adjointable-state normalization](Adjointable_State_Normalization.tex): when the input state maps have right adjoints, directed balance normalizes to a Grothendieck category of conjugation, equivalently all state-intertwiner cells. Only the chosen state maps need adjoints, not all pure maps. Functional spans give a recovery test with all graph maps.
- [Mixed Fubini](Fubini_for_Directed_and_Invertible_Grade_Contraction.tex): directed and invertible coordinate contractions commute with the required cross-slide compatibility. A walking-arrow example shows why making every pure horizontal balance directed breaks the old representable unit. Network evaluation does not follow merely from this presentation.
- [Relative parallel composite](Relative_Parallel_Composite_Criterion.tex): parallel structure on the independent context/content sides and a parallel-compatible crossing yield a **derived directed sequential/parallel interchanger** on their original relative composite. The proof includes coend descent and coherence. A sufficient pure-strand invertibility criterion is included.

## The important remaining gaps

The parallel theorem assumes the crossing's parallel compatibility as independent input. Deriving that compatibility from geometric hypotheses remains separate. It does not assert the full published concurrent-pseudomonad condition, general feedback compatibility, an instantaneous trace, arbitrary physical interference, or completion of the contract.

The state theorem and parallel theorem have different hypotheses. This package does not pretend that juxtaposing them proves their compatibility. The state completion's full free feedback universal property is not claimed here.

## Literature and research route

[The concise research trail](Feedback_Concurrency_Search_Trail.tex) records requirements, sources, exact contributions and the narrowing of candidate constructions. Hirata's lax Fubini, adjunction mates, Grothendieck constructions, and structured-monad composition are established background. Paquet–Saville's concurrent pseudomonads motivate noninvertible interchange; their theorem is not asserted to prove this relative composite automatically. No novelty claim is made.

## Verification

Independent written-proof review checked the balance relations, weak sequential coherence, adjointable normalization, cross-slide Fubini, coend descent and conditional composite coherence. These are not mechanized proofs. No TeX compilation was requested or run. Verify exact file integrity with:

```
sha256sum -c MANIFEST.sha256
```
