# Changing diagram shapes: transport boundaries and an admitted interaction

The [fixed-shape diagram theorem](../diagram-native-interaction/README.md) does not automatically allow shapes themselves to change. This tranche separates three obligations and provides a positive, explicitly restricted interaction.

## General categorical results

[Changing diagram shapes requires content transport](Changing_Diagram_Shapes_and_Content_Transport.tex) establishes:

- An exact terminal-base criterion: shape restriction must have a left adjoint for content optransport to exist.
- Sufficient indexed hypotheses using fibre colimits preserved by pushforward, with the full opcartesian universal property.
- An exact **universal retained-unit** criterion in that colimit construction: each incoming comma category `(r ↓ target)` must be nonempty and connected. For an individual model this need not be necessary.

It distinguishes transport from a valid one-sided unit. A genuine terminal-base interaction with discrete monoidal C2 lacks a required fold transport. Cartesian Set content has all transports, but a two-object fold sends the retained unit to two points rather than one, so the original unit cannot remain pseudonatural. These do not rule out different shape structures or deliberately lax alternatives.

## Positive family, not only obstructions

[Separated grades and an admissible changing-shape interaction](Separated_Grades_and_Admissible_Shape_Interaction.tex) constructs an actual native crossing from contravariant and covariant strong-monoidal indexed grade doctrines. Its extensions are the pure projections. Composition retains all native grade arrows and uses pullback for context grades and pushforward for content grades.

A semantic realization uses Set-valued diagrams. Shape maps are admitted when their left Kan extensions preserve finite products. This class is closed under composition. Sifted incoming comma categories give a sufficient test; for a fold to the terminal shape, siftedness is exact. The increasing natural-number chain gives a nontrivial admitted fold. A discrete two-object fold fails the unit test; a nontrivial group-orbit fold passes that test but fails product preservation.

## Scope and verification

The categorical construction comes first; Set-diagram calculations are its realization. No probability model, shared-store language, or physical scheduler defines the theory. The positive family does **not** cover arbitrary occurrence-changing content or shared-effect interference. Its two grade doctrines do not change pure interfaces, so no hidden mixed projection formula is assumed. Richer extensions still require their actual compatibility conditions.

The written proofs were independently checked against one-sided module units, native crossing order, strong-monoidal pseudofunctor coherence, shape transport, and the exact versus sufficient criteria. This is not mechanized certification. The underlying Kan-extension, siftedness and indexed-monoidal machinery is established background; no novelty or full-contract completion is claimed. TeX was not compiled. Verify source integrity with `sha256sum -c MANIFEST.sha256`.
