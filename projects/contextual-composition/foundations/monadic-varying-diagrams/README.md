# Monadic occurrence interaction on varying diagrams

[The manuscript](Monadic_Occurrence_Interaction_on_Varying_Diagrams.tex) supplies an occurrence-changing positive family on a pure category whose diagram shapes may vary.

## General construction

The category D(C) contains diagrams of small shape in C and maps consisting of a shape functor plus a natural transformation. Totalization preserves the pullbacks and fibred structure needed for a presented contextad. It does not preserve all finite limits or terminal categories.

An existing native monadic crossing with a Cartesian context lift and its extension comparison transports to D(C). The proof reconstructs the new module crossing on actual representatives and verifies changing-middle balance; it does **not** assume preservation of relative coends.

## Independent-input family

The [effect-fibre occurrence construction](../occurrence-effect-interaction/README.md), specialized to monadic content, supplies the needed presentation from:

- a commutative Set monad T for effect-bearing raw context fibres;
- a finitary Cartesian polynomial monad S for addressed content occurrences.

The resulting interaction over D(Set) admits every outer shape functor. It retains actual native arrows and occurrence addresses. Its content extension applies S, so this is not merely the projection-only separated-grade family.

## Why this does not contradict the shape boundary

The content **grade projection is identity**. Transport therefore has a unique target grade and requires no Kan extension of an independent grade diagram. Its extension is S, which may change pure data and occurrence shape. These are different functors with different roles.

The [general shape-transport obstructions](../changing-shape-interaction/README.md) remain valid for arbitrary grade content. This construction does not eliminate them, claim arbitrary contentads covered, or show arbitrary physical interference admitted. Changing a diagram shape is mathematical structure; interpreting it as participant creation, scheduling, or physical intervention is a separate semantic task.

## Scope and verification

No affinity is needed for the finite addressed crossing. Infinite effects, fairness and arbitrary interference are not claimed. The original independent-input theorem and standard categorical machinery are reused, with no literature-priority claim.

The written proof was independently reviewed for totalization, pullbacks, fibrations, Cartesian monad maps, actual coend representatives, changing-middle balance and the effect/polynomial specialization. This is not mechanized certification. TeX was not compiled. Verify the frozen sources with `sha256sum -c MANIFEST.sha256`.
