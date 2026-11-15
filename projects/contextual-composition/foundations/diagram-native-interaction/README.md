# Diagram-native interaction and the boundary of dependence

## Main categorical result

[Diagram lifting of a presented native interaction](Diagram_Lifting_of_Presented_Native_Interaction.tex) lifts an existing context/content presentation from its pure category C to the diagram category C^J for any small diagram shape J.

Contexts and content are actual diagrams in their total categories, retaining noninvertible native maps and their interface squares. The crossing acts on the entire representative diagram. The proof establishes literal comma normalization over diagram-valued middle interfaces, rather than assuming diagrams commute with relative tensors. It checks the four crossing comparisons and coherence, and verifies the required representative functoriality for the project's existing O1 construction and its [effect-fibre context variant](../occurrence-effect-interaction/README.md).

A star-shaped diagram can retain a joint context and its native projections to component views. This is a general categorical construction, not a definition in terms of stochastic kernels, channels, stores, or robots. Changing the diagram shape preserves the supplied structure but does not reconstruct missing comparison data.

## Two ancillary dependence results

- [Relational composition of all couplings](Relational_Composition_of_All_Couplings.tex): for a weak-pullback-preserving Set functor, all couplings form a category enriched in relations. Triple-joint existence defines the composition relation; four-coordinate gluing proves associativity. Hiding an intermediate state can preserve composition only laxly and introduce spurious composites.
- [Unique quadrilateral filling](Unique_Quadrilateral_Filling_and_Dependence.tex): under the same weak-preservation hypothesis, unique reconstruction of all quadrilateral effects from two triangle marginals is equivalent to full pullback preservation and uniqueness of all compatible binary couplings. This rules out that particular naive reconstruction of dependence, not richer native witness structures.

These clarify why the [retained-dependence construction](../retained-dependence/README.md) must retain actual joint data. The Rel-enriched category is not asserted to be the native context/content structure or its already-completed refinement.

## Exact scope and attribution

The main result lifts an **already constructed, square-functorial presentation**. It does not prove that arbitrary contextads and contentads interact, that C^J meets the original Set-polynomial existence criterion, or that all desired joint diagrams exist. Conditional native body squares remain essential. Arbitrary interfering dynamics, cyclic joint admission, scheduler implementation, fairness, and infinite effect laws are not discharged.

Functor-category lifting, weak pullbacks, and pseudodistributive machinery are established background. This tranche checks their precise compatibility with the project's retained native presentation. No literature-priority or full-contract-completion claim is made. The presentation hypothesis, actual O1 verification, and limits of the ancillary results are explicit in the proofs.

## Verification

The written proofs were independently reviewed for arbitrary small diagram shapes, (op)fibration sections, object/arrow-level coend normalization, changing-middle native crossing, coherence, and shape restriction. The ancillary results were reviewed for arbitrary maps, empty carriers and the difference between weak and strict pullback preservation. This is not proof-assistant certification. TeX was not compiled. Run `sha256sum -c MANIFEST.sha256` to check the exact sources.
