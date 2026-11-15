# Conditional higher native feedback evaluation

This general categorical result continues [generated native state towers](../generated-native-state-towers/README.md). It distinguishes a coherent source construction from the extra semantic data needed to evaluate that construction.

## Reading order

1. [The higher-uniformity boundary](Higher_Uniformity_Evaluation_Boundary.tex) gives a cell-existence counterexample: an ordinary state-map evaluation need not extend to the retained higher native cells.
2. [Local evaluation data](Higher_Uniformity_Local_Evaluation_Data.tex) explicitly present the hom pseudofunctor, retaining each complete state/process witness. This is a standard pseudofunctor presentation, not a new universal property.
3. [Finite-stage evaluation](Conditional_Evaluation_of_Generated_Native_Towers.tex) constructs evaluators at every generated finite depth from independently specified higher uniformity, held-body operations, pure recovery and assembly data. The actual process three-cell remains part of the next stage's input.
4. [Global joining comparison](Global_Joining_Evaluation_Comparison.tex) derives compatibility with ordered state merging and unit insertion from additional semantic joining data. The target need not have a faithful state projection: actual images of source unit-frame normalizations are retained, including uneven unit tuples and binary unit comparisons.

5. [Structured target transport](Structured_Target_Transport_of_Finite_Evaluation.tex) constructs comparisons between the finite evaluations in two targets from explicit local higher-uniformity morphism data. It restricts to interface-identity comparisons and retains the equations against assembly, joining and directed interchange.

## Hypotheses and scope

These are sufficient, explicit semantic hypotheses, not a proof that every process target admits feedback. The held-body and parallel operations must have the specified full-witness formulas and coherent comparisons. Joining requires its higher native naturality and assembly laws; those laws do not follow from a scalar feedback function.

The result is not an unrestricted higher state monad, an equivalence of evaluator categories, a minimal axiom characterization, instantaneous trace, arbitrary shared-diagonal synchronization, or a complete unrestricted concurrency theorem. Ordered joining merges consecutive retained state blocks and inserts empty blocks; it does not copy or delete arbitrary states. No implementation or concrete channel/store language is a premise.

## Foundations and verification

The source construction and notation are in the linked generated-tower package, particularly Native_Three_Cell_Hom_Categories.tex, Generated_Native_State_Towers.tex, and Ordered_Joining_Perturbation_Audit.tex. The two-boundary joining rectangle is written explicitly in the finite-stage evaluation source; no unpublished two-dimensional target presentation is required. Ordinary scalar equations alone do not provide higher witness transport.

Gurski–Osorno's structural symmetric monoidal coherence is used only after native process admission. Pseudofunctor presentation and transport of pseudonatural equivalences are standard mechanisms, explicitly proved where used; no novelty claim is made for them. Written proofs have independent review, not mechanized certification. The finite diagnostic checks ordered-index arithmetic and empty unit tuples, not higher coherence. TeX compilation is not required.

Run the diagnostic with `python3 check_ordered_joining_indices.py`.
