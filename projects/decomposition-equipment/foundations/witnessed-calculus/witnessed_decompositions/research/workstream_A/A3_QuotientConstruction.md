# A3 generic quotient construction

Author submission, 2026-10-24 UTC. This is a Lean-checked implementation candidate, not independent acceptance of A3. Contract v0.1-proposed, SHA256 47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e; the exact A3 freeze and its non-author 18:21 UTC pre-attempt PASS apply. Sections 2, 3, 13, 15, and 16 remain binding.

## Quantified theorem

Fix any interface type V : Type u, any Quiver.{v} V, any Calc.{u,v,z} V, and any ParallelCongruence M. No signature restriction, finiteness, decidability, termination, normal form, selected-model soundness, or nonempty-profile assumption is made. Construct quotient : Calc.{u,v,z} V with Op c = Quotient (R.setoid c). Full ordered profile descends by R.parallel. The quotient remains in the original operation universe z.

Substitution is defined in every independently prescribed operation fibre. Each quotient fibre element admits a representative in that exact fibre. The construction substitutes chosen representatives and projects the result. quotientSubstitute_project and projection_substitute_eq_of_rel prove simultaneous independence of every outer and inner representative. quotient_substitute_eq proves this fibre operation is literally the packaged quotient calculus's Calc.substitute, not a separate auxiliary operation.

The unit laws are transferred through projection. Associativity first lifts the outer operation and both independent total replacement families, uses M.substituteFamily_assoc, and proves projection commutes with Path.occurrenceTransport, Path.expandFamily, and CalcData.composeAt. It then derives the actual CalcData.composeFamily total associativity law. All component and profile transports are canonical equalities from the existing core. Empty families and repeated identical colours are covered by the unrestricted dependent-family quantifiers; neither is specially identified or excluded.

For every arbitrary target Calc.{u,v,z'} V and every strict F : Calc.Hom M N respecting R, factor F hF is a strict map from the quotient. projection_factor proves its composite with the projection is F; factor_unique quantifies over every strict candidate G. homEquiv gives an explicit bijection between quotient strict maps and R-respecting strict maps. factor_projection proves the identity case, and factor_comp proves target naturality. Compatible maps of arbitrary congruences induce quotientMap, whose projection square, identity law, and composition law are proved.

## Main declarations

All declarations are in WitnessedDecompositions.ParallelCongruence:

- quotientCollection, projectCollection, representativeOperation, projectOperation, projectOperation_surjective.
- quotientSubstitute, quotientSubstitute_project, quotientData, project_subst, projectFamily_surjective.
- quotient_subst_identity, quotient_identity_subst, quotient_subst_assocAt, quotient_subst_assoc.
- quotient, projection, quotient_eq_iff, projection_onOperation_surjective, quotient_substitute_eq.
- Respects, factor, factor_map_projection, projection_factor, factor_unique, factor_projection, factor_comp.
- projection_substitute_eq_of_rel, homEquiv, MapsTo, quotientMap, projection_quotientMap, quotientMap_id, quotientMap_comp.

## Source and verification

- Candidate and stable source: QuotientCalculusCandidate.lean and QuotientCalculusStable.lean.
- Both SHA256: c3fd5aea1d52941d7598a9a5299e08190745c75c35f85d08b12c344819ab5558.
- Imported Congruence.lean SHA256: 4863cd393ce71049cdfe09a6c3d0f223063949ecd4296df2a66d6c66e291caa8.
- Command: source ./env.sh; lake env lean QuotientCalculusCandidate.lean.
- Build result: exit 0, no warnings. Log: logs/quotient_candidate.log.
- Audit source: QuotientCalculusAudit.lean; log: logs/quotient_axiom_audit.log.
- The audited closure of quotient, projection, representative-independence, associativity, actual fibre substitution agreement, factorization, uniqueness, naturality, homEquiv, and quotientMap_comp is exactly propext, Classical.choice, Quot.sound. There are no custom axioms, sorry, sorryAx, placeholders, or native_decide.

Classical.choice enters through Quotient.out and is explicitly disclosed. It selects an arbitrary representative, not a normal form. All independence, typing, and algebraic laws are proved; no decidability or executable normalization claim is made. There is no finite test domain masquerading as a universal proof.

## Failed strategy and remaining scope

A direct dependent rewrite of the outer substitution in total associativity could not produce a well-typed rewrite motive because the second family depends on its actual composite profile. This was only a proof-engineering failure, not a mathematical obstruction. The final proof uses an independent expanded-profile family, proves the composeAt law, and canonically transports back to composeFamily. No target weakening was needed.

This candidate does not itself instantiate the quotient with Presentation.congruence E or prove the presentation-specific all-models equivalence, satisfy the required mixed-interface example suite, or accept A3. Those remain with the integration owner and independent reviewer. The generic universal property is available at arbitrary target universes, and the quotient itself is available in the source operation universe for the all-models separation argument. A1/A2 acceptance is not assumed by author build success. No public module or obligation ledger was modified by this attempt.
