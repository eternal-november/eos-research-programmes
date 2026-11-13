# B2 final bridge and functoriality — independent review addendum

**Verdict: PASS for the complete B2 mathematical/Lean scope, at the exact hashes
below and in `B2_CoreQuotient_SubstantiveReview.md`.** The previously pending
raw/free identification, arbitrary raw evaluation functor, unique raw lifting,
and literal functoriality gates are now independently verified. This is a
substantive B2 review, not a claim that the parent has completed final aggregate
packaging/reproduction, B1 acceptance, or the broader research program.

Reviewer: `/root/verify_semantic_refinement_proofs`; 24 October 2026, 23:02–23:04
UTC. Read-only on author sources. Additional reviewer checks are stored under
`/workspace/shared/witnessed_B_20261024/reviews/B2_Independent`.

## Exact additional source identity

Relative to the project root
`/workspace/shared/witnessed_B_20261024/witnessed_decompositions`:

| Source | SHA256 |
| --- | --- |
| `WitnessedDecompositions/RefinementComparison.lean` | `5e588ef5b301d2787cd45518659309750724bad2b46ba73cb76a127895ce37f6` |
| `WitnessedDecompositions/RefinementFunctoriality.lean` | `f3ab104b445c01b812db45e4f8ff7a7995199bd5d7f3b89d46e0b258ab3ea800` |
| `WitnessedDecompositions/RefinementLifting.lean` | `82a027cabd392c4fb76c9c033276bd0eb32ba537a037f99ba4ed7fecef462d6b` |

All earlier core/example/P source hashes remain as recorded in the principal
review. The final source manifest binds the additional audits and regression
files as well. No frozen target or baseline amendment was made.

## 1. Raw/free identification retains actual data

`rawToFreeArrow` applies the inverse of `Tree.profileSubstitutionEquiv` to the
entire structural forest. Its endpoint follows from `profileGraft_eq_graft`.
`freeToRawArrow` applies the forward equivalence to the complete semantic-free
tuple with the same endpoint theorem. Their two inverse equalities are proved
by the actual equivalence inverse laws, not by erasing forests. `arrowEquiv`
therefore is an explicit retained-data hom equivalence for every signature and
whole.

The resulting free-semantic hom is subsingleton because its tuple maps
injectively to a raw hom already proved subsingleton by B1. Using this fact for
`rawToFree_comp` and the two unit comparisons is sound. In particular this is
**not** the excluded shortcut of making arbitrary semantic homs thin:

1. raw and semantic composition already have independent explicit tuple data;
2. an explicit invertible forest/tuple map was proved first;
3. thinness is used only for the free-source specialization where B1 genuinely
   proves unique forest recovery;
4. arbitrary-target semantic laws were proved separately, entry by entry, with
   no cancellation or free-source assumption.

The functors `rawToFree` and `freeToRaw` are identity on underlying tree objects
(the semantic side merely wraps the tree). Both composite functors are proved
literally equal to the corresponding identity. Thus this is the frozen target's
actual category isomorphism, not an unproved renaming or a one-way map.

## 2. Raw interpretation and the exact lifting theorem

`rawFunctor H` composes this explicit raw/free functor with the arbitrary strict
semantic functor. `rawFunctor_map_val` identifies its exact arrow action as the
full-profile transport of entrywise interpretation of the recovered profile
family. Together with the accepted B1 occurrence-preserving forest/profile
comparison this is precisely evaluation of each original leaf replacement;
there is no alternative choice of representatives or tuple segmentation.

`evaluationFunctor M a` uses the accepted strict `Tree.extend M a`, not merely a
recursive fold with unrelated leaf values. Its identity and composition laws
are equalities of complete interpreted tuples.

`unique_raw_lift_of_family` has exactly the noncircular sufficient conditions:
injectivity of the interpretation at the fixed whole, plus a supplied family
whose mapped entries agree with the semantic arrow. It first invokes the
independently checked semantic lifting theorem to derive the missing endpoint;
then converts the resulting arrow to a raw forest. Its mapped-arrow equation
uses the explicit raw/free inverse. Uniqueness is B1 raw thinness. No lift
hypothesis assumes the raw endpoint, categorical fullness, or the desired
existence conclusion.

`rawFunctor_map_injective` is correctly automatic on fixed raw homs and makes
no object-recovery claim.

## 3. Literal strict-map functoriality and isomorphisms

`functor_identity` is literal identity of functors. `functor_composite` uses
functor extensionality and the previously proved full-tuple
`mapArrow_composite`; object maps are definitionally the same. The
`functor_inverse` hypotheses are equality of the given **calculus-map**
composites with the calculus identities. They are exactly the data of a strict
inverse pair, not an assumption that the refinement functors are inverse.
Their conclusion is proved from the identity/composite laws. This provides the
requested refinement-category isomorphism consequence, now also at L level.

## 4. Independent kernel checks against the actual comparison

The reviewer-only `IndependentComparisonChecks.lean` proves
`reviewer_actual_raw_map_not_full` and
`reviewer_actual_mixed_raw_map_not_full`: the **actual implemented**
`(rawFunctor projection c).map` is not surjective on the indicated fixed raw
hom, in the loop and the mixed-interface certificate respectively. A purported
preimage of the right semantic arrow is converted to its exact profile family,
then contradicted by the certified no-lift theorem. This verifies that the
nonfullness statement concerns this functor, not an unrelated family map.
The explicit inverse-functor equality is also instantiated there for arbitrary
signature and interfaces.

An initial reviewer test file omitted `open CategoryTheory`, causing a notation
parse error in its final inverse-functor example. The two no-fullness theorem
proofs already elaborated. Adding the namespace opening repaired this
reviewer-only test; the failed log is retained as
`IndependentComparisonChecks.initial-failed.log`. No author defect or author
source change resulted.

All final source modules are recompiled into the independent fresh dependency
closure, followed by the author's core/bridge example regressions, the reviewer
composite/comparison tests, and the `WorkstreamB.lean` aggregate import.
`rebuild.py`, exact module logs, `result.json`, and the stable before/after
source hashes make this rerun reproducible. The actual core and raw-evaluation
constructions/laws and supplied-family lifting use only `propext` and
`Quot.sound`. The two inverse-functor equality packages and the semantic
composite/inverse functor packages additionally depend on standard
`Classical.choice` through their category-theoretic equality packaging. This
is separate from choice used for quotient representatives or optional
existential lift collection; no custom axiom or unchecked oracle is introduced.

## Final B2 determination

Together, the principal review and this addendum discharge the frozen B2-S,
B2-F and B2-Q mathematical scope positively: arbitrary typed tuple categories,
strict semantic and raw interpretation functors, exact comparison hypotheses,
and a genuine witness-retaining mixed associative quotient with nonthin arrows
and a proved failure of fixed-target raw fullness. The sources do not weaken
the target to equal evaluations or a witness-discarding semantics.

No remaining B2 correctness/depth fix is requested. Parent-level final
acceptance must still bind the aggregate evidence and any separately required
B1 verdict to these exact sources. B3 quotient/completion coherence, B4 recovery
classification, A4 and C obligations are not settled or activated by this
review, and no mathematical novelty claim is being certified.
