# Independent B2 core, general comparison, and quotient-certificate review

**Verdict: PASS for the arbitrary semantic category/strict-map functor, the
reviewed general P comparison, the explicit lifting criterion, and the actual
associative-quotient certificate.** The final raw/free bridge is separately
reviewed in an addendum once its author freezes it; this report alone is not a
whole-B2 acceptance or final aggregate-reproduction certificate.

Reviewer: `/root/verify_semantic_refinement_proofs`, independent of the author
`/root/prove_refinement_obligations` and its implementation workers. Review date:
24 October 2026, beginning 22:58 UTC. This is agent-managed non-author review,
with shared-model limitations, not external human certification. The reviewer
made no changes to author sources. Additional checks live only in the review
folder.

## Binding target and exact sources

Project root is `/workspace/shared/witnessed_B_20261024/witnessed_decompositions`.
I read the complete CompletionContract §3 completion/acceptance rules, the B2
acceptance clause, and the frozen B1/B2 target. B2 is M-positive: its no-lift
example is evidence within a constructed positive theory, not an obstruction
branch substituted for the required construction.

| Source | SHA256 |
| --- | --- |
| `research/CompletionContract.md` | `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e` |
| `research/workstream_B/B1_B2_Targets.md` | `37912984dfcd045bb504e738823f8194e933975d5d94e043da50253cf94c8092` |
| `WitnessedDecompositions/SemanticRefinement.lean` | `d51a7902144328a1494f2889b44381dbe45af0b2c5da6e38b11d04c16bf55f65` |
| `WitnessedDecompositions/RefinementExamples.lean` | `903b4269320acd3dbe94f4f876544d741bb9ba84a99edf5952edd73e4afa82dd` |
| `WitnessedDecompositions/RefinementLifting.lean` | `82a027cabd392c4fb76c9c033276bd0eb32ba537a037f99ba4ed7fecef462d6b` |
| `WitnessedDecompositions/RawRefinement.lean` (B1 dependency) | `7de14174296acdc507dc078eb5a57bf4d6cba18d4964d143b33e648ee3b8f059` |
| `research/workstream_B/B2_GeneralComparison.md` | `5df666c820c4876b9beed8529cdbb5d3968ff72763e3162287f14a5a1afaaea4` |
| `research/workstream_B/B2_QuotientCertificate.md` | `30a461e75330c50351093e437ebb3151add4f3ce6506932f44acd405b2fab382` |

The only source change during the fresh compile was a documentation-only
clarification of the finite checker's project-root-relative path. The checker
already existed under `research/workstream_B/examples/`; it was not missing.
The listed final document hash incorporates this clarification. Frozen Lean
sources did not change. All 106 files in the imported-baseline manifest were
hash-checked unchanged. This supplements, rather than replaces, earlier A1–A3
acceptance and the separately assigned B1 review.

## 1. Generality and actual arrow data: PASS

`SemanticRefinement.Arrow M a b` is exactly the subtype of
`M.toCollection.Family (M.profile a)` with endpoint `M.subst a f = b`.
`Object M c` merely wraps **every** operation of the fixed whole; it imposes no
image restriction. The source has arbitrary interface and component universes,
arbitrary lawful `Calc`, finite typed paths of any arity, and independent source
and target operation universes for strict maps. No finiteness, decidability,
normalization, inhabited fibre, injectivity, cancellation, or nonempty-profile
assumption is added.

Because a family is a dependent function over actual `Path.Slot` occurrences,
its entries retain both operations and their individual full profiles. A total
composite equality is only endpoint proof data. There is no quotient by equal
totals, no label-keyed lookup, and no mere-reachability definition of arrows.
Repeated equal components can receive unequal replacement operations.

The intermediate `RefinementForest.Arrow` retains the same entire family with
its expanded target profile. `toForest_injective` is legitimate subtype-data
injection: it compares family values, not substituted totals. Its use to derive
semantic category laws therefore does not smuggle in cancellation.

## 2. Tuple category laws and strict functor: PASS

I traced `Calc.composeAt_assoc` through the accepted full-profile occurrence
API. The proof explicitly forms first-layer profiles, restricted second-layer
families, and their component-preserving profile equalities. After aligning the
outer profile casts, it invokes target `subst_assocAt` **inside each original
entry**. The remaining innermost family equality is exactly
`Path.expandFamily_assoc`, based on triple-occurrence coherence. This is an
actual tuple equality, not an inference from equality after outer substitution.

The two tuple unit laws similarly use singleton occurrence coherence and
operation units entrywise. Nullary entries cause empty subfamilies; no fake
occurrence or nonempty assumption is inserted. `RefinementForest.comp` uses
only endpoint-profile equality elimination to reindex the second family.
`SemanticRefinement.comp` then derives its operation endpoint from the input
`Calc.subst_assoc`. The concrete category instance uses these proved laws.

`Calc.Hom.map_composeAt` proves entrywise naturality of substitution with profile
casts; its final transport step is `Path.expandFamily_natural`. The resulting
`mapArrow` maps all entries and derives its endpoint by strict substitution
preservation. `mapArrow_id`/`mapArrow_comp` prove laws of the actual functor.
Identity/composite strict maps agree on entries through the proved canonical
reindex identities. This covers arbitrary target calculi, not only the quotient
model or free trees.

## 3. Comparison hypotheses: PASS at their stated strength

The complete arguments in `B2_GeneralComparison.md` remain at the same hash as
the prior independent P review. I independently checked their core logic and
matching APIs rather than treating that review as a substitute for inspection.

* Componentwise operation injectivity reflects equal object values and each
  entry of a fixed-hom tuple; `mapArrow_injective` reverses the common profile
  transport before applying injectivity at every slot component.
* Raw-source hom-faithfulness is correctly distinguished from object recovery
  and fullness: a map from a subsingleton hom is automatically injective. This
  is not described as retaining presentation distinctions.
* `liftArrow_of_family` receives a tuple lift, not an arrow or an assumed source
  endpoint. Strictness plus the target arrow gives `H(a[f]) = H(b)`; injectivity
  **at the fixed whole** derives `a[f] = b`. Thus the important endpoint step is
  proved, not hidden in the lift hypothesis.
* Equality of each mapped operation to its target entry already enforces its
  exact full profile by strictness. An output-only representative is not being
  accepted as sufficient. Empty tuples are covered.
* Optional carrier-surjectivity-to-hom-surjectivity collects entrywise witnesses
  using disclosed standard choice. Bijectivity then combines this with the
  independent hom-injection proof. No fullness or faithfulness hypothesis is
  assumed. General-source uniqueness needs entrywise injectivity; raw uniqueness
  comes instead from B1 thinness.
* The strict-isomorphism consequence in the P report follows by applying the
  explicit construction to the strict inverse. It is not a claim that arbitrary
  quotient projections are refinement-category quotients.

The profile-retaining, witness-discarding negative control is mathematically
lawful: operations are full typed paths at the fixed whole, and substitution is
path expansion. It is correctly labelled a negative control, not the main model.

## 4. Actual associative quotient and nonfullness: PASS

`RefinementExamples.Declared` is the unbounded family of typed associativity
corollas indexed by four natural-number interfaces. `equations` is exactly
that declaration relation, and `M` is `Presentation.quotient equations`, whose
accepted definition uses the least generated parallel congruence. The example
does not define equality by a statistic or hand-identify a finite pair.
`associativity_evaluated` uses `Presentation.quotient_eq_iff` and the actual
declaration derivation.

The shape discriminator retains leaves and distinguishes the two repeated-label
binary groupings. A preorder generator list alone would not, but is not used.
Thus object collapse is proved between literally distinct trees.

`leftArrow` and `rightArrow` are genuine parallel semantic arrows with fixed
source and fixed quotient target. Their first entries have complete profile
lengths two and one, respectively. Equality of arrows would imply equality of
these entry profiles and hence `2 = 1`. This proves real nonthinness rather than
merely two names or two endpoint proofs for one arrow.

Crucially, the no-lift theorem quantifies over **all** raw profile families at
the fixed raw source. Any family grafting to the fixed left target must equal
the left family by `Tree.graft_injective` and the A1 family/forest equivalence.
Its image therefore cannot be the right tuple. It excludes alternate quotient
representatives as well as the obvious failed right expansion. This proves the
claimed nonfullness boundary, not just noninjectivity on objects. Quotient
entries have representatives; it is whole-operation injectivity that fails.

The same phenomenon is embedded in the genuinely mixed context with interfaces
0, 1, 2 and original component sequence `(c01,x,x,c12)`. Source and target have
four and five leaves. Mixed arrow inequality examines the appropriate actual
slot; mixed equal evaluation follows from strict contextual substitution. The
mixed no-lift theorem again quantifies over every candidate family.

`quotient_retains_red_count` independently derives invariant preservation from
the generated congruence and additive witness weights. It separates red and
blue at every interface pair and in the mixed context despite the nonempty
associativity theory. The zero witness is not silently declared a unit: the
nullary refinement removes exactly its frontier contribution, while preserved
binary count separates its composite from the identity.

## 5. Discriminating execution and independent proof checks

Fresh reviewer build output is in `reviews/B2_Independent/fresh-lean`, with
logs and hashes alongside it. `rebuild.py` compiled all 18 relevant baseline and
new source modules in dependency order with the fresh output directory first
on `LEAN_PATH`. Therefore stale project oleans did not supply any project
module in that tested closure. `RefinementLifting.lean` was subsequently built
into the same reviewer-only directory. Lean version is the pinned 4.35.0.

`AllB2CoreExampleAxioms.lean` prints the transitive axiom dependencies of all
137 named definitions/theorems in the semantic-core and example files. Core
closures contain only `propext` and `Quot.sound`; actual quotient examples also
contain disclosed `Classical.choice`. The separate lifting audit confirms no
choice for supplied-family lifting and choice only in the optional collection
of existential operation lifts. No custom axiom, `sorryAx`, or unchecked oracle
occurs. A comment-stripped source screen found no `sorry`, `admit`, `axiom`,
`native_decide`, or `implemented_by` declaration in the tested new files.

The author Lean regression tests compile. More importantly, the reviewer-only
`IndependentCompositeChecks.lean` kernel-checks the first-entry profile lengths
**after actual nonidentity quotient-arrow composition**: two for the left
composite, one for the right. It proves `leftThenRedArrow ≠ rightThenRedArrow`,
not just their already-typed endpoints. It also checks concrete unit laws,
associativity, and units around the nullary arrow. Its axiom closure remains
exactly the disclosed standard quotient axioms.

The finite checker was read and rerun successfully: 81 typed associativity
instances, three parallel loop pairs, 750 two-layer checks, 375 three-layer
checks, and 183 nullary-containing second layers. It rejects a wrong component
at an original slot and contrasts red/blue retention with profile-only erasure.
Its independently defined additive-statistic model is lawful by concatenation
and addition, but **not asserted to be the exact A3 quotient**. These are C
regression checks, not unrestricted congruence completeness or Lean proofs.

## Scope and remaining gates

This review found no correctness or target-depth defect in the reviewed slices.
The sources deliver the required arbitrary-target tuple construction and
nondegenerate quotient comparison, not the excluded equal-evaluation shortcut.
They correctly claim standard infrastructure, not novelty or completion of an
integrated scientific bundle. A4, B3/B4, C and stronger quotient-completion
claims remain unactivated or open as specified.

Whole-B2 acceptance still requires the exact final raw/free bridge and raw
interpretation functor, its independent compilation/audit, and the final
aggregate dossier/reproduction. The author is finishing that separate module;
no weaker result is being substituted for it here.
