# B1/B2 non-author pre-attempt target-depth review

**Decision: PASS — clearance to attempt the frozen positive targets, not acceptance of results.**

Reviewer: `/root/review_refinement_target_depth`, separate from the author
`/root/prove_refinement_obligations`. Review completed 24 October 2026 at
22:38 UTC. This is agent-managed non-author review, not external human review;
shared model/tooling limitations remain. The reviewer did not author the target
document or any B1/B2 proof implementation and edited no mathematical source.

## 1. Exact reviewed baseline and chronology

The governing contract is `research/CompletionContract.md`, version 0.1 proposed
24 October 2026, SHA256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
The reviewer independently computed this hash. Sections 2, 3.1–3.6, 5, 13, 15,
and 16 were inspected; neither the contract nor its M-positive discharge rule
has been weakened. The user authorized pursuing B1 and B2. This review does not
authorize B3/B4 or promote A4's local verification to full acceptance.

The exact author target reviewed is:

`witnessed_decompositions/research/workstream_B/B1_B2_Targets.md`

SHA256:
`37912984dfcd045bb504e738823f8194e933975d5d94e043da50253cf94c8092`.

It contains the complete binding B1/B2 acceptance clauses, frozen inputs,
quantifiers, target statements, nonpassing shortcuts, dependencies, evidence,
and the positive-only branch. Its historical "pre-proof review candidate" and
"Pending" labels should be preserved; this separate record supplies the later
decision. The author reported no proof implementation had begun when presenting
that hash. The reviewer issued clearance by direct message at 22:37 UTC, after
reading the exact file. No after-the-fact target repair is represented as an
advance gate.

Accepted dependency evidence inspected:

- `Results_Workstream_A.md`, hash
  `50e8974e8a8a1f918df13af66b9ee272f18fa9e823189a6f52d871ad95af08bf`.
- `Acceptance_and_Evidence.md`, hash
  `f1c246801a1391980b37c709b356144f847fa9e1ed8bc3dea17cc292cad8ba05`.
- The accepted A1 arbitrary-calculus/fibre comparison, A3 quotient construction,
  and presented-universal-property proof dossiers.
- Actual `Core`, `Calculus`, `TreeOccurrences`, `FreeCalculus`, `FreeExtension`,
  `QuotientCalculus`, `PresentedCalculus`, and `PresentationExamples` Lean source.

The A1–A3 reports record acceptance, not merely successful authors' builds. This
pre-attempt review checks suitability of those inputs; it is not a new full
reproduction of their historical acceptance runs.

## 2. Cheapest technically compliant solution and intended depth

### B1

The cheapest compliant route is to keep the existing structural substitution
forests as arrow data, prove grafting injective for a fixed source by induction,
and use that actual forest recovery to simplify category-law proofs. Prove an
independent labeled-address prefix characterization and antisymmetry by
structural induction. Define legal one-primitive-corolla executions independently
of partial orders, identify their events with the added vertices ordered by
ancestry, and prove that their orders are exactly the linear extensions. The
elementary insertion argument connecting linear extensions by adjacent
incomparable swaps then gives the complete chronology result. Existing A1
occurrence equivalences can be reused, but must be linked to the actual new
arrow composition, including three layers and typed components.

**Does this meet the intended B1 goal? Yes.** It establishes all the distinctions
and boundaries B1 asks for uniformly over arbitrary signatures, rather than
adding artificial structure. It is expected to be standard infrastructure, not
an independently major research contribution. A short correct proof at this
strength passes; extra labor or new terminology would add no acceptance value.

### B2

The cheapest compliant route is a single general construction from an arbitrary
accepted `Calc`: an arrow is a tuple at every original occurrence with a checked
substitution endpoint. Compose tuples by actual typed occurrence splitting;
derive their category laws from the existing calculus laws. Map each entry under
an arbitrary strict calculus morphism and prove the functor laws. Specialize to
the free calculus and compare explicitly with B1's structural forests. Use the
actual A3 associative quotient for a witness-retaining, mixed-interface example
where two distinct occurrence tuples have the same composite. State elementary
operation-injectivity and tuple-liftability criteria, rather than claiming that
evaluation generally recovers syntax.

**Does this meet the intended B2 goal? Yes.** It covers arbitrary lawful targets,
not a hand-built associative case, and supplies the requested nonthin quotient
boundary. The frozen draft also proves nonfullness of the quotient comparison
on the displayed raw target. These are useful infrastructure and precise limits;
they do not claim B3's categorical-quotient comparison or B4's classification.

### Excluded cheap substitutes

| Proposed shortcut | Why it does not pass |
| --- | --- |
| A reachability proposition with category laws inherited from implication | Contract B1 minimum floor; B1-R requires actual forests and separately proves recovery. |
| A free category of execution traces | Contract §2.4 and B1 minimum floor: independent interleavings are not different raw refinements. |
| Define prefix as existence of a graft forest | B1 artifact and B1-P require an independently described labeled-address criterion. |
| Define histories to be linear extensions | B1 artifact and B1-P require independent legal executions and a proved correspondence. |
| Check two sample commutations or count leaves | B1 artifact/minimum floor and B1-O/P require all finite histories, ordered typed occurrences, and address transport. |
| Infer raw antisymmetry from increasing leaf count | Nullary and unary tests invalidate that argument; B1-R/P require actual antisymmetry. |
| Name a semantic category, or prove only total substitution associativity | B2 artifact/minimum floor and B2-S require composition and equalities of retained tuples. |
| Quotient tuples because their composites evaluate equally | Contract §2.4 and B2-S/Q explicitly retain tuple segmentation and require nonthinness. |
| Show two trees have equal evaluations in one selected target | B2 minimum floor first requires arbitrary-target category and functor constructions. |
| Use a one-object associative example as the principal certificate | Contract §3.5 and B2-Q require actual mixed-interface contextual coverage. |
| Use indiscrete witness semantics as a faithful-comparison certificate | B2 tests explicitly make witness-discarding semantics a negative control. |
| Assume fullness, or advertise raw-source categorical faithfulness as recovery | B2-F gives independent operation/lifting hypotheses; raw hom-faithfulness is automatic and therefore does not measure recovery. |
| Claim integrated scientific novelty from these standard constructions | Contract §§1.1, 3.2, 3.6 and the target scope leave the stronger integrated packages open. |

No tightening beyond the reviewed draft is necessary. The draft has already
closed the natural cheap-solution loopholes before proof work begins.

## 3. Frozen B1 targets, hypotheses, and evidence

**Inputs:** arbitrary interface type and quiver, arbitrary typed signature, all
finite accepted trees and ordered paths, with unary and nullary generators
enabled. No finite signature, decidable equality, inhabitedness, reconstruction,
exchange, copying, or internal-vertex-replacement assumption. B1 depends on A1.

**B1-R (L):** for every output component `c`, actual arrows `t → u` are
`{σ : Tree.Substitution t // Tree.graft t σ = u}`. Identity is the identity
forest. Composition is `Tree.compose` with the necessary equality transport of
the second forest. Prove endpoint correctness, all three category laws as arrow
equalities, and an actual category instance. Prove fixed-source graft injectivity,
so every hom is a subsingleton, and prove both-way refinement implies literal
tree equality. The full construction is the disjoint union over outputs; a
fixed-output implementation is not a one-interface restriction.

**B1-O (L):** construct the component-preserving equivalence
`Leaf(graft t σ) ≃ Σ l : Leaf t, Leaf(atLeaf t σ l)`; identify the replacement
at each original leaf after composed forests; prove both three-layer
parenthesizations yield the same ordered nested occurrence; connect this to
`frontierLeafEquiv`, `profileSubstitutionEquiv`, and `slotExpand`. Equal labels
never identify distinct occurrences.

**B1-P (P or L):** independently define finite child-ordinal addresses with
arity validity, and prove raw refinement iff every source internal address
persists with exactly its generator witness. Recover each inserted tree as the
target subtree at that source leaf address. Show this subtree address exists
with the required component, including nullary branches. Prove the event-poset
and chronology theorem for all finite forests and all complete atomic histories:
legal executions correspond to linear extensions, and equality of forests is
equivalent to connection by adjacent swaps of independent events. Primitive
events are inserted corollas; identities do not create events. Macro-graft
schedules expand into these atomic histories, not a false swap theorem between
different numbers of macro steps.

Address transport is concatenation of the original leaf address and local
address; nested concatenation is associative. Moving ordinal frontier ranks
must instead follow ordered block expansion. The general rank/correspondence
proof must cover an empty inserted block, which removes exactly one addressed
leaf. Neither a stable address nor an ordinal is merely a component label.

**Nonvacuity and negative controls:** two equal labels receiving different trees;
independent events in both orders; dependent parent/child events whose reversal
is illegal; unary chains; nullary insertion; a rejected internal-vertex
replacement; nontrivial three-layer correspondence; and changing frontier ranks.
At result review, rejection of internal-vertex replacement should demonstrate
the concrete obstruction (for example changed existing root label), not merely
omit an API. The prefix theorem provides the reusable explanation.

## 4. Frozen B2 targets, hypotheses, and evidence

**Inputs:** arbitrary lawful `Calc M`, arbitrary strict calculus morphisms, and
the accepted arbitrary-target free interpretation. Target operation universes
remain independent as supported by A2. B2 depends on A2, A3, B1; A3 is needed
for the certificate, not to restrict the general target class.

**B2-S (L):** at every whole `c`, include all objects `M.Op c`, not just image
objects. Define arrows by
`{f : M.Family(M.profile a) // M.subst a f = b}`. Each entry retains its full
profile, output, length, and position. Composition pulls the second tuple back
through canonical expanded occurrences and substitutes separately into every
first entry. Prove endpoint correctness and category laws as equalities of
tuples. The target calculus laws are legitimate hypotheses; tuple-category laws
must be conclusions. Accepted `Calc` already supplies the representation, so
"where representation permits" cannot be used to move this general construction
or its functor laws out of Lean.

**B2-F (L plus P general comparison):** every strict `H : M → N` induces the
entrywise refinement functor with canonical profile transport; prove its unit
and composition laws and compatibility with identity/composite calculus maps.
Give inverse identity-on-object comparisons between raw forests and refinement
tuples for the free calculus. Identify the A2 evaluation specialization.

The distinction hypotheses are frozen separately:

1. Componentwise operation injectivity reflects operation/object equality and
   makes the induced maps on fixed semantic hom-tuples injective.
2. Raw-source categorical faithfulness is automatic from thinness, even for
   lossy semantics. It gives no object recovery or fullness certificate.
3. For a semantic arrow between evaluated raw `t,u`, assume each entry lifts to
   an exact-profile tree and interpretation is injective on operations at the
   whole `c`. Then prove existence and uniqueness of the lifting raw arrow.
   Mere operation injectivity without entrywise liftability does not promise
   reflection of arbitrary semantic refinement existence.
4. A strict calculus isomorphism induces a refinement-category isomorphism.

These are sufficient, explicitly conditional criteria, not a B4 classification.
The associative quotient must expose which hypotheses fail rather than
pretending evaluation has preserved presentation objects.

**B2-Q (L/P plus executable tests):** instantiate the actual A3 generated
congruence with typed associativity equations, not the kernel of a selected
model. For repeated loop `x` and binary `μ`, prove
`L=μ[μ,id] ≠ R=μ[id,μ]` as raw trees but `[L]=[R]` in the quotient. Exhibit
two parallel semantic arrows with tuples `([μ],[id])` and `([id],[μ])`, and
prove their inequality from the different first-entry profiles (lengths 2 and
1). Their equality of total composites must not erase this difference.

Raw `μ→L` and `μ→R` have different target objects; they are not parallel raw
arrows. With raw target fixed at `L`, prove that the right-expansion semantic
arrow cannot lift. Show this phenomenon in a genuine mixed-interface context
with at least three distinct interfaces and nested trees with at least four
ordered leaves, including separately addressable repeated components. Retain
a nontrivial statistic distinguishing unary witness choices in the quotient.
The unbounded associative schema is a certificate family within B2, not a claim
to have proved B3 for an unbounded family of categorical completions.

**Nonvacuity and negative controls:** actual equal-valued distinct trees;
parallel unequal occurrence tuples; composition with a further nonidentity
refinement; unit/associativity checks; mixed-interface and four-leaf coverage;
surviving witness distinctions; and witness-discarding semantics as a negative
control. That control must still obey full-profile typing: an indiscrete target
per admissible profile is legal, while erasing profiles is not a `Calc` model.

## 5. Evidence boundary and eventual acceptance gate

The frozen targets require source, complete P arguments, discriminating tests,
named Lean theorem statements and axiom closures, baseline-preservation hashes,
a reproducible build, failures/negative controls, and a concise results report.
No custom axiom, `sorry`, `admit`, unchecked computation oracle, or assumed
conclusion is permitted. Standard classical choice must be disclosed where used.
Finite computations are C evidence only; they do not replace the arbitrary
prefix, chronology, semantic category, or comparison theorems.

The final reviewer must inspect actual proofs and declarations, not rely on this
target review or the author's report. Correctness and scientific scope require
separate verdicts. A successful build alone proves neither mathematical scope
nor overall program completion. An obstruction to either M target requires a
baseline/amendment decision and cannot be relabeled as a passing negative branch.

**Pre-attempt conclusion:** the exact reviewed targets meet the intended bounded
B1/B2 depth and exclude the cheapest vacuous substitutes. Proceed without a
material amendment. Proof completion, independent reproduction, and result-level
acceptance remain open.
