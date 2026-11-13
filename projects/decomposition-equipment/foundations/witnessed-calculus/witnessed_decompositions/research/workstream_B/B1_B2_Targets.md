# B1/B2 exact target freeze — pre-proof review candidate

Prepared 2026-10-24. **TARGET PREPARATION ONLY; implementation not begun.**
Contract: `research/CompletionContract.md`, version 0.1 proposed 24 October 2026,
SHA256 `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
The authoritative contract and accepted A1–A3 sources remain unchanged.
Authorized scope: B1 and B2 only; B3/B4/C are not activated; A4 remains locally
verified/open. Both obligations are M: constructive positive discharge only.

## Complete binding acceptance clauses

### B1 Raw refinement category and occurrence coherence

**Class and claim:** M. Construct the raw leaf-graft refinement category, prove its category laws, and characterize its thinness and antisymmetry for the selected planar syntax.

**Inputs:** A1; leaf-indexed forests and typed grafting.

**Artifact:** Category construction; unique recovery of the graft forest when valid; a proof of the tree-prefix characterization; and a theorem identifying finite graft-event partial orders and showing that complete histories for the same forest differ precisely by interchange of independent events. Specify how event addresses change under grafting and prove the correspondence, not just two sample swaps.

**Discharge:** L for the category laws, typed forest composition, and core occurrence correspondence. P or L for the full prefix and chronology comparison. If raw refinement is a poset, the result must say so; artificial parallel arrows must not be added to make it look richer.

**Tests:** Repeated labels at different positions; independent grafts in both orders; a dependent graft that cannot be interchanged; nullary grafts when enabled; and a failed attempt to refine an existing internal vertex rather than a leaf.

**Dependencies:** A1. **Status:** OPEN.

**Minimum passing floor:** Prove raw thinness and antisymmetry as well as the category and chronology comparison. A free category of execution traces, a reachability relation with lost forest data, or category laws proved only after erasing occurrence positions does not pass.

### B2 Evaluated refinements and comparison functors

**Class and claim:** M. Construct the semantic refinement category for a general target calculus and prove that interpretation induces a functor from raw refinements.

**Inputs:** A2, B1, and an interpretation $F(S)\to M$.

**Artifact:** Explicit objects and arrow tuples; the evaluation functor; its identity and composition laws; and sufficient hypotheses for reflecting or preserving the distinctions the report claims.

**Discharge:** L for the basic construction and functor laws where representation permits; P for the general comparison. Provide a genuine example in which two different presentation trees have the same evaluated witness. Provide a justified nonthin semantic refinement example, such as two different original occurrences refined to give the same quotient operation, and identify the arrow data that distinguish it.

**Tests:** The associative binary-tree quotient gives parallel semantic refinements corresponding to different leaf expansions while raw tree-prefix refinements remain thin. A semantics that discards all witnesses is a negative control, not a certificate of faithful comparison.

**Dependencies:** A2, A3, B1. **Status:** OPEN.

**Minimum passing floor:** Construct actual arrow tuples and a functor for arbitrary target calculi, then distinguish the nonthin semantic example from raw prefix refinement. Showing equal evaluations of two trees or naming a category without arrow composition does not pass.


## Frozen inputs, quantifiers, and definitions

All interfaces `V`, quiver component families, and signatures `S` are arbitrary;
there is no finiteness/decidable-equality assumption on these types. Every input
profile is an actual finite typed path. Nullary and unary generators are allowed.
Only finite trees exist. Equality means literal accepted `Tree S c` equality.
No exchange, contraction, hidden chronology, or vertex-replacement operation is
added. B1 depends exactly on A1. B2 depends on A2, A3, and B1 (A3 is used for the
quotient certificate, not for the general semantic category).

### B1-R: actual forest arrows and raw category (L)

For every output component `c`, define

```
Raw.Arrow (t u : Tree S c) := { σ : Tree.Substitution t // Tree.graft t σ = u }
Raw.id t := ⟨Tree.identity t, Tree.graft_identity t⟩
Raw.comp (f : Raw.Arrow t u) (g : Raw.Arrow u v) :=
  ⟨Tree.compose t f.val (transport (congrArg Tree.Substitution f.property.symm) g.val),
    proof from Tree.graft_assoc and f.property and g.property⟩
```

Here `transport` is ordinary equality elimination, not a chosen equivalence.
Prove these are well-typed and satisfy `id_comp`, `comp_id`, and `assoc` as
**equalities of arrows retaining the whole forest tuple**, and give an actual
`Category` instance. The full raw category is their disjoint union over `c`;
no arrows change the whole. A fixed-`c` implementation is the identical
fibrewise construction, not a restriction on permissible interfaces.

For every `t`, prove `Function.Injective (Tree.graft t)` (unique forest recovery).
Consequently every hom is subsingleton. Define reachability by inhabited actual
hom and prove antisymmetry: arrows both ways imply literal equality of trees.
Identify the category with the resulting tree-prefix poset; do not add artificial
parallel arrows. Category laws may exploit the separately proved unique recovery,
but neither arrows nor their composition may be defined by mere reachability.

### B1-O: typed nested-occurrence correspondence (L)

Construct, uniformly in `t` and `σ`, an explicit equivalence

```
Leaf (graft t σ) ≃ Σ l : Leaf t, Leaf (atLeaf t σ l)
```

and prove full component preservation. For composable forests `σ,τ`, prove that
the replacement at each original leaf in `Tree.compose t σ τ` is precisely
`graft (atLeaf t σ l)` by the second-layer forest read through this equivalence.
Prove compatibility of the correspondence for three layers: both parenthesizations
identify each final occurrence with the same ordered triple of occurrence
positions. Link this structural correspondence to A1's full-profile `slotExpand`
correspondence via `frontierLeafEquiv`/`profileSubstitutionEquiv`. Thus these are
actual typed occurrences, not label matching or only a count/frontier equality.

### B1-P: independent prefix and all-history theorem (P, L where practical)

Give vertices and leaves independent planar addresses: finite words of child
ordinals, with arity checked at each traversed vertex. An address records position,
not its component label. Every source internal address retains exactly its
primitive witness and hence all its typed ordered input/output data.

Prove for arbitrary finite trees `t,u` of the same output that a raw arrow exists
iff every internal vertex address of `t` is an internal address of `u` with the
same primitive witness. In the positive case the unique forest at each source
leaf address is exactly the subtree of `u` rooted there. Prove the root address
exists and has the source leaf's component, including closed/nullary branches.
Prove antisymmetry by this characterization (or independent structural induction).
The criterion is independent address-prefix data, not restated existence of σ.

An **atomic graft event** is insertion of one primitive corolla at a current leaf.
For a fixed forest σ, its event set is the internal vertices of all σ_l, tagged
by their distinct source leaf addresses. Order events by strict ancestry within
each tagged tree; events in different trees or incomparable branches are
independent. Prove this is a finite partial order (using reflexive ancestry for
≤), even with nullary/unary witnesses.

A complete atomic history starts at t, performs legal atomic events, and ends
at `graft t σ`, retaining event addresses and generator witnesses. Prove:
1. event histories correspond bijectively to linear extensions of this exact
   event poset; each internal vertex is inserted exactly once;
2. any two complete histories have the same forest iff they are connected by
   adjacent swaps of independent events, after identifying events by their
   source-leaf-tagged addresses; dependent events cannot be swapped;
3. address transport under a graft is concatenation `old_leaf_address ++ local`
   and nested grafting is literal word-concatenation associativity; distinguish
   these stable addresses from changing ordinal frontier indices;
4. explicitly compute the moving frontier rank by ordered concatenation of
   surviving/inserted frontiers, prove agreement with the core occurrence map,
   and show a nullary event removes precisely its addressed leaf;
5. every finite simultaneous or macro-graft schedule expands into such atomic
   histories; chronology comparison concerns that expansion, not a false claim
   that histories with different numbers of macro steps are related by swaps.

Proof of linear-extension connectivity must be supplied, not merely cited;
its standard nature will be credited as infrastructure, not novelty.

### B2-S: arbitrary semantic refinement category (L)

For every lawful accepted `Calc M` and every output `c`, objects are **all**
`M.Op c`, not only the evaluation image. Define actual arrows

```
Sem.Arrow (a b : M.Op c) :=
  { f : M.toCollection.Family (M.profile a) // M.subst a f = b }
```

Thus each tuple includes each operation's own complete profile, frontier length,
and full typed input/output data. Arrow equality is equality of these tuples;
proof fields are irrelevant, but tuple entries and their segmentation are not.
No quotient identifies tuples just because their substituted totals agree.
Identity is `M.identityFamily (M.profile a)`. Composition substitutes, at each
original slot, the appropriate second-layer tuple obtained by the full typed
`Path.slotExpand`/`CalcData.innerFamily` correspondence after endpoint transport.
Prove endpoint correctness and all category laws as actual tuple equality for
arbitrary target calculi, including nullaries. Source `Calc` laws are inputs;
forest/category laws are conclusions, not extra `Calc` assumptions.

### B2-F: comparison functors and explicit distinction hypotheses (L + P)

Every strict calculus morphism `H : Calc.Hom M N` induces a functor
`Ref(H) : Ref(M,c) → Ref(N,c)` by `a ↦ H.map a` and entrywise mapping of the
arrow tuple with the canonical full-profile transport. Prove identity and
composition preservation and compatibility with identity/composite strict maps.
Apply this to A2's interpretation `Tree.extend` and prove agreement, via the
B1-O forest/profile correspondence, with the raw forest evaluation functor.
The raw and `Ref(Tree.freeCalc S,c)` categories have explicitly inverse
identity-on-object functors, not an unproved reuse of the same name.

The comparison report must prove precisely these sufficient criteria:
* A componentwise injective strict map reflects operation/object equality, and
  induces injection on semantic hom-tuples (for fixed source and target).
* Raw-source hom-faithfulness holds automatically because Raw is thin; this
  says **nothing** about injectivity on objects or fullness and must not be
  advertised as preservation of presentation distinctions.
* Given raw t,u and an evaluated arrow tuple, if every tuple entry lifts to a
  raw tree of that exact output/profile and the interpretation is injective on
  operations at the fixed output c, then that tuple lifts to a unique raw
  arrow t→u. This proves a useful sufficient condition for fullness/refinement
  reflection, without assuming fullness or the wanted endpoint equality.
* In particular a strict calculus isomorphism induces a refinement-category
  isomorphism. State clearly when the injectivity/lifting hypotheses fail in
  the associative quotient certificate.

These criteria are basic comparison infrastructure. No categorical quotient,
equation-step completion, B3 criterion, or B4 recovery classification is claimed.

### B2-Q: nonthin associative quotient certificate (L/P with executable tests)

Use the actual A3 generated-congruence quotient of a typed binary signature,
not a manually equated pair or a semantics discarding all witnesses. Include
an unbounded family of typed associativity equations and retain a nontrivial
witness statistic (for example free unary decorations) independently proved to
survive the quotient. Full explicit definitions are part of the certificate.

For a repeated loop component x and binary μ : (x,x)→x, let
`L=μ[μ,id]` and `R=μ[id,μ]`. Prove literal `L≠R` but `[L]=[R]` in A3's
quotient. From `[μ]` to `[L]` exhibit two arrows with the distinct tuple data
`([μ],[id])` and `([id],[μ])`; their first-entry profiles have lengths 2 and 1,
so equality is impossible despite equal evaluated composites. Raw μ→L and
μ→R are distinct target pairs, each hom thin; when target is fixed at L, the
right-expansion semantic arrow has no raw lift. Prove this nonfullness claim,
not merely the object collapse.

The certificate suite must place this phenomenon inside genuine mixed-interface
contexts involving at least three distinct interfaces and repeated identical
components at separate positions, and include nested ≥4-leaf presentations.
It must distinguish retained unary witness choices in a nonempty equational
theory, so the example is not just the indiscrete/terminal target. Existing
A1–A3 mixed examples may supplement but not replace this contextual certificate.

## Required tests and evidence inventory

B1: different replacements at equal labels; independent events in both orders;
a dependent event whose attempted reversal is illegal; nullary removal; unary
event chains; attempted replacement of an existing internal vertex rejected;
three-layer occurrence association and moving frontier ranks.
B2: actual A3 associativity quotient with distinct evaluated-equal trees,
parallel unequal tuples, tuple composition through another nonidentity refinement,
identity/associativity tests, mixed context and four-leaf certificate, surviving
witness statistic, and witness-discarding semantics explicitly as negative control.

Deliver source, complete P proofs, discriminating executable examples, exact
Lean theorem index, dependency closure/axiom reports, baseline-preservation
hashes, reproducible build script/logs, negative/failed-attempt records, and a
concise results report. No `sorry`, `admit`, custom axioms, unchecked computation
oracle, or assumptions asserting the desired result. Standard classical choice,
if needed, is separately disclosed. No acceptance claim until independent review.

## Cheapest shortcuts explicitly excluded for non-author review

1. Defining Raw arrows as a proposition and obtaining laws for free: excluded by
   B1-R, which retains the forest and proves its unique recovery.
2. Defining Prefix as `∃σ, graft t σ=u`: excluded by independent address criterion.
3. Defining histories as linear extensions and declaring a correspondence:
   excluded by independently defined legal leaf-graft executions and proved maps.
4. Swapping two examples only, or erasing addresses: excluded by all finite
   histories, ancestor orders, arbitrary three-layer typed occurrence coherence.
5. Defining Sem arrows as reachability or quotienting tuples by total evaluation:
   excluded by B2-S tuple equality and the nonthin certificate.
6. Assuming forest category laws, fullness, faithfulness, or quotient coherence:
   excluded by arbitrary Calc inputs, explicit tuple law proofs, and hypotheses
   expressed solely in operation injectivity and exact entrywise liftability.
7. One-color associative sanity check as the sole model, or terminal witness
   collapse: excluded by contextual mixed-interface/witness-retaining certificate.
8. Treating this standard infrastructure as a novel integrated-result bundle:
   excluded by explicit provenance and the still-open A4/B3/B4/C5 gates.

## Reviewer decision

Pending independent pre-proof target-depth review. The author may inspect
baseline APIs/tool availability but must not begin proof implementation until
clearance. Reviewer changes must be recorded before freezing the approved target.
