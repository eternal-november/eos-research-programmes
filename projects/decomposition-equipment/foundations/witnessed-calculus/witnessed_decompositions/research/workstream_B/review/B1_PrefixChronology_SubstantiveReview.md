# B1 prefix/chronology P-slice: independent substantive review

**Verdict: PASS for the reviewed P slice, after one terminology correction.**
No unresolved central mathematical gap was found. This is not acceptance of
B1 as a whole, not a Lean/source audit, and not acceptance of B2.

Reviewer: `/root/review_refinement_target_depth`, separate from author
`/root/prove_refinement_obligations`. Reviewed 24 October 2026, 22:42–22:46 UTC.
This is agent-managed non-author review with shared-model limitations, not
external human certification. The reviewer wrote no author proof/source changes.

## Exact reviewed artifacts

Project root:
`/workspace/shared/witnessed_B_20261024/witnessed_decompositions`.

- Governing `research/CompletionContract.md`, SHA256
  `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
- Unchanged frozen `research/workstream_B/B1_B2_Targets.md`, SHA256
  `37912984dfcd045bb504e738823f8194e933975d5d94e043da50253cf94c8092`.
- Accepted-for-this-review `research/workstream_B/B1_PrefixChronology.md`, SHA256
  `bf1cf8ed1dca187706a15cb8b80f897f3b4465da7394e9211ab89a0f2a1067da`.
- The first inspected proof had SHA256
  `0511f7c3881805921703d76adc0f34bdc4c7759a125484a96a3a215bb3bb1c9c`.
  It is not silently substituted for the corrected final hash.

The accepted A1 tree/substitution, typed profile and occurrence infrastructure
is the dependency. Review reconstructs the arguments for all finite typed
trees, not only the supplied binary examples. No restriction to finite or
decidable generator/interface types, positive arities, or one interface is
introduced. All statements retain exact primitive labels and input orders.

## 1. Independent prefix and forest recovery

The definition of prefix is genuinely independent: inclusion of internal
child-word addresses with equality of their primitive labels. It does not
mention an existential forest, grafting, or the desired refinement relation.

The address lemma is sufficient and correct. Each edge address is either an
internal address or a leaf address; a nonroot address has an internal parent.
The output component plus all internal addresses and labels determines the
entire typed tree. At a nonleaf root, equal labels determine its arity, ordered
input components, and children to which induction applies. At an empty internal
address set, the sole tree is the identity leaf of the fixed output. This also
explains why equality of arity or component labels alone would not suffice.

For the nontrivial direction of the prefix theorem, I reconstructed the
simultaneous induction: a source leaf accepts exactly the whole target subtree;
a source node forces the identical target root generator, so childwise prefix
conditions are well typed and induction combines their recovered forests.
This proves existence of the subtree at every source leaf address and its
correct output, rather than assuming those data from address inclusion.

The zero-arity induction case is essential and is handled: the equal root
generator has no children, so the target is exactly that same nullary node and
the forest is empty. One cannot replace it by another closed tree. More
generally, a source with no leaves has only its empty forest and no strict raw
extension. No nullary witness is treated as an identity.

Fixed-source graft injectivity is proved independently by constructor
injectivity and childwise induction. It is not inferred merely from the
existence of a reconstruction formula. The resulting thinness is legitimate
because actual forest data were retained first. Both-way prefix inclusion gives
equal address sets and labels, hence literal tree equality. Antisymmetry does
not rely on leaf counts, which would fail for unary and nullary events.

## 2. Typed occurrences, stable addresses, and moving ordinals

The disjoint decomposition of new internal addresses and final leaves follows
from source-leaf prefix-freeness. A source internal address cannot extend a
source leaf. Therefore a final leaf has exactly one factorization `l a`, with
`l` a source leaf and `a` a leaf of its inserted tree. This supplies an actual
inverse to concatenation, including its full edge component. Equal component
labels at distinct source addresses do not create ambiguity.

The composed replacement is correctly `F_l[G_l]`, with `G_l(a)=G(la)`.
For successive levels the two occurrence maps agree by `(la)b=l(ab)`;
the inverses agree by unique prefix stripping. The planar traversal orders
these occurrences by consecutive source blocks, then by each inserted block.
Thus the conceptual comparison with A1's `slotExpand` is a comparison of actual
ordered occurrences, not merely equal frontier lengths. Its required Lean
implementation remains a separate gate.

The ordinal equation is correct: a leaf at local rank `j` in block `i` has
global rank `sum_{h<i} r_h+j`. It yields disjoint consecutive intervals and
exhausts the new frontier. Empty blocks contribute no occurrences; when all
blocks are empty the target frontier is empty. For a single arity-`n` event
at rank `k`, later old rank `r>k` becomes `r+n-1`, correctly interpreted in
the integers or with the stated nonnegativity condition. Unary events preserve
rank while adding a vertex; nullary events decrease subsequent ranks by one.

**Resolved precision defect:** the initial sentence "For n=0 the address k
disappears" conflated ordinal rank, frontier membership, and stable edge address.
I requested a correction before the final verdict. The author changed it to
say that the old leaf at ordinal `k` disappears from the frontier but its stable
address remains as the new internal vertex/edge address. The corrected hash
above contains this wording. No theorem hypothesis or conclusion was weakened.

## 3. Independent execution definition and finite event poset

Execution legality is defined before any final forest or partial order: the
address must be a current leaf, the generator output must match its component,
and the next tree is its corolla insertion. Thus histories are not defined to
be linear extensions. Execution records are addresses and generator labels;
legality/equality proofs are propositions, not extra chronological distinctions.

Every event adds exactly one internal address, which can never be removed or
relabelled. This rules out repeated event addresses and prevents cancellation
by nullaries. A descendant event requires its newly added ancestors first.
Incomparable addresses leave each other's leaf status and type unchanged, so
the local swap proof is sound. A numeric-index encoding must recompute ranks;
the proof expressly avoids treating stale indices as stable addresses.

The event set is finite because it consists of the finitely many added vertices,
tagged by distinct original leaf addresses. Its order is reflexive ancestry
within one tag, not equality of generator/component labels. Antisymmetry is
word-prefix antisymmetry. No decidability of arbitrary signature labels is
needed; event identities and their order are determined by finite ordinal words.

The down-set partial forest construction is genuinely useful, not a restatement
of the desired conclusion. At the first omitted planned vertex it truncates
the entire subtree to its typed identity leaf. A retained descendant cannot
have an omitted ancestor. The available-event lemma follows by traversing that
ancestor chain: either truncation blocks the address, or it reaches precisely
the current boundary leaf. Insertion then gives exactly the next down-set.

This proves every linear extension is legal and reaches the full forest. The
reverse direction uses monotonic retention of internal vertices and the
independently proved graft-address formula to show that a complete execution
contains exactly the prescribed events once, with their prescribed labels.
Ancestor precedence is then forced by legality. The intermediate-tree induction
shows the constructions are inverses, not just two surjections. This covers
the empty event poset, closed sources, repeated labels, unary chains, and
nullary terminal branches without exceptions.

## 4. All histories and macro-graft boundary

The linear-extension connectivity proof is complete: move the target first
element left past precisely those preceding elements, each incomparable by the
two extension orders, then induct on the remainder. Each adjacent swap changes
only that pair's order and preserves the extension property. No unproved
connectivity theorem is imported.

The three-way equivalence is noncircular:

1. Equal forests give equal final trees by grafting.
2. Equal final trees give equal forests by the separately proved injectivity.
3. For the common forest, execution/extension correspondence plus connectivity
   gives independent swaps.
4. Each legal independent swap preserves the intermediate tree, so every
   unchanged suffix remains legal and the endpoint is preserved.

Labels are retained throughout; isomorphic unlabeled event posets would not
imply equal histories or forests. Nor does a dependency edge disappear.

Arbitrary finite macro stages expand into atomic corollas by the proved
execution theorem. Concatenating expansions preserves endpoints and hence the
composite forest. Preorder provides a canonical ancestor-first expansion.
Identity stages contribute no events. The proof correctly does not claim that
macro histories with different numbers of steps are related merely by swapping
macro steps. This is the frozen atomic-history convention, not a retrospective
weakening of the chronology obligation.

## 5. Independent finite support and its limits

I reran the author's `B1_ChronologyChecks.py` (hash
`7e66ae71b436c5a1134fcaa04a7397c609aefeed9fc400625ad4b3795648a688`). It passed
and reproduced the recorded JSON (hash
`2730c53a4becd0ac890a84d0e517c3ccb76c96f67520751c6fc6e5449811cd8d`). Its stated
bounded domain is 157 loop-signature trees of at most three vertices, 24,649
ordered tree pairs, 1,237 forest/history cases, 4,309 histories, 4,122 rank
checks, and one mixed-interface six-event certificate. This rerun is not an
independent reimplementation of its entire bounded checker.

I additionally wrote a separate reviewer-owned frontier-list/internal-address
oracle, importing none of the author's tree/checker implementation:

- `/workspace/shared/witnessed_B_20261024/reviews/B1_IndependentChronologySpotcheck.py`,
  SHA256 `3db87a1e24370b60601bef360267d88b60df82bc76afad28f68ac6b4aede6183`.
- Its output `B1_IndependentChronologySpotcheck.json`, SHA256
  `e7678a375adeaafec1f4c5c7ea1ee45627d4d24ef6bf4371fc8f0625d06829d5`.

For the typed frontier `0→1, 1→1, 1→1, 1→2`, it checks all 720 orders of
six specified events, including repeated unary labels and a nullary branch.
Exactly 80 are legal, matching both the independently filtered ancestor order
and the direct count `6!/(3·3)`. All 80 are connected through 320 directed
adjacent-independent-swap checks and have the same typed five-leaf endpoint.
The oracle tracks changed ordinal positions, retains the nullary event's stable
internal address, and rejects a descendant-before-parent schedule.

These computations are C support only. The unrestricted verdict rests on the
proof reconstructions above, not on finite agreement or the supplied author
summary. No claim of new combinatorial novelty is warranted: these are standard
prefix/linear-extension mechanisms with the typed occurrence integration
required by B1.

## Final boundary

The corrected document meets the frozen B1-P prefix and all-chronology depth.
The reviewer found no unresolved correctness or scope defect in that P slice.
The mandatory Lean category/forest/occurrence declarations, their actual
dependency closures and builds, and the complete B1/B2 nonvacuity inventory
remain subject to their own independent review. References in the proof to
Lean evidence are not certified by this P-only verdict.
