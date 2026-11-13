# C1 Lean adapter: exact semantic comparison and assurance boundary

Contract v0.1, SHA-256 `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
Frozen target SHA-256 `7a5d4bb8dd3aa0715c82b73b8c169def2935b98f41addfd0eaaf03a606be244e`.
This is the P comparison of the new L fragment to `proof/C1_Model_Theorem.md`.
It does not implement or claim a fully Lean semantic `Calc`, C5, F2, or any
obligation beyond the authorized local C1 milestone.

## 1. Graph values, not ambient-location colours

`OrderedGraph n` is an actual Boolean symmetric irreflexive adjacency relation
on `Fin n`, for arbitrary n. `restrict_trans` is a generic literal equality of
the complete restricted graphs along composed increasing embeddings. It does
not assert the separate theorem identifying a composed inclusion with the
canonical enumeration of an image subset: that identification is R1 of the
P model theorem.

The bounded adapter uses `GraphCoordinates.Graph` on the ambient `Fin 6`.
`GraphColour` is the subtype of pairs `(r, matrix)` which admit a representation
`graphCode G s`. Its data field is ONLY `(r, matrix)`; the existential proof is
proof-irrelevant and stores no ambient vertex location. `graphCode` is the
complete row-major adjacency matrix in `enumerate s` order. The accepted
`GraphCoordinates.enumerate_eq_sort` identifies that executable enumeration
with the unique increasing enumeration. Matrix entry `i*r+j` recovers the
adjacency of canonical vertices i,j, so this code is faithful for ordered
graphs. No claim of graph-isomorphism quotienting is made.

Every ordered simple graph H on `[r]`, r≤6, has such a representation: choose
s={0,...,r−1} inside `Fin 6`; set G(i,j)=H(i,j) when both indices are <r and
false otherwise. G is symmetric and irreflexive, and increasing enumeration
of s sends i to i. Hence `graphCode G s` is exactly H's size and adjacency
matrix. Conversely every representation is an ordered simple graph of size
|s|≤6. This establishes both directions of the component-class comparison.
It is a P argument, not an extra claimed Lean theorem about `GraphColour`.

`Interface` is a distinct wrapper around `Fin 3`, avoiding a hidden replacement
of another quiver instance. `GraphArrow a b` is `(GraphColour, a≤b)`, the graph
paired with the unique chain-category arrow a→b. Proof irrelevance here is
appropriate: this category is thin. The generic P theorem retains actual
arrows for arbitrary, possibly nonthin, finite categories; the adapter's
endpoint-only grade representation must NOT be exported to those categories.

## 2. Canonical local coordinates and the signature

For s and b, `localBlock s b` filters `enumerate s` zipped with its zero-based
indices, then keeps the indices of entries lying in b. If b⊆s, membership of
index j is precisely `ε_s(j)∈b`. The zipped list has one entry at every j<|s|,
in increasing order, because `enumerate s` is increasing and has no repeated
vertices. Consequently `localBlock s b` is the increasing list of the rank
subset ε_s⁻¹(b), the same subset represented by the accepted
`GraphCoordinates.rankBlock`. Conversely applying ε_s to these indices
recovers b, exactly as `recover_rankBlock` proves for that finite-set form.
This argument establishes the executable-list/finite-set comparison without
assuming that block order follows vertex order.

A `BinaryCut` stores the three interfaces, whole graph code, two input graph
codes, and the two canonical local block lists. Its `valid` proposition states
that these fields are represented by one actual graph G on support s and an
ordered disjoint exhaustive bipartition (u,v) of s, with input graph codes
G|u,G|v and local blocks ε_s⁻¹(u),ε_s⁻¹(v). The witness's DATA do not include
that ambient representation: `binaryCut` supplies it only as a proof.
Therefore two ambient realizations with the same actual whole/input/partition
and interface data give the same generator, not extra ghost distinctions.
Input graph fields are redundant checked data, uniquely determined by the
whole and local blocks, not arbitrary graph decorations.

Conversely any binary cut in the N=6 chain model has a `BinaryCut`: represent
its whole on an initial segment, lift its canonical blocks to that support,
and use the preceding coordinate lemma. The `cutSignature` primitive is
exactly this binary cut, with a two-edge `Quiver.Path` of the actual input
graph colours and output colour the retained whole. Its other generators are
one designated nullary at each interface, with empty graph and identity
arrow. No identity leaf is a primitive, and no unequal-endpoint or arbitrary
nonidentity-loop nullary is introduced. The supplementary nonthin-category
nullary-grade negative test belongs to C/P, not this chain-only L fragment.

## 3. Full evaluation and why its fallback is unreachable

`treeBlocks` recursively computes blocks in the canonical coordinates of the
current output graph. For a leaf it returns the one block `[0,...,r−1]`. For a
binary node with local parent blocks U,V, it evaluates each child in that
child's own canonical coordinates, maps every child block through the
increasing list U or V, and concatenates results left then right. Nullaries
return no blocks. `liftBlock parent child` uses `parent[i]?.getD 0` only to make
a total executable function on raw lists; the fallback is NEVER reached on
any `CutTree` admitted by this signature, not merely in the six-vertex tests.

Here is the full induction proving that assertion and the semantic comparison.
For every `t : CutTree c`, claim that (i) `treeBlocks t` is a disjoint exhaustive
ordered partition of `[r]`, where r is c's graph size, and EACH returned block
list is strictly increasing (block order itself is unrestricted); (ii) all entries are <r;
(iii) the actual A frontier has one component for each block, whose graph is
the canonical induced subgraph and whose arrow is the corresponding chain
arrow; (iv) output arrow is the composite of that entire path.

* Leaf: its one range block is strictly increasing, has all four properties and equals the model
  identity cut, including when r=0. It is one occurrence, not zero.
* Nullary: output graph is empty and arrow identity by the signature. Empty
  partition/path have all properties and are the model's designated nullary.
* Binary node: unpack its `valid` proof. U,V are disjoint, exhaustive and
  increasing local subsets, and their lengths are the vertex counts of the
  two actual input graph colours. By induction all child block entries are
  strictly below those counts. Thus every list lookup in U or V is in range,
  establishing the fallback claim BEFORE interpreting it as a vertex map.
  Its value is the corresponding increasing inclusion. Images of a child's
  disjoint exhaustive partition partition U or V; the two images are disjoint
  and cover `[r]`. Each child block list is strictly increasing by induction,
  and lookup along an increasing parent block list is a strictly increasing
  map on its valid indices. Thus every image block list is strictly increasing
  too: the output is the canonical increasing list of that set, not merely
  an arbitrary representative with equal set of entries. Their canonical induced graphs agree with the frontier
  colours by R1/R2 of the P model theorem. `Tree.frontier` expands the exact
  input path, so concatenation retains every intermediate interface and grade.
  Category associativity supplies the composite arrow. These are exactly the
  graph-model substitution blocks and profile.

This proves, by structural induction on ALL trees of the signature (not a
size-limited enumeration), that `graphEvaluate` agrees with A2's semantic
interpretation under the binary/nullary cut assignment into the P-defined
actual graph `Calc`. The output is the full retained graph, ordered actual
canonical blocks and complete profile. `FullCut` itself is an unrestricted
record used as an executable carrier; it is not advertised as the Lean
semantic operation subtype. The induction just proved its `graphEvaluate`
image lies in that subtype. This image-validity and all-tree comparison are P,
not a claimed kernel theorem absent from the source.

`FullCut` does not repeat an output-arrow field: its type retains output
endpoints, and the chain has a UNIQUE arrow between those endpoints. Together
with those indices and `whole` it retains the full output component. This is
lossless for this adapter only, not for a nonthin category.

## 4. Public A1/A3 and occurrence links actually checked

`leftGrouped`, `rightGrouped`, `firstReplacement`, `secondReplacement`, and
`refined` are genuinely values of public `WitnessedDecompositions.Tree` over
`cutSignature`. Their leaves carry standardized graph colours, NOT root
support names. In particular `c1=c2` is proved with both supports nonempty.
`differentForest` has the exact dependent `Tree.Substitution rightGrouped`
type; `refined` is the actual public `Tree.graft`. The independently selected
middle replacements have identical whole/profile but local partitions
`[[0],[1]]` and `[[1],[0]]`. The checked full refined blocks are
`[[0],[1],[3],[4],[2],[5]]`. `colour_keyed_mutation_rejected` shows concretely
why reusing a single replacement for the repeated colour produces a different
cut. `coordinate_erasure_mutation_rejected` rejects forgetting local inclusions.

The generic `graph_graft_identity` and `graph_graft_assoc` use accepted A tree
equalities and apply `graphEvaluate`. They are L facts about evaluation of
raw grafts, not a disguised proof that arbitrary semantic full cuts form a
lawful `Calc`. That latter fact is proved independently in P.

`Declared.rotation` is ONE explicitly parallel three-leaf local rotation in
the actual `Presentation.Equations` type. It is not defined by semantic
agreement. `declared_full_cut_sound` checks its full cut equality.
`competing_groupings_derivable` uses the actual `Derives.substitute` constructor
with a shared occurrence-indexed forest to expand its third leaf into the
remaining binary subtree. The two resulting raw trees are the frozen
four-leaf groupings. `competing_groupings_equal_in_A3_quotient` then invokes
the real A3 `Presentation.quotient_eq_iff`. This checks the actual quotient
connection, while `competing_groupings_distinct_trees` proves syntax has not
already identified them. No completeness or quotient-by-all-semantics theorem
is claimed for this one-equation fragment.

## 5. Trust, failures, and remaining boundary

Theorems use ordinary Lean kernel proofs, reducible `decide`, and `omega`, not
native computation as an unchecked oracle. The complete listed declaration
closure reports only `propext`, `Classical.choice`, and `Quot.sound`; the graph
and canonical-coordinate infrastructure imports these standard logical
principles, and the actual A3 quotient uses the accepted quotient machinery.
There are no admissions or custom axioms. This is NOT an axiom-free claim.

`attempt01`–`attempt07` preserve ordinary elaboration failures and repairs:
structure-field syntax, explicit signature parameters, dependent occurrence
case splits, and an incomplete list-membership simplification. No target was
weakened; the kernel accepted `attempt08`, including all mutation controls and
the real A3 derivation. No discovered mathematical counterexample is concealed.

The all-size/nonthin model laws, all-tree validity/comparison above, canonical
image-enumeration uniqueness, finite-category cardinality argument and bounded
closure are P. The concrete graph data, generic restriction pullback law,
public typed A1/A3 constructions, full-cut equalities/inequalities and actual
occurrence graft certificates are L. The independently authored finite-domain
suite is C, not an unrestricted proof. Full C1's future C5/F2 use stays OPEN.
