# C3 author finite certificate: domain, maps and reproducibility

Contract v0.1 SHA256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
Cleared target `../C3_Targets.md` SHA256
`88ea710752d99cd83d10c85740f825b1c543d58c0f475615c667020bc1aa2825`.
Parent released the C3-only M-positive attempt after non-author §3.4 review.
Dependencies: accepted B2, locally verified C1/C2; C1's C5/F2 and C2's D2/E
acceptance gates remain OPEN. No A4/C5/B3/B4/D/E/F/G/I work is activated.

This is **C/X evidence**, not an all-size P proof, Lean theorem, acceptance
verdict or new mathematical novelty. The finite graph/partition and relation
suite uses only Python's standard library, with no randomness, network, cache,
external computation oracle, inherited evaluator import or nonstandard package.
The same author supplied the two redundant algorithms; a separate non-author
implementation is required for independent verification.

## Reproduce

From the project root, with Python 3.10 or later:

```
python3 research/workstream_C3/finite/check_c3.py \
  --output /tmp/C3-AuthorCertificate-rerun.json
```

The JSON is deterministic, omits machine-specific paths/timestamps, records
exact contract/target/source hashes, and is intended to compare byte-for-byte
with `AuthorCertificate.json` when the same source is used. `AuthorRun.log`
records the producer command's successful summary. An assertion failure or
other exception gives a nonzero exit status and no successful certificate.
The source path is resolved relative to this script; an arbitrary current
working directory is permitted. Inputs must retain the project-relative
contract and target paths.

## Representation and independent authored formulas

`Graph(n,edges)` retains every ordered vertex and undirected edge `(x,y)` with
`0 <= x < y < n`. Graph equality is literal, never graph isomorphism. A partition
is the full ordered tuple of increasing ambient blocks. `Graph.restrict`
uses rank dictionaries; `matrix_leaves` independently scans an adjacency
matrix. The main `reconstruct` lifts internal edge sets and unions cross edges;
`matrix_reconstruct` instead decides each ambient pair by its block/local
coordinates. They do not call one another. Redundancy can catch implementation
mistakes but is not labeled non-author independence.

`Cut` stores a whole `Comp(graph,src,dst)`, actual ambient ordered blocks and
the entire interface-object path. In the selected thin chain category the
object path determines every actual arrow and its composite. `profile()` keeps
the canonically induced graph and arrow for each separate occurrence. Equality
of components never merges occurrences. Cuts with a fixed whole may differ in
blocks or profiles; cuts with equal profiles may differ in retained wholes.

`Tree` distinguishes an external identity leaf (`primitive=None`) from every
primitive node, including a zero-child nullary. A primitive stores its full
binary/nullary C1 cut; labels are not inferred from shape. `evaluate` performs
recursive cut substitution. `direct_evaluate` separately follows address-wise
ambient embeddings and collects actual external leaves; it calls neither
`evaluate` nor `subst`. The full-witness outcomes, not just leaf graphs, must
agree. `decode` structurally reconstructs a tree from root, tagged shape and
address-to-primitive map, including the identity/nullary boundary.

## Exhaustive small graph domain

For each `m=0,1,2,3,4`, enumerate **every** simple graph on `[m]`: respectively
1, 1, 2, 8 and 64 graphs, 76 total. For each `k=0,1,2,3,4,5`, enumerate **every**
function `[m] -> [k]`, converting its level sets to an ordered k-tuple of blocks.
An absent label is a retained empty block, not a deleted slot. The unique empty
function exists when `m=0`, including `k=0`; no nonempty set maps to `[0]`.

Every nonempty-block ordered partition of every graph through four vertices
is therefore present, as are every empty-slot pattern at the declared arities.
Arbitrarily high arities with empty slots are infinite and **not** claimed
finitely exhaustive. The all-finite-size/all-arity result belongs to the P
proof. In particular, no empty-graph arrow slot is deleted: it can carry a
nonidentity grade, so graph-only empty-slot deletion would not preserve the
full typed path.

For each `(m,k,B)`, graphs are grouped by their complete ordered induced graph
tuple `H`. Every anchored fibre is compared as an actual SET of graphs against
all subsets of the cross-pair set `X_B`, reconstructed by the second formula.
Both roundtrips and the exact `2^|X_B|` cardinality are checked. Every possible
internal graph tuple occurs: the checker verifies the fibre count is
`2^(sum_i binomial(|B_i|,2))`, not merely that encountered groups look correct.
The zero-cross-pair/injectivity boundary is checked against at most one
nonempty block.

Separately, all `(G,B)` are grouped by `H` for fixed `(m,k)`. Every entire
unanchored leaf-only witness fibre is compared with the disjoint union over
all compatible ambient block placements and all their cross-edge subsets.
The cardinality is checked as

```
(m! / product_i |H_i|!) * 2^(sum_(i<j) |H_i|*|H_j|).
```

These are counts of total cut witnesses, **not** counts of distinct wholes
once B is forgotten. Since the sizes in H sum to m, no missing graph size can
supply a further member of that H fibre.

Actual counts:

| m | Graphs | Partitions k=0..5 | Graph/partition pairs | Represented typed pairs |
|---:|---:|---:|---:|---:|
| 0 | 1 | 6 | 6 | 83 |
| 1 | 1 | 15 | 15 | 295 |
| 2 | 2 | 55 | 110 | 2,434 |
| 3 | 8 | 225 | 1,800 | 42,680 |
| 4 | 64 | 979 | 62,656 | 1,552,448 |
| Total | 76 | 1,280 | 64,587 | 1,597,940 |

There are 4,485 anchored fibres and 1,742 unanchored fibres. The graph roundtrip,
cross-data roundtrip, and unanchored member enumeration each inspect 64,587
members. Histograms and a deterministic ordered-case digest are saved.

### Exact typed product accounting

Independently enumerate every weakly increasing object string in `{0,1,2}` of
length `k+1`; these are exactly all composable k-arrow strings of `[2]`. There
are `binomial(k+3,2)` such strings, respectively 3, 6, 10, 15, 21, 28; all 83
are physically checked for internal composability and endpoint composite,
including the three empty paths whose composites are their identity arrows.

The finite typed domain for each k is the Cartesian product of graph/partition
cases and these strings. For every pair, its induced component path is valid:
graph restriction checks only G and B, while composability/composite checks
only the string. Reconstruction changes edges/blocks but leaves the ENTIRE
string fixed. The anchored/unanchored bijections and cardinalities thus act
identically at every string; their proofs and checks never inspect arrow data.
Conversely every C1 cut in this finite chain-domain determines exactly one
such graph/partition pair and one such full string. This proves the factorized
coverage of the whole stated Cartesian product without silently shrinking it.

Accordingly **64,587 graph/partition pairs and 83 arrow strings were physically
checked**; **1,597,940 typed pairs are represented by their proved products**.
They are not described as 1,597,940 separately executed iterations or assertions.

## Full six-vertex family, syntax, and occurrence certificate

The baseline graph has edges `{01,12,13,24,34,45}` and blocks
`({0},{1,3},{2,4},{5})`, with interface path `(0,1,1,1,2)`. Internal edges are
precisely 13 and 24. Both middle components are literally the same nonempty
ordered K2 graph graded by `id_1`. The thirteen cross-pair bits vary freely:
**all 8,192** resulting graphs are reconstructed and checked, not only a toggle.

For every member, both binary trees `((B0 B1)(B2 B3))` and
`(B0(B1(B2 B3)))` are built with actual canonically restricted internal wholes
and binary primitive cuts. Recursive substitution and direct address evaluation
both produce the complete same cut `(G,B,path)`; their raw trees and shapes
remain unequal. This gives 16,384 recursive evaluations, 16,384 independent-
formula address evaluations and 16,384 full tree-encoding roundtrips. These are
redundant authored formulas, not an independently authored reviewer count.

On the named baseline member, the first middle occurrence receives the forward
singleton cut `({0},{1})`; the second receives the reverse cut `({1},{0})`.
These are distinct parallel witnesses on exactly the same K2/id_1 component.
The resulting ambient block order is
`({0},{1},{3},{4},{2},{5})`, with path `(0,1,1,1,1,1,2)`. Entrywise B2 tuple
interpretation thus retains two separate replacement data, not a lookup by
component value. Adding edge 05 changes the whole but none of the four leaves.
No categorical nonfaithfulness is inferred from object-evaluation collapse.

## Relation observations and the actual C2 semantic fixture

Enumerate every relation on `[a] x [b]` for `a=0..2`, `b=0..3`: **104** matrices.
The full Boolean `Truth` map is inverted and its distinctness checked. Group by
`Obs(R)=(dom R,ran R)` and examine all **105** candidate support pairs. The
members are independently enumerated as subsets of the candidate rectangle
with no missing row or column. Exactly **56** support fibres are nonempty;
49 are empty, 51 singleton, four have size 7 and one has size 25. Empty carriers,
empty supports and one-element support boundaries are explicitly included.

The unequal-cardinality collision is

```
R = {(0,0),(0,1),(1,2)}
R'= {(0,0),(1,1),(1,2)}
```

on `[2] x [3]`. Both endpoint supports are full, but their truth matrices differ.
This is the specified LOCAL observation of C2 component relations, not a
calculus morphism, empirical identifiability claim or arbitrary-probe theorem.

For the separate primitive-evaluation fixture use distinct interfaces
`A=[2], B=[3], C=[2]` with labels A,B,C retained even where carriers have the
same size. Use R above and `S={(0,0),(1,0),(2,1)}` from B to C. Their nonempty
composite is `T={(0,0),(1,1)}` strictly contained in the supplied whole
`W=[2] x [2]`. Two distinct binary primitive symbols alpha/beta have exactly
this input profile and output whole, and the recursive C2 containment-cell
evaluator sends their distinct raw corollas to the same `(W,(R,S))` cell.
The exact cell with whole T has the same profile but is a DIFFERENT total
semantic cell. Thin fixed-(profile,whole) fibres do not identify whole relations,
primitive symbols or existential realizing tuples.

## Executed wrong-map controls

Each control computes the actual erased/mutated map and checks a valid pair or
failed roundtrip, not just a hard-coded expected-failure label:

1. Drop cross edge 05 before reconstruction: the recovered graph is the other
   valid whole, not the supplied plus-edge input.
2. Drop B from `(profile,B,cross edges)`: opposite singleton K2 cuts collide.
3. Sort the ordered blocks as an unordered collection: those cuts collide.
4. Use a dictionary keyed by equal component values: the repeated middle
   replacement overwrites its other occurrence, changing the final ambient cut.
5. Drop primitive labels from full tree encoding: opposite-cut corollas collide.
6. Claim equal evaluation implies equal trees: the two six-vertex groupings
   provide equal full cuts and unequal source trees.
7. Replace Truth by endpoint-support Obs: the distinct 2-by-3 relations collide.
8. Drop the root from encoding identity trees: empty/one-vertex identity leaves
   have equal shape and empty primitive maps but different roots.

An additional boundary guard distinguishes a nullary primitive on the empty
identity whole from its unary semantic identity/external raw identity leaf:
zero blocks versus one empty block, and different tagged shapes. Full encoding
roundtrips hold for both. Positive injectivity here is supported by these finite
roundtrips and by the separate P theorem, not deduced from the negative controls.

## Reporting and assurance boundary

No baseline file is changed by this suite. No new Lean claim or axiom audit is
presented: inherited foundational Lean results remain separate evidence. The
full-size missing-edge theorem, all-finite-tree encoding proof and local
support-fibre theorem require the author's P text and non-author review. The
mathematics is credited as standard set-level coordinate/relational structure,
not a newly discovered major result. Parent acceptance and separate independent
P/C checks remain necessary; this author certificate cannot self-accept C3 or
close C1/C2's later-use gates.
