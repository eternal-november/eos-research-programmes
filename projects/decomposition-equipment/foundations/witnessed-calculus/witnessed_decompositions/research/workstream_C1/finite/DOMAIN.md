# C1 finite certificates: frozen domain and trust boundary

Contract v0.1, unchanged, SHA-256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
Target: `../C1_Targets.md`, SHA-256
`7a5d4bb8dd3aa0715c82b73b8c169def2935b98f41addfd0eaaf03a606be244e`.
This is **C evidence**, not a kernel proof or a replacement for the uniform
P theorem and typed L fragment. C1's C5/F2 downstream acceptance remains OPEN.
The graph family is standard restriction/ordered-partition infrastructure;
this package makes no novelty claim. The permitted branch is M, positive only.
Dependencies are accepted A1–A3, with B1–B2 used only for the parent Gate 1
assessment. No other C/B/F obligation is activated by these computations.

## Reproduce

From the repository root:

```
python3 research/workstream_C1/finite/check_c1.py \
  --output research/workstream_C1/finite/results-rerun.json
```

Python standard library only. No randomness, network, hidden cache, custom
native oracle, third-party package, or Lean trust claim. On the author machine
this takes approximately 15 seconds; exact runtime and Python version are in
the JSON. The output hashes both the immutable target/contract and the source.
Run logs are retained; `author_run_01.log` predates the clarified concrete
mutation predicates and `author_run_final.log` corresponds to the final source.
No mathematical counterexample or failed run was encountered. Earlier logs
are historical evidence, not interchangeable final-source verification.

## Carriers and independent representations

`Graph` stores vertex count and the complete set of undirected pairs `a<b`.
`Arrow` stores source, target, and an actual C₂ bit (zero in the principal
three-object-chain suite). `Component` pairs the graph and arrow. `Cut` stores
its complete whole component, ordered actual blocks, and full arrow string.
`Cut.leaves` erases block embeddings and returns canonical induced graph/arrow
pairs only. Thus the cross-edge test compares the right two maps: leaf data can
agree while whole and total witness data differ. No whole is reconstructed.

The primary algorithm uses sorted blocks, edge sets, and rank dictionaries.
`LabelCut` instead stores each ambient vertex's block label and a full adjacency
matrix. Its substitution counts earlier vertices with the same label to obtain
local rank, then adds an arity offset; it never calls the block substitution or
restriction implementation. Matrix leaf restriction scans selected rows and
columns independently. These two authored algorithms are redundant checking,
NOT a claim of non-author independence; a separate reviewer must supply that.

## Exhaustive small single-refinement suite

- Graph sizes: exactly `m=0,1,2,3`, every simple ordered graph, i.e. respectively
  `1,1,2,8` graphs (12 total).
- Outer arities: exactly `n=0,1,2,3`. Every map `[m]→[n]` is an ordered partition;
  absent labels remain empty blocks. In particular `n=0` has one partition
  when `m=0` and none otherwise.
- Interfaces: every weakly increasing chain in `{0,1,2}` of length `n+1`.
  These are every composable arrow string of the three-object chain category.
  There are `binomial(n+3,2)` such strings. The whole grade is its composite.
- For every such cut: validate full data, independently compare all induced
  matrix leaves, and test both units at FULL witness equality.
- For each original occurrence independently: every local arity `k=0,1,2`,
  every map from that occurrence's vertex set to `[k]`, and every interface
  string between its frozen endpoints. Other occurrences receive identities.
  Compare complete block and label substitutions, whole retention, and the
  exact concatenation of the supplied replacement profiles.
- Separately, for every graph and every subset `B⊆[m]`, test every subset
  `C⊆[|B|]`; increasing-enumeration composition and the full canonically
  relabelled induced graph satisfy restriction transitivity.

Exact counts: 4,395 cuts; 4,395 checks of each unit; 57,156 single-occurrence
refinements and redundant substitutions; 238 nested restrictions. Counts are
computed from actual execution, not estimated as a product of unrelated sizes.

## Exhaustive depth-three associativity suite and factorization proof

A shape is an outer arity `n∈{0,1,2}`, a vector of middle arities
`k_i∈{0,1,2}`, and a vector of innermost arities `ell_ij∈{0,1,2}`. Zero-ary nodes
are retained, not deleted from the shape. There are

```
1 + (1+3+9) + (1+3+9)^2 = 183
```

shapes. Their final leaf counts range from 0 to 8. For each shape with L final
leaves, each graph on `m≤3`, and every map `[m]→[L]`, the code obtains the
innermost ambient blocks from that map; each internal block is the union of
its descendant leaf blocks. Pulling these unions back through increasing
local enumerations constructs the three composable cut stages. It compares
both parenthesizations of substitution, their complete final flat witness,
and both independent label-algorithm parenthesizations. All retained wholes,
ordered empty slots, and final slot positions participate in the equality.

This covers **every nested three-stage vertex-label assignment** on these
shapes, not just every terminal assignment chosen independently: substitution
sends each vertex to exactly one descendant final slot, giving the inverse
map; an internal block must be the disjoint union of those descendants by
exhaustivity. Conversely every terminal labeling yields these uniquely forced
internal blocks. If L=0, there is one labeling only for m=0, as required.

Arrow checking is factored without shrinking the domain. For every shape and
every weakly increasing final chain `a_0≤...≤a_L`, the endpoints of every
internal arrow are forced by the boundaries of its contiguous descendant
interval. A zero-leaf interval has the same endpoint on both sides, hence the
identity grade; this treats nullary units correctly. The program independently
checks composition at every node and through all three levels. In a thin
chain category there are no further arrow choices. Conversely any well-typed
three-stage cut string determines exactly this final chain, and its internal
arrows necessarily have those endpoints. Thus graph assignments and interface
chains form a product for each shape. Graph restriction/substitution code
never examines arrow values, while arrow composition code never examines
graphs or labels. Full witness equality is equality of those two fields plus
the unchanged whole. The factored checks therefore cover their entire product.
This argument applies to this finite test domain; it is NOT used to omit
actual arrow values from the general finite-category theorem.

Exact execution counts: 91,848 graph/shape/label assignments; 3,123
shape/interface-chain assignments; 2,745,411 product cases represented. The
JSON distinguishes physically executed checks from this justified product
coverage, rather than claiming 2,745,411 independent runs.

## Mandatory six-vertex and boundary certificates

The target's frozen graph, noncontiguous blocks, `0→1→1→1→2` path, proper
forward/reverse binary middle refinements, and final block order are checked
literally. Both middle colours are the same nonempty two-vertex one-edge graph
with `id_1`; their local cuts are distinct despite equal induced leaf colours.
Actual recursively constructed binary tree nodes retain their own cut whole
and canonical inclusions. Their two distinct shapes evaluate through recursive
substitution to the SAME full flat cut, not merely the same leaves.

Adding `(0,5)` changes the whole but not the four induced leaf components.
There is no exhaustive claim about all six-vertex graphs or missing-edge
fibres: this is C1's required certificate, not C3 discharge.

Nullaries are checked on the empty identity-grade whole. The empty identity
component's identity operation retains one empty block and is distinct from
the zero-block nullary. Unequal-endpoint and nonempty nullaries are rejected.
For a nonidentity-loop test, the supplementary finite category is `[2]×C₂`:
composition adds bits modulo 2. An empty whole graded `(1,1,1)` rejects a
nullary even though its endpoints equal those of the valid `(1,1,0)` case.
Overlapping/missing-vertex partitions, noncomposable arrow strings, and wrong
composite grades are also rejected.

## Mutation-sensitive negative controls

Each control executes the erroneous map or predicate and demonstrates its
failure on a known certificate:

1. **Erase whole:** mapping a witness to only `(blocks, arrows)` collapses the
   two distinct cross-edge wholes.
2. **Collapse occurrences by component:** an actual dictionary keyed by leaf
   component overwrites one repeated middle occurrence's chosen cut; its
   substitution gives a different ordered final partition.
3. **Ignore canonical lift:** concatenating local-coordinate blocks without
   applying their parent embeddings gives a wrong, non-ambient partition.
4. **Forget arrow values:** a nullary predicate retaining only equal endpoints
   accepts the forbidden nonzero C₂ loop grade.
5. **Forget composability:** a predicate checking only the first/last endpoints
   accepts the supplied noncomposable internal arrow string.
6. **Empty leaf is nullary:** deleting empty blocks turns the one-slot identity
   operation into the forbidden zero-slot identification.

All controls must be killed, and all invalid data rejected, for the script to
report PASS. These controls delimit what the implementation tests; they do not
replace independent scope review or an all-parameter proof.
