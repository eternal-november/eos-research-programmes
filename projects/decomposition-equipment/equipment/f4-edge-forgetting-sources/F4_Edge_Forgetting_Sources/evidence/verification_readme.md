# Exact finite F4 verifier

Run `python verify_f4.py` from any working directory. Requires Python 3 and its standard library; do not use `python -O` (assertions are the checks). Results and exact loop counts are written to `results.json`; `run.log` captures the invocation output. This is executable finite evidence, not a Lean certificate, compiler proof, hardware benchmark, or all-degree proof.

## Domain and factorization

An ordered graph has vertex set `[v]`, `0≤v≤4`, and any subset of its unordered distinct pairs. A degree-n partition is a function `[v]→{1,…,n}`: all assignments, including noncontiguous blocks and any empty blocks, are enumerated. At degree zero only the empty graph admits a partition. Every monotone `[m]→[n]` for `0≤m,n≤4` is enumerated, including constants and repeats. Active means endpoints are preserved; in particular all `[m]→[0]` are active and `[0]→[n]` is active only when n=0.

The category is `C2×[1]`, with two objects and six actual arrows `(source,target,bit)`, source≤target. Composition adds bits mod 2; identities have bit 0. All object sequences and all bit strings of each degree≤4 are enumerated. This is nonthin. Keeping endpoints alone would lose the bit and is not the designated target.

**The complete graph×path product is not enumerated.** The simplicial action is coordinatewise, the target forgets only graph edges, and its complete path coordinate is unchanged by edge-forgetting. Thus equality, naturality, and the active pullback inverse factor into the graph and path checks. Geometry composition is checked for every composable monotone-map pair in degrees≤4 on each possible vertex block label. The transformation preserves the increasing order of selected original vertices. Therefore equality of these lineage/label transformations gives identical selected vertices, reindexing, and induced edges for every graph. Independently, every action on every full graph/partition record in the bounded domain is compared with a second implementation using literal block subsets and pairwise induced-edge lookup. This is documented factorized coverage, not a claim to have executed every full-record compositional pair.

## Independent active-fiber check

For each active map and each fine partition, all source edge sets are enumerated and grouped by their computed coarse record. Separately, the coarse partition is computed by the set-based reference implementation. Every possible coarse whole edge set is then tested: its bucket must consist of exactly the proposed inverse (fine partition, coarse whole edges). This verifies both existence and uniqueness against independently enumerated candidates, including empty graph/degree-zero cases. Paths are tested separately with actual arrow bits retained.

## Negative simplicial control

The code enumerates normalized triangle labels over F2 satisfying the four-vertex cocycle equation, i.e. degrees≤4 of the all-degree object `K(F2,2)`. Pullback along every monotone map gives zero on repeated triples and otherwise reads the pulled-back triangle. Closure and all compositional map pairs in those degrees are tested. Its degrees zero and one are singletons and degree two has two elements. Consequently `X×K(F2,2)→X` has two lifts over a fixed two-cut and its whole; this is a genuine simplicial duplicated-witness control, not ad hoc duplication of X2. All-degree validity follows from the cocycle pullback argument in the accompanying mathematical proof, not from this bounded enumeration. No 2-Segal claim is made for this negative control.

## Scope

The four-vertex/four-degree bounds and frozen six-vertex fixture are F2 dependency regressions, not a fabricated numerical F4 acceptance floor. This verifier does not claim to discharge all F2 obligations (e.g. every triangulation), C3, F3, or I3. The F4 theorem must be read together with its all-degree proof and the original designated discrete M=1 model; no replacement by the larger span groupoid is made.

## Fixtures and mutation controls

The first six-vertex fixture uses partition labels `(1,3,1,4,3,4)`, so its second block is empty and the first and third blocks are noncontiguous; it uses actual nonidentity category-arrow bits. The second is the **exact frozen C1 §8 fixture**: edges `{01,12,13,24,34,45}`, blocks `({0},{1,3},{2,4},{5})`, interface path `(0,1,1,1,2)` in the original three-object chain. The two middle component graphs are checked equal, and all bounded compositional map pairs are checked on the graph and path. This is an additional regression, not an assertion of the whole frozen certificate's original formal acceptance.

The wrong-edge restoration mutant substitutes the edgeless graph for a fixed edged coarse whole; the coarse projection then disagrees. The endpoint-only path mutant forgets actual bit labels: over object sequence `(0,0,1)` and fixed long arrow bit 0, the fine paths with bits `(0,0)` and `(1,1)` both lift. The designated edge-only target keeps those paths distinct and thus avoids this mutant ambiguity.

The frozen C1 whole is additionally compared with the whole obtained by adding edge `05`. Their four induced component graphs are identical, their complete whole edge sets differ, and edge-forgetting gives the same vertex/partition/path data. For each of these two fixed wholes, the prescribed fine partition's fiber is independently searched among **all 32,768** edge sets on six vertices and is a singleton. These are specifically two six-vertex fixture fibers, not six-vertex exhaustive partition coverage.

The cocycle control has 8 degree-three labels while the two-triangle comparison target has 4; it is explicitly **not** 2-Segal. A supplementary finite check records the two factorizations `0=0+0=1+1` in C2, for the optional second control `X×N(C2)→X`; the script does not claim a separate full all-degree 2-Segal verification of that product. The category-nerve argument belongs to the proof.

`results.json` is deterministic (including the verifier's SHA-256); measured elapsed time is printed only in `run.log`, never inserted in the deterministic results. Exact counts below are defined by their loop names; separate coordinate counts must not be added or multiplied and described as executed product tests.

Independent combinatorial count cross-check: graph/partition levels have sizes `sum(v=0..4) n^v·2^(v choose 2)` (with `0^0=1`), namely **1, 76, 1,099, 5,422, 16,933**, summing to 23,531. Category path levels have sizes `(n+2)·2^n`, namely **2, 6, 16, 40, 96**, summing to 160. Cocycle levels have sizes **1, 1, 2, 8, 64**, summing to 76.
