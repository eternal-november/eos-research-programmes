# Independent exact finite verification

31 October 2026. `verify_i5.py` uses only the Python standard library. All products are independently evaluated as function composition; the candidate multiplication table is a checked assertion, not the source of products. `verify_results.json` is the deterministic machine-readable output; source SHA256 pins are included. These checks support the analytical arguments, not proofs of unbounded graph/profile claims.

## Results

* For every k=4,...,64: closure generated independently by a,b has exactly 3k−2 distinct stated normal forms; every entry of the complete multiplication table agrees. Both-sided substitution repair fixes H-membership; saturated joint binary-cut repair is precisely the index partition. The elementary nontrivial cut-round count is `max(2,ceil(log2(k−2)))`. Saturated S-then-C sweeps have counts `2,k,2k,3k−2`. The aM separator excludes the second constant.
* N=2 scalar M4: the complete **label-template** model uses three distinct active-size sorts `(1)`, `(2)`, `(1,1)`, with carriers 10,10,100. Included are all one-hole substitutions and all ordered consecutive cut groupings: unary factorizations on both unary size types; a common-parent rank-two cut (1,000 records); and a separate-parent rank-two cut (10,000 records). Outer and inner factor partitions are arbitrary current tuple partitions, never forced coordinate products. Combined S/C block counts are `[2,2,4] → [3,3,16] → [9,5,65] → [10,10,100]`.
* The intermediate difference between the two unary size sorts is intentional: a size-one input can be embedded in a two-vertex context, while a size-two input has no such context under the same bound. Rank-only sorting is therefore unjustified for intermediate repairs.
* C alone has counts `[2,2,4] → [3,3,16] → [4,4,34] → [4,4,38]`. In particular, the rank-two C result is **38**, not the coordinate-index product with 16 classes. This is a substantive shared-parent effect, not a numerical artifact.
* Concrete splitter, verified for every tested k: `(A1,A1)` and `(A1,B1)` have the same coordinate indices. The query “one parent of index 1, both children of index 0” succeeds for the first and fails for the second. The parent candidate sets for A1 and B1 are respectively `{A1}` and `{B1}`. Marginal feasibility is true for both; joint feasibility fails. This does not by itself constitute locally *complete* module failure.
* M4² unary: 100 labels; all 100 block-diagonal actions on eight boundary points conjugate under the actual block-swap permutation to channel reversal. C/T commute at the selected first-channel seed (16 resulting classes); combined repair reaches 100. This is not a claim of generic C/T commutation.
* Exhaustive pairing of 1,000 scalar shared-parent records with 1,000 second-channel records checks 1,000,000 actual two-channel records at 10,000 fixed sources, with source-fibre cardinalities equal to the product of the independent channel fibre cardinalities. Direct construction checks every paired equation. This is channel independence, **not** independence of branches sharing a parent.
* Z4→Z2 and two-channel Z4²→Z2² positive controls remain stable on all N=2 templates. The latter keeps counts `[4,4,16]`, strictly compressing carriers `[16,16,256]`.
* An explicit empty-position graft retains all seven resulting slots, including empty ones. Full profile/frame tags are kept distinct even with the same empty-erased label tuple. Every scalar M4 two-branch associativity instance (10,000) passes.
* The six-state relational equivariance counterexample passes: C-stable P becomes C-unstable after involutive transport closure. It is only a warning example, not the graph-label family.
* Independently reconstructed the eight-element transformation monoid in `modular_repair_theorem.md` §8. Both stated two-block partitions are unary S/C-stable, their three-block intersection is S-stable but C-unstable, and the explicit source0/source1 shared-factor failure holds. N=2 template tests also confirm that the original local seeds cease to be C-complete. Thus the complete-local-repair counterexample is correctly restricted to N=1; do not silently promote it to the frozen principal N≥2 family.

## Coverage boundaries

No enumeration of all old graph-C5 profiles is claimed. The N=2 computation is complete for the stated finite **label** templates and size types; actual old graph admissibility remains an external guard. Unbounded arity, empty runs, grade paths, and unary/cut depth require the analytical schema and coordinate-necessity arguments. Full M4² rank-two S/C repair (10,000 states, up to 100,000,000 separate-parent records per cut template) was not enumerated. Its discrete endpoint is supported by the scalar necessity/channel-swap proof, not presented here as measured output.

No numerical output is used to infer an unbounded theorem, an optimal runtime, or unbounded saturated sweep counts. The old C5 commutative scalar theory is not identified with these noncommutative active labels. Presentation conservativity and scoped certificate transfer require the separate analytical comparison proof.

## Reproducibility

The bundled scripts pass Python compilation. Two successive runs of
`python3 verify_i5.py` produce byte-identical output. The source-pin metadata
names the final bundled mathematical files. All mathematical checks and every
non-source-pin JSON result are unchanged from the independent original run.
The source-pin update changes metadata only, not test logic.

SHA256:

* `verify_i5.py`: `52ce256225bc6b441f59216b85de9e00467216ae8f9d825178cbfbc7b3551fcc`
* `verify_results.json`: `2d40b08d000f2d6cf2b40c70202deacd5e5e3afcb8d2d1b537e4dde3c515aad6`

`python3 verify_modular_bridge.py` produces the bundled
`modular_verification_results.txt`, including the N=1 counterexample and failure
of its coordinatewise extension at two and three active inputs. Portable replay
commands are listed in README.txt.
