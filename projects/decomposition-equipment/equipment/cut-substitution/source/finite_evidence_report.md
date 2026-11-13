# I4 finite C evidence — declared domains and replay

31 October 2026. **PASS on the finite domains below.** This is computational evidence for the pinned repaired theorem, not proof at all degrees, original-signature completeness, a new quotient theorem, or a disposition of the broader I4 contract.

## Replay and integrity

Run `python run_finite_checks.py > finite_results.json` from this directory (Python standard library only). The runner verifies SHA-256 pins of the theorem, frozen output, both implementation modules and itself before importing tests. `finite_source_pins.json` records the precise source versions. Its hashes are also embedded in the output. A repeated run produced byte-identical sorted JSON.

- Pinned theorem SHA-256: `cdcc40aeab3b0112737ae0c2765bf95821683e067bcad87adc722170b8ebd70d`.
- Result SHA-256: `e105f21e9c9c0b0528c3479440be7c4e750202b32a00c98a6d6ea9006be61dbb`.
- `python -O run_finite_checks.py` fails explicitly with “Refusing optimized Python”; tests do not depend on `assert`.
- An isolated temporary copy with one appended comment in `core_checks.py` was rejected with “Source hash mismatch: core_checks.py”. No original source was mutated for this control.

## Exact finite domains

| Obligation | Executed domain and outcome |
|---|---|
| O support order | All 70,226 support masks on 1×1, 2×2, 2×3, 3×3, 3×4 and 4×4 grids. Chain iff row-major and column-major **tag** lists agree. |
| O full types | Nine named empty-slot cases: real empty/id retention, genuine unit removal, nonidentity empty grade retention and forbidden deletion, missing/misaligned slot positions, repeated types with different occurrence names, interface mismatch. Additional explicit original segmentation mismatch and actual diagonal-leg-table validation. |
| Actual spans | Main independent-cut/lambda examples use boundary carrier `{0,1}` and four witnesses `(x,y)` with legs `x,y`. Refinements insert named identity spans before the relation. Equal types are repeated under distinct occurrence names. Tables are fully specified by deterministic constructors, not replaced by carrier cardinalities. |
| Lambda/CS/SC | Tree `top(p(a,b),q(c,r(d,e)),f)` with six named leaves, arbitrary opaque noncanonical proper beta bijections and three refinement levels. CS is old exact skeleton plus actual external forest; SC has normalized tuple carriers and tuple beta maps. The separate supplied noncanonical diagrams test general arrows. Lambda is recursively computed from actual beta tables and inverse tables, and every naturality equation is checked pointwise. |
| Fixed root scope | The code's node named `root` is the **final proper cut edge**, not the output root. A separate unchanged output span `{(x,y)}` and endpoint-preserving, nonbijective outer coefficient forget all internal path choices. Its root component is identity and its equation is checked on 128 witnesses. Thus no arbitrary root is inverted. |
| Double laws | 25 pairs of empty/nested/disjoint contractions, including contraction of q and its descendant r; simultaneous versus sequential contraction, horizontal restriction/naturality and middle-four comparisons checked on actual tables. Literal identities on the same noncanonical beta diagrams. Three successive arrows additionally check horizontal association and units; named forest substitution retains 24 final occurrence addresses. |
| Independent-cut Xi | Alternating interval cuts of 3,5,7,9 named atoms; 16,64,256,1024 compatible tuples respectively. Xi is explicitly old-row inverse beta, flatten, regroup, new-column beta. Both Xi bijections and `Xi_old K_rows = K_columns Xi_new` are checked pointwise. |
| W_sem DP | All 1,618 pairs of unary functions with source/intermediate/target sizes independently 1..3. Composite fibre DP versus brute enumeration. Branching widths 2..5 with three fine witnesses and two intermediate witnesses; nontrivial endpoint-compatible branching widths 2..6, up to 8,192 fine tuples, checks compatibility and product multiplicities. |
| W staging/masking | Explicit singleton→two-point inclusion→singleton collapse: semantic evaluated occurrence bijective, retained intermediate staged map not bijective. Separate 2→2 constant leaf map hidden by a constant root coefficient: same flattened root equation passes but retained W_sem fails. Old fixed-interface fibres `[1,2]` become `[1]` under a declared boundary-value-0 pullback, distinguishing requested new-only from old-and-new diagrams. |
| B exhaustive | All 16 binary endpoint-support relations per span, all 256 span pairs, all seven maps from carriers of size 0..2 to `{0,1}` independently at three interfaces: 87,808 comparisons and 89,600 target fibres. Explicit separately reindexed compatible tuple enumeration is compared with the internal lift product for every fibre. |
| B controls | All seven nullary diagonal maps; three actual spans following internal value1 restricted to internal value0 (both adjacent targets empty but full target singleton/no lift); cross-edge 1–3 whole-support quotient masking a failed intermediate fibre2; raw apex bijections covering a noninjective boundary change whose fixed-interface pullback factor maps are not bijections. |
| B growth | Arity1..12, internal lift multiplicities0..3, repeated span types with named positions. Explicit source enumeration guard at 100,000 tuples: arity12/multiplicity3 omitted because 177,147 exceeds guard. This omission is not a pass; the exact included samples are recorded. |
| R | Missing beta on a three-element same-endpoint apex gives six actual bijective candidates: verdict is **actual comparison not determined**, not every map noninvertible. Identity2→2 and constant2→2 share endpoint support but differ in invertibility. |
| Scalars | C2 nonidentity scalar has inverse but fails normalized-scalar-1 condition; absorbing zero in `{0,1}` under multiplication is the nonunit control. |
| Graphs/grades | All 729 nested subset pairs of a six-vertex graph with cross-edges; induced restriction composition. All 729 length-six grade paths in C3 check grouped composites. |
| Cluster Theorem B | Independent enumeration of all nonnegative joint tables of dimensions1..3 ×1..3 and total mass0..5: 3,212 tables, 1,595 distinct marginal pairs. Chain-supported candidate uniqueness is compared with interval overlap. Two-clique 2×2 mass0..2 each: 225 table pairs/196 marginal cases, union-chain condition and unique tuple. Explicit incompatible two-clique union support. |
| Representative distinction | K2 actual opposite cuts have inverted intersection support and fail. Their orbit marginals `(1,1)` admit the diagonal joint table. No actual slot permutation is manufactured. |

## Scope and nonclaims

The finite-span controls use the declared ambient CUT extension. They are not asserted to be generated by the original C5 discrete signature. The clique occupancy controls belong to the stated original contiguous-clique quotient class. Full typed O is separately required.

Invertibility throughout is evaluated coefficient-diagram invertibility over a **fixed retained provenance forest**. No test declares the occurrence-refinement forest-bearing arrow invertible. Semantic W_sem and fully staged W are explicitly different observations. Proper exact beta is not inferred from a root equation. Boundary composition B is not silently folded into fixed-interface W.

Whole endpoint-support quotient masking demonstrates only the weak quotient observation. Both its actual whole c_f and actual intermediate c_f fail; the quotient is not credited with creating an actual inverse. Missing beta choice is underdetermination rather than a universal obstruction to all chosen lifts.

The finite data and growth samples substantiate implementation-level formulas and sharp examples. They do not establish the theorem's arbitrary-depth statement; that belongs to the separate mathematical proof and audit. Scientific attribution/baseline comparison and overall acceptance remain parent-owned obligations.
