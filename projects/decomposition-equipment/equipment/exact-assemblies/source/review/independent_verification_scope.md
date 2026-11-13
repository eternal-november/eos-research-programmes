# E5 independent finite replay and scope

**Result: PASS for the declared bounded finite checks.** A separate in-team AI reviewer copied exactly the frozen six-source manifest into an independent directory, checked every SHA-256 before and after execution, inspected the computations, and replayed the baseline, semantic mutations and guard suite. This is independent execution and inspection, not an external human or a new proof-assistant certificate. It does not by itself accept the parameterized mathematical theorem.

## Frozen input and exact replay

- Final finite manifest SHA-256: `8c9aa9ef9e7d6e7accae5c7974c16f417e0b07cb49fecbd7cd440939af859622`.
- Independent source root: `/workspace/shared/e5_independent_replay_20261031/final/source`.
- Three baseline modes, normal / `-O` / `-OO`, gave byte-identical output. All nine semantic mutations rejected in all three modes: **27 rejection controls**.
- The isolated guard suite passed **58 controls**, covering protected output aliases, source/dependency drift, exact manifest membership/schema, source symlinks, actual optimization mismatch, and a complete inherited-`PYTHONOPTIMIZE=2` replay.
- Independent finite receipt SHA-256: `ecb9ccf7dbd5c2ed490c6f2da9a3657dae26eb75fc388e6b9f9c64f6c2efc3c2`.
- Independent guard receipt SHA-256: `f393c336678b9b236168dbf2cefa006c9097fb138a429d53c915df85847478a4`.
- Each receipt is **byte-for-byte equal** to its separately produced verifier-owned receipt. Source and manifest bytes still match the independent copy after execution. The exact E3/E4 dependency bytes also match their prior source identities.

The earlier superseded source snapshot and its exploratory outputs are not evidence for this acceptance and are not included in the clean delivery.

## Actual finite objects inspected

The checker constructs finite functions with explicit domains, codomains and image tables, actual restricted spans, tuple carriers, typed graph partitions, scalar products and actual substituted cells. The verdict is not supplied by an expected-verdict field. In particular:

- **1,895 actual path comparisons**, including all 1,792 pairs of two-point relations with the seven middle maps of domain size 0–2; **7,981 target lift fibres** in the primary suite. The concrete examples distinguish fibres `[2,1]`, `[1,0]`, `[2,0]`, `[1,1]`, and missed `[0]` from mere endpoint support or equal cardinalities.
- The adjacent-vacuity control computes two empty-to-empty local comparisons but a whole-path empty-to-singleton comparison. Its all-run registry retains the failing length-three interval.
- **20 nullary diagonal fixtures**, including empty sets, test actual `A′ → A′ ×_A A′` tables against injectivity. Positive-path empty products are not substituted for this test.
- **88 full-tree coefficient maps** over all 22 binary shapes with 2–5 leaves and four uniform internal-map regimes; **1,096 contraction-prefix equalities**. Recursive substitution is compared with a separately constructed flat coefficient table; full cells include their forests and scalars. The receipt key `retained_tree_local_comparison_squares: 98624` counts **summed local-comparison domain entries**, not 98,624 distinct squares.
- **60 finite function inverse cases** between carriers of size 0–3. Actual two-sided inverses are enumerated. The retained `1 → 2 → 1` and involution-scalar examples explicitly refute root-only reconstruction and root-only normalization. A branching/nullary assembly retains every scalar.
- Cartesian restriction is tested by actual unique-factor enumeration on one nontrivial profile (three scalar cases), and an actual pulled-back bijection. This is distinct from the nonbijective internal seam comparison in the same equipment.
- All ordered graphs on 0–4 vertices and partitions into 1–3 named blocks: **157 partition cases and 939 reconstruction fibres**, each of cardinality `2^(cross-block pairs)`. Two cross-edge-different wholes have the same local pieces and no required unary factor; both remain legitimate cells. The no-cross-edge and retained-labelled-cross-edge repairs are checked directly.
- Scalar congruence closure is computed for the unit-subgroup and absorbing equations in the three-element monoid. Literal scalar-one, scalar-unit, coefficient-bijective and actual universal marks are kept distinct. Actual doubling sections and a postmap derive the parallel `id_2 = constant_2` equation, while actual factor fibres distinguish their prequotient universal behavior.

All nine mutations change a mathematical operation, a retained registry or a tested interpretation: lift deduplication, support-for-bijection substitution, adjacent-only retention, nullary empty-product treatment, rotated tree map, root-only reconstruction, omitted nullary scalar, existential-for-representative-invariant marking, and erased whole-graph reconstruction data. The cross-edge mutation uses the same reconstruction-key injectivity law in baseline and mutant.

## Separate independent supplements

`independent_supplementary_checks.py` supplies an additional direct finite oracle and runs against the same frozen sources. Its normal, `-O` and `-OO` results agree byte-for-byte.

- **610 mixed exterior/internal comparison tables**, covering **75,682 target witnesses**. The independent oracle constructs raw restricted spans and enumerates complete tuple sets from products of actual apex sets, then compares every entry of the actual comparison table. Families include duplicated witnesses, nonidentity exterior maps, mixed surjective/nonsurjective/empty internal maps, and path lengths 2–4.
- **153 mixed-chart graph-word tree tables** with **288 proper-node contraction equalities**, including nonempty graph words, one empty-graph occurrence and the distinct empty word. These preserve actual forests and scalar labels, extending the primary empty-word tree fixtures.
- A three-vertex whole with only the first-to-third edge is active, while its first-two-vertex induced graph is inactive. Duplicating the proper seam produces a genuinely two-to-one actual map. Actual forward and section cells give inverse composites modulo the active-root coefficient relation, but fail the inactive proper-node relation. This verifies the root-mask boundary from actual maps and graph partitions, not a root PASS flag.
- The square-zero monoid `{1,a,0}`, with `a²=0`, is checked directly: the classes `{1}` and `{a,0}` form a multiplication congruence preserving both literal identity and unit marks, while the required fixed-endpoint lift from outer scalar `a` to target scalar `0` is absent. This is a separate finite boundary, not a universal classification.

To replay the supplement from a packaged E5 root:

```sh
python -B review/independent_supplementary_checks.py --source-root .
```

The supplement shares the frozen primitive representations and transport functions. Its raw comparison oracle and finite monoid tables are independently implemented; this is not a wholly independent implementation of the equipment.

## Scope and omissions

1. Finite checks do not prove arbitrary arity/depth, every finite interface size or every commutative monoid. Primary trees are binary and use empty words; labelled mixed-chart supplements still have finite depth and do not enumerate arbitrary single-graph cut trees, graft/interface diagrams or all nullary-tree shapes. Those claims require the parameterized P proof.
2. The full generated congruence kernel, all-context equation closure, intrinsic quotient universal-property classification, certified cut-groupoid contractibility, factorial isotropy and scalar `H^r` memory results are not established by these finite examples. Their proof/source audit is separate.
3. **Every fixed-sort substitution quotient of a complete virtual equipment preserves its chosen cartesian restriction and contextual-unit bijections (L/U).** The demonstrated quotient failure concerns an extra actual-bijection or literal-normalization mark, not the existence/uniqueness of ambient restrictions. Existential marked representatives are not representative-invariant descent or faithful recovery of supplied witnesses.
4. Exact E3/E4 primitives are reused; their entire prior regression suites were not rerun. This evidence does not assert that the single-graph S model normally embeds into the graph-word W model, or equate W's empty word with one empty-graph occurrence.
5. The author theorem was inspected for compatibility of these scopes. Frozen mathematical acceptance, inherited proof attributions and the original contract's substantive passing floor remain the separate mathematical auditor's responsibility. No new Lean formalization, universal equipment theorem or later contract item is accepted here.

No original dependency source was modified. Only the final clean reports, receipts and supplemental source are supplied for packaging; private scratch and superseded runs are excluded.
