# Independent finite checks for I3 incidence descent

The executable checks distinguish three prescribed maps rather than replacing
the cut span by an arbitrary set of the same cardinality:

1. The original labelled ordered graph-cut object `X`, with actual vertex
   partitions, empty blocks, and actual composable arrows of the three-object
   category `[2]`.
2. F4's edge-forgetting map `X -> Y`, retaining every actual vertex placement.
3. `q: X -> Y -> Z`, where the second map is the homogeneous edgeless instance
   of F3's explicitly presented binary placement equations `L`. A target
   `Z_n` record consists of an ordered size vector and the retained arrow path.

The verifier is independent Python code: it imports no prior F3, F4, E5, or
author implementation. It reconstructs actual induced graphs and canonically
reindexed subsets from adjacency masks. Every cardinality is a cardinality of
labelled finite **sets**. There are no automorphism denominators or unrecorded
groupoid cardinality conventions.

## Run

```sh
python verify_i3.py --output results.json
python run_guards.py
```

The second command replays the complete suite normally, with `python -O`, and
with `PYTHONOPTIMIZE=1`, requiring identical mathematical JSON results. It also
runs four intentional semantic mutations in normal and optimized mode; each
must exit with code 1 after a mathematical check detects the defect. Neither
implementation uses an `assert` statement. The runner checks that syntactically
and records SHA-256 hashes of its exact sources.

## Finite domains

| Check | Explicit domain |
| --- | --- |
| Simplicial naturality of both actual maps | Every ordered simple graph on 0–3 vertices, every partition and `[2]` arrow path in degrees 0–3, every monotone operator with target degree 0–3 |
| Composition of simplex operators | Same with 0–2 vertices, initial degree 0–3, intermediate and final degree 0–2 |
| Active lifting fibres of `q` and F4 | Every actual source simplex on 0–3 vertices, fine/coarse degrees 0–3, every active operator |
| Independently generated pullback pairs | Every graph on 0–2 vertices, coarse degree 0–2, fine degree 0–3, all compatible independently enumerated target records |
| Representative independence | All 76 ordered simple graphs on 0–4 vertices, all binary partitions, every arrow and every two-factor factorization in `[2]` |
| Coassociativity, counits, factorial correction | Sizes 0–12, every arrow of `[2]` |
| F3 cluster occupancy formula | Every contiguous-clique composition of 0–6 vertices, all actual partitions in degrees 1–3; all restriction operators of target degree 0–2 for 0–4 vertices |
| Direct R/E group action and stabilizer | All degree 1–3 partitions of selected trivial `P4`, cluster `K3+K2+K1`, complementary contiguous multipartite, complete-4, and edgeless-4 fixtures |
| Coefficient-unstable coarsening | Ordered `K1,3` and `P4`, padded with isolated vertices to each size 4–12 |
| Standard and transported Möbius inverses | Sizes 0–12, every arrow of `[2]`, both convolution orders for the standard inverses |
| Effective length | Sizes 0–4, degrees 0–6, all size compositions and `[2]` paths; the sharp bound `v + j - i` is attained |
| Non-finite-length control | Empty graph over identity in `C2`, with 2, 4, …, 40 nonidentity factors |

`results.json` gives exact counted cases. The script includes malformed-domain
rejections, actual whole-edge loss, actual partition loss under `q`, and the
positive contrast that F4 retains those placements. Repeated identical graph
inputs, genuine mixed interfaces, nullary units, empty nonidentity-grade
factors, and the nonhomogeneous six-vertex graph `K3 + K2 + K1` are included.

## What the checks establish

The actual source cut counts pushed to size observations are binomial and
independent of the representative graph. They are not the intrinsic unit
coefficients of the prescribed size-cut target. Actual `q` lifting fibres have
the specified multinomial multiplicities; F4's corresponding fibres are
singletons. Cluster occupancy fibres have the product-of-multinomials formula
and the weight ratio `w(G) / product w(input)`, where
`w(G) = product(clique_size!)`.
Directly enumerated permutation actions also check the orbit/stabilizer formula
`|H_G| = |orbit(partition)| product |H_(G|U_i)|` on fixtures from all four
inherited R/E regimes. Every actual input graph is compared before and after
the action. This is not a fresh exhaustive proof of the F3 classification.

The diagonal map `e_v -> v! z_v` satisfies the coalgebra identity, but its
integral inverse is unavailable and its size-2 diagonal vanishes modulo 2.
It does **not** identify the two standard zeta functions. The standard Möbius
values tested are `(-1)^v mu_[2](i,j)` for the binomial coalgebra and
`(delta(v,0)-delta(v,1)) mu_[2](i,j)` for the intrinsic size-cut coalgebra.
The pullback of the latter's zeta is `v!`; its corresponding inverse is tested
separately.

The edge-count observation is genuinely unstable: the star and path both
have whole observation `(4,3)`, but their coefficients at `(3,2) tensor (1,0)`
are 3 and 2. After isolated-vertex padding, the coefficient at
`(1,0) tensor (v-1,0)` remains 1 for the star and 0 for the path. Grades and
their intermediate interface are fixed in both comparisons.

## Deliberate mutations

- `collapse_lifts`: replace the expected actual lift multiplicity by 1.
- `unit_coefficients`: replace binomial source coefficients by native target
  coefficients, demonstrating that coassociativity alone is not a sufficient
  verification of the claimed quotient.
- `wrong_factorial`: replace the diagonal weight `v!` by `v+1`.
- `ignore_empty_grade`: incorrectly bound effective length by vertex count
  alone, excluding legitimate empty nonidentity-grade factors.

## Evidence limits

These are finite C certificates, not proofs for arbitrary size, arbitrary
finite categories, arbitrary scalar decorations, or groupoid quotients.
Unbounded statements require the author's mathematical proof and independent
review. No claim is made that E5's arbitrary nonexact span cells constitute
this simplicial object, that arbitrary scalar decoration is cut-compatible,
or that finite test counts settle I3 scientific acceptance. The observed
`C2` examples corroborate, but do not prove, the unbounded-length obstruction.

The only new files are in this I3 working directory. Original contract and
prior-work files are read-only inputs; no uploads or external state changes
are part of this verification.
