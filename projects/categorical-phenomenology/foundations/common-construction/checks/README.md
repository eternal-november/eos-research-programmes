# Exact finite checks for common realization and its boundary

Run with Python 3 and its standard library:

    python3 verify_boundary.py > actual_results.json
    cmp actual_results.json expected_results.json
    python3 -O verify_boundary.py > optimized_results.json
    cmp optimized_results.json expected_results.json

All arithmetic uses `fractions.Fraction`. Every check raises an explicit
exception on failure; Python's `-O` flag does not remove checks. Output is stable,
sorted JSON. Generated `actual_results.json` and `optimized_results.json` need
not be retained in the source distribution.

## What is checked

1. The diagonal two-object/two-attribute Boolean table has two distinct observed
   profiles and four profiles under intersection closure, including the empty
   intersection (top). This is a finite example, not a test of all FCA contexts.

2. The stochastic matrix with rows one half of `1100, 0110, 0011, 1001` has
   ordinary rank 3, affine row-hull dimension 2, and four exposed vertices.
   Opposite-vertex sums agree; adjacent sides are perpendicular and of equal
   nonzero length. Its generated convex hull is therefore a square, not a
   simplex. A four-position fooling set certifies nonnegative rank at least 4;
   the factorization `H = I4 H` gives the matching stochastic upper bound.

3. The stochastic matrix with rows one twelfth of
   `543, 525, 363, 345` has ordinary rank 3 and four exposed vertices forming a
   parallelogram. This is affinely a square, without a claim of equal Euclidean
   edge lengths. Explicit mutually inverse affine maps on spanning vertices
   identify its abstract convex hull with the preceding square. Nevertheless,
   `Hinner = Hinner I3` and the ordinary rank bound give minimum latent count 3.
   The three latent emission vertices lie outside the generated row hull.

4. A mixed test-restriction/meet-completion square commutes but is not a
   pullback. Its fine observed profiles are `10,01`, its fine completion is
   `00,10,01,11`, and restriction retains the first coordinate. The coarse
   observed and completed sets both equal `{0,1}`. The actual pullback has four
   witnesses, while the fine observed set supplies two. The missing witnesses
   are `(0,00)` and `(1,11)`. This distinguishes coherence from exactness.

5. All 16 deterministic coarse-grainings of four outcomes to two outcomes are
   tested. Four produce a point hull and twelve a segment. For each, an exact
   stochastic factorization through the one or two endpoint distributions is
   constructed. Every further deterministic map from two outcomes to two
   outcomes is tested, giving 64 two-stage commuting squares. The transported
   endpoint realization produces the same observation matrix. This is finite
   coverage of the stated maps, not an exhaustive test of stochastic channels.

## Mathematical scope of the certificates

A nonnegative rank-one matrix has rectangular positive support. In a
nonnegative sum equal to `H`, each summand's support must lie in the support of
`H`; otherwise a zero entry would become positive. The four selected diagonal
positions have the property that any pair has a zero at a cross position.
Consequently no one rank-one summand can cover two of them, proving the lower
bound 4. The script verifies the finite premises of this argument; it does not
search an uncountable collection of factorizations.

Each claimed exposed vertex uniquely maximizes a displayed linear functional
among the rows. It therefore cannot be a convex combination of the other rows.
Four extreme points in an affine two-dimensional parallelogram cannot be
isomorphic as a convex set to a finite simplex. Affine isomorphisms preserve
extreme points and affine dimension; a simplex with four extreme points has
affine dimension 3.

The standard generated-observable convex realization is the row hull with its
inclusion in the response simplex. A realization whose state object is a finite
simplex and which is both generated (the affine extension of the preparation
map is onto) and observable (the evaluation map is injective) would be affinely
isomorphic to that hull. Neither square therefore has such a finite-simplex
realization. This is **not** nonexistence of stochastic latent realizations:
explicit realizations with 4 and 3 latent states respectively are given.

For the boundary square, the displayed `I4,H` realization is generated but not
observable: mixtures `(1/2,0,1/2,0)` and `(0,1/2,0,1/2)` have identical output.
For the inner square, the displayed `Hinner,I3` realization is observable but not
generated: none of the three emission vertices is in the row hull. Thus
minimum latent cardinality is not determined by the abstract generated convex
hull alone; its placement in the response simplex matters.

These checks support elementary proofs in the report. They do not establish
novelty, physical realizability, statistical learnability, or a general
categorical theorem. There is no Lean formalization in this check package.
