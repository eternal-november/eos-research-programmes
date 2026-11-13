# Frozen finite-checker complexity (F stage)

Source: check_integration.py SHA256
c566fe03d1dadab293fada67c799a6ed53f74d2cf5086db38df3185d75d077ae,
`factor_structures`, `check_factor`, `run_F`. This analyzes the validator, not the
mathematical normal-form/equality algorithm from P.

For one fixed whole graph on n vertices and one witness of arity a, choose an
interval of q leaves. The outer operation has p=a-q+1 leaves. The code generates
all intermediate graphs K with 0≤k=|K|≤n. Their count is
G(n)=sum(k=0..n)2^(k(k-1)/2), asymptotically Theta(2^(n(n-1)/2)).
For EACH K it enumerates all p^n outer ordered partitions, then computes their
full profiles. Thus the exact number of outer profile checks is G(n)p^n.
This G(n) ALREADY includes all intermediate sizes; no further graph-bound factor
belongs in this per-fixed-whole count.

Only when an outer profile matches does the code enumerate all q^k inner
partitions. Let A_k be the number of matching outer candidates of size k. The
exact number of inner candidate checks is sum_k A_k q^k, not G(n)p^n q^n.
Moreover sum_k A_k≤p^n: each outer partition determines its middle restricted
graph K, so at most one K can match. Profile cardinalities further force k to
the sum of the original interval component sizes; the brute outer loop does not
exploit that fact to skip the other K values.

Graph.restrict sorts the chosen vertices, rebuilds a set of whole edges, and
scans all vertex pairs. A full outer profile therefore costs at most
O(p(1+n^2)+n log(n+1)); a full inner profile costs
O(q(1+k^2)+k log(k+1)). Tuple creation/comparison does not make these O(1).
A conservative structural bound is consequently

    O(G(n)p^n [p(1+n^2)+n log(n+1)]
      + sum_k A_k q^k [q(1+k^2)+k log(k+1)]).

For fixed arities, the graph term has 2^(Theta(n^2)) growth; this is deliberately
brute independent validation, not an efficient algorithm or unrestricted proof.

After structural candidates S are cached, check_factor tries every one of m^2
scalar pairs for a monoid of size m, for each requested total value. Across all
m total values this is O(m^3 S) actual substitution tests, each with polynomial
composition/restriction cost. The structural cache key erases the value and
omits the monoid, so expensive structure enumeration is shared across all three
monoids and all totals. No multiplicity of unexecuted tests is reported.

## Concrete released run

For the named six-vertex arity-four witness, there are three intervals of
length2 (outer arity3) and two intervals of length3 (outer arity2).
G(6)=33,868, hence the exact outer-candidate scan count across the five
structural cache misses is

    33,868 × (3×3^6 + 2×2^6) = 78,404,420.

Do not multiply this count again by the three monoids or six total-value
choices: those calls reuse the five cached structural lists.

The separate Graphs(2) exhaustive domain has 27,270 operation/interval cases:
for a∈{3,4}, n≤2, multiply the 2^(n choose2) whole graphs, a^n partitions,
binom(a+3,2) C-arrow strings, m values, and
I(a)=sum(q=2..a-1)(a-q+1)=a(a-1)/2-1 proper intervals, then sum. Here I(3)=2,
I(4)=5. These are source-witness cases, not the inner brute candidate count.
The named six-vertex domain adds30 operation/interval cases but only five new
structural cache misses.

A separate author timing sample (not a math certificate) measured72,900 outer
checks in0.4792s, about152,123/s; extrapolating78,404,420 gives515s (~8.6min) for
the named structural scan. This is a measured-rate estimate, not a deadline or
claim that unobserved candidates have executed. Runs remain unchanged.
