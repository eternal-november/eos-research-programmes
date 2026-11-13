# A growing nonlinear family with unsupplied private factors

## Plain-language abstract

The sensors in this family do not correspond one-to-one to components. Each
sensor bundle sees a scrambled, noisy combination of three hidden variables.
Neighboring bundles overlap, but each also contains a private variable that no
other bundle exposes. Static agreement between bundles identifies the shared
variables but cannot identify the private ones: a private label can be changed
differently at every value of its shared neighbors without changing any static
overlap. The dynamics resolves this ambiguity when its independent local
updates are informative enough. A fair-noise case deliberately leaves the
ambiguity unresolved.

The family grows by adding bundles. Its whole hidden state grows exponentially,
but the proposed learner uses bounded observation tables and searches bounded
collections of past bundles. It discovers local state labels, the unknown
bundle overlap graph, nonlinear local updates, and a delayed signal needed at
the boundary. The observation assumptions are substantial: three independent
noisy views per bundle, local rank conditions, a finite delay bound, and a
declared independent-innovation dynamical universe. This is a structured
identification theorem, not a certification that arbitrary physical data belong
to that universe.

## 1. Family and declared observation access

For any N >= 4, arrange 2N hidden binary output variables a_i,b_i on a cycle.
The cycle order, latent labels, and correspondence of variables to sensors are
not supplied to the learner. Bundle i observes the latent tuple

    Z_i = (a_i,b_i,b_(i+1)).

Bundle names are visible only as measurement locations. Their cyclic order is
randomly permuted. Every bundle supplies three simultaneous sensor channels,
independent conditional on its latent tuple and independent of all other sensor
noises, past and future. All channels can have the same ten-symbol alphabet.
Their unknown 10-by-8 stochastic emission matrices have strictly positive
entries and full column rank. Thus no individual sample identifies even a
bundle state, and observed alphabet size does not specify hidden cardinality.

The learner receives stationary observation histories from these channels. It
does not receive latent samples, reset operations, membership queries, the
cycle, local state labels, or transition tables. The three-view bundle grouping
and conditional-noise model ARE supplied measurement assumptions.

Use independent fresh update randomness at each variable and time. Set

    P(a_i(t+1)=1 | history)
      = .12 + .04 a_i(t) + .06 b_i(t) + .08 b_(i+1)(t)
        + .03 a_i(t)b_i(t) + .02 a_i(t)b_(i+1)(t)
        + .01 b_i(t)b_(i+1)(t),

    P(b_i(t+1)=1 | history)
      = .20 + .15 b_i(t) + .20 a_(i-1)(t-1)
        + .10 b_i(t)a_(i-1)(t-1).

Indices are modulo N. These probabilities lie in [.12,.36] and [.20,.65],
respectively. Every displayed parent is essential. The terms involving products
give nonlinear interaction. There is feedback around the cycle through the
private and shared variables, not independent latent chains mixed only at the
sensor.

The actual sufficient Markov state consists of current a,b and previous a:
3N bits. A generic two-slice history representation would use 4N bits. No
claim of globally minimal hidden-state cardinality is needed here.

## 2. Discovery operations

### Unknown patch alphabets

The three-view tensor has the form

    T_i = sum_z pi_i(z) E_i^1(:,z) tensor E_i^2(:,z) tensor E_i^3(:,z).

The pair matrix has rank |Z_i|. Standard simultaneous diagonalization under
full-column-rank views identifies the emissions and latent bundle alphabet up
to a common permutation of its labels. A generic linear combination of third-
view slices has distinct eigenvalues, since distinct full-rank emission
columns admit a separating linear functional. This step is established
multi-view latent-variable machinery, not a novelty claim.

### Unknown bundle overlap and shared coordinates

Invert the learned emissions statistically on a pair of bundles. The resulting
latent pair support has edges exactly between tuple labels that agree on their
shared variables. This uses full support of the hidden output configurations,
which follows from positive local update kernels. Connected components of this
bipartite support recover the common coordinate.

For adjacent bundles the intersection is one b_i and the support has two
components. Disjoint bundles have a connected complete bipartite support.
Therefore these tests discover the cycle incidence and the shared b alphabets.
They do NOT expose a_i. Within each bundle, every shared-coordinate fiber has
two labels, and each fiber can independently be labeled as the two values of
an apparent private coordinate. There are 2^4 = 16 such complement charts.

### Learn a sufficient temporal context before testing products

The next tuple Z_i(t+1) has parents covered by the three patch-lag variables

    Z_i(t), Z_(i-1)(t-1), Z_i(t-1).

For example, b_(i+1)(t+1) needs a_i(t-1), which the third patch-lag variable
contains. The learner need not know this context. It enumerates sets of at
most three patch-lag variables from a declared two-slice window and minimizes
the conditional entropy of the next bundle state. A true sufficient context
is among the candidates. Its entropy equals the conditional entropy given
the whole past, so any exact minimizing context recovers the same full
conditional-next law on its supported contexts.

This step must precede the product test: marginalizing unknown common parents
can induce dependence between truly independently updated components.

The required observed laws involve at most three past sensor coordinates and
one next sensor coordinate. With ten symbols per sensor, this delayed
analytic construction can therefore require 10^4-entry raw temporal tensors.
The numerical immediate-coupling member described below uses only two past
coordinates and one next coordinate, hence 10^3 entries. Distinct sensors at a common patch/time must be
used when separate contractions would otherwise reuse the same noise. More
generally, a joint projection of a patch can use one learned left inverse.
The inverse is a signed statistical estimator, NOT a physical decoder that
recovers each hidden sample.

### The dynamics identifies private complements

Fix one sufficient old context. The next-state distribution on the true bundle
coordinates is

    Bernoulli(p) x Bernoulli(q) x Bernoulli(r),

with all three factors positive and p < .5. Every candidate private complement
that leaves the known shared coordinates fixed has the form

    a'_i = a_i XOR f(b_i,b_(i+1)).

Under its next-state distribution, conditional on next shared bits u,v, the
chance of a'_i=1 is p when f(u,v)=0 and 1-p when f(u,v)=1. Since the shared
tuple has full support and p != .5, a'_i is independent of the shared tuple
if and only if f is constant. Exactly two charts survive, differing only by
a global private-bit relabeling.

Thus the private factor is discovered from dynamical positivity/product
structure, even though no overlap isolates it. Static support connectivity
alone is insufficient. For a finite r-state private factor, one conditional
row with distinct private probabilities similarly forces all fiberwise
permutations to coincide. If repeated probabilities or symmetries remain,
retain the corresponding alternative charts rather than choose arbitrarily.

### Learn parent-lag sets and local mechanisms

After the factor charts are recovered, a signed sensor estimator for any
bounded tuple of factor values gives its exact joint probability law. Search
factor-lag sets of size at most three and minimize conditional entropy of each
next variable. Positivity gives full support on every finite history cylinder.
Consequently a kernel depending essentially on a parent cannot be represented
by omitting that parent and substituting other history coordinates. The
smallest exact minimizing set is its essential parent-lag set.

The resulting learned conditional tables are positive and reproduce the
true joint update because independent innovations are part of the declared
model universe. Low-order observations alone cannot certify that independence
promise against unrestricted external alternatives.

## 3. Scaling and statistical qualifications

For fixed sensor size, patch rank, maximum context size, and delay, all tensor
operations are bounded-dimensional. There are O(N^2) overlap tests and
O(N^4) patch-context tests in the naive search (N targets times O(N^3)
contexts), not 2^(3N) global states. Essential factor-parent discovery is also
polynomial for fixed maximum indegree. Constants can be large; this is not a
practical runtime benchmark.

Every selected k-output history cylinder has probability at least .12^k:
order the selected outputs chronologically, condition on earlier selected
outputs, and average the positive conditional local kernels over unselected
history. Within one time step the fresh update noises are conditionally
independent. This supplies bounded-table coverage independent of N.

The sum of single-parent total-variation influences is at most .30 for a_i
and .55 for b_i. Coupling two histories with shared fresh randomness gives
maximum site disagreement contraction by .55 every two ticks. A union bound
over current and required previous coordinates yields geometric mixing with
a prefactor O(N). Thus a gap O(log(N/epsilon)) ticks gives error epsilon for
one window coupling. For T sampled windows and total coupling error delta,
choose per-window error at most delta/T and a gap O(log(NT/delta)), in addition
to the fixed window length. A union bound then controls the entire sampled
collection. Fresh independent stationary episodes are another explicit
observation regime; independence is not obtained free by thinning a fixed gap
without accounting for T.

Finite-data identification additionally requires lower bounds on sensor
singular values, a spectral slice separation, positive latent support masses,
and a gap separating false context/coordinate candidates from valid ones.
No numerical QA below proves these finite-sample rates. Exact equality tests
must become confidence-separated tests or an explicitly retained candidate
family in finite samples.

## 4. Memory relocation is a real surviving ambiguity

The delayed term a_(i-1)(t-1) can be realized in at least two ways:

1. A one-bit boundary delay register stores the previous source output.
2. The source stores both its current and previous output and sends the
   previous one over a memoryless wire.

The full states are in bijection and the transition probabilities agree under
that bijection. Sensor observations cannot distinguish storage ownership.
There is one extra bit in either allocation, not an extra bit in BOTH. A
delay transducer receiving arbitrary binary input histories needs two states:
histories with different last inputs must produce different next delayed
outputs. This lower bound is conditional on the declared placement/timing
contract, not an unqualified physical-memory lower bound.

If the private update is fair in every context, then a_i XOR
f(b_i,b_(i+1)) remains independent of the next shared bits for all sixteen f.
The alternative coordinates can induce different dependency descriptions.
They are genuine observationally equivalent realizations in the broader
bounded-context universe; their admissibility under a tighter indegree bound
must be checked rather than presumed. In particular, substituting

    a_(i-1)(t-1)
      = a*_(i-1)(t-1) XOR f(b_(i-1)(t-1),b_i(t-1))

into the b_i update can require four parent-lag variables, including b_i(t),
rather than the original two. Therefore all sixteen charts are locally
product-compatible, but a global maximum-indegree-three universe can exclude
some. To retain every such fair chart in the explicit expanded family, permit
maximum indegree four and check the transported kernels. The QA reports below
count local charts, not accepted globally resource-constrained architectures.

## 5. Reproducible numerical checks and their limits

`check_hidden_patch_discovery.py` uses finite exact-law fixtures to test
local three-view recovery, overlap discovery, unknown component alphabets,
nonlinear parent discovery, and a two-tick delay. It constructs a small whole
transition law ONLY to generate and independently validate observable test
tables. The learner consumes bounded raw tensors, never that whole matrix.

The memoryless fixture has five components of sizes 2,3,3,2,2 and 72 whole
states. The delayed fixture has four components of sizes 2,2,3,2 and 576
two-slice whole states. All sensor alphabets have size ten; patch ranks and
component ranks are learned. Raw observable tensors have at most 1,000 entries.
It also verifies a concrete state-bijection intertwining source-owned and
boundary-owned delay memory, and a simple incompatible-pair marginal witness.

`check_private_complement_discovery.py` tests the cover {a,b},{b,c}. Static
overlaps expose b but neither private factor. Of four complement charts per
patch, exactly the two global-label variants survive generic nonlinear
conditional-product tests. Making a fair causes all four a-complements to
survive, which the checker retains. An explicit XOR transport preserves
observable two-step laws while generically destroying independent-factor
next-state products. The global state bijection proves all-history
observational equivalence when emissions are transported, not just the
tested two-step equality.

`check_growing_private_cycle.py` tests a four-bundle, eight-factor member of
the private-factor cycle family. Its numerical kernel uses the immediately
previous private value in each b update, rather than the extra delay, so a
two-bundle old context suffices. The unknown sufficient contexts are actually
selected by an entropy search over all old-bundle sets of size at most two.
Forty-four raw temporal tensors are queried, each of at most 1,000 entries.
Every bundle has sixteen private complement charts; exactly two survive in
the generic case. A fair-private variant retains all sixteen at its affected
bundle. These are local product-compatible charts; a tighter global indegree
or resource requirement would still require its own check. The generator's
256-state whole model is not passed to the learner.

These are exact-probability floating-point checks, not Lean proofs, external
human verification, finite-data experiments, or a production discovery tool.

