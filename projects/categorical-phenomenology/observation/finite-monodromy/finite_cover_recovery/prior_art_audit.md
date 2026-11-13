# Primary-source comparison: finite evidence for component-cover monodromy

## Scope

The model considered here is a circle-indexed family of mixtures of categorical distributions. Each independent restart chooses one component, then produces a length-t iid trajectory from that component. The exact model promises a fixed number p of distinct components, a positive lower weight bound, uniform component separation, and a known local Lipschitz bound. The target is the conjugacy class of the component-cover monodromy, with any stochastic-width conclusion supplied by a separate structural theorem.

This is a comparison with verified primary sources, not a claim that the complete pipeline is new or that the search is exhaustive.

## Direct statistical predecessors

### Fan and Li, COLT 2023

**Efficient Algorithms for Sparse Moment Problems without Separation.**
[Published paper and PDF](https://proceedings.mlr.press/v195/fan23b.html).

Theorem 6 applies to the same local observation model: one categorical component is chosen for a group, and all observations within the group are iid from that component. For a p-atomic mixing measure on the categorical simplex, it gives L1-transportation error O(epsilon) with probability at least 0.99 using polynomially many one- and two-observation groups and (p/epsilon)^{O(p)} groups of size 2p-1. It requires no component-separation assumption for this transportation guarantee. Theorem 5 supplies the underlying higher-dimensional moment inversion.

**Difference:** this is local mixture recovery, not reconstruction of how components continue around a parameter circle. However, it already supplies a quantitative local estimator suitable for that reconstruction. If all true weights are at least w*, separation is delta, the estimate has at most p atoms, and its transportation error is eta < w* delta/4, every true atom has a distinct estimated neighbor within eta/w*. Thus local recovery need not be presented as a remaining statistical result. Shorter groups can be obtained by truncating separate longer trajectories.

### Rabani, Schulman, and Swamy, ITCS 2014

**Learning Mixtures of Arbitrary Distributions over Large Discrete Domains.**
[Primary preprint](https://arxiv.org/abs/1212.1527).

Their sampling aperture is the trajectory length in the present model. They prove local recovery at aperture 2p-1 and general impossibility at aperture 2p-2, including hard instances with separated Bernoulli components. Their finite-sample theorem uses a width parameter incorporating both pairwise separation and a lower bound on a smallest nonzero covariance eigenvalue. Pairwise separation alone does not uniformly bound that eigenvalue near affine-rank degeneration; the advertised quantitative rate should not be imported with constants asserted to depend only on delta and w*. Fan–Li provides a later separation-free transportation guarantee.

**Difference:** the hard local-estimation instances do not themselves prove a monodromy lower bound. Bernoulli components lie on an interval and, while distinct, admit a global order. A topology lower bound must distinguish families with different monodromy, not merely different component parameters.

### Vandermeulen and Scott

**An Operator Theoretic Approach to Nonparametric Mixture Models.**
[Author-hosted paper](https://web.eecs.umich.edu/~cscott/pubs/aos_mixture.pdf).

Theorems 4.1–4.4 distinguish two sharp general thresholds: 2p-1 grouped observations identify a p-component mixture against alternatives with at most p components; 2p observations determine it against alternatives with arbitrary finite component count. Three observations suffice under linear independence, an assumption stronger than pairwise separation.

**Difference:** identification within a promised p-component class is not certification of that promise. In particular, the local distinction between p and p+1 components must not be conflated with a separate global distinction between stochastic widths p and p+1.

## Adjacent topological predecessors

### Yim, 2025

**Inferring Ambient Cycles of Point Samples on Manifolds with Universal Coverings.**
[Primary preprint](https://arxiv.org/abs/2502.02400).

Constructs transition maps and induced monodromy from finite point-cloud data on a Riemannian manifold, using its known universal covering and suitable metric/geodesic information.

**Difference:** the ambient covering is an input. This does not infer an unknown component cover from noisy grouped categorical observations. It nevertheless establishes that finite-data transition-map and monodromy constructions are existing methodology.

### Scoccola and Perea, 2023

**Approximate and discrete Euclidean vector bundles.**
[Published paper](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/approximate-and-discrete-euclidean-vector-bundles/0FD787673265108D500C4D997F661F5C).

Develops approximate cocycles, finite-sample bundle reconstruction, and stable computation of low-dimensional characteristic classes.

**Difference:** the inputs and target are approximate Euclidean vector-bundle data. Ordinary isomorphism of the vector bundle associated to a permutation representation can forget the finite covering's full discrete or flat structure. Over a circle, real vector-bundle classification does not retain every permutation cycle type. These results therefore should not be substituted for a full permutation-monodromy recovery theorem.

### Brysiewicz and Kim, 2026

**How to recover a permutation group amidst errors.**
[Primary preprint](https://arxiv.org/abs/2602.23505).

Studies recovery of a permutation subgroup from samples drawn from a mixture of the uniform laws on that subgroup and the ambient symmetric group, motivated by numerical monodromy computation.

**Difference:** the observations are already permutations and the target is a subgroup. The present observations are categorical trajectories, and the circle target is a generator permutation up to conjugacy. Its noise model is not a model for arbitrary matching errors without further justification.

### Balakrishnan, Rinaldo, Sheehy, Singh, and Wasserman, AISTATS 2012

**Minimax rates for homology inference.**
[Published paper](https://proceedings.mlr.press/v22/balakrishnan12a.html).

Provides finite-sample upper and lower bounds for manifold homology under several noise models and explicit geometric/distributional assumptions.

**Difference:** homology is not full covering monodromy, and the observations and promises differ. This is relevant precedent for statistical topology and promise-dependent minimax analysis, not a direct solution of the categorical component-cover problem.

## Interpretation of the proposed result

The elementary upper-bound pipeline combines an existing local estimator with a deterministic continuation lemma: accurate component estimates at adjacent mesh points have a unique correspondence when the local movement and estimation errors are sufficiently small relative to separation. Composing these correspondences, including the closing edge, gives monodromy up to conjugacy. The mere existence of this pipeline should not be portrayed as resolving an unknown local mixture-learning problem.

Potential substantive work lies in the precise end-to-end theorem, sharper trajectory-length/restart/query tradeoffs, topology-specific lower bounds, or the separate structural theorem translating monodromy into stochastic width. These possibilities are not novelty claims.

All conclusions are conditional on the exact model promises. Finite samples do not certify separation at every unsampled point, a global Lipschitz bound, exact iid-within-component behavior, or absence of additional components of arbitrarily small weight. Likewise, a local mixture-estimation lower bound, a worst-case mesh-gap obstruction, and a rare-component restart lower bound do not automatically combine into a matching lower bound for the full topology-recovery cost.
