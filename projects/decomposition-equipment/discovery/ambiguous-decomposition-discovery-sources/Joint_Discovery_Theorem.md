# Auxiliary refresh theorem and main-route sensor-discovery lemma

**Status:** Sections 1–8 are an auxiliary calibration, not completion of the demanding locally coupled target. The main-route contribution is Section 9, applicable to the independently developed noisy-copy ring family.

## Result and boundary

There is a polynomial constructive theorem for a growing interacting subclass: **bounded-width positive junction-tree refresh systems**. The input is a family of experimental readout scopes and their separate noisy stationary history laws, not a true partition, hidden positive frame, alignment of latent states, or junction tree. Singleton temporal covariances recover local noise and persistence; bounded-scope Fourier inversion recovers positive local laws; a maximum-weight spanning-tree calculation discovers all admissible bag-tree architectures in compact form; exact overlap identities decide a compatible positive joint lift in this class. The lift includes an operational causal sampler, aliases, timing, and resource charges.

This is an existential/conditional theorem. Failure of its architectural test excludes this **scope-resident junction-tree class**, not all possible bounded-interface realizations. Experimental scopes impose a locality contract: each supplied scope is resident in one component. Removing that contract is a different treewidth/completion problem. Exact bag data can determine the Markov completion law while leaving many physical wiring trees unresolved; the theorem does not establish ambiguity of that law or identify the actual physical world. Arbitrary non-Markov completions remain outside its guaranteed realization family.

## 1. Fixed subclass and partial experiments

Let V be N named binary readout ports. Experimental scopes B_1,...,B_m cover V, each of size at most w, with fixed w. Scopes can overlap and need not be a partition. They specify what each experiment measures and what a prospective local component must jointly own/read, not which junction-tree edges or separators actually exist. Duplicates may be removed after checking identical data.

A candidate whole has a positive distribution pi on {−1,+1}^V and stationary dynamics

    X_(t+1) = X_t with probability q;
              an independent draw from pi with probability 1−q,
    0 < q < 1.

At port i the readout is O_i,t = X_i,t D_i,t, where D are independent over ports/times, independent of X, and have unknown means 0<rho_i<1. Every fixed scope has an autonomous refresh marginal with the same q. Thus experiments may have different lengths, different scopes, different sampled lags, and independent stationary starts; no common observed history or state reconstruction is presumed. Do not combine samples from separate experiments as if they were same-episode joint observations. Independent records must each start in pi's corresponding marginal, or carry an explicitly modeled burn-in.

The realization subclass requires a tree T on the experimental scopes with running intersection: bags containing any port form a connected subtree. It requires pi to be the positive Markov completion of its bag marginals along T. This is a standard conditional-independence restriction, justified by a local separator sampling architecture. The interaction size can grow without bound; Section 7 gives connected examples.

## 2. Local discovery without a global positive frame

Each i has a singleton experiment (or a larger experiment projected to i) containing stationary lag-one and lag-two products. Write

    a_i = E O_i,t,
    c_i,l = E[O_i,t O_i,t+l] − a_i^2, l=1,2.

For any positive pi, |mu_i|<1, where mu_i=E X_i. The refresh law gives

    c_i,l = rho_i^2 (1−mu_i^2) q^l.

Consequently every c_i,1 is positive and

    q = c_i,2/c_i,1,
    rho_i = sqrt(a_i^2+c_i,1/q),
    mu_i = a_i/rho_i.

All recovered q values must agree and lie in (0,1); all rho_i must lie in (0,1). The convention rho_i>0 fixes only the otherwise unavoidable local sign gauge. If sensor signs are not calibrated, retain both sign gauges and transport every adjacent table accordingly; never declare a physical sign identified.

For a scope B, let h_B(S)=E product_(i in S) O_i at one time. Its latent character moment is

    g_B(S)=h_B(S)/product_(i in S)rho_i.

The local positive frame is synthesized, not supplied:

    p_B(x)=2^(−|B|) sum_(S subset B) g_B(S) product_(i in S)x_i.

Check normalization and strict positivity. This costs O(w 2^w) using a Walsh transform, besides reading the table. Only 2^w-sized tables are built; no 2^N-state frame is reconstructed. The temporal identification above is necessary but not sufficient for arbitrary external history laws: verify each supplied finite history table against the refresh-HMM constructed from p_B,q,rho, or assume the declared refresh universe. Without that membership assumption, matching finitely many moments does not establish equality of every history law.

## 3. Discover architectures by weighted trees, not enumeration

Build the complete graph on bags with edge weight s_ab=|B_a intersection B_b|. Let n_i be the number of bags containing i and

    R = sum_(i in V)(n_i−1) = sum_a |B_a|−N.

For any spanning tree T,

    sum_(ab in T) s_ab <= R.

Indeed, for fixed i the T-edges with both endpoints containing i form a forest on n_i vertices, with at most n_i−1 edges. Equality holds exactly when every such forest is connected. Therefore:

**Architectural discovery lemma.** The scope family admits a junction tree iff a maximum-weight spanning tree has weight R. Every maximum-weight tree is then a valid architecture; the full unresolved family is represented by the graph, weights, and optimal-weight equality, rather than enumerated.

This remains true with zero-weight edges, which connect independent pieces in the canonical completion. Run Kruskal or Prim in O(m^2 log m) after O(m^2 w) intersection construction. One witness tree is sufficient for execution; retaining the weighted-graph constraint does not pretend that witness is the unique physical architecture. Distinct trees can give genuinely different wiring and depths even when their stochastic law agrees.

## 4. Exact joint-lift test and witness

Check that every two bag tables have identical marginals on their intersection. It suffices to check separator consistency along a discovered running-intersection tree, since equality propagates along the path for each common subset. For clarity, direct all-pairs checks cost O(m^2 2^w).

If local tables are strictly positive, compatible, and a junction tree exists, set

    pi_T(x) = product_a p_Ba(x_Ba)
              / product_(ab in T) p_(Ba intersection Bb)(x_(Ba intersection Bb)).

Empty-separator probability is one. This formula is strictly positive and normalized. Root T; sample root from its table, then sample each child’s new variables from p_child(new | separator). Leaf elimination proves normalization and that each bag marginal is the specified p_B. It also proves the conditional-independence/Markov property and uniqueness within the chosen tree’s Markov-completion subclass.

Conversely any whole in this subclass must have these overlap equalities, a running-intersection tree, the same reconstructed local tables, and the displayed product factorization. Thus the tests are necessary and sufficient **for a scope-resident positive junction-tree refresh lift**. They are not merely a generic global-section criterion: all tables, denominators, state variables, random draws, transition steps and readout maps have been exhibited.

For discoveries A and B from different experimental collections: first identify only shared *named observed ports*; run the local sensor/persistence checks on overlaps; pool the scopes and rerun the tree/overlap tests. Success gives a common whole and explicit restriction maps to both collections. If a source used a local sign gauge, the overlap witness is the corresponding bit flip; it must commute with sensor kernels and every table restriction. No guessed latent alignment is allowed.

### Exact refinement witnesses

A coarse description attached to bag B is the local refresh-HMM state x_B. The whole-to-local state map is the projection r_B(x)=x_B. For every whole state x,

    r_B# K_whole(x,·) = q delta_(x_B)+(1−q)p_B = K_B(r_B(x),·).

Emission marginalization likewise gives the B readout kernel. Initialization projects pi to p_B. These three identities are an exact strong stochastic simulation witness, proving every finite local history law, not only low-order moment agreement.

In a distributed implementation with replicated separator registers, the invariant state space is

    Z_T={ (z_B)_B : z_B|_(B intersection C)=z_C|_(B intersection C) for all B,C }.

The map x↦(x|B)_B is a bijection from {−1,+1}^V to Z_T, with inverse selecting any occurrence of each named port. For two retained trees T,T', their completed distributions are identical. To prove this, if r has the same bag marginals then E_r log pi_T=E_pi_T log pi_T, since each logarithmic factor is a bag/separator function. Thus KL(r||pi_T)=H(pi_T)−H(r). Substituting r=pi_T' and reversing T,T' forces both nonnegative KL divergences to zero. Therefore the exact common refinement is the same named state x, and the transport is z↦x↦z'. It preserves the one shared refresh event and the one emitted readout per named port; it does not resample copied separator states or duplicate sensor events. This is a graph-isomorphism witness on consistent distributed states, not an assertion that arbitrary quotienting is invertible.

## 5. Causal positive common law and resource ledger

Initialize by one tree-conditional draw from pi_T. Store z_B in each component, with separator copies explicitly charged. At each tick:

1. Each named port has one designated sensor owner; sample its fresh BSC noise once and route the resulting readout to experimental consumers needing it.
2. Draw one common refresh bit F with P(F=1)=1−q; broadcast it along the tree.
3. If F=0, retain every register. If F=1, root draws its new bag, sends new separator values to its children; each child draws new private variables conditional on received separator and forwards its new separators. Commit when that tree traversal finishes.

All random draws are positive local conditional kernels. The common F is not independent per component: making it independent would change cross-scope temporal laws. No common hidden tape is free.

Resources: at most mw persistent binary registers (N independent degrees of freedom, mw−N redundant copies); at most w bits per separator message; O(mw) communicated bits per refresh plus O(m) refresh-broadcast bits; O(m 2^w) table storage; at most w local state bits per component; O(height(T)) synchronous communication rounds per macro-tick (or O(m) sequential steps). The readout fanout cost is sum_B |B| if every component receives every port in its scope. An unbounded-degree tree has unbounded component fanout; use a degree bound as an additional admissibility condition if required, or charge it. The present polynomial tree test does not solve arbitrary degree-constrained spanning-tree variants.

This constructs one common runtime for a selected completion, and exact world-indexed simulations for that completion. It does not imply that one runtime recovers unknown physical variables or implements world-dependent actions for every observationally compatible physical world.

## 6. Finite records and retained uncertainty

For finite records, do not divide point estimates and declare exact architecture/model identification. Build simultaneous confidence intervals for every measured bounded character statistic, with each statistic’s actual sample count. Independent stationary episodes permit Hoeffding and a union bound with heterogeneous counts; dependent within-record observations require a separate mixing argument or use one fixed statistic per independent record. For M statistics and statistic j based on n_j independent bounded [−1,1] observations, radius sqrt(2 log(2M/delta)/n_j) suffices. Covariances must be built from a simultaneous event for their means and pair-products, not treated as raw bounded observations without adjustment.

Retain all q,rho_i,p_B satisfying those intervals, refresh-history membership, positivity margins, and exact separator equalities, together with every accepted tree. This is a polynomial-size explicit constraint family at fixed w, **not a claim that arbitrary real feasibility is polynomial-time**. Every point has the exact operational lift above. A guaranteed compatible empirical lift can be found by convex local-marginal feasibility when q,rho are fixed/calibrated; noisy unknown calibration introduces nonlinear constraints. Do not silently label failure of a local numerical optimizer a proof of emptiness.

If two retained points share a tree, couple refresh coins, sensor noises, root draws, and conditional draws. If their respective q difference is epsilon_q, sensor total-variation differences sum to epsilon_s, and the sum of worst-case TV differences of root and child conditional sampling kernels is epsilon_p, then H observed ticks have TV distance at most

    min(1, epsilon_p + (H−1)(epsilon_q+epsilon_p) + H epsilon_s).

Initialization costs epsilon_p. At subsequent updates, conditional on no earlier mismatch, a union bound over common local draws gives epsilon_q+epsilon_p; emission draws cost epsilon_s. This is finite-horizon confidence propagation, not an infinite-time uniform bound. Strict separator-mass margins make conditional-table perturbations stable.

## 7. Growing interaction and architectural nonuniqueness

For growing connected interaction, take the overlapping bags B_j={j,j+1}, j=1,...,N−1, and pi proportional to exp(sum_j J_j x_j x_(j+1)+sum_i h_i x_i), with bounded finite nonzero J_j. This is strictly positive, interactions span an arbitrarily long chain, w=2, and partial noisy histories do not reveal states. The refresh law preserves every selected marginal automatically. The algorithm recovers local sensor parameters, bag marginals, and the chain junction architecture without constructing the global positive frame. Its global refresh is a deliberately charged synchronization mechanism, not nearest-neighbor continuous-time dynamics.

For unbounded architectural ambiguity at fixed width, use B_j={0,j}, j=1,...,m, with pi(x)=p_0(x_0) product_j p_j(x_j|x_0), all tables strictly positive and each child genuinely dependent on x_0. Every spanning tree on the m bags has running intersection (all intersections are {0}), giving m^(m−2) retained wiring trees, all with the same exact law and bounded one-bit separators. A balanced tree, path, or star are alternative physical message architectures with different latency/fanout. No enumeration is required. The fine named state and separator-alias witness allow transport between them exactly. This shows why a unique architecture must not be inferred even when the Markov completion happens to be unique.

## 8. What this does not settle

The supplied experimental cover is not a supplied true component partition, but its scope-residency contract is significant. If arbitrary readout scopes may be served remotely, failure of the junction-tree test says nothing decisive. Missing experiments can admit non-Markov wholes, different hidden-state dimensions, and world-dependent causal semantics. The theorem neither identifies those alternatives exhaustively nor guarantees one bounded runtime for them all. It is a substantive conditional joint-lift theorem with actual positive realizations and polynomial discrete architecture discovery, not the full unrestricted architectural-ambiguity solution.


## Auxiliary event-record qualification

Tree-to-tree equivalence above is an exact stochastic state/observation-law equivalence. It is not an isomorphism of arbitrary implementation random-draw transcripts: root/child conditional draws differ across trees. For an event-level common witness, choose the semantic event record (F,x,x',one owned sensor-noise value per named port); both implementations map to it by forgetting local sampling auxiliaries. Any calculus that insists on retaining individual RNG records needs an explicit additional stochastic refinement, not the assertion that these transcripts are bijective.

# 9. Main-route discovery lemma: unknown sensor frame from partial pair histories

This lemma applies to genuine locally coupled dynamics, without common refresh or latent reset. Let X_t be a stationary N-vector of ±1 spins satisfying

    E[X_(t+1)−mu | X_t] = A(X_t−mu),

where A is unknown and invertible, and C=Cov(X_t) is positive definite. This conditional-mean identity holds for the noisy-copy family: site i independently chooses predecessor P(i) with probability q1, predecessor P²(i) with q2, or fresh innovation with the remaining probability; innovations may have simultaneous cross-site dependence. Then A=q1 P+q2 P². Independence of site choice from the state is required; innovations are independent of the past.

Observations are Y_i,t=X_i,t D_i,t with independent fresh noise signs of unknown means rho_i in (0,1), independent of X. Let D=diag(rho_i), observed mean a=E Y, and define Γ_l=Cov(Y_(t+l),Y_t), l=1,2. These entries can be learned from separate fixed pair-port stationary histories with nonuniform sample counts. No episode must read all N ports. Order the lag matrix consistently: future port indexes its row.

**Constructive calibration theorem.** Exact observed a,Γ_1,Γ_2 determine rho,mu,C,A by

    B = Γ_2 Γ_1^(−1),
    S = B^(−1) Γ_1,
    rho_i = sqrt(S_ii+a_i²),
    D=diag(rho), mu=D^(−1)a,
    C=D^(−1)S D^(−1),
    A=D^(−1)B D.

**Proof.** Iterated conditional expectation gives Cov(X_(t+l),X_t)=A^l C. Fresh sensor noises at distinct times imply Γ_l=D A^l C D. Invertibility of D,A,C gives B=DAD^(−1), and S=DCD. Since X_i²=1, C_ii=1−mu_i². Therefore S_ii+a_i²=rho_i²(1−mu_i²)+rho_i²mu_i²=rho_i². The remaining formulas follow. No global hidden-state table, hidden coordinate mixing frame, full-history alignment, or positive cone is provided. The local hidden spin meaning is determined only up to the declared positive-noise sign convention. QED.

**Compatibility checks.** Reject if any required inverse fails, S is not symmetric positive definite, recovered rho is outside (0,1), or recovered A is outside the model's sparse nonnegative copy grammar. These are necessary checks; they are not a universal model-membership theorem for arbitrary histories. Actual whole-history prediction relies on the copy-family premise and its independently reconstructed innovation laws.

**Nontrivial conditioning.** If P is any permutation and q1>q2>0, then

    ||(q1 P+q2 P²)v|| >= (q1−q2)||v||,

so A is uniformly invertible independently of N. If rho_i>=rho0 and C>=c0 I, then σ_min(Γ_1)>=rho0²(q1−q2)c0. This converts matrix inversion into a quantitatively stable operation. An entrywise moment error ε has operator norm at most Nε; selecting accuracy o(1/N) yields polynomial sampling costs under fixed margins, rather than an uncharged global inversion oracle. Direct matrix work costs O(N³), memory O(N²), and each measured statistic involves at most two ports at two sampled times. The required temporal lag is two.

**What this does and does not discover.** The recovered A exposes actual locally coupled transition edges from partial noisy readouts. It need not identify the higher-order cross-site innovation law. Different positive innovation laws with the same relevant partial-stream laws can survive this exact calibration and remain nongauge physical alternatives. Thus recovering this local sensor frame does not first resolve the whole architecture: the innovation-coupling architecture remains uncertain and needs a separate positive-extension/joint-lift theorem. This lemma supplies that theorem's non-supplied local-law/frame input, not its complete proof.

## 10. No-reset exact stationary initialization for the noisy-copy main family

Write q=q1+q2<1. Use a graphical construction indexed by named site/time events: each update chooses one predecessor with total probability q, otherwise chooses its same-time fresh innovation. Innovation triples are sampled jointly, independently across triples/times; choices are independent of all innovations and the past.

For any current spin, its backward ancestry is a single path, not a branching tree: at each step it either follows one predecessor or terminates at a fresh innovation. Its probability of surviving t past steps is q^t. Coalescing ancestral paths use the same cached named site/time choice. If multiple terminal requests belong to one innovation-triple/time event, sample that entire triple once and cache it; never independently sample partner coordinates.

To generate stationary X_0 exactly, explore all N current ancestries until they terminate, obtain their innovation spin values, and copy these forward. Almost-sure termination follows from a union bound Nq^t. The resulting law is time-translation invariant because the underlying two-sided event field is iid in time. It satisfies the prescribed update rule and therefore is stationary. The same coupling shows uniqueness: two initial states driven by the same events agree at time t unless one of the N current ancestries reaches the initial boundary, so

    sup_(x,x') TV(K^t(x,·),K^t(x',·)) <= min(1,Nq^t).

In particular the distance to the unique stationary law obeys the same bound. This is local innovation regeneration, not a simultaneous whole-system reset.

The sum of ancestry lengths has expectation at most N/(1−q), before taking coalescence savings; sampling full innovation triples multiplies terminal storage by at most three. Maximum ancestry depth T satisfies P(T>t)<=min(1,Nq^t), hence E T=O(1+log(N)/|log q|+1/(1−q)). Exact initialization has unbounded but exponentially tailed random running time and finite polynomial expectation; do not call it a bounded-time deterministic primitive. Runtime persistent state after initialization is still N spin bits; transient initialization caches are separately charged.

For finite-data concentration from one long trajectory, select stationary windows separated by g unobserved updates, with Nq^g at most delta/(2K), where K is the number of retained windows. Sequential coupling then makes those windows jointly equal to independent stationary windows with failure probability at most delta/2; Hoeffding over bounded measured characters supplies the remaining delta/2. A burn-in from arbitrary initialization adds its own Nq^b budget. Nonuniform per-statistic sample counts and distinct view histories must use their actual K_j and the corresponding confidence allocation; unsynchronized records never create additional same-time cross-view moments.

# 11. Persistent higher-order innovation interface: bounded temporal witness

This extends the independently developed copy-ring family. Each innovation triad b has an independent hidden persistent spin H_b,t, with fair stationary law and E[H_b,t H_b,t+ell]=lambda^ell, 0<lambda<1. Conditional on the entire H path, innovation triads are independent across times/triads, with table

    p_(theta(H))(e)=p_base(e)+(theta0+d H) product_i e_i.

Choose theta0±d strictly within the table’s positivity interval. Every one- and two-coordinate marginal is independent of H, since summing the parity term over an omitted spin gives zero. Therefore, for every fixed pair of rings, its entire innovation path law is the same iid pair-projection law as under d=0. Its entire hidden/readout history law is consequently unchanged. This is persistent, nongauge dynamical architecture ambiguity, not just an unknown static coupling coefficient. The extra interface stores one bit per triad and feeds only that triad's innovation sampler.

Let r=1−q1−q2 and mu_i be the stationary innovation/site means. For triad sites i, define

    zeta_i,t = X_i,t+1 − q1 X_P(i),t − q2 X_P²(i),t − r mu_i,
    R_b,t = product_(i in b) zeta_i,t.

Let kappa(H)=E[product_(i in b)(E_i,t−mu_i) | H_b,t=H]. Summing against the signed parity perturbation cancels all lower-degree terms, so

    kappa(H)=kappa_base+8theta0+8dH.

Condition on X_t and E_t. Site choices are independent across the three triad sites, and each conditional residual mean is r(E_i,t−mu_i). Hence E[R_b,t|X_t,E_t]=r³ product_i(E_i,t−mu_i). Conditional on the complete H path, fresh innovations are independent of earlier state/choice history. Thus

    E[R_b,t | past, H_path]=r³ kappa(H_b,t).

For ell>=1, R_b,t is in the past of R_b,t+ell. Iterated conditioning first at the later time, then at the earlier time gives

    Cov(R_b,t,R_b,t+ell)=r^6 Cov(kappa(H_b,t),kappa(H_b,t+ell))
                         =64 r^6 d² lambda^ell.

The d=0 completion has zero such covariance; the d≠0 persistent completion has positive covariance. This is an explicit observational distinction once a sufficiently rich probe is authorized, although all existing fixed-pair histories agree exactly. It also proves that the added hidden interface has a genuine persistent effect rather than being a redundant fresh sampler.

Each R uses three future and at most six past spin locations. An adjacent R product uses at most eighteen site/time locations over three times. After expanding and reducing X_i,t²=1, every term is a bounded-degree spin monomial. Its noisy-readout expectation can be recovered by dividing the corresponding observed monomial by the product of its calibrated rho values, with one factor per distinct site/time location. This is a fixed-width temporal probe independent of the number of ring sites. It is not available from independently gathered pair histories and must not be fabricated by multiplying unrelated episodes.

## Persistent-interface initialization caveat and repair

Section 10's iid-time innovation sampling applies to the base family. For this H-extended family, first explore the copy ancestries and obtain their earliest time −T; these choices are independent of H. Draw each required H_b,−T from its fair stationary law and evolve its Markov chain through the latest terminal time (and to time zero to initialize the persistent runtime). Sample terminal innovation triples jointly conditional on their cached H_b,t. Because T is independent of H and each chain starts in stationarity, this samples exactly the correct stationary joint law of (X_0,H_0). Work adds at most O(m(T+1)) two-state transitions, with finite polynomial expectation. One cannot independently resample H at separate terminal times or retain the iid-innovation mixing estimate for the full state without amendment; full-state mixing also charges H's mixing time.
