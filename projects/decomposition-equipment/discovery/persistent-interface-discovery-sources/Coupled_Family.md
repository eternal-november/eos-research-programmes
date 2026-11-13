# A locally learnable delayed, mixed-readout benchmark with crossing region systems

28 October 2026. Constructive proposal, not a physically validated thermal/motion model and not a claim of a new general ICA theorem.

## 1. What this adds, and what it does not

The useful combined result is **unknown-frame and unknown-region recovery from one noisy nonreset trajectory, followed by discovery of exact compressed persistent influence transducers for crossing region systems**. The statistical part is a restricted finite-field autoregressive/ICA construction; it is not itself a new general decomposition principle. The interface part returns noncoordinate parity quotients with a canonical history-equivalence and a matching deterministic influence-preserving memory bound. These are meaningful positive results in the *same* growing interacting family.

It does not recover arbitrary physically intrinsic boundaries, does not prove optimality among all stochastic observational realizations, and does not establish any advantage over a baseline allowed to perform the same identification and linear systems minimization. That comparison remains open. In particular, arbitrary cuts always admit a positive implementation; our two preferred region systems are the uniquely finest invariant partitions of two distinguished mechanism/lag classes, not the uniquely true decomposition of an unrestricted world.

## 2. Hidden dynamics and the actual supplied data

All arithmetic below is over F2 unless probabilities or logarithms are indicated. There are n hidden binary modes, fixed maximum delay L, and a fixed number a of action bits:

    X_t = sum_{ell=1}^L A_ell X_{t-ell} + B U_t + E_t.

The innovations E_{t,i} are mutually independent over coordinates and time, with unknown p_i satisfying

    0 < p_min <= p_i <= p_max < 1/2.

Rows of the concatenated matrices [A_1 ... A_L] have at most d nonzeros. Matrices and innovation probabilities are unknown. Actions during discovery are independent uniform U_t in F2^a. The realized initial latent history is unknown, not set or revealed. For the clean end-to-end subclass, impose A_L invertible and take the environment already in its stationary law: the lag-history vector is uniform on F2^(nL). This is a known nonrevealing distribution, not observed state or reset access. Indeed the deterministic companion update is invertible, so every additive-innovation update preserves uniform measure; contraction below makes this stationary law unique. An arbitrary unknown initial distribution is allowed for transition discovery after burn-in, but exact reconstruction of that initial distribution is not claimed. The model also supports other observable-history action policies once its generative law is identified.

The learner sees only actions and

    Y_t = M X_t + N_t,

where N has independent known Bernoulli(eta) entries, 0<eta<1/2. M is unknown and invertible. Up to unknown permutations of its rows and columns, M is block diagonal with blocks of size at most q. Neither these small sensor-mixing blocks nor the much larger sought regions are supplied. These are distinct things. This is a substantive bounded-local-mixing restriction, not arbitrary unknown observation maps. Every readout is noisy; no individual hidden variable or joint hidden state is revealed. A single observation y has positive probability under every hidden x. No operation names or reports a region, and no local positive latent frame or local kernel is given.

The known scalar noise level is a calibration assumption. Unknown sensor noise is not silently covered by the theorem. Likewise, binary modes are a coarse hidden-state benchmark, not a model of continuous temperature or mechanical position.

Write W=MX, C_ell=M A_ell M^{-1}, F=MB, and Z=ME. Each raw recurrence row has at most r=q^2 d past-coordinate terms. Thus the latent frame can be unknown while a sparse search in raw coordinates remains possible.

## 3. Population discovery theorem

**Theorem A.** For fixed q,d,L,a and the stated strict bias/noise bounds, the stationary action/readout law identifies (M,{A_ell},B,{p_i}) up to a common permutation of latent coordinates. It can be reconstructed using polynomially many bounded-order observable parity moments and polynomial arithmetic in n. No global hidden-state table or observation alphabet of size 2^n is enumerated.

### A1. Recover the raw delayed recurrence

For each output i enumerate parity predictors using at most r past readout coordinates from the last L times, together with any subset of the a current action bits. First consider their uncorrupted counterparts. The true predictor has residual Z_{t,i}, with positive mean in sign coordinates

    lambda_i = E[(-1)^{Z_{t,i}}] >= (1-2p_max)^q.

For a wrong predictor, its residual is Z_{t,i} plus a nonzero parity of past W and/or U_t. Z_t is independent of all those quantities. If the current-action parity is nonzero, its expectation is zero. Otherwise take the most recent time with a nonzero coefficient in that past parity. Because M is invertible, the coefficient on X at that time is nonzero. Conditional on everything earlier, at least one independent innovation at that time occurs in the parity. Its conditional absolute sign mean is at most 1-2p_min. Consequently every wrong predictor has mean at most lambda_i(1-2p_min). The true predictor uniquely maximizes the residual sign mean, with a uniform positive gap at least 2p_min(1-2p_max)^q.

For any parity on k distinct observed (time,coordinate) locations, its expectation equals the corresponding W parity expectation times (1-2eta)^k. Dividing by this known factor supplies an unbiased moment estimate. Here k<=r+1. This recovers every C_ell and F by sparse enumeration, without observing any W or Z samples.

### A2. Recover the unknown latent frame from innovations

Once C and F are known, each characteristic moment

    phi(s)=E[(-1)^{s^T Z_t}]

is a bounded-order parity moment of W_t and its recent history, hence is obtainable from Y by the same correction. Do not claim that subtracting the noisy recurrence produces an independently noisy Z sample: it generally does not. The moment calculation is the valid operation.

For raw coordinates i,j,

    phi(e_i+e_j)/(phi(e_i)phi(e_j))
      = product_{k: M_ik=M_jk=1} (1-2p_k)^(-2).

This ratio exceeds one exactly when the two rows share an innovation column. Build that overlap graph. Its connected components have size at most q and separate the innovation mixing into its actual indecomposable blocks. (An originally declared mixing block may split further; that is harmless.) Invertibility implies that the number of latent columns in each such component equals the number of rows.

Within each component J, obtain phi(s) for its 2^{|J|} subsets. All are strictly positive. Put g(s)=log phi(s). If m_k is a column of M in that block and alpha_k=1-2p_k, then

    g(s) = sum_k log(alpha_k) [s^T m_k=1].

The normalized Walsh coefficient at a nonzero vector v is

    g_hat(v) = -log(alpha_k)/2  if v=m_k,
             = 0              otherwise.

Distinct columns follow from invertibility. Thus the positive Walsh coefficients identify precisely the columns of M and their p_k, up to column order. Equal innovation biases cause no extra rotation ambiguity. Invert M blockwise and transport C,F back to recover A,B.

This proves actual frame discovery, rather than assuming the desired positive coordinates and then clustering them. The proof breaks at fair innovations: if p_i=1/2, logarithms or identifying coefficients can disappear.

## 4. A finite-trajectory, polynomial-data version

Impose the explicit high-noise contraction condition

    rho = d(1-2p_min) < 1.

This condition is restrictive but compatible with p_max<1/2. Couple two hidden histories using identical actions and coordinatewise maximal couplings of their next-step conditional Bernoulli laws. A differing parent can affect a conditional output distribution by at most 1-2p_min. Let delta_t=max_i P(X_{t,i} differs from its coupled copy). Row sparsity gives delta_t<=rho max_{1<=ell<=L} delta_{t-ell}. Every L steps, the maximum coordinate-mismatch probability over the history window contracts by rho. Using total expected Hamming distance in this recursion would be wrong without a column-degree bound; the coordinate maximum avoids that error. A union bound gives a coupling/mixing tail of order nL rho^{floor(t/L)} (constants and a one-window offset are immaterial). The observed process inherits this bound.

All needed moments involve at most max(2,q)(r+1) observed bits and a window of length L+1. Their noise-correction norm is bounded by (1-2eta)^(-max(2,q)(r+1)), a constant when the declared structural parameters are fixed. There are n(nL+a)^{O(r)} recurrence candidates, O(n^2) overlap checks, and O(n2^q) block moments. The recurrence gap, row-overlap gap, smallest phi, and nonzero Walsh coefficient all have positive lower bounds depending only on p_min,p_max,q. For example the overlap difference phi(e_i+e_j)-phi(e_i)phi(e_j), when nonzero, is at least

    (1-2p_max)^{2q} ((1-2p_min)^(-2)-1).

Here is an explicit sample schedule. Let epsilon be the required simultaneous corrected-moment accuracy, K the total number of candidate moments (including moments for every possible size-at-most-q mixing block, so post-selection is covered), and delta the failure budget. Put

    B_obs = (1-2eta)^(-max(2,q)(r+1)),
    N = ceil(2 B_obs^2 epsilon^(-2) log(4K/delta)),
    g = L ceil(log(4N nL/delta)/(-log rho)) + L.

Use N disjoint windows of length L+1, leaving g transition steps between consecutive windows. For arbitrary starting state, first burn in g steps; for stationary initialization this is unnecessary. The uniform coupling bound puts these windows within total variation at most N nL rho^(floor((g-L)/L))<=delta/4 of independent stationary windows; initial burn-in costs at most another delta/4. Each corrected parity variable lies in [-B_obs,B_obs], so Hoeffding plus a union bound costs at most 2K exp(-N epsilon^2/(2B_obs^2))<=delta/2. Thus all moments meet their error tolerance with probability at least 1-delta. A sufficient trajectory length is

    T = g + N(g+L+1).

The extra L in g absorbs the window offset in the coupling estimate. A safe bound is K <= 2^a sum_{j=0}^w binomial(n(L+1),j), where w=max(2,q)(r+1): include every parity of that width and every current-action parity, covering selected recurrences as well as selected mixing blocks. This remains polynomial at fixed structural widths. Covering all such moments is a conservative way to avoid dependence from both recurrence and block post-selection; sample splitting is an alternative. This explicit schedule is conservative, not an optimized rate. Computation is polynomial in n with degree depending on r; it is emphatically not practical for large r. As eta or p_max approaches 1/2 the constants diverge. Growing q,d,L is not covered by the fixed-parameter polynomial assertion.

### Stronger nonreset version without high-noise contraction

For the invertible-terminal-coefficient subclass, the restriction rho<1 is unnecessary. Let G be the nL-dimensional companion transition and J insert innovations into its first n coordinates. G is invertible, and the controllability matrix [J,GJ,...,G^(L-1)J] is invertible: its block structure is triangular with identity diagonal. Set alpha_max=1-2p_min<1 and D=nL. On a Fourier character chi_v(z)=(-1)^(v^T z), the Markov operator is

    K chi_v = phi_E(J^T v) chi_(G^T v),

up to a unit-modulus phase for a fixed action; independent exploration actions can only reduce the multiplier. For each nonzero v, controllability guarantees a nonzero J^T(G^T)^j v for some 0<=j<L. That factor's absolute innovation characteristic is at most alpha_max. Since G^T permutes nonzero characters, the L-step operator norm on mean-zero L2(uniform) is at most alpha_max. The adjoint has the same norm. Therefore, from every initial distribution,

    TV(Law(z_t), Uniform) <= (1/2) sqrt(2^D-1)
                              alpha_max^(floor(t/L)).

This also bounds the uniform mixing coefficient. Although the displayed prefactor is exponential, its logarithm determines spacing, giving polynomial time. In the preceding explicit sampling schedule retain N,B_obs,K and replace g by

    g_F = L ceil(((D/2)log 2 + log(4N/delta)) /
                 (-log alpha_max)) + L.

Then all coupling and Hoeffding guarantees still hold, without any relation between d and p_min. Total length is g_F+N(g_F+L+1). This costs O(nL^2) spacing at fixed accuracy rather than the optional contraction proof's O(log n) spacing, but permits moderate innovation noise. The uniform stationary initializer remains exactly valid. The Fourier proof is for independent discovery actions (or a fixed external action sequence); it does not claim stationary mixing under arbitrary feedback policies.

### Continuous-kernel uncertainty and policy-level use

Finite data recover the discrete matrices/frame on the support-separation event; they do **not** recover real-valued p_i exactly. If each local characteristic moment is estimated to epsilon_m<=phi_min/2, where phi_min=(1-2p_max)^q, then the log moment errors are at most 2 epsilon_m/phi_min. Normalized Walsh averaging has operator norm one in the sup norm. Since p=(1-exp(-2g_hat))/2 has derivative at most one for g_hat>=0, appropriately clipped estimates satisfy |p_i-p'_i|<=2 epsilon_m/phi_min=:epsilon_p. The same concentration calculation applies at this finer accuracy.

Initialize the true model P and the clipped estimator P' with the same uniform lag history in the invertible-terminal-coefficient subclass, use identical observation noises, and maximally couple corresponding innovations. Until the first innovation mismatch, all hidden states and readouts agree. Any controller using only its observation/action history can choose coupled identical actions while histories agree. A union bound therefore gives, simultaneously for all such H-step policies (including a policy selected after learning),

    TV(Law_P(action/readout transcript), Law_P'(transcript))
      <= min(1, n H epsilon_p).

This is a finite-horizon approximation bound, not exact all-horizon identification from finite data. Achieving a fixed behavioral error for growing n,H requires the corresponding finer moment accuracy and hence additional polynomial samples. Initialization outside the uniform subclass retains the qualification already stated.

## 5. Unknown crossing region systems

Distinguish two mechanism classes by lag 1 and lag 2. Define P as the connected components of the *undirected support* of A_1, and Q as those of A_2. These are exactly the finest partitions for which the respective matrices are block diagonal. SCCs are not an interchangeable definition here. The complete dynamics need not respect either partition: all other lags become cross-region modeled influences. The classes could instead be physically justified distinct known mechanism bands, but their interpretation must be an explicit modeling assumption.

The recovered matrices discover both partitions up to the same latent permutation. P and Q may cross. Each is a valid whole-system implementation only when its omitted cross-class dependencies are implemented as channels; neither is an autonomous decomposition merely because one lag matrix is block diagonal.

### Explicit growing, bidirectionally interacting instance

Take an m by m toroidal array of sites, m>=3, with two hidden bits per site, so n=2m^2. This geometry is a construction witness, not a supplied partition. Let

    R = [[1,1],[0,0]],       S = [[0,1],[1,0]].

At lag 1, put S on each site's diagonal and R from each horizontal neighbor to the site. At lag 2, put S on each site's diagonal and R from each vertical neighbor to the site. Set L=3 and A_3=I, adding only local delay-3 persistence. This invertible terminal coefficient gives the uniform stationary history law described above without adding cross-region ports. Independent nondegenerate innovations drive every bit. The maximum row parent count over all lags is 11, so p_min>.455 (for example .46) and p_max<.5 ensure contraction.

Then P consists of rows of sites and Q consists of columns of sites. Each row and column region has 2m hidden bits. Every row/column intersection has two bits, and neither partition refines the other. No single laminar tree contains all these regions. Horizontally and vertically, influence goes in both directions. S prevents the second local coordinate from being merely a dead innovation sink. This is a dynamically interacting stochastic system, not a product of static latent labels.

The thermal/motion interpretation is only motivational: a mechanism with one spatial extent and response time can overlap another with different extent and time. The algebra does not establish that lag 1 is motion or lag 2 is heat, and this particular torus is not an empirical robot model.

### Bounded-region variant (if per-module width, not just local degree, must be fixed)

Use k two-bit sites in a chain. At lag 1 put S locally and bidirectional R on the matching edges (1,2),(3,4),...; at lag 2 put S locally and bidirectional R on the shifted matching (2,3),(4,5),...; retain A_3=I. The union is a connected interacting chain. P and Q are recovered matching blocks (plus endpoint singletons), each containing at most four latent bits. Interior blocks cross in two-bit site intersections and neither family is laminar with the other. The maximum row degree over all lags is seven, so the same contraction assumption is easier to satisfy. This gives a growing number of bounded-width modules with bounded-degree, bounded-delay, bounded-mixing observations, not growing hidden local state spaces. For a two-site interior P block both of whose sites have outgoing shifted-match edges, D_2 has rank two and its standalone interface has four persistent bits; the corresponding Q interface has rank-two D_1 and two persistent bits. Thus strict parity compression survives the bounded-width variant. The torus variant instead demonstrates scaling of compressed interfaces for growing physical regions.

## 6. Discovered persistent interfaces: a separate exact theorem

Fix any recovered region S and write its outgoing influence coefficient matrices as

    D_ell = A_ell[S^c,S].

D_ell stacks **all** outside recipients. This permits one shared sender interface; per-recipient messages are projections. Do not sum independently minimized recipient Hankel ranks and call that the joint memory optimum. Its contribution to outside updates is the stream filter

    v_t = sum_{ell=1}^L D_ell x_{S,t-ell}.

These are **modeled internal signals**, not controller observations. A controller still receives only Y and its own action history. The simulator may sample its latent modes and communicate v among internal modules; that does not make latent modes available to a deployed controller.

Form the finite block Hankel matrix H_D with blocks (H_D)_{ij}=D_{i+j+1} for i,j=0,...,L-1, with D_ell=0 beyond L. Consider a deterministic transducer which reads x_{S,t} once per tick, has no other historical access, and must produce v_t exactly for every source stream, with output-before-current-input timing.

**Theorem B.** The coarsest exact history interface has 2^h states, where h=rank_F2 H_D. It admits a linear realization with h persistent bits. Every deterministic transducer satisfying the same stream contract needs at least h bits, even if its state and update are nonlinear.

**Proof.** The last L source values form a vector z. With all future source values set to zero, the complete residual future output sequence is H_D z. Two source histories are equivalent under every common continuation exactly when these residual future sequences agree: future inputs contribute identically by linearity. There are exactly 2^h equivalence classes, all represented by histories. Reading a new source vector induces a well-defined transition on the quotient, and the first residual output is a well-defined readout. Choosing a basis for the image gives an h-bit linear realization. Distinct quotient values have a distinguishing future output, hence cannot share the state of any exact deterministic transducer. Full-support innovations imply all finite source histories have positive probability in this model, so unreachable histories cannot remove classes. QED.

This quotient is canonically defined by future influence equivalence; coordinates on it remain gauge-dependent. It can be calculated in polynomial time by linear algebra after discovery. It is not a theorem of minimum **stochastic observational** hidden-state dimension. It is also not automatically an additive lower bound on component memory plus interface memory: shared registers must be counted once, and giving a source free historical access invalidates the standalone-transducer bound. In particular A_3=I already makes the local generator retain past state. It may compute a delayed outgoing parity from that storage at send time, with zero extra interface registers. Alternatively it can stream current parities into a standalone delayed channel, paying that channel's Hankel memory. These are distinct permitted placements if no physical timing constraint rules one out. An observed autoregressive lag is not evidence of physical propagation delay. The 2m versus m interface comparison is for the declared stream-input contract, not minimum total physical architecture memory across all retimings.

### Strict compression and persistence in the same growing instance

For a row region, D_1=0. The outgoing D_2 sends each site's parity x_1+x_2 to both neighboring rows. It has rank m although the source has 2m modes. Thus the port sends m independent parity bits per output tick, rather than all 2m source bits, and H_D has rank 2m. Its standalone exact influence generator needs 2m persistent bits. This is a genuine delayed, noncoordinate, rank-deficient interface with bidirectional use across the row network.

For a column region, D_2=0 and D_1 has rank m. Its exact persistent interface has m bits. Thus the two crossing region implementations have different interface-storage profiles on precisely the same learned system. A fanout value is produced once and reused at its two consumers; treating occurrences as independent fresh noises would change the law.

For communication, let k=rank [D_1 ... D_L]. The current influence v_t lies in a 2^k-element image and can be sent losslessly in k bits. That is a matching alphabet lower bound for a receiver required to decode v_t from the current message alone. It is **not** a general network communication lower bound when the receiver has correlated side information or persistent shared state. More elaborate state placement may improve communication and must account for that memory explicitly.

## 7. Positive assembly and ambiguity

For either recovered partition, each module stores its local lag history, consumes the incoming influence sums, samples its independent local innovation, and applies the learned local recurrence. Interface quotient transducers reproduce the outgoing sums exactly. Induction over time shows pathwise agreement with the centralized hidden recurrence when initialized from the same joint latent-history distribution and coupled to the same innovations. Implement the original mixed noisy emission channel as a separately charged sensor layer: each raw sensor reads at most q current latent coordinates, computes their parity, and adds its noise. There are O(nq) coordinate-to-sensor wires with bounded fan-in; sensor wires crossing a chosen region boundary must be included in that implementation's ledger. A global uncharged decoder is not permitted. The Hankel bounds above cover dynamic influence ports only, not this additional sensing communication. This yields the same action/readout law for every controller policy based only on permitted observations, not just the discovery policy. Arbitrary correlated initial histories must be represented consistently; initializing all modules independently is generally wrong. In the invertible-terminal-coefficient subclass, exact initialization is simply a jointly sampled uniform nL-bit lag history, and each quotient interface is initialized from that same history. This costs O(nL) random bits and avoids an unproved exact stationary-sampling algorithm. With arbitrary unknown nonstationary initialization, only transitions and asymptotic stationary behavior are reconstructed; the theorem does not recover potentially exponentially complex initial correlations.

There remain genuine obstructions:

* Without the lag/mechanism distinction or a resource objective, the data do not privilege P versus Q versus a merged region: all implement the same law.
* Without a declared stream-interface contract, the Hankel theorem cannot be advertised as an architecture-independent physical memory lower bound.
* If innovation bias is fair, ICA identifiability can fail. If observations become fair, all dynamical information disappears.
* If sparse bounded sensor mixing is removed, sparse raw recurrence enumeration need not remain polynomial.
* No observation-only test can identify unused internal channel implementations beyond their influence equivalence; a channel can carry extra ignored information without changing observable laws.
* No physical controller gains access to the discovered latent parities merely because an internal simulator uses them.

## 8. Full global predictive rank despite polynomial local discovery

In the invertible-terminal stationary subclass, the exact past/future observation Hankel rank is 2^(nL). Here is a direct finite-block lower bound. Let h=(X_0,...,X_(1-L)) be the uniform boundary register, and fix the next L actions to zero. The preceding L readouts are an invertible blockwise-M image of h plus independent sensor noise. Their conditional-law matrix E, with columns indexed by h, is square and invertible: binary convolution is diagonalized by Walsh characters, and every sensor-noise characteristic is nonzero.

The next L hidden vectors are O h plus a linear image of fresh innovations. The map O is invertible whenever A_L is invertible. To see this, in the noiseless zero-input recurrence recover X_0 from the equation for X_L using its A_L coefficient and known X_1,...,X_L; then recover X_(-1) from the equation for X_(L-1), and continue backwards. Thus the next L readouts are an invertible linear image of h plus additive noise independent of h. Every characteristic of this additive noise is a product of positive innovation/sensor biases, hence is nonzero. Their conditional-law matrix F is therefore also invertible.

Past sensor noises and future innovation/sensor noises are independent given h. The square joint past/future-readout matrix is consequently

    E diag(2^(-nL)) F^T,

which has rank 2^(nL). Under random exploration, conditioning on the future zero-action word only contributes its known positive probability. Marginalizing past action symbols is a linear combination of the corresponding history rows, so cannot create this rank from a lower-rank controlled history/test matrix. Conversely the nL-bit hidden register supplies the matching upper bound. Therefore the controlled predictive rank equals 2^(nL).

Any exact finite-state stochastic presentation in which state separates past and future needs at least 2^(nL) states, even though the discovered sparse, factored presentation and its certificates have polynomial description and checking cost. This is a genuine cardinality/rank statement; it does not prove an exponential sample or computation lower bound for the strongest baseline, which may use the same compact factorization. It also does not establish minimum extra interface registers: total predictive memory and placement-specific boundary memory are different questions.

## 9. Easiest fair baseline and the honest next theorem

The strongest easy baseline runs the same sparse parity regression and finite-field ICA, forms A_ell, and applies standard finite linear-system minimization to each desired cut. It obtains the above positive assemblies and canonical deterministic history quotients without a specialized structural calculus. Exhaustive global HMM learning is unnecessary and is not the right comparator.

Consequently this is a useful hard-but-attainable **benchmark and composed theorem**, not a demonstrated structural-theory advantage. A substantive next target is to prove a resource-constrained multi-cut reuse or certification result that this baseline does not already obtain for the same cost: for example, simultaneously updating certificates for overlapping region changes while preserving shared-producer occurrences and avoiding re-learning, with a clearly specified cost model. Unknown graph/frame recovery, exact quotient construction, and resource-optimal distributed stochastic control should remain separate claims.

## Deployment and scope clarification

The finite-horizon comparison requires matched deployment initial laws, including after conditioning on training data when a controller is data-selected. A fresh independent common-uniform start is sufficient. Same-run continuation is not automatically a common-uniform start. A certified initial-law TV discrepancy epsilon_0 adds to the innovation mismatch bound, giving min(1, epsilon_0+nH epsilon_p). Physical hazard transfer requires a sound event interpretation or conservative proxy relation; class-relative confidence does not certify the physical world belongs to the class. See `Audit_Scope_Clarifications.md`. The canonical mixing target is the finest indecomposable partition, not an arbitrary assigned coarsening.
