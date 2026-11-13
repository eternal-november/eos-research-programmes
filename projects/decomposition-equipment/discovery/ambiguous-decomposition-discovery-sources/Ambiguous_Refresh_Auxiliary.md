# A biased triangle-tree observation-law fiber

## Result and scope first

There is a growing, connected family in which noisy, fixed-width observation laws discover overlapping components and persistent one-bit separator ports, while exponentially many genuinely different interaction architectures remain observationally indistinguishable. The completion is an explicit junction product with a linear-size sampling implementation, not a global-state enumeration. A width-three simultaneous probe separates the remaining ambiguity. There are strictly positive, biased pair laws that agree on overlaps but have no joint lift.

**Important limit:** the proved temporal law is a common persist-or-refresh clock with a correlated tree-structured refresh draw. It has connected stochastic coupling and persistent shared states, but does **not** establish discovery for unknown neighbor-conditioned transition mechanisms. Consequently this is a nonidentification/lifting stress theorem, not discharge of the full stronger interacting-dynamics target. The shared clock and refresh randomness are explicitly charged below. No physical hardware layout is identified: “architecture” below means the canonical stationary interaction hypergraph and an explicit compatible realization.

## 1. Family, without supplied partition or latent frame

Let G be an unknown labelled graph obtained by gluing m triangles along singleton vertices, with a tree of bags (each new triangle attaches along exactly one existing vertex; no other identifications). It has n=2m+1 named binary readout ports. The triple bags and their singleton separator ports are not supplied. State X has one hidden bit at each port, but no state is accessible. This is an explicit restricted grammar, not unrestricted discovery.

For one triangle b define

    q_theta(x1,x2,x3) = w(x)/95 + theta*(-1)^(x1+x2+x3),
    w(x) = 2^(x1+x2+x3+x1*x2+x1*x3+x2*x3).

The weights by Hamming level are 1, 2, 8, 64, so their total is 95. Use theta_b in [-1/190,1/190], which guarantees strict positivity. Each singleton marginal has p=P(X_i=1)=82/95. Each pair has P(11)=72/95 and covariance c=116/9025. Put v=p(1-p)=1066/9025 and rho=c/v=58/533. The singleton and pair marginals are independent of theta, because summing the signed perturbation over any missing coordinate gives zero.

Choose any bag tree T consistent with the running-intersection property and let s_e be its singleton edge separator. Define

    Q_theta(x) = product_b q_theta_b(x_b) / product_e p_s(x_s),
    p_s(1)=82/95, p_s(0)=13/95.

Leaf elimination proves normalization, strict positivity and the stated bag marginals. This is the constructive lift, not an assertion that arbitrary overlap agreement suffices on cycles.

The uncontrolled transition is

    K_theta(x,x') = (1-r)*1[x'=x] + r*Q_theta(x'),  0<r<1.

Start in the unknown stationary state Q_theta. There is no controllable or revealing reset. Each port emits Y_i=X_i XOR N_i with fresh independent Bernoulli(eta_i) noise, 0<eta_i<1/2. The eta_i may be unknown, but quantitative guarantees require eta_i <= (1-a_min)/2 for declared a_min>0. All finite noisy histories have positive probability; stationary does not mean uniform: biases and persistence make histories strongly nonuniform.

## 2. Exact access contract (essential)

An experiment chooses at most two named ports and receives their noisy trajectory from an independent stationary run. The observer cannot switch masks within a run, join records across runs, observe the refresh clock, inspect the state, or control initialization. Independent runs are an observation-law sampling facility, **not** an action resetting an exposed physical device. If only one switchable physical trajectory is available, this theorem is not its access model.

The mask restriction is indispensable. Successive masks on the same persistent trajectory can collectively acquire triple information; “only two observations per tick” would NOT justify the nonidentifiability claim. An optional stronger experiment in Section 7 permits three simultaneous ports.

## 3. Discovering the overlapping bags from pair observations

First recover each noise attenuation a_i=1-2eta_i from its observed mean:

    E[Y_i]-1/2 = a_i*(p-1/2).

Then recover latent stationary pair correlations by dividing observed covariances by a_i*a_j*v. For distinct vertices u,v,

    Corr(X_u,X_v) = rho^(d_G(u,v)).

Proof: within a bag it is rho. Across a singleton separator S, the two sides are conditionally independent under Q. Binary variables with common marginal p obey E[X_u-p | X_S]=Corr(X_u,X_S)*(X_S-p). Conditional covariance and induction multiply correlations along the unique block path. An edge inside a triangle contributes one factor; its internal alternative two-edge route is not a separator path, and the shortest graph distance is the correct exponent.

Thus adjacency is detected by threshold (rho+rho^2)/2. Every true edge has correlation rho and every nonedge has correlation at most rho^2. Recover triangles as maximal cliques; these are precisely the bags. Shared vertices, and hence persistent separator ports, follow from incidence. No global state frame or permutation of a supplied hidden partition is recovered or needed. Naive work/storage is O(n^2) pair statistics; graph extraction can be polynomial without constructing the 2^n state table.

A finite-sample version needs only uniform error less than (rho-rho^2)/2 in recovered correlations. For independent stationary one-time samples per mask, bounded-variable concentration and the rational estimator above give N=O(a_min^-4 * gap^-2 * log(n/delta)) samples per mask, with constants depending only on fixed p; a sufficiently conservative constant absorbs estimation of a_i. Here gap=rho-rho^2 is fixed. The total access cost is O(n^2*N) emitted pairs, not N observations of the whole system. Streaming counters use O(n^2) words; processing masks serially can reduce counter memory while retaining O(n^2) output graph storage. Reusing a single long trajectory requires a mixing correction; it is not counted as independent data.

## 4. Exact nonidentification from entire pair histories

For every fixed set A of at most two vertices, the projected state itself is Markov with kernel

    K_A(z,z')=(1-r)*1[z'=z]+r*Q_A(z').

Every Q_A is independent of the full theta vector, by Section 3 and fixed binary marginals. Thus the full finite-dimensional noisy process law for each allowed mask is theta-independent, not merely its first two moments. Adaptive selection of the next mask based on previous **independent-run** records also cannot distinguish theta, by induction on the experiments.

These alternatives are not coordinate permutations. For one bag define the canonical three-way loglinear contrast

    L(theta)=sum_x (-1)^|x| * log q_theta(x).

L(0)=0 because log q_0 is a polynomial of degree at most two. Its derivative is sum_x 1/q_theta(x)>0. Hence L(theta) is zero exactly at theta=0. The global log density is the sum of bag log densities minus singleton terms, so each nonzero theta contributes a genuine three-variable interaction on its own bag; other bags cannot cancel it. Choices theta_b in {0,1/380} give 2^m distinct labelled canonical interaction supports, all observationally identical under the allowed access. In particular the all-zero and all-nonzero choices have different counts of triple interactions, so no relabelling can equate them. Their full stationary laws differ and a simultaneous triple probe detects the difference.

This is not a claim that a statistical interaction uniquely locates a hardware component. The discovered triangle-bag decomposition is common to the entire fiber, whereas its internal interaction order is not identified.

## 5. Persistent realization and explicit costs

A compatible realization stores the n=2m+1 unique hidden port bits persistently. Local bag implementations may duplicate separator bits, giving 3m bits of local storage, provided their copies are initialized consistently and kept synchronized. Neither storage nor shared initialization is free.

At each tick one shared Bernoulli(r) refresh flag is generated. On no-refresh ticks all state bits persist. On refresh ticks:

1. Sample the root bag from q_theta_root.
2. In tree order send the freshly sampled singleton separator bit to each child.
3. Sample each child's two new bits from q_theta_child conditioned on that separator.

This uses m-1 one-bit messages per refresh, O(m) bounded-size table accesses and random draws, and depth(T) sequential rounds. The global refresh flag requires either a shared clock/random source declared in the realization type or broadcast (up to m-1 more bits per tick on the tree). The full refresh sampler has O(m) local probability tables; it does not need a 2^n table. Noise draws and observation outputs have their own linear costs when all ports are produced, though each experiment accesses only its selected ports.

The separator is a persistent bit, not just equality of fresh outputs: its same stored value is retained between refreshes and is simultaneously used by incident bags. Independent local refresh clocks generally destroy this path law. This construction certifies existence for every theta in the fiber, not a minimal interface theorem or a universal implementation under arbitrary access restrictions.

## 6. Local agreement is insufficient: a positive biased obstruction

Consider three pair-view proposals with identical singleton marginal P(X_i=1)=0.6. On each pair prescribe

    P00=0.025, P01=P10=0.375, P11=0.225.

Every entry is positive; singleton marginals agree. Each pair has disagreement probability 0.75. But any triple of bits has either zero or two disagreeing unordered pairs. Therefore every joint distribution obeys

    P(X1!=X2)+P(X2!=X3)+P(X1!=X3) <= 2.

The proposed sum is 2.25. No joint stationary distribution, and hence no stationary path lift, exists. Adding the same known invertible binary noise channel to each local proposal does not cure nonliftability relative to that emission model; deconvolution recovers the impossible latent pairs. The 0.25 gap makes this a robust obstruction: if each inferred disagreement has error less than 1/12, the strict violation persists.

For a valid binary triple's fixed pair marginals, the entire signed affine fiber is q_theta=q_0+theta*(-1)^|x|. This follows by successively imposing zero one-coordinate sums on the difference tensor. Nonnegativity reduces to a single interval of eight endpoint bounds, not enumeration of global states. For our specific q_0 the full closed probability interval is [-1/95,2/95]; the theorem deliberately uses a compact interior subinterval. On a triangle tree, choosing one feasible triple completion per bag automatically glues via the explicit product. On a cyclic cover the tree argument does not apply; the displayed obstruction is the smallest such warning.

A crossing implementation that separates two adjacent ports into independently initialized, independently randomized autonomous components cannot realize our observed covariance c>0. It must add shared initialization, shared randomness, communication, or a retained shared interface and charge that resource. This modest obstruction is not a general crossing-memory lower bound.

## 7. Allowed ambiguity-resolving probe

Upgrade the mask facility to allow one simultaneous three-port stationary sample on a discovered bag. With calibrated a_i, the observed parity moment deconvolves:

    E[(-1)^(Y1+Y2+Y3)] / (a1*a2*a3)
       = E_q0[(-1)^(X1+X2+X3)] + 8*theta_b.

Thus one third-order moment identifies theta_b exactly at population level; finite accuracy epsilon in theta requires O((a_min^-6)*epsilon^-2*log(m/delta)) independent samples per bag (plus calibration accuracy). It does not require state access or resetting to a known state. For the discrete alternatives {0,1/380}, the separation is fixed. If theta is arbitrary continuous, finite samples cannot certify theta=0 against arbitrarily small nonzero theta without a declared margin.

## 8. What remains open

The family supplies observation-law discovery of a common persistent decomposition, genuine within-observed nonidentification, an explicit parameterized lift, costs, a local-to-global obstruction and a separating probe. It does not yet supply an ambiguity-sensitive optimal interface budget, nor robust discovery for a locally interacting transition family without a common refresh mechanism. Those are separate obligations, not consequences of this construction.
