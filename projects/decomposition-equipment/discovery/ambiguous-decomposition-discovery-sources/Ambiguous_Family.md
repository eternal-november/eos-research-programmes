# Interacting noisy-voter rings with unresolved innovation architecture

## Useful result first

A growing positive family supports **joint discovery of unknown causal edges and unknown correlated-innovation components from noisy pair trajectory laws**, but retains genuinely distinct three-way innovation mechanisms compatible with every allowed experiment. Dynamics have two local causal inputs, directed feedback cycles, nonuniform histories, and no reset or common refresh clock. A symbolic family of joint lifts has linear-sized local tables and explicit memory/access costs. A bounded-width additional probe identifies the unresolved mechanism. This is not identification up to a coordinate permutation and not enumeration of global states.

The construction is deliberately restricted: three autonomous *causal* layers are statistically coupled by fresh innovation triples. It does not claim nonidentification under arbitrary adaptive switching of observation masks, unknown emission families, or arbitrary coupled transition graphs. “Architecture” means the declared causal dependencies plus canonical interaction order of the innovation sources, not unique physical hardware placement.

## 1. Unobserved model, known grammar, unknown instance

There are n=3m named binary readout ports, m>=5. Their hidden bits X_i are organized into three directed rings of m sites, but their ring membership, cyclic order, and alignment across rings are not supplied. Every site has two distinct causal parents, its first and second predecessor in its ring. Fix unknown q1,q2>0 with q=q1+q2<1; quantitative stability uses a margin q1,q2,r=1-q>=epsilon>0. Each site independently chooses at each tick:

* copy its first parent with probability q1;
* copy its second parent with probability q2;
* emit a fresh innovation E_i with probability r.

Thus X_i(t+1) is the selected value. Selector variables are independent across sites/ticks and of the innovations/history. Innovations are independent across ticks and across m unknown disjoint triples, each triple containing one site from each ring. To make the family simple, align equal positions of the rings into these triples; this is also not supplied.

For one innovation triple b,

    q_theta(x)=2^(x1+x2+x3+x1*x2+x1*x3+x2*x3)/95
                 + theta_b*(-1)^(x1+x2+x3),
    theta_b in [-1/190,1/190].

Weights at Hamming levels 0,1,2,3 are 1,2,8,64, summing to 95 with multiplicities. All entries are positive. Every innovation singleton has

    p=82/95,  v=p(1-p)=1066/9025,

and every within-triple innovation pair has P11=72/95 and covariance

    c=116/9025,  lambda_E=v-c=950/9025.

These quantities do not depend on theta: summation over any missing bit annihilates the signed perturbation. Innovations in different triples have covariance zero. The fixed biased p is part of the family grammar, not a supplied latent frame.

Port i emits Y_i=X_i XOR N_i with independent fresh Bernoulli(eta_i) readout noise, unknown 0<eta_i<1/2. Quantitative claims require a_i=1-2eta_i>=a_min>0. No X, selector, innovation or state reset is accessible. Start in the stationary law. Its existence and uniqueness follow either from strict positivity of the finite transition matrix, or a backward graphical coupling: each single lineage copies one of two ancestors until refresh, and survives t ticks with probability q^t; the probability that any of n lineages survives is at most n*q^t. This argument does not require observing or choosing a reset. All finite noisy histories are positive and the stationary means p are nonuniform.

## 2. Observation contract

Each experiment chooses at most two named ports and receives their noisy trajectory from an independent uncontrolled stationary run. Masks remain fixed within each run; no stitching or cross-run joint samples are allowed. The choice of later experiments may depend on earlier completed experiments. Independent stationary runs are explicitly an observation-law sampling facility, not a known-state initialization action.

This restriction is essential. Two observations per tick with freely switchable masks is a different, potentially separating experiment class.

## 3. Causal and innovation decomposition discovery

Write Z=X-p*1 and let A have q1 and q2 in the two parent columns of each row. Then

    E[Z(t+1) | X(t)] = A*Z(t).

Every stationary singleton has mean p. Let C=E[Z(t)Z(t)^T] and D=E[Z(t+1)Z(t)^T]. Exact pair-view laws supply all entries of these matrices. In particular,

    D=A*C,    A=D*C^{-1}.

The matrix C is uniformly positive definite:

    C >= r*lambda_E*I.

Proof: condition on the previous state and all selectors. The fresh subset of each innovation triple has covariance a principal submatrix of the matrix with diagonal v and off-diagonal c, hence at least lambda_E times the identity on that subset. Conditional output covariance is therefore at least lambda_E on each freshly selected coordinate. Average selectors and apply total covariance; each coordinate refreshes with probability r. This proves the bound without a global stationary table.

Readout calibration is also observable because p differs from 1/2:

    a_i=(E[Y_i]-1/2)/(p-1/2).

For i!=j, divide the observed same-time covariance by a_i*a_j to obtain C_ij; set C_ii=v. Divide each lagged covariance (including i=j) by a_i*a_j to obtain D_ij. Thus neither true partition nor noiseless state access is being smuggled into the regression.

The nonzero entries of A recover both causal parents and their probabilities, and its strongly connected components recover the three rings. Distinguishing the first from second predecessor requires q1!=q2 or graph structure; the theorem only needs the recovered weighted causal graph, so equal weights cause no problem.

Now form R=C-A*C*A^T. For distinct sites i,j,

    R_ij = r^2*c, if i,j share an innovation triple;
           0, otherwise.

Proof: conditional on X, selectors at distinct sites are independent. The only covariance of their outputs is the event both select fresh innovations, of probability r^2, times Cov(E_i,E_j). Conditional means are the corresponding rows of A*Z. Total covariance gives the formula. Diagonal entries need not obey this formula and are not used.

Consequently the graph of nonzero off-diagonal entries of R is exactly m disjoint triangles. It discovers the unknown innovation-source components and their correspondence across the causal layers. This is a second decomposition, not the same as the three dynamic components. The recovered causal edges identify persistent one-bit input ports between site mechanisms; each innovation triangle is a distinct fresh shared-source interface.

## 4. Genuine architecture ambiguity survives all allowed histories

Fix A, alignment and readout kernels. Any two observed ports lie in at most two causal rings. The entire state evolution of those one or two rings is causally closed. Its innovations have exactly the same joint law for every theta vector, because each innovation triple contributes at most two bits and all such marginals are fixed. Selectors and emissions are also identical. Uniqueness of the stationary law for this closed process implies that its complete stationary trajectory law is theta-independent. Hence every allowed pair experiment, including adaptively selected independent-run experiments, is exactly unable to distinguish theta.

The alternatives are genuine and affect the observed variables under stronger probes. For each innovation source define

    L(theta)=sum_x (-1)^|x|*log q_theta(x).

L(0)=0 because the base log density is linear plus pair terms. L'(theta)=sum_x 1/q_theta(x)>0, so theta=0 is the unique absence of a canonical triple interaction. The choices theta_b in {0,1/380} yield 2^m different labelled interaction supports. The all-zero versus all-nonzero cases have different counts of ternary interactions and therefore are not related by any coordinate permutation. Their full transition kernels differ: condition on a fixed previous global state; the joint output third-order cumulant on an innovation triple contains r^3 times the innovation third cumulant, which changes with theta. No invisible extra state is appended.

One must not infer from this that the innovation triples are physically located in one particular device. The theorem distinguishes canonical stochastic mechanisms and supplies realizations, not unique hardware inference.

## 5. Symbolic joint lift, persistent interfaces and costs

The discovery output is (A, innovation triples, readout kernels, theta interval per triple), not an arbitrary chosen unique architecture. For every vector theta in the interval there is an explicit joint implementation:

1. Store one bit per site, n persistent bits total.
2. Generate one independent selector per site per tick.
3. Each triple source samples one tuple from its eight-entry q_theta table, independently across sources and ticks.
4. Each site reads its selected parent bit or its assigned fresh innovation bit, then synchronously updates its stored bit.
5. Generate independent readout noises.

This uses O(n) local table storage, n persistent state bits, at most 2n potential one-bit parent accesses per tick (n selected accesses suffice if selection is local), and n fresh innovation outputs per tick. If the source and receiving sites are physically separated, transmitting those outputs costs up to three bits per innovation source per tick; the correlated source and selector entropy are not free. No shared global refresh coin or global-state draw is used. Parallel synchronous updates require the ordinary declared tick boundary; double-buffering uses 2n state bits if overwrite-safe hardware is unavailable. No all-time history is retained in place of charged state.

Every adjacent site mechanism has a persistent one-bit input interface: it reads a stored parent value that survives into subsequent influence paths. Feedback cycles have length m. These are interfaces of the exhibited completion, not a proof that every realization has the same minimal memory allocation.

The lift is a composition of bounded local tables and shared fresh sources. It avoids enumeration of the 2^n hidden states or their 2^n-by-2^n transition matrix. Ordinary observed-state linear regression occurs only in n-dimensional moment space, not in a supplied hidden basis.

## 6. Finite information and computation are charged

Population recovery requires O(n^2) same-time/lagged moments. Their acquisition requires O(n^2) pair-mask experiments, not free simultaneous observation of all ports. Each independent length-two record yields bounded observations; if each moment has error at most delta, matrix errors are at most n*delta in operator norm. The lower bound r*lambda_E on C controls inversion. With fixed epsilon,a_min and sufficiently small delta polynomial in 1/n, perturbation bounds preserve the positive A-edge and R-edge gaps. Hoeffding plus a union bound therefore gives a polynomial sample bound. This paragraph claims polynomiality, not an optimized exponent or an unproved dimension-free rate.

Implementation uses O(n^2) moment/output storage and O(n^3) dense linear algebra, plus polynomial graph extraction. Known lower margins are needed to turn approximate zeros into discrete structure. If long records replace independent stationary runs, the coupling estimate n*q^t supplies a mixing separation; correlated ticks are not counted as independent samples.

## 7. An explicit stronger probe resolves the relevant ambiguity

For an innovation triple (i,j,k), define the latent residuals

    U_i = X_i(t+1) - p - sum_l A_il*(X_l(t)-p),

and likewise j,k. Conditional independence of selectors and centering imply

    E[U_i*U_j*U_k] = r^3 * kappa_b,
    kappa_b = E[(E_i-p)(E_j-p)(E_k-p)].

To see this, write each residual as its centered selector-dependent conditional mean plus its fresh-selected centered innovation. Terms with one centered innovation vanish. Terms with two innovations multiply an independent zero-mean selector residual at the third site and vanish. Only three fresh innovations survive, with coefficient r^3. The pure selector-residual triple also vanishes because selectors are independent and each residual has mean zero conditional on X.

Here kappa_b=kappa_0-theta_b: the signed perturbation contributes -theta to the degree-three monomial and zero to every lower-degree term. Thus this moment identifies theta_b.

The stronger probe reads the three next-time outputs and the six current parent ports, at most nine named ports over a two-tick window. Every monomial in the expanded residual product has degree at most three and is recoverable under calibrated independent BSC emissions by invertible one-bit moment transforms. This uses no state access and no controlled reset. A fixed nonzero separation from theta=0 gives finite-sample testing; arbitrary continuous theta cannot be certified exactly zero from finitely many samples without a margin.

## 8. Nonliftable local candidate and a crossing warning

Pair laws with singleton P(X_i=1)=0.6 and, on every pair,

    (P00,P01,P10,P11)=(0.025,0.375,0.375,0.225)

are strictly positive and agree on overlaps, but cannot be the three marginals of any innovation source. Each pair disagrees with probability 0.75, whereas any three bits have at most two disagreeing pairs. The proposed sum 2.25 violates the universal bound 2. This is a direct obstruction, robust to less than 1/12 error per disagreement, not a global CSP search.

For any feasible fixed binary pair marginals, all joint triples differ by theta*(-1)^|x|, and positivity is a one-dimensional interval. In our family the full closed feasible interval is [-1/95,2/95]; the compact theorem interval stays strictly inside. Shared innovation sources therefore have explicit locally checkable completion fibers. Once one completion per source is selected, Section 5 produces a global process automatically, because sources are independently owned and the causal updates are well typed. The impossible pair candidate blocks that construction before deployment.

A crossing proposal that assigns the three rings independent fresh sources is inconsistent with the discovered R_ij=r^2*c>0 across rings. It must provide some cross-ring shared random resource or communication; within-ring parent messages cannot generate this conditional fresh covariance. This is a source-access obstruction, not yet an optimal persistent-memory lower bound. Conversely an arbitrary crossing regrouping with unrestricted global access is not claimed impossible.

## 9. Limits and relation to the refresh calibration

`Ambiguous_Refresh_Auxiliary.md` is an additional simpler junction-tree calibration with one-bit separators and a common refresh clock. It is **not** the main interacting example. The present rings remove that clock/reset-like mechanism and use actual multi-parent local causal updates. Remaining limitations are the three causally autonomous layers, fixed-mask independent-run access, known biased innovation marginal, and restricted update grammar. Interface minimality and nonidentification under arbitrary same-run mask switching remain unproved.

## 10. Reproducible checks and companion refinements

`check_ambiguous_family.py` and `Ambiguous_Family_QA.json` give exact-transition numerical checks on a reduced 3-rings-of-length-3 fixture (not the discovery algorithm). All 36 pair projected histories through length three agree across theta=0 and theta=1/380 to 5.4e-15, while the full transition kernel differs by 6.6e-4. Recovered A and source residual edges agree within 5.6e-16 and 4.7e-17. The residual triple difference equals -r^3/380 to numerical precision. Finite checks support, but do not replace, the general proofs above.

`check_persistent_interface.py` and `Persistent_Interface_QA.json` independently verify the persistent-source extension's identity Cov(W_t,W_(t+h))=r^6*delta^2*lambda^h at h=1,2,3,6 in a 16-state isolating fixture. Its general proof and exact stationary sampler belong to the companion process-gluing result; this fixture is not itself a multi-parent graph-discovery example.

A final scope distinction: the grammar stipulates one hidden binary variable per named noisy port. It does not supply the global partition, causal graph, source alignment or any global latent change of coordinates. Nevertheless this is not arbitrary latent state-cardinality/type discovery. Claims about “no supplied frame” should retain that explicit local binary-emission assumption.
