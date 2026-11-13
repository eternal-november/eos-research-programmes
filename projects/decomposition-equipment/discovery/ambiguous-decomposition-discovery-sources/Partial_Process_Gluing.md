# Causal crossing lifts with persistent, observationally hidden innovation sources

28 October 2026. Supplement to `Ambiguous_Family.md`; this is a proved restricted construction, not a general latent-process realization theorem or novelty claim.

## Finding

The noisy-voter ring construction admits **persistent hidden source mechanisms**, not only independent innovation choices. They are indistinguishable under every admitted fixed-pair trajectory experiment, yet their temporal mechanisms differ. Crossing pair-ring descriptions lift to one stationary process with bounded online state. Its stationary initialization is constructible by local backward tracing, without a global stationary table or an initial marginal-gluing oracle.

The key extra certificate is temporal: the same source state and parameter choice must be reused at all occurrences. Compatible one-time triple completions alone do not certify this.

## 1. Declared positive class and what is actually discovered

Use the discovered weighted causal graph A, the discovered disjoint innovation triples b, and calibrated readout channels from `Ambiguous_Family.md`. Put r=1-q1-q2>0. The discovery of A and the triple supports uses only the observable first/second moments already proved there; no hidden chart is an input.

For every triple b, admit an autonomous source with state H_b(t) in {-1,+1}, independent across b, with stationary symmetric transition

    P(H_b(t+1)=h' | H_b(t)=h) = (1 + lambda_b*h*h')/2,
    0 <= lambda_b < 1.

Conditional on the entire source-state paths, sample innovation triples independently at every source-time, with table

    P(E_b(t)=e | H_b(t)=h) = q_0(e) + (theta0_b + delta_b*h)*(-1)^|e|.

Require theta0_b +/- delta_b in [-1/190,1/190]. All source tables are strictly positive. Source transitions, selectors, and readout noise are mutually independent except for the displayed dependence. Innovations E(t) are used in the update X(t+1). The source bit is persistent and affects genuine future observable laws under richer access; it is not an inert appended state.

The binary-source bound, autonomous-source typing and selector grammar are declared model-class assumptions. The unknown actual source parameters and the source-to-port assignment are not supplied. The pair evidence discovers the assignment and local transition coefficients, but leaves the entire displayed source-parameter fiber unresolved. No claim that pair evidence identifies lambda or delta is made.

## 2. All admitted local histories remain unchanged

Every proper marginal of q_0(e)+theta*(-1)^|e| is independent of theta. In particular, for any fixed set of one or two causal rings, the corresponding marginal of each E_b(t), conditional on the **entire collection of H paths**, is a fixed table not depending on those paths. Conditional source-time independence therefore gives

    P((projected E_b(t))_(b,t) | all H paths)
       = product_(b,t) q_(selected coordinates).

Thus the projected innovation process is IID across time and independent across sources even though the unprojected source is persistent. The dynamics within those one/two rings are causally closed. Their selectors and emissions are the same. Their unique stationary trajectory law is exactly the original pair-ring law, for every lambda, theta0, delta in the fiber.

A fixed pair-mask experiment sees at most two rings, so every finite/infinite admitted history law is unchanged. Adaptation between independent runs does not alter this argument. Same-run changing masks is not covered.

The moment identities used to recover A and innovation triples remain valid: single- and double-coordinate innovation marginals are constant even conditional on the full source path and hence on the previous X state. In particular, the source memory cannot leak into the regression through an unaccounted conditional pair covariance.

## 3. Process distinction, not merely different one-time tables

For a discovered triple b=(i,j,k), let

    U_i(t) = X_i(t+1) - p - sum_l A_il*(X_l(t)-p),
    W_b(t) = U_i(t) U_j(t) U_k(t).

Let kappa0 be the centered third moment under q_0. Conditional on X(t), H(t), and the earlier complete past, independent selectors and fixed innovation singleton/pair marginals give

    E[W_b(t) | X(t), H(t), past]
      = r^3 [kappa0 - theta0_b - delta_b H_b(t)] =: c_b(H_b(t)).

Proof: expand each residual into its centered selector contribution plus its fresh-selected centered innovation. A term with one centered innovation has zero mean. A term with two innovations has a remaining independent centered selector contribution and vanishes. Three centered selector contributions vanish by their conditional independence. Only the three-fresh-innovation term remains. The parity perturbation contributes -theta to the cubic moment and zero to all lower-degree moments.

For h>=1, the tower property and autonomous source transition give

    Cov(W_b(t), W_b(t+h)) = r^6 delta_b^2 lambda_b^h.

This does **not** assume the residuals are independent through time. First condition W(t+h) on its past and source state, obtaining c(H(t+h)). Then use that the source's future given H(t) is independent of W(t), including the selectors and innovation draw at t. Finally E[H(t)H(t+h)]=lambda^h.

Hence lambda=0 and lambda>0 with the same theta0 and nonzero delta have identical one-time source tables after averaging H, identical admitted pair histories, but different higher-order temporal laws. The lagged residual product is accessible by calibrated richer noisy observations of the three outputs and their parent coordinates at the two relevant update windows. These are distinct process mechanisms, not coordinate relabelings.

**Scoped resource obstruction.** In the typed class where this source is autonomous, has no input and draws independent random bits each tick, a zero-persistent-state implementation emits IID tuples. Its residual statistic has zero positive-lag covariance. A member with delta!=0 and lambda>0 cannot be implemented by such a source without persistent memory or an explicitly charged external temporal resource. One binary source state suffices. This is not a lower bound against arbitrary simulation using the sites' state, external communication, or a pre-correlated random tape.

### 3a. Exact lift classification for specified temporal summary evidence

With only the admitted pair laws, both IID-source and persistent-source lifts are feasible: the observations cannot justify choosing one. Add the stronger summaries M=E[W(t)] and c_h=Cov(W(t),W(t+h)). In the displayed symmetric two-state class, a candidate must satisfy

    theta0 = kappa0 - M/r^3,
    c_h = r^6 delta^2 lambda^h.

If c1,c2>0, these force

    lambda = c2/c1,
    delta^2 = c1^2/(r^6*c2).

They give an exact positive realization for these summary constraints iff 0<lambda<1, theta0 +/- sqrt(delta^2) are in the allowed interval, and every additionally specified c_h agrees with the geometric formula. A sign change of delta is the harmless H-label exchange. If c1=0, all positive-lag c_h must vanish; an IID realization is feasible whenever theta0 is allowed. Negative c_h, c1>0 with c2=0, or violated positivity/geometric equations are explicit obstructions within this nonnegative-lambda class.

An IID boundary source with the same local copying mechanism gives W(t)-E W(t) a martingale-difference property relative to the whole pre-update state/history, so positive-lag covariance is zero **despite the persistence of X**. Thus c1>0 rules out that typed lift rather than merely rejecting a memoryless X process. The persistent source realizes it with one source bit. These iff statements concern the listed summaries in the specified source class; matching them is not asserted to validate arbitrary additional full trajectory data.

## 4. Constructive stationary initialization

A forward local sampler is immediate once (X(0),H(0)) is initialized jointly. Sampling H(0) independently of a guessed stationary X(0) would be wrong. The following algorithm samples the correct joint stationary state without enumerating 2^(n+m) states.

Use a bilateral stationary source chain for each b and bilateral independent selector draws conceptually. To determine each X_i(0), inspect its selector at time -1. A fresh selection terminates at the corresponding innovation coordinate E_i(-1); otherwise follow the selected first/second parent at time -1 and inspect its selector at time -2. Continue. Merge repeated visits to the same site-time node and reuse its selector. Each lineage is a single path, not a two-parent branching tree: the update selects exactly one parent.

Each line survives T levels with probability q^T. Therefore all n requested bits terminate almost surely,

    P(maximum tracing depth > T) <= n*q^T,
    E[number of visited site-time nodes] <= n/r.

After tracing, collect the finite set of terminal (source b,time t) requests. For each source sample its stationary chain at all requested times and time 0. Sorted gaps use the exact skip transition

    P(H(s+d)=h' | H(s)=h) = (1 + lambda^d*h*h')/2.

Then sample a single E_b(t) tuple for each requested source-time conditional on H_b(t), and reuse it for every terminal request there. Read each requested X_i(0) from its terminal coordinate. This also produces H(0), with the correct correlation to X(0), so online simulation can continue from the ordinary source Markov transitions.

**Correctness.** The algorithm reveals a finite random restriction of the stationary bilateral graphical construction; the tracing graph is selected independently of source paths. Every queried random variable has exactly the stipulated joint law and reuse identity. No infinite ancestor survives almost surely. Shift invariance gives stationarity, and the update equations hold pathwise. Coupling two X processes with the same source paths and selectors removes dependence on any earlier X initialization with probability at least 1-n*q^T. The finite autonomous source chain has its unique stationary law, so this constructs the unique joint stationary law.

This initialization is Las Vegas with expected O(n/r) ancestry work, plus source-time sorting and bounded-table sampling. It has unbounded worst-case temporary workspace. A hard depth cap T with arbitrary fallback has total-variation error at most n*q^T under the natural coupling. A success flag is not permission to call the success-conditioned output unconditionally exact. Exact bounded-worst-case initialization is not claimed.

## 5. Crossing pair descriptions and one common-world lift

Let the recovered rings be R1,R2,R3. Consider the three genuinely crossing process descriptions on R1∪R2, R2∪R3, R1∪R3. Each is generated from the inferred ring updates and the corresponding inferred two-coordinate innovation tables. Their state/event maps to a global candidate are literal restriction maps **constructed after discovery**. Selectors belonging to a shared site and source coordinates belonging to a shared source-time are the same random occurrences, not independently resampled copies.

For each source, three supplied binary pair tables with consistent singleton marginals have a one-dimensional affine space of joint completions: the difference of any two completions is theta*(-1)^|e|. Positivity is eight affine inequalities, hence an explicit interval (or emptiness). In the concrete family, this interval is [-1/95,2/95] around the displayed q_0, and the theorem uses a strictly interior compact subinterval.

Selecting a source **process** consists of selecting theta0,delta,lambda once, not selecting a completion separately at each tick. The construction in Sections 1 and 4 then produces one whole stationary path measure. Every crossing pair projection is the required whole pair path measure by Section 2; all projection compositions and same-occurrence identifications commute pathwise. The construction therefore certifies all finite cylinders and, by their consistent extension, infinite histories. No history switches between physical worlds.

The completion calculation itself is static and constant-size. What makes the lift causal is the persistent H process, shared occurrence reuse, state-dependent copying dynamics and jointly correct stationary initialization. The proof does not substitute static marginal consistency for these obligations.

**Local obstruction.** If a proposed triple's pair tables give total pair disagreement greater than 2, they have no joint completion, since every binary triple has at most two unequal pairs. Such a source cannot be lifted even with source memory: each fixed-time marginal would violate this inequality. More generally, an empty eight-inequality interval is a checkable infeasibility certificate. Conversely, nonempty intervals alone do not certify a prescribed temporal triple process; its own positive transition realization is an additional obligation. The displayed two-state family discharges that obligation constructively.

### 5a. Actual crossing theorem: rings versus source-aligned columns

Index the discovered alignment by sites (a,b), a in {1,2,3}, b in {1,...,m}. The fine record graph has site-store vertices X_(a,b), source-store vertices H_b, and at every tick:

* one selector occurrence S_(a,b), one update occurrence with old/new X_(a,b), and one sensor-noise occurrence N_(a,b);
* one source occurrence containing old/new H_b and the single tuple E_b;
* named parent-read wires from the appropriate old X stores and named source-coordinate wires E_b[a].

Equality/endpoint constraints make every read refer to the actual old register, every next tick refer to the preceding new register, and every use of a source tuple refer to its one occurrence. The event probability conditional on the old stores is exactly the product of the m source transition/emission factors, the 3m selector factors and the 3m sensor factors, times the deterministic update indicators. Whether H advances before/after emission is fixed as emission from H(t) then transition to H(t+1). The sensor occurrence at tick t emits Y_i(t)=X_i(t) XOR N_i(t) from the old store; the update computes X_i(t+1).

There are two crossing regroupings:

1. **Ring grouping:** group all site mechanisms with fixed a; retain m source components as shared boundary providers. Ring parents are internal. Each source's E_b coordinates are delivered to the three rings. H_b is owned once by its source component, never independently copied into ring state.
2. **Column grouping:** group the three sites (1,b),(2,b),(3,b) together with source b. Source delivery is internal; first/second predecessor parent wires cross column boundaries.

Unlike the observational pair projections in Section 5, these complete regrouped records retain the hidden source states and every full source tuple. Observational projection coherence alone is not claimed to establish an exact/cartesian event-record API. The common refinement is the displayed site/source record graph. Flattening either packet organization back to named occurrences gives a bijection onto exactly the same valid complete records. Its inverse just groups those occurrences differently. Thus their comparison is an explicit finite coordinate regrouping with equality constraints, not an appeal to planar/noncrossing interchange. The two component orders need not be intervals of one another. Both grouped descriptions retain the **joint** source kernel, not the product of its three marginals.

For every fixed parameter vector omega=(theta0_b,delta_b,lambda_b)_b, the record comparison preserves probability, endpoints, types, and every finite concatenation exactly. Section 4 initializes those same records stationarily; consequently the comparison preserves every stationary history law. Source parameters remain omega at all times. Shared-source aliases in the ring view and local source ownership in the column view are two presentations of the same H state, not separate samplers.

The fine description has 3m site bits, m source bits, 6m potential parent wires and 3m source-coordinate delivery wires; selectors and sensor noise add O(m) bounded event tables. Ring grouping has O(m) shared-source boundary traffic; column grouping has O(m) persistent parent traffic. Buffers and initialization workspace are charged separately. This is a concrete positive crossing lift with linear-sized local records, not a claim that either grouping yields independent components without its declared interfaces.

### 5b. The information-loss obstruction and its quantifiers

Fix delta!=0 and theta0, and take W0 with lambda=0 and W1 with 0<lambda<1 at a source. Every admitted pair trajectory law agrees. Both worlds have a positive joint globalization, and each has the ring/column crossing lift above. Nonetheless their actual whole laws differ by the residual temporal covariance.

Therefore:

* For every compatible world omega there exists a coherent crossing implementation L_omega preserving its whole law.
* A single **parameterized** program scheme can express all L_omega, with the world parameters selected and frozen; this is a family, not a unique inferred world.
* There does not exist one fixed whole process law L that is simultaneously equal to the whole laws of W0 and W1, even though L may reproduce all the available pair laws.
* In particular, replacing the compatibility family by one IID-source representative preserves all admitted local observations but cannot preserve the whole law of W1 under the joint crossing lift. A forgetful replacement that removes H can succeed on each local pair description yet fail jointly.

This is a failure of information-preserving descent to a common low-memory boundary type, **not** a no-globalization theorem. A worldwise proof choice is not an unobserved runtime permission to switch between W0 and W1. From pair evidence alone the IID-source lift is possible, but it is not robustly whole-law-preserving across the compatibility family. Once a nonzero temporal residual covariance is included, the IID-source lift is impossible in the stipulated autonomous-source type and the persistent-source lift remains constructive.

### 5c. Parameter-indexed evidence restriction commutes with regrouping

Let Theta be the fixed positive parameter domain and let Rec_R(omega), Rec_C(omega) be the complete ring/column record spaces for a fixed world, compared by the explicit regrouping J_omega. New evidence E' defines Theta'={omega in Theta: the law L_omega satisfies E'}. Restriction is literal subfamily selection. Thus restricting the disjoint family of records over Theta to Theta' and then applying the J_omega gives exactly the same indexed records as applying all J_omega and then restricting. In symbols, J|_(Theta') composed with restriction equals restriction composed with J. The equality holds on actual named records, endpoints, probabilities and concatenation, not just on observable equivalence classes.

The retained world tag is a proof/model index, not an extra evolving runtime memory register. Its selected numerical transition tables are charged as fixed program-description data. Removing the tag and choosing one representative after every new prefix would not be this construction. Parameter restriction preserves one world throughout an execution and across both crossings. Richer temporal data can remove the IID candidates while retaining persistent ones; pair-only evidence does not permit that deletion.

## 6. Resource and quantifier ledger

* Discovery: O(n^2) noisy pair moments, polynomial-dimensional matrix/graph computations; unknown ring and source assignment is recovered before constructing projection charts.
* Compatibility object: a product of explicit bounded source-parameter domains, not an enumeration of global states or all architecture supports. Its lambda=0 and lambda>0 members include genuine temporally distinct architectures.
* Each completion: n persistent site bits plus at most m source bits; synchronous double buffering may add n bits. O(n) local table data. At most two potential parent-bit accesses per site per tick; source tuple transmission and independent selectors/readout randomness remain charged.
* Initialization: expected linear ancestry work at fixed r>0, exact but random temporary resources; capped initialization has the explicit error bound above.
* Robust statement: every member of the declared parameter fiber has the three jointly compatible crossing descriptions. Proof maps may depend on the recovered assignment but are ordinary restrictions once it is discovered.
* Uniformity: one program schema accepts a selected parameter tuple and implements the corresponding completion. This is **not** one parameter-free physical sampler reproducing all different whole laws simultaneously.
* Stronger probes can distinguish source memory; admitted pair observations cannot. A two-state source bound is a class/resource restriction, not a source state discovered as uniquely necessary from pair evidence.

## 7. Boundary relative to prior work

The earlier finite completion/lifting theorems already enforce common-world histories and event-sensitive projection coherence. This note does not claim those principles are new. The additional restricted construction starts from partially informative nonuniform noisy history laws, derives causal edges and source supports by the main family's moment calculation, retains an explicit nontrivial process-level ambiguity fiber, and compiles every member by local positive tables with an exact stationary sampler. It avoids a supplied full physical-state chart and exponential global transition/initialization tables. Broader hidden realization discovery, arbitrary overlaps, arbitrary source automata, and optimal memory/communication complexity remain outside the proved scope.
