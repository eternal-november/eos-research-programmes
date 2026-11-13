# Principal generalization: learn innovation marginals and all positive source completions

## Theorem scope

The prescribed innovation probability 82/95 and the prescribed Gibbs reference table in the original ring example are unnecessary. They remain useful checked witnesses, not input to this theorem. Assume only the following declared noisy-copy grammar:

* N named binary noisy ports, one hidden bit per port; an unknown permutation P whose cycles have length at least five, with UNKNOWN number and lengths of causal rings, unknown first/second predecessor order, and unknown source alignment. Sources partition the sites into blocks of size one, two, or three; each block is rainbow, containing at most one site from any causal ring. Neither component count is supplied.
* Independent site selectors copy first predecessor with q1, second with q2, or take their innovation with r=1−q1−q2>0. Require q1>q2>0 for unambiguous weight labeling and uniform invertibility (q1≠q2 suffices for inversion).
* Unknown positive binary innovation source laws on blocks of size one, two, or three, independent across sources and time. No marginal, reference table, common mean, or common pair covariance is prescribed.
* Within each nonsingleton innovation source, the graph of nonzero pair covariances is connected. Quantitative discovery assumes a positive gap on its nonzero edges. Covariances may have either sign, and one of the three edges may vanish. Cross-source independence makes other covariance edges zero.
* Unknown independent fresh BSC readout noise with attenuation rho_i in (0,1). Experiments consist of fixed one-/two-port stationary histories from separate runs; no cross-run stitching.

Assume exact history data come from this grammar. Then the data constructively determine the noisy sensor kernels, weighted causal graph A, hidden stationary means/covariances, source partition, and every innovation singleton and pair marginal. Singleton and two-site source laws are fully identified. **The full fiber of iid source-law completions consistent with every allowed history law is exactly one explicit open interval per discovered three-site source.** Every point has the bounded local positive runtime already exhibited for the ring family; no true partition or positive local table is input.

## 1. Discover sensors, causal dynamics and innovation lower marginals

Use spin coordinates S_i=(−1)^X_i and observed T_i=(−1)^Y_i. Let a=E T and Γ_l=Cov(T_(t+l),T_t), l=1,2. These entries are available from distinct fixed-pair histories; they are not products of unrelated episodes.

Set

    B=Γ_2 Γ_1^(−1), S=B^(−1)Γ_1,
    rho_i=sqrt(S_ii+a_i²), D=diag(rho_i),
    μ_s=D^(−1)a, C_s=D^(−1)S D^(−1), A=D^(−1)B D.

The proof is the exact identity Γ_l=D A^l C_s D and C_s,ii=1−μ_s,i². It remains valid at zero spin means. It does not assume a known biased innovation distribution. A is invertible because A=q1P+q2P² and σ_min(A)>=q1−q2. Positivity gives C_s positive definite as quantified below.

Recover q1,q2 from the two positive entries of each row of A; check common weights, ring geometry, and the first/second-predecessor relation. The weighted graph's strongly connected components discover all causal rings, including their unknown count and lengths. With q1>q2, the larger-weight entry in each row directly reconstructs P; check that the smaller-weight entry is P² and all cycles have length at least five. These are checks/discovery within the fixed grammar, not membership certification for arbitrary external processes.

Convert to bits:

    μ=(1−μ_s)/2, C=C_s/4.

Stationarity of conditional means gives μ=Aμ+r e. Hence innovation singleton probabilities are learned:

    e=(μ−Aμ)/r.

For distinct i,j, independence of site selectors gives

    V_ij = Cov(E_i,E_j) = (C−A C A^T)_ij/r².

This identity holds with heterogeneous innovation means. Conditional on X_t, covariance between different next-state outputs arises only when both sites select fresh innovations; its probability is r². Total covariance adds A C A^T. The diagonal residual has additional selector variance and is NOT divided by r² to infer innovation variance; instead set V_ii=e_i(1−e_i).

The graph of nonzero offdiagonal entries of V, including its isolated vertices, has exactly the true source blocks as connected components under the declared connectedness assumption. Check that each component has size at most three and at most one site in any discovered ring. Thus source count and block sizes are discovered, not supplied. A pure three-way-dependent source with zero pair covariances is outside this connected-support promise. Recover source pair masses

    p_ij=P(E_i=1,E_j=1)=V_ij+e_i e_j.

Thus the full marginal data defining the extension problem are learned from noisy histories, rather than supplied as local positive frames.

## 2. Explicit complete positive-extension fiber

For one recovered triple relabel its sites 1,2,3 and write p_i=e_i. Let t=P111. Every table having the learned singleton/pair masses is necessarily

    P111=t,
    P110=p12−t, P101=p13−t, P011=p23−t,
    P100=p1−p12−p13+t,
    P010=p2−p12−p23+t,
    P001=p3−p13−p23+t,
    P000=1−p1−p2−p3+p12+p13+p23−t.

This follows by solving the seven independent normalization/marginal equations, or direct substitution followed by dimension count. Define

    L=max(0,p12+p13−p1,p12+p23−p2,p13+p23−p3),
    U=min(p12,p13,p23,1−p1−p2−p3+p12+p13+p23).

A strictly positive table exists iff L<U, and the entire positive fiber is t∈(L,U). No numerical feasibility oracle or global architecture enumeration is needed. With required atom margin ε>0, the complete closed fiber is [L+ε,U−ε], nonempty iff L+ε<=U−ε. This simple uniform shift holds because all eight affine coefficients of t are ±1.

For multiple partial descriptions, pool their learned singleton/pair constraints after verifying named-port/sensor and causal-graph identities. If they impose the same pair data, their permitted t subintervals intersect. If they specify different subsets of pair marginals, retain their linear marginal constraints in the eight atom variables; positivity and normalization are an eight-variable linear feasibility problem per triple, independent of global system size. If supplied exact descriptions disagree on an overlapping required marginal or yield L>=U, they admit no strictly positive lift in the declared grammar. Overlap consistency alone is insufficient: the L<U test is the actual local positive-extension obstruction.

## 3. Completeness relative to the declared iid-source grammar

**Necessity.** Any second grammar instance with the same complete collection of fixed-pair history laws has the same a,Γ1,Γ2, hence the same positive sensor attenuations and A,C,μ. It therefore has the same e,V, recovered source partition and pair masses. Its source law must be one of the displayed tables, and positivity puts t in the displayed interval. This uses the positive-attenuation convention; without it the corresponding bit-complement gauges must also be retained.

**Sufficiency.** Choose t independently in every interval and use independent source events across triples/times. Any fixed pair of observed ports belongs to at most two of the discovered causal rings. Those rings form a causally closed subsystem. By the rainbow promise, each innovation source supplies at most two coordinates to that subsystem, whose joint law is fixed by the learned lower marginals and independent across time/source. Its selectors and emissions are also fixed. Thus its entire transition/observation law and its unique stationary law are independent of all t. Consequently every fixed-pair stationary trajectory law agrees, for every finite length and every allowed adaptive choice of later independent-run masks. This is whole-history equivalence, not merely a covariance match.

Together these prove that the product of the learned intervals is exactly the full observational-equivalence fiber **within the declared iid triple-source grammar**. They do not classify arbitrary hidden dimensions, temporally dependent sources, extra couplings, or alternative emission families.

## 4. Genuine mechanism ambiguity, including removal of a triple interaction

Changing t changes the joint innovation table and the full transition law while preserving every permitted observation. If a canonical log-linear criterion is desired, let

    J3(t)=sum_(x∈{0,1}³) (−1)^|x| log P_t(x).

The derivative P'_t(x)=−(−1)^|x|, so

    J3'(t)=−sum_x 1/P_t(x)<0.

As t approaches L from above, at least one positive-slope atom vanishes and J3 tends to +infinity; as t approaches U from below, at least one negative-slope atom vanishes and J3 tends to −infinity. Since L<U, no atom from the opposite endpoint slope vanishes at the same endpoint. There is a unique t*∈(L,U) with J3(t*)=0. Thus every nonempty strictly positive marginal fiber contains exactly one zero-canonical-triple-interaction source and continuum many sources with nonzero canonical triple interaction. Independent choices at the recovered m3 three-site sources produce 2^m3 labelled ternary-interaction supports without enumerating them. If a prescribed large positivity margin restricts to a smaller closed interval, it may exclude t*; do not claim all support patterns inside every margin-restricted subfiber.

## 5. Persistent-interface extension, explicitly a larger grammar

For each triple optionally introduce a finite-state autonomous Markov source H_b,t, independent across b and of selectors, with a specified stationary law (or a uniquely stationary irreducible transition kernel); conditional on H paths, source events are independent and have table P_(t_b(H_b,t)). Require every t_b(h) to lie inside the learned interval (or margin subinterval). Because each conditional one-/two-coordinate table is exactly the same learned marginal, the entire projected innovation path on any two rings is still iid with that law, even though the three-way process has memory. Hence all allowed fixed-pair histories remain identical.

For a two-state fair persistent H and t(H)=t0+dH with t0±d∈(L,U), a centered triple-update residual W_b,t has conditional mean r³(kappa0+t(H)), since the coefficient of t in the centered bit triple moment is +1. Therefore

    Cov(W_b,t,W_b,t+ell)=r^6 d² lambda^ell,

where E[H_t H_(t+ell)]=lambda^ell. This differs from the parity-perturbation parameter theta in the older example, for which P111 decreases with theta and the centered triple moment has derivative −1. The covariance is the same because the sign squares.

This proves a persistent nongauge alternative with one extra stored bit per three-site source, while retaining its full learned positive table interval. It is an exhibited symbolic extension family, not the claim that product intervals alone classify every possible temporally dependent source process. Exact stationary initialization must preserve the H temporal dependence: trace copy ancestors, start H in stationarity at the earliest required time, evolve forward, and cache shared source events.

## 6. Exact causal lift and event ownership

For every retained iid parameter vector, or every explicitly selected persistent extension, instantiate one owned innovation tuple event per source/time, one independent selector event per site/time, and one sensor-noise event per port/time. Store one state bit per site, plus the selected H stores. Site updates read old parent registers and their own coordinate of the single owned innovation tuple. Shared source coordinates and separator occurrences are aliases, not independent resamples. Initialization uses the same named graphical event construction.

A fixed-pair view is the projection of this common execution to its two complete causal rings followed by its named sensor ports. The projection preserves initial distribution, the marginal transition kernel, and the emission kernel. These identities prove the exact whole-history lift. Different choices of t are different possible wholes, not isomorphic execution records; never identify them merely because the permitted view laws agree. Within a selected whole, crossing component presentations share the same named state/selector/source/noise events and old/new update order, giving the common fine realization with actual alias identities. Any additional hardware restriction on access to those shared events needs its own admissibility check.

Resource bounds are unchanged: O(N) local tables and N persistent site bits; constant-width source outputs and two potential one-bit parent inputs per site/tick; optional one H bit per source; double-buffering and separated source-output transmissions charged as in the main family. No global transition table is constructed.

## 7. Conditioning, finite data and honest retained sets

If every atom of a k-site source is at least ε>0, its spin covariance is at least 2^k ε I and therefore at least 2ε I uniformly for k=1,2,3. For a three-site source the sharper bound is 8ε I. Indeed Var(v·E)=min_c E(v·E−c)^2 >= ε min_c sum_(x∈{±1}^k)(v·x−c)^2 =2^k ε||v||². Conditioning on site selectors and past, the fresh subset covariance has the same principal-submatrix lower bound. Averaging fresh indicators yields C_s>=2rε I uniformly over source sizes one through three (and C_s>=8rε I in the all-triple witness). Therefore

    σ_min(Γ1)>=rho0² (q1−q2) 2rε.

Together with lower margins on r,rho_i,q1−q2 and the nonzero source-covariance edges, this controls every inverse/division and discrete support decision. With N dimensions, entrywise moment error δ gives operator error at most Nδ. Matrix perturbation followed by the displayed formulas yields polynomial accuracy/sample requirements under fixed margins. The exact exponent is not claimed optimized. Lag-two records replace the original lag-one-only calibration; all observations still use fixed pairs and at most three times.

For finite samples, retain all parameter points satisfying simultaneous observed-moment intervals, the copy grammar, positivity margins and the explicit local fiber inequalities. This contains the true family on the simultaneous confidence event. It is not legitimate to plug noisy inferred pair masses into an empty interval and claim a population impossibility without accounting for their uncertainty. With calibrated source-marginal intervals alone, local eight-atom feasibility is linear; unknown sensor/dynamic calibration adds nonlinear constraints and is not asserted to have a polynomial real-feasibility algorithm. Finite-horizon coupling/parameter errors remain separate from exact equality between presentations of a selected retained model.

## 8. Constructive positive empirical completion and stationary pair-law error

The following optional finite-data compiler avoids a global nonlinear feasibility assertion. Its input is the simultaneous estimation event, **after correct discrete ring/source recovery**, with an error bound η on each estimated innovation singleton/pair probability, an error bound on selector probabilities, and a bound εrho on each sensor attenuation error. These bounds can be obtained by ordinary perturbation estimates from §7; this paragraph does not replace them with a claimed optimized sample exponent.

For each discovered three-site source independently, solve an eight-atom linear program (use the analogous two-/four-atom program for smaller sources): atom probabilities at least the declared ε, summing to one, with the maximum absolute discrepancy between their six singleton/pair moments and the six estimated values minimized. The true table is feasible and has objective at most η. Hence every selected minimizer has all six lower moments within 2η of truth. This is a constant-size LP per source. Any minimizer is a valid strictly positive whole-source table; it need not recover the unknown actual triple parameter. Alternatively choose a deterministic tie-breaker to make the compiler reproducible. Clip/project the common selector vector to its declared compact simplex margin, and sensor attenuations to their declared interval. These operations preserve validity and at most multiply parameter-estimation error by fixed constants. The inferred discrete graph is kept fixed on the correct-recovery event.

Let εsel bound total variation between the true and fitted three-way selector laws. A learned source pair table has TV error at most 8η: its P11 error is at most 2η, each of P10,P01 at most 4η, and P00 at most 6η, so half the L1 error is at most 8η. Write εsrc=8η; singleton projections obey this bound too.

For any requested fixed pair of ports, their one- or two-ring closed hidden subsystem has at most N sites and at most m independent projected source events per tick. Couple selectors and projected source events maximally by their shared names. The one-step discrepancy probability is at most

    alpha = N εsel + m εsrc.

The estimated completion can differ arbitrarily in the unobserved third-order source coordinate; this does not enter the projected source coupling. Thus the claim is about allowed pair-history laws, not full global readout laws.

Assume both fitted and true total copy probabilities are at most qmax<1. Start the two coupled systems at the same arbitrary state T steps before the requested observation interval. Each model's resulting distribution differs from its own stationary law by at most N qmax^T, by the backward-ancestry coupling. Couple at most T+H update steps and the two requested sensor outputs on each of H ticks. Since sensor BSC TV is half the attenuation error, the resulting stationary H-tick pair-law bound is

    TV(P_pair,H, P_hat_pair,H)
       <= min(1, 2N qmax^T + (T+H)alpha + H εrho).

This explicitly accounts for differing stationary initial distributions. Choose T of order log(N/desired_accuracy)/|log qmax| to control the first term. It is invalid to reuse a uniform-initial-state or identical-stationary-initialization shortcut here. The same projected-law bound applies to the optional persistent-source extension when its conditional pair tables remain fixed, because each projected source sequence is still iid.

The compiler yields one positive empirical completion and a valid allowed-view error bound. It does not certify that this point lies in every original nonlinear moment confidence constraint, that it matches an arbitrary external process, or that its full joint law is close to the unknown actual whole. The retained population fiber remains the appropriate statement of unresolved architecture.

## 9. Sharper constructive outer family and dimension-free allowed-view error

The following refinement gives a simpler positive representative under quantitative atom slack. Suppose each true source atom is at least γ and estimated singleton/pair marginals have coordinate error at most η. The maximum formula implies |Lhat−L|<=3η and |Uhat−U|<=6η. Since U−L>=2γ,

    Uhat−Lhat >=2γ−9η.

For η<=γ/12 this is positive. Choose t_hat=(Lhat+Uhat)/2. Each of its eight atoms is at least (Uhat−Lhat)/2>0. This is an explicit feasible positive point, with its estimated lower marginals exactly reproduced; no LP is needed. The more flexible §8 constant-size LP remains useful when retaining a specified atom margin or noisy interval constraints.

A confidence outer family can be built from parameter boxes for the identified common selector weights, sensor attenuations, and source singleton/pair masses. Within each k-site source retain 2^k atom variables satisfying their marginal intervals, normalization, and positivity/margin constraints. These are linear local polytopes. Keep the exact recovered discrete graph and clip the selector/sensor boxes to their declared valid domains. All family points then describe valid models; the true point is included on the confidence event. This is a constructive confidence **outer** family, not the exact finite-data identified set; it deliberately does not reimpose every nonlinear measured moment equation. Structural support margins are treated as confidence qualifications rather than claiming every outer point rediscovers the same nonzero covariance support. The known source component ownership is retained even if an outer point happens to have a vanishing source edge.

### Dimension-free stationary pair-history coupling

Consider an H-tick history on two fixed ports and let K=2(H+1), a conservative bound on the number of requested state/sensor roots. For each root trace its graphical copy ancestry backward until a fresh innovation is reached. The query pattern depends only on selectors, not on innovation values. Explore shared named site/time events only once. The expected number of queried selector events is at most K/r0 when both true and fitted refresh probabilities are at least r0. There are at most K terminal source/time events (possibly fewer by coalescence).

Couple selectors with total-variation error at most εsel per named event. Before the first mismatch, both models request identical events. A union bound over queried events in the true graphical construction bounds selector mismatch probability by K εsel/r0. This uses the fact that whether a new event is queried depends on earlier revealed events, not on its own still-unrevealed selector. For terminal innovations couple the full cached source tuple projected to the one or two causal rings involved. Query patterns are independent of innovation values, so each such coupling costs at most εpair and the total is at most K εpair. There are at most K sensor events with error εsensor each. Thus the stationary allowed-view law satisfies

    TV(P_pair,H,P_hat_pair,H)
       <=min(1,K[εsel/r0+εpair+εsensor]).

No global state initialization is coupled by assertion: both sides are sampled from their exact two-sided stationary graphical construction. The bound is independent of N, and independent of their unobserved triple parameters or persistent H variants, provided those variants have the fixed conditional projected pair tables. A fully finite fallback truncates every lineage at T and gives

    TV <=min(1,2K qmax^T+K T εsel+K εpair+K εsensor).

Both tail terms are included because each model may have an unclosed lineage. This finite construction also justifies passage to the almost-sure terminating graphical coupling by taking T→infinity, while the expected-occurrence argument sharpens its rate.

## 10. Prior work and contribution boundary

The basic copy/fresh model and observed-state moment recovery are established baselines, not claimed inventions here. Jentsch and Reichmann, *Generalized binary vector autoregressive processes*, Journal of Time Series Analysis 43 (2022), 285–311, DOI 10.1111/jtsa.12614, define independent multinomial site selectors with jointly distributed binary innovations (Definition 2.1). Their Theorem 2.7 and equation (2.25) give Yule–Walker parameter recovery; Theorem 2.8 yields innovation-covariance identification. [Primary full text](https://d-nb.info/127887058X/34).

The scoped combination here is unknown noisy-sensor calibration from partial pair histories, the exact class-relative all-history completion fiber, persistent higher-order alternatives, constructive confidence outer families, and explicit shared-event realization witnesses. No literature-priority or superiority claim is established for that combination, and no generic latent architecture discovery theorem follows.

## 11. Complete fiber in an explicitly declared persistent binary-source subclass

Completeness can be strengthened beyond iid sources without pretending to classify arbitrary hidden temporal processes. Declare exactly this enlarged grammar: for every source triple b, an independent fair stationary binary Markov spin H_b has transition kernel

    P(H_next=h'|H=h)=(1+lambda_b h h')/2,
    |lambda_b|<=lambda_max<1.

Conditional on all H paths, source tuples are independent across source/time, and source b emits P_(t_b(H_b,t)), where both conditional tables have the same singleton/pair marginals. Each conditional table must satisfy the declared atom margin γ. Every pair of such binary-triple tables is necessarily represented by

    t_b(H)=t0_b+delta_b H.

Therefore the **entire parameterized realization fiber within this declared subclass** is

    L_b+γ <= t0_b−delta_b <= U_b−γ,
    L_b+γ <= t0_b+delta_b <= U_b−γ,
    |lambda_b|<=lambda_max,

independently over b, together with the already recovered sensors, causal graph and lower source marginals. Without a fixed atom margin replace the first two inequalities by strict L_b<t0_b±delta_b<U_b.

Necessity follows from noisy calibration and the eight-atom characterization, plus the declared binary modulator form. Sufficiency follows because conditional one-/two-coordinate laws do not depend on H; integrating any stationary H path leaves the same iid projected source process on any two rings. Thus every parameter point produces exactly every allowed fixed-pair history law. This is a complete symbolic fiber for the named subclass, not an exhaustive classification of all temporally dependent couplings.

Swapping H labels replaces delta by −delta and changes nothing physical; optionally impose delta>=0 to quotient that gauge. At delta=0, H is dynamically irrelevant. At lambda=0, H is iid and the emitted source process is the iid P_t0 law, so keeping the extra H bit is a redundant realization; one may remove it explicitly. When delta*lambda!=0, the residual correlation r^6 delta² lambda^ell gives a genuinely persistent observable higher-order distinction under the stronger probe. Negative lambda produces alternating signs rather than invalidating the construction.

The finite confidence outer family remains constructive: retain local atom/marginal inequalities for both t0±delta, together with the lambda box. All source-table inequalities are affine in the source lower marginals,t0,delta. No global nonlinear feasibility problem is introduced. Physical realizations charge the optional H registers, their initialization and Markov update events; observational equivalence alone never makes them free.


## 12. Count-free principal scope and final interpretation

The principal theorem now allows an unknown number of unequal-length causal cycles and unknown source counts/sizes, as specified at the start. The earlier three equal rings and all-triple sources are a growing checked witness, not an input to discovery. Every source-related formula for an eight-atom table, t interval, midpoint, ternary interaction or persistent modulator applies only to discovered size-three sources. Size-one tables are (1−e_i,e_i); size-two tables are (1−e_i−e_j+p_ij,e_j−p_ij,e_i−p_ij,p_ij), fully learned, with positivity checked directly. Their finite confidence sets are the analogous two-/four-atom linear polytopes. Optional H stores on size-one/two blocks with fixed conditional lower marginals are behaviorally redundant and are omitted.

In the iid and declared binary-persistent completion theorems, take the product only over recovered size-three sources; multiply by the uniquely determined size-one/two factors. All full-pair-history necessity and sufficiency proofs remain unchanged: pair views close in at most two causal cycles, and the rainbow condition limits every source projection to at most two coordinates. The matrix bounds use the conservative uniform 2rε covariance lower bound now recorded in §7. In resource counts, m means the discovered total number of sources (at most N), while the number of optional H bits is only the discovered number of three-site sources. No count, equal-length assumption, or three-way zero-pair-covariance block is silently supplied or admitted.
