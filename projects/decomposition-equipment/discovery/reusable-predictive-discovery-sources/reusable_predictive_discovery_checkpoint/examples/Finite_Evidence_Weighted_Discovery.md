# Finite-evidence discovery of recurrent service interfaces

29 October 2026. Reproducible synthetic finite-horizon integration result.

## Plain-language abstract

This experiment starts with noisy finite counts of complete service episodes, not exact transition tables. It searches which earlier readings and neighboring signals each predictive component needs, proposes a small recurrent implementation, and then checks that implementation against every complete history represented by the evidence. It does not assume that the true environment has the proposed short memory.

The accepted implementation remembers one earlier local reading, receives one neighboring signal, and coordinates its random responses through a positive common source. For two future decisions, its entire action/readout predictions differ by at most 0.043613 in total variation from every evidence-compatible causal environment, uniformly over adaptive controllers. A verifier that treats the rarest history as typical gives the much worse bound 0.19998 and rejects the same proposal. Weighting uncertainty by actual possible visitation is therefore doing visible work.

The data are simulated, not physical. The histogram represents 10.24 million independent synthetic episodes; compression does not make that acquisition cost disappear. The two readout ports are given. The search discovers their predictive input scopes and required history/messages, not the unknown number or unique physical partition of environmental mechanisms. This is an end-to-end calibration of the general discovery certificate, not a practical-scale architecture-discovery demonstration.

## 1. Actual synthetic sampling and the evidence object

`check_weighted_episode_discovery.py` samples a multinomial histogram of N=10,240,000 IID episodes using NumPy seed 202610291533. Sampling the histogram directly is distributionally the same as drawing N independent categorical episodes and counting them. It does not materialize ten million records. Floating arithmetic approximates the rational generating probabilities; this is ordinary synthetic simulation, not an exact random-arithmetic theorem.

Each episode has six observed pairs:

    previous readouts z, current readouts y, action a0,
    next readouts u, action a1, final readouts v.

There are 4096 possible complete episodes. The acquisition policy samples each of the four joint actions uniformly and independently at each decision. The initial (z,y) pair is uniformly distributed in the generator. The true generating kernel is used only to produce the synthetic episode distribution. The proposal and validator subsequently receive the sampled counts, not that kernel or its coefficients.

There are 64 first-decision history/action rows and 1024 second-decision FULL-history/action rows. A second-decision history is (z,y,a0,u), not merely its last two readouts. Every row is measured. The smallest observed row count is 365.

The underlying source family and the two-port formulas are described in `Discovered_Service_Memory_and_Shared_Load.md`. This note replaces its population-table-only validation with a finite-evidence calculation. The billion-episode and perfectly balanced synthetic histograms retained in the directory are conservative intermediate calibrations, not the main result.

## 2. Unknown scopes and positive proposal

For each port, the proposal routine searches all 64 subsets of the six observed coordinates (y0,y1,z0,z1,a0,a1). A fixed 0.01 empirical-range tolerance identifies candidate masks. It discovers the unique inclusion-minimal masks

    port0: (y1,z0,a0),
    port1: (y0,z1,a1).

The tolerance is a proposal heuristic, not a significance guarantee. The pooled local response estimates are rounded to tenths, and a common-source mixture weight estimated from the joint response counts is rounded to tenths. These operations propose a compact rational implementation; they do not assume that the real environment belongs to that rational family. The later uniform confidence-set check remains valid for data-dependent proposals.

The proposal recovers mixture weight 1/2. Its 110 positive response atoms implement the two local response tables at all contexts simultaneously. The memory update is m_i := current local readout. A component uses m_i, its neighbor's current readout, and its own action. Initial memory is the actual preceding recorded local readout.

Only the two named readout ports are fixed. Predictive dependence boundaries are discovered around those ports. This does NOT identify latent component count, ownership or a unique physical partition. A centralized implementation and the distributed implementation remain different allowed placements. Their memory/communication tradeoff must be accounted for explicitly.

## 3. A confidence universe with no finite-memory promise

Let p_hat_h,a be the four-outcome empirical next-readout law at a full history/action row with n_h,a visits. Let M=1088. Fix exponent thresholds T=13 for conditional rows and T0=16 for the initial law, independently of the observed counts.

For four outcomes, total variation equals the maximum signed difference on a subset. A union bound over the 14 nonempty proper subsets and one-sided Hoeffding inequalities yields

    Pr[TV(p_hat,p)>r | n] <= 14 exp(-2 n r^2).

Define r_h,a by rounding upward to a millionth from

    sqrt(13/(2 n_h,a)).

For the sixteen-outcome initial law use r_init rounded upward from sqrt(16/(2N)). Both roundings use integer square roots and exact rational inequalities; there is no floating logarithm or square-root rounding assumption in the certificate. The fixed unconditional union bound is 14 M exp(-13) + 65534 exp(-16). Exact rational Taylor sums through degree 100 lower-bound each exponential, proving this total is less than 0.041804218 and hence less than .05. No realized sum of count-dependent tail bounds is reported as an unconditional guarantee.

These count-dependent radii are valid conditional on the visit count at a fixed time/history/action row: independent episodes give independent next outcomes conditional on that prefix. Unconditioning preserves the bound because the per-row upper bound 14 exp(-13) is fixed. Rows at different times may be dependent; the union bound does not require their independence. A zero-count row would receive radius one and arbitrary empirical center, not an invented estimate.

Let C consist of EVERY finite-horizon causal law with initial law in the initial TV ball and conditional next laws in all of these full-history TV balls. No Markov, latent-mode, finite-state, additive, rational or shared-source promise is imposed on C. The proposed predictor has such a structure; the environment being certified need not.

The confidence construction requires genuinely independent complete episodes in one stable regime, an exogenous acquisition policy, and unchanged response kernels when the controller policy is changed. The simulation supplies these conditions. Real logs would need independent justification. The statistical intervals do not establish those physical assumptions.

## 4. Weighted robust certificate

For the data-derived positive predictor K, at every full row define

    gamma(h,a) = min(1, TV(p_hat_h,a,K_h,a) + r_h,a).

For every P in C this bounds the true one-step predictive discrepancy at that full history. It need not be small at rare rows.

For a four-outcome TV ball, maximizing a linear expectation is exact: move probability mass, up to the TV radius, from smallest-value outcomes to largest-value outcomes, respecting nonnegativity and total mass. The checker performs this finite operation using rational arithmetic.

At the final decision, let

    V1(h) = max_a gamma(h,a).

At the first decision, let

    V0(h) = max_a [gamma(h,a)
                  + max_(p in row TV ball) sum_y p(y) V1(h,a,y)].

Finally maximize E[V0] over the initial TV ball, and add the bound

    TV(p_hat_initial,K_initial) + r_init

for the initial-law discrepancy. This is an upper bound on the initial discrepancy plus the expected sum of one-step discrepancies, uniformly over every P in C and every adaptive controller using the admitted readouts/actions. Sequential coupling gives the resulting action/readout-path TV bound.

For THESE particular confidence constraints, conditional rows can vary independently over their TV balls: any choices define a causal law. Thus the history DP does not discard an extra shared-parameter constraint. If additional evidence coupled rows or imposed persistent parameter identities, this DP would remain an outer relaxation unless that constraint was retained. It is not a license to rectangularize arbitrary uncertainty.

## 5. Checked result and benefit of weighting

The reproducible run gives:

- conditional TV radii: 0.006357 through 0.133448;
- total simultaneous failure bound: 0.041804218;
- robust weighted path discrepancy: 0.043612461;
- outward rational certificate: 43613/1000000 = 0.043613;
- uniform worst-prefix bound on the SAME data and proposal: 0.199983509.

With acceptance threshold 1/20=.05, the weighted certificate accepts and the worst-prefix certificate rejects. This is not merely a smaller coefficient in a theorem: the finite calculation changes the decision.

Two explicit adaptive controllers are included in the companion checks: request service when the local readout is clear, and request service when it is busy. The all-controller certificate is stronger: it includes policies depending on the entire shared observed history, not only these two examples. It transfers the whole observable law over H=2, not a single hazard statistic. No infinite-horizon or physical hazard guarantee follows without further arguments.

## 6. The discovered memory and message have a certified purpose

The nominal positive law defined by the candidate K and uniform initial distribution lies inside C; the checker verifies all of its conditional and initial TV inequalities. It is therefore a valid adversarial member of the uncertainty set for rejecting weaker proposals.

Under the controller a_i=1-y_i, pair initial histories differing only in z_i. They have equal mass 1/16 and their next local response probabilities differ by 1/5. A predictor lacking access to z_i must issue one marginal forecast for both histories. The triangle inequality gives expected first-step TV at least 1/10 after summing these pairs.

Likewise, pair histories differing only in the neighbor's current readout. A component without that readout or any equivalent delivered information must use the same forecast; summing again gives weighted first-step discrepancy at least 1/10. Thus either omission fails the .05 certificate criterion, whereas the discovered implementation passes.

These lower bounds concern the fixed distributed access contract: each port sees its own action, not the other controller's action as a free side channel. An action or stored message encoding the missing signal is information and must be charged. Moving storage to a neighbor, adding query/reply phases, or centralizing both ports changes the contract. The result does not assert an unconditional physical one-bit lower bound against all architectures.

The rejection is a lower bound on the one-step-discrepancy certificate objective J. It must not be mislabeled as a matching lower bound on total path TV: the latter needs its own argument. The comparison establishes usefulness for this reusable-prediction certificate, not unique physical necessity.

## 7. Reproduction and limits

Run, in order:

    python check_finite_episode_discovery.py
    python check_weighted_episode_discovery.py

The first creates the rational source histogram used solely for sampling. The second draws noisy counts, discovers masks and the positive proposal, validates every full-history row, solves the robust weighted DP and checks the cheaper-context witnesses. The optional `check_sampled_episode_discovery.py` runs the billion-episode uniform-bound baseline. No check materializes a billion records.

The main compressed input/output artifact is `weighted_sampled_service_histogram.json`; numerical results are `weighted_episode_discovery_checks.json`.

The 10.24-million-episode cost remains large for this small H=2 example. It is not a claimed sample-efficient practical method. Longer horizons have exponentially many full histories under this exhaustive evidence scheme. The meaningful gain established here is that a compact recursively executable positive proposal can be selected from finite data, certified against non-Markov alternatives, transferred across controllers, and shown superior to weaker information scopes using the weighted criterion. General architecture discovery, sparse evidence reduction and real physical assurance remain separate burdens.

### Shared randomness is an explicit resource

The joint sampler is executable in centralized software, but its common noise must not be treated as free communication in a distributed implementation. A concrete driver draws a uniform integer R in {0,...,199}. For R<100 it sends floor(R/10) to both ports. Otherwise it sends floor((R-100)/10) to port0 and (R-100) mod10 to port1. Each port compares its threshold divided by10 with its selected response probability. Enumeration verifies the desired joint table.

Thus a distributed sampler requires a declared common driver with 200 equiprobable outcomes per tick and a 10-symbol threshold delivery to each port (4 fixed binary bits), in addition to the one-bit neighboring observation and one-bit recurrent memory per port. The source-to-port messages are causal model-simulation resources, not newly assumed sensors of the actual environment. Centralized sampling can avoid physical interprocessor delivery, but then the implementation is centralized. A centralized numerical forecaster can calculate the joint probabilities without drawing any random source; these random-source resources concern execution of the generative simulator. An ideal uniform200 primitive is part of that execution contract. Implementing exact uniform200 from fair bits by rejection has unbounded worst-case draws, so an exact fixed-deadline sampler is not supplied merely by declaring an eight-bit register. Counters, synchronization, delivery and random-bit generation have their own costs. No installed hardware capability is certified by this mathematical witness.

### Optional bounded-work random driver

An approximate driver removes the ideal uniform200 sampler's deadline issue. Draw exactly twenty independent fair bits, interpreted as U in {0,...,2^20-1}, and set R=floor(200 U/2^20). This uses a twenty-bit input register and arithmetic producing an eight-bit driver identifier; the threshold deliveries remain ten-symbol messages. It assumes a declared fair-bit source and bounded arithmetic/delivery capabilities, not hardware attestation.

The 200 driver probabilities have counts either 5242 or 5243 out of 2^20. Exact total variation from uniform200 is

    delta_source = 33/1638400 = 0.0000201416015625.

Deterministic threshold postprocessing cannot increase TV, so every predictive response row changes by at most delta_source. The same recursive states and evidence certificate therefore give J_new <= J_old + H delta_source. For H=2 the exact checker obtains an outward J bound of 0.043653, still below .044 and the .05 acceptance threshold. This is a fixed twenty-random-bit generative program, not a claim that eight fair bits can sample uniform200 exactly. A centralized numerical probability forecaster needs neither this approximation nor random sampling.
