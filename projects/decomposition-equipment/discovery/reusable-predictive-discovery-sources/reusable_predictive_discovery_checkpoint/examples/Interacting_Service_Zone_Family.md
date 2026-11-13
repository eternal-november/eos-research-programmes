# A stress-test family for reusable predictive decomposition

29 October 2026. Candidate benchmark specification, not an identification theorem.

## Plain-language abstract

Consider a mobile robot moving among zones whose doors, communications and braking support can become busy or slow. Requests add work; service removes work; heat and neighboring congestion change service quality. Sensors report these conditions imperfectly. We do not supply the decomposition into independent services, and no experiment reveals component membership directly. The aim is to discover which streams need joint prediction, what history must be remembered, and which messages can carry that history between discovered components.

A useful stress test must admit an honest negative answer. Even a two-state hidden mode with ordinary noisy observations can require infinitely many distinct exact predictive states. Thus a finite physical mechanism does not imply a finite exact, executable predictor. Approximation and explicit prediction error are essential, not cosmetic. Moreover, two local predictive beliefs need not suffice jointly when their services share an uncertain persistent cause. The family below supplies positive mechanisms, real interaction and these failure modes, without claiming that its architecture is uniquely recoverable from arbitrary logs.

## 1. Parametric environmental family

There are N named command/readout ports, but no supplied grouping into mechanisms. A candidate realization chooses a directed graph G, a partition B of ports into latent service groups, and parameters. The graph and partition are unknown candidate variables, not reported labels.

Each port i has a finite workload Q_i(t) in {0,...,C_i}. Each group b has a hidden thermal/service mode H_b(t) in a finite alphabet. An optional shared external mode Z(t) has a finite alphabet. Commands A_i(t) in {0,1} represent an admitted additional service request, not an arbitrary physical intervention. The local update is:

1. Draw a service bit S_i(t), jointly with other bits in its shared-source group, conditional on Q(t), H(t), Z(t), A(t).
2. Q_i(t+1) = min(C_i, max(0,Q_i(t)+A_i(t)-S_i(t))).
3. Draw H_b(t+1) from a strictly positive table depending on H_b(t), the group's workloads/commands, and permitted neighboring group summaries.
4. Draw Z(t+1) from a strictly positive mode table.
5. Emit Y_i(t+1) from a positive noisy readout table depending on Q_i(t+1), H_{b(i)}(t+1).

For example the marginal service probability can be

    sigmoid(alpha_i - beta_i H_b - gamma_i Z
            - sum_(j->i) w_ij 1[Q_j=C_j]),

with nonzero weights and positive probabilities bounded away from zero and one. For finite alphabets this is simply a positive finite table; logistic parametrization is optional. Grouped service draws may be positively or negatively correlated conditional on the displayed state; their FULL joint table, not only marginals, is part of the positive realization. Workload interaction is dynamical: one group's congestion changes another's transition law, which changes later congestion. This is not a conservation constraint or independent block permutation.

All shared randomness has one source identity per time and one persistent mode trajectory. Replacing it with fresh independent copies is a different model. The entire finite system has a positive stochastic transition/emission realization (although deterministic workload updates make some global transition entries zero). This alone says nothing about identifiability.

The finite alphabet, capacity, possible neighbors, mode-size bounds, admitted action alphabet and sensor family define a structural universe. They are substantive assumptions. One may omit parametric logistic restrictions and use all positive local tables. Neither version promises tractable inference.

## 2. Evidence and unknown grouping

Data consist of time-stamped commands and noisy readout streams, possibly only on patches, under declared acquisition policies. Recorded synchronization is retained. A patch of separately sampled episodes supplies a marginal process law, not an aligned joint law. Group labels, workloads, thermal states and shared Z are not supplied.

A candidate discovery result should output a SET of positive joint realizations and executable predictive interfaces, together with which aspects are common to all evidence-compatible members. A finest physical grouping need not be unique. Zero interaction weights, observationally equivalent duplicated modes, and unexcited actions all produce ambiguity. A grouping may nevertheless be predictively useful even when it does not coincide with a unique physical partition.

There is no reset operation here. Commands add work and may indirectly change heat and congestion. Their effects need not distinguish all hidden causes. Controller transfer is restricted to commands and histories supported by the acquisition/identification contract. Passive logs from a never-requested service do not establish its response to requests.

Discovery is NOT established by this definition. An eventual theorem or computation must search unknown grouping, causal message dependencies and recursive updates from the actual evidence. Supplying G, B, or exact local filters as inputs would reduce the benchmark to verification and miss the research target.

## 3. Why exact finite predictive memory can fail

A subfamily already gives a sharp obstruction. Let H_t in {0,1} have transition probabilities P(H_(t+1)=1|H_t=1)=9/10 and P(H_(t+1)=1|H_t=0)=1/10. Let Y_t be a conditionally independent readout with P(Y_t=1|H_t=1)=4/5 and P(Y_t=1|H_t=0)=1/5. Start P(H_0=1)=1/2. There are no actions in this subcase, so failure also applies to any controller family containing a passive policy.

If p is the posterior mode probability after a history, prediction followed by readout 1 updates

    r = 1/10 + (4/5)p,
    f(p) = 4r/(1+3r).

Starting at p=1/2 and repeatedly observing 1 yields infinitely many strictly increasing posterior values. Indeed f is strictly increasing, f(1/2)>1/2, and its unique fixed point in (0,1) is an upper bound; a non-fixed iterate cannot reach the fixed point because f is injective. Every finite all-1 word has positive probability. Next-readout probability is

    P(Y_next=1|history)=13/50+(12/25)p,

so all these histories have different next laws. Any deterministic finite-state exact predictive observer with a fixed state-to-forecast map would merge two of them and issue the same next law, a contradiction. An unbounded external clock or a time-indexed infinite table is not free: if it changes the forecast, it counts as predictive state or another explicitly charged resource. This rules out finite exact predictive state, not finite physical latent state or real-valued Bayesian filtering.

There is also a same-time version: at length t, the t+1 strings 0^(t-k)1^k, k=0,...,t, have strictly increasing posteriors. Adjacent strings differ only by replacing one 0 with 1; the common-prefix posterior is identical, the 1-update strictly exceeds the 0-update, and all common-suffix updates are strictly increasing. Thus at least t+1 predictive states are required at that time, even if the forecast map is allowed to depend on an external time index. The obstruction is stronger than a finite-horizon state count: no fixed finite-state exact predictor works for all horizons. A horizon-H predictor can always store the whole history, at exponential cost. A declaration that predictive interfaces have finite memory must therefore either restrict the universe beyond finite latent mechanisms, allow approximation, or return infeasibility.

## 4. A positive approximate recursive interface in that subfamily

Let ell=log(p/(1-p)). A readout adds either +log(4) or -log(4) after the mode transition. The transition maps ell to

    T(ell)=log((.1+.9 exp(ell))/(.9+.1 exp(ell))).

Its derivative has maximum .8, attained at ell=0. Therefore each full update is .8-Lipschitz in log odds, independently of the observed symbol. After one update the exact log odds lie in [-log36,log36]. A uniform grid on this interval, rounded to within d/2 after every update, gives

    |ell_t - ellhat_t| <= .8^t |ell_0-ellhat_0| + (5/2)d.

The logistic map is 1/4-Lipschitz, hence posterior error is at most (5/8)d after exact initial grid placement. One-step readout total variation is at most (.48)(5/8)d = .3d. Coupling sequential predictions gives total variation at most min(1,.3 H d) for H future readouts, when the approximate predictor updates on the actually generated/read symbols. This is a positive stochastic predictor: output probability remains in [0,1], not a signed predictive-state formula.

Grid state count is about 2 log36/d +1; its stored state costs log2 of that count. The certificate is uniform over every observation string, including unlikely ones. It does not identify the unknown parameters from data. Parameter confidence sets must be retained or their induced filter error bounded separately.

For a controlled two-mode family with transition matrices having a common projective contraction bound, the same proof works uniformly over actions; action-dependent emission tables add their corresponding log likelihoods. Adaptive controllers can then be coupled using the same random coins until observations differ. But the contraction bound must be proved for every admitted action; it is not implied by randomized experimentation.

## 5. Joint prediction is not a product of local filters

If two service zones share H or Z, filtering all aligned readouts updates ONE posterior on the shared state. Local posteriors computed from disjoint local histories are not independent physical causes. A joint prediction must use a compatible posterior and one joint innovation table.

Even with no persistence, two Bernoulli readouts with the same marginal parameter can have independent or correlated couplings. Unaligned single-zone streams cannot determine that coupling. With persistence, their aligned joint history may also change the posterior on a common mode and therefore future predictions. Returning two correct local marginal predictors is insufficient for arbitrary controllers that select future commands using both streams.

This makes three distinct valid outcomes necessary:
- a positive jointly predictive implementation and a quantified uniform error;
- several incompatible joint implementations left unresolved by the available evidence;
- an obstruction to the proposed memory/message budget or to any positive implementation in the declared class.

A general exact classification of all such joint realizations is not established here. The benchmark is intended to expose that obligation, not assume it.

## 6. What would count as a consequential demonstration

Use at least one interacting instance with unknown port grouping and multiple action choices, learn/recover a family of recursive interfaces from a proper subset of aligned histories, and test held-out controllers whose command choices differ from the acquisition policy but respect coverage. Compare against full-history storage and separate local predictive fits. Report which groupings remain observationally equivalent; do not score arbitrary latent naming as an identification error.

A useful boundary must improve memory/communication or evidence requirements while retaining positive joint prediction over the controller family. If every useful solution simply stores the full joint history, that is an honest adverse result. If the evidence admits both safe and unsafe physical modes, report the ambiguity rather than selecting a convenient fitted world.

The physical interpretation needs independent calibration connecting readouts and workload states to actual stopping/clearance/thermal limits. Prediction transfer alone is not physical safety. This example specification supplies no such real-world calibration and no physical validation.
