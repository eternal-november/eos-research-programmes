# Evidence reduction: routes, barriers, and acceptance conditions

29 October 2026. Focused audit for the new authorized target. This is not a novelty clearance. Primary papers inspected below; mathematical comparisons labeled as deductions are this audit's derivations.

## Plain-language abstract

The previous construction spent millions of episodes learning uncertainty at every observation history. We can avoid much of that expense if the required predictions concern a rich but explicitly bounded language of experiments, rather than every conceivable transcript event. The unknown interfaces can still be discovered and implemented as positive joint recursive systems. But the cheaper evidence supports a narrower promise, and action coverage can remain expensive. Another route retains full prediction guarantees by assuming that the actual process belongs to a compact learnable family. That promise must be stated as a new assumption, not inferred from passing a few tests. Conditional-independence tests and active experiments help in particular regimes; neither makes unobserved history dependence disappear. The next result should make one of these trades explicit and demonstrate a substantial gain on the same acquisition problem, while retaining unknown memory, interactions, and legal communication as outputs.

## 1. Previous boundary

Read: `reusable_predictive_discovery_20261029/audit/Prior_Coverage_and_Target_Burden.md`, and `safety_representation_discovery_20261029/audit/Safety_Representation_Baselines.md`.

The last theorem gives full joint finite-horizon transcript total variation uniformly over the declared full-history controller family, without a latent finite-memory assumption on truth. Its example validates 1088 full-history/action rows using 10.24 million H=2 episodes. That numerical count is an upper cost of that method, not a lower bound. The prior safety milestone already uses direct importance-weighted task moments and robust moment LPs. Calling that alone a new decomposition-discovery theorem would repeat existing coverage.

## 2. Why cheap global certification needs an explicit trade

**Unrestricted distribution learning.** Even a system with one action and one final observation can encode an arbitrary distribution on K outcomes. Therefore unrestricted TV prediction includes ordinary K-symbol distribution learning. A short note by Canonne gives the standard finite-domain learning rates; its TV requirement scales with domain size, unlike weaker metrics. Primary source: https://arxiv.org/abs/2002.11457 . Our reduction is elementary: use one episode as one draw from the unknown K-point law. Consequently a theorem claiming domain-free full-TV learning for all causal laws must have introduced another restriction, whether on data access, truth, or guarantee.

**Testing is cheaper than learning, but not generally dimension-free.** Canonne–Diakonikolas–Kane–Stewart, *Testing Conditional Independence of Discrete Distributions* (STOC 2018), studies X,Y of bounded alphabet conditional on n-valued Z. Its optimal fixed-confidence sample complexity is

Theta(max(sqrt(n)/epsilon^2, min(n^(7/8)/epsilon, n^(6/7)/epsilon^(8/7)))).

Their epsilon is l1 distance to the conditional-independence property, not exactly our TV convention. Primary source: https://arxiv.org/abs/1711.11560 . Thus testing whether a summary discards relevant history cannot generically erase dependence on the number of conditioning histories. This is a route-specific obstruction, not a lower bound on every decomposition method.

**Candidate comparison is not absolute certification.** A finite positive candidate family allows likelihood-ratio/Scheffe comparisons with complexity logarithmic in candidate count. The usual agnostic TV conclusion includes an approximation term inf_Q TV(P,Q). That term cannot be silently set to zero because a candidate matches the comparison statistics. For an unrestricted true law, finite comparison tests can miss distinctions absent from every candidate. This is the important distinction between model selection and a certified representation-completeness claim. No new theorem or novelty is claimed for this observation.

## 3. Most viable assumption-light route: explicit experiment language

Let Pi be a finite family of executable controllers and G a finite family of bounded [0,1] joint transcript monitors. Let P be any causal observable process, and Q a positive joint recursive implementation selected from a bounded language with unknown scopes, memory/update maps, encoders and source coupling. The relevant error is

sup_(pi,g) | E_P^pi g - E_Q^pi g |,

not full TV unless G separates every transcript event.

Under exogenous exploration e with known action probabilities, each target expectation equals E_P^e[w_pi g]. If 0<=w_pi<=W, Hoeffding plus a union bound gives simultaneous error eta using

N >= W^2 log(2 |Pi||G|/delta)/(2 eta^2).

This elementary bound is a transparent baseline, not a proposed optimal statistical method. Empirical-Bernstein/variance methods may improve W^2, but must include their own finite-sample conditions. Confidence over an entire predeclared countable grammar can instead allocate delta by prefix code; adaptively chosen monitors cannot be treated as fixed tests without such protection or a fresh holdout.

A candidate satisfying all certified moment constraints inherits the corresponding operational prediction guarantee. Positive recursive implementation is a separate exact semantic obligation, not a property deduced merely from the moments. The truth need not have finite memory. The guarantee simply stops short of asserting full predictive sufficiency.

**Rich enough to be more than one risk calculation:** bounded-state controller programs; finite-state monitors for latency, repeated failures, joint alarms, conditional service response, bounded temporal patterns and cumulative thresholds; combinations across components; an explicit horizon. All must operate on genuinely available observations. For a deterministic m-state controller with observation alphabet O and action alphabet A, a rough program count is m * A^m * m^(m|O|). For an r-state Boolean monitor on alphabet A x O it is at most r * r^(r|A||O|) * 2^r. Logs of these counts are polynomial in program sizes despite exponentially many programs. Time-indexed versions add H factors. These counting bounds are audit deductions, not identifiability claims.

**Critical controller caveat:** deterministic stationary tables do not generally convexly generate the performance set of repeatedly sampled randomized stationary tables with tied parameters. Include randomized tables explicitly (e.g. a finite grid with proved approximation error), or restrict the claim to the actual deterministic grammar. All causal history policies may be treated by deterministic extremal trees, but their class is enormous and restores history complexity.

**Critical acquisition caveat:** W can be |A|^H for deterministic targets under uniform actions. Running each of M controllers on-policy can remove importance weights but cost M experiment groups. A uniform random mixture over M arbitrary controllers need not give log M acquisition cost. No distribution-free theorem can manufacture coverage of action sequences never adequately sampled. This is likely the next practical bottleneck after removing full-output-law estimation.

**Why decomposition is still an obligation:** the synthesized artifact must be one reusable joint process satisfying all tests and an actual distributed execution contract. It must discover which histories/interactions need retaining, not output separate scalar fits for each (pi,g). Charge initial shared memory, source correlations, message timing and entropy, numerical precision, and the cost of computing the candidate's test expectations. Central moment estimation by itself is not decomposition discovery.

## 4. Stronger guarantee route: learnable predictive family

Zhan–Uehara–Sun–Lee, *PAC Reinforcement Learning for Predictive State Representations* (2022), has an especially relevant precise boundary. Section 2 supplies a core test set (not necessarily a minimum one). Assumption 3 requires realizability, a quantitative inverse conditioning bound, and validity of every model's induced trajectory distributions. These are not consequences of randomized sampling. Primary full paper: https://arxiv.org/html/2207.05738v3 . Its model-based policy-learning result does not automatically give a positive decentralized realization or discover legal interfaces. A proposed use must prove those extra obligations, rather than treating linear predictive coordinates as physical executable state.

This route can be substantively worthwhile if the unknown universe permits wide, nontrivial interaction patterns and the result discovers them. But it changes the old assumption-light contract. A supplied core test family already carries a completeness promise. Bounded rank, bounded memory, positivity, quantitative identifiability and experiment coverage must each be named. Known algebraically favourable families from the programme must not simply be reintroduced under a different name.

## 5. Active queries and interface experiments

Active experiments can direct samples to discriminating continuations. They do not provide a free exact equivalence oracle. A physical ability to reset an entire system to a known state is distinct from replaying an observed history; replay may induce different hidden posterior states. A local reset can alter the shared exterior coupling being tested. New interventions need an exclusion/noninterference contract, and the earlier complete-probe objection still applies.

Primary comparison: Aichernig et al., *Efficient Active Automata Learning via Mutation Testing*, identifies conformance testing as the major practical bottleneck and discusses resets/membership versus equivalence queries: https://doi.org/10.1007/s10817-018-9486-0 . The older factored-PSR comparison remains directly relevant: Wolfe, James and Singh, *Approximate Predictive State Representations*, https://www.ifaamas.org/Proceedings/aamas2008/proceedings/pdf/paper/AAMAS08_0647.pdf . Local test scopes and growing predictive structure are established; the programme's extra burden is evidence-honest positive joint recursive realization with executable interfaces.

## 6. Acceptance checklist for the next result

1. Compare on the same input observations and declared horizon; do not count simulated multinomial histogram size as physical acquisition speed.
2. State whether conclusion is full TV, bounded-monitor IPM, controller-specific utility, or model-relative TV.
3. State separately true-process promises, candidate grammar restrictions and hardware capabilities.
4. Unknown communication, scope or memory must actually be inferred; a supplied sufficient feature map is not discovery.
5. Retain positive shared temporal coupling and initial uncertainty; no independent resampling of unresolved worlds.
6. Report experiment coverage and statistical multiplicity together; merely replacing 1088 rows by 10 moments while multiplying policy coverage is not a proven gain.
7. Compare against central direct moment estimation and the last weighted full-history method. Explain what the discovered executable decomposition adds.
8. Measure computation, width and certificate size separately from samples. Finite enumeration may establish existence, not scalability.
9. Include an adversarial misspecification case passing marginal tests but failing an added joint temporal monitor. Do not interpret it as proof that a finite monitor suite is universally complete.
10. A substantial positive bounded example plus honest general theorem is acceptable. Do not certify original-contract completion or publication novelty from this audit.
