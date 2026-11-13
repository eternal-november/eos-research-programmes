# Evidence indexed coverage for learned hidden decompositions

28 October 2026. Technical bridge note. No contract amendment or novelty claim.

## Finding

A rigorous bridge is available for a **bounded hidden stochastic model class, finite external alphabets, a fixed deployment horizon, and explicitly covered experiments**. It does not require a hidden-state readout, a reset to each hidden state, or an already known component assignment. It does require independent episodes from the same unknown initialization law and a known exploration policy with support on every admitted external action.

The constructive output is a nested set of positive hidden realizations, including their unknown component counts, local states, graphs, observation maps, and action assignments. A supplied realization witness establishes the exact law of one candidate. Observable data then establish a simultaneous finite-horizon approximation guarantee for every accepted candidate and every admitted adaptive context. Exact architecture recovery, reusable physical ports, and robust controller claims need their own additional checks; none follows from fitting alone.

The basic statistical cost is large and explicit. If the exploration policy assigns probability at least kappa to each action at each observable history, the worst-case transfer multiplier is kappa^(-H). A hidden prefix-monitor example makes this multiplier sharp. This is a substantive finite-data adapter, not an efficient discovery theorem or a demonstrated new structural advantage over existing joint generative learning.

## Four claims that must remain separate

1. **Candidate realizability.** The supplied positive kernels, causal schedule, initialization, emissions, and allocation witness implement the fitted candidate law. This is a deterministic statement about that candidate.
2. **Population identification.** Exact equality of the relevant experimental laws identifies a parameter or structure only up to a stated equivalence and only under the chosen identifiability assumptions.
3. **Finite-data coverage.** With specified probability over the actual sampling experiment, the retained set contains a true presentation and every accepted candidate has a stated observable-law error on the declared experiment class.
4. **Controller use.** A particular implementation uses only its actual observations/actions, meets physical resource limits, and satisfies a quantitative specification in every admitted world. This has an existential implementation followed by a universal world quantifier, not the reverse.

The published mechanism-sparsity result and its nonparametric extension supply population results under exact observational-law equality, decoder, variability/influence and sparsity assumptions. Their qualitative span assumptions are not numerical conditioning margins, and their proposed training procedures are not universal finite-sample or global-optimization guarantees. They already learn representations, mechanisms, graphs and unknown action targets; the present adapter must not claim those achievements as new. Primary texts: [Lachapelle et al. 2022, Theorems 4–5](https://proceedings.mlr.press/v177/lachapelle22a/lachapelle22a.pdf), and [version-pinned nonparametric extension, Theorems 22, 24 and 32](https://arxiv.org/html/2401.04890v2).

## Model class and actual experimental access

Fix finite external action and readout alphabets A and Y, a horizon H, and finite resource/model bounds B. An action may have several known external channels; **which hidden component a channel influences remains unknown**. Fix a finite collection D_B of candidate discrete templates. A template specifies only a candidate number and cardinalities of local hidden states, candidate parent graph, candidate action allocation, and candidate emission/communication placement. All templates meeting B are searched, not just a supplied desired decomposition.

For each template d, let Theta_d be a compact product of stochastic simplices with any declared closed rational-polynomial constraints. Its parameters include an arbitrary joint initial hidden-state distribution, local conditional transition kernels, and finite-alphabet stochastic emission kernels. A simple subclass has

    Z_t = (Z_t^1,...,Z_t^m),
    T_theta(z' | z,a) = product_i q_i(z'_i | z_Parents(i), a_Assigned(i)),
    Y_t ~ E_theta(. | Z_t).

The local innovations are conditionally independent in this subclass, but the components need not be dynamically independent: cross-time edges and correlated initialization produce persistent dependence. A bounded shared innovation or persistent common state can instead be added explicitly to the template. Its physical storage and access are part of a typed realization witness. No exact inverse of the noisy emission map is assumed available at runtime.

This gives a genuinely hidden, unknown-decomposition family. Finite observed symbols need not identify a hidden state. Parameters and discrete templates are outputs of learning. B bounds the search universe; it does not supply the answer. Degenerate, redundant, or observationally equivalent decompositions can survive and must be reported.

The experiment consists of independent episodes, each starting from the **same unknown law mu_theta**, not from a known or chosen hidden state. A real reset protocol or independent replicated systems must justify this assumption. Within an episode, a fixed known behavior policy b chooses actions from the actual readout/action history h_t, with

    b(a | h_t) >= kappa > 0

for every action allowed in the promised deployment class. It never sees hidden states. Its independent randomization is exogenous to the environment noise. The observed episode is

    W = (Y_0,A_0,Y_1,...,A_(H-1),Y_H).

There are at most K = |Y|^(H+1) |A|^H such transcripts. Write p_theta^b for its distribution. A known rational b, such as uniform action randomization, makes each transcript probability a polynomial in the finite stochastic parameters after summing hidden paths.

These are **new named restrictions**, not hypotheses inherited from the continuous noisy-decoder baseline. No experiment is assumed safe merely because it has positive probability under b. If full-support exploration is unauthorized or unsafe, restrict A/the admitted context class or return a coverage obstruction. Independent episodes cannot be replaced without proof by arbitrary windows of one dependent trajectory.

## A data constructed nested evidence set

From n independent episodes form the empirical transcript law p_hat_n. Let TV(p,q) = (1/2) sum_w |p(w)-q(w)|. For n >= 1 set

    epsilon_n = min{1, sqrt[(K log 2 + log(pi^2 n^2/(6 delta)))/(2n)]}.

For an exact real-algebraic feasibility implementation, replace this radius everywhere by a certified rational upper bound; the same proof and all error bounds use that enlarged radius. Define

    C_n = {theta in union_d Theta_d :
           TV(p_theta^b, p_hat_m) <= epsilon_m for every 1 <= m <= n}.

The constraints include the positive normalized kernel equations, not merely a signed linear realization or an unconstrained low-rank fit. C_n is a symbolic feasible set, not a finite list purporting to list a continuum. Template enumeration and real-algebraic feasibility give an in-principle procedure: introduce auxiliary nonnegative variables for absolute values in the TV constraints, then apply a decision/quantifier-elimination algorithm to the resulting rational polynomial formulas. Such general algorithms exist; see [Perrucci and Roy, quantifier elimination over real closed fields](https://arxiv.org/abs/1609.02879). Certified witness checking is distinct from a heuristic optimizer's failure to find a witness. No polynomial-time claim is made.

**Lemma 1 — simultaneous evidence coverage.** If the true system has some theta_star in the declared class and the sampling assumptions hold, then

    Pr[theta_star in C_n for every n >= 1] >= 1 - delta.

Every equivalent true presentation in the class with the same experimental law is retained on the same event. The conclusion permits stopping after inspecting the data, selecting a template, and selecting a context after seeing the data. It does not license silently discarding surviving alternatives.

**Proof.** For each transcript subset S, its empirical probability is an average of independent indicators. The one-sided bounded-variable inequality gives Pr[p_hat_n(S)-p_star(S) > r] <= exp(-2nr^2). There are at most 2^K subsets, and TV is the maximum such difference. Allocate 6 delta/(pi^2 n^2) to time n and sum over n. Intersecting all previous balls makes the sets nested, without assuming the numerical radii themselves are monotone. This is an elementary application of [Hoeffding 1963, Theorem 2](https://www.cs.rpi.edu/academics/courses/spring06/random/hoefding.pdf).

The union bound here is only the concentration component. The substantive bridge below uses causal likelihood cancellation, explicit experimental support, positive realization feasibility, and structural separation. It does not assume that a user-supplied confidence set already solves these problems.

## The finite horizon coverage theorem

An admitted context pi is any causal randomized policy on the same actual observable history, possibly implemented by a finite-state controller, whose actions lie in the support promised by b. Its private randomness is independent of the environment. It has no privileged hidden signal and no unimplemented latent intervention. All compared systems start from their declared initialization in the same manner as the experiment.

Define the world-independent transcript weight

    L_pi(w) = product_(t=0)^(H-1) pi(a_t | h_t) / b(a_t | h_t).

It satisfies 0 <= L_pi <= kappa^(-H). Causal factorization gives

    p_theta^pi(w) = L_pi(w) p_theta^b(w).

The environment likelihood cancels because pi and b use the same external history and action semantics. Hidden dynamics and noisy emissions need not be identified for this identity.

**Theorem 2 — evidence indexed behavioral realization.** On the event in Lemma 1, simultaneously for every n, every accepted positive candidate theta in C_n, and every admitted context pi, including a data-selected pi,

    TV(p_theta^pi, p_star^pi)
        <= min{1, kappa^(-H) TV(p_theta^b,p_star^b)}
        <= eta_n := min{1, 2 kappa^(-H) epsilon_n}.

The same bound holds for any projection of the transcript and every event measurable from it. For a loss in [0,R], the expected-loss discrepancy is at most R eta_n. For a loss in [-R,R], use 2R eta_n instead.

**Proof.** Multiply the signed difference of the two behavior transcript laws by the same nonnegative L_pi, sum absolute values, and use its supremum bound. Both candidate and truth lie in the current empirical ball, so their behavior-TV distance is at most 2 epsilon_n. The calculation is pointwise in pi on the single coverage event, so no union over the uncountable policy class or additional post-selection confidence penalty is needed.

For a candidate checked with explicit numerical feasibility slack rho_n, the second bound becomes kappa^(-H)(2 epsilon_n + rho_n); it must not silently remain eta_n. A solver's unexplained residual is not a certificate.

A sufficient sample condition for eta_n <= eta < 1 is

    n >= 2 kappa^(-2H) [K log 2 + log(pi^2 n^2/(6 delta))] / eta^2.

This displays the exponential alphabet/horizon and exploration penalties rather than hiding them. An experiment-specific smaller likelihood-ratio bound sup L_pi can replace kappa^(-H). Better estimators and smaller context classes may improve this deliberately simple sufficient rate; no such improvement is claimed here.

### What observational and interventional coverage means here

Open-loop externally implemented action strings and adaptive externally implemented policies are covered. The learned graph may explain an action's target, but merely naming a new do(Z_i=z) operation does not put that operation in A or prove that existing equipment implements it. Such a port requires a physical/causal witness and its own experimental support. A context that uses a new sensor, a different initialization law, a longer horizon, or an uncovered action is outside the theorem.

Composition is valid for typed contexts whose **whole resulting experiment** remains in this class and uses at most H steps. Two certificates each starting from mu cannot automatically be concatenated without actually resetting to mu or proving state-conditional guarantees. Parallel composition does not automatically permit multiplying laws when the systems share unmodeled noise.

## Exact realization and robust physical use

Use two different objects. A **candidate realizer R_theta** is an executable generative implementation of the learned environment law. Its witness W_real(theta,R_theta,T) checks positive stochastic kernels, causal phases, initialization, emission generation, local storage, message alphabets and randomness access. A **deployed context/controller I** interacts with an environment through actual readouts and actions. A witness W_use(theta,I,T) checks that this fixed context can use the interface and meets the requested specification/resource bounds in candidate world theta. A generative emission sampler is not an inverse decoder available to I.

There are two useful conclusions.

**Nominal realization with robust external behavior.** If W_real is checked for one theta in C_n, the learned candidate has an exact positive typed realization. If a fixed admissible external-history context I has a certified event/loss prediction in that candidate, the prediction transfers to the true external behavior under the same I with eta_n. I's code and actual stored state can have exact syntactic resource bounds. Neither conclusion makes R_theta a physical realization of the unknown actual environment or makes the candidate's latent decomposition the true physical decomposition.

**Robust interface use.** To assert that an implementation can use a physical interface and satisfy the property in every admitted world, the required quantifier is

    exists one I such that for every theta in C_n,
        there exists a checkable W_use(theta,I,T) for the same I and actual external ports,
        and the promised property holds.

The witnesses may differ as mathematical explanations; I may not consult the unknown true theta or change wiring by oracle. The weaker statement “for every theta there exists I_theta” is not robust deployment. If the claim is just a bounded external event probability, a nominal prediction certificate with its eta_n slack can suffice. If it concerns physical ownership of state, availability of latent information, communication, or initialization resources, observational TV cannot supply the missing witness. A separate claim about a common physical environment realizer likewise requires an explicit common-realizer witness; it must not be inferred from controller transfer.

**A constructive sufficient controller check.** Fix a finite-state context I with rational stochastic kernels, actual readout/action access, and a bounded-horizon success event S explicitly represented as a transcript subset or finite event monitor. Either (a) certify in one accepted candidate that Pr_theta^I(S) >= p + eta_n, which implies Pr_star^I(S) >= p, or (b) certify that the semialgebraic counterexample set

    {theta in C_n : Pr_theta^I(S) < p}

is empty. For finite-state I and the finite polynomial hidden class, the event probability is obtained by a finite sum of hidden/controller paths and is polynomial in the stochastic parameters. Thus (b) is a concrete feasibility check, not an assumed coverage oracle. If I is to be synthesized, fix a finite controller-memory/code universe first and use the same existential-I/universal-world order; continuous controller probabilities yield a quantified real-algebraic problem. Any additional structural W_use must itself have an effective finite witness encoding for this decision route to apply. Otherwise the structural check remains a separately named unresolved obligation. This is a downstream consequence of the discovered ambiguity set, not a replacement of decomposition discovery by suitability testing.

For a bounded objective J, the honest evidence interval is

    [inf_(theta in C_n) J(theta,I), sup_(theta in C_n) J(theta,I)].

As evidence is refined by intersection these intervals contract and universal claims remain valid; feasible implementation sets can expand because fewer worlds need covering. A new model restriction or a new experimental assumption is not evidence refinement unless justified separately. One cannot preserve the confidence level by keeping only the most attractive fitted model.

## Structure, gauges and positive factorization stability

### Equivalence must preserve the claim being transported

Local state-label permutations and component permutations are harmless gauges only when their port, emission, initialization and resource roles are transported. External action labels have fixed operational meanings and cannot silently be permuted. A broad latent diffeomorphism or equality of observed laws is not automatically a distributed typed-interface equivalence.

Retain observationally equivalent but physically inequivalent realizations as ambiguity. For example, augment any hidden process with an unobserved independent persistent bit: the observations can be identical although the physical state description differs. A minimal-resource convention may choose one presentation, but the data alone have not proved that the discarded hidden subsystem does not exist. Bounds/minimality are legitimate declared model assumptions, not facts learned from those identical observations.

### Computable rejection margin for a competing structure family

For a compact competing template family F define its behavior-law gap

    Delta(F;theta_star) = inf_(theta in F) TV(p_theta^b,p_star^b).

If Delta > 2 epsilon_n, then F has no member in C_n. Conversely, overlapping observational laws cannot be separated by these data. The practical certificate is infeasibility of F intersect C_n; Delta need not be handed to the learner. Finite template enumeration can therefore identify a quotient class when every inequivalent class is separated, while returning an explicit ambiguity set otherwise.

Supergraphs containing zero-effect edges overlap their subgraphs. Without a nonzero-effect convention, exactly recovering a displayed support is ill-defined. A positive effect threshold can make an exact-support family closed, but a hidden mechanism margin alone is insufficient when the readout erases that effect. The required discovery separation is ultimately experimental/observable, not merely an algebraic nonzero entry.

### What quantitative inverse stability requires

Let G be a finite group of claim-preserving label permutations and let d_G be the minimum, over G, of a continuous parameter metric (on a finite disjoint union of compact template spaces when needed). Thus the quotient is Hausdorff and d_G is continuous. More general gauges need these properties checked separately. On a compact class that is identifiable modulo G under the chosen H-step experiment, define

    omega(r) = sup{d_G(theta,theta') :
                  TV(p_theta^b,p_theta'^b) <= r}.

Compactness and injectivity on the quotient imply omega(r) -> 0: otherwise take convergent subsequences with behavior distance tending to zero and parameter distance bounded away from zero, contradicting quotient identification. Every pair in C_n then differs by at most omega(2 epsilon_n). This is a set-valued continuity statement, not a universal linear rate.

An independently certified inverse bound

    TV(p_theta^b,p_theta'^b) >= beta d_G(theta,theta')

gives the quantitative radius 2 epsilon_n / beta. Neither population identifiability nor a small empirical residual supplies beta. Near nonidentifiability beta can approach zero. If quotient identification fails at horizon H, omega need not tend to zero at all. Finite polynomial bounds permit expressing the displayed minimization/universal inequalities as real-algebraic questions, but that observation supplies no efficient algorithm or favorable constant.

### Forward stability of already positive local factors

For two realizations on the same aligned template, suppose their initial laws differ in TV by at most r_0, each corresponding local conditional kernel differs uniformly by r_i, and each emission row differs by r_E. Successive maximal couplings give, for every common external policy,

    TV(p_theta^pi,p_theta'^pi)
        <= min{1, r_0 + H sum_i r_i + (H+1) r_E}.

This uses product-kernel coupling only conditional on the same current state/action; it does not assume the stationary components are independent. A declared shared innovation can be coupled as an additional factor with its own error term. This is forward positive-factorization stability. It must not be reversed into stable factor recovery without an inverse condition.

An approximate signed table is not a stochastic realization. For one signed row v with negative mass nu, row sum s, and positive-part mass c=s+nu>0, clipping and normalizing gives q=v_plus/c and

    ||q-v||_1 = |1-c| + nu <= |1-s| + 2nu.

If this repair is applied locally it preserves the chosen local input scope and produces valid local stochastic rows. The repaired assembled law must then be evaluated against the evidence constraints, with its error propagated. Small algebraic factorization residual alone does not ensure small distance to an exact positive factorization, nor preserve an exact structural property at a singular boundary. Explicit nonnegative normalized witnesses and certified residuals avoid this gap.

### An explicit positive factorization singularity

For 0 <= d < 1/2 consider the binary joint-output table

    P_d = [[1/4 + d^2, 1/4 - d^2],
           [1/4 - d^2, 1/4 + d^2]].

An exact nonnegative product-mixture realization samples a fair hidden bit U; conditional on U, the two outputs are independent Bernoulli(1/2+d) when U=1 and independent Bernoulli(1/2-d) when U=0. All local probabilities are strictly positive for d<1/2. Yet

    TV(P_d,P_0) = 2d^2,
    det(P_d) = d^2.

For d>0, ordinary matrix rank is two, hence no one-term nonnegative product factorization exists; the displayed two-term factorization is minimal. At d=0 a one-term independent product suffices. Thus the exact number of shared latent mixture states jumps from one to two at an arbitrarily small observational perturbation. This is a statement about that product-mixture interface, not an unrestricted simulator-memory lower bound.

In the displayed family, after quotienting the swap U<->1-U and choosing d>=0, parameter error d corresponds to observed TV error 2d^2. Any inverse-Lipschitz constant therefore diverges as d approaches zero; the square-root modulus is exact for this parametrization at zero. A rank-one approximation with small nonzero residual remains a useful approximate law but is not an exact rank-one realization of P_d. This elementary computation supplies a concrete positive-factorization stability boundary without invoking a general instability slogan.

## Sharp boundaries and distinguishable failures

### The exploration multiplier is necessary in general

Choose a prescribed H-action word u. A finite hidden prefix monitor records whether the actions so far agree with u; it emits a constant symbol before the end. Two worlds differ only in the final output after the entire word u: one emits 0, the other 1. Under independent exploration assigning probability kappa to each required action,

    TV(p_0^b,p_1^b) = kappa^H,
    TV(p_0^u,p_1^u) = 1.

A bounded hidden transducer with O(H) prefix states realizes this example. Thus no smaller universal behavior-to-all-context TV multiplier can hold for this class. No revelation of the hidden prefix state is required.

If b never executes u (or an action needed for it), the behavior laws are identical. The terminal output can represent a catastrophe. The data then cannot certify that attempting u is safe. Universal coverage of unexplored hazards and a guarantee that the required experiments are harmless are both absent, for a precise support reason.

### Qualitative identifiability does not give a uniform finite sample assignment guarantee

Consider bounded actions a=(a_1,a_2) in {0,1}^2. In world j in {1,2}, let fresh latent states obey

    Z_(t+1) | a_t ~ Normal(e a_(t,j), 1),
    X_(t+1) = Z_(t+1) + N_(t+1),
    N_(t+1) ~ Normal(0,sigma^2),

with e>0 and identity decoder. Every positive e gives a nonzero identifiable action influence in the full conditional law; j is the unknown target assignment. For any adaptive action design using M observations, Gaussian KL chain rules give

    KL(P_1 || P_2) <= M e^2 / [2(1+sigma^2)],
    TV(P_1,P_2) <= e sqrt(M) / [2 sqrt(1+sigma^2)].

For any binary assignment estimator the sum of its two error probabilities is at least 1-TV. Choose e=sqrt(1+sigma^2)/(2sqrt(M)): the maximum error is then at least 3/8. Both alternatives have a nonzero edge; the obstruction is not merely testing a zero-edge boundary. This is an original elementary calculation using the standard [KL-to-TV inequality](https://arxiv.org/html/2202.07198v2#S1); it demonstrates the need for quantitative signal/excitation assumptions, not a failure of population identifiability. For fixed exogenous action sequences this is a scalar Gaussian subclass of the published mechanism-sparsity assumptions: T(z)=z is minimal and invertible, the active action has nonzero finite-difference influence e, the temporal span is vacuous, and the singleton active child supplies the graphical separation condition. The same example fits the discrete-action nonparametric influence condition. The sources state conditional-law identifiability, not this adaptive-experiment guarantee: when actions depend on noisy observations, the displayed adaptive KL bound uses our explicit causal kernel sampling semantics and KL chain rule, rather than claiming the source assumes noise independent of all future feedback actions. The fixed open-loop subclass already establishes the absence of a uniform finite-sample margin.

### Quantization does not extend the theorem to continuous TV

For any fixed finite partition of a continuous readout domain, two distributions can assign equal probability to every bin while putting their mass on disjoint subsets inside every bin. Their quantized laws agree and their original laws have TV=1. Consequently, finite-symbol certification covers the quantized observation interface only. A continuous-to-finite extension needs a declared approximation norm, tail/smoothness restrictions and a proved discretization error. Similarly, no finite-Hankel-rank premise is inferred from continuous latent dimension. The previous rank-conditioned valid-law lemma is applicable only after its actual finite-rank, conditioning and validity hypotheses have been independently verified.

### Status vocabulary

- **Accepted candidate:** explicit positive realization and evidence feasibility certified; observable errors and scope displayed.
- **Insufficient coverage:** initialization, action support, horizon or sample precision does not justify the proposed context; retain uncertainty rather than claim failure of the world.
- **Structural ambiguity:** two inequivalent template/witness families survive. This can coexist with a useful robust external contract.
- **No certified positive realization:** the requested template/resource bound is infeasible, or the solver has not certified feasibility. Distinguish proved infeasible from computationally unresolved.
- **Empty evidence set:** incompatible with the declared class and sampling assumptions on the high-probability event. This is evidence of some assumption/model failure, not automatic identification of which one failed; the delta-tail event remains possible.
- **Physical interface obstruction:** a valid candidate law exists, but no witness establishes the claimed local access, causal timing or resource bound.
- **No common implementation:** each admitted world may permit its own implementation, but the robust existential-universal claim fails.

## Epistemic uncertainty and physical resources

Theta_star is an unknown fixed world parameter. Keeping a confidence set, prior, posterior, or alternative factorization proofs does not by itself create a physically stored controller state. Charge physical local state, persistent channel state, retained random seeds, memory actually used for online belief updates, and any implemented decoder/communication procedure. Charge search, enumeration, proof generation, algebraic feasibility and certificate storage/verification separately as offline costs unless deployed at runtime.

A simulator of a Bayesian mixture may sample theta once and retain it so that its synthetic outputs remain correlated. That can be memory of that simulator. It does not prove that the real controller or environment stores a Bayesian label, nor establish a physical-memory lower bound by definition. Ontic fresh innovation and epistemic uncertainty about a fixed mechanism must remain distinct.

## What this resolves and what remains open

The core concentration, likelihood-transfer, forward-coupling, signed-row repair and Gaussian lower-bound constants were independently checked in the associated bridge review. The note establishes an explicit hidden-data-to-coverage route with selection-valid refinement, common-context transfer, positive witness requirements, a quantitative factor-error bound, gauge-aware ambiguity, and concrete impossibility boundaries. The sampling class is learnable in finite-horizon observable law; exact decomposition identification is conditional on an additional observable separation/identifiability condition and can honestly remain unresolved.

It does not establish efficient joint discovery, unrestricted continuous-model confidence, guarantees after arbitrary unmodeled distribution shift, physical uniqueness, universal safe exploration, an infinite-horizon theorem, or an advantage supplied specifically by the programme's structural machinery. A matched comparison should identify which part of the typed witness or structural reasoning strictly improves the output/cost over the baseline plus standard finite-model inference. Until that is shown, this is a rigorous integration candidate and a clear boundary map, not closure of the full research target.
