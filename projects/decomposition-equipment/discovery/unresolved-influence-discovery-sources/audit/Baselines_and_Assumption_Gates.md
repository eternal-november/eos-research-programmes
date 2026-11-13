# Audit: discovery with unresolved influences

29 October 2026. A targeted primary-source audit, not an exhaustive novelty determination.

## Executive assessment

The approved target is worthwhile: discover a useful task component before identifying the whole mechanism, while retaining incompatible explanations and reporting when an additional permitted experiment can resolve them. But neither universal validity across data-compatible models, task-preserving partition refinement, symbolic state-space avoidance, nor invariant-observable closure is itself a new mechanism. The burden is their constructive connection to incomplete readouts and physically meaningful decomposition witnesses.

The proposed task-generated algebra route is mathematically sound in principle, but needs a separate data-to-uncertainty theorem. Otherwise it is a standard reduction of a supplied parametric model. The proposed extremal-mixture route can establish hidden-effect independence without a separating probe, but exact saturation of known bounds is a strong replacement identification assumption. A useful theorem must expose this rather than advertise assumption-free hidden-influence discovery.

## 1. Closest established baselines

### Data informativity

Van Waarde, Eising, Trentelman and Camlibel formulate analysis/control over all systems consistent with the observed data, including cases where unique system identification is unnecessary. Thus “find something valid across all remaining explanations” is an established organizing principle. Their original results emphasize linear systems; this does not subsume the intended nonlinear decomposition construction, but it does subsume its basic quantifier structure.

Primary source: https://arxiv.org/abs/1908.00468 (v3, 2020). Accessible tutorial: https://www.math.rug.nl/~trentelman/psfiles/tutorial.pdf .

### Symbolic and parametric probabilistic bisimulation

Dehnert, Katoen and Parker compute bisimulation quotients directly from guarded-command descriptions using SMT, avoiding prior construction of the entire reachable state space. Their method is explicitly applicable to parametric Markov chains. Therefore symbolic task partition refinement over a compact supplied transition program, even with exponentially many concrete states, is not enough to establish a new discovery contribution.

Primary source: https://www.cs.ox.ac.uk/people/david.parker/papers/vmcai13.pdf .

### Constrained exact lumping and Koopman discovery

CLUE computes a smallest linear state reduction preserving supplied observables for polynomial ODEs, using common invariant-subspace methods despite nonlinear dynamics. Haseli and Cortés give a data-driven iterative method for the maximal Koopman-invariant subspace inside a supplied dictionary. These are not identical to finite stochastic subalgebra discovery: deterministic lumping, linear observable subspaces, and stochastic quotient algebras differ. Nevertheless, “close task observables under dynamics and derive a reduced system” must be compared explicitly against them.

Primary sources:
- Ovchinnikov, Pérez Verona, Pogudin and Tribastone, CLUE: https://arxiv.org/abs/2004.11961 .
- Haseli and Cortés, Learning Koopman Eigenfunctions and Invariant Subspaces from Data: Symmetric Subspace Decomposition: https://arxiv.org/abs/1909.01419 (v4, 2021).

### Reduction without whole-state construction

Cardelli, Tribastone, Tschaikowski and Vandin derive a lumpable quotient from chemical reaction syntax, with polynomial partition refinement in species/reactions rather than enumerated population states. This is another direct baseline for claims that a growing nonlinear interacting family can be reduced without building its exponentially large state model.

Primary source: https://arxiv.org/abs/1707.02132 .

### Causal identification under unresolved architecture

Jaber, Zhang and Bareinboim identify causal effects over a partial ancestral graph representing an equivalence class. Their complete algorithm either identifies the effect or gives nonidentifiability structure. This does not solve component discovery, but it means “shared answer across indistinguishable architectures, or an obstruction” is not a new causal principle.

Primary source: https://proceedings.mlr.press/v97/jaber19a.html .

### Data-driven abstraction and compositional transfer

Makdesi, Girard and Fribourg build a minimal set-valued approximation from transitions of an unknown monotone system and a finite alternating-bisimulation abstraction. Samari, Nejati and Lavaei develop data-driven compositional abstractions with unknown interconnection topology, while still treating the network as individual agents. These should prevent overstating “unknown topology” or “data-driven abstraction” as unique features. The proposed target differs only if component grouping itself and its interface are actually discovered.

Primary sources:
- https://proceedings.mlr.press/v144/makdesi21a.html .
- https://arxiv.org/abs/2411.06743 (v2, March 2026).

A recent coalgebraic behavioral-transfer paper is also relevant to the larger programme, not a replacement for the discovery theorem: Zhang, Luo and Baltieri, https://arxiv.org/abs/2606.25357 (v2, August 2026). It treats abstraction as a homomorphism and transfers behavioral structures; its stated contribution is not architecture discovery from incomplete readouts.

## 2. Mathematical distinctions the theorem must retain

Let U(D) be the compatible positive mechanism family and A a finite algebra of state functions containing the task observables.

1. K_theta A subset A for every theta in U(D) supplies a common quotient architecture. Its reduced transition law may still depend on theta.
2. The stronger condition (K_theta - K_theta')f=0 for every f in A and every theta,theta' identifies a common reduced transition law.
3. Validity pointwise in a hidden influence is stronger than Markov closure after averaging it under one experimental law.
4. A common quotient q valid in every world is stronger than each world separately admitting some q_theta. If world-specific maps are used, their relationship to the observed interface must be stated and witnessed.
5. An invariant linear space of expected observables is not automatically a stochastic state quotient. On a finite state set, the unital multiplicatively closed function algebra corresponds to a partition; closure of only first moments can miss joint evolution.
6. A quotient plus arbitrary residual disintegration is a mathematical reconstruction. It is not automatically a physically isolated subsystem with bounded outgoing communication. Charge residual state, synchronization, interface sensing and initialization.

## 3. Incomplete data and invisible effects

If the universe allows arbitrary hidden perturbations of next-task probabilities at contexts or modes never constrained by the experiment, those perturbations can leave all available readouts unchanged while destroying pointwise task autonomy. A universal theorem cannot certify their absence. It must either restrict their admissible action, prove cancellation from evidence and positivity, retain them as an interface, weaken the guarantee to the experimental distribution, or return an obstruction.

This is not a claim that every nonidentified system lacks useful quotients. Uncertainty may lie entirely in directions annihilated by a discovered quotient. The useful result is to establish that annihilation from the stated evidence and universe without assuming the quotient in advance.

Do not mix deployment and observational claims. A counterexample exploiting an unvisited mode establishes failure outside experimental support, not failure to predict a fully known law under exactly the same input and initialization regime.

## 4. Extremal-mixture route: exact and approximate conclusions

Suppose an observed response is p = sum_h w_h p_h, all p_h >= e, and p=e. Then every h with w_h>0 has p_h=e. This elementary exposed-face argument can identify a task-relevant response while leaving the hidden decomposition unresolved. It does not need a full-rank separating probe.

Its costs are important:
- The bound e must be known and valid conditionally on every admitted hidden mode, context, and relevant history.
- Exact equality p=e is a boundary condition, not a generic interior identification regime.
- Zero-weight hidden modes remain unrestricted; continuous modes give an almost-everywhere statement unless regularity/support assumptions strengthen it.
- If p<=e+delta, then p_h<=e+delta/w_h. A uniform pointwise bound requires w_h>=mu>0. Without such a floor, an arbitrarily rare dangerous mode is compatible with arbitrarily small average slack.
- A future shift of hidden-mode weights requires its own support or density-ratio guarantee.

A strong demonstration should retain truly unidentified mechanisms that affect some measured behavior, show the discovered quotient is not supplied, and include an interior approximate case. If every useful success requires exact saturation at a perfectly calibrated noise bound, describe it as an exact conditional discovery family rather than broad physical validation.

## 5. Algebraic and computational traps

Universal polynomial equality must be tested on the actual positive feasible set, not merely by matching unconstrained formal coefficients. Shared constraints can create cancellations. Conversely, the ideal generated by displayed polynomial equations need not equal the real vanishing ideal of the semialgebraic feasible set. Positivity faces can impose further equalities. General feasibility, real radical computation, and minimal interface search must not be called cheap.

Even checking a proposed quotient can be hard with succinct mechanisms. For a Boolean formula phi(z), take state (a,t,z), task a, and a positive next-task Bernoulli law with success probability e+(1-2e)(a XOR (t AND phi(z))), where 0<e<1/2; give all other next coordinates fresh positive distributions. The task-only partition is a strong quotient iff phi is unsatisfiable. If phi is satisfiable, changing t at a satisfying z changes next-task behavior; if unsatisfiable, the dependence vanishes. Thus arbitrary compact Boolean transition descriptions do not make universal quotient verification polynomial. A violating pair is short; certifying its absence needs additional structure or a proof certificate. This is an elementary reduction supplied here, not a literature novelty claim.

For sparse polynomial methods, count dictionary size after products/composition, degree growth, term growth, positivity representation, constraint width, and witness size. A fixed-degree initial dictionary need not remain bounded under repeated closure. Distinguish output-sensitive termination from polynomial complexity in raw readout length.

## 6. Recommended acceptance gates for this milestone

A substantive combined result should establish all of the following in at least one honest model universe:

A. Construct the compact compatible-mechanism constraints from the actual allowed readouts, rather than hand the learner a whole model or an already reduced state dictionary.
B. Discover a task quotient and a recursively usable interface that are absent from the input; give a coarseness or meaningful optimality statement within an explicit representation class.
C. Keep hidden directions genuinely unresolved and show which remain irrelevant, conditional, or obstructive.
D. Preserve shared parameters/hidden occurrences across components and time; no independent per-row or per-visit completion.
E. Produce positive common realizations, not only linear expectation identities.
F. Exhibit a growing nonlinear interacting family with a strict reduction and an observationally indistinguishable failure pair, with no specially revealing reset or preassigned solution partition.
G. Separate exact-law, finite-sample, distributional and pointwise guarantees. Quantify the instability of extremal certificates.
H. Compare directly with data informativity, symbolic parametric bisimulation, CLUE and dictionary-based Koopman identification.

The likely defensible contribution is the data-to-certificate integration and its specific nontrivial family, not the invariant-algebra closure or universal-compatibility definition alone. A genuinely new general mechanism has not been established by this audit.

## 7. Additional audit: moment-resolution dichotomy

The sharpened candidate has a more substantial conclusion than invariant closure alone. Let X={-1,+1}^n, V_d the span of Walsh monomials of degree at most d, and suppose the data identify T f for every f in V_d. Consider ALL stochastic kernels with those conditional moments, optionally with the same fixed positive stationary law pi. Assume this completion class contains a strictly positive kernel.

Claim checked: every proper deterministic partition that is a strong quotient for every completion has its entire block-constant function algebra contained in V_d. Here proper means not the discrete identity partition. The discrete partition is always a quotient and is explicitly exempt.

Proof: a proper partition has distinct source states x,x' in one block. If some output block indicator b is outside V_d, its orthogonal projection onto V_d-perp is a nonzero signed vector h with <h,b> nonzero. Since 1 belongs to V_d, h has total mass zero. Add epsilon h/pi(x) to row x and subtract epsilon h/pi(x') from row x'. All known conditional moments stay fixed. Weighted row cancellation preserves pi. Strict positivity permits a nonzero sufficiently small epsilon. The two source rows' aggregate probabilities for b change in opposite directions, so at least one of the compatible perturbed kernels violates quotient closure. Without a stationary constraint, perturbing one row is already sufficient.

Consequently, generate the smallest unital function algebra containing the task and closed under the identified action T while it remains inside V_d. If closure remains there, it defines an identified quotient. If algebraic or dynamic closure leaves V_d, there can be no proper robust quotient containing that task. This is a genuine completeness/obstruction result for the declared moment-completion universe, not merely a sufficient reduction algorithm.

A sharper size consequence: any such proper quotient has at most 2^d blocks. Every nonzero degree-at-most-d Boolean-cube polynomial has support at least 2^(n-d). Apply this to each block indicator and sum disjoint supports. The support lemma follows by induction: write f=g+x_n h. If h=0, duplicate the support of g. If h is nonzero of degree at most d-1, every nonzero h evaluation contributes at least one nonzero evaluation of f over the last bit, giving the same bound. Thus a task already requiring more than 2^d classes forces the identity alternative in this universe.

Scope and contribution:
- This theorem turns the limitation of low-order evidence into an exact resolution barrier and supports constructive obstruction witnesses. That is stronger and more informative than the general data-informativity definition or task-closure algorithm alone.
- Its proof is elementary finite-dimensional duality plus positivity. No exhaustive prior-art search has established novelty of this exact formulation; it should not be called a new general algebraic mechanism on that basis.
- Observing a Markov state X and recovering polynomial conditional moments is a major declared universe. The unknown part here is joint transition coupling, not unrestricted hidden-memory exterior dynamics.
- Learning conditional moments through Gram inversion needs a bounded current-degree realization promise, moment coverage and conditioning. Without that promise, finitely many mixed moments need not identify the conditional functions.
- Maintaining a known stationary law does not neutralize the obstruction because paired source-row perturbations preserve it. This is a useful strengthening worth retaining.
- With independent final-bit noise, a fixed-degree Gram bound can be polynomial in n, but not dimension-free: even independent identically biased bits have a degree-one Gram matrix (including the constant) whose smallest eigenvalue decreases on the order of 1/n.
- A positive noise-structured stress family can escape the obstruction only by restricting the completion universe. Independent final noise and extremal pre-noise constraints exclude the perturbations available in the full stochastic moment-completion class. Strict positivity of the observed noisy kernel does not remove those additional constraints. Describe this as a stronger structural promise yielding more inference, not as defeating the impossibility under unchanged assumptions.
