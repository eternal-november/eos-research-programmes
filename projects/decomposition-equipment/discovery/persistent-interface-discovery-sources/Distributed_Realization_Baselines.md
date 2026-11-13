# Distributed realization baselines and the additional theorem worth targeting

**Audit date:** 28 October 2026. **Status:** primary-source research plus explicit mathematical reductions; proposed theorem below is a research target, not proved. Target: jointly discover unknown components and finite persistent interfaces from noisy action/readout records or a learned global predictor. Neither true partition, local mechanisms nor port alignment is input.

## Executive finding

Existence of a bounded distributed realization is too weak a novelty target. With finite alphabets and explicit state/message bounds it reduces to finite architecture enumeration plus finite-state equivalence, or to an existential real-algebraic feasibility problem for stochastic kernels. Exact global predictive identification does not identify physical decomposition. Even minimum asynchronous realizations need not be unique.

The promising additional problem is **budget-preserving compatibility of several independently discovered, nonnested decompositions of the same controlled process**: discover which can coexist through dynamically stable typed interfaces, give an explicit common implementation when they can, and an observable crossing witness when they cannot. A substantial result must beat full global-state enumeration, expose a structural obstruction, or obtain quantitative robustness—not merely rename feasibility or compositional verification.

## 1. Asynchronous realization: already substantially stronger than a vague component claim

### Zielonka (1987)

Input: a fixed finite distributed alphabet, i.e. process set and action domain map, and a regular language closed under the commutations induced by disjoint domains. Output: a finite asynchronous automaton realizing that language. Local process states persist; shared actions synchronize participating states. This already constructs component mechanisms from global behavior, but the intended architecture/independence relation is supplied. It is a language result, not a noisy identification or probabilistic realization result. [Original paper, *Notes on finite asynchronous automata*](https://www.numdam.org/item/ITA_1987__21_2_99_0/).

**Exact reduction when architecture is unknown (our deduction).** For a bound of k processes, enumerate the at most `(2^k-1)^|Sigma|` nonempty action-domain assignments, reject architectures violating explicit wiring budgets, and test induced commutations on the minimal DFA. For each survivor use Zielonka. This discovers some architecture without a supplied true partition. It does **not** guarantee a prescribed local-state bound; enforcing that bound is a further finite enumeration of local automata. A single process always realizes a DFA, so an unqualified existence claim is vacuous. Require nontrivial locality, allowed action access, limits on shared actions and message/state budgets.

### Safe closed execution: Ștefănescu–Esparza–Muscholl (2003)

Their Theorem 2 characterizes exact safe asynchronous realization using regular trace languages that additionally are prefix-closed and safe-branching: independently enabled actions can jointly execute. Proposition 2 gives a minimal-DFA criterion. Their different problem of finding a safe implementable **sublanguage** of a supplied specification, using every action, is undecidable (Theorem 3); the restriction to subautomata is NP-complete (Theorem 4). Input architecture is still supplied. [Primary conference paper](https://archive.model.in.tum.de/um/bibdb/esparza/concur03.pdf).

**Why it matters:** a persistent implementation is not automatically obtained by recognizing accepted traces. Do not conflate language recognition, safe execution, controller synthesis against an environment, and stochastic generative realization. Finite resource bounds make exhaustive implementation search possible but do not defeat the unbounded undecidability theorem in its original setting.

### No canonical minimum decomposition in general

Bruschi–Pighizzini–Sabadini exhibit a recognizable trace language with no unique minimum asynchronous automaton; they obtain uniqueness under the special condition of transitive dependency. Thus an unconditional claim that behavioral minimality determines *the* recovered distributed organization is already ruled out. [Primary 1994 article](https://doi.org/10.1006/inco.1994.1010).

Target output should be an equivalence/refinement class, Pareto frontier, or chosen optimal representative. A unique physical architecture requires extra identifiable intervention/locality assumptions, not merely choosing a complexity penalty.

## 2. Positive and structured stochastic realization

### Positive realization is not ordinary predictive rank

Anderson's 1999 problem starts from probabilities of all finite output strings and asks for a finite-state hidden Markov realization. Hankel matrices and invariant polyhedral cones are central; this directly absorbs any proposal whose novelty is merely replacing a global linear predictor by a finite positive stochastic state model. [Primary article metadata and abstract](https://doi.org/10.1007/PL00009846); [author's institutional record](https://researchportalplus.anu.edu.au/en/publications/realization-problem-for-hidden-markov-models/).

A stronger general cone formulation is classical: a positive realization corresponds to a finitely generated, shift-invariant positive cone in a quasi-realization. **Do not call a static nonnegative Hankel factorization sufficient:** persistence requires compatibility with every one-symbol update. Likewise finite linear predictive dimension does not by itself imply a finite HMM. Vidyasagar's *The Complete Realization Problem for Hidden Markov Models: A Survey and Some New Results* explicitly discusses these distinctions and warns that a cone existence condition may only restate realization unless it yields a construction. The author-hosted PDF is indexed but currently redirects on direct opening; this audit therefore does not assert a newly checked theorem number from it. [Indexed author PDF](https://personal.utdallas.edu/~mxv091000/Research/hmm-full.pdf).

### Generic minimal HMM recovery is already quantitative

Huang–Ge–Kakade–Dahleh assume a stationary finite-alphabet process generated by an HMM of order at most k, with transition/emission parameters in general position. Exact probabilities of all strings of length `N > 4 ceil(log_d k)+1` suffice for their generic minimal HMM and quasi-HMM realization results. The algorithms recover actual HMM parameters, not just predictions. Their empirical analysis has conditioning dependence; a small required window is not a uniform sample-complexity guarantee. No decomposition into unknown interacting components/ports is produced. [Primary paper, including Theorems 1–4](https://arxiv.org/pdf/1411.3698).

**Structured extension baseline (our deduction).** Bound component counts, each local-state/message cardinality, and specify a synchronization semantics. Enumerate graph, channel/action ownership and message routing. Each candidate's global kernel is a polynomial in local kernel entries. Add nonnegativity, stochastic normalization, initialization and permitted-local-dependence equations. Matching a known finite-dimensional global predictor is finite algebraic feasibility; merely adding factorization equations does not escape the baseline.

Important distinction: the minimal number of hidden states is not the same optimization as minimal aggregate local memory, minimal maximum port memory, minimum communication rate, or a Pareto optimum across these costs. State the chosen resource order explicitly.

## 3. Predictive state factorization

Wolfe–James–Singh's *Approximate Predictive State Representations* introduces factored PSRs to trade compactness for predictive accuracy; its theory controls approximation error under its assumptions and experiments learn from a single trajectory. It is direct prior art against “factor a learned global predictor into smaller predictive pieces” as a novelty headline. These pieces are not automatically finite-state physical mechanisms or finite message protocols. [Primary 2008 paper](https://web.eecs.umich.edu/~baveja/Papers/Wolfe_AAMAS08.pdf).

The PDF is indexed with substantive abstract/text but repeatedly timed out on direct fetch in this audit. Therefore no detailed theorem-specific constants or hypotheses are claimed here. In particular, do not transfer its bounded-error claim to arbitrary finite interfaces, arbitrary policies, or unobserved interventions.

## 4. Network reconstruction supplies the right impossibility intuition

Gonçalves–Warnick show that even perfect input–output transfer knowledge does not generally determine the Boolean dynamical network; additional structural information is required. Their dynamical structure functions retain dependence among specified measured variables, rather than treating arbitrary state coordinates as physically meaningful components. [Primary published article](https://doi.org/10.1109/TAC.2008.928114); [accessible authors' earlier formulation](https://arxiv.org/pdf/q-bio/0610008).

Hendrickx–Gevers–Bazanella's partial-node measurement identifiability result explicitly assumes known topology and a known excitation at each node. It can identify transfer functions from a subset of node measurements, but cannot be cited as solving the present unknown-component/unknown-port task. [Primary institutional record and article](https://research.dial.uclouvain.be/entities/publication/9cb8bab1-cb9e-4462-b76d-013633715a01).

**Consequence for this project:** action richness helps only after specifying what interventions mean physically and which readouts they can affect. An arbitrary action label supplied to a monolithic learned predictor does not identify where it enters an unknown mechanism.

## 5. Strongest exact reduction: global predictive model → bounded distributed realization

This is a baseline construction, not an innovation claim.

Let the known controlled predictor have rational linear representation `(alpha, {M_ao}, beta)` of dimension r, giving action-conditioned observation-string weights. Candidate architecture A, with all persistent local and port states included, expands to N global states. Fix a timing convention so its symbol matrices `T_ao(theta)` are polynomial in finitely many local stochastic parameters theta. Feed-forward within-step wiring, or an explicit finite scheduler/microstep state, avoids an implicit algebraic feedback loop.

For each enumerated architecture impose:

1. Probability/simplex constraints for local transitions and initialization.
2. Locality: entries depend only on permitted local state, incoming port states and permitted actions.
3. Resource limits, with port memory counted as persistent state—not free global scratch space.
4. Equality of string weights for every action/observation word of length at most `r+N-1`.

**Why finite matching suffices:** form the block-diagonal difference representation of dimension `r+N`. The reachable row-span generated from its initial row stabilizes by length `r+N-1` (earlier if its rank is smaller). If its terminal column annihilates all these rows, it annihilates every continuation. Thus the finite polynomial constraints enforce equality at every horizon. This is the standard weighted-automaton linear-span idea; Tzeng gives polynomial-time equivalence testing for explicit probabilistic automata. [Primary algorithm paper](https://doi.org/10.1137/0221017).

Existential real quantifier elimination now decides each bounded candidate. A finite union handles architecture discovery, action-domain assignment and port alignment. For finite rational grids, direct enumeration is enough. If the learned predictor is not valid globally, a successful stochastic realization certifies that it is; failure can instead mean predictor invalidity or budgets too small.

This route is exact for finite rational/algebraic encodings. It does not automatically cover continuous outputs, arbitrary real black boxes, unbounded scheduling, or unbounded messages. Exact real-valued probability parameters also do not give a finite-bit implementation without an encoding or approximation budget.

### Noise changes the claim, not the basic reduction

Finite data cannot establish exact all-horizon equivalence. One can constrain finite-word probabilities to confidence intervals, but then the answer is “a model consistent with these intervals,” not identified physical components. Uniform confidence requires sampling/coverage assumptions; a behavior policy may never excite decisive action sequences. All-horizon approximate error additionally needs contraction/mixing/stability or a specified horizon. No continuity argument upgrades a finite fit into persistent accuracy for free.

## 6. Ambitious concrete additional theorem: typed crossing realization with local obstruction witnesses

### Proposed target (not established)

Input: a learned controlled predictor with a verified finite-test error envelope; finite observable action/readout channels; budgets q for local/port states; allowed locality/cost rules; and a separation/conditioning margin eta. **No true coordinate partition, local kernels, or alignment is supplied.** Candidate decompositions must be inferred from the predictor's observable continuation structure.

For a sharply restricted but interacting class—for example locally observable finite stochastic systems with bounded interaction width w—prove an algorithm that:

- discovers feasible component/port decompositions up to stated behavioral equivalence;
- constructs typed continuation interfaces whose one-step updates are closed and whose message cardinalities respect q;
- for two discovered nonnested descriptions, constructs a common dynamically valid refinement **without silently multiplying every global state space**, or produces a bounded observable crossing witness showing that no refinement within the requested interface budget exists;
- gives a completeness theorem within the class and a quantitative error certificate under the eta-separated version;
- runs in `f(q,w,1/eta) poly(r,m,input-bit-length)` rather than enumerating the full q-to-the-number-of-components global product, or proves an equally substantive structural criterion/lower bound.

Here m counts observed channel/action labels. This is deliberately an ambitious *candidate theorem*: the width, local observability and margin hypotheses need formal development and may require strengthening. No claimed FPT theorem is proved in this note.

### Why crossing/refinement machinery would genuinely matter

A description optimized for motion and one optimized for heat need not be nested partitions. Independently valid finite interfaces may disagree about which histories they identify. A common refinement must simultaneously preserve readout meaning, action admissibility, causal direction, local update closure, and the memory budget. Pairwise static alignment is insufficient: updates can require information forgotten by an overlap; cyclic overlap maps can be mutually inconsistent; Cartesian products always hide the hard memory cost.

The needed object is therefore not just an unlabeled tensor factorization or a bisimulation check on supplied components. It is an observable **interface atlas with typed update intertwiners**, together with a theorem characterizing which crossing atlases admit a bounded persistent realization. The negative output should be histories and continuation/action tests demonstrating the missing distinctions or incompatible update transport, with an explicit port-state lower bound. Such a witness is meaningful to data collection and can suggest the next experiment.

### What would still be mere rebranding

- Searching all bounded kernels and printing “typed incompatibility” when a solver says UNSAT.
- Calling all constraints a “crossing theorem” without eliminating, localizing or structurally characterizing them.
- Recovering one optimal model and declaring it uniquely physical.
- Supplying the latent partition under an “observability” assumption.
- Using ordinary rank or static nonnegative rank as a persistent-message cardinality certificate without update closure.
- Verifying a supplied family of mechanisms rather than discovering it.

### Minimal proof obligations before announcing success

1. A counterexample separating per-cut finite factorization from dynamically compatible bounded interfaces.
2. A nonnested crossing family where the theorem constructs a budget-respecting implementation.
3. A family with a short observable crossing witness forcing strictly larger port memory despite individually small descriptions.
4. Completeness, including initial-state compatibility and every admissible action history.
5. Robustness with an explicit margin and coverage condition, or an explicit decision to keep the first theorem population-exact.
6. A comparison against the full semialgebraic baseline showing an actual algorithmic or structural gain.

## 7. Relation to the completed bridge work

The existing bridge directory establishes population residual restrictions and a source-compatible analog/raw-port placement. It does not supply finite predictive interfaces, finite-state realization of arbitrary learned predictors, statistical discovery, or unknown architecture identification. Its legitimate role is to narrow an admissible latent equivalence class **when its source assumptions apply**. The present realization problem starts after—or independently of—that narrowing and remains genuinely open at the proposed structural level.

**Recommendation:** first formulate and prove the exact typed crossing/obstruction theorem for a narrowly defined finite controlled class. Treat noisy discovery as a second theorem with explicit coverage and separation. Do not market generic bounded search as the missing bridge.

## 8. Additional audit: partition algebra, cascade synthesis, and probabilistic crossing

### Deterministic crossing/refinement is already automata algebra

Hartmanis (1962) explicitly studies realization from smaller machines using substitution-property partitions and partition pairs. The loop-free realization correspondence uses partition families with zero product/meet; the partial order records information flow and partition-pair algebra studies information passed between components. This is much closer prior art than generic compositional verification. [Original paper, *Loop-free structure of sequential machines*](https://doi.org/10.1016/S0019-9958(62)90193-6).

Hartmanis–Stearns (1964), *Pair Algebra and Its Application to Automata Theory*, is the direct follow-on baseline. [Original article DOI](https://doi.org/10.1016/S0019-9958(64)90181-0). In deterministic language: `(P,Q)` is a partition pair when `s =_P t` implies `delta(s,a) =_Q delta(t,a)` for every input a. A local memory partition plus incoming-information partitions determines the next local memory exactly when this condition holds. Nonnested partitions, meet refinements, and next-state dependence are therefore not new just because described as typed crossings. This audit verified the original 1962 primary abstract and the 1964 bibliographic identity; it did not inspect the full 1964 proof.

Zeiger (1967) constructs a cascade realization of any finite-state machine from permutation/reset machines, connecting directly to Krohn–Rhodes prime decomposition. This supplies a powerful universal decomposition baseline but not recovery of physical components, prescribed communication budgets, or stochastic causal couplings. [Original paper, *Cascade synthesis of finite-state machines*](https://doi.org/10.1016/S0019-9958(67)90228-8). State expansion and changed wiring matter: an unconstrained cascade realization is not a budget-preserving implementation of an inferred physical architecture.

Alur et al. (2014) synthesize communicating finite-state protocols from message-exchange scenarios plus safety/liveness constraints, assuming scenarios adequately cover desired states; the task becomes completing partial communicating automata. Their algorithms include heuristic and symbolic search. [Primary paper](https://www.cis.upenn.edu/~alur/HVC14.pdf). This is stronger than fitting a single global automaton to traces, but component roles/messages and state coverage are supplied through the scenario model. It does not start with arbitrary noisy readouts and recover unknown port semantics.

### Concrete probabilistic crossing sanity test (derived here, no novelty claim)

Take states `u,v,t00,t01,t10,t11`. Two binary readouts A and B label `u,v,t00` by `(0,0)`, and `tij` by `(i,j)`. Let the transition rows be:

- from u: half to t00, half to t11;
- from v: half to t01, half to t10;
- from each tij: uniform over t00,t01,t10,t11.

Every row gives each individual next readout probability one half. Therefore the partition by A and the partition by B each define an exact two-state strong lumping. Their common four-cell refinement **does not**: u and v occupy its same `(0,0)` cell, yet the next readout event `A=B` has probabilities 1 and 0. The state t00 has event probability one half and lies in that cell as well. Any deterministic state quotient refining both readouts and strongly lumpable for all initial states must distinguish all three of u,v,t00; the other three cells are singletons. Thus such a common quotient requires six states, although each separate quotient needs two and their static pair has only four labels.

This is a concrete distinction between separately preserved marginals and jointly preserved dynamics. It is **not** a general lower bound against arbitrary hidden-state stochastic realizations with initialization-specific encodings, and it is **not yet a communication lower bound**. The obstruction is an elementary lumpability/coupling obstruction, so extending it to a new theory requires more than citing the example.

### Conditions for an honest observable/message witness

To turn the example or any Hankel certificate into an experiment, exhibit accessible histories/interventions whose conditional predictive states correspond to the compared cases. A hidden u/v difference inaccessible in data is not an observable witness. To turn it into a port-state lower bound, hold receiver local state/history and every other authorized input fixed, and freeze the initialization/shared-randomness convention. Otherwise the receiver may already know the distinction and no message is needed. This correction is essential for the Section 6 proposed theorem.

With those conditions satisfied, a deterministic interface merging two source histories cannot realize target event probabilities separated by Delta with worst-case error below Delta/2: the merged interface forces a common predicted value, and the triangle inequality gives the bound. For stochastic interfaces, cardinality lower bounds require a convex-mixture/nonnegative-factorization argument across multiple histories, not simply pairwise distinguishability. Dynamic closure of the same message representation under future actions is an additional constraint beyond any static factorization.

**Updated novelty bar:** jointly discover probabilistic coupling information that individually valid predictive quotients lose; characterize persistent, resource-limited reconciliation across nonnested descriptions; and produce receiver-conditioned observable witnesses with robustness. Deterministic partition lattices, generic bounded synthesis, invariant-cone existence, and ordinary lumpability each cover only parts—but all must be named as baselines.

## 9. Final finite-field checker credits

See `Finite_Field_ICA_Source_Credits.md`: Yeredor's *Independent Component Analysis Over Galois Fields*, Theorem 2, already proves that pairwise independence of K nontrivial mixtures of K independent nondegenerate nonuniform sources in GF(2)/GF(3) forces a monomial mixing matrix. The binary population frame checker is therefore classical finite-field ICA. Gutch et al. (2012) supplies the broader finite-field ICA comparator; Yan et al. (2021) supplies sparse noisy parity learning; Nitta–Sugimoto–Satoh (2005) supplies blind AR identification using ICA. The proposed contribution is the explicitly proved noisy-trajectory/bounded-moment/persistent-interface composition, not these ingredients or an unproved LPN-hardness reduction.
