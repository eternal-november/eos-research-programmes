# Baselines for reusable environment discovery

29 October 2026. Primary source audit for the proposed research target, not a novelty clearance or a completed theorem. This extends the checked 28 October audit in `/workspace/shared/related_work_audit_20261028`, especially `Discovery_Target_Comparators.md`, `Positive_Realization_Audit.md`, and `Operational_Systems_Audit.md`.

## Finding

The proposed combination is substantially harder than learning a dependency graph, but its ingredients have strong precedents. Unknown observation grouping and controlled latent dynamics are already learned together in restricted classes. Recursive predictive-state discovery, finite-record guarantees for new covered policies, positive common-response feasibility, and invariant probabilistic relations each have direct baselines. No checked source below establishes the full proposed integration of unknown grouping, hidden recursive memory, resource-accounted executable stochastic interfaces, common positive realization of crossing descriptions, and finite-data controller reuse without exponential whole-state work. That bounded negative finding is not evidence of priority.

The defensible research burden is an explicit theorem and algorithm under matched assumptions, with a useful improvement in what can be discovered, certified, or computed. In particular, embedding a standard marginal-extension LP inside a search over unknown response recodings does not itself establish a new theorem. The search, its statistical validity, its operational semantics, and its complexity must be compared separately from the LP checker.

## Scope and comparison protocol

The intended inputs are finite, incomplete action/readout records. Distinguish passive logs, chosen experiments, resets, direct subsystem access, exact probability queries, and equivalence oracles. They are not interchangeable. The intended output is an executable positive architecture with a stated covered controller class, not only a low-rank predictor or one reward-specific policy.

For each comparison below, ask which actual structure is supplied and which is inferred. A bounded model class is not a supplied answer. A positive generative parametrization counts as genuine realization. Independent local innovations do not imply independent subsystem trajectories. Conversely, a conditional expectation, a signed observable-operator model, or a graph of statistical influences is not automatically a bounded-message distributed implementation.

## Direct primary comparators

### CoalA discovers an unknown synchronization decomposition

Henry, Mousavi, Neele, and Sammartino, CONCUR 2025, *Compositional Active Learning of Synchronizing Systems Through Automated Alphabet Refinement*. Section 5 assumes a known global alphabet and a membership/equivalence teacher for the whole system, not component alphabets. Alphabet distributions and component LTSs are learned together. Theorem 5.3 proves termination and global trace equivalence. Local unknown table entries are genuine incomplete local information, not passive finite-data statistical uncertainty.

The distribution order has the single full-alphabet component as its top element; the guarantee does not force recovery of a nontrivial or physically original decomposition. The experiments count queries with constant-time teacher responses and explicitly do not establish absolute-runtime superiority. Thus unknown grouping and compositional learning are direct antecedents, but finite passive records, stochastic positivity, physical resource costs, and end-to-end avoidance of whole-state work are not supplied by this theorem. [Primary text, Sections 3.2, 5, 6 and Theorem 5.3](https://drops.dagstuhl.de/storage/00lipics/lipics-vol348-concur2025/html/LIPIcs.CONCUR.2025.20/LIPIcs.CONCUR.2025.20.html).

### Timed whole-system access is not unknown alphabet discovery

Chen, Liu, and Zhang, *Compositional Automata Learning of Timed Synchronous Systems*, arXiv:2610.21237v1, 15 October 2026. Section 3.1 supplies the number of components and their action sets. A whole-system membership/equivalence teacher supports component learners through an adapter, positive-evidence RTAs, incomplete timed observation tables, SMT, and backtracking. Theorem 6.1 says that **if** the algorithm terminates, its network has exactly the target timed language. Do not upgrade this conditional correctness statement to unconditional termination.

This is a strong baseline for learning component dynamics without individual component access, but not discovery of the component/action allocation from passive stochastic logs. The continuous-time and synchronization machinery should not be dismissed merely because it solves a different access problem. [Version-pinned primary text, Sections 3.1 and 6](https://arxiv.org/html/2610.21237v1).

### FactoRL learns unknown grouping and sparse latent dynamics

Misra, Liu, Jin, and Langford, ICLR 2021, *Provable Rich Observation Reinforcement Learning with Combinatorial Latent States*. Definition 2 supplies a factored block-MDP universe: binary latent factors, observation atoms, factorized emissions with unknown disjoint atom groups, disjoint emission supports, sparse transition parents, and a deterministic episode start. Assumptions 1–2 impose backward-dynamics separation and within-factor atom dependence. Realizable regression classes, regression oracles, a planning oracle, and local-factor reachability are used.

Theorem 1 learns emission grouping up to permutation, a decoder, transition model, and policy covers. Complexity depends polynomially on factor count for fixed parent bound, not on the full latent product cardinality; computational efficiency is conditional on the oracles. Section 3 explicitly acknowledges the difficulty of factored planning.

This is a direct counterexample to saying that existing efficient controlled factor discovery always receives the grouping. Its rich observations eliminate genuine hidden-state ambiguity at each time. It does not certify arbitrary shared persistent randomness or charged distributed interfaces. [Published primary PDF, Definitions 1–2, Assumptions 1–2 and Theorem 1](https://openreview.net/references/pdf?id=0wpcsuBLCN).

### Factored MDP structure learning predates latent grouping results

Strehl, Diuk, and Littman, AAAI 2007, *Efficient Structure Learning in Factored-state MDPs*. SLF-Rmax learns unknown transition-parent structure while interacting in one long trial without resets. The observed state factorization is supplied. Its guarantees concern experience efficiency and near-optimal behavior; the paper explicitly separates these from computation and uses an MDP planner. Enumerating bounded-parent candidates avoids full transition-table estimation but is not a general efficient planning theorem. [Primary PDF, introductory scope, Theorem 2 and its corollary](https://cdn.aaai.org/AAAI/2007/AAAI07-102.pdf).

Innes and Lascarides additionally allow initially unknown factors/actions, but use expert assistance to reveal relevant missing concepts. This does not supply a passive-log solution to unknown latent architecture. [Primary paper, learning model and expert protocol](https://proceedings.mlr.press/v115/innes20a/innes20a.pdf).

### Recursive predictive memory is an established discovery object

Shalizi and Shalizi, UAI 2004, *Blind Construction of Optimal Nonlinear Recursive Predictors for Discrete Sequences*. CSSR learns predictive equivalence classes of histories and splits them until updates are recursive. Section 2 states that recursive next-step sufficiency implies sufficiency for the entire future. Its consistency conditions include conditional stationarity, finitely many causal states, and a finite synchronizing suffix for each state. This is not a universal finite-record discovery theorem, and the uncontrolled process formulation is not automatically policy-invariant when action symbols are inserted into the observed alphabet. [Primary PDF, Sections 2–4](https://arxiv.org/pdf/cs/0406011).

James and Singh, ICML 2004, distinguish discovering the PSR tests from learning their update parameters, and solve both with reset access. Thus predictive-coordinate discovery itself is not new. [Primary author manuscript](https://web.eecs.umich.edu/~baveja/Papers/icml04reset.pdf).

### Factored predictive representations already allow overlapping scopes

Wolfe, James, and Singh, AAMAS 2008, *Approximate Predictive State Representations*. Section 4.2 assigns each output coordinate a predictive model on a chosen, possibly overlapping subset of observed coordinates. This extends a fully independent product model; it does not simply assume every component independent. Theorems 5 and 7 compare model rank and expected prediction loss as scopes expand. Scope functions are given in these learning/update procedures. Theorem 3 bounds approximate predictive-state error under its contraction assumptions.

This is a particularly relevant comparator for crossing predictive descriptions and local/global prediction tradeoffs. It does not provide unknown physical grouping, a general positive common realization of separately fitted scopes, or resource-accounted seed/channel implementation. Expected prediction loss must not be silently promoted to uniform new-controller behavior. [Primary proceedings PDF, Sections 3–4 and Theorems 3, 5, 7](https://www.ifaamas.org/Proceedings/aamas2008/proceedings/pdf/paper/AAMAS08_0647.pdf).

### Context trees supply data-driven variable memory with nonasymptotic bounds

Garivier and Leonardi, *Context Tree Selection A Unifying View*, 2011. Theorem 2.14 bounds overestimation without mixing assumptions. Theorem 2.18 bounds underestimation under the paper's non-nullness/continuity assumptions, identifiable context distinctions, adequate depth, and context probability terms; Theorem 2.22 gives strong consistency. Do not summarize this as unconditional finite-sample exact memory recovery. [Primary PDF, Theorems 2.14, 2.18, 2.22](https://arxiv.org/pdf/1011.2424).

Belloni and Oliveira, *Approximate Group Context Tree*, allow shared tree structure across several stationary processes, distinct transition probabilities, and misspecification; oracle/adaptivity bounds use continuity and polynomial beta mixing. This is stronger than fitting one fixed-order Markov chain. The shared-tree premise is not discovery of arbitrary interacting component interfaces. [Primary version v3](https://arxiv.org/pdf/1107.0312).

### Approximate information states already transfer recursive prediction to control

Subramanian, Sinha, Seraj, and Mahajan, JMLR 2022, *Approximate Information State for Approximate Planning and Reinforcement Learning in Partially Observed Systems*. An information state supports reward prediction and prediction of its successor, equivalently recursive updating plus observation prediction. Approximate versions yield value and policy-loss bounds through approximate dynamic programming: Theorem 9 is finite horizon and Theorem 27 discounted infinite horizon. Extensions include stochastic state compression, action compression, and multiagent models.

The primary theoretical transfer assumes the approximation properties hold; learning a representation by optimizing empirical losses does not itself certify them uniformly. A new theorem that merely assumes an accurate recursive summary and then telescopes control error is closely adjacent to this baseline. The discovery and simultaneous certification of unknown compatible local summaries would be the extra burden. [Primary journal PDF, Sections 2–5, Theorems 9 and 27](https://jmlr.org/papers/volume23/20-1165/20-1165.pdf).

### Finite output-only data already supports controller refinement

Coppola, Peruffo, and Mazo, *Data-Driven Abstractions for Control Systems via Random Exploration*. The inspected arXiv v2 is dated 26 September 2024; a journal version appears in Automatica, September 2026. Do not conflate their versioned theorem details.

In v2, Assumption 1 specifies a deterministic, free-input plant. Independent sampled finite input/output trajectories produce a history-based abstraction. Proposition 4.10 converts a sampled-input violation bound to a bound uniform over input words, paying `epsilon * |U|^H` for uniform action-word sampling, or an inverse minimum probability otherwise. Corollary 4.13 provides a probabilistic alternating simulation relation supporting control refinement. Confidence is over data; remaining violation probability is over initial states. Longer-horizon claims need additional assumptions in Section 5.

This is not merely prediction under the logging policy. It is an important baseline for new controller reuse, with an explicit coverage price. Unknown stochastic component grouping and positive distributed realization are separate obligations. [Inspected primary version, Proposition 4.10 and Corollary 4.13](https://arxiv.org/html/2402.10668v2); [journal metadata](https://doi.org/10.1016/j.automatica.2026.113129).

### Offline PSR learning already handles new covered policies

Huang, Liang, and Yang, *Provably Efficient UCB-type Algorithms For Learning Predictive State Representations*, arXiv:2307.00405v3 and ICLR 2024. Section 5 learns from independent precollected behavior-policy trajectories. Assumption 1 imposes well-conditioning. Theorem 2 bounds the learned policy's loss against target policies with finite history-distribution coverage coefficient; dependence also includes core-test action probabilities, model complexity, rank, conditioning, and horizon. The method uses an MLE oracle and learned predictive features with sample splitting.

This directly blocks a broad novelty claim for finite incomplete observation histories plus guarantees for a new covered controller. It does not directly identify a finite positive local implementation or shared-seed architecture. Its computational claims must retain their oracle qualifications. [Version-pinned primary PDF, Section 5 and Theorem 2](https://arxiv.org/pdf/2307.00405v3).

### All-policy controlled model estimation is also established

Chen, Bai, and Mei, *Partially Observable RL with B-Stability*, inspected arXiv:2209.14990v2. Appendix F.2 gives an all-policy model-estimation algorithm; Theorem F.3 bounds `sup_pi TV(P_hat^pi, P_true^pi)` and Theorem F.4 specializes complexity to B-stable PSRs. The class has common core-test sets, a rank bound, stability, and a model-class cover. The algorithm actively chooses exploration policies and its optimization is not an unconditional efficient discovery algorithm for physical components. Proposition D.1 is a particularly close antecedent for policy-conditioned operator-error telescoping, as the previous audit already recorded. [Primary PDF, Appendix D.1 and F.2](https://arxiv.org/pdf/2209.14990v2).

Bowling et al., ICML 2006, also treat PSR learning under non-blind, observation-dependent data-collection policies. Action-selection bias is not a newly noticed issue. [Primary author PDF](https://webdocs.cs.ualberta.ca/~bowling/papers/06icml-psr-exploration.pdf).

### Data-driven compositional abstraction can learn unknown interconnections

Ajeleye and Zamani, *Data-driven Construction of Finite Abstractions for Interconnected Systems A Compositional Approach*, arXiv:2408.08497v2. Section 3.2 supplies designated subsystem state/input/internal-input coordinates and subsystem black-box access. Dynamics and the static interconnection map are unknown; input/output samples of that map are available. Assumptions 1–2 supply Lipschitz constants, without certifying their estimation. Theorem 4.11 composes abstractions through a feedback refinement relation; sparse map approximations can introduce intermediate latent computational variables.

Thus “unknown interfaces” alone is not a differentiator. Discovery of subsystem boundaries from mixed readouts, rather than unknown connections between supplied coordinates, is an actual distinction. [Primary text, Section 3.2, Assumptions 1–2 and Theorem 4.11](https://arxiv.org/html/2408.08497v2).

Lavaei, *MDP Abstractions from Data Large-Scale Stochastic Networks*, constructs local stochastic storage certificates with confidence and composes them into a global stochastic bisimulation certificate under a dissipativity condition. It starts with designated subsystems, interconnection, and state-level data, not raw grouping discovery. [Primary PDF, Theorems 5.1 and 6.1](https://arxiv.org/pdf/2309.07941).

### Fixed uncertain parameters and fresh uncertainty have different semantics

Mertens, Quatmann, and Katoen, *Compositional Reasoning for Probabilistic Automata with Uncertainty*, arXiv:2603.29550v1. Parametric PAs retain parameter dependence across states under one valuation. For robust PAs, Section 7 separates memoryless once-and-for-all nature from history-dependent nature. It gives counterexamples to naïve lifting of assume-guarantee rules for memoryless nature, nonconvex uncertainty, and interval-arithmetic parallel composition. The positive results for convex history-dependent uncertainty use a convexity-preserving composition and reduction to probabilistic automata. Section 8 distinguishes valuation-dependent strong simulations from one relation valid uniformly across valuations.

This is directly relevant to common seed and uncertainty witnesses. Separate local confidence intervals or independently chosen per-step couplings can change the uncertainty semantics. A persistent unknown mechanism must not silently become a fresh adversary or a freshly resampled latent cause. [Version-pinned primary text, Sections 7–8](https://arxiv.org/html/2603.29550v1).

## Common response and positive coupling baselines

### Common response tables are a classical marginal extension problem

Fine's 1982 theorem, in its specified binary two-party correlation setting, equates a factorizable stochastic hidden-variable model, a deterministic-response model, and an appropriate common joint distribution. This is not a theorem about arbitrary dynamic systems, but it is a direct static response-table baseline. [Primary article](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.48.291).

Abramsky and Brandenburger give the broader measurement-cover formulation: existence of a global distribution corresponds to a factorizable hidden-variable realization. Positivity, compatible local tables, and a global extension must be distinguished; signed extension is weaker. [Primary paper, especially Theorem 8.1](https://arxiv.org/pdf/1102.0264).

For a **fixed finite** local response grammar, write `r_i : local_input_i -> local_output_i`. A shared-seed distribution over complete response tuples gives

`p(y | x) = sum_r w_r product_i 1{r_i(x_i) = y_i}`, with `w_r >= 0` and `sum_r w_r = 1`.

Matching observed rows is a linear feasibility problem in `w`. Replacing exact rows by simultaneous confidence constraints stays linear. A separating dual inequality or Farkas certificate is standard convex separation, not a new obstruction principle. Unknown relabelings, response alphabets, grouping, memory, or recodings add a discrete or nonlinear search outside this fixed LP; a theorem must account for that search rather than rebrand the LP as discovery.

### A fresh common seed is not necessarily a persistent common seed

If a seed is newly drawn each step, a valid response-table distribution at each admissible state can define a normalized Markov kernel. If the same seed persists across steps, checking each one-step marginal separately is insufficient. The joint law must retain a single latent assignment or a specified seed transition, including the posterior information revealed by previous outputs. In particular, an input-conditioned seed law can invalidate the intended causal/local interpretation when it lets the seed depend on future or external controller choices.

This is an analytical distinction, not a priority claim. It is consistent with the fixed-versus-fresh uncertainty warning above. The proposed theorem must state whether its witness is a distribution over static response functions, a causal stochastic transducer, a state-dependent fresh random map, or one persistent source process.

### Invariant couplings require comparison with probabilistic simulation

A relation whose successor distributions admit positive couplings supported inside the relation is the standard lifted-relation shape of probabilistic simulation/bisimulation. Deng and Du, *Logical Metric and Algorithmic Characterisations of Probabilistic Bisimulation*, Theorem 2.4 identifies relation lifting with a nonnegative weight matrix having prescribed marginals and support in the relation; Theorem 3.7 reduces finite lifting to unit maximum flow. Section 6 gives greatest-fixed-point characterizations and Section 7 an on-the-fly algorithm. [Primary paper](https://arxiv.org/pdf/1103.4577).

Zhang, Hermanns, Eisenbrand, and Jansen, *Flow Faster*, LMCS 2008, supplies an algorithmic benchmark for strong/weak probabilistic simulation using improved flow techniques. Polynomial complexity is measured in the supplied finite transition system, not in a compact unknown-factor description. [Primary journal paper](https://lmcs.episciences.org/989/pdf).

Thus coupling feasibility is a transportation LP or flow problem, and eliminating pairs that fail successor closure is established fixed-point reasoning. A common-response invariant may be **stricter** if one coupling/seed must witness components and crossing charts simultaneously, rather than allowing a separate existential coupling for each obligation. That quantifier change must be explicit and must survive the following elementary packaging test.

**Unrestricted action-table packaging.** For finitely many global actions `a`, suppose each action has a feasible coupling `q_a` on its successor-pair space. Set the common seed to a tuple `z=(z_a)_a` with law `q=product_a q_a`, and make the response at action `a` read coordinate `z_a`. This is one positive common response law whose action marginals are exactly the separate couplings. Consequently, requiring a common seed across actions adds no strength by itself when support size is unrestricted and no further cross-action identities exist. The same construction applies to finitely many contexts if their responses need not agree on overlapping local inputs.

Strictness must instead come from local response reuse across global contexts, a bounded seed/resource budget, prescribed compatible recodings, or persistent dynamic restrictions. The Bell/CHSH obstruction is the standard locality example. Dynamic persistence must be analyzed on the specified transition/conditioning semantics; it should not be asserted merely because a random source is given one name.

The exact dynamic reduction is not closed by this audit. Do not claim that every proposed simultaneous invariant is already identical to ordinary pairwise bisimulation, or that a new name establishes a new invariant. The appropriate comparison is a constructive translation of witness variables, quantifier order, and closure operator, with any strictness proved by a finite example.

## Assumption and proof pitfalls

### Finite data does not certify exact hidden architecture without restrictions

Different local factors, redundant latent states, and common causes can induce the same controlled observable law. “Recover the true components” requires an identifiability theorem and an equivalence convention. A sound compatible realization, a minimal realization under a stated cost, and a set of all compatible realizations are three different deliverables.

Exact equality, exact zero support, exact context merging, and absence of an influence cannot generally be concluded because a finite-data test fails to reject. Exact structural recovery needs separation/faithfulness and positive visitation assumptions, or a carefully stated confidence-set result. A Bayesian posterior alone does not give a frequentist simultaneous coverage theorem.

### Unknown memory is not validated by a one-step fit alone

A proposed summary `m(h)` must admit an executable update `m(hao)=u(m(h),a,o)` on the covered support. Histories merged by a one-step test can require different successors. Recursion closure is a real check but its principle is already present in CSSR and information-state theory. Finite suffix trees additionally restrict the memory class; a finite hidden machine need not have a bounded exact synchronizing suffix.

If candidate local states are latent and imputed, empirical counts at those states are not automatically samples from their true local transition rows. A valid concentration argument must handle inference, selection, and dependence. Observable deterministic recodings of history simplify this issue but must themselves be learned with simultaneous or held-out validity.

### Controller coverage needs a precise probability space

Record the collection policy, which aspects are known, whether actions are exogenous conditional on recorded history, and which policies are covered. Distinguish action support, history-distribution density ratios, occupancy of a learned summary, and coverage of counterfactual tests. Local action support is not automatically sufficient for joint histories involving several interacting components.

A model accurate on average under one policy can be inaccurate where a new feedback controller concentrates. Coverage must either bound this change of measure or provide uniform control of the relevant kernels/tests. If there are unvisited actions or histories, compatible environments can agree on every recorded experiment and disagree completely there. Abstention or explicit wide uncertainty is a legitimate output.

Confidence over training data, probability of deployment failure, and approximation error are different quantities. Finite-horizon statements do not imply infinite-horizon safety. A learned controller selected after inspecting the model needs an event uniform over the relevant candidate/controller class, not a fixed-controller confidence interval selected after the fact.

### Positive common realization is not pairwise compatibility

Matching each component marginal, and even each pairwise overlap, need not yield one positive global extension. Conversely, a single valid jointly learned generative model already supplies coherent marginals by construction and deserves full credit. Crossing chart requirements must say whether they demand only these marginals or an executable, resource-preserving common refinement with commuting updates.

The relevant quantifier order can be the entire issue: `for each chart exists a seed law`, `exists one seed law for all charts`, and `exists one causal seed process for all times and controllers` differ. Pairwise coupling witnesses need not be jointly realizable. A product of local uncertainty sets may include impossible combinations and, depending on how assumptions are used, invalidate a compositional proof.

### No whole-state enumeration must be measured end to end

Count all of: proposed groupings/recodings; local-memory candidates; deterministic response functions; shared-seed support; coupling/refinement states; constraint rows and columns; probability estimation; planning oracles; verification; and online execution memory. A compact certificate does not prove an efficient search for it. A local LP can have exponentially many response-table variables. Column generation without a tractable separation/pricing oracle does not solve that issue. Sum-of-local-cardinalities sample complexity is not the same as polynomial runtime.

The meaningful target is a parameterized guarantee, for example polynomial dependence on number of components and records, with explicit dependence on bounded interface width, local memory, alphabet size, response grammar, conditioning, and coverage. A method allowed to fall back to one global component must not present that fallback as the promised nontrivial compositional discovery result.

## Required matched tests before a novelty claim

1. Translate the fixed common-response feasibility problem into the classical response-table LP, identifying any constraints that are genuinely additional.
2. Translate the invariant closure condition into a lifted probabilistic relation. If the common witness has stricter quantifiers, supply a small counterexample separating it from ordinary pairwise couplings.
3. On the rich-observation subclass, compare discovery outputs with FactoRL rather than only with a supplied-group DBN learner.
4. On known grouping but unknown memory, compare with CSSR/context-tree and factored-PSR baselines under matched data access.
5. On the prediction-to-control step, compare with AIS, offline PSR-LCB, and output-only probabilistic alternating simulation. State which coverage factor or guarantee improves.
6. For persistent seeds or fixed unknown mechanism parameters, test a case where separate one-step feasible couplings do not admit a common dynamic witness.
7. Report whether crossing refinements create a new certified decomposition, remove an invalid one, sharpen uncertainty, or reduce computation. Ordinary projection consistency is not enough.
8. Give actual operation counts on a growing family with bounded local interfaces; do not omit an exact teacher, global decoder, or planner from the cost accounting.

## Current classification

Standard machinery: controlled predictive sufficiency, suffix/context refinement, positive fixed-response marginal LPs, coupling constraints, greatest-fixed-point closure, confidence-set pessimism, and simulation-based controller transfer.

Genuine candidate research burden: jointly discovering unknown response/seed recodings and recursive local structure from finite records; producing one correctly quantified positive dynamic witness across crossing descriptions; retaining local implementability/resource costs; and proving a nonvacuous simultaneous covered-controller guarantee with a demonstrated complexity or expressive advantage over the matched baselines.

Status: no novelty clearance. The dynamic common-response-to-bisimulation translation and the claimed efficient unknown-recoding search remain unclosed comparisons. This is a bounded primary-source audit, not an exhaustive literature exclusion.

## Addendum: the current conditional-product theorem and calibration certificate

Checked against `theory/Discovery_and_Reuse.md`, Sections 8–15, on 29 October 2026. The current theorem is broader than its additive demonstration: it assumes an unknown conditional-product partition with block size at most b, unknown input scopes of size at most w, and an observable-memory ceiling L. It tests output marginals of size at most b on augmented input scopes of size at most 2bw. It does not assume the actual partition or scopes are known. The promise of a bounded conditional-product universe, independent endpoint acquisition, common observed initialization, and explicit coverage gate remains essential. This is not general hidden-state learning from arbitrary dependent logs.

### Credit for the multinomial KL calibration

Agrawal, *Finite-Sample Concentration of the Multinomial in Relative Entropy*, IEEE Transactions on Information Theory 66(10), 2020, Theorem I.3, states that for m iid samples on k symbols and their empirical law Q,

    E exp(t KL(Q || P)) <= (1-t/m)^(-(k-1)),  0<=t<m.

The KL direction is empirical-to-true, not the reverse. This is the gamma-MGF bound itself, not an asymptotic chi-square approximation. [Version-pinned primary text, Definition I.1 and Theorem I.3](https://arxiv.org/html/1904.02291v4).

Its application here is a standard consequence: conditional on successful structural recovery from separate discovery data, let fresh calibration contain m iid residual vectors with mutually independent recovered blocks. Their empirical block histograms are independent. Writing D=sum_B(k_B-1) and S=sum_B KL(Q_B || P_B), multiplication of the MGFs gives E exp(lambda m S)<=(1-lambda)^(-D). The usual Chernoff/sub-gamma calculation gives

    Pr[m S > D + sqrt(2 D u) + u] <= exp(-u).

Thus x=D+ceil(sqrt(12D))+6 is a conservative integer threshold with failure at most exp(-6)<0.0025. The case D=0 is deterministic. The alphabet sizes k_B must be fixed valid bounds, not uncertified observed support sizes. This calculation does not automatically apply to dependent blocks, discovery-selected calibration data, or arbitrary context-dependent row histograms.

For correctly recovered additive responses, product-KL additivity and data processing bound each conditional learned-to-true output KL by S. With identical initialized memory and the same causal controller, the transcript KL chain rule gives KL(Q_pi^H || P_pi^H)<=H S; Pinsker gives TV<=min(1,sqrt(H x/(2m))). The argument is pointwise in the controller on the single calibration event, hence permits a data-selected feedback controller without a controller union bound. Any coverage stopping and structural-recovery failure must still be accounted for separately. These are established concentration and change-of-measure ingredients, explicitly not a new concentration or feedback-transfer theorem.

### Direct local-marginal-to-whole-law comparator

Daskalakis and Pan, COLT 2017, *Square Hellinger Subadditivity for Bayesian Networks and its Applications to Identity Testing*, already state the following TV bound for laws on a common DAG:

    TV(P,Q) <= sum_v TV(P_{v union pa(v)},Q_{v union pa(v)})
               + sum_v TV(P_pa(v),Q_pa(v)).

Their Theorem 1 gives squared-Hellinger subadditivity, and their testing results allow an unknown common graph and, separately, potentially different unknown trees. Thus learning/testing through local marginals rather than whole-state tables has a direct primary baseline. [Published extended abstract, page 3 and Theorem 1](https://proceedings.mlr.press/v65/daskalakis17a/daskalakis17a.pdf).

An immediate comparison, derived here, covers two different size-b block-product partitions: orient the clique of every block in both partitions according to one common coordinate order, then union the edges. Both laws factor on this DAG. Each node-plus-parent neighborhood has at most 2b-1 coordinates. Consequently the displayed classical TV inequality yields whole-law error at most 2n zeta from accuracy zeta of all marginals of size at most 2b-1. The DAG is needed only in the proof, not as supplied information.

The current Section 10 lemma uses only b-coordinate marginals and the positive intermediate law R=product_{C in pi}P_C to obtain (|pi|+|tau|+|pi meet tau|)zeta<=3n zeta. This is a genuine, precisely stated support-size distinction from the preceding straightforward DAG reduction. Its proof uses elementary marginalization, product coupling, and triangle inequalities. No checked source in this narrow addendum supplies that identical b-support inequality; this is not a priority finding, and “proved here” is preferable to “new.”

The Section 11 lifting from augmented-scope tests to pointwise joint-kernel error exploits that marginal S has an unknown sufficient input union of size at most bw, and explicitly tests its union with the candidate scope. That is the theorem-specific bridge to compare, not merely “uses local tests.” Once the joint-kernel bound is obtained, stopped maximal-coupling/union-bound transfer to covered feedback controllers is standard. The positive comparison law R is not an exact common operational realization; the separate response-table LP, recursive interface equations, and resource checks still carry that burden. The present audit establishes useful matched distinctions, not novelty clearance for their integration.
