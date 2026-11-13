# Prior art and scope for uncertain linear coupling

30 October 2026

These notes place safe finite-budget acquisition of a mission-sufficient positive interface alongside existing identification, coding, realization and safe-learning results. This is a targeted primary-source comparison, not an exhaustive novelty certification. The scoped construction uses classical finite-field support learning, annihilator linear algebra, finite route checking and hypothesis-testing arguments. No priority or general causal-discovery claim is made.

Task-relevant partial causal discovery, unknown shared confounding, safe acquisition, and task-optimal identification each already have substantive theorems. Combining these topics is not itself a new target. The specific operational question is whether restricted, physically safe evidence supports a positive interface for a declared family of mission contexts while unresolved joint couplings remain. Source freshness, noninvasiveness, calibration-to-production transport, isolation and gate/drain laws remain explicit physical premises.

## Identification and safe learning baselines

### 1. Partial causal discovery with hidden confounding

Elahi, Ghasemi and Kocaoglu, **Partial Structure Discovery is Sufficient for No-regret Learning in Causal Bandits** (NeurIPS 2024), explicitly characterize which latent confounders must be discovered to obtain the possibly optimal minimum intervention sets. Their two-stage algorithm learns reward-ancestor structure plus relevant confounders, then runs a bandit algorithm. Thus neither “unknown coupling” nor “learn only mission-relevant shared sources” is independently new.

The inspected finite-sample theorem assumes interventional faithfulness, positive causal-effect and do-versus-see gaps, a lower bound on nonzero conditioning-event probabilities, and an appropriate degree bound. Its discovery algorithm samples arbitrary prescribed joint interventions. It does **not** establish that those interventions are physically safe, that experiments leave a mission reachable, or that the learned result is a positive compositional realization under feedback.

Primary source: https://arxiv.org/html/2411.04054 (Assumptions 1–4; Sections 3–5).

### 2. No graph recovery is itself an established objective

Lu, Meisami and Tewari, **Causal Bandits with Unknown Graph Structure** (NeurIPS 2021), exploit only reward-relevant structure. Their setup supplies the Markov equivalence class, observes all variables each round, assumes causal sufficiency/faithfulness and quantitative effect/reward-identifiability gaps, and analyzes specified graph families. It is not discovery from unconstrained black-box partial observations.

Primary source: https://proceedings.neurips.cc/paper/2021/file/d010396ca8abf6ead8cacc2c2f2f26c7-Paper.pdf

Malek, Aglietti and Chiappa, **Additive Causal Bandits with Unknown Graph** (ICML 2023), identify a best intervention without explicit parent learning. Their crucial simplification is additive outcome structure; they exclude latent confounding between the reward and its ancestors and permit intervention on all observed non-reward variables. This is a direct baseline for “partial identification is enough.”

Primary source: https://proceedings.mlr.press/v202/malek23a.html

Shahverdikondori, Etesami and Kiyavash, **Graph Learning Is Suboptimal in Causal Bandits** (AISTATS 2026), give a stronger warning: recovering parents can conflict with regret minimization, and graph-free algorithms can be preferable. Their setting includes causal sufficiency, hard subset interventions and post-intervention vector observations. The theorem is not an arbitrary hidden-confounding or soft-intervention result.

Primary source: https://arxiv.org/html/2510.16811

### 3. A separator is already an interface-like object

De Kroon, Mooij and Belgrave, **Causal Bandits without prior knowledge using separating sets** (CLeaR 2022), use a separating set to factor estimation through an intermediate boundary. For a true separating set, their discrete iid estimator is unbiased with variance no larger than the ordinary sample mean. The theoretical estimator guarantee should not be promoted into an end-to-end guarantee that finite data have certified the discovered separator. A proposed boundary still requires a proof of adequacy under admitted couplings.

Primary source: https://proceedings.mlr.press/v177/kroon22a.html

### 4. Task-oriented system identification

Wagenmaker, Simchowitz and Jamieson, **Task-Optimal Exploration in Linear Dynamical Systems** (ICML 2021), derive task- and instance-specific lower bounds and finite-time experiment-design guarantees. Their central question is precisely how much of an environment must be learned to complete a task. The main model is a fully observed linear dynamical system with Gaussian process noise, smooth decision loss, and an expected input-energy constraint. That energy budget is not a pathwise physical-safety or irreversible-deadline guarantee. This baseline is relevant to task-sensitive acquisition as well as to full system identification.

Primary source: https://proceedings.mlr.press/v139/wagenmaker21a/wagenmaker21a.pdf

### 5. Safe learning: distinguish safe output from safe experiments

Wang, Wagenmaker and Jamieson, **Best Arm Identification with Safety Constraints** (AISTATS 2022), provide genuine safe-acquisition results from known initial safe doses, under linear or monotonicity/smoothness structure. In the monotone setting the acquisition guarantee permits a specified safety tolerance above the target threshold; this must not be presented as unrestricted zero-risk discovery.

Primary source: https://proceedings.mlr.press/v151/wang22h.html

Camilleri et al., **Active Learning with Safety Constraints** (NeurIPS 2022), optimize identification of the best safe output. Section 5 explicitly leaves *safety during exploration* as an extension. It is a strong experimental-design comparator but not evidence that every query is safe.

Primary source: https://arxiv.org/html/2206.11183

Huang, Yang and Liang, **Safe Exploration Incurs Nearly No Additional Sample Complexity for Reward-free RL**, establish strong safe exploration guarantees in an episodic setting with a safe baseline and slack. Their expected-cost policy-safety formulation, resets and realizability/oracle assumptions differ from pathwise physical finite-mission safety semantics.

Primary source: https://arxiv.org/html/2206.14057

## Limits of standard constructions

A finite candidate family with a confidence set and robust planning is a partially observed control/model-selection construction when the hidden candidate persists across time. A finite history-tree positive realization can be useful, but does not itself establish discovered local interfaces. Arbitrary products of separately projected confidence sets can erase shared-source constraints; independent switching of the hidden model at every step changes the semantics unless expressly allowed.

Pairwise independence is not joint independence, and nonrejection is not a certificate of a missing shared source. Pairwise tests require additional assumptions excluding higher-order dependence and cancellations before they determine a source partition. Quantitative faithfulness can carry a discovery guarantee rather than follow from it.

At a fixed physical state, budget and context language, fewer plausible worlds weakly improve robust feasibility. An actual experiment changes elapsed time, pending physical state and remaining resources; confidence-set refinement alone does not imply improved mission completion. Propagation of assumed local comparison squares also does not supply evidence that those squares are valid.

Different requested interface laws alone do not establish mission incompatibility. An information obstruction needs indistinguishability over every safely affordable adaptive experiment, including cumulative same-source reads and residual mission feasibility, together with incompatible successful decisions. Randomized policies and allowed failure probabilities matter. This is a specialization of an established decision-theoretic obstruction, not independent novelty.

## Exact projected-support lemma and its scope

Let an unknown law be uniform on a binary linear subspace S of a finite ambient vector space. Probe A_e reveals only its image law and projected support U_e=A_e S. Define V=intersection_e A_e^(-1)(U_e). For jointly realizable data A_e V=U_e. The relaxed compatible worlds are all subspaces S'<=V satisfying A_e S'=U_e. For a desired joint linear query Q, the exact criterion is

    row(Q|V) minus {0} subset UNION_e row(A_e|V).

This is a union, genuinely not its linear span: probes are separate marginals on different activations, not jointly observed values on one activation. A compatible S' with Q S' properly contained in Q V gives a nonzero character in row(Q|V) annihilating S'. If that character belongs to a probe row space, probe surjectivity gives a contradiction. Conversely an uncovered character chi gives S'=ker(chi|V), which preserves every probe image but reduces the Q-image.

This is an elementary finite-dimensional separation/annihilator argument, not a safely established new general theorem. Its necessity requires the model class to contain the hyperplane witness: a fixed-rank, restricted-incidence, fixed-memory, or other physically constrained candidate family need not contain it. Overapproximating by all subspaces gives a sufficient certificate, not automatically a sharp physical impossibility theorem. In particular, the maximal V need not admit the stationary finite-memory Toeplitz realization required of a narrower physical source class.

## Coding and realization baselines

**Forney, Codes on Graphs: Fundamentals** (2013/2014), Sections 3.3–3.4, 4, 5, and 6.2, is the closest realization baseline. It proves projection/cross-section and sum/intersection duality, represents a code as the external projection of a global constraint behavior, treats observable internal states, develops interface decompositions, and studies connecting fragments. These are exactly the algebraic operations underlying projected support, inverse-image constraints and wiring. The earlier Forney–Gluesing-Luerssen paper analyzes observability/controllability and local reduction, including cyclic realizations. These are direct realization baselines in addition to the causal-bandit references.

Sources: https://arxiv.org/pdf/1306.6264 ; https://arxiv.org/abs/1203.3115

**Massey, Minimal Codewords and Secret Sharing** (1993), characterizes access structures using minimal dual codewords. A target linear functional is reconstructible from a coalition precisely through a suitable linear relation; otherwise an invisible direction hides it. This is the direct classical privacy/annihilator mechanism behind the hyperplane witness. Important distinction: a secret-sharing coalition jointly sees multiple shares of the *same* draw; separate experimental marginals do not. Consequently one cannot import a span-of-all-probes condition in place of the union criterion.

Primary author-hosted paper: https://www.isiweb.ee.ethz.ch/papers/arch/mass-1993-3.pdf

**Maynard and Siemons, On the reconstruction of linear codes** (1998), studies reconstruction of code isomorphism classes from collections of punctures/residuals. This is relevant terminology and neighboring prior art, but its reconstruction-deck question is not immediately identical to our known labelled probe maps and mission-relative image question. Only the publisher abstract was inspected; do not claim its theorems subsume this criterion without full-text comparison.

Source: https://doi.org/10.1002/(SICI)1520-6610(1998)6:4%3C285::AID-JCD6%3E3.0.CO;2-B

**Forney and Vontobel, Partition Functions of Normal Factor Graphs** (2011), treats external functions obtained by summing products over internal variables, and transformations preserving those functions. This supplies an existing language for distribution-preserving graphical realization, not just support equality.

Source: https://arxiv.org/abs/1102.0316

**Willems, The Behavioral Approach to Open and Interconnected Systems** (2007), models interconnection through constraints/shared variables and eliminates latent variables to obtain manifest behavior. This is the appropriate control-theoretic baseline for finite-window trajectory subspaces. Merely learning a span and projecting an interconnected linear relation is not a new reconstruction-versus-composition principle.

Primary source: https://ieeexplore.ieee.org/document/4384643/

## Probability and compositional qualifications

Uniformity is a substantive restriction, not a consequence of linear support. If X is uniform on S, a linear map L sends it to the uniform law on L(S): each nonempty fiber is a coset of ker(L|S) and has equal size. Thus equality of Q-images really does imply equality of Q-laws in this model class. Arbitrary biased source bits invalidate the inference.

A single global source sampled uniformly on V realizes all learned probe marginals. Independently sampling each component's projected support generally does not: it erases shared parity constraints and temporal persistence. For example, one shared fair bit yielding (Z,Z) cannot be replaced by two independent fair bits even though individual marginals agree. A factor-graph implementation must preserve a common global constrained configuration and its weight, not redraw local marginal configurations.

For a globally uniform linear solution space, projecting internal variables remains uniform on the external image by constant fiber cardinality. This is an exact algebraic fact. It does not by itself make a feedback construction executable: sampling uniformly from solutions of closed-loop equations may amount to postselection rather than running the physical system. A causal generative construction, or a separately justified well-posed solution map with the correct source law, is required. Likewise, a finite-window subspace alone does not guarantee consistent overlapping windows, stationarity, an admissible bounded-memory realization, or correct action-conditioned kernels.

Adaptive observation and feedback require complete joint transcript maps, not separate endpoint queries. A family whose members each satisfy the criterion need not make their joint map satisfy it. Branching policies require a transcript-law argument, including conditioning and zero-probability branches; they are not automatically linear maps. Full cumulative-query coverage is sufficient for transcript preservation but need not be necessary for a particular value-guarded mission.

The appropriate limited description is an explicit coding-theoretic identifiability lemma integrated with safe mission acquisition. For fixed finite dimensions, recovering a uniform subspace from sufficiently many independent samples is elementary rank learning, not a new learning principle. The physically justified probe/context maps, positive causal realization, budgets, allowed feedback and restricted comparison cylinders are separate obligations.
