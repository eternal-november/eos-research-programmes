# Safety representation discovery prior coverage and theorem gates

29 October 2026. Focused primary-source audit for the approved target. This is not a priority clearance or a proof review of a yet-unwritten theorem.

## Plain language abstract

The new objective is substantially more demanding than finding consistent decompositions inside a chosen finite catalogue. However, several apparent next steps already have close precedents: task-specific state abstraction, finding sufficient sensors, learning assume-guarantee interfaces, data-driven probabilistic abstractions, and rejecting implementations that use unavailable information. Earlier work in this programme also already constructs continuation-sensitive interfaces and causal memory witnesses across persistent possible worlds. A substantive next result must connect these capabilities to incomplete evidence while preserving quantitative uncertainty and jointly discovering the representation and its executable interfaces. Its failure outputs must distinguish a coarse representation from insufficient evidence, an infeasible interface, and an actually unsafe controller. Merely adding a robust safety check to the previous finite constraint solver would not meet that burden.

## 1 Internal predecessor obligations

The latest sources were restored and inspected directly: `certificate_guided_discovery_20261029/theory/Relative_Realization_Theorem.md`, `Operational_Certificate_Bridge.md`, and its focused operational audit. They establish an exact original C5 local constraint compiler; a separate operational compiler with unknown bounded local mechanisms, ownership and deliverable encoders; all-step local update/wiring equations; shared-world residual solving; and task-relative contextual summaries. Their conclusion is explicitly existential possible-model realization, not assurance for every readout-compatible world. Local compilation is complete for the stated finite table witnesses and full Cartesian domain, not arbitrary reachable-state implementations.

The available source `related_work_audit_20261028/Operational_Systems_Audit.md`, especially sections 4–6, records more extensive older coverage:

- A genuine original Calc/presentation/refinement interpretation into dynamic state/event graph maps, including nullary boundaries, has already been established in a limited slice. The current gap is not the absence of every categorical-operational connection, but the absence of a proved connection for the newer locally synthesized operational language.
- Finite continuation/operator closure already gives a coarsest quotient preserving the declared continuation verdicts. Mathematical classes are not free sensors: an actual observation/history factorization is separately required.
- Persistent-world causal-cut reconstruction already uses one permitted update table across all occurrences and worlds, shared cut anchors and common acceptable responses. Pairwise feasibility and independent cut coloring are explicitly insufficient; update closure matters.
- The earlier suitability construction quantifies one installed implementation before every persistent physical world and every adverse execution. Analyst belief storage is not free runtime memory.
- Exact unknown crossing-refinement recognition already exists over a supplied whole and a finite permitted map alphabet. It is not an arbitrary unknown-environment identification theorem.

Consequently, coarsest task quotients, causal interface synthesis, robust quantifier order and unknown common refinement are not new by themselves. The proposed new burden is their evidence-driven quantitative integration without supplying the desired representation or a complete list of physical mechanisms.

## 2 Closest external baselines

### Task relevant state variables

Wang, Wang, Xiao, Zhu and Stone, *Building Minimal and Reusable Causal State Abstractions for Reinforcement Learning* (AAAI 2024), derive task-specific abstractions using learned dynamics and reward dependencies. Their Theorem 1 connects reward ancestors to a bisimulation feature set. Appendix C explicitly assumes fully observed factored states and conditional independence of next-state components given the current state. This is a direct baseline for “find which variables matter to the task,” but not a solution to incomplete evidence, unknown physical interfaces or robust safety under unobserved shared influences. [Full paper](https://arxiv.org/html/2401.12497v1).

### Discovering sensors and needed observations

Fu, Dimitrova and Topcu, *Abstractions and sensor design in partial-information, reactive controller synthesis* (ACC 2014), use counterexamples and interpolation to refine abstractions and identify additional sensing modalities for safety synthesis. The starting concrete game and sensor-design formalism are given. Thus “a counterexample says we need another distinction or sensor” is not a new mechanism. [Author manuscript](https://eprints.whiterose.ac.uk/id/eprint/156437/1/acc14.pdf).

Chatterjee, Chmelik and Topcu, *Sensor Synthesis for POMDPs with Reachability Objectives* (ICAPS 2018), synthesize weakest additional sensors so that a small-memory policy achieves almost-sure reachability, prove NP-completeness and give a SAT encoding. This directly covers sensor-memory tradeoffs in a specified POMDP. It does not establish the POMDP itself from uncertain physical evidence or discover distributed component ownership. [Original proceedings article](https://ojs.aaai.org/index.php/ICAPS/article/view/13875).

### Learned quantitative assumptions and informative counterexamples

Feng, Kwiatkowska and Parker, *Compositional Verification of Probabilistic Systems using Learning* (QEST 2010), learn probabilistic assumptions using model-checking queries. Their method can prove satisfaction, return a probabilistic counterexample, or produce probability bounds when the assume-guarantee rule cannot settle the question. Its components are supplied. [Full paper](https://qav.cs.ox.ac.uk/papers/qest10learn.pdf).

Komuravelli, Pasareanu and Clarke, *Assume-Guarantee Abstraction Refinement for Probabilistic Systems* (CAV 2012), infer conservative component assumptions and refine them using stochastic-tree counterexamples to strong simulation; simpler counterexample forms are not generally sufficient. This is a warning against promising that every informative probabilistic failure is one pair of states or one path. [Paper and full-proof link](https://arxiv.org/abs/1207.5086).

Giro and Rabe, *Verification of Partial-Information Probabilistic Systems using Counterexample-Guided Refinements* (ATVA 2012), eliminate spurious schedulers that exploit information unavailable under the observation model. Hence executable information restrictions are already a central verification issue, not a new principle here. [Authors' publication record](https://qav.cs.ox.ac.uk/bibitem.php?key=GR12).

### Data driven uncertainty bounds

Coppola, Peruffo, Romao, Abate and Mazo, *Enhancing Data-Driven Stochastic Control via Bundled Interval MDP* (2024), construct richer uncertain stochastic abstractions using samples of an unknown noise law and scenario-theoretic guarantees. Their method still uses known underlying dynamics for backward reachability. The paper explicitly contrasts data-driven abstraction and adaptive-memory methods. Thus adding sampled transition intervals and robust safety evaluation is established, while the dynamics/coverage assumptions remain substantive. [Author-hosted paper](https://licioromao.com/assets/bibfiles/individual-pdf/CPRAM24.pdf).

Jackson, Laurenti, Frew and Lahijanian, *Strategy Synthesis for Partially-Known Switched Stochastic Systems* (HSCC 2021), learn unknown nonlinear residual dynamics with Gaussian processes and build interval-MDP abstractions for finite-trace temporal specifications. Their hypotheses include a declared function class and independent stationary sub-Gaussian noise. This is a close baseline for “incomplete observations to uncertainty-aware safety abstraction,” but does not automatically produce unknown decomposition interfaces. [Author manuscript](https://mortezalahijanian.com/papers/HSCC2021.pdf).

### Persistent coupled uncertainty

Mannor, Mebel and Xu, *Robust MDPs with k-Rectangular Uncertainty* (2016), study structured coupling of uncertain model parameters and state augmentation. The point relevant here is that independent local uncertainty choices can be more conservative than one persistent shared model. A decomposition algorithm must not silently change static shared uncertainty into fresh independent adversarial choices at every component and time. [Original article](https://doi.org/10.1287/moor.2016.0786).

These are comparisons of explicit problem ingredients. No assertion is made that the complete intended theorem is a direct corollary of one cited paper.

## 3 What the new theorem must actually add

A suitable target should make the representation itself an output. It should not start with a complete unknown-model catalogue whose entries already carry all relevant state variables and causal structure, then merely minimize a supplied transition table.

A strong possible formulation is an evidence-relative, task-sensitive decomposition theorem with the following separately checkable obligations:

1. **Evidence semantics.** State precisely which histories, interventions, sensors and physical hazard observations are available. Construct a confidence or consistency region with justified coverage. The distinction between a model-class assumption and something tested by the evidence must remain explicit.
2. **Joint necessity.** Return a concrete pair, family, stochastic tree or dual bound showing that omitting a proposed distinction or interaction prevents a specified risk guarantee within the allowed representation class. A necessary feature should not merely be one selected by the algorithm. When no individual feature is mandatory but alternatives suffice, return the family of tradeoffs rather than a fictitious canonical minimum.
3. **Executable sufficiency.** Construct components and causal interface programs that expose the retained information at the correct time, through the available sensors, memory and communication. A map on latent states is not itself such a program.
4. **Quantitative composition.** Bound the closed-loop task error or risk over the remaining joint uncertainty, retaining shared parameters and sources. A union bound can be sound but vacuous; the result should state when its quantitative guarantee remains useful and how coupling affects it.
5. **Evidence versus abstraction diagnosis.** Distinguish (a) a spurious failure caused by a coarse representation, (b) physically distinct evidence-compatible worlds with different safety outcomes, (c) a required observation that cannot be implemented, and (d) a genuine unsafe execution under the controller. These cases call for different actions: refine, gather evidence, change hardware/interface, or reject operation.
6. **Observable improvement.** Demonstrate a class where the method discovers a nontrivial useful decomposition and the retained types make the downstream controller question materially simpler. Counting a certificate as valid does not establish usefulness.

The most promising additional burden is simultaneous discovery of task-relevant interactions and a distributed executable interface under persistent coupled uncertainty. That combination is materially stronger than causal ancestor closure, sensor synthesis in a supplied model, or robust model checking alone. It still needs an actual derivation and a useful model class; the combination of words is not a theorem or novelty proof.

## 4 Statistical and logical traps

- A confidence interval for each preselected representation is not automatically valid after searching many representations using the same data. Either provide uniform coverage over the search class, a suitable sequential confidence construction, or independent validation. The computational cost of uniformity and the statistical cost of adaptivity must be counted.
- Observations under one policy do not establish transitions under arbitrary counterfactual controls without support or causal assumptions. A fixed-controller target can reduce that burden, but decomposition interfaces may still be used in contexts not represented in the data.
- Finite readouts cannot rule out arbitrary hidden physical hazards. A hazard readout or sound physical relation between the specification and measured variables is part of the assurance boundary.
- Quantitative ambiguity and state compression are different. A representation can be adequate while evidence leaves the controller's risk unresolved. Further representational refinement cannot necessarily remove that epistemic gap.
- A fixed unknown model shared across time and components must remain one model. Rectangular relaxation is allowed as an explicit conservative bound, but its gap must not be hidden or interpreted as physical behavior.
- “Minimal” always needs an order and a cost model. Coordinate inclusion, message cardinality, memory, sensing cost, latency and statistical complexity can have incomparable optima.
- Failure of a sufficient local certificate is not proof that no safe decomposition exists. Completeness must be limited to its actual certificate class unless a stronger theorem is proved.

## 5 Current audit conclusion

There is a worthwhile hard target, but the obvious individual mechanisms are well covered. The next result should be evaluated by whether it constructs a justified safety-relevant representation from incomplete evidence while producing executable joint witnesses and quantitative, nonvacuous assurance. A new finite consistency solver, robust safety checker, bisimulation quotient or sensor-selection encoding alone would not satisfy the user's stated objective.

This audit supplies design gates and primary comparisons. It does not amend the original research contract, prove the proposed result, or establish publication novelty.

## 6 Addendum: nearest baselines for the actual quantitative route (14:07 UTC)

This addendum supersedes any impression that CEGAR and sensor synthesis are the nearest mathematical engines of the completed proof. I inspected `theory/Causal_Evidence_and_Risk_Decomposition.md` and `theory/Executable_Observer_Calculus.md`. The resulting core is finite-horizon policy reweighting plus a generalized moment problem, finite LP duality, and executable observer compilation. These are established mechanisms. The specific integration is useful programme progress; this audit does not establish theoretical novelty.

### Policy change and robust off-policy evaluation

**Precup, Sutton and Singh, Eligibility Traces for Off-Policy Policy Evaluation, ICML 2000.** Author-hosted primary paper: https://web.eecs.umich.edu/~baveja/Papers/OffPolicy.pdf . This is an early direct baseline for likelihood-ratio correction between behavior and target policies. In our proof, the product of target/exploration action ratios is ordinary trajectory importance sampling. Allowing the environment to depend on complete observable history avoids a Markov assumption but does not make the change-of-measure identity a new mechanism. Known exogenous randomized exploration and support coverage are precisely what license the calculation; arbitrary passive logs do not.

**Kallus, Mao, Wang and Zhou, Doubly Robust Distributionally Robust Off-Policy Evaluation and Learning, ICML 2022.** Primary paper: https://proceedings.mlr.press/v162/kallus22a.html . They develop robust off-policy evaluation under divergence-based distribution shifts and efficient doubly robust estimation. This already combines policy evaluation with worst-case expectations and statistical guarantees. Their context/action/reward setup and divergence uncertainty sets are not our finite sequential law polytope with partially observed joint statistics. Conversely, our union-bound intervals and exact LP do not supersede their statistical efficiency results or establish robustness to unspecified deployment distribution shift. The overlap is the robust-OPE engine, not a claim of identical theorem statements.

**Kallus and Zhou, Confounding-Robust Policy Evaluation in Infinite-Horizon Reinforcement Learning, NeurIPS 2020.** Primary paper: https://arxiv.org/abs/2002.04518 . They derive sharp partial-identification bounds under explicit hidden-confounding sensitivity assumptions, using stationary occupancy ratios. Our present result instead excludes action confounding through experimentally known randomization. It admits arbitrary hidden environmental memory, but that is not the same as robustness to confounded actions. This comparison should prevent presenting causal-polytope feasibility as experimental validation.

### Marginal risk bounds and dual potentials

**Embrechts and Puccetti, Bounds for the sum of dependent risks having overlapping marginals, Journal of Multivariate Analysis 101 (2010).** Author-institution record: https://air.unimi.it/handle/2434/358569 . This explicitly treats risk bounds with overlapping marginal information and unknown remaining dependence. Thus, preserving a common joint law while bounding risk from overlapping partial views is not by itself new. Our hazard need not be a sum, and we add policy constraints, uncertainty intervals, and executable acquisition. In finite spaces those additions yield a generalized finite moment LP rather than a new duality principle.

**Fan, Park and Xu, Quantifying Distributional Model Risk in Marginal Problems via Optimal Transport, Mathematics of Operations Research, published online 2025.** Primary published paper: https://econ.washington.edu/sites/econ/files/documents/research/Quantifying-distributional-model-risk-in-marginal-problems-via-optimal-transport.pdf ; DOI https://doi.org/10.1287/moor.2024.0557 . They establish strong duality and existence for marginal laws in Wasserstein uncertainty balls, with applications to combining data sources and worst aggregate risk. Our interval/moment ambiguity differs from their transport-ball ambiguity. Nonetheless, uncertain marginal observations plus worst compatible joint risk plus dual local potentials is already a developed mathematical pattern. Calling the dual terms a decomposition must not obscure that baseline.

### Causal constraints and transport duality

**Backhoff-Veraguas, Beiglböck, Lin and Zalashko, Causal transport in discrete time and applications (2017; preprint 2016).** Primary author manuscript: https://www.mat.univie.ac.at/~mathias/Causal_arxive.pdf ; https://arxiv.org/abs/1606.04062 . Their treatment formulates causal couplings through linear constraints, obtains duality (Theorem 2.5), and develops dynamic programming. Our fixed-exploration action constraints are not literally the same two-process coupling problem, so no direct theorem identification is asserted. But encoding nonanticipation linearly and extracting dual causal potentials is established. **Kršek and Pammer, General Duality and Dual Attainment for Adapted Transport (2025)** further cover causal/bicausal and multimarginal constrained transport: https://doi.org/10.1007/s00245-025-10240-y . A finite LP cannot be advertised as advancing those general duality results.

### Exact status of the other proof ingredients

The equal-observation paired-law test is a finite partial-identification criterion. Its exact-risk row-span characterization is elementary linear algebra on the feasible affine hull; its threshold version is an LP. These are useful certificates distinguishing missing interactions from confidence width, not a new identification mechanism. Finite counterexample-guided row addition is constraint generation. Scheduled finite observer circuits have standard compositional function semantics. The source functor ensures our representations are honestly executable under the declared capability contract; it does not establish a bridge to the original C5 calculus or recover physical subsystem mechanisms.

### The mandatory centralized baseline

With complete aligned records, known exploration probabilities, a fixed target policy, and an executable hazard surrogate, the scalar `w_pi * g_plus` is already an observable statistic whose expectation is the target surrogate risk. Estimating that statistic directly can bypass decomposition entirely. Its variance and range may be poor; an expensive decomposition must show a real advantage rather than merely redescribe its expectation.

Consequently, observer decomposition is motivated here only by genuine constraints: missing cross-sensor alignment; separate owners; limited communication, timing or memory; prohibited centralized retention; or reusable capabilities across several tasks. Those constraints must come from the application, not be invented after seeing the solution. Existing full aligned data cannot be treated as unavailable just to make local interfaces appear necessary. Nor can an executable future observer supply evidence before its joint outputs are actually measured.

**Claim guidance:** describe the actual result as an exact, quantitatively sound integration of partial-evidence risk bounds with resource-accounted executable observation discovery, within the declared experiment. Do not describe it as a new robust-OPE method, new risk-duality theorem, latent physical decomposition recovery, or novelty-cleared application. The next substantive validation burden is a case where actual acquisition restrictions make the observer decomposition necessary and useful relative to the centralized weighted-risk baseline.
