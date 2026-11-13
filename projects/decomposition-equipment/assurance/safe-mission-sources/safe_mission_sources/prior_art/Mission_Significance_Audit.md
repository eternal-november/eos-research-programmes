# Safe mission completion: target and prior-art challenge

29 October 2026. Target-selection audit, not a novelty clearance or a completed mission result.

## Plain-language conclusion

Getting a robot to a destination while keeping it safe is already a substantial field. So are safely gathering information, breaking a mission into subtasks, and learning unknown dependencies. Merely joining those ingredients would not meet the user's request to prefer the hard problem.

The promising target is more specific: discover, through actions that are themselves safe, which histories and coupled mechanisms a mission actually requires; preserve one coherent account of the unknown environment; and turn that discovery into small reusable controller certificates. The payoff should be completion of new missions without rebuilding the entire model or solving the whole belief-state problem again. Safe probing, initialization, time, energy, and failed progress must all count.

This target is a recommendation. Its mathematical and empirical claims remain to be established. A finite version-space planner with a progress rank is a useful reference construction, but those ingredients alone are not the research advance.

## Closest primary baselines

### 1. Safe exploration already includes reachable initial conditions and returnability

Turchetta, Berkenkamp and Krause's [SafeMDP](https://papers.neurips.cc/paper_files/paper/2016/hash/9a49a25d845a483fae4be7e341368e36-Abstract.html) learns an unknown safety constraint under a Gaussian-process regularity model. It expands the safely reachable part of a finite MDP while considering whether the agent can safely get back out. Therefore replacing the supplied favorable history with a safely reachable starting region is necessary, but is not itself a new principle. The relevant comparison is the knowledge supplied about transitions, regularity, and safe seed conditions, not a caricature that earlier methods learn by crashing.

### 2. Safe task-directed learning with unknown stochastic dynamics is established

Roderick, Nagarajan and Kolter's [ASE](https://proceedings.mlr.press/v130/roderick21a/roderick21a.pdf), AISTATS 2021, provides safe PAC-MDP exploration of unknown stochastic dynamics. Its informative safe actions can establish the safety of goal-directed actions through supplied analogies. Important assumptions include an initial communicating safe set, known immediate danger/rewards, supplied analogy maps and discrepancy bounds, a minimum nonzero transition probability, polynomial communication, and sufficiently similar return paths. See Sections 3–4, especially Assumptions 1–5. This is the closest challenge to a proposal of “probe at the depot, then safely traverse a route.” A new contribution must learn useful transfer/interfaces or give a sharper class/cost result rather than quietly supply the correct analogy map.

### 3. Learning unknown factors and making conservative policy changes is not new

Simão and Spaan's [Structure Learning for Safe Policy Improvement](https://tdsimao.github.io/assets/pdf/Simao2019structure.pdf), IJCAI 2019, learns unknown parent sets in a factored MDP using KWIK-admissible learners. It compares learned structure with known-structure and flat baselines. “Safe” there means high-confidence performance nondegradation relative to a behavior policy, not absence of collisions throughout exploration. The state variables and a maximum indegree are supplied, and the standard conditional independence of next-state factors is assumed. Its experiments use flat transition estimates/value iteration even while exploiting structure for estimation. This baseline matters whenever our claim is reduced evidence cost through unknown-scope learning. The distinction must come from history discovery, coupled uncertainty, trajectory safety, or proved computational reuse, not the words “unknown structure.”

Rosenberg and Mansour's [Oracle-Efficient Regret Minimization in Factored MDPs with Unknown Structure](https://arxiv.org/abs/2009.05986) also learns factor structure while controlling regret. It explicitly assumes a planning oracle. Thus a computational claim must expose planning costs rather than hide them inside an oracle or a general controller-synthesis routine.

### 4. Compositional control of unknown stochastic networks already supports temporal missions

Lavaei and colleagues' [Compositional Reinforcement Learning for Discrete-Time Stochastic Control Systems](https://arxiv.org/html/2208.03485v1) treats supplied networks of continuous-space subsystems with unknown dynamics and known Lipschitz constants. Local minimax learning and assume-guarantee reasoning yield lower satisfaction bounds for finite-horizon co-safe temporal specifications. The network/subsystem interfaces are inputs, not discovered from unstructured records. The paper also explicitly notes conservatism and that the resulting composition need not be optimal. Therefore “learn local controllers, compose them, and prove a mission probability” is baseline capability; discovery and coherent handling of retained coupling must carry our additional burden.

### 5. Verified reach-avoid policy composition is particularly close to a delivery mission

Žikelić and colleagues' [Compositional Policy Learning in Stochastic Control Systems with Formal Guarantees](https://arxiv.org/html/2312.01456v1) learns policies with reach-avoid supermartingales and composes them through a SpectRL-derived graph. Algorithm 1 takes the dynamics function, noise distribution, initial set and specification as inputs. Its nine-room experiment already demonstrates a global mission where directly learned control cannot be verified but composed subtasks can. The verifier uses the supplied dynamics and Lipschitz information. Thus a multi-room mission with local rank or supermartingale certificates alone would be a weak novelty target. Our additional object must be the safely learned, reusable environmental representation, not just a graph of goal regions.

### 6. Partial-observation compositional shields already maintain coherent beliefs

Carr, Bakirtzis and Topcu's [Compositional Shield Synthesis for Safe Reinforcement Learning in Partial Observability](https://arxiv.org/html/2509.12085v1), 2025, combines local shields for avoidance and reach-avoid objectives, with information sharing and coherent belief-support tracking. It supports safety during and after learning. Sections 3–5 assume a partial model specifying possible transitions; Algorithm 1 also takes a decomposition strategy. The experimental decompositions are manually chosen, as explicitly stated under “Automated Approaches to Decomposition.” This is the most direct baseline for compositional online heterogeneous checking in a partially observed mission. A credible advance would discover sufficient local observers/interfaces and the relevant support from permitted evidence, while checking that the composed representation remains sound. Supplying the graph and partition would surrender that distinction.

### 7. Recent goal-driven safe exploration has physical demonstrations

Shinde and colleagues' [Safe Stochastic Explorer](https://arxiv.org/html/2602.00868v1), 2026, combines information gathering with safe goal-driven exploration, and includes continuous and object-centric cases plus hardware demonstrations. Its formal discrete formulation uses a known distribution over stochastic arrival states and learns the safety function with Gaussian processes. This is not the same unknown-decomposition problem, but prevents positioning a synthetic goal-driven exploration example as unprecedented physical progress. Our physical map and timing premises must remain separate from learned predictive structure.

Plaut and colleagues' [Safe Learning Under Irreversible Dynamics via Asking for Help](https://jmlr.org/papers/v27/25-2248.html), JMLR 2026, studies effective learning without resets, using a mentor and transfer across similar states. Its reported guarantees concern regret and mentor-query growth under online-learning assumptions. It is an important alternative information resource, not evidence that no-prior-knowledge safe autonomous discovery is generally possible. No mentor is authorized or supplied in the present target.

### 8. Logical guards require a direct safe action-model learning comparison

The SAM family is an especially close baseline if the benchmark learns logical guards and then plans. Le, Juba and Stern's [Learning Safe Action Models with Partial Observability](https://ojs.aaai.org/index.php/AAAI/article/view/29995), AAAI 2024, learns PDDL models with guarantees that resulting plans are sound, and analyzes sample complexity for probabilistic completeness under partial state observations. Thus learning preconditions from masked readouts and solving new goals is not an empty prior-art category.

Mordoch and colleagues' [Conditional-SAM](https://arxiv.org/html/2403.15251v1), ICAPS 2024, treats deterministic fully observed Boolean domains with conditional and universal effects. It proves exponential worst-case sample requirements and obtains tractability with bounded effect antecedents. Its strong safety notion requires permitted plans to be applicable and induce the same states under the unknown real model. Offline model learning is distinct from guaranteeing safe online acquisition, but simply bounding unknown logical guards and eliminating inconsistent candidates is not enough to distinguish our target.

Juba and Stern's [SAM+](https://www.cse.wustl.edu/~bjuba/papers/sam%2Baaai.pdf), AAAI 2022, learns uncertain stochastic PPDDL models from existing trajectories and supports goal generalization. It gives polynomial time/sample claims for its learned interval representation and compares goal achievement with the training-policy distribution. Its principal formulation assumes independent post-state fluent outcomes given the pre-state. This directly overlaps any claim of “learn uncertain components once and safely plan for many goals.” Persistent coupled model alternatives, online acquisition, learned recursive memory and compact evidence-to-checking could still distinguish the proposed theorem, if actually proved.

The recent [OHCAM](https://arxiv.org/html/2608.30955v1), August 2026, actively selects actions by disagreement among hypotheses about conditional and quantified effects, expands a compact hypothesis collection, and evaluates unseen tasks and hardware examples under noisy observations. Its abstract/introduction establish active hypothesis-driven acquisition as a close baseline; this audit does not infer an all-execution safety guarantee from those passages. Merely adding online disagreement-based probes to SAM therefore also needs careful comparison.

## Recommended hard target

**Safe discovery and reuse of mission-relevant environmental interfaces.**

Start from a declared class of permitted actions/readouts and bounded candidate mechanisms, a defensible initial physical uncertainty set, and a nontrivial mission. The true scopes, recursive memories, and some shared influences are unknown. The controller must choose safe informative interactions, preserve a coherent set of persistent explanations, extract a useful compositional witness, and use it to finish the mission. The output should include an executable observer/controller and a compact certificate that a separate checker can validate.

The strongest feasible theorem package would distinguish:

1. **Sound execution:** on the stated model/evidence event and physical premises, every probe, transit and terminal maneuver preserves safety. All data acquisition is included, not just deployment after training.
2. **Finite useful progress:** from the actual initial uncertainty, the certified controller reaches the task goal within an explicit resource bound or probability threshold. A safe abort is not mission completion. An infinite sequence of safe probes is not completion either.
3. **Safe distinguishability or mission-equivalence:** the candidate models need not be uniquely identified. What is necessary is either a safely obtainable discriminating observation or a common safe mission strategy for all remaining candidates. Make this condition explicit and demonstrate failure when it is absent.
4. **Discovery and reuse:** identify sufficient scopes/memory or shared constraints from the records, and reuse local evidence/certificates across a family of previously untested mission compositions. Do not first enumerate the complete joint environment and then label its projection “discovery.”
5. **Cost accounting:** charge candidate generation, safe probe travel, observation count, state/memory updates, witness size, synthesis and checking separately. If tractability needs bounded separator width, state whether that width is promised, discovered, or checked, and expose the cost of finding it.

A suitable constructed family could involve unknown cross-couplings among load, thermal state, network response and braking capacity. Safe depot interactions identify only what the next delivery needs; time or energy limits make probing everything infeasible. Persistent mechanisms recur across routes, so evidence should transfer. The actual family should be chosen by the theorem, not by superficial robotic decoration. A known route map and a physical envelope are legitimate supplied inputs if clearly distinguished from the unknown decomposition.

## Nontriviality gates before running a large experiment

- If a history-free robust controller finishes every mission with the same resource bound, discovery has no demonstrated utility here.
- If each probe explicitly names the unknown factor it reveals, ask whether the hardest interface-discovery problem was supplied in the probe vocabulary.
- If the task reduces to independent doors with one identifying bit per door, use it only as a regression test, not the motivating result.
- If all pairwise local candidate combinations are treated as possible at every step, persistent global constraints may be lost; if only convenient combinations are used, the result may be unsound. Keep one consistent version space or a proved equivalent factored representation.
- A locally narrow factor graph need not imply a compact history-dependent belief state after conditioning. Prove the claimed width bound under updates, rather than assuming local transition sparsity automatically controls inference or planning complexity.
- Rank on a knowledge state is useful, but choosing a decreasing action may itself require global synthesis. Do not bury that cost inside a local type checker.
- A minimum nonzero transition probability, known support alphabet, deterministic noiseless signatures, or finite-sample confidence argument must support any declaration that an unseen unsafe outcome is impossible.
- The preceding predictor's independent reset/warmup endpoint evidence cannot silently be reinterpreted as online samples from one dependent trajectory. Adaptive data selection requires an appropriate uniform or sequential validity argument.
- No free restart after a failed probe, simulator access to hidden modes, privileged test-state conditioning, or supplied favorable history.
- Resource bounds must include sensing, computation, actuation, probing and recovery. A deadline chosen solely to make the preferred method win is not an independent task requirement.

## Baselines and claims they can support

Use several matched-information baselines rather than one deliberately weak partition:

1. A conservative controller with the same physical premises but no new learned distinctions. This tests whether information has utility, not whether decomposition is unique.
2. A strong fixed decomposition, preferably selected on separate development instances, with the same observations and budget. This tests representation choice. Include a correct oracle decomposition separately as an upper reference, not an attainable baseline.
3. A centralized coherent full-memory/version-space solver on small instances. It must have at least the expressive capability of the proposed compact method. Matching its certified decisions while lowering cost is a good result. Claiming superior completion at equal information requires explaining approximation or resource constraints.
4. A memory/communication/coupling ablation, assessed under the same safety requirement. Its failure establishes necessity only for that specified representation, not all alternatives.
5. Probe-all and task-directed probing at equal total resource limits. This tests whether the discovery is mission-relevant rather than gratuitously reconstructing the full world.

Report certified completion, actual simulated completion, aborts, violations, elapsed steps/energy, probe costs and computation separately. A risk number, a training-confidence number and a simulation failure frequency are different evidence. If only one fixed mission is tested, do not claim compositional reuse for a mission family.

## Honest significance wording

Before results: “We are investigating when useful environmental interfaces can be learned safely and then reused to certify mission completion without rebuilding the whole joint model.”

After success, the exact supported claim should identify the class, discovered object, checkable witness and scaling parameter. The mechanisms of safe exploration, belief-state planning, rank arguments, temporal composition and statistical confidence are established. The candidate contribution is their precise discovery-to-reuse connection under information and resource restrictions; neither this audit nor the current construction establishes literature-wide novelty.

Quantaloids and institutions are possible semantic tools, not selected premises. The immediate test is whether certificates with different meanings preserve one common execution interpretation and valid assumptions. A framework should earn its place by solving that compatibility problem or reducing actual checking/discovery cost.
