# Potential of applications for the research programme

The completed dossiers provide a substantial foundation for demonstrations in machine learning, robotics, transactions, probabilistic programming, and compositional systems. Other applications would require importing established categorical machinery; some would justify new theorems.

The catalogue below distinguishes those cases instead of treating every application as a novel result.

## Readiness classification

| Level                  | Meaning                                                                                                                       |
| ---------------------- | ----------------------------------------------------------------------------------------------------------------------------- |
| D — Demonstration      | Existing mathematical machinery is sufficient for a bounded model. This may mean O1–O6, established external theory, or both. |
| I — Integration        | A concrete application requires a new typed interpretation, specialized proof, or bridge between established constructions.   |
| R — Research extension | Requires new general structure or a significant theorem not supplied by O1–O6.                                                |

These classifications concern mathematical readiness, not implementation time or historical novelty. They assume the submitted results at their declared scopes: principally finite, bounded sequential computations with retained witnesses, typed capabilities, qualified framing, and contextual refinement. General differentiation, feedback, concurrent transactions, and equilibrium preservation are not assumed.

## 1. Foundational categorical demonstrations

These are useful for illustrating what the framework encompasses, including familiar constructions from the attached list.

| Example                                           | Construction and demonstration                                                                                                              | Level |
| ------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------- | ----- |
| 1. Parameterized neural-network layers            | Use \\(\mathrm{Para}\\) to compose layers while retaining parameter spaces and parameter transformations.                                   | D     |
| 2. Cellular automata and neighborhood computation | Use comonadic context to model computations that read neighborhoods. Compare local rules and composed updates.                              | D     |
| 3. Graph paths and relational reachability        | Compare spans retaining intermediate paths with relations retaining only existence. Test when witness-forgetting is compositional.          | D     |
| 4. Partial parsers with exceptions                | Model parsing operations whose admissible inputs depend on earlier results, distinguishing missing data, failure, and successful output.    | D     |
| 5. Dependent probabilistic trees                  | Construct finite programs whose outcomes determine the number and type of subsequent samples. Compare raw histories with probability laws.  | D     |
| 6. Typed event pipelines                          | Combine context requirements, generated events, accumulated costs, and changes of interface. Verify composition and representation changes. | D     |

These provide relatively clean explanations of contextads, contentads, relative composition, native cells, and observational quotients. Their mathematical value is pedagogical unless they expose a new preservation property.

## 2. Neural networks and machine learning

The natural existing baseline is \\(\mathrm{Para}\\), lenses, and reverse differentiation. Standard backpropagation and several optimizer families already have categorical descriptions; the new opportunity is their interaction with dependent effects and changing capabilities.&#x20;


| Example                                        | What to construct or test                                                                                                                                                 | Level |
| ---------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----- |
| 7. Stochastic neural networks with dropout     | Distinguish reused masks, fresh masks, and shared latent randomness across layers or calls.                                                                               | D     |
| 8. Activation checkpointing                    | Prove when recomputing discarded activations reproduces the original forward values and gradients, including stochastic layers and RNG state.                             | I     |
| 9. Mixture-of-experts routing                  | A router selects a variable number of experts with different resource or accelerator requirements. Compare eager and conditional execution.                               | I     |
| 10. Speculative decoding                       | Model draft generation, probabilistic verification, rejection, and correction. Establish the appropriate public-law preservation theorem.                                 | I     |
| 11. Neural inference with external tool calls  | A speculative output requests an external operation. Separate proposed execution, authorization, commitment, and compensation.                                            | I     |
| 12. Optimizer state and representation changes | Compare SGD, momentum, or Adam under network reparameterization. Test which transformations preserve the learning trajectory rather than only the represented function.   | I     |
| 13. Model quantization and distillation        | Compare implementations under explicit numerical error, resource-cost, and contextual-observation metrics. Exact equivalence should not be assumed.                       | I     |
| 14. Input-dependent parameter spaces           | Build differential contextads where admissible trainable parameters vary with the operating regime or input type. Prove compatibility of differentiation with reindexing. | R     |
| 15. Neural architecture search                 | Model network construction where earlier results change subsequent graph topology and trainable parameter spaces.                                                         | R     |

Best bounded neural example: activation checkpointing with stochastic layers. PyTorch already provides a concrete implementation baseline and explicitly handles RNG preservation during recomputation.&#x20;

Best systems-oriented neural example: speculative inference with an external commit boundary. The underlying exact speculative-decoding algorithm already exists; the additional question concerns its interaction with irreversible effects.&#x20;

## 3. Categorical cybernetics, learning, and feedback

The main baseline is parametrized optics and bidirectional processes. Existing categorical cybernetics already treats learning, controller-environment interaction, and several reinforcement-learning algorithms.&#x20;

| Example                                                | What to construct or test                                                                                                                          | Level |
| ------------------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------------------------------- | ----- |
| 16. Finite thermostat or homeostat                     | A controller observes, updates internal state, and changes future actions. Show the sequential and optic presentations.                            | D     |
| 17. Reinforcement-learning update rules                | Express finite value iteration or temporal-difference updates using parametrized optics, then compare their effectful execution semantics.         | I     |
| 18. Partially observable controller                    | Maintain a finite belief state updated from actual evidence. Distinguish observation, conditioning, latent state, and capability changes.          | I     |
| 19. Model-predictive control with changing constraints | Earlier actions alter the feasible control set. Prove which controller substitutions preserve legality and resource bounds.                        | I     |
| 20. Dual control and active experimentation            | An action simultaneously changes the world and generates information about its dynamics. Compare information-seeking and task-performing policies. | I     |
| 21. Learned world-model revision                       | A neural transition model changes after observations, changing future action selection. Establish guarantees under explicitly bounded model error. | I/R   |
| 22. Guarded feedback for dependent computations        | Construct a general feedback operation compatible with O1's relative composition, changing interfaces, and resource typing.                        | R     |

The most interesting mathematical separation is between a finite feedback loop that can be unrolled using existing sequential composition, and an abstract categorical feedback operator that must work compositionally across an entire class of systems.

The former is currently attainable. The latter remains a genuine research target.

## 4. Open games, strategic interaction, and multi-agent systems

This category is a natural extension of the programme's double-category viewpoint. Hedges' open-game double category already supplies lenses, strategic composition, and morphisms compatible with best responses. The new question is how strategic correctness interacts with O1's effects and O5's contextual replacement.&#x20;

| Example                                          | What to construct or test                                                                                                                         | Level |
| ------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------- | ----- |
| 23. Market-entry games                           | Reproduce a standard open-game equilibrium computation and its double-category morphisms as a baseline.                                           | D     |
| 24. Strategic information disclosure             | One actor knows a mechanism's state; another must decide whether to inspect or act. Model disclosure incentives and observation limits.           | I     |
| 25. Auctions granting executable capabilities    | Winning an auction changes which operations a player is allowed to execute. Strategies and future interfaces depend on the auction outcome.       | I     |
| 26. Multi-agent resource allocation              | Multiple controllers compete for shared tools, energy, or compute capacity. Compare feasible allocations and strategic outcomes.                  | I     |
| 27. Strategic compensation and warranties        | One actor can compensate for a failed transaction but may have an incentive not to. Compare operational correctness with incentive compatibility. | I     |
| 28. Equilibrium-preserving contextual refinement | Determine when replacing a computation under O5 also preserves mapped best responses or equilibria.                                               | R     |
| 29. Dependent open games                         | Construct games whose admissible strategy sets depend on earlier outcomes, newly acquired capabilities, or observations.                          | R     |

A useful warning: an action becoming cheaper or computationally more efficient can change a game's equilibrium. Thus O5 cost refinement does not imply equilibrium preservation.

The strongest new theorem target here is a compositional interface between O1's computation cells and open-game strategy transformations.

## 5. Transactional robotics and embodied systems

This remains the closest domain to the motivating example: discovering action semantics in an environment where actions may be irreversible or only partially compensable.

There is already relevant robotics work, including TAMPURA, which handles planning under uncertain action outcomes and potentially irreversible consequences. The distinct contribution would be a categorical and typed residual-correctness result.&#x20;

| Example                                           | What to construct or test                                                                                                                              | Level |
| ------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------ | ----- |
| 30. Unknown latch or fastening mechanism          | A robot probes a mechanism, discovers whether a release action exists, and determines which compensations remain valid.                                | I     |
| 31. Adhesive or irreversible assembly             | Assembly actions permanently change the workpiece. Compensation may restore safety or usability without restoring the original physical state.         | I     |
| 32. Occlusion and blocked-access manipulation     | Moving an object changes which other objects and robot actions are accessible. A seemingly reversible move may eliminate future options.               | I     |
| 33. Consumable scientific sampling                | A robot takes a destructive measurement that changes the specimen. Later decisions depend on evidence obtained from a nonrepeatable operation.         | I     |
| 34. Tool wear and consumable resources            | Actions use up tool life, battery capacity, or material. Compare physical undo with resource and capability restoration.                               | I     |
| 35. Multi-robot task handover                     | One robot transfers control of a tool or object to another. Verify sequential ownership, capability transfer, and recovery after a failed handover.    | I     |
| 36. Discovery of previously unmodeled affordances | An experiment reveals that the initial state/action model was incomplete. Define how the model's vocabulary and admissible transitions may be revised. | R     |

For cases 30–35, a finite hypothesis space and a fixed resource-token pool allow much of the existing machinery to be reused. Case 36 requires a richer model-revision interface.

A later extension could introduce concurrent robotic transactions, but simultaneous physical operations require additional scheduler, interference, and resource-composition laws.

## 6. Distributed systems, software transactions, and autonomous agents

The classical baseline is the Saga pattern: a long-running transaction is decomposed into smaller steps with compensating operations. This already addresses partial rollback, but it does not automatically provide O1's typed capability or retained-witness semantics.&#x20;

| Example                                         | What to construct or test                                                                                                                            | Level |
| ----------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------- | ----- |
| 37. Distributed Saga workflows                  | Model multi-step operations and partial compensations. Prove residual-state guarantees under declared failure points.                                | I     |
| 38. Autonomous agents invoking external APIs    | Separate planned tool calls, actual execution, receipts, and effects. Prove a bounded replacement or commit-safety property.                         | I     |
| 39. Retried operations and idempotency          | Compare retry protocols with deduplicated execution. Preserve correlations across repeated calls and avoid inventing exactly-once guarantees.        | I     |
| 40. Rolling schema and API migrations           | Extend O6's deployment example with mixed-version clients and changing interface contracts. Test representation preservation and failure boundaries. | I     |
| 41. Escrow, authorization, and partial refunds  | Model reservation, commitment, and compensation as distinct operations. Verify which obligations survive a failed transaction.                       | I     |
| 42. Concurrent transactions and serializability | Develop a scheduler-aware calculus with interleavings, isolation guarantees, and possibly distributed compensation.                                  | R     |

Cases 38 and 39 are especially relevant to agentic software, where an internal computation may be repeated safely while an external action cannot.

Case 40 is an extension of the already completed deployment family, not automatically a new independent application.

## 7. Databases, provenance, probability, and causality

This category makes particularly good use of retained witnesses, native morphisms, and controlled forgetting.

Classical semiring provenance and relational algebra already provide mature baselines.&#x20;

| Example                                             | What to construct or test                                                                                                                | Level |
| --------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------- | ----- |
| 43. Polynomial semiring provenance                  | Annotate facts using \\(\mathbb N[X]\\); compare witness-level derivations with the resulting provenance polynomials.                    | D/I   |
| 44. Provenance-preserving query optimization        | Compare relational query plans under transformations that preserve annotated results, and identify changes to intermediate witnesses.    | I     |
| 45. Probabilistic databases with correlated records | Show why independently sampling each use of a record differs from reusing one shared random fact.                                        | I     |
| 46. Bayesian sensor fusion                          | Combine observations from multiple sensors while preserving specified dependence. Add conditioning as a separate justified operation.    | I     |
| 47. Causal intervention versus observation          | Compare observing a variable with intervening on it. Determine which dependencies and action consequences each interpretation preserves. | I     |
| 48. Continuous dependent probabilistic queries      | Use QBS or measurable-kernel semantics for adaptive queries with continuous observations, beyond finite witness carriers.                | D/I   |
| 49. Privacy leakage through retained histories      | Compare systems with identical public output distributions but different internal traces, access patterns, or timing observations.       | I/R   |

For case 43, ordinary provenance annotations are not generally normalized probabilities. A full O1 interpretation should use an appropriate semimodule or coefficient representation rather than silently assuming every annotation family sums to one.

Case 48 uses the separately established continuous QBS machinery; it should not be presented as a consequence of the finite O1 history construction.

## 8. Logic, verification, and heterogeneous semantic systems

These are natural applications of the O4–O5 typing and contextual-correctness results, with potential extensions into categorical logic and institutions.

| Example                                                        | What to construct or test                                                                                                                    | Level |
| -------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------- | ----- |
| 50. Hoare logic for dependent protocols                        | Derive preconditions and postconditions for computations whose future capability interfaces depend on results.                               | I     |
| 51. Runtime monitoring of causal event trees                   | Verify temporal, resource, and safety properties using the observations actually exposed by the execution semantics.                         | I     |
| 52. Proof-carrying capability transactions                     | An operation produces a certificate justifying later permissions. Distinguish having a proof from possessing the capability to execute.      | I     |
| 53. Grothendieck institutions for heterogeneous specifications | Assemble several logical systems and their translations into one institution while retaining each logic's origin and satisfaction structure. | D     |
| 54. Effectful computations across different institutions       | Combine O1 composition with logical-system translations. Prove preservation of satisfaction, types, and computational effects.               | R     |
| 55. Model revision that changes the specification language     | Discover new states or actions that require extending the logical signature, not merely changing numerical parameters.                       | R     |

Case 53 is established institution theory, not a new consequence of O1. The proposed result in case 54 would be an actual compatibility theorem between heterogeneous logical assembly and dependent effect composition.&#x20;

The especially interesting distinction is between updating beliefs within a fixed language and discovering that the language itself omits distinctions necessary for correct decisions.

## 9. Circuits, network interconnection, and physical infrastructure

These connect the cospan/corelation side of the attached construction map to effectful computations.

Decorated cospans and corelations already support compositional network descriptions and black-box semantics.&#x20;


| Example                                                      | What to construct or test                                                                                                                         | Level |
| ------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------- | ----- |
| 56. Passive electrical circuits                              | Compose resistor or other passive linear networks by wiring their interfaces, then compare with externally observable electrical behavior.        | D     |
| 57. Cospans versus corelations                               | Compare networks retaining internal junctions with representations that forget internal topology while preserving declared boundary connectivity. | D     |
| 58. Reconfigurable sensor networks                           | Sensor measurements determine which communication paths or sensing operations become available.                                                   | I     |
| 59. Adaptive microgrids and load shedding                    | Uncertain demand changes legal switching operations and resource budgets. Model costs, observations, and partial restoration after faults.        | I     |
| 60. Interaction between network wiring and dependent effects | Establish conditions under which interconnecting systems commutes coherently with their sequential effect composition.                            | R     |

Case 60 is the substantial generalization. Existing cospan composition does not automatically give a distributive law compatible with O1's result-dependent effects.

## Possible portfolio

Rather than pursuing all sixty, the strongest approach would be to maintain at least three distinct portfolios: illustrative constructions, bounded integration results, and foundational research targets.

Portfolio A — Illustrative demonstrations

Quick models that display the scope of the mathematics without needing a new general theorem.

Graph paths vs relations
Stochastic dropout
Finite feedback controller
Market-entry open game
Provenance polynomials
Electrical circuit black-boxing

Portfolio B — Application integration

Concrete theorems that use the current result in ways not already covered by the approved O6 casebook.

Stochastic activation checkpointing
Mixture-of-experts routing
Speculative tool execution
Robot partial compensation
Strategic disclosure and warranties
Adaptive sensor networks

Portfolio C — New structural theorems

Potentially independent research contributions, with significant unresolved proof obligations.

Differential contextads
Guarded dependent feedback
Equilibrium-preserving refinement
Dependent open games
Heterogeneous institution/effect assembly
Concurrent partial compensation

## Which examples would be the most informative?

For the next round, six stand out because each exposes a different mathematical boundary.

| Priority | Candidate                                      | Decisive test                                                                                                              |
| -------- | ---------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------- |
| 1        | Robot transaction with partial undo            | Can compensation satisfy a residual guarantee under all still-admissible environment models?                               |
| 2        | Speculative neural execution with tools        | Can speculation preserve public behavior without allowing rejected computations to change the external world?              |
| 3        | Stochastic activation checkpointing            | When can a backward recomputation reproduce the correct gradient while saving memory and preserving random dependencies?   |
| 4        | Equilibrium-preserving refinement              | When does a computational replacement preserve strategic best-response structure in an open game?                          |
| 5        | Effectful categorical cybernetics              | Can parametrized-optic controller updates coexist coherently with O1's changing contexts and effects?                      |
| 6        | Heterogeneous logic with effectful transitions | When can logical translations and computational composition be assembled without losing satisfaction or typing guarantees? |

These are deliberately different: one tests physical recoverability, one speculative execution, one learning semantics, one incentives, one feedback, and one changing logic.

The robot transaction, stochastic checkpointing, and finite open-game transaction are the strongest immediate candidates for concrete, independently checkable examples. Each can begin with a small finite model using existing results and expose a specific obstruction before committing to a new general theory.

The higher-level research opportunities are the bridges between constructions—not simply placing \\(\mathrm{Para}\\), lenses, QBS, open games, institutions, and relative pseudopromonads in one diagram, but establishing exactly which operations, observations, and correctness judgments survive their composition.