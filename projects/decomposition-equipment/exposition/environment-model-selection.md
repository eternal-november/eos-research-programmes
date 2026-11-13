# A correspondence chart for environment models, exceptions, and replanning

> Status: Supporting modelling guidance, not a new reconstruction theorem. The AIMA dimensions organize different assumptions; they do not establish a universal hierarchy of models or a solution to planning.

The objective is to select the **least structured mathematical model adequate for a specified planning problem**, while retaining enough information to:

1. Represent the environment's admissible evolution.
2. Detect or characterize exceptions, constraint violations, and failures of feasibility.
3. Compose behavior and construct admissible replacement plans or policies.

**Qualification:** “Least structured” is relative to the required semantics and operations. No universal ordering of models by environmental complexity exists. The AIMA axes describe distinct properties of task environments; they do not prescribe a chain of increasingly sophisticated mathematical objects.

## 1. Common semantic interface

Let:

- `S` denote the state space.
- `A(s)` denote the actions enabled in state `s`.
- `T` denote the transition law.
- `Y` denote the observation space, with observation law `O` when needed.
- `K ⊆ S` denote a set of safe states.
- `Φ` denote a predicate on trajectories or histories specifying admissibility.
- `r` or `c` denote rewards or costs, when performance optimization is required.

The transition law has different types depending on the environment:

| Dynamics | Transition representation |
|---|---|
| Deterministic | `T(s,a) = s'` |
| Nondeterministic | `T(s,a) ⊆ S` |
| Stochastic | `T(s,a) ∈ Dist(S)` |
| Continuous-time controlled | `ẋ = f(t,x,u)` or `ẋ ∈ F(t,x,u)` |

The nondeterministic and stochastic models are not interchangeable: the former specifies possible successors without assigning probabilities; the latter specifies a probability law. The continuous-time forms additionally require appropriate existence, regularity, and admissibility assumptions.

These are alternatives for the dynamics component, not complete planning models. Observation laws, history dependence, time, adversarial behavior, constraints, and objectives must be supplied separately when relevant.

## 2. Correspondence chart

The rows describe **modeling triggers, not mutually exclusive environment classes**. Several rows may apply to one system.

| Environment property | Smallest commonly sufficient representation | Exceptions, composition, and replanning | When additional structure is justified |
|---|---|---|---|
| **Deterministic, fully observable, episodic, static, discrete** | A finite input–output function or relation; a partial transition function `T:S×A ⇀ S` when state changes must be represented. | An exception is an explicitly defined unacceptable outcome or failed precondition. An alternative action can be selected from those available. Episodic independence means within-episode path composition is generally unnecessary. | Introduce a state ordering only when an actual refinement, information, preference, or reachability order is defined. Multi-step planning requires transitions and paths, not necessarily a lattice. |
| **Sequential; future decisions depend on earlier actions** | An action-labeled transition system or directed multigraph. Its free path category provides an optional compositional representation. | States are vertices, enabled transitions are labeled edges, and paths compose by concatenation. Safety can be checked on paths. Replanning searches for an admissible continuation from the current state and retained history. | If history affects legal actions, constraints, or future distributions, augment the state or retain relevant history. Use automata for trace properties, temporal logic for temporal specifications, and categorical structure when composition is itself important. |
| **Stochastic** | A controlled Markov kernel `P:S×A → Dist(S)` for a Markovian model; use a measurable-space kernel for general state spaces. | Kernels compose by marginalization or integration. Failure probability can be computed for specified events. Replanning updates a policy using the current information and a declared criterion, such as expected cost or a chance constraint. | Use an MDP for controlled Markovian decision-making. Add observation structure for a POMDP; history or state augmentation for non-Markovian effects. An absorbing failure state is an optional construction, not an automatic property of stochasticity. |
| **Partially observable / unknown rules** | For partial observability: an observation map or kernel and an information state. This is a set of possible states in a possibilistic model, or a posterior distribution in a probabilistic model. For unknown rules: an unknown-model parameter or hypothesis class, with an appropriate estimator or uncertainty set. | Beliefs update after actions and observations. Unexpected observations can trigger model checking, estimation, or policy revision. Unknown state and unknown dynamics are separate uncertainties and may coexist. | Use topological structure when continuity, neighborhoods, or local observational domains matter. Use a sheaf only when compatible information or behavior over overlapping domains must be glued. Neither partial observability nor unknown rules alone requires a topology, Heyting algebra, or sheaf. |
| **Nonstationary / drifting** | Time-dependent transition laws `T_t`, or a model with an evolving parameter `θ_t`; a time-indexed transition system is sufficient when the evolution law is specified. | Time-ordered transitions compose when their input/output and time interfaces match. Model mismatch can trigger re-estimation and replanning under updated dynamics. | Use a sheaf of trajectories when restriction to subintervals and gluing compatible trajectories are relevant. Use state augmentation, switching models, or stochastic parameter processes for evolving latent dynamics. Nonstationarity of transition laws is distinct from AIMA's static/dynamic distinction, which concerns environmental change during deliberation. |
| **Multi-agent, cooperative or competitive** | A joint-action transition system with agent-indexed actions, information, and objectives. For strategic interactions, use normal-form, extensive-form, or stochastic games as appropriate. | Exceptions include safety violations, coordination failures, incompatible objectives, and deviations from agreements or protocols. Replanning may require unilateral policy revision, negotiation, or recomputation of a joint strategy or equilibrium. | Open games supply categorical composition when game components have explicit interfaces. Bayesian games handle private types; partially observable stochastic games handle private observations and stochastic dynamics. Indexed or fibred categories, polycategories, and stacks are optional tools for particular interface or descent problems, not consequences of heterogeneous agents. |
| **Continuous state or action** | A state space such as `S ⊆ ℝⁿ`, equipped with discrete-time controlled dynamics or, for continuous-time evolution, an ODE or differential inclusion. | Safety is expressed by a constraint set `K`. Replanning can use reachable-set analysis, viability theory, optimal control, or model predictive control. An admissible control must actually generate the proposed replacement trajectory. | Use manifolds and tangent bundles when smooth, coordinate-independent geometry is required. Use tangent cones for suitable nonsmooth constraints. Introduce hybrid automata when continuous evolution combines with discrete transitions. Continuity of state or action spaces does not by itself require differentiable manifolds. |
| **Real-time deadlines / irreversibility** | A timed transition system; a timed automaton for finite-state control with finitely many real-valued clocks, guards, invariants, and resets. Irreversibility may instead be represented by ordinary reachability or resource constraints. | Deadline violations are detected through clock constraints or temporal monitors. Replanning searches for a feasible timed continuation under remaining deadlines and available transitions. Clock resets are allowed only where specified by the model. | Standard timed automata admit a finite region-graph abstraction for time-abstract reachability, but the region graph is not generally a lattice. Use timed games, probabilistic timed automata, hybrid automata, or timed control models when the added dynamics demand them. |
| **Sparse / hidden reward** | A reward or cost function such as `r:S×A×S → ℝ`, possibly time-dependent, stochastic, or only partially observed. | Trajectory rewards aggregate according to a specified valuation rule. Replanning requires comparing admissible continuations by an objective. Zero reward is a legitimate value, not an exception. Hidden reward means uncertain or unavailable information about valuation. | Add reward-learning or latent-parameter models when rewards are unknown. For additive path rewards, a functor from the path category to the one-object category associated with `(ℝ,+,0)` is available. Lexicographic, path-dependent, and risk-sensitive objectives require valuation structures chosen for their actual aggregation and time-consistency properties. |

## 3. Exceptions are not one mathematical construction

Three kinds of exceptions should be distinguished.

**A. Realized violations**

A safety violation is a state or trajectory that fails a declared condition, such as `s ∉ K` or `Φ(path) = false`. This is a property of behavior relative to a specification.

A distinguished error state or output can record such a violation, but it must be added to the model with an explicit meaning. Neither an upper set in a poset nor a subobject is automatically an exception set.

**B. Model discrepancies**

An observation may contradict a deterministic model, lie outside the predicted support of a discrete probabilistic model, or be sufficiently anomalous under an explicitly selected statistical test.

These are epistemic discrepancies, not necessarily safety failures. Rare events are not automatically model failures.

**C. Obstructions to continuation**

Given a current history and remaining constraints, an obstruction occurs when no admissible continuation exists.

This is different from observing a failure. For example, a deadline might not yet have been missed even though every feasible future plan would miss it.

An obstruction can be represented by an empty feasible-continuation set, failure to extend a constrained partial trajectory, or unsatisfiability of the remaining planning constraints.

These constructions can coexist, but they are not equivalent.

## 4. Composition and replanning

**Composition** is a structural operation: it combines compatible pieces of behavior.

Examples include:

- **Transition systems:** concatenate paths whose endpoints match.
- **Categories:** compose morphisms with matching source and target.
- **Markov kernels:** compose stochastic transitions by integration.
- **Timed systems:** compose timed transitions while respecting clocks, guards, and resets.
- **Sheaves:** glue compatible local sections over a cover when the sheaf condition applies.
- **Open games:** compose game components through their declared strategic interfaces.

**Replanning** is a different operation. Given the actual observation history, current model, remaining resources, objectives, and constraints, a planner must select or synthesize an admissible continuation.

Algebraic composability alone does not establish that a continuation is safe, feasible, or optimal.

For compositional replanning, interfaces must preserve the data relevant to future feasibility: state, elapsed time, remaining resources, observation or information state, and any necessary specification-monitor state.

A replacement suffix must be compatible with the realized prefix. Conditions that depend on the entire trajectory cannot generally be validated by checking independent segments without retaining an appropriate summary of their histories.

## 5. Where lattices and sheaves actually help

### Lattices for reachability and safety

A finite set of states `S` induces the powerset lattice `(P(S), ⊆)`, with intersection as meet and union as join.

This supports operations on **sets of states**, not an automatically ordered set of individual states.

For a finite, fully observable safety-control problem with nonempty successor sets, define `CPre(X)` to be the states from which some enabled action guarantees that every possible successor lies in `X`.

Then the maximal indefinitely maintainable safe region is the greatest fixed point:

`W = νX. (K ∩ CPre(X))`

This is a genuine use of lattice-theoretic structure for exception avoidance and controller synthesis. The transition relation still supplies the dynamics; the lattice supports computation over state predicates.

### Sheaves for local-to-global consistency

A sheaf `F` over a topological space or site assigns local data to domains together with compatible restriction maps.

For open sets `V ⊆ U`, the restriction goes from `F(U)` to `F(V)`.

These maps restrict data; they are not generally forward-time evolution maps.

For a cover of `U`, compatible local sections must agree on overlaps, and the sheaf condition guarantees their unique gluing into a section over `U`.

A trajectory sheaf can encode behavior over time intervals, with restrictions obtained by shortening the interval. Failure to extend an existing partial trajectory under constraints can then express a genuine planning obstruction.

A missing global section does not, by itself, imply an empty stalk, and sheaf gluing does not optimize or synthesize a replacement trajectory.

A stack becomes relevant when local objects and their isomorphisms, rather than only set-valued sections, require coherent descent. Multiple agents do not automatically create that requirement.

## 8. Selection rule

**Start with the least structure that preserves the required behavior, information, constraints, and composition operations. Add another structure only when a specific required operation cannot be represented faithfully without it.**

A practical selection procedure is:

1. **Specify the planning contract.** Identify available observations, enabled actions, transition semantics, constraints, objectives, and the exact meaning of a successful continuation.
2. **Choose the dynamics model.** Use a transition function, relation, stochastic kernel, or continuous-time dynamical model according to the actual semantics.
3. **Add independent structure as needed.** Introduce history, beliefs, clocks, agent-indexed utilities, constraint monitors, or evolving-model parameters where they affect decisions.
4. **Choose compositional machinery for a concrete obligation.** Use path composition for sequential plans, categorical interfaces for modular processes, fixed points for relevant reachability calculations, or sheaf gluing for local-to-global consistency.
5. **Verify replanning and abstraction.** A candidate replacement must satisfy its remaining constraints. Any state abstraction or coarsening must preserve the observations, actions, temporal information, failure predicates, and performance comparisons that the planner or verifier uses.

The central distinction is between **representational adequacy**, **algebraic composability**, and **planning solvability**. None implies the others without additional assumptions.

### One-liner

**Model evolution with transitions; uncertainty with relations or kernels; information with observations and beliefs; constraints with predicates and monitors; composition with compatible behavioral interfaces; and replanning with feasibility analysis and policy synthesis. Use categorical, lattice-theoretic, or sheaf-theoretic structure when its specific operations are required—not as an automatic promotion to a higher rung.**