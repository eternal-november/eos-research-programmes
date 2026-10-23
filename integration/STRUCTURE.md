# Joint local decisions, constructive gluing, and physical realization

Status: derived adapter and parametric construction, with first-pass Lean and executable checking. The relational assembly theorem is an import of established acyclic-join mathematics. This component does not assert novelty, unrestricted synthesis, completion of the whole research program, or repository acceptance. [STRUCTURE-SOURCES](STRUCTURE-SOURCES.md) records checked sources and import boundaries.

## The judgment and its scope

Fix one causal kernel with actors, local interfaces, a static unknown joint fault f, initial worlds, observation production, issued commands, actual hostile effects, conduct requirements, and service contracts. The fault label persists through observation, decision, actuation and continuation. A planner may remain compliant while its sensor or actuator fails. A forbidden Byzantine effect remains an effect of the plant; permissions constrain compliant responses and protected outcomes, not the adversary's existence.

The selected decision problem asks for one locally implementable policy that preserves a supplied finite envelope Q. Q contains the plant, pending commands, controller memories, service ages, capability modes and fault identity needed for that judgment. Q includes every admitted initialization. It need not be the maximal winning region. Closure from every member of Q can be stronger than winning from the actual initial family; those two questions are not identified here. The observation alphabet and memory representation are also fixed indices. Replacing raw reports by LOW/HIGH labels changes the strategy interface unless an additional reflection theorem is supplied.

The runtime output is one local table per executor. Offline synthesis may inspect all scenarios. No actor receives Q, the actual fault, other actors' reports or the join computation during execution. A mathematical joint effect relation describes independent causal interactions; it is not a protected execution gate.

## Compilation from the existing causal kernel

The executable imports Kernel, Node, Table, Observation and Outcome from [finite_model.py](../enforcement/finite_model.py). For actor i, a decision variable is (i,m,o), where m is its current local memory and o its current observation. Its domain consists of pairs (u,m') of issued command and next local memory. This matches Table.react: memory updates at the invocation, before the outcome. Initial-memory maps are supplied. An absent invocation supplies no decision variable and holds memory; a faulty executor's program is not followed and its bookkeeping memory is held, exactly as in the source verifier.

The absent-invocation seam is a projection, not literal equality of scopes. Python omits variables for uninvoked actors, whereas the generic Lean decisionScope includes every compliant actor's current abstract view. In the integration boundary model, that view is (memory, Option observation), and the abstract choice is (command, next memory). The issuedMask definition in CoreBridge sends None at an absent invocation, and memoryMask retains the current memory; absent_is_not_a_command and follows_masks establish that unissued abstract entries cannot affect the source round. The actual Outcome verdicts also use masked issued values and actual outcomes, so they do not judge a ghost command. This property must be checked for an adapter; an arbitrary Kernel or edgeGood predicate need not ignore ghost values.

Consequently the full relation is a cylindrical extension of the relation on consumed variables. restrict_extend, cylinder_ignores_ghosts and cylinder_nonempty_iff in Structure.lean prove exact restriction/extension and equality of nonemptiness, given a fixed fallback assignment. Unused entries may be extended arbitrarily and then normalized to the programPolicy convention (fallback command, current memory); the masks preserve the same actual runs. No currently faulty-only occurrence justifies deleting a variable that is consumed at another correct occurrence. Initial memory remains \(\mu_i(j_i)\), where \(\mu\) is fixed before f and \(j_i\) is the actor's actual initial input. Ghost extension never selects memory from the analyst's world or fault label. The executable checks sixteen local tables at fixed initial memory one, all producing (None,1) on absence, and verifies a nonempty join's exact projection from eight ghost-extended solutions to its two consumed-variable solutions.

A predecision scenario s consists of a node in Q and one jointly admitted observation tuple. Its scope V_s contains the variables of the currently invoked compliant executors. The relation R_s contains exactly those tuples whose actual kernel outcomes are nonempty and universally satisfy the conduct/world verdicts and return to Q. Service ages are updated from Outcome.delivered, not from requests, endorsements or inferred capability. A bounded service obligation is therefore part of the same transition check. Unbounded recurrent service additionally requires a supplied natural-valued rank on Q that strictly decreases on every service-free edge; missing rank data is rejected. This rank requirement is a certificate interface, not a theorem that every arbitrary representation admits such a rank.

The same local variable is reused whenever the actor, memory and local observation agree, including across different faults. Thus information is represented by variable identification; causal and institutional admissibility are represented by rows; their interaction is the natural join

\[
\mathcal J_Q=\Join_{s}R_s.
\]

The exact adapter judgment is

\[
\mathcal J_Q\ne\varnothing
\quad\Longleftrightarrow\quad
\exists\text{ one local table family that preserves every scenario in }Q
\]

at the declared local interface, initial-memory maps and supplied recurrence certificate. A joined assignment gives the table entries. Unused entries receive a declared domain value. Conversely, any table family with the stated closure property gives a joined assignment. A finite path induction proves Q membership and every actual edge verdict; the nonempty-outcome condition prevents vacuous safety. Bounded service follows from the actual age update; a natural rank cannot decrease forever on a service-free suffix.

Initialization is checked only at actual initial nodes. Membership in Q by itself does not establish that every off-reachable Q state satisfies a world-safety predicate or an initialization condition. The from-Init mission follows from a valid initial verdict and every subsequent Outcome.violations being empty, together with service-age updates. Requiring Q to lie inside a separate world-safe predicate is an additional envelope obligation; the applied physical family proves that stronger property analytically. The startup-only regression admits a legal later state that would fail the initial validator and checks that it is not rejected as an unsafe transition.

The implementation intersects constraints having the same scope while streaming scenarios. Once a tuple has failed one scenario, skipping its later tests is sound because intersection cannot restore it. This optimization does not remove an environmental successor from a retained tuple's universal check. An entirely empty observation iterator contributes an empty constraint, and an empty outcome iterator rejects the tuple. As in the source kernel interface, an individually admitted primitive branch that has no continuation must be represented explicitly as failure rather than silently omitted from an iterator.

[Structure.lean](Structure.lean) mechanizes robust-row locality from the compliant-command and successor semantics, the assignment/local-policy correspondence, run preservation, and nonblocking. Its abstract state includes the predecision information and outcome labels needed by the row. Lean keeps InitialGood separate from the per-edge edgeGood predicate; the run theorem retains the initial verdict and every edge verdict without asserting Q implies world safety. In the concrete-kernel interpretation, next masks faulty program-directive entries and quantifies their actual choices through the outcome relation, including invalid outcomes. The theorem acyclic_kernel_synthesis combines per-scenario bag coverage with running-intersection gluing to construct a local policy. The Python-to-Lean adapter is a mathematical interpretation of these fields, not a verified extraction of Python into Lean. The coordinator's separate execution bridge owns transport to the broader Execution model.

## When local compatibility becomes constructive

For relations over scopes V_s, a join tree has one bag per relation and satisfies running intersection: the bags containing any decision variable form a connected subtree. On such a tree, semijoin reduction proceeds upward and then downward. A semijoin retains a row exactly when a neighboring relation has a row with the same values on the shared variables. It never removes a global solution.

After these two passes, either the root relation is empty, proving that the original join is empty, or a root tuple can be selected and extended to each child. Running intersection ensures that agreement with the parent also gives agreement with every already selected bag. The resulting union is a single consistent assignment. The proof of this final extension construction is mechanized as running_intersection_glue; semijoin_preserves_join proves the elementary solution-preservation step. The ordered two-pass implementation and its completeness are additionally justified by the tree induction: the upward pass retains exactly the rows extendible through each subtree; the downward pass restricts them to globally extendible rows.

The theorem uses equality of overlap projections after reduction. Nonempty pairwise intersections alone are insufficient. Three binary constraints a=b, b=c and a≠c have identical overlap projections and no global solution. The executable exhibits this both as relations and as an actual Kernel with three possible contexts, absent invocations, joint conduct requirements and delivered service. Each local observer sees the same GO symbol when invoked. All eight uniform policy profiles fail, despite pairwise consistency and available actual service.

Raw policy constraints need not have a join tree. The executable can instead use an explicitly checked tree decomposition: every original constraint is assigned to a bag containing its scope, and bag relations are computed from exactly those constraints. This transformation preserves the complete join because bag coverage loses no constraint and running intersection loses no identification. Its cost is indexed by the largest bag and domain sizes. For binary variables, enumerating a bag of width w can require 2^w rows. A single bag containing every variable is always a possible exact fallback, but supplies no structural speedup. Physical topology alone does not certify decision-scope acyclicity: private observations and cross-fault aliases can create additional overlap cycles.

Acyclicity of a single decision slice does not discharge continuation. Here every row already checks return to Q, using the same policy variables. A different construction that independently re-solves each slice must prove a compatible continuation law. The finite relation procedure does not decide unrestricted distributed synthesis or discover every useful invariant.

## A heterogeneous family with changing physical capabilities

The applied family extends the existing independently driven PeerBrakes kernel. There are three independent brakes, a motor/output chain, one-step command FIFOs, speed x, heat h, and a capability mode z. Let b_i(z) be positive integer force numerators with

\[
b_i(z)\ge1,\qquad \sum_{i=0}^{2}b_i(z)\le30.
\]

An arbitrary finite set of such modes may be installed; the environment may choose the next mode on every transition. Planners do not observe the mode. Actual engagements e_i are binary. An intact effect path applies its queued command; a compromised actuator may independently choose either engagement. The joint fault permits at most one index in the union of compromised planners and actuators. Motor/output compromise is separately recorded in the same f, not re-selected at each component proof.

The actual recurrences are

\[
x^+=\max\!\left(0,\left\lfloor\frac{5x+10u-\sum_i b_i(z)e_i}{10}\right\rfloor\right),\qquad
h^+=\left\lfloor\frac{5h+x\sum_i e_i}{10}\right\rfloor.
\]

A normal motor supplies u=4 and delivers x^+; a compromised chain chooses u∈{0,…,6} and may withhold output. The heat relation intentionally charges engagement rather than weighted force. These are declared quantized mechanics, not a calibrated physical scaling law. Every faulty engagement has its actual speed and heat consequences.

The LOW/HIGH observation interface is inherited from the source kernel's error-one, threshold-three frontend. HIGH implies x≥2, and x≥4 forces HIGH at each compliant invocation. The source-path correctness premise and its threshold quotient remain those of [FINITE](../enforcement/FINITE.md). Source identities erased by that frontend are not newly identified by this construction; a new source/capability correlation would require retaining its fault information or proving the quotient still sufficient. The local conduct rule permits ON only at actual invocation speed at least two.

Choose any two or three planners to use LOW→OFF, HIGH→ON; all remaining planners always issue OFF. The analytic envelope has 0≤x≤10, 0≤h≤6, normal-motor x≥1, binary queued commands, and

\[
x\ge8\ \Longrightarrow\
\exists i\notin(\mathrm{planner}(f)\cup\mathrm{actuator}(f)):
\mathrm{pending}_i=1.
\]

The initial speeds 0,…,4 (or 1,…,4 for a normal motor), heat 0,…,6 and OFF queues satisfy it. This envelope is specified before synthesis rather than defined to be a computed winning set.

The proof has four coupled steps. If x≤7 then x^+≤9. If x≥8, the pending witness contributes at least one force numerator, giving x^+≤⌊109/10⌋=10. If x^+≥8 then x≥4, so every threshold planner received HIGH; at least one of the two selected planners has both intact execution and actuation, establishing the next pending witness. For a normal motor, total force at most thirty gives x^+≥⌊(5+40−30)/10⌋=1. Finally h^+≤⌊(30+30)/10⌋=6. HIGH also proves the issued-conduct rule. All four arguments concern the same transition and f, including capability changes and malicious effects.

The executable uses force modes (4,10,16) and (7,9,14), twenty fault scenarios and six local decision variables. It constructs the analytic envelope and relations, obtains four local policy rows, and replays every returned row with the existing source verifier. Its raw scopes are not asserted acyclic: a six-variable device bag records the actual local synthesis cost.

For a fleet of J≥2 devices, retain one global fault whose projections satisfy the preceding conditions and whose faulty motor/output set has size at most p<J. The actual product kernel sums actual deliveries; every global transition projects to the corresponding local transition. Hence the product of the envelopes is closed and actual aggregate delivery is at least J−p each tick. Separate heat stores obey total heat at most 6J. This is a product of separate stores, not a proof for an unmodeled smaller shared thermal resource. A shared resource requires its own relation and can introduce additional bag overlap.

The executable instantiates two devices with one shared brake-owner fault budget across the whole fleet and at most one faulty motor. It extracts the two local tables by a two-bag join, checks every joint fault projection, and exercises every physical outcome at a declared initial boundary state with differing capability modes. The all-run guarantee comes from the product closure and actual-output argument, not from claiming those boundary probes enumerate the full global graph. Correlated faults are retained in the product fault object; no global runtime gate is introduced.


## Overlapping physical assembly through one shared planner

A second fleet interface makes the join overlap operational. Five planners control two devices: planner 0 supplies brake 0 on both devices, planners 1–2 supply the remaining brakes on the first device, and planners 3–4 supply those on the second. A compliant shared planner issues one command, which is passed to its two independent queued effect paths. A compromised shared planner may send distinct commands; compromised shared effect ownership may affect both brake-0 paths. The same global fault explicitly correlates those roles. This is a shared command source, not an executor through which the other motors or brakes must obtain permission.

Planner 0 receives a designated pair signal: PAIR_HIGH is the conjunction of the two source frontends' HIGH bits. Its selected program interface retains that conjunction; it does not claim completeness for programs reading the two bits separately. The four other planners retain their original target-local observations. PAIR_HIGH certifies that both current speeds are at least two. If either target cannot support HIGH, the pair signal is LOW. No target identifier is silently erased to equate two different views.

For local verification, each device exposes a shared-signal port. Its contract permits PAIR_LOW at any speed and PAIR_HIGH only when that device's speed is at least two. It does not promise HIGH when that target alone is fast. Each actual pair signal projects into both component ports. This sound overapproximation forgets correlations between the targets; it can make local synthesis stricter and is not claimed to reflect every global winning policy.

The two nonshared planners on each device use threshold control, while the shared planner may use either PAIR_HIGH→ON or always OFF, with PAIR_LOW→OFF. At speed at least four both nonshared planners receive HIGH. One survives the local union fault bound, so the analytic Q proof still establishes continuation even when the shared signal is LOW. The shared PAIR_HIGH→ON choice is factively permitted on both devices. It has actual independent braking and thermal consequences.

Each component has six decision variables, but the two shared-planner variables are identical in both bags. The global controller consequently has ten variables, rather than twelve independently assignable entries. The two-bag tree has a two-variable separator. Semijoin extraction selects a shared PAIR_HIGH→ON policy and four target-local threshold policies. The local six-variable search cost is retained; no ten-variable policy enumeration is needed for this construction.

The physical composition argument has three obligations. First, actual observations project into the component contracts, preserving the shared signal and each target-local view. Second, every global outcome projects into each component's actual outcome under the projection of the same f; the shared compliant command is equal on both paths, while faulty commands and engagements retain their independently admitted effects. Third, the component envelopes imply the aggregate mission: at most one faulty motor/output chain leaves at least one positive actual delivery, and the two separate heat stores remain bounded. These obligations prove a sufficient global all-run certificate. The join is exact for the two component closure contracts; their observation overapproximation is why it is not advertised as complete synthesis for the entire physical fleet.

The executable checks all 121 speed pairs and every corresponding admitted observation tuple for the first obligation, all forty-eight joint fault scenarios and every boundary effect for the second, and actual summed delivery on those effects. The general all-run proof uses the factorization and component closure, rather than treating these probes as a complete global state traversal. Modes differ between devices and can change on the same transition. Each individual shared or private planner and effect owner occurs in a compromised scenario.

The same assembly extends to any finite J≥2 devices. One shared planner receives ALL_HIGH, the conjunction of the J target frontends' HIGH bits, and controls one brake per device; each device retains two private threshold planners. Each six-variable bag shares the same two ALL_LOW/ALL_HIGH entries, so a star join has width six while the full policy has 4J+2 entries. Arbitrary heterogeneous mode sets satisfying the displayed force bounds may be chosen per device. The local observation/effect projection and Q arguments are unchanged. Any one global fault family with each device's union fault bound at most one and at most p<J faulty motors gives actual aggregate service at least J−p. A shared-owner fault may affect that owner's brake on every target. Obtaining the J source bits at the modeled synchronous invocation is an explicit input/timing premise, not a free communication theorem. The executable instantiates J=2; the finite-tree theorem and this factorization argument establish the parametric statement.

A coupling obstruction changes the two response rules while preserving the physical system: at a shared PAIR_HIGH invocation, the first device requires the shared command ON and the second prohibits it. Both local physical contracts have individually valid policies; their permitted shared-variable projections are respectively {ON} and {OFF}. The semijoin becomes empty. In the actual kernel, the admitted all-compliant initial state with both speeds four produces PAIR_HIGH, and either binary command violates one duty on every physical outcome. This is a concrete authority/composition obstruction, not an argument that normal positive operation violates its rules.


## Supports, obstructions and the ordinary quorum specialization

Resource access structures are legitimate only under a proved order. Fix the task, fault family, effects and admissible policy witnesses. Let a resource set K make precisely those witnesses available whose required resources lie in K. If K⊆K', the same witness can be reused, so feasibility is upward closed. optional_resources_monotone proves this order. It does not apply when adding autonomous actors also adds hostile force, compulsory duties or interference.

For finite optional resources, take the clutter C of inclusion-minimal sufficient supports. Its blocker consists of minimal sets meeting every member of C. Availability K contains a sufficient support exactly when its complement contains no blocker. support_obstruction_dual mechanizes the underlying support/complement judgment; finite minimalization and blocker involution are imported established results and exhaustively checked over all 168 clutters on four resources, including the degenerate families. The required supports must be obtained from the joint control judgment. Three separately feasible evidence, influence and permission supports do not imply one compatible policy; a mixed empty join is an obstruction to their assembly.

The permission extraction applies this duality to the actual joined brake rows, rather than to an unrelated set family. Let K be the indices whose compliant programs may issue ON at their selected HIGH view. Keep the physical plant, joint fault family, Q, initial-memory maps and observation class fixed. Define

\[
\mathcal J_Q(K)=\{r\in\mathcal J_Q:\forall i\notin K,\ r(i,\mathrm{HIGH}).\mathrm{command}=0\}.
\]

Every LOW entry is already OFF in the computed relations. Each row's used-resource set is read from its actual HIGH commands; minimalization gives the sufficient supports, and hitting-set dualization gives the blockers. The executable tests every enabled subset and every inclusion between subsets, preserving the same row witness when permissions grow. These are permissions on compliant programs, not removed actors, disabled actuators or filtered Byzantine commands.

For the four joined switching-device rows, the extracted minimal supports are {0,1}, {0,2} and {1,2}, and their blocker is the same three pairs. An enabled pair retains one policy; all three permissions retain four; zero or one retains none. For the two weak shared-port rows, the minimal support is {1,2}, the two private planners, and the blockers are {1} and {2}. Enabling the shared planner additionally permits its PAIR_HIGH→ON row but is not necessary for this component's closure guarantee. These families are exact for the supplied Q and selected memoryless LOW/HIGH interfaces; they are not a characterization of arbitrary-history controllability or physical component deletion.

For both kernels, a concrete probe fixes enabled programs K={1,2} while planner 0 is OFF whenever compliant. With its actuator compromised, two actual outcomes retain its uncommanded engagement. With its planner compromised, two outcomes retain its ON command and place that command in the FIFO despite its missing compliant-program permission. K is never passed into the physical outcome enumerator. Thus the resource restriction cannot manufacture resilience by removing the hostile effects it must tolerate. The different support and blocker families arise from the jointly checked evidence, surviving influence, permitted commands, delayed continuation and actual-service obligations; their cardinalities alone do not establish a signing-quorum theorem.

Ordinary quorum geometry is recovered only after the signing and transition interfaces align. [QUORUM-ALIGNMENT](../research/QUORUM-ALIGNMENT.md) and its Lean module provide the existing specialization: generated correct signing obeys an own-history exclusivity guard; accepted certificates refer to actual authenticated issued shares; honest intersection excludes conflicting certificates; availability additionally needs an all-correct available support and actual common-value publication. A transition must then check that current scope and certificate and realize the specified effect. Those hypotheses connect an ordinary quorum to this component's row relations. Q3 alone proves neither physical capability nor recurring service, and the independently actuated brake construction does not pretend that its mechanical effects are quorum-gated.

## Evidence and residual obligations

Run the Python component with --check to reproduce [structure_results.json](structure_results.json). It binds normalized hashes of the compiler, Lean module, these documents and the imported kernel. Run Structure.lean with Lean 4.33.0 to check its nineteen theorems. The first-pass executable evidence includes all 256 binary two-edge relation databases, the cyclic control obstruction, service/nonblocking/initialization failures, all four-resource clutters, permission supports and blockers extracted from the actual joined rows, absent-variable projection, the complete supplied-envelope constraint compilation, independent source-verifier replay, the joint fleet boundary cases, the shared-planner observation/effect projections, and the conflicting-duty outcome witness. The twelve-module join-chain regression is an algorithmic width check only; it claims no extra physical coordination mechanism.

The checks do not prove empirical fidelity, compiler extraction correctness, maximality of Q, raw-report completeness, or unrestricted synthesis. The symbolic row and tree statements support arbitrary typed models within their hypotheses; effective finite computation additionally needs explicit finite domains. Independent review of this session's adapter, implementation and physical-family proof remains a separate integration obligation. Repository acceptance remains pending.
