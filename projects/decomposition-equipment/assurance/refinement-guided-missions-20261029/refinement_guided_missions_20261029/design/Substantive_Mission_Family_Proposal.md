# A substantive mission family for refinement guided discovery

29 October 2026. Target proposal and proof obligations only. No experiment or implementation has been performed for this proposal.

## Recommendation

Use a network of thermally limited actuators or service stations executing overlapping positive workloads. Responses have unknown sparse delayed couplings. A mission specifies jobs, release times, deadlines, physical service demand, and shared power or resource limits. Keeping every actuator off fails the task. Temperature or braking-reserve limits must hold through all delayed response tails, not merely at job completion.

The central algorithm should be evidence-constrained mission refinement: a failed mission proof identifies a relevant missing coupling or lag distinction; the agent either repairs an unnecessarily coarse representation using existing evidence or chooses a safe paid experiment that resolves a genuinely relevant ambiguity. Learned local interfaces are reused across later workload compositions.

This is a stronger application target than unknown Boolean gates. It is not, by itself, a novelty claim: safe linear system identification, robust MPC, task-oriented identification, and abstraction refinement are established. The distinctive obligation is the connection from safely acquired local evidence and discovered scopes to reusable mission certificates, with honest acquisition and verification costs.

## A tractable physical abstraction

For a first rigorous family, use nonnegative finite-memory responses

    y(t) = b(t) + sum over lags ell of G_ell u(t - ell) + r(t).

Commands u represent actuator effort or completed service load. Outputs y are calibrated thermal loads or other safety-relevant capacities. The actual nonzero input scopes, lag positions and coefficients are unknown. The permissible coefficient family, memory ceiling and bound on r are supplied. Relevant state is the actual command history; travel and idle actions continue to change that history.

Generic thermal RC dynamics do not have exactly finite memory. Either describe this honestly as a finite transport-lag synthetic family, or supply a stability-based bound for the truncated tail and include it in r. Do not equate an exact FIR simulator with validated thermal hardware. The output-to-temperature or output-to-braking relationship also needs its own physical contract.

The class may use a finite coefficient spacing and bounded deterministic observation error for exact support discrimination, or interval coefficients and a margin/slack condition for conservative approximate discovery. Finite data alone cannot certify that arbitrary unmodeled coupling is absent. Unresolved support remains possible rather than being silently set to zero.

Low-amplitude excitation is safe only because a coarse a priori response envelope proves it. Every excitation, cooldown or synchronizing interval, observation, and resource expenditure belongs to the mission accounting. There is no free reset or hidden initial temperature/history assignment.

## The prospective strictness seed

The following is a useful proof fixture, not an adequate whole research target.

Take n = 2q jobs, each requiring one unit command pulse by the end of command slot 1. Shared power permits at most q unit pulses per slot. Jobs are vertices of a connected path. Each edge e joins two jobs and has unit capacity. In the actual environment its response is

    y_e(t) = u_i(t) + u_j(t - 1),

where the path has a consistent directed ordering. One endpoint is the immediate parent and the other is the delayed parent. The coarse summary retains the unordered parent pair and the fact that exactly one contribution is immediate and one delayed, but forgets the assignment. This preserves memory length and the same action possibilities; it does not replace dynamics by a memoryless controller.

The fine model permits the first q jobs along the directed path in slot 0 and the remaining q in slot 1. Within a batch, the two contributions occur at different times; across the batch boundary, the direct contribution occurs before the delayed contribution. Every capacity remains at most one, including the final delayed tail.

Any controller robust for the coarse summary must put q jobs in each of the two slots to finish all work. Since the path is connected, some edge crosses the batches. One permitted assignment places its early job in the delayed role and late job in the immediate role, causing a capacity violation at slot 1. Waiting to diagnose this after the first batch cannot restore the deadline. Thus the fixed-budget robust certificate set is strictly enlarged by the lag-role distinction.

Safe pulses of amplitude at most one half obey the unit edge capacity, and total power remains at most q even if all jobs are pulsed. Causal pulse/flush observations can identify the relevant roles. With a bounded sparse support class, command codes can also discover actual parents rather than being given the path ordering.

This proves a difference between robust certification under two specified models. It does NOT prove that every controller receiving the original raw probe history is unable to infer the discarded role assignment. A strong unrestricted same-data controller can perform the same inference. The fixture also remains too close to a role-assignment puzzle to serve as the sole motivating result.

## Required enlargement beyond the seed

The principal family should have overlapping multi-lag response scopes, heterogeneous workloads and durations, multiple constrained outputs per job, shared power limits, and deadlines or release times that force genuinely interacting schedules. New missions must use workload combinations and orderings not simply repeated identical jobs. At least one mission-relevant counterstrategy must actually traverse multiple lag/coupling constraints before the refined certificate succeeds.

The graph may arise as a computational representation, but the result should be stated in terms of physical response interfaces and task semantics rather than claiming a graph-specific puzzle solves general decomposition. Actual functional wiring and useful history must remain outputs of discovery.

## The scaled rehearsal challenge

For a linear system with full sensing and freely scalable controls, executing a low-amplitude version of the complete proposed mission can reveal its full-amplitude response. This can bypass identification of a decomposition for a single mission. It is a serious baseline, not an implementation inconvenience.

Therefore include direct safe scaled-task rehearsal, with its actual time, cooldown and sensing cost. Also include a dense matched-memory model learner that caches observations and uses linear inference: it may reconstruct the same information as the proposed method. Do not forbid that reconstruction just to create a separation.

The legitimate benefit is likely amortized across genuinely new task compositions or the cost of maintaining and checking local witnesses. Long non-resettable workloads and paid acquisition can make repeated full-task rehearsal expensive, but these restrictions need a physical/application reason independent of winning. A full-information or dense exact model should match the learned method's capabilities; the question is what evidence, computation and interface resources are needed to reach that capability.

## Evidence constrained refinement loop

1. Compile a proposed mission against the current conservative response abstraction.
2. When certification fails, retain the actual failed safety/progress obligation or finite spoiling tree, not merely a scalar score.
3. Check whether the obstruction is compatible with the same persistent response operator and all acquired evidence. If it exists only because the abstraction independently switches incompatible coefficients or histories, refine the representation without claiming new information.
4. If it reflects a genuinely possible operator, find a permitted experiment whose outcomes separate the mission-relevant alternatives. Prove the experiment safe under every current possibility, and charge its complete duration and residual effect.
5. Update knowledge with all possible outcomes, rebuild only affected interfaces/certificates when justified, and certify a completing continuation or explicitly abstain.

A quantifier caution is essential. Robust nonexistence means that every permitted policy has some compatible persistent environment in which it fails. It does not require one environment that defeats every counterfactual policy. For example, one world may defeat action a and another defeat action b, leaving no uniformly safe successful choice even though each known world is individually controllable. Counterstrategy coherence must be checked along actual observation histories and against the declared knowledge game, not by incorrectly demanding one hidden parameter for every mutually exclusive controller branch.

## Intended theorem and test gates

- Prove refinement preserves robust certified capability under the same interface and resource contract.
- Exhibit a nontrivial task family and a checkable strictness or amortized-cost witness before outcome experiments.
- Prove the acquisition rule is safe and finite under explicit safe-identifiability and slack assumptions. Report where safe distinction is impossible.
- Discover relevant scopes and lag memory from records, without enumerating the full global operator catalogue or hiding a full control solver in a local type.
- Expose policy synthesis, evidence acquisition, conditioned constraint width, memory, communication and certificate-checking costs separately.
- Compare with robust coarse planning, matched-memory dense identification/planning, direct scaled rehearsal, and a known-kernel reference. No unsupported claim to outperform an information-equivalent optimal controller.

## Alternatives considered

A partially observed hybrid contact or traction network would be more nonlinear and physically ambitious, but finite safe acquisition becomes much harder to justify: unvisited modes can hide catastrophic transitions. It should not be selected merely to defeat the linear rehearsal baseline.

A navigation map with correlated passage hazards is easier to implement, but is at high risk of becoming another secret-bit or gate puzzle with a supplied model graph. It is a useful regression family, not the preferred central target.

The thermal delayed-workload family is the best current tractable choice, provided the main claim survives the rehearsal/dense-model baselines and the workload gate. If it does not, report that failure before running another large benchmark.

## Close baseline to examine

Lu and colleagues, Safe Exploration for Identifying Linear Systems via Robust Optimization, 2017, explicitly considers safe identification with linear constraints and a data-center cooling example: https://arxiv.org/abs/1711.11165 . This prevents claiming that safe thermal identification itself is the new result. The independent prior-art worker is checking additional adaptive robust MPC and compositional refinement comparisons.
