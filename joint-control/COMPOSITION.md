# Composition and useful-information assumption exchange

Status: structural derivation and assembly obligations, awaiting the component constructions and independent checking. This document is not a completed W5 result until its premises are instantiated by E/I/R/C. Its purpose is to state a dischargeable compatibility law, rather than rename whole-system winning as compatibility. The source mission and local interfaces are fixed in [SOURCE](SOURCE.md).

## A common trace and a small interface

Fix one source d and one complete causal scenario σ. Every component refers to that same run: the same physical x, domain map, current accesses, contaminated stores, acquired credentials, pending effects, local receipts, schedules and shared stock. A role budget is a projection of σ. No module is entitled to choose a different faulty set, useful calibration, spare, resource supply or initial world to establish its own premise.

For tick t, the information/restoration interface consists of: an analyst set J_t of impaired effect channels; for each i outside J_t, an actual implemented command law and effect-time error bound η_i; the actual maintenance and acquisition liability schedule; and cumulative shared cost envelopes. J_t and error certificates need not be locally known. They are proof objects describing the consequences of actual local programs and operations. A participant receives only its own permitted initialization/history and computes its own action. The nominal effect statement is required only when the detailed source demonstrates that the executable image, memory, inference and realization path currently meet it; no hidden status bit is supplied to the program.

For an affine controller u_i=K_i hat{x}_i plus bounded command rounding, define its allowed nominal effect set at physical state x by

\[
U_i^{\rm nom}(x)=\{K_i x+e:\|e\|\le\epsilon_i\}\cap U_i,
\]

where ε_i is derived from η_i, the fixed gain and the actual rounding/effect map. A direct delayed-effect lemma is required to refer this set to x at the effect time. Channels in J_t may choose any U_i allowed by their physical influence. The joint image is assembled by the source effect relation, not by assuming that a nominal authorization gate selects one global command. Overapproximation by all combinations of these sets is sound even when actual choices are correlated; it can lose precision but does not add independence premises. Negative claims cannot be reflected through that overapproximation without their own source witness.

The reusable plant obligation is a quantitative robust image inequality, for example

\[
\left\|A_\theta+\sum_{i\notin J}B_{i,\theta}K_i\right\|R
 +\sum_{i\notin J}\|B_{i,\theta}\|\epsilon_i
 +\sup_{u_i\in U_i,i\in J}\left\|\sum_{i\in J}B_{i,\theta}u_i\right\|
 +\bar w+\bar p\le R,
\]

Here B_i is the signed source effect matrix and the prescribed command is K_i hat{x}_i; the concrete removal-flow branch has negative B_i. This is an explicit algebraic sufficient condition over declared matrices, sets and budgets, not an unexplained “the product wins” premise. Source-specific C derives and verifies it or a less conservative phase condition. Physical effect bounds, both coordinates, actual throughput lower bounds, allowed individual/aggregate response and shared stock limits remain separate consumed inequalities; safety alone does not discharge them.

## X1 Local disagreement is compatible with the control guarantee

Suppose actual I/R proofs establish, under the preceding safe source history, that every i outside J_t has its actual estimate within η_i of x_t at effect time, and the bound on J_t follows from E/R's actual schedule/access theorem. Suppose C's algebraic image, service and response inequalities hold for every retained θ and every admitted J, and its resource envelope pays the same actual operation schedule. Then arbitrary differing local estimates within those bounds produce the C one-step conclusion. No equality of estimates, messages, chosen points or commanded values is required.

**Proof.** For each intact effect path write the actual estimate as x_t plus its bounded error, including the separately bounded effect delay and rounding. Substitute each distinct local error into the joint source equation. The matrix image/triangle or polytope bound is uniform over their Cartesian product and the adverse channels. It therefore applies to the actual correlated tuple. Apply the actual throughput/response inequalities to these same effects, not a second hypothetical tuple. Charge the actual probe, communication, compute and repair operations once in the shared cost bound. These establish the next source verdict and the resource update. The statement is a compatibility lemma; recurrence additionally needs the initialization and induction below.

A realized positive theorem that invokes only these bounds therefore requires a weaker coordination object than global point-value agreement. To complete the comparison, exhibit actual permitted recipients with unequal sets/estimates and show that their independently implemented choices satisfy the common guarantee; merely stating that disagreement is allowed is insufficient. This establishes sufficiency of compatible local estimates/actions in this family, not a universal communication lower bound or a claim that agreement can never help.

## X2 Closing the inference–restoration–control cycle

The induction invariant retains the source state/stock envelope, the installed/contaminated state distinction, actual pending queues, the locally computed uncertainty histories and the maintenance schedule. It is not just x∈K. The proof order is causal:

1. The stipulated commissioning family supplies initial physical uncertainty, actual image/configuration and baseline effects; damaged fields remain in their admitted support. Startup uses a direct drift/service/resource bound until the first usable observations and effects exist. It does not initialize an oracle belief with the true x.
2. Given the source envelope through tick t, nominal raw samples taken at earlier ticks lie in their true relation. Actual schedule, ingress and processing bounds imply the claimed ages. I derives truth inclusion and decision precision at the relevant recipients; it does not infer past safety from the desired conclusion.
3. E/R derives which paths have completed actual halt/write/boot, new inquiry and effect transition, and which remain impaired through contamination, access, tool reach, maintenance or old effects. Their lifetimes determine J_t. Current fault labels or a successful READY are not premises.
4. X1/C uses those derived facts and source effects to establish tick t+1, actual service and stock. The local memory/queue transition is simultaneously preserved for the next invocation.

This is ordinary initialized simultaneous induction. Conditional component lemmas may assume the already proved safe prefix, not the entire infinite desired guarantee. The program must exhibit the initial and recurring parameter regime satisfying all costs and phases together. Individually feasible modules or pairwise resource checks do not establish this step.

## X3 Replacing an information component

An I implementation can be replaced when the replacement is local-history realizable, accounts for the same joint uncertainty/fault scenario, and supplies effect-time errors no larger than the ones consumed by C, while its actual timing, side effects and joint resource liabilities satisfy the assembled inequalities. It may use different raw rows, messages or points. Preserve source units/referents, actual parameter alternatives and retained-key powers; an unexplained change there is not an implementation substitution.

The proof is direct substitution in X1 plus X2's actual temporal/resource premises. This gives a useful refinement law without erasing distinctions the mission consumes: transport only the properties supported by the new bounds. A faster nominal estimator with larger attack support or a cheaper inspector that changes the plant need not refine the old one. If it does not fit, recompute the affected inequalities or retain the failed obligation; a common type name provides no guarantee.

## X4 The required assumption exchange

The comparison baseline is the same primitive plant, mission, initial query, actuator permissions and joint fault scenario, equipped with a conditional useful-information service at the controller invocation points. That service supplies η-bounded local data by a stated deadline; it is precisely the premise previously left internal to the program. Its mathematical conditional controller result can remain useful but does not supply that service.

Remove that service while retaining only the fixed passive-sum interface: B1/B2 give a source-valid information/latency obstruction. This removal is not repaired by adding value-agreement replicas, since their histories can remain identical in the paired worlds. The replacement is I's actual requested acquisition, bounded receipts and local computation, supported by E/R's retained-credential/effect accounting. C must pay for its real time, side effects and shared cost. The common plant has those apparatus/operation primitives available to both variants; the baseline need not use them. If the available supply/deadline only supports the oracle baseline, no exchange guarantee is claimed at that parameter.

The required translation is on the consumed information/effect contract: every new source run induces a sequence of η-valid local outputs at their actual invocation/effect times, permitting X1's old conditional feedback argument. Added probe and repair events are retained in the new source trace and its cost/effect bounds; they are not silently erased from the mission. The guarantee transported is joint source safety/service/admissibility under the explicitly checked new timing/resource regime. Equal physical traces, zero-cost sensing and an exact estimator are not claimed.

Completion of X4 requires naming the actual I/E/R/C statements and a shared numerical/parametric witness. At present those are construction obligations. This document cannot itself be used to mark BC5, the useful-information exchange, or program completion as checked.
