# Budgeted interleaved mission compatibility benchmark

Status: proposed specification and evaluation gate, not an executed experiment. The parent may freeze a smaller exact tier after implementation feasibility checks, before inspecting comparative results. Any change must be recorded. This benchmark does not itself establish a novel general theorem.

## 1. Why this family

Use persistent, unknown directed lag interactions on an overlapping ladder superscope. Productive actions and diagnostics share physical time, power, and a finite total energy budget. A productive action also provides delayed evidence useful to later jobs. Jobs have releases, multistage routes, alternatives, and deadlines. The exact decision problem is whether a single observation-based policy safely completes all jobs for every mechanism consistent with current evidence.

The superscope is supplied; the actual directed edges are not. This is justified bounded-width prior structure, not discovery of arbitrary unknown graph topology. Actual incoming scopes and irrelevant candidate edges can be learned. There is real cross-cell coupling: a work action in one ladder column can make work in the next column unsafe, and evidence plus the no-reciprocity prior can establish absence of an edge in the other direction.

## 2. World and clock

Actuator nodes form a 2 by m ladder with horizontal and vertical undirected candidate edges. Each node i has one static unknown parent P_i drawn from {none} union neighbors(i). Impose no reciprocal pair: P_i=j and P_j=i cannot both hold. A parent denotes one real directed lag edge. Multiple children may share a parent. There are no other physical edges.

At the START of slot t, the controller knows all observations through the END of slot t-1, the previous input u(t-1), completed stages, chosen routes, clock, and remaining energy. It chooses the entire vector u(t) before receiving any slot-t measurements. Inputs belong to {0,1,2}; 0 is idle, 1 is a diagnostic pulse, and 2 is a productive full-power activation.

The physical load is x_i(t) = u_i(t)/2 + u_{P_i}(t-1)/2, interpreting u_none=0. All loads must remain at most 3/2. Initially u(-1)=0. At the END of each slot all x_i(t) are observed exactly. These observations reveal which of {0,1,2} the parent carried in the PREVIOUS slot, not necessarily its identity. Equal-valued simultaneous inputs therefore yield relationally ambiguous evidence.

Per-slot power: sum_i u_i(t) <= Pmax. Total energy: sum over slots and nodes of u_i(t) <= E. Every nonzero physical input must be charged, whether diagnostic, productive, rejected in planning, or involved in a failed run; rejected proposals themselves do not consume simulated energy unless actually executed. Wall-clock computation is reported separately and must not silently become free physical time if a real-time claim is made.

A final all-zero flush slot checks delayed effects and releases persistent state. The simulator must not reset u(t-1), evidence, energy, or unfinished jobs between releases. Idle safety is automatic for this model, but must still be checked in replay.

Diagnostics u_i=1 are individually safe even after a full-power parent: 1/2+1=3/2. Full work u_i=2 is unsafe exactly when its actual parent had u=2 in the previous slot. Several diagnostics can be performed together within the power limit; the algorithm must not assume each identifies a separate column.

This is an exact deterministic unknown-mechanism benchmark. It does NOT test noisy estimation, stochastic risk calibration, an unknown baseline, arbitrary unbounded delays, or deployment timing. Those should not be smuggled into the claims.

## 3. Jobs and useful work

A job is a finite set of alternative actuator routes. One route is selected at its first productive stage, and subsequent stages must follow that route. A stage requires one full-power activation of its specified actuator in a slot at or after release. Distinct stages of the same job occupy strictly increasing slots. A single physical activation cannot count for two jobs; the controller must name the stage receiving credit. More than one job may run simultaneously on distinct actuators if power allows. Deadline d means the last useful stage finishes by the END of slot d.

The primitive tight job on a candidate pair (A,B) permits routes (A,B) and (B,A). Richer cases add length-three routes (A,B,C), (C,B,A), and alternatives using a neighboring actuator rather than a cosmetic relabeling. Route sets and workloads are sampled independently of the realized hidden mechanism, from a publicly fixed generator. Do not select jobs after looking at which edges were sampled.

Overlapping jobs share actuators and neighboring lag edges. A stage's work can provide evidence for a later release, but it can also block a next-slot work choice through delayed load. Pending effects and pending diagnostic information are both part of the physical/evidence state.

## 4. Strict learning-to-completion gate (prove before main runs)

Two actuators A,B have possible hidden relations: no edge, A->B, or B->A. No reciprocal pair is allowed. Initially idle. One job has routes (A,B) or (B,A), release r=2, deadline d=3, total energy E=5, and per-slot power Pmax=2. Useful stages cannot be done before release or in the same slot.

Positive policy: pulse A with u_A=1 in slot0; idle slot1. At end1, x_B reveals whether A->B. If absent, run A then B in slots2,3. If present, no-reciprocity proves B->A absent, so run B then A. Flush slot4. All three worlds are safe, both stages complete by d, and energy is exactly5.

Negative no-informative-interaction gate: without an informative nonzero input before release, the history at the START of slot2 is identical in all three worlds. To complete both stages by d, work must occur in both slots2 and3. Whichever first actuator is selected, its outgoing delayed effect is not observed until the END of slot3, after the second decision. One consistent orientation makes that order unsafe. A randomized choice cannot give an all-world sure guarantee either. A simultaneous activation cannot count both sequential job stages. Thus there is no uniform safe completion policy in this no-informative-pre-release policy class, although every individual world has an oracle safe schedule.

Expired-probe gate: if the first possible diagnostic is slot1, its delayed edge evidence arrives at end2, after the first productive decision. It may sometimes help particular worlds, but cannot give a uniform guarantee by d under E=5 and Pmax=2. Prove this by enumerating the finite first productive decision and all feasible slot1 actions, not by a solver timeout. At slot2 current measurement from the first work itself contains no previous full-work hazard and does not disclose its outgoing edge in time for slot3.

A full-power pre-release input u=2 is also informative acquisition even if it earns no job credit. It is legal physically, but costs2 rather than1 and therefore cannot coexist with the required4 productive energy under E=5. Negative certificates must enumerate it and reject it by budget, not silently forbid it.

Budget gate: with E=4, productive work exhausts the entire budget. The previous no-informative-pre-release argument applies. This distinguishes per-world physical feasibility from evidence-based compatibility.

Embed this pair in the ladder by holding other actuators idle and including outside parent possibilities in the evidence, rather than quietly deleting them. The clean gate is a restricted two-node submodel; the main family has the full unknown superscope.

## 5. Exact epistemic classifications

For information state K, physical input memory v, mission automaton q, time t, and energy e:

1. CERTIFIED WIN: one causal observation-based strategy is safe and completes for every mechanism in K.
2. CERTIFIED NO GUARANTEE: every policy in the declared finite action/observation model has a consistent mechanism/outcome branch that violates safety or misses the mission/budget. This does not mean every true world is impossible.
3. UNRESOLVED: computation/resource cap reached before either certificate is produced.

Report independently whether each individual world has an oracle feasible schedule. The important mixed cases have oracle feasibility in all worlds but no uniform policy under the observation/budget regime. A per-world collection of successful schedules is not a uniform positive certificate.

For realized trajectory evaluations, report actual completion separately from root robust certification. An abstention can be sound even when the realized hidden world was feasible. Never reinterpret an unresolved root as an impossibility.

## 6. Algorithms and fair comparisons

A. Factored evidence plus local certificate checker: exact junction-tree/CSP relations over P_i, with the no-reciprocity constraints retained. Query only action-relevant bags plus separators, but preserve the full archive and global consistency. Discover active/irrelevant support from evidence. Certificate nodes include the global mission/resource state, so locality does not pretend scheduling is independent.

B. Same-information, same-symbolic-representation GLOBAL planner/checker: identical candidate policies, action grammar, evidence, caching, and limits, but performs full-scope exact support queries/validation. This is the principal fairness comparison. An advantage over only a dense enumerator is not enough.

C. Explicit-world coherent solver on sizes where affordable: exact world-set updates and contingent planning. Reference implementation for correctness, not the only claimed competitor.

D. Frozen initial-evidence robust controller: can choose robust work/idle schedules but ignores later information. Its refusals must be exact for its declared policy class, not interpreted as no-learning impossibility outside that class.

E. Full-information oracle: knows actual parents and solves the same physical scheduling problem. This is an upper reference, not an attainable observation-based baseline.

Optional F. Full-identify-first controller: safely identifies all columns before serving work, with every acquisition tick/energy charged. This is diagnostic context, not the main strong baseline.

Planning is globally coupled and can be exponential. Do not claim bounded-width evidence alone makes mission planning polynomial. Local validation may win even if search uses an identical proposed policy tree; report search and checking separately.

## 7. Proposed fixed evaluation tiers

Tier0 exhaustive gates: two-node witness above, plus all allowed parent assignments for four-node ladder. Exhaustively compare transition/observation/safety semantics and winning classifications for short horizons and several budgets. Include cases with identical per-node domain projections but different relational constraints if reachable; otherwise explicitly mark such a fixture as a separate admissible evidence test.

Tier1 exact overlapping workloads: ladders n=4,6,8. Predeclare seeds (731,947), power limits (2,4), tight/roomy deadlines, and energy allowances of minimum productive energy plus (0,1,3) diagnostic units. Start with three pair jobs released at2,4,6, with adjacent pairs sampled without replacement where possible and overlapping endpoints required. Tight d=r+1; roomy d=r+3. Horizon includes the last deadline plus one flush slot. Add a separate predeclared length-three/alternative-actuator workload family rather than changing the original workload after outcomes. This is 72 settings before the additional route family; if infeasible computationally, retain all offered cases and label unresolved under a fixed cap.

Tier2 checking/acquisition scaling: larger ladders n=12,20,32 for certificate verification and policy proposals only. Exact known policies can be supplied by a declared construction, but the method must verify them from evidence and account for safe acquisition. Do not compare constructed-policy success against exhaustive search timeout as if they were equal inference tasks. Include full-scope symbolic checker on the identical certificate and evidence.

Before the main comparison, freeze machine definitions, workload generator, random seeds, deadlines, energy/power limits, solver caps, outcome definitions, and metric schema. Record development reruns and corrections. A preregistered numerical protocol is not an immutable source preregistration.

## 8. Metrics and evidence

For every offered case and method retain: root information class, win/no-guarantee/unresolved status, certificate hash, oracle status where checked, productive stages completed, safe probe count, energy, simulated ticks, learned actual edges/nonedges, columns fully identified, evidence queries, cache hits, local bag/separator visits, maximum relation cardinality, memory high-water mark, planning and certificate-checking CPU/wall time separately, rejected candidate count, timeout reason, and actual final delayed effects.

For per-case matched comparisons use identical hardware/process settings and include all failures. Memory and time ratios require the same unit and scope; do not divide Boolean invalidations by physical coefficient visits. Report uncertainty for noisy timing measurements, not just one favorable runtime.

Independent replay should reconstruct x exactly from rational arithmetic, check each stage credit/release/deadline, power, total energy, pending tail, observation order, and persistent parent assignment. Independently verify negative certificate action coverage and observation support; do not trust the searcher's cached labels. Exhaustive small instances supply an independent truth table.

The required meaningful positive outcome is completion before full identification and either reduced acquisition or reduced representation/checking cost against the strong same-information comparator. If no such advantage appears, report that result plainly. A correct compatibility certificate may still be useful, but it does not establish the claimed decomposition benefit.

## 9. Obstruction fixture for omitted shared information

Treat an observed edge A->B as evidence. The prior excludes B->A, so B then A is safe. If a local interface forwards only B's marginal currently observed load and forgets the cross-edge/no-reciprocity constraint, it can reject a safe route unnecessarily. More seriously, if it replaces correlated parent possibilities by independent favorable selections when validating consecutive work, it can accept a route unsafe in a compatible world. Construct explicit paired histories/worlds for the chosen implementation and replay both. The verifier must preserve universal support, not combine locally convenient witnesses.

Another direct failure is omitting u(t-1): identical current parent knowledge and mission position can require different legal work actions depending on the previous slot. Any proposed summary must retain the lag input or an equivalent exact sufficient statistic. This is physical-state insufficiency, distinct from forgetting relational evidence.

## 10. Limits

The strict gate is intentionally small and serves as a falsifier, not the main accomplishment. The ladder family still assumes a finite prior, exact measurements, known response coefficients, a known one-slot lag bound, known superscopes, and a bounded action vocabulary. It does not discover arbitrary physics or decide discoverability for all environments. Any main theorem must state these assumptions and explain which local summaries preserve the global mission game.
