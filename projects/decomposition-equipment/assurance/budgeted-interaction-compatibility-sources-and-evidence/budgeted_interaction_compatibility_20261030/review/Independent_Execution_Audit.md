# Independent execution audit: budgeted mission compatibility

Status: PASS for the final repaired 88-case benchmark, supplementary diagnosis gate, and cap-control regressions. The subsequently added, sequence-bound policy-interface wrapper also passes the separate audit below.

## Independent interpreter

`independent_execution_audit.py` imports none of the author's model, transition function, planner, or certificate checker. It enumerates legal fixed parent assignments directly from ladder adjacency and the prohibition on reciprocal pairs. There are 47, 610 and 7,791 initial worlds for n=4,6,8. Full finite ternary controls and injective job-stage credit assignments are reconstructed independently.

The separate `export_author_semantics.py` adapter imports the implementation solely to export results for comparison. Its initial deterministic audit suite checks 160 arbitrary consistent evidence/public-state configurations across n=4,6,8 and power=2,4: 11,236 legal-action reconstructions, 1,179 transitions, and 3,346 feasible joint outcomes. All agree. These are semantic regressions, not additional benchmark scenarios.

For each completed benchmark case, `audit_measured_results.py` validates the main and frozen-evidence certificates, including complete negative action coverage, unsafe witness support in an actual consistent fixed world, all positive observation branches, exact successor evidence, stage credits, releases, deadlines, energy, power, physical lag memory and safe terminal flush. Terminal deadline, productive-energy and sequential-slot lower bounds are independently reconstructed. UNKNOWN has no certificate and is not counted as a negative theorem.

Every certified main WIN is additionally replayed against every initial world, maintaining that same world throughout its trajectory. The independent replay recomputes physical load and job/resource accounting, then compares the reported acquisition/work/full-identification metrics. Local evidence-induced constant rows are counted separately from rows already constant under the initial prior and current input.

## Strong baseline fairness

The principal `local` and `smart_global` checkers currently execute the same sparse physical-row algebra and the same exact relational inference with memoization. Equality of their counted work is therefore by implementation, not an independent empirical discovery. Runtime differences between those labels are timing variability, not evidence for a decomposition speedup. The `full_scope` variant deliberately checks additional rows whose safety follows directly from their low input; it is a diagnostic weak comparator.

The implementation does not yet build a distinct CRS-reduced record representation with proof construction/amortization, nor does it discover the ladder superscope. Its evidence does identify actual parent possibilities and validate previously unavailable safe work. These are substantive learning effects but must not be confused with a demonstrated representation/checking advantage of a new decomposition algorithm.

## Sampled oracle reference

The runner validates then discards its oracle certificates, retaining only statuses and selected worlds. `independent_oracle_audit.py` therefore solves these sampled known-world scheduling instances separately. It uses a justified dominance reduction: when the world is fully known, deleting an uncredited nonnegative input lowers present and next-slot loads and energy without changing useful stage credits or losing needed information. Thus credited full-power controls and idle suffice for existence of a schedule. A cap returns UNKNOWN, never LOSE. The oracle samples are not an exhaustive claim that all worlds are individually feasible.

## Supplemental diagnosis gate

`independent_diagnosis_audit.py` validates all four supplemental certificates, 14 nodes total: pure completion at budget3 loses; diagnosis-and-service at budget3 wins; diagnosis-and-service at budget2 loses; classification at budget2 wins. The reference feasibility predicate is fixed initially (L,R feasible; broken infeasible), preventing expenditure-induced failure from being relabeled initial impossibility.

The classification implementation actually requires a singleton mechanism, stronger than distinguishing the feasibility classes {L,R} and {broken}. This does not change any of the four reported reachable-case outcomes. The report should call it full mechanism classification or retain this qualification.

## Scope

This is a deterministic finite prior with exact end-of-slot measurements, known one-slot lag and coefficients, supplied ladder candidate scopes, static unknown parents, and explicitly bounded policy search. It does not validate noisy risk calibration, hidden dynamic state filtering, arbitrary structure discovery, real-time execution deadlines, general computational discoverability, or all symbolic representations. Solver elapsed time is separate from simulated mission ticks.

## Final independent results

All 88 frozen offered cases are present and independently checked. The main classification is 42 WIN, 34 LOSE (no uniform guarantee), and 12 UNKNOWN. These comprise 36/29/7 in the 72-case pair workload and 6/5/5 in the 16-case richer-route workload.

- Main certificates: 157,342 independently interpreted nodes across 76 resolved roots. All positive observation branches and negative complete-action refutations pass.
- Frozen-evidence comparator certificates: 103,367 independently interpreted nodes; its unresolved result remains unresolved.
- Every initial fixed world for every main WIN: 102,784 trajectories and 1,028,502 physical ticks, zero violations. All reported work/acquisition/full-identification metrics agree with independent replay.
- Sampled known-world oracles: all 264 independently solved and matched, 246 WIN and 18 LOSE. These are case/world pairs, not 264 independent environments and not exhaustive per-world feasibility for every case.
- The 17 main WIN/frozen-evidence LOSE comparisons are exact within the frozen-evidence controller class. One further main WIN has an unresolved frozen comparator and is not counted as a proved strict gain.
- The evidence-constancy totals independently match: 394,257 prior/action-constant node×rows, 185,359 additional evidence-constant node×rows, and 363,284 remaining nonconstant node×rows. Counts include terminal nodes and repeated states across cases, not unique learned interfaces or physical trials. There are 2,621 productive rows in chosen positive policy actions whose safety is not justified by the original prior but is justified by current evidence.

Post-hoc descriptive partial-identification analysis also checks mission-used actuators, not merely unused nodes: among 8,751 terminal policy leaves, 5,813 retain ambiguity in parent coordinates of the actually chosen work routes. Weighted by compatible fixed worlds, this is 95,511 of 102,784 trajectories. For any actuator, ambiguity remains in 7,480 leaves / 101,513 trajectories. This is not a proof of minimum necessary acquisition or a cost advantage over the equally informed symbolic comparator.

## Budget repair and lineage

The first implementation continued exploring sibling transitions after an UNKNOWN return, exceeding the intended search budget. The repaired implementation uses immediate global budget-exhaustion propagation, checks around action generation and transitions, and clears the active stack on interruption. Five independent adversarial tests pass: zero/one-node caps, sibling-abort behavior, a slow action-generation call, and a slow transition call. None creates a false negative certificate.

The wall limit remains cooperative, not a hard real-time bound. A 25ms noninterruptible model call with a 5ms cap returns UNKNOWN after approximately25ms. Main recorded search reached24.485s under a20s soft cap; frozen search reached20.357s. Certificate extraction, serialization, replay and checking are separately outside the search cap. Terminal/memo handling is performed before a generic visit-cap check; no general callable-independent hard bound is claimed.

Original and short intermediate source/results are retained under the implementation's versioned paths and manifests. The final88 numerical scenarios, seeds, caps, allowed actions and physical semantics were unchanged. A runtime interruption after82 completed cases was resumed for the six missing cases, preserving the completed results. V1 independent audit records are retained under review/versions/v1; they are not mixed into the final counts above.

## Final source and evidence fingerprints


- example/FROZEN_PROTOCOL.json: 26f7b97ce217ce8b13d6d34ec089286c4bbc72cc214ef448497d7f1baf71e8c8
- example/CAP_REPAIR_MANIFEST.json: ec6213ad5937eb26977bae087b7553685dce232c3afda4f5afdae8034c6417d8
- example/exact_search.py: 926cb690e64b8b4334265c728133b95c8e5ee8069db64955d2188debe7256608
- example/ladder_model.py: 98fab0d7ab07dbf36a8f0f0483632e257f83959ffd92feda2b3356a82da7f954
- example/workloads.py: ad9325ef3795c02462746edfc721954e87fc0b5a20a0b2e66c59a0f57fd16a8d
- example/run_benchmark.py: d46312e947c633ac9d4af339f06d259b2b541e629e8bb804331e89603ce1d18d
- example/results/results.json: 10c47abf801c6a5a911f9726dfa288de0204204bdddc4bd012b57ff20384f3b4
- example/results/aggregate_summary.json: 3f9cdce4ad646867f70dbad0b14834efd3dc1a727505c52a5679cc2c6d54fa96
- review/independent_execution_audit.py: 6f31cbfaef50c1c5d10a9de22c9ac35184a722a668c87869bc52839e207e7a52
- review/audit_measured_results.py: 9fce439a7d8e73ea9f1af547d257d84a36692a0861e6dc65d2b43b9974e08629
- review/independent_execution_results.json: 45b20d5e6a74272303ecff3c0097ebb56caa4fba405085464ca6594e7a6b96c9
- review/independent_oracle_audit.py: 3a543d64ceafb85b471e2adf76cde20306286329d35e083262091ed25aa8156c
- review/independent_oracle_results.json: 5940c3a22834ca47f6ff0075fe73b3d9d6652a970455ab096299bffba7b27b75
- review/independent_partial_identification.py: a4c76294fe6c2dc6809bef0dc92dee9d2863ef2a8db7c48b83e80cd937161ce8
- review/independent_partial_identification_results.json: daaac37b123f70421a6d9b62b948e23adeec37e249d14e806b1da0afe6360adc
- review/independent_diagnosis_audit.py: 1140caced24deddb01e942b7c4f3977cc129a1bcda90321ef1da1d2952f852ee
- review/independent_diagnosis_results.json: ba511edff3561e6a5bf0a8a58d27e73f23df19df5555a5829a628d4d9a0093ad
- review/independent_cap_audit.py: e012ad1ce5e5e8085072768321db0ca7cccdc4e9f92d6902ed802b3fa304e282
- review/independent_cap_results.json: 246ae719f762fcd944ec82731d7bdf7224da0b9fae076cf35887fdf566ebbf7f

## Supplemental executable policy interface

The first wrapper bound observations only by value, so a stale report could be accepted after a new command when its value matched a legal branch. This was caught before release. The revised wrapper includes a nonnegative integer sequence in each report, checks it against the pending command, and leaves state unchanged on a stale-sequence rejection. Original wrapper source/results are preserved under example/versions; main benchmark evidence is unchanged.

The independent wrapper regression imports the wrapper API but none of the author ladder model, workload generator, simulator or planner. Its constructor-check adapter and simulated physical readouts use the independent dense interpreter. All47 fixed worlds /470ticks pass. It additionally checks423 previous-round stale-report rejections after new commands,470 immediate duplicate-observation rejections,470 duplicate-command rejections, isolation from mutation of the caller-owned certificate, exact integer input typing, permanent rejection of a current-round out-of-contract readout, and explicit copy/deepcopy API refusal for a live runtime. Immutable report copying remains permitted.

This is an API discipline, not authenticated telemetry, linear typing or physical capability enforcement. The host can fabricate plausible current-sequence readouts; Python private fields are not a security boundary. The host must enact commands exactly once and supply faithful corresponding measurements. Rejection after a failed premise does not itself provide physical recovery or a post-failure safety guarantee. The47-world supplemental API regression must not be conflated with the88 main benchmark scenarios.

- example/policy_interface.py: 7ecec5996dea4677149f12009cbf79f10bb367c9873d3cb4822ab7d87d3e23c7
- example/POLICY_INTERFACE_SUPPLEMENT_MANIFEST.json: 17dab6a2771a28c3363394a6eff73a6d85abe814ad2fcf41723eba4ef1c03377
- review/independent_policy_interface_audit.py: f60c6f2e0b159fba4d4c18975e50242c2366746093e4ae1803e14defe8ba9a3e
- review/independent_policy_interface_results.json: dddbc2afa140f26a89bde5a350622d787b810b38d82998c1cfafc0207219df6a
