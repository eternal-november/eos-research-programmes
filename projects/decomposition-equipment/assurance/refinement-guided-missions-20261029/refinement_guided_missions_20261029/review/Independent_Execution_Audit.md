# Independent execution audit — delayed resource missions

29 October 2026. Scope: frozen synthetic FIR class and finite fixed-schedule grammar, not hardware, arbitrary feedback controllers, optimal experimental design, or literature-wide novelty.

## Decision

**Pass the final corrected execution and provenance audit, with the comparison qualifications below.** Every prescribed world, regime and method remains: 72 streams, 432 batch records including refusals. Independent standard-library integer/rational replay validates 5,967 actual physical ticks, all 289 accepted batch schedules, 4,791 proposal certificate timestamps and 2,306 rational LP certificates. No physical, delayed-tail, power, command-history or deadline violation was found. All 72 coarse initial-interface obstruction witnesses are independently checked. All 12 local/dense stream pairs have identical physical traces, raw equations, query choices, accepted schedules and outcomes.

`review/Independent_Execution_Replay.json` is the deterministic final evidence. Preserved v1 also passes a separate safety replay in `review/Independent_Execution_Replay_v1.json`; its weaker rehearsal comparison is superseded, not erased. Cost and matched summaries independently pass `review/independent_summary_checks.py` (six aggregates, four comparisons and 36 dimension/regime rows).

## Verified final outcomes

Each method receives 72 batches across 12 streams. Tick totals include failures and all diagnostic actions; different completion totals must not be interpreted as equal-work speed comparisons.

| Method | Completed batches | Completed jobs | Total ticks | Column probes | Rehearsals | Diagnostic energy (quarter-effort ticks) |
|---|---:|---:|---:|---:|---:|---:|
| Initial no-refinement interface | 0 | 0 | 36 | 0 | 0 | 0 |
| Local column | 58 | 170 | 1,250 | 120 | 0 | 120 |
| Dense column | 58 | 170 | 1,250 | 120 | 0 | 120 |
| Cached column | 58 | 170 | 1,250 | 120 | 0 | 120 |
| Corrected cached rehearsal | 53 | 159 | 1,379 | 0 | 62 | 1,333 |
| Known-kernel reference | 62 | 184 | 802 | 0 | 0 | 0 |

Matched local/rehearsal batches: 51 both complete, seven local-only, two rehearsal-only and 12 neither. Local/dense and local/cached-column completion masks coincide exactly. The known-kernel reference completes all 58 local successes plus four others. These outcomes do not demonstrate a universal acquisition or representation advantage.

All methods pay 36 startup ticks in aggregate. Each column method pays 392 singleton-tail ticks; corrected rehearsal pays 209 rehearsal-tail ticks. Service terminal tails are respectively 0, 170, 170, 170, 159 and 184 ticks. Other zero-command waiting is distinct from terminal tails. Every tail is present in the actual contiguous trace, not implemented as a hidden history reset.

## Independence and checked contracts

The independent checker imports no author simulator, planner, inference or verification implementation. It reconstructs causal convolution with exact Fractions; decodes observations from their stated physical units; independently eliminates rational observation equations; derives new dual bounds from multipliers; and reconstructs schedules from job/stage assignments. Primitive regressions pass 126 noise-endpoint decoding cases and 459 exhaustive sparse top-k comparisons, plus span/dual and delayed-violation cases. The eight original cache unit tests also passed, but are not independent evidence.

### Truth isolation and generation

Source inspection found hidden coefficients consumed only by plant dynamics, audit serialization, and the explicitly known-kernel reference. Learner decisions use observations, supplied class constants, declared missions and retained evidence. World and workload generation are separate seeded operations; workload code does not inspect coefficient values. Every realized world has the preregistered row sparsity and input/lag diversity. Cross-method and cross-regime world identity, and same-regime job identity, are checked. The generator's exactly-s and diversity restrictions are not silently substituted for the learner's at-most-s class.

### Causality, noise and evidence

Every raw evidence record is linked back to the corresponding actual command/observation segment in order, with no gap other than the explicit all-off startup. Service, rehearsal and probe histories end with L physical zero ticks. Physical disturbance and sensor noise are separately bounded by 1/256; their sum is bounded by 1/128. Quarter-amplitude response spacing is 1/16, and unit-service spacing is 1/4, both strictly greater than twice total error. Integer grid values are reconstructed from noisy readings, not copied from nominal plant truth.

Every cached certificate uses only the evidence prefix present before acceptance. Identified cached columns are separately proved from those equations. Every row-span response and final cached matrix rank is independently checked. Local and dense methods retain the same raw equations, though their declared column summary intentionally ignores extra joint constraints when constructing its conservative envelope.

### Certificates and schedules

Column envelopes equal the exact sparse top-k maximum for the stated known-column summary. Cache LP certificates are independently recomputed as valid rational weak-duality bounds for the nonnegative box/row-mass relaxation; floor rounding uses integer objectives. Floating MILP and LP statuses are never the independent proof. Every proposed schedule with a certificate and every accepted schedule is rechecked for stage/mode identity, positive contiguous durations, occupancy, releases, precedence, job deadlines, shared power, batch deadline and complete terminal tails.

Accepted direct rehearsal is independently tied to its quarter-scale trace and later identical unit-scale schedule; shifted deadlines and exact decoded peak are checked. Corrected exact-unsafe exclusion cuts are independently derived from their pre-action row-space evidence, with no physical time consumed by the cut.

## Coarse-interface witness

Each of the 72 prescribed workload specifications has a mandatory stage of duration at least two, and every alternative mode is nonempty with the same selected actuator(s) used throughout that stage. Pick any selected actuator j. The initial at-most-s class permits a persistent row with G[j,0] = G[j,1] = 4 and every other entry zero, because s >= 2 and L >= 1. On the second consecutive unit-service tick its integer load is eight, exceeding six. Thus no fixed schedule robust to that initial class can complete the mandatory workload. This is independent of the solver's infeasibility status.

This is an initial/no-refinement fixed-schedule obstruction, **not** an impossibility theorem for arbitrary adaptive controllers that refine their model from observations. The earlier temporal-path theorem remains a distinct restricted theoretical witness.

## Transparent v1 correction

The original cached-rehearsal implementation executed 68 rehearsals: 56 followed inconclusive rational-LP tests, while 12 followed exact cached row-space predictions already proving the schedule unsafe. Two additional exactly known unsafe proposals stopped for rehearsal budget. The latter replay behavior was an avoidable baseline reuse defect, not a physical safety defect.

The parent explicitly authorized a single correction: add the sound monotone exclusion cut immediately for an exactly known unsafe activation pattern, without physical replay. Source diff inspection confirms only that branch was added. No seeds, dimensions, budgets, solver limits or query-strategy parameters changed. All original results and source are preserved under `example/v1/`; only cached rehearsal was rerun. The corrected run makes 24 direct cuts, executes 62 rehearsals, and completes 53 batches rather than 49. The final composite is checked byte-for-byte against each method's actual source result, with per-method source hashes; it does not claim all methods were rerun under v2.

## Qualifications that remain

- Failure of a relaxed LP upper-bound safety test is inconclusive, not a verified evidence-compatible violating sparse operator. The final cached-column strategy makes 120 probes after these tests; corrected rehearsal makes 62 replays. These counts describe the declared strategies, not necessary acquisition. How many a stronger sparse optimizer could avoid is unestablished.
- The finite proposal limit and MILP/backend results do not prove global infeasibility, optimality or eventual mission success. Only the separate initial-interface witness supplies the stated mathematical obstruction.
- Solver and certificate-checking seconds are measured, but evidence assimilation/column promotion, simulation and serialization are not separately exhaustively charged per method. Wall-clock computation is not converted into mission ticks. No real-time hardware guarantee or exhaustive per-method CPU comparison follows.
- Sparse/local and dense methods both materialize the dense planning tensor and preserve raw data. Sparse certificate arithmetic is not a demonstrated resident-memory separation.
- Independent replay verifies all accepted trajectories and the stated certificates; it does not prove behavior on unseen seeds or all hypothetical observation histories of an unrestricted controller.

