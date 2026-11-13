# Independent execution audit: budgeted mission compatibility

Status: IN PROGRESS. This document will receive final counts and source hashes after all frozen offered cases have been independently checked. No currently unverified case is covered by this draft.

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

Final counts and hashes pending.
