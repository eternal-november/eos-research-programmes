# Executable shared priority transport results and limits

## Result

`python reference_shared_pipeline.py` passes:

- 60 end-to-end instances: n=2,4,6,10; identity, reverse, shuffled priority; five arbitrary seeded payload streams. Singleton calibration, persistent-resource adaptive mergesort, independently predeclared commissioning deadline, anonymous production, exact certificate and independent verification all run.
- 1,108 exhaustive binary production words across n=2,4,6,10 against a known-total-priority reference. These are arbitrary lawful outcomes, not a payload-distribution assumption.
- 24 end-to-end task-uniform acquisition cases: choose any remaining incomparable cross-role pair, perform the actual slow/fast probe, close evidence, and stop when every incomparable pair has the same role. At most the number of cross-role pairs are probed. All-same-role cases use zero joint probes. Block-role cases retain unknown within-role priorities.
- Six **physical** worlds with evidence 0<3,1<2, roles (A,B,A,B), and observed rank word 0011. All six have identical retained diagnostic raw records and production raw records; all command (1,1). Marginal possible-rank matching also permits the impossible order [0,2,1,3], giving (0,0). Thus the exact joint-poset certificate resolves a real case rejected by that marginal relaxation. The fixture generator conditions lawful bit outcomes by world; no controller receives the priority or conditioning map.

Main fullsort envelope examples (public cap Q_cap=100, R=nQ_cap; these main fixtures also happen to have true Q=100):

| n | Observed comparison counts | Predeclared T0 | Mission deadline | Actual total requests |
|---|---|---:|---:|---|
| 2 | 1 | 2400 | 2620 | 8 |
| 4 | 4–5 | 7200 | 7620 | 20–22 |
| 6 | 7–11 | 19200 | 19820 | 32–40 |
| 10 | 15–23 | 62000 | 63020 | 60–76 |

These include paid local learning; no end-to-end speedup or optimality is claimed.

## Operational model and public boundary

`Plant` has one persistent strict-priority, nonpreemptive, work-conserving arbiter and a local FIFO per module. No queue, busy state, grant or clock is reset between probes. A legal-grid batch is fully admitted before the idle dispatch at that time, including when another job completes at that exact tick. The protocol permits **one atomic batch commit per legal tick**, including empty commits. A second same-tick commit is rejected. This restriction is essential to the sharp original (n+1)/2^n success bound, not to every growing-family obstruction. Relaxing it permits a chosen singleton to start before a second same-stamped enqueue and completely solves n=2. The separate relaxed-admission theorem in `transport_theorem.md` §7.1 still proves growing failure for larger n under multiple same-tick commits. This executable continues to model the one-commit protocol; it does not implement the relaxed API.

The public callback list contains only `(time, bit)` tuples. No source, job ID, grant or priority is supplied to the learner or decision code. There is no live empty-status oracle. Initial empty state is a supplied setup premise; thereafter the controller derives drain from known total-work/report upper horizons and its own request record. An unused `_truth_empty` method is test-only, never consulted by decisions. `_truth_*` logs and hidden priority are read only by the validation oracle. The commissioning controller passes its measured local work certificate into production. Standalone controls explicitly pass supplied known-work certificates. PublicCaps supplies only the service upper cap, grid, module count and lag bound; true demand is private. An additional end-to-end fixture has true work 75 under public upper cap 100, measures P=75 and D=150, and uses those measurements without changing its previously frozen deadline.

The selected interface has productive/fast operation P of work Q and diagnostic/slow operation D of work 2Q on each addressed FIFO. This is a **richer selected interface than a previous one-address-only plant**, not an inference that every old component has a safe slow operation. Payloads are uncontrollable; calibration/probe jobs are never reused as fresh useful jobs. Fixed work under wiring, stable priority, safe gate, reliability, atomic admission, retention and no external traffic are supplied assumptions; finite timing samples do not establish them.

## Charged timing and resources

Integer supplied interface bounds: initial setup/drain 7, each probe handling/dispatch preparation 5, each probe tail 3, compile/planning 10, production checker/read/command runtime 8, final mission tail 4, gamma 20. They are independently supplied hardware implementation envelopes, **not measured Python runtimes**. Probe handling includes batch construction and pre-tick atomic submission setup. Compile covers evidence closure/check preparation and storage readiness; production runtime covers exact certification, independent verification and command output. For larger n these constants require stronger hardware or larger Q/gamma; there is no size-independent physical processing claim.

Before observations, `envelope` reserves rounded local singleton slots and joint comparison slots using the independently declared public upper cap Q_cap (P work <= Q_cap, D work <= 2Q_cap), not the unlearned true work Q. The code parameter named `Q` in `envelope` denotes this public cap:

- local: n ceil_R(Q_cap+8) + n ceil_R(2Q_cap+8);
- joint: ceil_R(7) + m ceil_R(3Q_cap+8) + ceil_R(10);
- m=n ceil(log2 n) for fullsort, or the number of cross-role pairs for uniform task learning;
- predeclared T0 equals their sum; fresh mission deadline T0+nQ_cap+20.

For the true-Q=75/public-Q_cap=100 fixture, preregistration still uses 100 and 200; measured 75 and 150 are used only afterward for safe probe timing and production interpretation. Reserved probe horizons, handling, tails, initial setup, compilation, invocation counts and grid idle are retained in results. For main equal-cap fixtures the probe horizons equal service; for the smaller-work fixture they deliberately include conservative waiting. Waiting until T0 is intentional conservative commissioning slack. Each main instance counts exactly 2n+2m_actual+n requests; none are hidden. Production reserves from the **actual current time** both runtime and final tail, refusing when `now+8+4 > deadline`, even if a nominal completion estimate would fit. Rank reliability requires learned min demand > J; lag consumes the physical observation horizon before this remaining-budget check.

Storage is finite: n local P/D measurements; O(n²) reachability/evidence for the elementary checker; O(n log n) bits for stored priority/order labels; O(n) productive bits; optional O(m) retained diagnostic records for audit (streaming can discard raw records only under a separately justified evidence-retention policy). The script retains all audit logs rather than claiming minimal memory. The bound must also pay idle energy, actuator delivery and leases in a physical implementation. Both T0 and the absolute mission deadline are frozen before learning, and production receives the latter as a required argument; it never selects a deadline from measured work. No useful loads exist before T0; their lease must cover the declared nQ_cap+gamma. Serial repair requires the longer supplied lease explicitly.

## Negative and boundary controls

- Opposite priorities produce identical complete isolated calibration histories with the same bit realization. A two-module local-only naive identity command is wrong on raw [(100,1),(200,0)] while every local intrinsic work/FIFO fact remains valid. The safe poset checker returns UNRESOLVED.
- No-learning distinct-role n=4 accepts exactly 2 of 16 words (the constant words), not all refusal disguised as success.
- Same-role partial evidence and payload-specific partial evidence both accept without full priority.
- Legal drained serialization commands correctly at time 1312 under enlarged deadline 1320, but misses tight deadline 420.
- J=3<Q positive lag passes; J=101>=Q is rejected before invocation. An explicit raw reorder [(200,1),(201,0)] demonstrates why the guard is necessary for the general lag model.
- Late admission, cyclic evidence, extra/missing manifest jobs, and insufficient actual-now residual time reject. Extra jobs are rejected before any invocation.
- Repeated same-tick commits are rejected even after an empty commit. A busy slow job is not preempted or reset when a high-priority job arrives. Completion/admission boundary test serves the newly admitted high-priority job before the old low-priority queue head.

`reference_shared_pipeline_results.json` retains fixtures/evidence and `reference_shared_pipeline_test_log.txt` records the run. The imported `poset_parity_checker.certify` and separately implemented `poset_parity_verifier.verify` check each production certificate. This executable validates the chosen structural model; it does not prove the physical assumptions, generic scheduler composition, novelty, or optimal acquisition.
