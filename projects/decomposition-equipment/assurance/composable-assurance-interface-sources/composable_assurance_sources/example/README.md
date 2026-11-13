# Executable discovered assurance interface — scoped result

## Plain-language result
The simulator starts without knowing which controls affect which cells, which sensors share queues, what history a packet averages, when it captures its data, or which errors are shared. Safe diagnostic records identify those distinctions in this separated finite family. The learned interface can then certify useful two-slot work and a polling-order replacement, while rejecting a superficially similar polling replacement that uses an extra random source frame. A whole-system checker reaches the same conclusions.

This is a **synthetic proof-of-concept with expensive commissioning**, not a deployment method or a new generic incremental verifier. The original broad discovery goal is not discharged.

## Reproduce
Python3.12, NumPy2.3.5 (recorded also in evidence metadata):

    python experiment.py
    python negative_tests.py
    python replay_observations.py
    python online_regressions.py

`PROTOCOL.md` was frozen before outcome execution. Main results include its SHA256. Code received implementation corrections for explicit FIFO recurrence, reference-trace preservation, honest operation counts and sampled diagnostic packet noise; the frozen cases and thresholds were not selected using outcomes. Final files replace development-run files.

## Scope and evidence
- n=5,10,20 hidden permuted interacting five-cycles, two seeds, global or independent-cycle source sharing: twelve acquisitions, ten offered variants each.
- Physical inference uses recorded bounded-reference pulse responses. FIFO inference uses recorded empty-queue pair completion times from a causal FIFO recurrence. Width/capture diagnostics use physically reachable reference trajectories; capture discrimination crosses a physical frame boundary.
- Calibration uses one million **disjoint width-two** windows per case. Only observable averaged residual categories enter `calibrate`; true p never enters admission. Independent physical references have bounded error. The simulator vectorizes the already-checked idle acquisition template rather than claiming 24 million separately interpreted event-loop executions.
- Exact decoded observation matrices are retained losslessly as NPZ. Raw packet/reference residuals regenerate from recorded RNG state, fixed algorithm, supplied world seed/family and NumPy version; independent replay hashes validate equivalence. The world truth used by that audit is not passed into certificate inference.
- Confidence exclusions .002 rate + .002 block sharing are distinct from the .05 **illustrative operational** allowance; physical/reference/clock/source-family premises remain supplied. For12 separate artifacts, .004 is per artifact, not a simultaneous all-experiments guarantee.
- Reports carry learned source-frame identities; full packet-window incidence matters. The accepted reordered case changes microtick order only in a drained queue and preserves windows. The main checker uses the declared queue template, not general pending-state migration. Nonempty-queue replacement is explicitly refused in supplemental regression.

## Results and limitations
See `results/results.json` for every refusal, learned interval and paid cost. Expected final totals:32/120 admitted configurations,320 nominal two-slot jobs completed,0 replay violations. Independent source clusters at n10/20 cannot fit the single global budget; no cluster-level reset is hidden. The coherent checker and same-support incremental baseline agree on all120 decisions. Conservative unresolved-sharing interfaces refuse these missions. None of those nominal replay counts estimates the rare-event risk; the source theorem and independent analytic witness establish that conditional guarantee.

Main maintenance is a **conservative evidence-validity dependency DAG**, retaining original evidence and marking downstream nodes dirty. It is not the generic candidate-relation/join-tree algorithm in the theory. Main restoration toggles stand for externally revalidated support, not a discovery algorithm that repairs corrupted past evidence.3,000 multi-update/query regressions compare cached and dense validity. Operation counts refer to different units (cached Boolean proof nodes versus full physical rows/source incidences), so they do not establish a speed advantage. Calibration/discovery dominates the accounted synthetic acquisition.

Supplemental exact-incidence tests reject marginal-only joint replacement, old-token forgetting, frame split without reaccounting, post-exposure unconditional-rate charging and expiry refunds. They implement a sufficient identity-preserving witness, not arbitrary joint-kernel equivalence.

Supplemental online regressions invalidate a premise after first work slot. Given detection before second actuation and the still-valid hard FIR/background envelope d<=1, stopping is safe through the tail (first d+.5<=1.5, stop tail d+.25<=1.25), but all five two-slot jobs fail. Existing risk charges remain. Late detection is classified assurance loss and can produce physical violation. No autonomous detector or guaranteed latency is inferred.

Unimplemented: richer ordered/alternative job synthesis, nonempty queue migration, arbitrary new hardware generations, generic correlated source laws, generic join-tree factor retraction, or complete identification outside the safely separated family. A missing safe separator causes abstention rather than invented support. No memory/speed advantage over an equally informed ordinary incremental checker is claimed.

Final correction: both checkers reject changed malformed coefficients/capture/width and an additional independent source block (`changed_interface_tests.py`). Native interface validation scans the full coefficient arrays at query time; its cost is additional to Boolean cache recomputation. Actual original/reversed polling traces are saved per case and checked against the world FIFO recurrence. See `LINEAGE.md` for development-rerun provenance and `FINAL_MANIFEST.json` for stable final hashes.
