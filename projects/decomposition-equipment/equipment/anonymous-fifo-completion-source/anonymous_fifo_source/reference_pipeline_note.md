# Executable anonymous FIFO reference — 2026-10-31

Run `python reference_pipeline.py` and `python reference_baseline.py` in this directory. The pipeline imports the included polynomial checker from `binding_checker.py`; no network or packages are needed. Results are deterministic JSON; rational timestamps are serialized as exact strings, not floats.

## Implemented boundary

`Plant` privately owns fixed queue membership, fixed per-address duration, persistent busy times, delivery events and tie priority. There is no reset method. Collection advances a real release clock; diagnostic waits cover a known number of requests using D,J and physical-tail allowance. An initially empty state and diagnostic isolation are trusted capabilities. A regression submits a second request while the first is still busy and checks completion at 10 rather than 6.

A report is **only `(arrival_time, binary_payload)`**. Binary values are arbitrary correlated mission data, never pilots. The public probe ledger additionally records controller-known submitted addresses, release time and drain reservation. Private service truth is stored separately under `validation_private`; it is not an argument to the planner, inference or report controller. Function-signature/AST checks and a hidden-world mutation regression audit that boundary (not a language-level noninterference proof).

Solo intervals, pair-maximum band separation and equivalence-relation consistency recover routing or refuse. The planner uses the global enclosing L,U,W, inferred q,h; chooses the first strictly admissible Q-grid Delta; checks both strict timing inequalities and `(h-1)Q<L`; dispatches actual jobs with per-queue first offsets and Q-grid internal spacing. Actual report windows use per-job max-plus interval recurrence, not an assumed common duration. Acquisition waits and next admissions round upward to the request grid. Fractional D/J/tail/compute regression checks this rounding; actuator and calculation completion need not lie on the request grid.

The runtime constructs the whole report-job graph, invokes and independently validates the existing matching certificate, and fires only for a certified role-parity vector. Private validation checks inclusion of the physical assignment and equality to the XORs of the same actual service payloads by physical role. A real two-queue reversed-arrival trace has overlapping windows: same-role ambiguity certifies; changing the roles makes it unresolved and refuses. This illustrates acceptance without unique report identification.

## Results

12 runs: `(q,h)=(2,2),(2,3),(3,3),(4,4)`, seeds 0,1,7. All fired correctly. Actual equal durations belong only to fixture construction/private validation, never a homogeneity assumption given to the algorithm. Jitter cycles through both adversarial endpoints and intermediate values; payloads are correlated. Illustrative seed-zero costs:

| n | charged commissioning finish | post-release bound | total finish | physical serial service lower bound |
|---:|---:|---:|---:|---:|
| 4 | 1830 | 214 | 2051 | 400 |
| 6 | 5547 | 437 | 5991 | 840 |
| 9 | 17325 | 623.5 | 17955.5 | 1800 |
| 16 | 90552 | 1400.5 | 91959.5 | 5440 |

The commissioning envelope, T0, and fixture deadline are fixed before any probes: the envelope uses only n and declared caps, and the mission deadline is part of the fixture design contract, not chosen from observed outcomes. Returned acquisition cost must fit that predeclared envelope. Total finish includes commissioning, a charged wait to independently supplied T0, service reports, compute/status allowance and physical tail. There is **no one-mission end-to-end speedup claim**. Status/compute are declared hardware time allowances in the executable model, not measured Python WCET guarantees. The program does not establish those capabilities or the physical downstream hazard law.

Controls pass: missing timing margin/ambiguous acquisition refuses; impossible perturbed pair refuses; invalid bound refuses; surplus duplicate refuses by report count; missed deadline refuses; cross-role ambiguous graph refuses; same-role ambiguity certifies; true assignment stays in graph; hidden truth mutation leaves planner output unchanged. Exactly-once delivery remains a trusted premise: an undetectable equal-count replacement/duplicate cannot generally be ruled out from anonymous tuples.

## Comparators and limits

`reference_baseline.py` accepts **no true partition**. It computes a robust marginal window hull over every possible unknown partition, either explicitly or by an equivalent monotonicity formula. The scalable formula is compared with exhaustive enumeration on 120 deterministic small fixtures. Tight global staggering fails its sufficient disjoint-window certificate on these runs; that is not a claim that every global-stagger policy fails. Slower global staggering is also evaluated and certified in every run, and a partition-free serial-and-drain baseline is available. No comparator optimality claim is made. Marginal hulls can refuse jointly feasible schedules.

The growing examples and finite tests are implementation evidence, not uniform proofs. The separate deadline obstruction proof establishes the tau=Q sharp deadline result; this program does not manufacture a negative conclusion from a failed matching certificate. The trusted same-service physical XOR interlock bridge, FIFO/repeatability, diagnostic safety, reliable delivery, service bounds, and actual computation/tail guarantees still need independent physical validation. There is no hardware safety certification.

## Runtime and resource boundary

`control(plan,reports,caps,deadline,now)` takes an actual public current-clock reading, rejects future-dated reports, and gates firing on `max(now,last_arrival)+compute+status+tail <= deadline` as well as the plan's bound. A late-invocation regression now refuses even when the stored packet timestamps and planned finish would have fit. The 7-unit commissioning-to-T0 gap is explicitly `Caps.planning`, a declared planning WCET allowance fixed before acquisition, not unexplained free computation. All compute/status/planning allowances remain hardware premises, not measured Python WCETs.

Memory, energy and finite global dispatch-port capacity are **not quantitatively checked** by this reference. The simulator admits the planned vector of Q-grid releases, including simultaneous releases to different addresses; sufficient dispatch capability is a premise. The implementation checks the time envelope and control arithmetic, not all resource-admission premises of the broader theorem.

The auxiliary serial baseline's `max(J,physical_tail)` assumes the physical tail starts at job completion and overlaps delivery lag. The pipeline conservatively adds its tail reservation after the report envelope; these are safe but differently conservative accounting conventions, not identical elapsed-time claims. No speedup or necessity result relies on their difference.
