# Finite load-bearing handoff

Run `python3 -B pilot.py` under Python 3.12 without optimization. For exact event traces and the action sets for each observation, run `python3 -B pilot.py --json | cmp results.json`.

## The cut and the work owed

Every run starts with the same executed prefix. A brings a load and engages its support, B commands a latch, and D has an operating duty on the shared support. At tick 1 the latch seats or stops partway. A still bears some load in both arms. B receives a contact report at tick 2 unless it is lost. The controller cannot read actual latch state, remote queue state, or the arm name. An optional local probe can provide a second observation. These are model primitives, not calibrated plant data.

The controller chooses one action during [1,2): wait, run the probe, or try to prepare the cradle early. The setup position remains held during that interval; the early cradle attempt is refused and consumes the interval. At t=2 the controller acts on its report and probe result. It can wait, command direct release, command the cradle, or use a fixed fail-closed interlocked release. One action fits before C's required passage at t=3. Ground-state contact limits the effect of a command, not the controller's selection of commands. Unlisted commands, replanning, multiple attempts in a phase, and sensors that inspect the latch directly are outside this base model.

A seated latch supports the load after release; its geometry blocks the cradle. In the partial state the cradle can take the load and settle it on a fixed rack at t=3, clearing A for C's passage. Direct release in that state is unsafe. A fail-closed release refuses it safely but misses C's passage; waiting and a blocked cradle also miss. C's passage is a distinct service from D's support duty.

## What the probe consumes

The normalized transfer load is 4. Before release, B bears 3 if seated or 1 if partial. The test shifts `min(2,4-B)` from A onto the shared support: 1 or 2. A continues to bear the remainder. D has a live load of 2 during the normal probe, so the shared demand is 3 or 4 against capacity 4. In the overload variant D carries 3 instead. Both partial-probe demand 2 and D demand 3 separately fit, but jointly demand 5. The true partial state is not known at the time the probe is ordered.

At t=2 the full cradle needs all 4 units until t=3, when the rack takes the load. D's next unrelated demand of 1 normally starts at t=3. If it starts at t=2 instead, the cradle is refused rather than displacing D, and C's deadline is missed even with a correct contact report. An early second D duty breaks the original positive four arms; it is not evidence of a probe-specific defect.

## Policy and direct comparison

An incumbent that follows the report, defaulting to release on missing, succeeds in the nominal, partial-only, and loss-only arms. Both changes together select an unsafe release. The safer default of interlocked release cannot meet both safety and passage service. Without a probe and with a missing report, seated histories require release (plain or guarded), while partial histories require cradle. The allowed sets are disjoint. Trying the early cradle gives no additional evidence. This establishes a universal-policy limit only for the enumerated action and observation interface.

A single installed policy runs a probe during [1,2) and acts on its result at 2. The sensor measures the extra support demand in half-load units, not a ground-state label. Exact readings are 2 and 4; admitted additive errors of −1, 0 or 1 give bands {1,2,3} and {3,4,5}. With separated readings and the normal D duties, it preserves safety plus C and D service in all four arms. An overlapping reading gives the same missing-report observation in both states and restores the obstruction. Probe overload removes safety and D service in the partial state; the model does not turn a failed experiment into free information. A separate favorable counterdesign adds a hardware interface that sees the latch at t=2 and branches within the action budget. It passes without probing under the normal D duties. That sensor and chooser are absent from the base model; real implementations might supply them more cheaply than probing.

The independent reference computes the legal last-action sets by custody state and capacity, then intersects them over each reachable observation fibre. It checks the sets against every simulator action, not just the displayed winning policy. It explains the result without Contextual Composition. There is no result about a physical apparatus, broader controller repertoire, transferred proof, or advantage over the direct finite game.

Two hypothetical coupling envelopes have the same marginal sets of probe demands and prior D demands, and both admit loss or delivery of the report. The probe wins with complementary demand pairs `(1,3),(2,2)`, but no policy wins with aligned pairs `(1,2),(2,3)`. The latter includes the infeasible sum 5. D's demand is not in the supplied controller observation in either envelope. This is a sensitivity check on admitted joint states, not a held-out transfer or a measurement of real dependence.
