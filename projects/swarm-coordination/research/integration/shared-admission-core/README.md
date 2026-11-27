# A shared admission kernel for warehouse and radio effects

**I1 development only.** This runs one admission interpreter over joined
events from two pinned replay plants. It neither closes I1/I2 nor sets
aside an independent acceptance mission. The independently written
factored check gets the same results with the same evidence.

See [the contract and results for this model](Shared_Admission_Core.tex)
and the [development freeze](FREEZE.txt). The two native components
are the ordered warehouse source producer (#588) and the timed radio
source producer (#589). The bridge from bay clearance to channel
availability is authored; it is not something either plant proved.

## Replay

Python 3.10+, NumPy and a C++17 compiler. Use the exact paths below
from a checkout of this repository; their relevant blobs are pinned in
`COMPONENTS.tsv`. The upstream input tree has the same layout as in
the [radio producer's source manifest](../subt-relay-debit/pending-scope/timed-source-producer/SOURCE.tsv),
including the pinned warehouse simulation files.

    RESEARCH=/path/to/eos-research-programmes/projects/swarm-coordination/research
    sh replay.sh /path/to/upstream \
        "$RESEARCH/multi-owner-coordination/named-withdrawal/in-flight/source-producer" \
        "$RESEARCH/multi-owner-coordination/named-withdrawal" \
        "$RESEARCH/multi-owner-coordination/named-withdrawal/in-flight" \
        "$RESEARCH/integration/subt-relay-debit/pending-scope/timed-source-producer" \
        | cmp expected.json -

`core.py` interprets typed facts, rolling capacity, deadlines and
exactly-once effects. `replay.py` translates plants, compares to direct
rules, and executes five selected decisions against the radio plant in
addition to the standalone native controls. Neither the bridge nor the
shared variable used in the correlation control was inferred from traces.

## Action-dependent follow-up

[Two-cut reactive diagnostic](reactive-observation/README.md): two probes can produce the same timely evidence yet differ in whether the old clearance still meets its deadline. The same checker also distinguishes state-dependent silence from an unqualified loss model. The direct adaptive comparison ties.

## Native authority follow-up

[Live reservation replacement](live-authority/README.md): the same native range can refer to a newly granted path, while an earlier reservation receipt and the actual crossing clearance remain separate. Five in-process controls also distinguish inline qualification from a remote snapshot. The matched direct check ties.

## Clock and resource binding follow-up

[Clock-bound bay occupancy](clock-bound-occupancy/README.md): a sampled gap is reusable for a fixed start query when clock and physical scope can be joined within a world. Equal normalized profiles need not survive named removal in the same way. The direct tick checker agrees.

## Return-to-contact comparison

[Terminal receipt and staging commitment](return-commitment/README.md): a timely terminal receipt avoids staging on the already-served branch while preserving report, inspection and egress deadlines. The gain is against the specified aggregate movement interface, not an equally informed direct planner or an end-to-end ACHORD implementation.

## Joint cave-planning reduction check

[Pinned COPS and coupled cave fork](cops-coupled-fork/README.md): the same report loses its direct and old rendezvous options when passage and contact both fail. A native flow planner solves the known subproblems; preposition and a local cue make a common implementable policy. Same-information direct ties; this is held-in I2 development.

## Hosted cave cue and prior physical duty

[Hosted and dedicated cave probes](hosted-cave-probe/README.md): individually feasible route choices may spend a still-live old clearance tick while obtaining the cue. The initial check rejects that hosted prefix even if an erased cue would later prevent any new report. Same-information exact direct ties.

## Reply shape and the earlier consumer

[Packed reply versus early prelude](ack-packing-window/README.md): the same final fields can give different old physical effects. Early independent availability and a spare route repair different sides of the shared-airtime obstruction. Matched exact direct ties.

## Fixed-cut proof revalidation

[Named history fibers](named-fiber-revalidation/README.md): complete qualified replacements reuse all untouched fiber profiles. Equal current decisions and counts do not support the same named retraction. Atomic edits and the exact profile-state bound are checked; the factored direct cache ties the affected plant work.

## Finding which history fibers changed

[Scoped source edits](scoped-source-edits/README.md): declared joint links and their incidence provide complete local recompilation for this model. An edit can add a previously absent bad history or change a latent dependency without changing the current proof. Full join and fresh admission agree; a same-input direct index can do the same local work.

## Restart around the actual effect

[Restart and supplier loss](restart-and-replacement/README.md): identical absent receipts can hide paid and unpaid duties. A one-key station gate with a staged timer tolerates loss of a prepared route and its notice while a separate duty proceeds. RIFL-strength atomicity is modeled, not improved on; scoped to a held-in application effect.

## Transfer to a physical latch and departure

[Reversible warehouse actuator](physical-restart-transfer/README.md): replaying a set-down as a raw toggle can undo the old effect. Guarding every writer allows an overlapping repair; separately measured departure satisfies the deadline where the stated serial drain/check misses. Same-interface exact direct ties. This is held-in native simulation.

## One issue rule across station and latch effects

[Typed effect transfer](typed-effect-transfer/README.md): the same selector runs at each native receiving cut. A successful proof must cover every writer at one authority point through the actuation horizon, or use a true terminal fence and subsequent reading. A same-information direct selector matches. Modeled authority; held-in development only.

## Native partially effective prefixes

[Two-plant admission with ordered past effects](native-prefix-phases/README.md) retains a no-callback TX charge and distinguishes unloading from departure. The unchanged core uses both to select a qualified backup in a tight held-in local view; matched direct oracle ties.

## Recovery-induced radio debit follow-up

[Self-renewing diagnostic debit](live-clearance-generation/radio-bounded-handoff/recovery-debit-loop/README.md): two successful checks at a separate receiver can repeatedly bar a live warehouse handoff on the same transmitter. Joint reservation meets all deadlines when the second check can wait for the debit to expire. The exact direct comparison ties. This is scoped I07/F47 evidence, not accepted inventory coverage.

## Second fault changes the suffix supplier

[Selected-source replay](live-clearance-generation/radio-bounded-handoff/suffix-supplier-change/README.md): one local notice and one received preparation request can redirect the old suffix while unrelated work continues. The new supplier needs its own current license and rolling headroom. Scoped positive I1 development; the same-information direct budget calculation ties.
