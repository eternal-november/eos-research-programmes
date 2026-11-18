# Abort entry: retained evidence and the unresolved source join

Status: derived conditional completed-return barrier, reproduced local instruction probes and static incidence witness; unresolved admitted-history/phase correspondence. This records the investigation at the requested pause. It establishes neither an admitted H-deadline failure nor a repaired controller. The relevant source/probe point is4aeebea352d3bfb96ffeed87c07ececc9e1d01a6, with actual threshold image f5a15942c14956c85c3c061fe6ee3c67e03935e62f8ba21faf77f00b2b935ed1. The completed frozen baseline remains unchanged.

## What is established at the local scope

For a return that actually traverses the full stroke, [HYBRID](../local-control/HYBRID.md)'s retained FULL and one-way/contact order, [the actual helper](threshold_program_source.py)'s EXITING priority, return travel and post-normal holding supply a conditional separation argument. With J=12795915/1048576, stage=38387745/16384 and maintenance age517, the existing abort-join allowance plus60 for stable E/T drainage is1550009387/524288<100000/11. Exit clearing plus ordinary zero application has allowance517+stage+3J+15=3053045857/1048576<R*=2748532811/524288. The full bad positive effort bound3478/125=27.824 remains below stiction28 by22/125. These comparisons consume actual all-emitter formation, contact availability, field retirement and bank-birth laws; they do not supply those laws by arithmetic.

A separate force argument is valid while the conforming MODE contribution stays unchanged or becomes more negative: after a negative return crossing, changing only an adverse contribution bounded by W<theta, for a common stiction lower bound theta, cannot produce the opposite crossing. The unresolved case permits a previously neutral conforming helper to issue a new positive MODE; that is outside this monotonicity premise. Neither small adverse force alone nor this conditional barrier resolves that case.

Two actual compiled helper probes were reproduced by the coordinator from the reviewer's retained assignments. Fields not assigned retain helper_fixture values. Command tuple order is(route,side,CAM,MODE,action,index,amplitude).

| Input/private-state fixture | Actual result |
|---|---|
| ENTERING predicate1, FULL0, NORMAL_STOP0, retained EXITING1 and EXIT_OBSERVED1 | (26,0,0,-20,0,0,0); EXITING remains1, EXIT_OBSERVED becomes0;398015 instructions |
| Normal cam entry with BOOT-default exit/watch/abort fields | (0,1,20,0,0,0,0); TIMER becomes2400000000 and ABORT stays0;398724 instructions |

The first is a state-product countercase to treating negative EXITING as generic entry progress. Under the one-way entering law, negative MODE cannot complete that stroke or return it to NORMAL. It is not proof that the combined state is reachable in an admitted history. The second shows that a zero initial watchdog does not itself force a spurious abort.

A compact reproduction, from this directory with unoptimized Python3.12, is:

```python
import threshold_program_model as pm
import threshold_design as td
isa = pm.load_isa()
c = pm.compile_program(isa, td.design(isa))
b = pm.bounds(isa, c)
k = c.constants
Ports = pm.ports_class(isa)
base = k["TARGET_BASE"]
for exiting in (True, False):
    ports = Ports(c)
    machine, view = pm.helper_fixture(isa, c, ports, 0, 0)
    view[k["MODE"]] = int(exiting)
    view[k["ABORT_FULL"]] = 0
    view[k["NORMAL_STOP"]] = int(not exiting)
    if not exiting:
        view[k["CAM"]] = 0
    ports.set_view(0, view)
    for field in ("EXITING_ABORT", "EXIT_OBSERVED", "EXIT_WAIT", "WATCH_HALF", "LAST_PHASE", "ABORT", "TIMER", "RANK_VALID"):
        machine.W[base+k[field]] = 0
    if exiting:
        machine.W[base+k["EXITING_ABORT"]] = 1
        machine.W[base+k["EXIT_OBSERVED"]] = 1
    machine = pm.call(isa, c, ports, "helper", (0,), b["instruction_upper_bounds"]["helper"]+100, machine)
    command = next(e for e in reversed(ports.events) if e[0] == "command")
    assert list(command[2:]) == ([26,0,0,-20,0,0,0] if exiting else [0,1,20,0,0,0,0])
    assert machine.W[base+k["EXITING_ABORT"]] == int(exiting)
    assert machine.W[base+k["EXIT_OBSERVED"]] == 0
    if not exiting:
        assert machine.W[base+k["TIMER"]] == k["WATCH_FRAMES"]
        assert machine.W[base+k["ABORT"]] == 0
```

## Retained static incidence witness

The reviewer's bounded search used seed8301 and25000 trials. Its retained witness was reproduced directly without another search. Signed offsets are relative to target0 in m=12*(6+2**98)+2; a negative offset denotes its residue modulo m. The classes partition the actual forty neighbors:

```python
bad = {-12,-7,-3}
fresh_good = {-20,-18,-15,-14,-13,-6,-5,1,2,3,4,9,10,11,13,14,16,18}
old_good = {-19,-17,-16,-11,-10,-9,-8,-4,-2,-1,5,6,7,8,12,15,17,19,20}
selected_consumers = {-20,-19,-18,-17,-16,-15,-14,-13,-11,-10,-9,-8,-6,-5,-4,-2,-1,*range(1,18)}
```

Assign(FULL,CAM_ENTRY)=(1,0) to bad providers,(0,0) to fresh good providers, and(1,1) to old good providers. For all34 selected consumers, their actual maintenance_group for target0 then has FULL count at least8 and CAM_ENTRY count below8. This is one common static provider partition, not separately chosen bad sets for each consumer. The check is:

```python
import threshold_incidence_model as incidence
m = 12*(6+2**98)+2
bad, fresh_good, old_good, selected_consumers = [
    {v % m for v in values}
    for values in (bad, fresh_good, old_good, selected_consumers)
]
assert bad | fresh_good | old_good == set(incidence.neighbors(m, 0))
assert not (bad & fresh_good or bad & old_good or fresh_good & old_good)
for receiver in selected_consumers:
    target_ordinal = incidence.neighbors(m, receiver).index(0)
    providers = {o for o, _ in incidence.maintenance_group(m, receiver, target_ordinal)[1]}
    assert len(providers & (bad | old_good)) >= 8
    assert len(providers & old_good) < 8
```

This establishes only an incidence possibility. It supplies no timestamps, source-bank intervals, helper-private histories, packet schedule or physical trajectory. In particular, it cannot be spliced with a separate two-held-helper force calculation and called one admitted history.

## The missing initial/temporal correspondence

[INITIAL-RETURN](../local-control/INITIAL-RETURN.md) gives canonical geometry outside the initial charged supports; [PORT-SOURCE](../local-control/PORT-SOURCE.md) permits initially arbitrary direct domains within the hard envelopes. The exact physical scope of that allowance must be pinned. A coherent partial RETURN with small positive abort position, ACTIVE=FULL=1, NORMAL_STOP false and satisfied cleanup/cam-entry contacts differs from an arbitrary Cartesian flag tuple. Neither its admission nor exclusion has been established here. Later digital acquisitions do not teleport physical positions into that state.

After a sufficiently short partial return, some helpers might retain EXITING while others remain in FULL post-stage waiting. A later helper may read aged FULL=1 and a newer missing CAM_ENTRY, then request MODE+ and REWIND through abort_action. On the first such invocation the fresh signature wait can suppress the actual REWIND amplitude while MODE+ is still flushed. FULL and CAM_ENTRY are separate published facts; their conjunction is not the coherent ACTIVE/FULL word used to derive ENTERING. The present phase representation omits the helper EXITING mixture and this inter-stream chronology. That omission needs a preservation argument, a refined state/phase account, or a controller change.

The decisive check is one actual source schedule. The bound image has FAST_BATCH16 over RAW_MAINT_HEADS3600, with RAW_TARGET_HEADS90; this raw-head cursor is distinct from the FAST_KEYS2003 published-record interface. VIEW_WORDS46 plus four eleven-member functional folds account for the difference. Target-local CAM_ENTRY offsets40/41 precede FULL45. The schedule must jointly obey that order, ten-frame target revisits,2100-frame post-stage waits, actual fixed provider groups, source-bank availability, packet/receipt timing, paid operations and the same raw acquisition/occupancy history. Independent age assignments are insufficient.

A mixed stall also need not persist indefinitely. Fresh helper-bank formation clears private EXITING and can restore positive MODE; released bad helpers cannot simply be kept bad forever. A sufficiently long admitted stall could refute the currently assigned local ENTERING edge without refuting the much larger H deadline. Neither result has been established. Letting corroborated ENTERING override an old EXITING latch is an unverified repair candidate, not a selected change; its stale-ENTERING/FULL/RETURN interactions, repeated-abort consequences, work and timing remain untested.

The [emitter turnover analysis](ABORT-EMITTER-TURNOVER.md) gives a restricted initial recovery proof, a bounded post-seat first-crossing question, and an alternative escape mechanism if re-entry does occur.

## Original resumption discriminator

First examine the additional research and reassess the representation and primitive/composition boundary. If this construction is retained, pin the initial A0 physical relation without silently narrowing it, then either construct the single timed history or prove a no-new-positive-emitter invariant for the partial-return case. Preserve the full RP0–RP6 objective and the distinction between local proof/check evidence, source admission, whole-history closure and repository acceptance. This residual is a correction surface, not permission to declare the family complete or manufacture a failure theorem.
