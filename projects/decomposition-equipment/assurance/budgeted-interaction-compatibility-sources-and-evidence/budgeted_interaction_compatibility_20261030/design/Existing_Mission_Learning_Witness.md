# Existing main workload already requires productive evidence

This is an analytical explanation of the frozen main case n4_s731_p2_r1_e0. It is NOT a replacement benchmark or a post hoc workload change. An initial suspicion that all roomy successes might admit idle-separated frozen-prior schedules was premature: individual job slack does not imply enough aggregate slack under overlapping releases and shared power.

## Model and jobs

The four-node ladder has candidate edges 0--1, 0--2, 1--3, 2--3. Each node has zero or one parent, and reciprocal pairs are forbidden. All such worlds are initially possible. Inputs are 0,1,2, with sum at most2; loads satisfy u_i(t)+u_parent(t-1)<=3. Measurements arrive at slot end. Energy12 permits exactly the six required productive inputs and no diagnostic energy.

J1: routes (0,1)/(1,0), release2, deadline5.
J2: routes (0,2)/(2,0), release4, deadline7.
J3: routes (1,3)/(3,1), release6, deadline9.

## Explicit uniform winning policy

Slots0,1: idle.
Slot2: actuator1 for J1's first stage.
Slot3: idle. The end-slot observation identifies whether 1->3.
Slot4: actuator0, completing J1.
Slot5: actuator0, starting J2. Repeating the same actuator is safe because self-parents are excluded. The end-slot observation identifies whether 0->2, from slot4's useful work.

Case A: 0->2 is present.
- Slot6: actuator3, starting J3. Nodes0 and3 are not neighbors.
- Slot7: actuator2, completing J2. Knowing P2=0 excludes parent3, so the previous actuator3 cannot overload2.
- Slot8: actuator1, completing J3. Nodes2 and1 are not neighbors.

Case B: 0->2 is absent.
- Slot6: actuator2, completing J2.
- If 1->3 is absent, use actuator1 at7 and actuator3 at8 for J3. The 2-to-1 transition is between nonneighbors, and the 1-to-3 transition is certified absent.
- If 1->3 is present, use actuator3 at7 and actuator1 at8 for J3. P3=1 excludes parent2, so the 2-to-3 transition is safe. No-reciprocity excludes3->1, so the next transition is safe.

Slot9: zero-input tail flush.

Every branch uses six productive activations, energy12, maximum power2, and no diagnostic pulse. All deadlines hold. The safety-relevant distinctions are learned by useful work and include consequences of the one-parent and no-reciprocity priors. This is not merely learning a table that never affects the mission.

## Frozen-initial-evidence impossibility

Partition nodes into X={0,3} and Y={1,2}. Every cross-partition pair is a candidate edge. A controller certifying each decision against the unrefined initial world class cannot put a full-power activation from X immediately after one from Y, or conversely. Each such color change needs a non-full-work separator slot. Same-color consecutive work is universally safe.

All six required full-work stages must fit into slots2 through9: eight slots total. Therefore at most two separator slots, and hence at most two changes of work color, are available. Each job needs one stage of each color. One color change cannot serve J1 by5 and both stages of J3 released6; at least two changes are needed. The only possibilities are X-Y-X and Y-X-Y, ignoring idle prefixes/suffixes.

In either pattern, the initial color block cannot serve a J2 stage: such a stage cannot occur before4, after which a separator and the opposite-color J1 stage would finish no earlier than6, violating J1's deadline5. It also cannot serve a J3 stage, released6.

Consequently the middle color block must contain three distinct stages: J1's opposite-color stage, J2's middle-color stage, and J3's middle-color stage. Its first slot cannot be earlier than4 because J1's initial-color stage cannot occur before2 and a separator is required. Its last stage cannot be earlier than6, both from the count and J3's release. The separator before the final block is then no earlier than7, and J2's final-color stage no earlier than8, violating its deadline7.

Thus no schedule whose safety checks remain at the initial evidence can complete the mission. This argument also covers additional diagnostic energy allowances if observations remain unused: diagnostics may provide a separator, but cannot provide an extra slot or discharge a required full-work stage. It does not claim impossibility for all raw-history controllers; the winning policy above is such a controller and explicitly uses observations.

## Interpretation and limits

The matched learned-WIN/frozen-LOSE distinction is structurally meaningful. The roomy jobs individually permit separated work, but their overlap and shared power do not permit enough global separators. Productive observations remove the need for particular separators.

This proves a learning-to-completion benefit in an existing main workload. It does not by itself establish a decomposition speedup over an equally informed coherent symbolic planner, which remains a separate comparison. All four actuators eventually run in this small case, so do not use it alone to claim lifetime partial identification of all columns.

The earlier unexecuted release-spacing3/4 family was only a contingency proposal. It should not be run or substituted merely because of the initial mistaken inference about roomy cases.
