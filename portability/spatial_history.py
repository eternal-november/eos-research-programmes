"""Spatial incidence, recurrence envelope and paid local impairment at the threshold point.

The conditional extension theorem consumes one coupled source history. Its
bounded clock fixtures exercise only the schedule arithmetic.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from math import ceil
from pathlib import Path
import subprocess
import sys

import fixed_island_model as islands
import input_lifecycle as inputs
import parent_retirement as retirement
import threshold_incidence_model as incidence

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = "theories-and-designs/byzantine-control/portability/"
BASE = "75ef803d9569caf7b443df35b28bbd286b32d3a8"
H = 2 * 10**13
PERIOD = 42 * H
WINDOW = 2 * H
OFFSETS = (0, 250, 600)
DURATION = 500
COHORT = 12 * (6 + 2**98) + 2
RATE = Q(1, 104548602495950)


def need(ok, message):
    if not ok:
        raise ValueError(message)


INPUT_BASE = "318b343be4953f8ec58121ac1785b121c17794d2"


def binding(name):
    source = INPUT_BASE if name == "input_lifecycle.py" else BASE
    committed = subprocess.check_output(["git", "show", source + ":" + PREFIX + name], cwd=REPO)
    clean = lambda b: b.replace(b"\r\n", b"\n")
    need(clean((HERE / name).read_bytes()) == clean(committed), "Supplier changed: " + name)
    return sha256(clean(committed)).hexdigest()


def regions(columns):
    edges = incidence.region_edges(columns)
    neighbors = {(row, j): set() for row in (0, 1) for j in range(columns)}
    for left, right in edges:
        neighbors[left].add(right)
        neighbors[right].add(left)
    return {v: {v} | ns for v, ns in neighbors.items()}


def packing(columns):
    neighborhoods = regions(columns)
    centers = tuple((0, j) for j in range(0, columns, 5))
    need(10 * len(centers) >= 2 * columns, "Spatial density vanished")
    for j in range(columns):
        bag = {(r, k) for r in (0, 1) for k in range(max(0, j-1), min(columns, j+2))}
        # One-hop receiving queries AND the larger overlapping path bags.
        need(sum(bool(bag & neighborhoods[c]) for c in centers) <= 1, "Shared bag spends two clusters")
        for r in (0, 1):
            need(neighborhoods[r, j] <= bag, "A local constraint left the three-column bag")
        if j + 1 < columns:
            right_bag = {(r, k) for r in (0, 1) for k in range(j, min(columns, j+3))}
            need(len(bag & right_bag) <= 4, "Separator exceeded four regions")
    return centers, neighborhoods


def region_regressions():
    for cols in range(3, 101):
        packing(cols)
    _, n = packing(7)
    left, right, middle = (0, 0), (0, 3), (0, 1)
    need(not n[left] & n[right], "Old packing example is not separated")
    need(n[middle] & n[left] and n[middle] & n[right], "Missing straddling-query countercase")
    return dict(column_counts_checked=98, lower_centers_per_region="1/10",
                first_countercase={"centers": [left, right], "query": middle},
                bag_size_upper=6, separator_size_upper=4, conditional_direct_export_radius=1)


def cluster(start, region, epoch, columns):
    need(type(columns) is int and columns >= 3 and type(epoch) is int and epoch >= 0,
         "Uninstalled population or epoch")
    need(type(region) is tuple and len(region)==2 and all(type(v) is int for v in region)
         and region[0]==0 and 0 <= region[1] < columns and region[1]%5==0,
         "Uninstalled cluster anchor")
    need(type(start) in (int,Q) and epoch*PERIOD <= start <= epoch*PERIOD+WINDOW,
         "Cluster does not belong to this physical opportunity window")
    # Identity is common across all consumers; restrictions keep the same tuple.
    return tuple((start + offset, start + offset + DURATION, (region, epoch, index),
                  (("execution", 0), ("pair", 100), ("primary", 200))[index])
                 for index, offset in enumerate(OFFSETS))


def raw_checks():
    n = 28
    centers, neighborhoods = packing(n)
    events = []
    for j in range(5):
        for i, center in enumerate(centers):
            # Include both timing extremes on alternating epochs; illustrative
            # opportunities only. No claim these particular traces are physical.
            start = j * PERIOD + (WINDOW if (j+i) % 2 else 0)
            events.extend(cluster(start, center, j, n))
    audited = 0
    for c, query in neighborhoods.items():
        reached = [e for e in events if query & neighborhoods[e[2][0]]]
        need(len({e[2][0] for e in reached}) <= 1, "Local raw constraints used inconsistent centers")
        starts = sorted(e[0] for e in reached)
        for i, a in enumerate(starts):
            for j in range(i, len(starts)):
                need(j-i+1 <= int(3+RATE*(starts[j]-a)), "Closed arrival endpoint failed")
                audited += 1
        for t in {v for e in reached for v in e[:2]}:
            need(sum(a <= t <= b for a,b,*_ in reached) <= 2, "Direct occupancy exceeds two")
    need(Q(3,40*H) <= RATE, "Existing raw rate was changed")
    need(OFFSETS[-1] > DURATION and OFFSETS[-1] < OFFSETS[1]+DURATION, "Third event lost its overlap")
    malformed=0
    for args in ((-1,(0,0),0,n),(WINDOW+1,(0,0),0,n),(True,(0,0),0,n),
                 (0,(1,0),0,n),(0,(0,1),0,n),(0,(0,0),True,n)):
        try:cluster(*args)
        except ValueError:malformed+=1
        else:raise ValueError("Invalid phase trigger, anchor or data type accepted")
    bins = ceil(Q(WINDOW, 140))
    return dict(event_start_endpoint_checks=audited, master_period=PERIOD, opportunity_window=WINDOW,
                minimum_per_offset_separation=PERIOD-WINDOW, peak_direct=2,
                incident_offsets=OFFSETS, effect_interval_after_start=[210,490],
                simultaneous_common_interval=140, time_bins=bins,
                simultaneous_impaired_hosts_per_region=Q(1,10*bins),
                fresh_acquisitions_per_region_per_quantum=Q(3,10*PERIOD),
                invalid_calendar_or_anchor_rejections=malformed, same_history_raw_rate=RATE, projected_six_token_cover=1+2+int(3+2*RATE*H))


def input_checks():
    checks=[]
    for kind, receiver, slot_ids in (("pair",100,(1,2)), ("primary",200,(0,))):
        group=incidence.plant_group(COHORT,receiver,1)
        if kind=="pair":
            need(tuple(group[j] for j in slot_ids)==islands.installed_pair(COHORT,receiver),
                 "Changed physical paired island")
        need(inputs.support(COHORT,receiver,group,(kind,receiver))==set(slot_ids),
             "Wrong physical slot reach")
        for j in slot_ids:
            o=group[j]
            payer=inputs.SourceWork(o,2**30,2**30)
            role="primary" if j==0 else "auxiliary"
            for rb in (0,1):
                lanes=[]
                for sb in (0,1):
                    shared=lanes[0].captures if lanes else None
                    lane=inputs.RawLane(COHORT,inputs.LaneId(o,sb,receiver,rb),payer,shared)
                    record=lane.records[1]
                    need(record.role==role,"Logical data routed to wrong capture")
                    record.value=1000;record.set_ttl(8)
                    need(lane.private_capture(1,role)==1000,"Nominal finite capture failed")
                    lanes.append(lane)
                cap=lanes[0].captures[role];cap.snapshot=inputs.MASK;cap.clock_enabled=False
                for lane in lanes:
                    need(lane.captures[role] is cap and lane.private_capture(1,role)==inputs.MASK
                         and lane.records[1].value==1000,
                         "Stopped shared read clock silently obtained a fresh sample")
            checks.append(dict(kind=kind, receiver=receiver, origin=o, slot=j,
                               committed_word=1000, nominal_and_suppressed_reads=4))
    return checks


def output_checks():
    isa,c,Ports=retirement.source_inputs()
    parent_point=json.loads((HERE/"parent_realization_results.json").read_text(encoding="utf-8"))
    image_hash=retirement.parent.program.hash_text(json.dumps(c.image))
    need(image_hash==parent_point["image_sha256"] and isa.source_hash==parent_point["frozen_ISA_sha256"],
         "The execution probe and actual paid-source record use different images")
    bank_cap=Q(parent_point["cost_bounds"]["actual_bank_capacity"])
    m=retirement.RetirableParent(isa,c,bank=retirement.parent.BankWork(int(bank_cap),bank_cap))
    world=next(i for i,w in enumerate(c.image) if isa.decode(w)[0]==isa.IO
               and isa.decode(w)[4]==isa.PRIM["world"])
    _,_,arg,arity,_=isa.decode(c.image[world])
    need(arity==2,"WORLD arity changed")
    # Two instances of the declared direct-private fault at instruction boundaries.
    # This tests the model's damaged executor. There is no new control program.
    m.pc=world;m.R[arg]=m.R[arg+1]=(-100)&isa.WORD_MASK
    ports=Ports(c)
    need(m.step(ports) and ports.world_latch==(-100,-100),"Funded ordinary WORLD was not accepted")
    m.pc=len(c.image)
    need(not m.step(ports) and m.halted and m.powered and m.rejected["invalid_pc"]==1,
         "A malformed next PC did not retain the powered mailbox with a halted executor")
    need(m.C==c.image and m.pending is None and m.fabric.token is None,
         "Fixture spliced in a replacement source or erased a parent")
    # Do not call the generic step polling on the halted parent: it precharges
    # work if the slot is empty. That work would remain in its actual cell.
    m.balance()
    need(m.bank.supplied==40960 and m.cell.spent+m.cell.dumped==40960, "Bank accounting changed")
    speed=Q(11,10); earliest_power=Q(c.constants["POWER_AT"])/speed
    need(1100<earliest_power,"A fresh candidate could take over during the cluster")
    residual=Q(2)/(1+Q(200,2*100))**2
    need(-1+residual==Q(-1,2), "RC settling from worst-case initial track failed")
    return dict(synthetic_direct_private_damage_only=True, actual_image_sha256=image_hash, installed_WORLD_address=world,
                cpu_retired=m.steps, parent_work_received=m.bank.supplied,
                work_spent=m.cell.spent, work_dissipated=m.cell.dumped,
                transmitted_mailbox=list(ports.world_latch), powered_after_invalid_PC=m.powered,
                halted_after_invalid_PC=m.halted, code_bytes_unchanged=True,
                original_target_power_upper_speed=speed, earliest_cold_POWER=earliest_power,
                stable_actual_DAC_required_by=10, tracker_upper_after_210=-1+residual,
                execution_scope="Two paid operations on an operating bank. Fixed sampled WORLD delivery is a separate physical port law.")


def encode(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x


def generate():
    need(sys.version_info[:2]==(3,12) and __debug__, "Use unoptimized Python 3.12")
    names=("threshold_incidence_model.py","fixed_island_model.py","input_lifecycle.py",
           "parent_retirement.py","parent_realization.py","regional_coupling_results.json",
           "threshold_program_source.py","threshold_program_model.py","threshold_design.py",
           "threshold_field_source.py","cam_reformation.py","legacy_realization.py",
           "parent_realization_results.json","interrupted_renewal_results.json",
           "constructors.py","threshold_publication_model.py")
    bindings={name:binding(name) for name in names}
    coupling=json.loads((HERE/"regional_coupling_results.json").read_text(encoding="utf-8"))
    world=coupling["world"]
    service=Q(world["actual_effector_service_lower"])
    need(Q(world["conservative_net_service_lower"])==service-Q(1,10)>Q(1,10),
         "Combined endpoint transport allowance or service floor changed")
    need(service==((Q(3,10)-Q(2,11**10))*(1-Q(6,COHORT))-Q(2**98+6,COHORT))
         and service>Q(1,10), "Changed normalized service interface")
    need(Q(coupling["checks"]["ablation"]["total_rung_dissipation_lower_per_Rm"])==Q(256,5),
         "Changing the scale eliminated the installed coupling")
    itinerary=json.loads((HERE/"interrupted_renewal_results.json").read_text(encoding="utf-8"))
    need(Q(itinerary["H"])==H,"History must be rebound for this H")
    return encode(dict(scope="Connected regional raw schedule and conditional realized finite-window/unbounded load theorem",
                       base_commit=BASE, input_commit=INPUT_BASE, regions=region_regressions(), schedule=raw_checks(),
                       source_inputs=input_checks(), paid_output=output_checks(),
                       service_lower=service, net_service_lower=service-Q(1,10), combined_active_rung_prefix_dissipation_lower_per_Rm="256/5",
                       spatial_compatibility_proved_at_stated_support=True,
                       full_source_orbit_and_joint_history_admitted=False,
                       RP2_complete=False, immutable_inputs_sha256=bindings,
                       local_hashes={n:sha256((HERE/n).read_bytes().replace(b"\r\n",b"\n")).hexdigest()
                                     for n in ("SPATIAL-HISTORY.md","spatial_history.py")}))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write",action="store_true");group.add_argument("--check",action="store_true")
    args=parser.parse_args();value=generate();path=HERE/"spatial_history_results.json"
    if args.write:path.write_text(json.dumps(value,indent=2,sort_keys=True)+"\n",encoding="utf-8",newline="\n")
    else:need(value==json.loads(path.read_text(encoding="utf-8")), "Spatial history result differs")
    print("PASS spatial raw history and bounded source probes; actual recurrent source admission remains open")


if __name__=="__main__":main()
