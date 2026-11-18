"""Two-bank continuity interface checks; no successful repair or W0 admission oracle."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys

if sys.flags.optimize:
    raise RuntimeError("Run without optimization")

HERE=Path(__file__).resolve().parent


def serial(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {k:serial(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return [serial(v) for v in value]
    return value


def contained(intervals,t,work):
    return [i for i,(start,end) in enumerate(intervals) if start<=t and t+work<=end]


def geometry_trace():
    # Source interface inputs: actual contact motion and an independently valid
    # boot/startup prefix. Nominal readiness is not inferred from power alone.
    distance,vmax,ready_bound,work=F(12),F(2),F(2),F(4)
    cycle=F(30)
    on=[cycle*k for k in range(13)]
    speeds=[F(1),F(3,2),F(2)]*5
    prefixes=[F(1),F(3,2),F(2)]*5
    ready=[F(0)]+[on[k]+prefixes[k] for k in range(1,13)]
    off=[on[k+1]+distance/speeds[k+1] for k in range(12)]
    intervals=list(zip(ready[:12],off))
    assert distance/vmax-ready_bound>=work
    for k in range(11):
        assert ready[k+1]+work<=off[k]
        # The same physical bank is unavailable before its next preparation.
        assert on[k+2]-off[k]>=18
    checked=0
    for tick in range(0,1320):
        t=F(tick,4)
        assert contained(intervals,t,work)
        checked+=1
    return dict(distance=distance,vmax=vmax,ready_prefix_bound=ready_bound,work=work,
                physical_bank_ids=[k%2 for k in range(12)],power_on=on[:12],
                ready_intervals=intervals,offline_preparation_opportunity_lower=18,
                checked_start_times=checked,
                boundary="Boot-prefix correctness and absence of disrupting faults within each ready interval are separate source premises")


def interval_cases():
    checked=0
    for work,span,shift in product(range(1,5),range(2,11),range(1,9)):
        if span-shift<work:continue
        intervals=[(F(k*shift),F(k*shift+span)) for k in range(12)]
        for t in (F(i,3) for i in range(3*10*shift)):
            assert contained(intervals,t,F(work))
            checked+=1
    return checked


def rr_visits(start,end,degree,pointer,durations):
    trace=[]
    t=start
    k=0
    while t<end:
        v=durations[k%len(durations)]
        trace.append((pointer,t,t+v))
        t+=v
        pointer=(pointer+1)%degree
        k+=1
    return trace


def polling_cases():
    checked=0
    for degree in range(1,7):
        work=F(degree+1+2)  # Local response plus a powered application tail.
        span=3*work
        shift=span-work
        intervals=[(k*shift,k*shift+span) for k in range(8)]
        for pointer in range(degree):
            visits=[rr_visits(a,b,degree,(pointer+k)%degree,(F(1),F(1,2),F(3,4)))
                    for k,(a,b) in enumerate(intervals)]
            for step in range(0,int(5*shift)*2):
                t=F(step,2)
                owner=contained(intervals,t,work)[0]
                for job in range(degree):
                    delivery=F((owner+job)%3)
                    responses=[finish+delivery for j,begin,finish in visits[owner]
                               if j==job and begin>=t and finish+delivery<=t+work]
                    assert responses
                    checked+=1
    return checked


def dry_speed(force,stiction):
    if force>stiction:return force-stiction
    if force<-stiction:return force+stiction
    return F(0)


def held_output_cases():
    # Single monotone stage with static-friction law. Observation/command lags
    # are adversarial endpoints; all nominal donors eventually hold the same action.
    checked=0
    for delays in product(range(4),repeat=3):
        x=F(0)
        history=[x]
        for tick in range(20):
            good=sum(tick>=d for d in delays)
            opposing=F(1)
            speed=dry_speed(F(good)-opposing,F(1))
            assert speed>=0
            x=min(F(8),x+speed)
            history.append(x)
        assert x==8
        # By tick3 all three donors hold; thereafter net speed is at least1.
        assert history[11]==8
        checked+=1
    return dict(cases=checked,donors=3,per_donor_force=1,opposition=1,stiction=1,
                stroke=8,settling_bound=3,minimum_settled_speed=1,completion_bound=11)


def guard_cases():
    checked=0
    for error,travel,slack in product(range(4),range(6),range(1,4)):
        guard=2*error+travel+slack
        for sample_lag in range(2*error+1):
            for distance in range(travel+1):
                assert sample_lag+distance<guard
                checked+=1
    return checked


def counterexamples():
    short=[(F(3*k),F(3*k+4)) for k in range(8)]
    assert all(any(a<=F(t,4)<=b for a,b in short) for t in range(80))
    assert not contained(short,F(2),F(5))
    assert all(b-a<5 for a,b in short)
    # Nominal execution with a mutual READY prerequisite yields no donation.
    ready_flags=[False,False,False]
    donations=[int(all(ready_flags)) for _ in ready_flags]
    assert sum(donations)==0
    # Each donor is fair but their pulses never overlap above the threshold.
    bursts=[(int(t%2==0),int(t%2==1)) for t in range(12)]
    assert all(dry_speed(F(a+b),F(3,2))==0 for a,b in bursts)
    assert dry_speed(F(2),F(3,2))>0
    # Power removal does not consume an already launched command.
    pending=dict(sent=0,delivered=2,force=1)
    powered_off=1
    assert pending["delivered"]>powered_off and pending["force"]>0
    powered,code_equal,pc_initialized,buffers_fresh=True,True,False,False
    execution_ready=powered and code_equal and pc_initialized and buffers_fresh
    assert not execution_ready
    bank_limit=F(2)
    assert bank_limit<=3 and 2*bank_limit>3
    assert dry_speed(F(-3),F(2))<0
    new_ready,emitted,old_off,applied=3,4,4,6
    assert emitted<=old_off<applied
    assert old_off-new_ready>=1 and old_off-new_ready<1+2
    startup_force=34*(F(2)-F(11,5))-6*F(22,5)-1
    assert startup_force==F(-171,5) and dry_speed(startup_force,F(28))<0
    return dict(power_continuous_no_uninterrupted_job=dict(intervals=short[:4],
                    requested=[2,7],work=5),
                silent_donors=dict(ready_flags=ready_flags,donations=donations),
                opposite_bursts=dict(forces=bursts,stiction="3/2",progress=0),
                late_command=dict(power_off=powered_off,pending=pending),
                false_powered_readiness=dict(powered=powered,code_equal=code_equal,
                    pc_initialized=pc_initialized,buffers_fresh=buffers_fresh,ready=execution_ready),
                doubled_force=dict(per_bank=bank_limit,actual_overlap=2*bank_limit,protected_limit=3),
                retirement_before_application=dict(new_ready=new_ready,emitted=emitted,
                    old_off=old_off,applied=applied,local_response_bound=1,delivery=2,
                    maintenance_force_gap=[old_off,applied]),
                uninitialized_bank_force=dict(ready_old_hosts=34,old_force=2,
                    uninitialized_new_force="-11/5",bad_hosts=6,bad_host_force="-22/5",
                    disturbance=-1,net_force=startup_force,stiction=28),
                reverse_force_exceeds_stiction=dict(force=-3,stiction=2,speed=-1))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    g=p.add_mutually_exclusive_group(required=True)
    g.add_argument("--check",action="store_true")
    g.add_argument("--write",action="store_true")
    args=p.parse_args()
    names=("CONTINUITY.md","Continuity.lean","continuity_model.py")
    hashes={n:sha256((HERE/n).read_bytes().replace(b"\r\n",b"\n")).hexdigest() for n in names}
    result=dict(status="passed",scope="conditional ready-interval, local-response and held-force interfaces; not source admission",
                sources_sha256_lf=hashes,geometry=geometry_trace(),
                interval_cases=interval_cases(),polling_cases=polling_cases(),
                applied_response_delay_bound=2,
                held_outputs=held_output_cases(),guard_cases=guard_cases(),counterexamples=counterexamples(),
                external_suppliers=["actual code/data installation, reset and startup-prefix proof",
                    "sound permission and physical-stage information despite primary-frame corruption",
                    "actual contact geometry, no bypass power cut and bounded force/speed relations",
                    "per-neighbor held output realization, shared budget and old-command tails",
                    "source fault/resource envelopes supporting the claimed ready intervals"])
    text=json.dumps(serial(result),sort_keys=True,indent=2)+"\n"
    dest=HERE/"continuity_results.json"
    if args.write:dest.write_text(text,encoding="utf-8",newline="\n")
    else:assert dest.read_text(encoding="utf-8")==text,"Continuity record differs"
    print(json.dumps(dict(status="passed",interval_cases=result["interval_cases"],
                         polling_cases=result["polling_cases"],held_cases=result["held_outputs"]["cases"],
                         guard_cases=result["guard_cases"])))


if __name__=="__main__":main()
