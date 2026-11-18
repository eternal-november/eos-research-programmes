"""Exact candidate algebra for local renewal; H and W are not achieved service."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from math import ceil
from pathlib import Path
import sys

if sys.flags.optimize:
    raise RuntimeError("Run without optimization")

HERE=Path(__file__).resolve().parent
DEGREE,BAYS=40,80
VISIT,COMMAND_DELAY,READY_PREFIX=2,3,16384
INVOCATION=DEGREE*VISIT+1
TIME_QUANTUM=F(1,250000)


def serial(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {str(k):serial(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [serial(v) for v in value]
    return value


def round_million(value):
    return ceil(F(value,10**6))*10**6


def parameters(length):
    j,d,b=INVOCATION,COMMAND_DELAY,BAYS
    scan=(b*length+2)*j
    applied=scan+j+2*d+1
    overlap=round_million(F(6,5)*applied+READY_PREFIX)
    reset=2*d+j+2
    activation=scan+5
    kernel=((j+2*d+reset)+(j+2*d+5)+(j+2*d+6)
            +(3*length+2)*j+(2*length+2)*d+(j+2*d+5)
            +scan+(j+2*d+activation)+5+READY_PREFIX)
    rearm_lengths=activation+overlap+reset+6+5+5
    rearm_derived=rearm_lengths+6*(j+2*d)
    rearm_reserved=round_million(rearm_derived)
    attempt=kernel+overlap+rearm_reserved+1000
    period=round_million(F(6,5)*attempt)
    return_bound=2*period
    arrival_rate=F(3,10*period)
    effective=1+2+int(F(3)+arrival_rate*(return_bound+attempt))
    opposing=F(22,5)*effective+1
    nominal=2*(DEGREE-effective)
    assert effective==6
    assert opposing<F(28) and nominal-opposing-28==F(63,5)
    assert overlap-READY_PREFIX>=applied
    assert F(period)/F(101,100)>attempt
    assert period+j+attempt<return_bound
    assert arrival_rate*(return_bound+attempt)<1
    assert READY_PREFIX+attempt>overlap  # Wrong Twork := whole attempt is circular.
    assert arrival_rate*period==F(3,10)
    adapter_slack=min(F(period)/F(101,100)-attempt,
                      return_bound-period-j-attempt,
                      1/arrival_rate-return_bound-attempt)
    assert adapter_slack>0
    return dict(image_cells=length,scan=scan,applied_local_work=applied,
                overlap_stroke=overlap,ready_overlap_lower=overlap-READY_PREFIX,
                kernel_budget=kernel,rearm_lengths=rearm_lengths,
                rearm_derived_if_each_stroke_progresses=rearm_derived,
                rearm_reserved=rearm_reserved,attempt_budget_W=attempt,
                local_period_C=period,candidate_return_H=return_bound,
                raw_arrival_rate=arrival_rate,arrivals_per_cycle=arrival_rate*period,
                arrival_window_product=arrival_rate*(return_bound+attempt),
                effective_support_bound=effective,nominal_force=nominal,
                opposing_force=opposing,stiction=28,forward_margin=nominal-opposing-28,
                hypothetical_bad_whole_cycle_overlap_deficit=READY_PREFIX+attempt-overlap,
                strict_additional_adapter_time_slack=adapter_slack,
                largest_integer_extra_with_strict_margins=ceil(adapter_slack)-1,
                physical_attempt_time=TIME_QUANTUM*attempt,
                physical_period=TIME_QUANTUM*period,
                physical_candidate_return=TIME_QUANTUM*return_bound,
                status="candidate budgets conditional on source suppliers; not achieved completion")


def raw_burst_witness(p):
    period=10*p["local_period_C"]
    rate=p["raw_arrival_rate"]
    n=72*6
    events=[]
    for k in range(4):
        for j,offset in enumerate((0,1,3)):
            release=(k*period+2 if j==0 else (k+1)*period+(j-1))
            events.append(dict(host=(3*k+j+1)%n,acquired=k*period+offset,
                               released=release,bank="a source-realized useful side"))
    endpoints=sorted({F(t)+delta for e in events for t in (e["acquired"],e["released"])
                      for delta in (F(-1,2),F(0),F(1,2))})
    interval_checks=0
    for a,b in product(endpoints,endpoints):
        if b<=a:continue
        count=sum(a<=e["acquired"]<b for e in events)
        assert count<=F(3)+rate*(b-a)
        interval_checks+=1
    maximum_direct=0
    for t in endpoints:
        current=sum(e["acquired"]<=t<e["released"] for e in events)
        assert current<=2
        maximum_direct=max(maximum_direct,current)
    witness_time=period+3
    current=[e["host"] for e in events if e["acquired"]<=witness_time<e["released"]]
    # This records damage retained in the three-step witness prefix; no recovery
    # transition is executed or inferred by the model.
    released=[e["host"] for e in events if e["released"]<=witness_time
              and witness_time-e["released"]<p["candidate_return_H"]]
    cover={0,*current,*released}
    assert current==[5,6] and released==[2,3,4] and len(cover)==6
    return dict(events=events,maximum_direct_control=maximum_direct,
                raw_interval_checks=interval_checks,witness_time=witness_time,
                current_hosts=current,released_but_uncleared_hosts=released,
                persistent_host=0,effective_witness_hosts=sorted(cover),
                boundary="Actual retained code damage is admitted in this prefix; the H-based global clearance implication still needs source proof")


def neighborhood(host,n):
    return {(host+offset)%n for offset in range(-20,21) if offset}


def spatial_checks():
    count=0
    for regions in (6,7,10):
        n=72*regions
        for host in range(n):
            assert len(neighborhood(host,n))==40 and host not in neighborhood(host,n)
            assert (host+1)%n in neighborhood(host,n)  # Connected cycle subgraph.
        for r in range(regions):
            assert ((r+1)*72)%n in neighborhood(((r+1)*72-1)%n,n)
        for shift in range(n):
            bad={(shift+i)%n for i in range(6)}
            assert max(sum(h//72==r for h in bad) for r in range(regions))<=6
            relevant={h for b in bad for h in neighborhood(b,n)}
            assert all(len(bad&neighborhood(h,n))<=6 for h in relevant)
            count+=1
    bad={69,70,71,72,73,74,75}
    assert len(bad&neighborhood(76,432))==7
    assert max(sum(h//72==r for h in bad) for r in range(6))==4
    force=7*F(22,5)+1
    assert force>28 and min(F(1),force-28)==1
    return dict(projected_placement_cases=count,
                seven_host_countercase=dict(host=76,bad_helpers=sorted(bad),
                    per_region_counts=[3,4],opposing_force=force,
                    stiction=28,unattended_enabled_stroke_increment=1),
                boundary="Global bound implies both projections; separate regional bounds do not imply the local bound")


def plant_units():
    error0,age=F(1,200),1000
    coordinate_rate=F(829,500)
    row_rate=2*coordinate_rate
    row_error=error0+row_rate*TIME_QUANTUM*age
    assert row_error==F(2283,125000) and row_error<F(1,50)
    assert error0+row_rate*F(1,200000)*age>F(1,50)
    bad=F(6,72)
    upper=(1-bad)*F(86,100)-bad
    lower=(1-bad)*F(34,100)+bad
    service=(1-bad)*F(3,10)-bad
    upper_collar=(1-bad)*F(84,100)-bad-F(64,100)-3*F(1,50)*F(1,100)
    lower_collar=F(56,100)-((1-bad)*F(36,100)+bad)-3*F(1,50)*F(1,100)
    assert (upper,lower,service)==(F(141,200),F(79,200),F(23,120))
    assert (upper_collar,lower_collar)==(F(691,15000),F(2191,15000))
    inversions=0
    for es,ed in product((F(-1,50),F(0),F(1,50)),repeat=2):
        assert abs((es+ed)/2)<=F(1,50) and abs((es-ed)/2)<=F(1,50)
        inversions+=1
    assert (1-F(9,10))*2+F(1,5)==F(2,5)
    return dict(time_quantum=TIME_QUANTUM,raw_row_error=error0,complete_age_budget=age,
                coordinate_variation=coordinate_rate,row_variation=row_rate,
                row_error_at_use=row_error,row_error_reserve=F(1,50)-row_error,
                upper_boundary_flow=upper,lower_boundary_flow=lower,service_floor=service,
                upper_collar_margin=upper_collar,lower_collar_margin=lower_collar,
                row_inversion_error_cases=inversions,old_load_after_mix_nine_tenths=F(2,5),
                rejected_quantum=F(1,200000),
                boundary="Error, work, coupler and joint host-output premises are source obligations; these are not estimates from an implemented controller")


def accounting():
    per_bank=F(11,5)*DEGREE*(BAYS+4)
    host=2*per_bank
    assert per_bank==7392 and host==14784
    # Illustrative clip-before-charge account conditional on all-in demand <=20000.
    demand,capacity=20000,60000
    supply=[0,0,60000]*8
    stock=capacity
    history=[stock]
    for incoming in supply:
        available=min(capacity,stock+incoming)
        assert available>=demand
        stock=available-demand
        history.append(stock)
    assert 0 in history and max(history)==capacity
    return dict(per_bank_port_force_sum_cap=per_bank,two_bank_host_cap=host,
                nominal_two_bank_cap=2*DEGREE*(BAYS+4)*2,
                conditional_energy_example=dict(demand=demand,capacity=capacity,supply=supply,stocks=history,
                    unallocated_energy_if_force_cost_one_per_quantum=demand-int(host)),
                boundary="Force is not energy; CPU, raw admissions, sensing, movement, both plant coordinates and idle power must fit one converted account")


def bootstrap_budget():
    words=8192
    instructions=3*words+4
    evidence,entry=1000,3000
    slow=instructions+evidence+entry
    faster=F(instructions,2)+evidence+entry
    assert instructions==24580 and slow>READY_PREFIX and faster<READY_PREFIX
    return dict(private_words=words,prefix_instructions=instructions,
                evidence_budget=evidence,entry_budget=entry,
                rejected_one_quantum_per_instruction=slow,
                conditional_half_quantum_per_instruction=faster,
                remaining_prefix_margin=READY_PREFIX-faster,
                boundary="Q is working-memory size, not image length L; neither this prefix rate nor the complete V=2 visit bound has been implemented here")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    modes=parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--write",action="store_true")
    modes.add_argument("--check",action="store_true")
    args=parser.parse_args()
    names=("FEASIBILITY.md","feasibility_model.py")
    hashes={name:sha256((HERE/name).read_bytes().replace(b"\r\n",b"\n")).hexdigest() for name in names}
    cases=[parameters(length) for length in (8192,65536)]
    record=dict(status="passed candidate arithmetic; H and W are conditional budgets, not actual service",
                sources_sha256_lf=hashes,degree=DEGREE,bays_per_target_side=BAYS,
                visit_budget=VISIT,per_target_invocation_bound=INVOCATION,
                command_delay=COMMAND_DELAY,ready_prefix_budget=READY_PREFIX,
                parameter_cases=cases,raw_history=raw_burst_witness(cases[0]),
                spatial=spatial_checks(),plant_compatibility=plant_units(),accounting=accounting(),
                bootstrap=bootstrap_budget())
    text=json.dumps(serial(record),sort_keys=True,indent=2)+"\n"
    path=HERE/"feasibility_results.json"
    if args.write:path.write_text(text,encoding="utf-8",newline="\n")
    else:assert path.read_text(encoding="utf-8")==text,"Feasibility record differs"
    print(json.dumps(dict(status=record["status"],image_cases=len(cases),
                         raw_interval_checks=record["raw_history"]["raw_interval_checks"],
                         spatial_cases=record["spatial"]["projected_placement_cases"])))


if __name__=="__main__":main()
