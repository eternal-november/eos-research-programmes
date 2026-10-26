"""Exact W0 resource probes; no successful repair or source admission is assumed."""
from __future__ import annotations
import sys
if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent


def admissible_supply(values,rate,latency):
    for left in range(len(values)):
        total=0
        for right in range(left,len(values)):
            total+=values[right]
            if total<rate*max(0,right-left+1-latency):return False
    return True


def run_stock(supply,demand,capacity,clip_first):
    stock=capacity;history=[stock]
    for tick,(energy,cost) in enumerate(zip(supply,demand)):
        available=min(capacity,stock+energy) if clip_first else stock+energy
        if available<cost:return dict(failure=tick,stocks=history,available=available)
        stock=available-cost if clip_first else min(capacity,available-cost)
        history.append(stock)
    return dict(failure=None,stocks=history)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    modes=p.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    args=p.parse_args()
    names=('PROBES.md','capacity_probe.py')
    hashes=lambda:{n:sha256((HERE/n).read_bytes().replace(b'\r\n',b'\n')).hexdigest() for n in names}
    before=hashes()
    accepted=0
    for supply in product((0,9),repeat=12):
        if not admissible_supply(supply,3,2):continue
        assert run_stock(supply,[3]*12,6,False)['failure'] is None
        assert run_stock(supply,[3]*12,9,True)['failure'] is None
        accepted+=1
    periodic=[0,0,9]*8
    assert admissible_supply(periodic,3,2)
    net=run_stock(periodic,[3]*len(periodic),6,False)
    failed=run_stock(periodic,[3]*len(periodic),6,True)
    proper=run_stock(periodic,[3]*len(periodic),9,True)
    assert net['failure'] is None and failed['failure']==4 and proper['failure'] is None
    assert net['stocks'][3:6]==[6,3,0]
    assert proper['stocks'][3:6]==[6,3,0]
    exact_cases=0
    for length in range(1,5):
        for supply in product(range(3),repeat=length):
            for demand in product(range(3),repeat=length):
                direct=max(sum(demand[a:b])-sum(supply[a:b])
                    for a in range(length) for b in range(a+1,length+1))
                clipped=max(sum(demand[a:b])-sum(supply[a+1:b])
                    for a in range(length) for b in range(a+1,length+1))
                for capacity in range(5):
                    assert (run_stock(supply,demand,capacity,False)['failure'] is None)==(direct<=capacity)
                    assert (run_stock(supply,demand,capacity,True)['failure'] is None)==(clipped<=capacity)
                    exact_cases+=1
    assert exact_cases==36900
    arithmetic=0
    for burst,rate,gap,surplus in product((F(0),F(1,2),F(5)),(F(1),F(3,2),F(7)),range(5),(F(0),F(1),F(4))):
        supply_rate=rate+surplus
        for length in [F(0),F(gap,2),F(gap),F(gap+1),F(100)]:
            assert burst+rate*length-supply_rate*max(F(0),length-gap)<=burst+rate*gap
        for length in range(1,21):
            assert burst+rate*length-supply_rate*max(F(0),length-1-gap)<=burst+rate*(gap+1)
        arithmetic+=1
    assert F(120)/(F(1,2)*F(3))==80
    closures=0
    for base,burst,work,service,arrival in product((F(1),F(5)),(F(0),F(2)),(F(1),F(3)),(F(2),F(5)),(F(0),F(1,4),F(1))):
        if arrival*work>=service:continue
        horizon=(base+work*burst/service)/(1-arrival*work/service)
        rhs=lambda h:base+work*(burst+arrival*h)/service
        assert rhs(horizon)==horizon
        assert rhs(horizon+1)<horizon+1 and rhs(horizon-F(1,10))>horizon-F(1,10)
        closures+=1
    assert before==hashes()
    result={'status':'passed','scope':'conditional resource-order probes and finite enumeration; not the full AC source theorem',
        'sources_sha256_lf':before,'all_binary_supply_words':2**12,'admitted_words':accepted,
        'rational_envelope_parameter_cases':arithmetic,
        'exact_interval_trace_capacity_cases':exact_cases,'conditional_closure_cases':closures,
        'periodic_supply':periodic,'net_update_capacity6':net,
        'clip_first_capacity6_counterexample':failed,'clip_first_capacity9':proper,
        'health_example':{'initial':120,'loss_per_service':'1/2','required_rate':3,'maximum_endurance':80}}
    encoded=json.dumps(result,sort_keys=True,indent=2)+'\n';path=HERE/'capacity_results.json'
    if args.write:path.write_text(encoded,encoding='utf-8',newline='\n')
    else:assert path.read_text(encoding='utf-8')==encoded,'Record differs; inspect before refresh'
    print(json.dumps({'status':'passed','admitted_words':accepted,'parameter_cases':arithmetic,'charging_order_failure_tick':4}))


if __name__=='__main__':main()
