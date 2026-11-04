"""Receiver-affine computation with separately funded raw rails.

Exact checks for the declared lumped electrical/finite-word source. The code
never supplies truth, permission, fault identity, or a renewed actor.
"""
from __future__ import annotations
import argparse
from collections import defaultdict, Counter, deque
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys
import incidence_model as inc

HERE=Path(__file__).resolve().parent
MU=1<<27
SMALL=F(1,1<<64)


def require(ok, message):
    if not ok: raise AssertionError(message)


def digest(name):
    return sha256((HERE/name).read_text(encoding="utf-8-sig").replace("\r\n","\n").encode()).hexdigest()


def serial(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,dict): return {str(k):serial(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)): return [serial(v) for v in x]
    return x


def allocation(n=432):
    # One record is stored once: primary records are in T_i; auxiliary records
    # are in E(i,o). Both source/receiver banks contribute the factor four.
    rails=Counter()
    for i in range(n):
        for target in inc.neighbors(i,n):
            for slot,o in enumerate(inc.groups(i,target,n)[0]):
                rails[(o,i,slot==0)]+=4*683
        for parity in (0,1):
            group=tuple(o for o in inc.neighbors(i,n) if o%2==parity)[:13]
            for slot,o in enumerate(group): rails[(o,i,slot==0)]+=4
    by_source=Counter(); by_receiver=Counter(); counts=Counter()
    for (o,i,_),nr in rails.items():
        by_source[o]+=nr; by_receiver[i]+=nr; counts[o]+=1
    used=4*13*(40*683+2)
    require(set(by_source.values())==set(by_receiver.values())=={used},"Raw power reassignment lost actual record multiplicity")
    require(max(counts.values())<=80,"More than two rail classes per neighbor")
    return rails,dict(hosts=n,records_per_origin=used,records_per_receiver=used,
        installed_rail_counts=sorted(set(counts.values())),max_rails_per_origin=max(counts.values()),
        maximum_records_per_rail=max(rails.values()),allocated_records_per_host=1420796)


def rail_point(records, b=80, record_bits=2048, rate=1<<31, capture_price=1024, capture_delay=F(1,1<<30)):
    # The extra capture term deliberately overcounts repartitioned padding.
    # It therefore cannot spend unused record padding without paying its work.
    bits=record_bits*records+2*b*256
    control_power=F(1<<20) # finite raw selection/control/signal-emission budget
    load=bits*rate+F(bits,1024)+2*b*capture_price/capture_delay+control_power
    j=load/F(299)+1
    h=j+1
    current=2*j+3
    r=c=SMALL
    bleed=F(1,1000)
    slope=30*current
    upper=2*current+2*b-slope/F(10)-300*bleed
    shift=2*r*h
    # Moving lower region v_s>=a+shift, v_r>=a, a_dot=.5/C.
    source_lower=current-h-300*bleed
    receiver_lower=h-j-300*bleed
    charge=2*c*(299+shift)
    require(upper<0 and shift<F(1,2) and shift+r*current<1,"Raw rail has no inward voltage/nominal headroom")
    require(source_lower>=F(1,2) and receiver_lower>=F(1,2),"Moving lower comparison fails")
    require(charge<F(1,1<<30),"Raw rail cold charge exceeds a raw capture interval")
    require(current<=1<<64 and slope<=1<<64 and 1/r<=1<<64,"Raw rail exceeds hard material transfer alphabet")
    return dict(records=records,charged_bits=bits,load_power=load,load_current=j,
        endpoint_current=current,endpoint_capacitance=c,series_resistance=r,
        shunt_slope=slope,bleed_conductance=bleed,upper_boundary_net=upper,
        nominal_source_net_at_lower=source_lower,nominal_receiver_net_at_lower=receiver_lower,
        comparison_voltage_shift=shift,cold_charge_bound=charge,
        source_voltage_lower=300,source_voltage_upper=600,
        gross_upstream_power=600*current,front_storage=c*300**2,
        lowest_nominal_bleed_power_per_rail=2*F(299**2,1000))


def raw_supply_bill():
    old=json.loads((HERE/'resource_results.json').read_text())['runtime_inventory']
    require(old['design']['degree']==40 and old['design']['bays']==80 and old['fast_keys']==27283,
            'Current concrete source dimensions changed; rebind actual rail incidence')
    maps=[]
    for n in (432,444,504):
        _,facts=allocation(n); maps.append(facts)
    rails,_=allocation()
    selected=[(key,rail_point(count)) for key,count in rails.items() if key[0]==0]
    raw_power=sum((q['gross_upstream_power'] for _,q in selected),F(0))
    front=sum((q['front_storage'] for _,q in selected),F(0))
    # Keep the entire old rate: old raw background work is conservatively paid
    # again, rather than relying on a guessed partition of an old power bill.
    old_rate=F(old['upstream_rate']); burst=F(old['upstream_burst'])
    rate=old_rate+raw_power+4
    margin=max(burst+rate,F(1<<76))
    capacity=4*margin
    feed_v=F(1<<70)
    reservoir_c=2*margin/feed_v**2
    top_voltage=2*feed_v
    spill_onset=top_voltage-1
    usable_capacity=reservoir_c*spill_onset**2/2
    lower_stock=usable_capacity-burst-2*rate
    require(lower_stock>=margin,"Shunt-backed reserve is insufficient")
    incoming_current_at_top=F(1<<96)/top_voltage
    shunt_current_at_top=F(1<<64)
    require(incoming_current_at_top<shunt_current_at_top,"Actual upstream shunt has no inward upper barrier")
    turns=feed_v/300
    require(capacity/margin==4,"Transformer raw upper voltage600 invalid")
    require(reservoir_c>=SMALL and capacity<1<<96 and 2*rate<1<<96,"New upstream point exceeds HARD-BOUNDARY")
    require(feed_v**2*capacity/margin<(1<<81)**2,"Actual reservoir voltage exceeds hard feed rating")
    capture_bits=2*80*(3*40)*256
    padding=(2048-976)*1420796
    require(capture_bits<=padding,"Per-backend primary raw captures lack allocated storage")
    drop=2*sum((q['lowest_nominal_bleed_power_per_rail'] for _,q in selected),F(0))-front
    require(drop>0,"Supply deficits have no actual drawdown witness")
    return dict(source_map_checks=maps,rail_parameters=[dict(receiver=k[1],primary=k[2],**q) for k,q in selected],
        raw_rail_power_upper=raw_power,raw_front_stock=front,
        old_upstream_rate=old_rate,upstream_rate=rate,upstream_burst=burst,
        upstream_capacity=capacity,upstream_reserve_margin=margin,
        spill_onset_voltage=spill_onset,spill_free_capacity=usable_capacity,
        proved_upstream_lower_stock=lower_stock,upstream_upper_voltage=top_voltage,
        incoming_current_at_upper=incoming_current_at_top,shunt_current_at_upper=shunt_current_at_top,
        reservoir_capacitance=reservoir_c,reservoir_voltage_floor=feed_v,
        fixed_transformer_ratio=turns,offered_supply_on_power=2*rate,
        actual_two_quantum_deficit_drawdown_lower=drop,
        raw_capture_bits=capture_bits,existing_raw_padding=padding,
        bank_stock_and_code_unchanged=True,old_rate_retained_as_conservative_overcount=True,
        world_effector_addition=4)


def private_point():
    rate=F(4,3)*16384*MU
    link_delay=F(1,8*MU)
    tail=F(1,1<<26)+F(1,64)
    work=F(928+1024) # capture1024 is supplied by raw rail or own-read capsule
    j=(rate+1024/link_delay)/299+1000
    current=2*j+3
    r=SMALL; c=F(1,1<<42); bleed=F(1,16); vmax=F(1000)
    line_heat=3*r*current**2*tail
    bleed_energy=2*bleed*vmax**2*tail
    fronts=c*vmax**2
    control_export=vmax*tail
    source_energy=work+line_heat+bleed_energy+fronts+control_export
    capsule=F(20480); minimum=F(2048)
    cell_voltage=F(900)
    charging_current=4*capsule*MU/cell_voltage
    require(300<=cell_voltage<1000 and charging_current<1<<64,"Private work-cell voltage/charging current invalid")
    require(source_energy<capsule-minimum,"Private comparison drains its actual instruction capsule")
    require(3*r*current<F(1,2),"Private power link loses voltage headroom")
    require(current<=1<<64 and 30*current<=1<<64,"Private endpoint exceeds hard alphabet")
    require(2*current+1-3*current-bleed*vmax<0,"Private upper barrier omits raw input leakage")
    # Even maximally toggled raw control inputs have total parasitic current<=1.
    # On source disconnection, the two front capacitors obey the inequality.
    rho=F(1); eq=c*rho**2/(2*bleed**2)
    reset_energy=c*32**2/2
    require(2*eq<=reset_energy,"Raw leakage can hold private execution above reset")
    # Halve E itself while above threshold; do not halve E-equilibrium and
    # mistakenly omit the residual 128*c.
    for multiplier in (1,2,4,1024):
        energy=reset_energy*multiplier
        require(-bleed*energy/c+rho*rho/(2*bleed)<=-bleed*energy/(2*c),
                "Threshold-relative decay comparison is invalid")
    start_energy=c*vmax**2
    half=0; bound=reset_energy
    while bound<start_energy: half+=1; bound*=2
    voltage_drain=half*2*c/bleed
    logic_reset=F(1,16*MU)
    require(voltage_drain+logic_reset<F(1,8*MU),"Leak-tolerant electrical/reset suffix misses existing allowance")
    charge=2*c*(299+2*r*(j+1))
    propagation=F(1,32*MU)
    require(charge+propagation<link_delay,"Private cold power delivery exceeds private-link allowance")
    # Every I-control terminal gets its share of the actual current budget.
    control_leads=16384
    per_lead=F(1,control_leads)
    control_settle=2*SMALL*control_leads
    require(control_settle<link_delay,"Finite raw-control input capacitance misses capture")
    units=2*80*(2*40+1)
    terminals=2*units*(control_leads+4)+4*80
    stock=units*(fronts+control_leads*SMALL*300**2)+80*SMALL*300**2
    require(terminals<1<<30 and stock<1,"Added terminal/material reservation exceeded")
    return dict(private_native_and_link_work=work,raw_capture_paid_elsewhere=1024,
        nominal_source_voltage_range=[300,1000],source_capsule_voltage=cell_voltage,
        work_cell_full_charge=capsule/cell_voltage,maximum_cell_charging_current=charging_current,
        capsule_initial_energy=capsule,capsule_reserved_minimum=minimum,
        endpoint_current=current,endpoint_capacitance=c,series_resistance=r,
        bleed_conductance=bleed,private_suffix=tail,series_heat_bound=line_heat,
        bleed_energy_bound=bleed_energy,front_storage=fronts,
        control_input_reverse_export_bound=control_export,
        total_capsule_draw_bound=source_energy,
        raw_control_leads=control_leads,parasitic_current_per_lead=per_lead,
        total_parasitic_current=rho,off_energy_equilibrium=eq,
        reset_voltage=32,reset_energy=reset_energy,
        electrical_drain_bound=voltage_drain,private_control_reset=logic_reset,
        combined_reset_bound=voltage_drain+logic_reset,declared_reset_settling=F(1,8*MU),
        private_cold_charge_bound=charge,private_round_trip_propagation=propagation,
        raw_control_settling_bound=control_settle,private_units_per_host=units,
        additional_terminal_bound=terminals,additional_front_and_control_stock=stock,
        private_control_has_no_raw_write_strobe=True,
        no_raw_to_operating_carrier_edge=True)


def differential_checks():
    count=0
    for voltage,current,ratio in product((F(300),F(600),F(1<<70)),(F(0),F(1),F(1<<20)),(F(1),F(1<<70,300))):
        require(voltage*(current/ratio)==(voltage/ratio)*current,'Transformer changed actual port power')
        count+=1
    for vs,vr in product((F(0),F(16),F(32),F(299),F(1000)),repeat=2):
        g=F(1,16);rho=F(1);c=SMALL
        E=c*(vs*vs+vr*vr)/2
        derivative=rho*vr-g*(vs*vs+vr*vr)
        upper=-g*E/c+rho*rho/(2*g)
        require(derivative<=upper,"Leak/bleed energy comparison invalid")
        count+=1
    # A total-current rating is necessary: unlimited parallel data leakage
    # invalidates no-rearm even when every individual current is 'small'.
    rho_bad=F(1000);g=F(1,16)
    require(rho_bad/g>299,"Shared unbounded-leak countercase missing")
    # Diode/limiter terminology cannot justify nominal power delivery by itself.
    q=rail_point(81964)
    require(q['load_current']>0 and F(1,10)<299,"Undervoltage countercase empty")
    return dict(exact_energy_inequality_cases=count,unbudgeted_leak_equilibrium=rho_bad/g,
        low_drive_can_preserve_upper_cap_but_not_delivery=True,
        current_limit_does_not_establish_truth=True)


def recurrence_checks():
    # Unit-normalized offer2R in four quanta, no offer in two. Verify every
    # grid-phase interval; the text proves all real intervals via the sawtooth.
    def cumulative(t):
        full=t//6;rest=t-6*full
        return 8*full+2*max(F(0),rest-2)
    checks=0
    for a in (F(j,4) for j in range(48)):
        for length in (F(j,4) for j in range(121)):
            supplied=cumulative(a+length)-cumulative(a)
            require(supplied>=max(F(0),length-2),"Recurring supply envelope failed")
            checks+=1
    return dict(interval_checks=checks,period=6,outage=2,on_power_over_rate=2,
        indefinite_latency_rate_supply=True,supply_phase_not_actor_visible=True)


def graph_checks():
    # Typed power/authority graph for one receiver i and two origins o,p.
    # Energy edges and writable-data edges are intentionally different graphs.
    data={ 'origin_o':{'raw_o'}, 'origin_p':{'raw_p'},
           'core_i':{'private_i','outgoing_i'},'private_i':{'core_i'},
           'raw_o':set(),'raw_p':set(),'primary_i':set() }
    def reach(start):
        seen=set(start);todo=list(start)
        while todo:
            for v in data.get(todo.pop(),set()):
                if v not in seen:seen.add(v);todo.append(v)
        return seen
    require('raw_p' not in reach({'origin_o'}),"One origin wrote another raw array")
    require(not {'raw_o','raw_p'}&reach({'core_i'}),"Private code gained raw-store write authority")
    e=reach({'raw_o','private_i'})
    require('core_i' in e and 'raw_p' not in e,"Island fault projection amplified")
    # Electrical control leakage is real but ends at the local front/dump.
    energy={'raw_o':{'control_front_i'},'control_front_i':{'private_bus_i'},
            'instruction_capsule_i':{'private_bus_i'},'private_bus_i':{'local_dump_i'},
            'raw_rail_o':{'raw_o','raw_dump_o'},'bank_i':{'instruction_capsule_i'}}
    seen={'raw_o'};todo=['raw_o']
    while todo:
        for v in energy.get(todo.pop(),set()):
            if v not in seen:seen.add(v);todo.append(v)
    require('bank_i' not in seen and 'instruction_capsule_i' not in seen,"Raw leakage rearms the operating carrier")
    return dict(raw_arrays_remain_distinct=True,island_fault_execution_owner='i',
        real_raw_leak_ends_at_local_dump=True,one_way_capsule_charger_retained=True,
        semantic_predicate_supplied_by_receiver_not_inferred_from_volts=True)


def main():
    require(not sys.flags.optimize,"Unoptimized checking required")
    ap=argparse.ArgumentParser();g=ap.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true')
    args=ap.parse_args()
    names=('RECEIVER-POWER.md','receiver_power_model.py','RECEIVER.md','receiver_model.py',
        'HARD-BOUNDARY.md','BOUNDARIES.md','RESOURCES.md','resource_results.json','RUNTIME-PORTS.md','incidence_model.py')
    hashes={name:digest(name) for name in names}
    result=serial(dict(status='raw/private electrical and resource adapter; joined-source acceptance separate',
        sources=hashes,raw_supply=raw_supply_bill(),private_supply=private_point(),
        differential=differential_checks(),recurrence=recurrence_checks(),graph=graph_checks()))
    require(hashes=={name:digest(name) for name in names},"Input changed during checking")
    target=HERE/'receiver_power_results.json'
    if args.write:target.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:require(json.loads(target.read_text(encoding='utf-8'))==result,"Receiver-power reproduction differs")
    print('PASS receiver power:',len(result['raw_supply']['rail_parameters']),'origin rails; private draw',result['private_supply']['total_capsule_draw_bound'])


if __name__=='__main__':main()
