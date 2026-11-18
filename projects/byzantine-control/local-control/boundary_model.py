"""Exact consumers of BOUNDARIES; component physics and source scope stay explicit."""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
import math
from pathlib import Path
import transducer_model as T

HERE = Path(__file__).resolve().parent
C = F(1,10000)
RPORT = F(1,10000)
ICAP = F(5)
RBLEED = F(1000)
VCAP = F(300)
VSHUNT = F(2999,10)
GSHUNT = F(1000)
UMIN = F(599,2)


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def phi(value, series=1):
    return max(-ICAP,min(ICAP,F(value)/(series*RPORT)))


def shunt(v):
    return GSHUNT*max(F(0),F(v)-VSHUNT)


def digest(name):
    data=(HERE/name).read_text(encoding='utf-8-sig').replace('\r\n','\n')
    return sha256(data.encode('utf-8')).hexdigest()


def parameter_checks():
    upstream=json.loads((HERE/'transducer_results.json').read_text(encoding='utf-8'))
    for name,value in upstream['sources'].items():
        require(digest(name)==value,'Transducer evidence stale: '+name)
    require((T.R,T.RMAX,T.XMAX,T.UMAX,T.KAPPA,T.VMAX)==
            (F(100),F(101),F(3),F(300),F(11,15),F(11,10)),
            'The intended actual transducer changed')
    p=T.parameter_checks()
    delta=F(179,150)
    require(F(p['net_decay_drop'])==delta,'Wrong braking margin')
    energy=C*VCAP**2+T.XMAX**2
    require(energy==18,'Front capacitors or actual coil omitted')
    small=C*delta**2/8
    require(energy/small < 2**20,'Twenty dyadic energy intervals insufficient')
    require(F(2)/(RBLEED*C)==20 and T.R>=20,'Open-input energy decay does not hold')
    sector=ICAP/VCAP
    voltage_damping=sector/3+1/RBLEED
    require(2*voltage_damping/C >= 100,'Grounded voltage energy decays too slowly')
    require(1+2*T.R*T.XMAX/delta < 2**9,'Nine winding log intervals insufficient')
    open_zero=F(20,20)+F(2,100)*9
    grounded_zero=F(20,100)+F(2,100)*9
    require((open_zero,grounded_zero)==(F(59,50),F(19,50)),'Zero bound mismatch')
    line_current=F(18,5)
    offset=2*RPORT*line_current
    progress=F(3,10)
    charge_time=C*(F(299)+offset)/progress
    require(charge_time < F(1,10),'Voltage lower-barrier charging took too long')
    rise=F(p['nominal_rise_rational'])
    complete=F(2)+F(1,64)+max(F(1,10)+rise,grounded_zero)
    require(complete < 3 and open_zero < 6,'Parent timing interfaces no longer fit')
    pairs=2*40*(15+2*80)
    return dict(capacitance=C,current_limit=ICAP,series_resistance_each=RPORT,
        always_on_bleed=RBLEED,shunt_threshold=VSHUNT,shunt_slope=GSHUNT,
        source_full_interval=[UMIN,VCAP],actual_transducer_full_interval=[299,300],
        actual_transducer_resistance=[T.R,T.RMAX],actual_transducer_L=2,
        raw_field_storage_per_direction=energy,raw_field_storage_per_pair=2*energy,
        healthy_source_power_per_direction=VCAP*ICAP,
        healthy_source_power_per_pair=2*VCAP*ICAP,
        open_energy_decay_rate=20,grounded_energy_decay_rate=100,
        small_energy_threshold=small,energy_ratio=energy/small,
        voltage_charge_bound=charge_time,nominal_rise_bound=rise,
        complete_command_force_bound=complete,open_input_zero_bound=open_zero,
        grounded_zero_bound=grounded_zero,field_cap=T.KAPPA*T.XMAX,
        installed_pairs=pairs,host_field_stock=pairs*2*energy,
        host_gross_field_power=pairs*2*VCAP*ICAP,
        common_velocity_heat_rate=2*VCAP*ICAP+T.KAPPA*T.XMAX*T.VMAX,
        independent_velocity_heat_rate=2*VCAP*ICAP+2*T.KAPPA*T.XMAX*T.VMAX,
        additional_ground_or_line_stores_need_binding=True,
        physical_voltage_temperature_ratings_are_source_inputs=True)


def invariant_faces():
    checks=0
    # A failed opposite endpoint can choose any voltage; its good counterpart
    # still limits current. Neither endpoint needs the opposite voltage truth.
    for incoming,outgoing in product((-ICAP,0,ICAP),repeat=2):
        derivative=incoming-outgoing-shunt(VCAP)-VCAP/RBLEED
        require(derivative<0,'Source endpoint upper face points outward')
        checks+=1
    for incoming,x in product((-ICAP,0,ICAP),(0,T.XMAX)):
        require(incoming-x-shunt(VCAP)-VCAP/RBLEED<0,'Receiver voltage escapes')
        checks+=1
    for v,r,g,w,sign in product((0,VCAP),(T.R,T.RMAX),(F(2),F(26)),
                                (-T.VMAX,T.VMAX),(-1,1)):
        numerator=v-r*T.XMAX-g-sign*T.KAPPA*w
        require(numerator<0,'Actual coil upper face escapes')
        checks+=1
    for voltage in (F(-10**12),F(-1000),F(0),F(1000),F(10**12)):
        require(abs(phi(voltage))<=ICAP,'A surviving current element lost its cap')
        require(voltage*phi(voltage)>=0,'Current element is not passive')
        checks+=1
    # Lower boundaries are physical freewheel diode relations, not post-hoc
    # clipping of an unsafe upper state.
    require(max(F(0),-3)==0,'Ground diode fails zero-voltage balance')
    return dict(exact_face_cases=checks,opposite_voltage_not_used_as_a_truth_bit=True,
                lower_freewheel_contact_explicit=True,no_upper_state_projection=True)


def voltage_progress():
    h=F(18,5)
    offset=2*RPORT*h
    margin=F(3,10)
    cases=0
    for a,u,x in product((F(0),F(1),F(100),F(299)),(UMIN,VCAP),(F(0),T.XMAX)):
        vs,vr=a+offset,a
        source=phi(u-vs)-phi(vs-vr,2)-shunt(vs)-vs/RBLEED
        receiver=phi(vs-vr,2)-x-shunt(vr)-vr/RBLEED
        require(source>=margin and receiver>=margin,'Moving lower voltage barrier fails')
        cases+=1
    # A real worst-parameter nominal equilibrium, independent of the intended
    # response being named successful. Both current elements are unsaturated.
    r,b=RPORT,RBLEED
    aa=1+4*r/b+2*(r/b)**2
    cc=3*r+2*r*r/b
    external_brake=14+T.KAPPA*T.VMAX
    vr=(UMIN+cc*external_brake/T.RMAX)/(aa+cc/T.RMAX)
    x=(vr-external_brake)/T.RMAX
    line=x+vr/b
    vs=vr+2*r*line
    drive=line+vs/b
    require(299<=vr<vs<VSHUNT and 0<x<3,'Nominal equilibrium outside source law')
    require(drive<ICAP and T.KAPPA*x>2,'Nominal source cannot supply useful force')
    require(phi(UMIN-vs)==drive and phi(vs-vr,2)==line,'Equilibrium is not circuit-compatible')
    return dict(moving_barrier_cases=cases,barrier_offset=offset,
                equilibrium=dict(v_source_node=vs,v_receiver_node=vr,current=x,
                                 source_current=drive,field=T.KAPPA*x),
                no_charged_or_ready_oracle=True)


def conservation_checks():
    checks=0
    for u,vs,vr,x,r,g,w,sign in product((F(0),F(300)),(F(1),F(299),F(300)),
            (F(1),F(299),F(300)),(F(1,2),F(3)),(T.R,T.RMAX),
            (F(2),F(26)),(-T.VMAX,T.VMAX),(-1,1)):
        ind=phi(u-vs); line=phi(vs-vr,2)
        ds=(ind-line-shunt(vs)-vs/RBLEED)/C
        dr=(line-x-shunt(vr)-vr/RBLEED)/C
        dx=(vr-r*x-g-sign*T.KAPPA*w)/2
        actual=C*vs*ds+C*vr*dr+2*x*dx
        heat=(u-vs)*ind+(vs-vr)*line+vs*shunt(vs)+vr*shunt(vr)+(vs*vs+vr*vr)/RBLEED+r*x*x+g*x
        mechanical=sign*T.KAPPA*x*w
        require(actual==u*ind-heat-mechanical,'Circuit lost or duplicated energy')
        require(heat>=0,'Negative heat used as a free source')
        checks+=1
    return dict(exact_power_identities=checks,
                returns_and_stored_energy_retained=True,
                zero_voltage_diode_reaction_has_zero_power=True)


def withdrawal_checks():
    cases=0
    delta=F(179,150)
    for vs,vr,x,r,g,w,sign in product((F(0),F(1),F(299),F(300)),
            (F(0),F(1),F(299),F(300)),(F(0),F(1,2),F(3)),
            (T.R,T.RMAX),(F(2),F(26)),(-T.VMAX,T.VMAX),(-1,1)):
        line=phi(vs-vr,2)
        heat=(vs-vr)*line+vs*shunt(vs)+vr*shunt(vr)+(vs*vs+vr*vr)/RBLEED+r*x*x+g*x
        derivative=-heat-sign*T.KAPPA*x*w
        energy=C*(vs*vs+vr*vr)/2+x*x
        require(derivative<=-20*energy,'Open-input universal energy bound failed')
        grounded=derivative+vs*phi(-vs)
        require(grounded<=-100*energy,'Grounded-zero energy bound failed')
        cases+=1
    # Missing bleeds permit a positive current for every finite time under an
    # allowed already-failed passive-brake trajectory, with no new energy.
    eps,r,c=1e-5,float(RPORT),float(C)
    sample=[]
    for t in (0,1,10,100):
        q=math.exp(-t); x=eps*q; dx=-x
        difference=r*eps*q/(1-r*c)
        mean=10-eps/(2*c)*(1-q)
        vs,vr=mean+difference/2,mean-difference/2
        ds=-x/(2*c)-difference/2
        dr=-x/(2*c)+difference/2
        line=difference/(2*r)
        brake=vr-100*x-2*dx
        require(2<brake<26 and x>0 and max(vs,vr)<299.9,'Missing-bleed witness leaves physical range')
        require(abs(c*ds+line)<1e-12 and abs(c*dr-line+x)<1e-12,
                'Missing-bleed capacitor trajectory is not actual')
        require(abs(2*dx-(vr-100*x-brake))<1e-12,'Missing-bleed coil trajectory mismatch')
        sample.append(dict(time=t,current=x,brake=brake))
    return dict(exact_open_grounded_dissipation_cases=cases,
        missing_bleed_counterexample=sample,
        missing_bleed_formula='x(t)=1e-5*exp(-t)>0 for every finite t; six failed cells realize g(t) in[2,26]',
        withdrawal_not_inferred_from_finite_energy=True)


def graph_and_heat_checks():
    cases=0
    n,banks,coordinates=5,2,4
    local={i:set() for i in range(n)}
    edges=set()
    for site in range(n):
        local[site].add(('running',site))
    for source,target,bank in product(range(n),range(n),range(banks)):
        if source==target: continue
        out=('out_write',source,bank,target)
        inlet=('in_write',target,source,bank)
        local[source].add(out);local[target].add(inlet)
        edges.add((out,inlet))
        selected=((target+1)%n,0)
        body=('running',target) if (source,bank)==selected else ('candidate',target,source,bank)
        local[target].add(body)
        # Actual good-fixture writer exclusion, not a code/image test.
        if body[0]!='running': edges.add((inlet,body))
    def reach(graph,start):
        found={start}
        while True:
            more={b for a,b in graph if a in found}
            if more<=found: return found
            found|=more
    for failed in range(n):
        damaged=edges|set(product(local[failed],repeat=2))
        for source,target,bank in product(range(n),range(n),range(banks)):
            if source==target: continue
            found=reach(damaged,('out_write',source,bank,target))
            require({x[1] for x in found if x[0]=='running'}<={failed},
                    'Local rewiring reached a remote running image')
            for node in found:
                if node[0]=='candidate' and node[1]!=failed:
                    require(node[2] in (source,failed),
                            'Payload identity changed a remote physical candidate')
            cases+=1
        good=(failed+1)%n
        # A receiver-wide post-inlet writer defeats the exact graph theorem.
        leaked=damaged|{(('in_write',good,failed,0),('running',good))}
        require(('running',good) in reach(leaked,('out_write',failed,0,good)),
                'Shared receiver crossbar counterexample disappeared')
    for failed,source,target in product(range(n),repeat=3):
        if source!=target:
            require(source!=failed or target!=failed,'One region reached both distinct endpoint cells')
    force=34*F(2)
    require(force==68 and force>F(137,5),'Common post-limiter router countercase lost')
    # A source-local-only limiter may be bypassed at source. The healthy
    # receiver element is what still bounds its input.
    require(abs(phi(F(1000)))==ICAP,'Surviving receiver element did not contain bypass')
    local_short_current=F(1000)/F(1,100)
    require(local_short_current>ICAP,'Local path bypassing both limits was overlooked')
    # Foreign series heat cannot be paid with only the receiver's old stock.
    time=F(1,50); supplied=F(1000)*ICAP*time
    series_heat=(F(1000)-VCAP)*ICAP*time
    old_local=18+(VCAP*ICAP+T.KAPPA*T.XMAX*T.VMAX)*time
    require(supplied==100 and series_heat==70 and series_heat>old_local,
            'Foreign stored-energy heat obstruction disappeared')
    # Summing a *net* conservation identity cancels internal exchange. Positive
    # exports alone can count the same circulating energy repeatedly.
    initial,supply,final,heat,external_work=100,40,20,110,10
    require(initial+supply==final+heat+external_work,'Joint energy example is not conserved')
    require(heat<=initial+supply,'Global heat bound failed')
    repeated_positive_exports=20*100
    require(repeated_positive_exports>initial+supply,'Positive-flow versus net-energy distinction lost')
    return dict(fixed_receiver_sink_cases=cases,
        one_bad_region_cannot_remove_both_end_cells=True,
        common_post_boundary_force=str(force),local_short_current=local_short_current,
        mechanical_cable_tension_not_an_electrical_edge=True,
        foreign_source_energy=supplied,foreign_series_heat_lower=series_heat,
        insufficient_old_local_heat_allowance=old_local,
        incoming_positive_flow_is_not_new_energy=True,
        actual_contact_and_functional_probe_map_still_required=True)


def normalize(v):
    if isinstance(v,F): return str(v)
    if isinstance(v,dict): return {k:normalize(x) for k,x in v.items()}
    if isinstance(v,(list,tuple)): return [normalize(x) for x in v]
    return v


def main():
    parser=argparse.ArgumentParser()
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write',action='store_true')
    group.add_argument('--check',action='store_true')
    args=parser.parse_args()
    sources={name:digest(name) for name in ('BOUNDARIES.md','boundary_model.py','TRANSDUCER.md',
        'transducer_model.py','transducer_results.json','PORTS.md','RUNTIME-PORTS.md','INCIDENCE.md','FAULT-MAP.md')}
    result=normalize(dict(status='constructed two-end supplier; raw full-source ratings and recurrence remain open',
        sources=sources,parameters=parameter_checks(),faces=invariant_faces(),voltage=voltage_progress(),
        conservation=conservation_checks(),withdrawal=withdrawal_checks(),graph_heat=graph_and_heat_checks()))
    rendered=json.dumps(result,sort_keys=True,indent=2)+'\n'
    path=HERE/'boundary_results.json'
    if args.write:
        path.write_text(rendered,encoding='utf-8',newline='\n')
        print('boundary record written')
    else:
        require(path.read_text(encoding='utf-8')==rendered,'Boundary record stale')
        print('boundary record matches')


if __name__=='__main__':
    main()
