"""Exact replacement and semantic checks for the primary source assembly.

Universal hybrid/strategy arguments are in PRIMARY-ASSEMBLY.md. Immutable
records are inputs, not a simulation of the entire indefinite population.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
import math
from pathlib import Path
import subprocess
import sys
import types

if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')
HERE=Path(__file__).resolve().parent
PREFIX='theories-and-designs/byzantine-control/local-control/'
SOURCE_REV='95f4a0938c689dcb9d1ff13af2d077d70a21bbf0'
RESOURCE_REV='e666c823a55be7486888cb3b581722ec797d48e8'
CORE_REV='613670b378e54276f6bb2e67f582de27a02e8380'
COUPLED_REV='613670b378e54276f6bb2e67f582de27a02e8380'

def need(ok,msg):
    if not ok: raise AssertionError(msg)

def text_at(rev,name):
    return subprocess.check_output(['git','show',rev+':'+PREFIX+name],cwd=HERE).decode('utf-8-sig').replace('\r\n','\n')

def digest(text):return sha256(text.encode('utf-8')).hexdigest()

def frozen(rev,name):
    text=text_at(rev,name);r=json.loads(text)
    for n,h in r.get('sources',{}).items():
        need(digest(text_at(rev,n))==h,'Stale immutable source '+n)
    return r,dict(commit=subprocess.check_output(['git','rev-parse',rev],cwd=HERE).decode().strip(),record=name,sha256=digest(text))

def inputs():
    need(RESOURCE_REV is not None,'Final immutable resource/source binding is not yet selected')
    source,sb=frozen(SOURCE_REV,'port_source_results.json')
    resource,rb=frozen(RESOURCE_REV,'port_resource_results.json')
    initial,ib=frozen(CORE_REV,'initial_return_results.json')
    geometry,gb=frozen(CORE_REV,'geometry_results.json')
    receiver,reb=frozen(CORE_REV,'receiver_results.json')
    need(receiver['projection']['one_shared_cover'] and receiver['projection']['two_sites_one_owner_two_inputs'],'Receiver token map lost multiplicity')
    need(receiver['concrete_graph']['input_dependence_not_private_write_authority'],'Raw input was aliased with execution writes')
    coupled,cb=frozen(COUPLED_REV,'coupled_port_results.json')
    need(resource['bindings']['source']['commit']==sb['commit'],'Resource and source are different physical histories')
    need(not source['parameters']['raw_capture']['receiver_waits_for_raw_ready'],'Raw input fault can stop every private consumer')
    need(source['parameters']['hard_work_store']['all_mode_intrinsic'],'Nominal charge limit was substituted for a hard capacity')
    for n,h in source['base_binding']['sources'].items():
        need(digest(text_at(source['base_binding']['commit'],n))==h,'Source base is stale: '+n)
    return source,resource,initial,geometry,receiver,coupled,dict(source=sb,resources=rb,initial=ib,geometry=gb,receiver=reb,coupled=cb)

def world_adapter(source,initial,geometry):
    p=source['parameters']['world'];m=p['fixed_regional_population'];M=p['raw_world_flow_bound']
    b=p['effective_cover'];physical=p['persistent_physical_sites'];bad=b+M*physical
    tau=F(p['plant_time_per_hardware_quantum']);xdot=F(2);rowrate=2*xdot
    age=F(initial['world']['effect_age']);radius=F(initial['world']['verification_radius'])
    beta=F(1,200)+rowrate*tau*age
    need(2*beta<radius and radius+beta<F(1,50),'Actual changing rows do not support the old quantile interface')
    command=2*(beta+F(1,2000))+F(1,100)
    decay=F(2,11**10);lag=2*xdot*tau/F(1,100);error=command+lag+decay
    need(error<F(1,25),'Actual tracker cannot refine .84/.36 collar')
    need(F(88,100)-error>F(84,100) and F(32,100)+error<F(36,100),'True force/flow collar lost')
    need(m%2==0 and m>=12*(6+M)+2 and m>=72,'Population does not cover complete export')
    world_capacity=F(m)/tau
    for x in (F(35,100),F(1,2),F(65,100)):
        for flow in (F(-1),F(0),F(1),F(M)):
            dx=-flow/world_capacity
            need(world_capacity*x*dx==-x*flow,'Actual WORLD effort/flow/storage units do not cancel')
    need(F(p['complete_absolute_world_work_ceiling'],1)/(F(p['safety_lower'])*tau)>M,'Plant-time-flow countercase vanished')
    need(F(p['complete_absolute_world_work_ceiling'],1)/F(p['safety_lower'])<M,'Actual work/flow conversion is unsound')
    upper=F(84,100)*(1-F(b,m))-F(bad,m)
    lower=F(36,100)+F(bad,m)
    service=F(3,10)*(1-F(b,m))-F(bad,m)
    upper_required=F(61,100)+F(1,100)+F(2,100)+3*F(2,100)*F(1,100)
    lower_required=F(59,100)-F(1,100)-F(2,100)-3*F(2,100)*F(1,100)
    need(upper>upper_required and lower<lower_required,'Actual inward collars lost')
    need(service>F(1,10),'Actual continuing service lost')
    absolute_rate=F(61,100)+F(9,10)+F(bad,m)+3*F(2,100)*F(3,10)+F(1,100)+F(2,100)
    need(absolute_rate<xdot,'Claimed derivative does not follow from complete output')
    startup=xdot*tau*F(initial['initial']['commissioning'])
    need(startup<F(1,20),'Entry tube reaches boundary before useful feedback')
    ctl=lambda n:max(30,min(90,60+(2*((n//2)-500))//10))
    need(min(ctl(n) for n in range(1240,3001))==84,'Integer upper collar changed')
    need(max(ctl(n) for n in range(-1000,761))==36,'Integer lower collar changed')
    return dict(actual_state_derivative_upper=xdot,actual_row_rate_upper=rowrate,plant_time_per_quantum=tau,
        command_age=age,available_row_error=beta,validation_only_error=radius+beta,command_error=command,
        tracker_initial_residue=decay,tracker_lag=lag,actual_tracker_error=error,
        regional_population=m,actual_world_capacity_per_coordinate=world_capacity,world_store_is_external=True,raw_site_export=M,typed_loss_plus_export=bad,upper_flow_lower=upper,lower_flow_upper=lower,
        upper_inward_margin=upper-upper_required,lower_inward_margin=lower_required-lower,service_lower=service,
        commissioning_displacement=startup,old_M4_derivative_not_imported=True,off_body_export_not_subtracted=True)

def force_deadline_adapter(source,initial,geometry,coupled):
    m=source['mechanical'];s=source['return_schedule'];p=source['parameters']['mechanical']
    tau=F(p['tau']);H=s['conditional_return_H'];Hold=s['previous_return_H'];rate=F(s['original_raw_acquisition_rate'])
    clear=F(m['clearance_time']);age=F(source['base_binding']['functional_guard_horizon'])
    drift=(F(p['hard_j_l1'])+22*F(m['W_hard'])/tau)/(128*tau)
    upper=F(3,2)*(F(1,2)+F(1,100))+drift*age
    need(upper<1 and drift==F(273,4194304),'Actual load continuation cannot support LOAD500')
    old=coupled['primary_source_mechanics']
    for key,value in [('hard_potential',m['W_hard']),('physical_mechanical_energy_upper',m['mechanical_hard_storage']),
                      ('actual_clearance_time',clear),('force_continuation_growth',drift),('actual_force_guard_upper',upper),
                      ('updated_return_H',H),('original_raw_compromise_rate',rate)]:
        need(F(old[key])==F(value),'Shared coupled point changed without a new adapter: '+key)

    need(F(m['clear_load_upper'])<=F(1,8),'Obtained shunt does not produce usable low force')
    need(H==Hold+5*clear and rate==F(1,104548602495950),'Deadline was paid by silently slowing faults')
    need(1+2+math.floor(3+2*rate*H)==6,'Shared two-H incident cover exceeds six')
    t=geometry['timing'];sequence=F(s['unchanged_partial_bound'])+F(s['abort'])+2*F(s['half_cycle'])+F(t['old_suffix'])
    slack=F(H)-F(t['commissioning'])-sequence
    need(slack>0 and slack==F(s['strict_slack']),'No strict causal prefix slack')
    need(F(s['unchanged_timer_job'])<=F(s['unchanged_nontransferable_ready_window']),'Timer job lacks one ready interval')
    need(F(m['varying_coefficient_loaded_entry'])+6<F(s['actual_pre_power_travel_lower']),'Uncleared early exit was spliced to a fresh loaded state')
    need(F(initial['initial']['ready_including_tracker_upper'])<F(t['commissioning']),'Commissioning needs a repaired future bank')
    need(F(initial['initial']['first_old_effect_loss_lower'])-F(t['commissioning'])>F(t['work']),'Initial ready interval omits complete work')
    need(F(initial['initial']['remaining_drain_min'])>F(initial['initial']['last_old_prefix_effect']),'Initial hidden old effect survives formation')
    opposition=6*F(22,5)+F(p['total_coordinate_disturbance'])
    need(opposition==F(55,2) and opposition<28 and 68-opposition-29>=2,'Contested force margins fail')
    need(F(s['unchanged_earliest_timeout'])>clear,'Clearance was inserted beyond watch')
    # Whole finite record is separately hashed; the final selected source must
    # retain the same shared-state point even when its additional adapters grow.
    return dict(force_growth=drift,force_age=age,guard_force_upper=upper,bank_side_clearance=clear,
        actual_clear_force_upper=F(m['clear_load_upper']),return_H=H,unchanged_lambda=rate,shared_token_cover=6,
        repair_sequence=sequence,strict_prefix_slack=slack,contested_opposition=opposition,
        minimum_progress_surplus=68-opposition-29,loaded_entry=F(m['varying_coefficient_loaded_entry']),
        pre_power_travel=F(s['actual_pre_power_travel_lower']),one_history_not_marginal_budgets=True)

def timing_adapter(source,geometry,initial):
    p=source['parameters']['execution'];c=source['capture_work'];g=geometry['compiler']['processing_certificate']
    need(F(p['nominal_instruction_rate_min'])==F(g['instruction_service_min_per_quantum']),'Nominal service minimum changed')
    need(F(p['nominal_instruction_rate_max'])==F(g['instruction_service_max_per_quantum']),'Nominal service maximum changed')
    delta=F(source['parameters']['raw_capture']['recharge_delta'])
    earliest=F(p['private_capture_timer_edges']-1,p['private_capture_timer_tick_max'])
    latest=F(p['private_capture_timer_edges'])/F(p['private_capture_timer_tick_min'])
    need(earliest>=F(c['raw_good_capture_upper']),'Private strobe can outrun actual source capture')
    suffix=latest+2*delta+F(p['private_io_boundary_work_upper']+p['private_reset_work_upper'])/F(p['private_native_work_rate_capacity'])
    need(suffix==F(c['actual_private_suffix']),'The independent-phase timer has an unpriced suffix')
    need(suffix>6*delta and suffix<=F(3,4)/F(p['nominal_instruction_rate_max']),'Hard/nominal service scopes were conflated')
    need(suffix+2*delta<F(1)/F(p['nominal_instruction_rate_max']),'Same capsule cannot keep nominal service')
    old=F(1,p['nominal_instruction_rate_min']);own=old+F(1,64)
    need(suffix<old and own+2+delta<F(initial['initial']['remaining_drain_min']),'New private islands outlive formation drainage')
    need(not source['parameters']['raw_capture']['receiver_waits_for_raw_ready'],'A raw fault blocks nominal private progress')
    return dict(timer_strobe_interval=[earliest,latest],actual_suffix=suffix,parent_recharge=2*delta,
        fastest_nominal_cycle=F(1)/F(p['nominal_instruction_rate_max']),unchanged_instruction_tail=old,
        unchanged_own_read_tail=own,previous_hard_cycle_comparison_withdrawn=True,
        hard_launch_rate_is_upper_only=p['raw_instruction_launch_ceiling'],nominal_frame_and_age_supplier_preserved=True)

def energy_adapter(resource):
    p=resource['point'];t=resource['transit'];th=resource['thermal'];s=resource['supply']
    d=F(p['bank_rate']);b=F(t['bank_burst']);on=F(t['actual_Eon']);off=F(t['actual_Eoff']);T=F(p['per_bank_transit_capacity'])
    connected=on-b-F(20,41)*d
    need(connected>off and connected==F(t['connected_from_arbitrary_transit_lower']),'Old connected reserve was imported unchanged')
    need(off+T<on and 10*F(t['residual_input_power'])<on,'Historical low-E contact does not prevent rearm')
    need(F(p['upstream_usable_reserve_lower'])>1,'Full useful feed is assumed rather than funded')
    need(F(p['new_upstream_capacity'])-F(s['maximal_deficit'])==F(p['upstream_usable_reserve_lower']),'Reserve was counted twice')
    need(th['physical_zone_owner_cover']==41 and F(th['temperature_upper'])==2,'Physical thermal placement differs')
    need(F(th['resulting_side_effect_upper'])<F(1,50),'Actual heat side effect exceeds world budget')
    need(p['receiver']['ready_and_pending_stock_once']==12800*1024,'Capture reservation has another hidden copy')
    need(p['receiver']['additional_own_read_energy_stock']==0,'Own-read work was cloned by target')
    return dict(cold_start_bound=F(t['startup']),running_reserve_lower=connected,off_to_rearm_margin=on-off-T,
        no_launch_bound=t['no_new_launch_upper'],half_off_bound=t['half_off_upper'],upstream_reserve=F(p['upstream_usable_reserve_lower']),
        nonthermal_stock=F(p['total_nonthermal_inventory_upper']),temperature_upper=2,
        historical_low_E_implies_no_new_launch=True,E_alone_not_claimed_monotone=True,
        actual_outage_drawdown_lower=F(s['outage_drawdown_lower']),physical_placement_is_not_funding_ownership=True)

def initial_member(source,resource,geometry):
    m=source['mechanical'];tau=F(source['parameters']['mechanical']['tau'])
    phi=4*tau;q=258*tau;W=11*(abs(phi)+abs(q));H=11*(phi*phi+q*q)/(2*tau)
    need(W<F(m['W_hard']) and H<F(m['mechanical_hard_storage']),'Exhibited initialized load exceeds paid physical state')
    need(F(258,128)>1,'Running prohibited condition was removed')
    init=source['initial_relation']
    return dict(keeper_side=0,bay=0,active_phi_each=phi,active_q_each=q,active_H_total=H,active_W_total=W,
        cold_E_T_phi_q=0,world_coordinate=F(1,2),selected_world_tracker=F(3,5),maintenance_record=35184372221952,
        maintenance_force_store=0,thermal_coordinate=0,operating_energy=resource['transit']['actual_Emax'],
        transit_energy=resource['point']['per_bank_transit_capacity'],upstream_energy=resource['point']['new_upstream_capacity'],
        J_par=source['mechanical']['parameter_work_store_capacity'],pending_old_instruction=None,
        private_state='actual entry formation prefix; no arbitrary hidden completion',clock_offsets='independent arbitrary admissible offsets',
        inactive_C_and_raw_I='arbitrary within admitted bounded alphabet',initial_debt_D0=0)

def frozen_program(source):
    base=source['base_binding']['commit']
    pm=types.ModuleType('_assembly_pm');pm.__file__=str(HERE/'program_model.py');sys.modules[pm.__name__]=pm
    exec(compile(text_at(base,'program_model.py'),pm.__file__,'exec'),pm.__dict__)
    class Source:
        def read_text(self,**kwargs):return text_at(base,'program_source.py')
    pm.SOURCE=Source()
    gm=types.ModuleType('_assembly_gm');gm.__file__=str(HERE/'geometry_model.py');sys.modules[gm.__name__]=gm
    previous=sys.modules.get('program_model');sys.modules['program_model']=pm
    try:exec(compile(text_at(base,'geometry_model.py'),gm.__file__,'exec'),gm.__dict__)
    finally:
        if previous is None:sys.modules.pop('program_model',None)
        else:sys.modules['program_model']=previous
    c=pm.compile_check(gm.design());image=sha256(b''.join(x.to_bytes(24,'little') for x in c.image)).hexdigest()
    need(image==source['base_binding']['image_sha256'],'Assembly installed a different policy')
    return pm,c,image

def actual_policy_checks(source):
    pm,c,image=frozen_program(source);cases=[]
    for sumword,diffword,attack in ((1135,1135,0),(865,865,2000),(1001,1000,0)):
        m=pm.Machine(c);m.W=[0]*len(m.W);p=pm.RawPorts(c)
        for origin in range(c.constants['ORIGINS']):
            for bank in range(2):
                p.fast[(origin,bank,0)]=sumword if origin>=6 else attack
                p.fast[(origin,bank,1)]=diffword if origin>=6 else 2000-attack
        for key in range(3):p.fast[('head',key)]=1000
        m.enter('frame')
        while not any(e[0]=='world' for e in p.events) and m.steps<2000000:
            need(m.step(p),'Real frame blocked before WORLD')
        need(any(e[0]=='world' for e in p.events),'No real local feedback action')
        need(m.C==c.image,'Nominal local execution changed C')
        action=tuple(p.world_latch)
        x=(sumword+diffword-1000)//2;y=(sumword-diffword+1000)//2
        expected=tuple(max(30,min(90,60+(2*(z-500))//10)) for z in (x,y))
        need(action==expected,'Actual integer action disagrees with world adapter')
        cases.append(dict(rows=[sumword,diffword],six_bad_slot_value=attack,actual_world=action))
    return dict(image_sha256=image,actual_cases=cases,program_cells=source['base_binding']['actual_code_cells'],
        local_strategy_support=dict(kind='written local-interface and instruction-induction proof',
            location='PRIMARY-ASSEMBLY.md: An actual local policy lift; LOCAL-INDEXING gives the parameterized interface argument',
            conclusion='same permitted local history gives same action; no global-size runtime input',
            executable_scope='these frame cases check integer output semantics, not population independence'))

def token_and_recurrence_checks(source):
    # E(i,o) has distinct raw and execution projections. At i, its own output
    # origin is not an input group member; elsewhere only that output can reach.
    receivers=range(4);i=1;o=2;cases=0
    for r in receivers:
        slots=set()
        if r==i:slots.add(o)
        if r!=i:slots.add(i)
        need(len(slots)<=1,'Off-body token acquires two slots at one intact receiver')
        cases+=1
    e1=(1,2);e2=(1,3)
    need(len({e1,e2})==2 and len({e1[0],e2[0]})==1,'Token multiplicity contrast vanished')
    H=source['return_schedule']['conditional_return_H'];rate=F(source['return_schedule']['original_raw_acquisition_rate'])
    need(F(3,40*H)<=rate,'Rotating witness exceeds unchanged rate')
    starts=[40*H*k+a for k in range(4) for a in (0,250,600)]
    for l in range(len(starts)):
        for r in range(l,len(starts)):
            need(r-l+1<=math.floor(3+rate*(starts[r]-starts[l])),'Closed-endpoint cluster budget violated')
    episodes=[(a,a+500) for a in starts]
    endpoints=sorted({x for e in episodes for x in e})
    need(max(sum(a<=t<b for a,b in episodes) for t in endpoints)==2,'Witness lacks the required overlapping direct occupancy')
    need(600<F(source['return_schedule']['actual_pre_power_travel_lower']),'Third acquisition is no longer before new formed activation')
    return dict(typed_projection_cases=cases,host_deduplication_rejected=True,maximum_direct_occupancy=2,
        new_start_before_previous_return=600,cluster_spacing_lower=40*H,original_rate=rate,
        universal_count='three start streams separated by40H imply3+3L/(40H)<=3+lambda L',
        continuation_opportunity='derived recurring phase0, not a primitive successful scheduler')

def continuous_mode_checks(source):
    # In (S,Y), upper-store reaction is diagonal and its heat cancels in Y.
    cases=0
    for store in (F(0),F(1,2),F(3)):
        for incoming in (F(0),F(2),F(5)):
            for request in (F(0),F(1),F(7)):
                for theta in (F(0),F(1),F(2)):
                    exported=min(F(1),store)*request
                    dump=max(F(0),incoming-exported) if store==3 else F(0)
                    ds=incoming-exported-dump
                    bath=2*theta
                    dtheta=(dump-bath)/5
                    need(ds+5*dtheta==incoming-exported-bath,'Actual dump did not cancel in zoneY')
                    if store==0:need(ds>=0,'A lower reaction created fuel')
                    if theta==0:need(dtheta>=0,'Thermal coordinate became negative')
                    cases+=1
    m=source['parameters']['mechanical']
    # A held sign and nonnegative g make each active inverse coefficient
    # monotone until its first endpoint; requests, not hit events, can reverse it.
    hits=2*m['modules_per_host']
    need(hits==44,'Coefficient-bound event inventory changed')
    return dict(zone_energy_coordinate_cases=cases,physical_store_normals_are_not_world_projection=True,
        coefficient_bound_hits_per_host_per_held_interval=hits,
        coefficient_request_rate=source['parameters']['causal']['physical_request_rate'],
        coefficient_totality='held inverse rate times g(J), finite endpoint stops; no retained-state reset',
        arbitrary_raw_ready_cannot_block_private_clock=True,
        universal_scope='all admitted causal held updates and bounded measurable exogenous inputs, with retained unsuccessful outcomes')

def obstruction_checks():
    # Historical carrier-only low energy does not stay invariant with transit.
    d=F(1000);on=4*(d+1);off=2*on/3;T=d/2
    need(4*T-off/10>0 and off+T<on,'Retained-transit contrast vanished')
    inactive=on-1
    need(4*T-inactive/10>0,'Inactive-gate counterexample vanished')
    # An old pending destination remains different despite equal present code.
    pending=('old_body','STORE','x',1);fresh=('new_body','STORE','x',1)
    need(pending!=fresh,'Physical destination was quotiented by current C')
    R={'x':{'a','b'}};S={'a':{'safe'},'b':set()}
    composite=set().union(*(S[y] for y in R['x']))
    need(composite=={'safe'} and any(not S[y] for y in R['x']),'Blocked branch was hidden')
    return dict(low_E_can_rise=True,low_E_total_below_rearm=True,inactive_gate_is_not_low_E=True,
        old_pending_destination_retained=True,nonempty_safe_endpoints_do_not_prove_totality=True)

def encode(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x

def generate():
    s,r,i,g,receiver,c,b=inputs()
    return encode(dict(status='independently reviewed initialized source/policy adapter; full-contract audit and aggregate reproduction separate',
        bindings=b,world=world_adapter(s,i,g),force_and_return=force_deadline_adapter(s,i,g,c),
        energy=energy_adapter(r),timing=timing_adapter(s,g,i),initial_member=initial_member(s,r,g),actual_local_policy=actual_policy_checks(s),
        token_history=token_and_recurrence_checks(s),continuous_modes=continuous_mode_checks(s),counterexamples=obstruction_checks(),
        source_law_formation_is_not_achieved_repair=True,program_completion=False,
        sources={n:digest((HERE/n).read_text(encoding='utf-8-sig').replace('\r\n','\n')) for n in ('PRIMARY-ASSEMBLY.md','primary_assembly_model.py')}))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true');args=ap.parse_args()
    result=generate();path=HERE/'primary_assembly_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    if args.check:
        need(json.loads(path.read_text(encoding='utf-8-sig'))==result,'Primary assembly record differs')
        print('primary assembly record matches')
    if not args.write and not args.check:print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
