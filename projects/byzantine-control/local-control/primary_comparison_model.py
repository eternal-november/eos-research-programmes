"""Source-bound W5 comparisons; exact checks and actual frozen PROGRAM executions."""
from __future__ import annotations
import argparse,json,math,subprocess,sys,types
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
if sys.flags.optimize:raise RuntimeError('Unoptimized Python required')
HERE=Path(__file__).resolve().parent
PREFIX='theories-and-designs/byzantine-control/local-control/'
SOURCE='95f4a0938c689dcb9d1ff13af2d077d70a21bbf0'
RESOURCES='e666c823a55be7486888cb3b581722ec797d48e8'
ASSEMBLY='712112c12f350daf7ed2acfeda50c9753af79fc8'
def need(ok,message):
    if not ok:raise AssertionError(message)
def text_at(commit,name):
    return subprocess.check_output(['git','show',commit+':'+PREFIX+name],cwd=HERE).decode('utf-8-sig').replace('\r\n','\n')
def digest(text):return sha256(text.encode()).hexdigest()
def record_at(commit,name):
    text=text_at(commit,name);data=json.loads(text)
    for filename,expected in data['sources'].items():
        need(digest(text_at(commit,filename))==expected,'Frozen input mismatch: '+filename)
    return data,dict(commit=subprocess.check_output(['git','rev-parse',commit],cwd=HERE).decode().strip(),record=name,sha256=digest(text),sources=data['sources'])
def serial(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serial(v) for v in x]
    return x

def load_policy(base,expected):
    pm=types.ModuleType('_comparison_pm');pm.__file__=str(HERE/'program_model.py');sys.modules[pm.__name__]=pm
    exec(compile(text_at(base,'program_model.py'),pm.__file__,'exec'),pm.__dict__)
    class FrozenSource:
        def read_text(self,**kwargs):return text_at(base,'program_source.py')
    pm.SOURCE=FrozenSource()
    gm=types.ModuleType('_comparison_gm');gm.__file__=str(HERE/'geometry_model.py')
    previous=sys.modules.get('program_model');sys.modules['program_model']=pm
    try:exec(compile(text_at(base,'geometry_model.py'),gm.__file__,'exec'),gm.__dict__)
    finally:
        if previous is None:sys.modules.pop('program_model',None)
        else:sys.modules['program_model']=previous
    c=pm.compile_check(gm.design())
    image=sha256(b''.join(v.to_bytes(24,'little') for v in c.image)).hexdigest()
    need(image==expected,'Comparisons compiled a different policy')
    return pm,c,image

def point_checks(source,resource,assembly):
    p=source['parameters'];w=p['world'];m=w['fixed_regional_population'];M=w['raw_world_flow_bound'];b=6;physical=1
    weight=b+M*physical;tau=F(w['plant_time_per_hardware_quantum'])
    upper=F(84,100)*(1-F(b,m))-F(weight,m)
    lower=F(36,100)+F(weight,m)
    service=F(3,10)*(1-F(b,m))-F(weight,m)
    margins=(upper-F(6406,10000),F(5594,10000)-lower)
    need(min(margins)>0 and service>F(1,10),'Rebound IA1 positive region failed')
    need(margins[0]==F(assembly['world']['upper_inward_margin']) and margins[1]==F(assembly['world']['lower_inward_margin']), 'Assembly collar belongs to another source')
    need(service==F(assembly['world']['service_lower']),'Service map changed')
    # Reopen the complete source inequality; its exported2 is a rounded ceiling,
    # which by itself has no margin for a wider hostile inlet.
    source_derivative=F(61,100)+F(9,10)+F(weight,m)+3*F(2,100)*F(3,10)+F(w['independent_hostile_input_abs'])+F(w['side_effect_abs'])
    need(source_derivative<F(source['world']['protected_state_derivative_upper'])==2,
         'Complete source derivative does not refine its exported ceiling')
    hostile_family_derivative=source_derivative+margins[0]
    need(hostile_family_derivative<2 and margins[1]-margins[0]==F(84,100)*F(b,m),
         'Changed hostile capacity loses the row4, entry, or lower-collar supplier')
    need(F(m)/tau==F(assembly['world']['actual_world_capacity_per_coordinate']),'Physical plant scaling disappeared')
    H=source['return_schedule']['conditional_return_H'];H0=source['return_schedule']['previous_return_H'];rate=F(source['return_schedule']['original_raw_acquisition_rate'])
    need(H==assembly['force_and_return']['return_H'],'Comparisons use a different achieved-return bound')
    cover=1+2+math.floor(3+2*rate*H)
    need(cover==6 and rate*H<F(1,2),'Selected source lost its original raw rate')
    thresholds=0
    for raw_product in (F(0),F(1,10),F(499,1000),F(1,2),F(501,1000),F(2)):
        need((1+2+math.floor(3+2*raw_product)<=6)==(raw_product<F(1,2)),'Strict cover boundary differs')
        thresholds+=1
    return dict(m=m,M=M,typed_adverse_weight=weight,old_replacement_underestimate=F(1,m),upper_margin=margins[0],lower_margin=margins[1],service_lower=service,
        fixed_collar_hostile_capacity_threshold=F(1,100)+margins[0],
        base_complete_world_derivative=source_derivative,positive_hostile_family_derivative_upper=hostile_family_derivative,
        unchanged_row4_and_entry_supplier=True,world_capacity=F(m)/tau,
        selected_H=H,previous_H=H0,H_ratio=F(H,H0),unchanged_raw_rate=rate,lambda_H=rate*H,whole_attempt_cover=cover,
        exact_threshold_cases=thresholds,resource_D=resource['point']['upstream_rate'],resource_U=resource['point']['new_upstream_capacity'],resource_stock=resource['point']['total_nonthermal_inventory_upper'],
        optional_electrical_H_not_substituted=True,failed_certificate_not_universal_impossibility=True)

def actual_policy_checks(pm,c,source,assembly):
    k=c.constants;world=[]
    for rows in ((998,1000),(1002,1000)):
        m=pm.Machine(c);m.W=[0]*len(m.W);ports=pm.RawPorts(c)
        for origin in range(k['ORIGINS']):
            for bank in range(2):
                ports.fast[(origin,bank,0)]=rows[0];ports.fast[(origin,bank,1)]=rows[1]
        for key in range(3):ports.fast[('head',key)]=1000
        m.enter('frame')
        while not any(e[0]=='world' for e in ports.events) and m.steps<2000000:need(m.step(ports),'Stored frame stopped before WORLD')
        need(any(e[0]=='world' for e in ports.events) and m.C==c.image,'WORLD witness changed code or did not execute')
        world.append(dict(rows=rows,actual_world=ports.world_latch,instructions=m.steps))
    need([x['actual_world'] for x in world]==[(59,59),(60,60)],'Actual local disagreement disappeared')
    m=pm.Machine(c);m.W=[0]*len(m.W);ports=pm.RawPorts(c)
    for key in range(3):ports.fast[('head',key)]=1200
    m.enter('frame')
    while not any(e[0]=='world' for e in ports.events) and m.steps<2000000:need(m.step(ports),'Missing-data frame blocked')
    need(ports.world_latch==(60,60),'Actual unavailable-row fallback changed')
    fallback=ports.world_latch
    # Both physical provider neighborhoods fit the SAME region and share no head.
    offsets=list(range(-20,0))+list(range(1,21));a,b=40,140
    left={a+x for x in offsets};right={b+x for x in offsets}
    need(not left&right and min(left|right)>=0 and max(left|right)<source['parameters']['world']['fixed_regional_population'],'Disagreement assigned contradictory readings to a shared physical head')
    tau=F(source['parameters']['world']['plant_time_per_hardware_quantum']);window=5000
    row_drift=4*tau*window;sum_error=F(2,1000)+row_drift
    need(sum_error<F(5,1000) and row_drift<F(5,1000),'Displayed rows cannot arise from actual source heads')
    need(F(assembly['world']['command_age'])<window,'Receipt/effect age leaves the physical witness window')
    initial=json.loads(text_at(source['base_binding']['commit'],'initial_return_results.json'))['initial']
    need(F(initial['first_genuine_plant_upper'])<window,'First real source data arrives after witness window')
    # The same literal permission routine, with truthful full clearance.
    load_key=3+k['VIEW_WORDS'];guard=[]
    for words in ([125]*13,[1100]*13,[0]*7+[1100]*6):
        m=pm.Machine(c,poison=0);ports=pm.RawPorts(c)
        for origin,word in enumerate(words):
            ports.fast[(origin,0,load_key)]=word;ports.fast[(origin,0,load_key+2)]=0
        m.enter('permission',(k['TARGET_BASE'],0));need(m.run(ports,until_yield=False)=='halt','Permission routine did not complete')
        need(m.C==c.image,'Input-only comparison modified execution code');guard.append(m.result())
    need(guard==[1,0,1],'Factual guard or wide-input counterexample changed')
    # A design-level rival guard is initialized before execution, not installed
    # by an intrusion or called faulty because its choice violates the rule.
    rival=pm.Machine(c);rp=pm.RawPorts(c)
    rival.C[:2]=[pm.encode(pm.LI,2,immediate=1),pm.encode(pm.HALT)];rival.PC=0
    rival_reference=list(rival.C)
    need(rival.run(rp,until_yield=False)=='halt' and rival.result()==1 and not rival.faults and rival.C==rival_reference,
         'Always-permit rival was not faithfully realized by an ordinary finite branch')
    factual_permissions=[load<=1 and F(1)>=F(4,5) for load in (F(1,8),F(11,10))]
    rival_verdicts=[rival.result(),rival.result()]
    rival_violations=[bool(action and not permitted) for action,permitted in zip(rival_verdicts,factual_permissions)]
    need(factual_permissions==[True,False] and rival_violations==[False,True],
         'The rival comparison changed the factual rule or lost the high-load violation')
    need(not any(action and not permitted for action,permitted in zip(guard[:2],factual_permissions)),
         'Literal P violated the same fixed rule in the compared opportunities')
    # One enabled private candidate write, unlike the old external threshold bit.
    target_ordinal=0;source_bank=0;producer_host=140;address=100;requested=7
    actual_owner_map={t:2*offsets.index(-offsets[t])+source_bank for t in range(len(offsets))}
    reverse_ordinal=offsets.index(-offsets[target_ordinal])
    target_host=producer_host+offsets[target_ordinal]
    owner=actual_owner_map[target_ordinal];foreign=2*reverse_ordinal+1-source_bank
    need(target_host+offsets[reverse_ordinal]==producer_host and owner==78 and foreign==79,
         'Private write fixture does not bind the actual reverse-neighbor lead')
    need(set(actual_owner_map.values())==set(range(source_bank,k['BAYS'],2)),
         'One source bank aliases or omits a physically owned candidate')
    direct=pm.Machine(c);dp=pm.RawPorts(c);dp.own_bays=actual_owner_map
    dp.target_cells[(target_ordinal,0,owner,address)]=0;dp.target_cells[(target_ordinal,0,foreign,address)]=19
    direct.C[:6]=[pm.encode(pm.LI,3,immediate=target_ordinal),pm.encode(pm.LI,4,immediate=0),
        pm.encode(pm.LI,5,immediate=address),pm.encode(pm.LI,6,immediate=requested),
        pm.encode(pm.IO,7,3,4,pm.PRIM['write_own']),pm.encode(pm.HALT)]
    direct.PC=0;need(direct.run(dp,until_yield=False)=='halt','Actual ordinary candidate write did not execute')
    need(dp.target_cells[(target_ordinal,0,owner,address)]==requested and dp.target_cells[(target_ordinal,0,foreign,address)]==19,
         'Private write was thresholded or aliased a foreign candidate')
    need(F(2)+F(1,4)<F(21,2),'Old external single-writer threshold comparison changed')
    # Both old and new sources separately allow retained internal self-writing.
    m=pm.Machine(c);ports=pm.RawPorts(c)
    m.C[:4]=[pm.encode(pm.LI,3,immediate=0),pm.encode(pm.LI,4,immediate=100),pm.encode(pm.STOREC,3,4),pm.encode(pm.HALT)]
    old=m.C[100];m.PC=0
    need(m.run(ports,until_yield=False)=='halt' and m.C[100]==0 and m.code_writes==1,'Ordinary retained self-write was not realized')
    return dict(differing_world_commands=world,actual_missing_data_fallback=fallback,missing_row_case_keeps_local_raw_heads=True,physical_consumers=[a,b],disjoint_actual_provider_sets=True,
        physical_prefix_quanta=window,max_row_variation=row_drift,sum_head_error_needed=sum_error,difference_head_error_needed=row_drift,
        actual_command_age=assembly['world']['command_age'],first_genuine_plant_upper=initial['first_genuine_plant_upper'],
        permission_low_high_and_seven_slot_verdicts=guard,
        fixed_rule_policy_rival=dict(always_permit_verdicts=rival_verdicts,factual_permissions=factual_permissions,
            rival_violations=rival_violations,chosen_action='issue physically available positive cut when verdict1',
            initialized_policy_choice_not_runtime_fault=True,matching_initial_code_reference_retained=True,whole_rival_recurrence_claimed=False),
        truthful_loads=[F(1,8),F(11,10)],truthful_clearance=1,
        seven_slot_case_scope='larger raw-input footprint; mechanism failure, not universal policy impossibility',
        ordinary_candidate_write=dict(producer_host=producer_host,target_host=target_host,target_ordinal=target_ordinal,
            reverse_neighbor_ordinal=reverse_ordinal,source_bank=source_bank,owner=owner,foreign=foreign,
            owner_by_target_ordinal=[actual_owner_map[t] for t in range(len(offsets))],address=address,before=0,after=requested,foreign_unchanged=19,
            old_single_external_field_upper=F(9,4),old_external_write_threshold=F(21,2)),
        retained_self_write=dict(address=100,before=old,after=0,actual_writes=m.code_writes),
        no_agreement_imported=True,physical_witness_needs_maintained_receipt_supplier=True)

def timing_and_restriction_checks(source,assembly):
    p=source['parameters'];delta=F(p['raw_capture']['recharge_delta']);e=p['execution']
    raw=F(source['capture_work']['raw_good_capture_upper']);earliest7=F(6,e['private_capture_timer_tick_max'])
    need(earliest7<raw,'Independent-phase seven-edge certificate obstruction disappeared')
    lower=F(7,e['private_capture_timer_tick_max']);upper=F(8)/F(e['private_capture_timer_tick_min'])
    need(lower>=raw and [str(lower),str(upper)]==assembly['timing']['timer_strobe_interval'],'Selected timer does not realize the comparison')
    suffix=F(source['capture_work']['actual_private_suffix']);cycle=F(source['capture_work']['private_cycle_through_recharge'])
    nominal=F(1)/F(e['nominal_instruction_rate_max'])
    need(suffix<nominal*F(3,4) and cycle<nominal,'Nominal-service transport failed')
    need(suffix>6*delta and cycle>8*delta,'Superseded hard-cycle comparison was accidentally credited')
    # Same real event convention: separated/finite-total histories remain subsets.
    H=source['return_schedule']['conditional_return_H'];rate=F(source['return_schedule']['original_raw_acquisition_rate'])
    starts=[40*H*k+j for k in range(4) for j in (0,250,600)]
    intervals=0
    for i,a in enumerate(starts):
        for j in range(i,len(starts)):
            need(j-i+1<=math.floor(3+rate*(starts[j]-a)),'Cluster restriction broke the unchanged arrival envelope');intervals+=1
    events=sorted([(t,1,h) for h,t in enumerate(starts)]+[(t+500,0,h) for h,t in enumerate(starts)])
    held=set();peak=0
    for _,kind,h in events:
        if kind:held.add(h)
        else:held.remove(h)
        peak=max(peak,len(held))
    need(peak==2 and 600<F(source['return_schedule']['actual_pre_power_travel_lower']),'Overlap is only a label or cleanup tail')
    return dict(seven_edge_earliest=earliest7,seven_edge_result_mode='certificate obstruction; summed upper delays not proved jointly attained',raw_good_capture_upper=raw,eight_edge_interval=[lower,upper],actual_private_suffix=suffix,actual_parent_cycle=cycle,
        nominal_cycle=nominal,old_hard_cycle_comparisons_withdrawn=True,finite_cluster_interval_cases=intervals,actual_peak_direct_occupancy=peak,
        source_maps=['aligned timing is scenario restriction','finite-total and separated acquisitions are scenario restrictions','shared-mode source has actual maintained information supplier'],
        finite_tests_not_infinite_rotation_proof=True,infinite_rotation_supplier='PRIMARY-ASSEMBLY causal40H-separated clusters and finite-roster revisit')

def supply_and_health_checks(source,resource):
    D=F(resource['point']['upstream_rate']);standing=F(resource['supply']['selected_raw_record_holding_work'])
    constant=F(4,3)*D
    def supplied(t):
        periods=t//6;phase=t-6*periods
        return periods*8*D+2*D*max(F(0),phase-2)
    need(supplied(F(6))/6==constant,'Compared supply averages differ')
    cases=0
    for a in (F(0),F(1,3),F(2),F(5),F(6),F(25,3)):
        for length in (F(0),F(1,2),F(2),F(3),F(6),F(15)):
            bound=D*max(F(0),length-2)
            need(supplied(a+length)-supplied(a)>=bound and constant*length>=bound,'Supply coordinate no longer refines the same reserve interface');cases+=1
    need(standing>0 and F(resource['supply']['outage_drawdown_lower'])==2*standing,'Outage comparison lacks actual drawdown')
    # Conservation is independent of how the complete finite boundary is partitioned.
    health_cases=0
    for flows in product((F(-2),F(0),F(1),F(3)),repeat=4):
        need(sum(abs(x) for x in flows)>=sum(flows),'Cancelling/remapped flow escaped the wear bound');health_cases+=1
    algebra_cases=0
    m=source['parameters']['world']['fixed_regional_population'];tau=F(source['parameters']['world']['plant_time_per_hardware_quantum']);s=F(1,10)
    for R,H0,epsilon in product((6,9),(F(1),F(1000000)),(F(1,100),F(1))):
        rate=2*R*m*epsilon*s;T=H0/rate
        need(rate*T==H0 and tau*T>0,'Source service/health time conversion failed');algebra_cases+=1
    return dict(constant_supply=constant,interrupted_on_supply=2*D,outage_quanta=2,period_quanta=6,same_average=True,supply_interval_cases=cases,
        actual_outage_drawdown_lower=2*standing,shared_D=resource['point']['upstream_rate'],shared_U=resource['point']['new_upstream_capacity'],
        health_flow_triangle_cases=health_cases,health_source_unit_cases=algebra_cases,
        complete_actual_WORLD_boundary_required=True,nominal_four_tracker_count_not_a_complete_wear_inventory=True,
        health_hardware_endurance='H_health/(2*R*m*epsilon*s)',health_physical_endurance='tau_plant*H_health/(2*R*m*epsilon*s)',
        useful_replenishment_necessary='H_health+R_useful(T)>=2*R*m*epsilon*s*T',raw_material_not_useful_preparation=True,
        health_comparison_scope='finite-health source variant with nonempty unavailable continuations; not an indefinite wearing-source construction')

def negative_capacity_checks(source):
    tau=F(source['parameters']['world']['plant_time_per_hardware_quantum'])
    drift=F(61,100)+F(1,2)-1-F(18,1000)-F(2,100)
    need(drift==F(9,125),'External-capacity obstruction changed')
    exit_time=F(5,100)/drift
    need(exit_time==F(25,36),'Wrong source-valid capacity deadline')
    return dict(no_internal_target_write_on_either_side=True,larger_hostile_capacity=F(1,2),larger_hostile_hardware_flow_capacity=F(source['parameters']['world']['fixed_regional_population'],2),
        larger_hostile_protected_prefix_work_rating=F(65,100)*F(source['parameters']['world']['fixed_regional_population'],2),
        all_defenders_granted_full_unit_output=True,
        unavoidable_plant_time_drift=drift,plant_time_exit_upper=exit_time,hardware_time_exit_upper=exit_time/tau,
        unchanged_P_blind_fallback_exit_plant_time=5,blind_fallback_exit_hardware_time=F(5)/tau,
        capacity_obstruction_is_all_policy=True,missing_information_failure_is_selected_policy=True,
        all_peer_write_exhaustion_requires_cofinal_exposure_and_no_other_preparation=True)

def generate():
    s,sb=record_at(SOURCE,'port_source_results.json');r,rb=record_at(RESOURCES,'port_resource_results.json');a,ab=record_at(ASSEMBLY,'primary_assembly_results.json')
    need(r['bindings']['source']['commit']==SOURCE and a['bindings']['source']['commit']==SOURCE,'Source identities differ across compared components')
    need(a['bindings']['resources']['commit']==RESOURCES,'Assembly consumes another bill')
    pm,c,image=load_policy(s['base_binding']['commit'],s['base_binding']['image_sha256'])
    files=('PRIMARY-COMPARISONS.md','primary_comparison_model.py')
    return serial(dict(status='independently reviewed source-preserving comparisons; full-contract audit and aggregate reproduction separate',bindings=dict(source=sb,resources=rb,assembly=ab),
        actual_policy_image=image,current_point=point_checks(s,r,a),actual_policy=actual_policy_checks(pm,c,s,a),
        timing_history=timing_and_restriction_checks(s,a),supply_health=supply_and_health_checks(s,r),negative_boundaries=negative_capacity_checks(s),
        program_completion=False,source_admission_not_created_by_comparisons=True,
        sources={name:digest((HERE/name).read_text(encoding='utf-8-sig').replace('\r\n','\n')) for name in files}))
def main():
    p=argparse.ArgumentParser();g=p.add_mutually_exclusive_group(required=True);g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');args=p.parse_args()
    result=generate();path=HERE/'primary_comparison_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    else:need(json.loads(path.read_text(encoding='utf-8'))==result,'Comparison record differs')
    print('primary comparison record '+('written' if args.write else 'matches'))
if __name__=='__main__':main()
