"""One source-bound work, reserve and retained-storage account for source B.

The source and primitive-core inputs are immutable Git records. This checks
their typed quantitative join; it is not the full program completion audit.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')
HERE=Path(__file__).resolve().parent
PREFIX='theories-and-designs/byzantine-control/local-control/'
SOURCE='95f4a0938c689dcb9d1ff13af2d077d70a21bbf0'

def need(ok,message):
    if not ok: raise AssertionError(message)

def text_at(commit,name):
    return subprocess.check_output(['git','show',commit+':'+PREFIX+name],cwd=HERE).decode('utf-8-sig').replace('\r\n','\n')

def digest_text(text):
    return sha256(text.encode('utf-8')).hexdigest()

def record_at(commit,name):
    raw=text_at(commit,name);record=json.loads(raw)
    for source,expected in record['sources'].items():
        need(digest_text(text_at(commit,source))==expected,'Frozen record mismatch: '+source)
    return record,dict(commit=commit,record=name,sha256=digest_text(raw),sources=record['sources'])

def source_inputs():
    source,binding=record_at(SOURCE,'port_source_results.json')
    base=source['base_binding']['commit']
    for name,digest in source['base_binding']['sources'].items():
        need(digest_text(text_at(base,name))==digest,'Source/core binding mismatch: '+name)
    core,core_binding=record_at(base,'resource_results.json')
    ports,ports_binding=record_at(base,'port_results.json')
    return source,core['runtime_inventory'],ports['bounds'],dict(source=binding,core=core_binding,ports=ports_binding)

def core_identities(core,ports):
    db=F(core['per_bank_rate']);b=F(core['per_bank_burst'])
    need(db==F(core['per_bank_recharge_peak'])+F(core['generator_power'])/2+F(core['leakage_power'])/2,
         'Frozen bank demand identity changed')
    rows=core['per_bank_external_rows']
    external_bank=sum(F(row['count'])*F(row['price'])*F(row['rate']) for row in rows)
    external=2*external_bank+F(core['background_power'])+F(core['leakage_power'])
    need(external==F(core['external_rate']),'Frozen external-rate identity changed')
    old_bulk=F(core['total_upstream_charger_input'])
    need(old_bulk==8*db,'Old two-bank bulk allowance is not8d')
    need(F(core['upstream_rate'])==old_bulk+external,'Frozen upstream bill does not assemble')
    old_nonU=2*F(core['per_bank_capacity'])+F(core['combined_capsule_field_capacity'])+F(core['transducer_capacity'])
    need(F(core['total_stored_capacity'])==F(core['upstream_capacity'])+old_nonU,
         'Old upstream reserve was hidden or duplicated in stock')
    need(F(core['combined_capsule_field_capacity'])==F(ports['capsule_energy_capacity'])+F(ports['data_field_energy_capacity']),
         'In-flight fields were removed from retained work')
    return dict(bank_rate=db,bank_burst=b,retained_external_rate=external,
                replaced_bulk_allowance=old_bulk,retained_nonU_stock=old_nonU,
                retained_core_scope='finite instruction/slot/array work and the conservative field allocation; no electrical rail/thermal realization is imported')

def receiver_account(source,core,ports):
    p=source['parameters'];r=p['raw_capture'];e=p['execution']
    count=r['autonomous_cells_per_host'];cell=r['ready_plus_pending_capacity_per_cell']
    delta=F(r['recharge_delta']);eta=F(r['charger_efficiency_min'])
    need(count==2*p['bays_per_side']*2*p['degree']==12800,'Raw capture multiplicity changed')
    need(r['own_read_latches_per_host']==2*p['bays_per_side']*p['degree']==6400,'Own-read snapshots changed')
    need(r['own_read_source_capsules_per_host']==ports['installed_slots']['own_read']==160,
         'Own-read capsule was cloned by destination')
    need(cell==r['capture_work']==1024,'Ready/pending capacity does not fund one capture')
    output=F(r['charger_output_capacity']);upstream=F(r['charger_input_capacity'])
    need(output*delta>=cell and eta*upstream>=output,'Actual refill misses delta')
    new_stock=count*cell
    new_rate=count*upstream
    need(new_stock==source['capture_work']['new_capture_capacity'],'Source stock export differs')
    need(new_rate==F(source['capture_work']['upstream_peak']),'Source upstream export differs')
    snapshot=r['raw_snapshot_latches_per_host']*r['raw_snapshot_bits']
    metadata=count*r['raw_metadata_bits_per_cell']
    padding=(2048-976)*2*core['selected_records_per_bank']
    need(snapshot+metadata<=padding,'Raw capture/control state lacks paid storage')
    extra_private=8*(2*p['degree']+1)
    need(source['base_binding']['existing_private_words']+extra_private<=core['padded_private_words'],
         'Private operation state lacks paid storage')
    capsule=e['per_instruction_capsule_energy']
    generic=e['native_instruction_work_upper']+e['local_admission_driver_work_upper']
    private=e['private_io_boundary_work_upper']+e['private_boundary_link_energy']+e['private_reset_work_upper']
    need(generic<=capsule and private<=capsule,'Instruction reservation cannot fund its actual operation class')
    need(r['own_read_capture_part']<=r['own_read_capsule_work'],'Own read consumes an unallocated second capsule')
    # Actual microcase, not the16384-step generic path with I/O appended.
    actual=F(source['capture_work']['actual_private_suffix'])
    nominal_period=1/F(e['nominal_instruction_rate_max'])
    nominal_budget=F(3,4)*nominal_period
    need(actual<nominal_budget,'Private suffix cannot support the actual nominal instruction service')
    need(nominal_budget==F(source['capture_work']['reserved_private_suffix']),
         'Source and resource use different nominal execution budgets')
    need(actual+delta<8*delta,'Raw refill misses the next hard launch opportunity')
    timer_lo=F(source['capture_work']['receiver_private_strobe_lower'])
    timer_hi=F(source['capture_work']['receiver_private_strobe_deadline'])
    raw_good=F(source['capture_work']['raw_good_capture_upper'])
    edges=e['private_capture_timer_edges']
    need(timer_lo==F(edges-1)/F(e['private_capture_timer_tick_max']) and
         timer_hi==F(edges)/F(e['private_capture_timer_tick_min']) and timer_lo>raw_good,
         'An independent-phase private timer can read before nominal raw completion')
    need(e['private_capture_timer_control_steps']+e['private_other_control_error_work_upper']==256,
         'Private timer adds unpriced control work')
    need(not r['receiver_waits_for_raw_ready'] and source['capture_work']['raw_ready_not_a_private_wait_guard'],
         'One failed raw origin can block an intact receiver')
    need(source['hard_stores']['smooth_empty_throttle_not_used_for_funded_deadlines'],
         'Exact funded work is incorrectly subjected to asymptotic empty-store throttling')
    need(source['capture_work']['reset_complete_before_parent_release'],
         'Parent can be reused before its funded reset ends')
    parent_recharge=F(source['capture_work']['parent_recharge_time'])
    need(actual+parent_recharge<nominal_period and parent_recharge==2*delta,
         'Parent completion/reset/recharge cycle exceeds the actual nominal instruction interval')
    return dict(capture_cells=count,ready_and_pending_stock_once=new_stock,
        raw_charger_upstream_rate=new_rate,raw_charger_local_output_rate=count*output,
        raw_charger_efficiency_floor=eta,capture_refill=delta,
        own_read_snapshot_latches=r['own_read_latches_per_host'],existing_own_read_capsules=160,
        additional_own_read_energy_stock=0,raw_snapshot_bits=snapshot,new_control_bits=metadata,
        consumed_raw_padding=snapshot+metadata,available_raw_padding=padding,
        additional_background_bits=0,extra_private_words_per_cartridge=extra_private,
        instruction_capacity=capsule,generic_ISA_work_envelope=generic,
        private_IO_link_reset_upper=private,private_unallocated_budget_lower=capsule-private,
        private_parent_cycle=actual+parent_recharge,
        nominal_private_suffix_budget=nominal_budget,fastest_nominal_period=nominal_period,
        private_strobe_interval=[timer_lo,timer_hi],nominal_raw_capture_upper=raw_good,
        independent_phase_timer_steps=edges,failed_raw_ready_cannot_block_private_completion=True,
        hard_rate_is_launch_ceiling_not_per_opcode_service=True,
        unallocated_budget_is_not_another_store=True,parent_retained_through_reset_and_settlement=True,
        own_read_wait_is_separate=True,source_origin_funding_preserved=True)

def mechanical_account(source):
    p=source['parameters'];m=source['mechanical'];mp=p['mechanical'];gap=p['clearance']
    delivered=F(m['hard_mechanical_absolute_port_power'])
    upstream=F(m['hard_mechanical_upstream_work_ceiling'])
    need(upstream==delivered/F(mp['work_converter_efficiency_min']),
         'Mechanical delivered work was mistaken for upstream work')
    parameter=F(m['parameter_recharge_delivered_rate'])
    parameter_up=F(m['parameter_recharge_upstream_ceiling'])
    need(parameter_up>=parameter and parameter==F(m['continuous_parameter_work_rate']),
         'Parameter work/refill meanings differ')
    gap_delivered=F(gap['elastic_residual_power_per_host']);gap_up=F(gap['gap_upstream_power_per_host'])
    need(gap_up==gap_delivered/F(gap['gap_work_converter_efficiency_min']),
         'Gap actuator conversion was omitted')
    return dict(mechanical_state_capacity=F(m['mechanical_hard_storage']),
        parameter_store_capacity=F(m['parameter_work_store_capacity']),
        gap_state_capacity=F(gap['elastic_residual_storage_per_host']),
        mechanical_delivered_absolute_work_upper=delivered,mechanical_upstream_upper=upstream,
        parameter_delivered_recharge=parameter,parameter_upstream_upper=parameter_up,
        gap_delivered_work_upper=gap_delivered,gap_upstream_upper=gap_up,
        added_upstream_rate=upstream+parameter_up+gap_up,
        parameter_to_mechanics_is_internal=True,dissipation_is_not_billed_again=True,
        negative_mechanical_work_returns_to='U or heat; no direct old E/T route')

def operating_point(source,core,ports):
    c=core_identities(core,ports);r=receiver_account(source,core,ports);m=mechanical_account(source)
    p=source['parameters'];bulk=p['bulk_work'];db=c['bank_rate'];b=F(core['upstream_burst'])
    transit_input=F(bulk['transit_input_multiple_of_bank_rate'])*db
    transit_source=transit_input/F(bulk['upstream_efficiency_min'])
    need(transit_source==F(bulk['upstream_draw_multiple_of_bank_rate'])*db,'Bulk conversion cost mismatch')
    new_bulk=2*transit_source
    D=c['retained_external_rate']+new_bulk+r['raw_charger_upstream_rate']+m['added_upstream_rate']
    need(D==F(core['upstream_rate'])-c['replaced_bulk_allowance']+new_bulk+r['raw_charger_upstream_rate']+m['added_upstream_rate'],
         'Old and new bulk paths were both billed')
    # Same continuous-reservoir doctrine as RESOURCES, with actual overflow.
    latency=F(2);margin=D+b;Ucap=b+latency*D+margin
    need(margin>bulk['upstream_full_delivery_energy_threshold'],'No positive full-delivery reserve')
    Tcap=F(bulk['transit_capacity_multiple_of_bank_rate'])*db
    stock=c['retained_nonU_stock']+Ucap+2*Tcap+r['ready_and_pending_stock_once']
    stock+=m['mechanical_state_capacity']+m['parameter_store_capacity']+m['gap_state_capacity']
    memory=p['memory']
    need(memory['stable_word_recoverable_work']==0,'A finer memory-energy model needs an actual added store')
    need(stock>F(core['total_stored_capacity']) and stock<2**66,'Unexpected complete source stock range')
    return dict(core=c,receiver=r,mechanics=m,bank_rate=db,upstream_rate=D,upstream_burst=b,
        old_bulk_rate_removed=c['replaced_bulk_allowance'],new_two_bank_bulk_rate=new_bulk,
        old_upstream_capacity_removed=F(core['upstream_capacity']),new_upstream_capacity=Ucap,
        upstream_latency=latency,upstream_usable_reserve_lower=margin,
        full_delivery_scope='physically intact funding/charge boundary; arbitrary code/input requests within actual installed rate limits',
        failed_boundary_lower_reserve_not_claimed=True,
        per_bank_transit_capacity=Tcap,total_nonthermal_inventory_upper=stock,
        existing_field_storage_counted_once=F(core['transducer_capacity']),
        field_allocation_is_upper_bound_not_added_generators=True,
        source_low_energy_request_scaling=p['bulk_work']['source_energy_enable'])

def thermal_checks(point,core,ports,source):
    p=source['parameters'];boundary=p['material_boundary'];degree=p['degree']
    # Fixed physical placement, not a multiplication of usable reserves.
    owner_cover=p['placement']['body_zone_host_bag_cover']
    need(owner_cover==degree+1 and p['placement']['fixed_installed_store_locations'],
         'Physical placement does not supply the host-bag cover')
    need(p['placement']['endpoint_zone_host_bag_cover']<=owner_cover,
         'Endpoint stores escape the material-zone cover')
    need(p['hard_work_store']['all_mode_intrinsic'] and
         source['hard_stores']['all_mode_capacity_not_from_nominal_charger'],
         'Nominal charging was used as an all-mode hard stock bound')
    Czone=owner_cover*point['total_nonthermal_inventory_upper']
    Pin=F(boundary['positive_external_energy_input'])
    need(Pin==F(boundary['total_nonbath_absolute_work']), 'Wrong physical boundary orientation')
    need(F(boundary['world_absolute_work'])+F(boundary['other_nonbath_absolute_work'])==Pin,
         'WORLD and other external work were not jointly retained')
    # A deliberately loose peak check for the selected primitive profiles.
    # Positive-cost operations use their rated native/control clocks; reset
    # dumps and coefficient jumps are internal energy transfers, not inlets.
    endpoint_peak=2*sum(F(row['count'])*F(row['price'])*F(p['execution']['raw_background_cell_clock_ceiling'])
                        for row in core['per_bank_external_rows'])
    native_peak=F(p['execution']['private_native_work_rate_capacity'])*p['execution']['processors_per_host']
    mechanical_loss=F(p['mechanical']['R_max'])*(F(source['mechanical']['W_hard'])/F(p['mechanical']['tau']))**2
    primitive_peak=(F(core['all_capsule_recharge_peak'])+F(core['background_power'])+
                    F(core['leakage_power'])+F(core['generator_power'])+F(core['portal_power'])+
                    endpoint_peak+native_peak+point['receiver']['raw_charger_upstream_rate']+
                    point['new_two_bank_bulk_rate']+point['mechanics']['added_upstream_rate']+mechanical_loss)
    profile=owner_cover*(2*point['upstream_rate']+4*primitive_peak)
    need(profile<Pin,'Known primitive profiles do not fit the chosen raw boundary rating')
    k=Pin;Ctheta=Czone
    init=p['initialization']
    theta0_lo=F(init['thermal_theta_min']);theta0_hi=F(init['thermal_theta_max'])
    need(0==theta0_lo<=F(init['concrete_thermal_theta'])<=theta0_hi==1,
         'Actual initial thermal state does not support the combined-energy bound')
    need(source['hard_stores']['external_transfers_are_finite_rate_ports'],
         'Positive external energy impulses require a burst-aware thermal bound')
    faces=0
    for share in (F(0),F(1,4),F(1,2),F(3,4),F(1)):
        E=share*Czone;theta=(2*Czone-E)/Ctheta
        need(theta>=1 and Pin-k*theta<=0,'Combined energy/temperature face is not inward')
        for move in (F(0),E/2,E):
            need((E-move)+Ctheta*(theta+move/Ctheta)==2*Czone,
                 'Internal dissipation created total energy')
            faces+=1
    thermal_row=F(p['thermal_coupling']['complete_row_l1_max'])
    mechanical_row=F(p['thermal_coupling']['mechanical_row_l1_max'])
    mechanical_feature=F(p['thermal_coupling']['normalized_mechanical_feature_abs_max'])
    side_effect=2*thermal_row+mechanical_row*mechanical_feature
    need(side_effect<F(source['parameters']['world']['side_effect_abs']),
         'Actual thermal/mechanical coupling exceeds the world allowance')
    return dict(physical_zone_owner_cover=owner_cover,
        placement='body/receiver zones use their own and direct-neighbor bags; E, own-read and propagation zones use endpoint bags',
        physical_zone_nonthermal_upper=Czone,thermal_capacity=Ctheta,
        raw_positive_nonbath_input_upper=Pin,passive_bath_coefficient=k,
        nominal_primitive_peak_fit_upper=profile,initial_temperature_upper=theta0_hi,temperature_lower=theta0_lo,
        combined_energy_upper=2*Czone,temperature_upper=2,
        complete_gross_with_bath_upper=Pin+2*k,checked_energy_faces=faces,
        thermal_complete_row_l1=thermal_row,mechanical_complete_row_l1=mechanical_row,
        normalized_mechanical_feature_upper=mechanical_feature,resulting_side_effect_upper=side_effect,
        global_comparison='Ydot<=2P−(P/C_zone)Y; local jumps conserve or decrease Y',
        internal_heat_to_work_transfers_cancel=True,
        source_material_bound_is_not_nominal_demand=True,
        capacity_bound_is_not_duplicated_funding=True)

def transit_checks(point,core,source):
    db=point['bank_rate'];b=F(core['per_bank_burst']);Tcap=point['per_bank_transit_capacity']
    on=F(core['per_bank_on']);off=F(core['per_bank_off']);emax=F(core['per_bank_capacity'])
    rho=F(core['per_bank_residual_backfeed']);k=F(1,10)
    a=F(source['parameters']['bulk_work']['output_rate_coefficient'])
    need(a==4 and (a+k)*Tcap==F(41,20)*db,'Transit equilibrium differs')
    # Integral of4T from empty is >=2d*t−20d/41. Until Eon no spill.
    startup=F(6);lower=db*startup-F(20,41)*db-b
    need(lower>on,'Six-quantum cold prefix does not reach actual Eon')
    forming_deficit=F(20,41)*db
    connected_lower=on-b-forming_deficit
    need(connected_lower>off,'Still-forming transit cannot maintain the operating reserve')
    need(emax+Tcap<4*off and rho<=k*off/4,'40/60q total-energy drainage no longer holds')
    need(off+Tcap<on and rho/k<on,'Transit return can rearm a genuinely off carrier')
    return dict(startup= startup,startup_carrier_lower=lower,actual_Eon=on,actual_Eoff=off,
        actual_Emax=emax,bank_burst=b,residual_input_power=rho,total_retirement_stock=emax+Tcap,
        no_new_launch_upper=40,half_off_upper=60,off_contact_total_bound=off+Tcap,
        connected_from_arbitrary_transit_lower=connected_lower,
        additional_transit_formation_deficit=forming_deficit,
        established_supply_only_lower=on-b,
        inactive_hysteresis_alone_is_not_low_energy=True,
        retained_total_decay='(E+T)dot<=rho−k(E+T)',
        E_only_contact_does_not_erase_T=True,isolated_old_operations_keep_their_existing_tails=True)

def source_identity_checks():
    cases=0
    for ready in (F(0),F(512),F(1024)):
        for reserved in (F(0),F(512),F(1024)):
            if ready+reserved>1024:continue
            for move in (F(0),ready/2,ready):
                before=ready+reserved;after=(ready-move)+(reserved+move)
                need(after==before and after<=1024,'Reservation minted a second capture store')
                cases+=1
    # A real event may spend stored energy or transfer it; neither creates it.
    for U,E,J,transfer,loss in ((F(10),F(2),F(3),F(2),F(1)),(F(7),F(0),F(0),F(3),F(0))):
        after=(U-transfer-loss)+(E+transfer)+J
        need(U+E+J-after==loss,'Conversion loss or internal transfer miscounted')
    return dict(reservation_cases=cases,private_surplus_not_recredited=True,
                background_repartition_adds_no_bits=True,own_read_latches_not_energy_capsules=True)

def supply_checks(point,core):
    D=point['upstream_rate'];b=point['upstream_burst'];capacity=point['new_upstream_capacity']
    def cumulative(t):
        periods=t//6;phase=t-6*periods
        return periods*8*D+2*D*max(F(0),phase-2)
    grid=[F(k,4) for k in range(97)];cases=0
    for a in grid:
        for z in grid:
            if z<a:continue
            supplied=cumulative(z)-cumulative(a)
            need(supplied>=D*max(F(0),z-a-2),'Recurring supply violates all-interval lower envelope')
            cases+=1
    need(4*D-b>=2*D+b,'One on-period does not recover the worst deficit')
    need(capacity-(b+2*D)==point['upstream_usable_reserve_lower'],'Reserve not derived from actual stock')
    standing=F(core['memory_categories']['selected_input_records'],1024)
    need(0<standing<=F(core['leakage_power'])<D,'Selected real raw-clock holding load is not funded')
    return dict(quarter_quantum_interval_cases=cases,outage_duration=2,period=6,on_power=2*D,
        all_interval_supply='D*(L−2)^+',actual_request_envelope='b+D*L',
        maximal_deficit=b+2*D,usable_reserve_lower=capacity-b-2*D,
        maximum_demand_on_period=4*D+b,on_period_available_work=8*D,
        selected_raw_record_holding_work=standing,outage_drawdown_lower=2*standing,
        witness_returned_work_routing='all returned work is dissipated; raw record clocks remain powered from the proved U reserve',
        proof='D*t−S(t) rises2D in each outage and falls4D in each on-period; complete periods lower it2D')

def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {k:encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [encode(v) for v in value]
    return value

def generate():
    source,core,ports,bindings=source_inputs()
    point=operating_point(source,core,ports)
    return encode(dict(status='independently reviewed source-bound work/reserve/thermal component; full source assembly and admission remain separate',
        bindings=bindings,point=point,transit=transit_checks(point,core,source),
        identity=source_identity_checks(),supply=supply_checks(point,core),
        thermal=thermal_checks(point,core,ports,source),
        source_admission=False,program_completion=False,
        sources={name:digest_text((HERE/name).read_text(encoding='utf-8-sig').replace('\r\n','\n'))
                 for name in ('PORT-RESOURCES.md','port_resource_model.py')}))

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');args=p.parse_args()
    result=generate();path=HERE/'port_resource_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:need(json.loads(path.read_text(encoding='utf-8-sig'))==result,'Direct resource record differs')
    print('port-resource record '+('written' if args.write else 'matches'))

if __name__=='__main__':main()
