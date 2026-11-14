"""Constructive initial native state and split bootstrap for the threshold source.

This checks a finite initial relation and conditional timing suppliers, not
source admission, a full hybrid trace, or recurrent restoration after release.
"""
from fractions import Fraction as Q
import argparse
import json
import sys
import threshold_program_model as program
import threshold_design as design
import threshold_incidence_model as incidence
import legacy_realization as legacy

HERE=program.HERE
BASE='6a5f8aad0f0e5156edb21a054f8c72adcbf7120e'
FIELD='215ecb755312f580cbd8c283b419f0958518766f'
need=program.need
need(sys.version_info[:2]==(3,12) and not sys.flags.optimize,'Unoptimized Python3.12 required')


def frozen(name):
    return legacy.text_at(BASE,'portability/'+name)


def native_initial_points(field,population):
    targets=tuple('region0/host'+str(x) for x in incidence.neighbors(population,0))
    cases=[]
    for active in (False,True):
        for funded_reset in (False,True):
            pulse=field.PulseSelector(cut=not active,native_inhibit=not active,
                initial_reset_energy=(field.RESET_SOURCE_ENERGY,field.RESET_RECEIVER_ENERGY)
                                    if funded_reset else (Q(0),Q(0)))
            setter=field.SettingWriter(targets,cut=not active,native_inhibit=not active,
                reset_stock=field.SETTER_RESET_ENERGY if funded_reset else Q(0))
            need(pulse.slots==[None]*3 and pulse.pending==[None]*3 and pulse.force==0,
                 'Initial native row has retained pulse debt')
            need(pulse.counter_bound_holds() and not pulse.reset_motor_owner,
                 'Initial native state is not the stated idle physical point')
            need(len({id(x) for x in pulse.energy})==3 and
                 len({id(x) for x in pulse.trigger_energy})==3,
                 'Initial energy cells alias')
            need(all(x.stock==field.PULSE_ENERGY for x in pulse.energy) and
                 all(x.stock==field.TRIGGER_ENERGY for x in pulse.trigger_energy),
                 'Initial charge was inferred from capacity')
            need(setter.phase=='ready' and setter.energy==field.SET_ENERGY and
                 not setter.parent_live and setter.parent_record is None and not setter.held,
                 'Initial setter has an unfunded or old parent')
            if not active:
                need(setter.issue((0,0,0,1))=='cut' and pulse.capture(0,1)=='cut',
                     'Inactive initial row is not actually inhibited')
            cases.append(dict(source_bank_active=active,reset_stores_initially_full=funded_reset,
                actual_pulse_work=sum(x.stock for x in pulse.energy),
                actual_trigger_work=sum(x.stock for x in pulse.trigger_energy),
                actual_source_reset_work=pulse.reset_source_reserve.stock,
                actual_receiver_reset_work=pulse.reset_reserve.stock,
                actual_setter_work=setter.energy,actual_setter_reset_work=setter.reset_reserve.stock,
                no_pending_parent_or_packet=True,held_setting_default=0,force=0))
    a=field.PulseSelector();b=field.PulseSelector()
    need(all(x is not y for x in a.energy for y in b.energy),'Two installed channels share a stock')
    # The initial relation is not a reset method. Release does not turn a
    # corrupted counter/force/parent state into any of the above constructors.
    retained=field.PulseSelector(slots=[[1,field.PULSE_COUNTER_CAP],None,None],force=field.FORCE)
    before=(retained.slots[0][:],retained.force,retained.energy[0].stock)
    retained.cut=True
    need((retained.slots[0],retained.force,retained.energy[0].stock)==before and
         not retained.counter_bound_holds(),'Cut relabelled old native debt as initialized')
    return dict(representative_role_cases=cases,distinct_channel_stores=True,
        product_index='(region,source host,source bank,target ordinal,target bank,bit,slot)',
        release_or_cut_is_not_initialization=True,
        retained_after_cut=dict(counter=retained.slots[0][1],force=retained.force,
                                actual_work=retained.energy[0].stock))


def normalize(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:normalize(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [normalize(v) for v in x]
    return x


def generate():
    isa=program.load_isa();c=program.compile_program(isa,design.design(isa));bounds=program.bounds(isa,c)
    geometry_text=frozen('threshold_geometry_results.json');geometry=json.loads(geometry_text)
    publication_text=frozen('publication_timing_results.json');publication=json.loads(publication_text)
    field_text=legacy.text_at(FIELD,'portability/threshold_field_source_results.json');point=json.loads(field_text)
    field,field_code=legacy.module_at(FIELD,'portability/threshold_field_source.py','_initial_native_source')
    need(program.hash_text(field_code)==point['sources_sha256_lf']['threshold_field_source.py'],
         'Initial native model differs from reviewed source')
    image_hash=program.hash_text(json.dumps(c.image))
    need(image_hash==geometry['changed_image_sha256'] and bounds==geometry['bounds'],
         'Initial code/geometry binding changed')
    need(len(c.image)==8192 and all(type(w) is int and 0<=w<2**192 for w in c.image),
         'Initial image is not a finite ordinary code state')
    population=12*(6+2**98)+2;native=native_initial_points(field,population)
    a=geometry['arithmetic'];k=c.constants
    fmin=Q(a['frames']['min']);fmax=Q(a['frames']['max']);boot=Q(a['vectors']['boot'])
    world_accurate=boot+(k['PLANT_ENTRY_FRAMES']+1)*fmax+3
    world_settled=world_accurate+10000
    commissioning=Q(a['recognition_allocation'])
    need(world_settled<commissioning==50000,'Initial world bootstrap exceeds its source tube')
    need(Q(publication['initialization']['plant_entry_min'])>
         boot+publication['receipts']['plant']['arbitrary_counter_cap']+4,
         'Initial plant data acquired a fictitious sample history')
    need(Q(publication['initialization']['maintenance_entry_min'])>
         boot+publication['receipts']['maintenance']['arbitrary_counter_cap']+4,
         'Initial maintenance data did not drain')
    full=Q(a['reconstruction_startup_allocation'])
    need(full==commissioning+Q(a['vectors']['data_and_pool_prepare'])+
         Q(a['vectors']['freshness']),'Changed split initialization allocation')
    # Every cold activation starts at actual zero. The no-earlier-loss
    # implication also needs the stated nominal cam/keeper and abort law.
    earliest_loss=Q(k['WARM_AT'])/Q(a['physical_inputs']['stroke_max'])
    job=Q(a['watchdog']['complete_timer_job'])
    need(full+job<earliest_loss,'Initial keeper cannot cover the complete nontransferable job')
    tube=2*Q(1,10**7)*commissioning
    need(tube==Q(1,100)<Q(1,20),'Initial world tube consumes the reserve')
    tracking=Q(publication['world']['tracker']['tracking_error'])
    need(tracking<Q(1,25),'Initial formed keeper lacks the conditional collar supplier')
    sequence=Q(a['complete_sequence_allocation']);H=Q(a['candidate_H'])
    residual=sequence-full
    need(residual==Q(a['partial_time_allocation'])+Q(a['abort_time_allocation'])+
         2*Q(a['fresh_half_time'])+Q(a['old_suffix_allocation']),
         'Initialization was charged twice or removed from the return allocation')
    need(full+residual<H,'Split bootstrap loses the deadline margin')
    epsilon=Q(2,11**10);W=2**98+6
    service=Q(3,10)*(1-Q(6,population))-Q(W,population)
    formed_service=(Q(3,10)-epsilon)*(1-Q(6,population))-Q(W,population)
    need(service>formed_service>Q(1,10),'Initial actual service does not fit the global consumer')
    resources=point['point']['resources']
    need(Q(resources['usable_reserve_lower'])>1,'Initial upstream assignment has no conservative reserve')
    files=('THRESHOLD-INITIALIZATION.md','threshold_initialization.py','threshold_program_model.py',
           'threshold_program_source.py','threshold_design.py','threshold_incidence_model.py',
           'constructors.py','legacy_realization.py','threshold_publication_model.py')
    frozen_inputs={BASE+':portability/threshold_geometry_results.json':geometry_text,
        BASE+':portability/publication_timing_results.json':publication_text,
        FIELD+':portability/threshold_field_source_results.json':field_text,
        FIELD+':portability/threshold_field_source.py':field_code}
    for name in ('INITIAL-RETURN.md','PORT-SOURCE.md','CYCLE.md','HYBRID.md'):
        frozen_inputs[program.BASE+':local-control/'+name]=program.frozen(name)
    return normalize(dict(status='constructed initial relation and derived conditional split-bootstrap supplier',
        base=BASE,field_base=FIELD,python_version=sys.version,frozen_isa_sha256=isa.source_hash,
        actual_image_sha256=image_hash,code_cells=len(c.image),population=population,
        initial_native_state=native,
        initial_relation=dict(keeper='A; symmetric relabeling permitted',
            active_code='actual compiled C at its physical rails, entered by BOOT or a characterized pre-publication prefix',
            active_tracker=Q(3,5),active_mailbox=Q(3,5),active_activation=k['WARM_AT'],
            cold_activation=0,cold_energy_and_transit=0,cold_tracker_interval=[-1,1],cold_output_weight=0,
            inactive_code='arbitrary retained physical bit states, isolated from CPU/read service until actual formation',
            ordinary_command_fields_and_pending_commands='neutral; no arbitrary old CUT or MODE parent',
            raw_input_records_and_data_queues='arbitrary within their finite capacities; no fictitious sample times',
            clocks='independent phases and admissible uncertain rates',world_box=[Q(2,5),Q(3,5)],
            host_and_coupler_initial_heat='within the recorded combined-energy initialization',
            upstream_initial_stock=Q(resources['upstream_capacity']),
            total_host_capacity_envelope=Q(resources['unchanged_total_host_stock']),
            fault_overlays='actual raw direct/physical footprints within hard state/flow caps; charged from time0',
            initial_debt_clearing='conditional on actual finite initial-pipeline drainage, clock and custody suppliers'),
        bootstrap=dict(latest_accurate_DAC=world_accurate,latest_world_tracking=world_settled,
            early_commissioning=commissioning,world_tracking_slack=commissioning-world_settled,
            initial_displacement=tube,initial_reserve=Q(1,20),
            all_role_commissioning=full,early_world_not_delayed_to_vector_ready=True,
            first_nominal_keeper_loss_lower=earliest_loss,complete_job=job,
            initial_whole_job_slack=earliest_loss-full-job,
            initial_service=service,later_formed_service=formed_service,
            recurrence_after_initialization=residual,H=H,H_slack=H-full-residual,
            no_second_charge_of_initialization=True),
        source_premises=['complete ordinary parent/port nominal timing under actual funded entry',
            'initial native point at all uncharged sources, not restoration by release',
            'actual-cam/keeper/abort implication: initial A service cannot be lost before initially-zero B reaches warm',
            'actual overlap and mutable-code/field custody after first normal handover',
            'one common raw history and its execution/recipient-slot/export projections',
            'source-local reservoir, thermal and physical caps on the protected prefix'],
        remaining=['complete same-history physical source admission and all-mode continuation',
            'paid parent/port realization and actual reset/cam/phase mappings',
            'full charged/interrupted-state retirement and common recurrent closure',
            'positive spatial-density history and independent frozen transfer'],
        sources_sha256_lf={name:program.digest(HERE/name) for name in files},
        immutable_inputs_sha256_lf={name:program.hash_text(text) for name,text in frozen_inputs.items()},
        full_hybrid_trace=False,independent_review_pending=True,program_completion=False))


def main():
    parser=argparse.ArgumentParser(description=__doc__);g=parser.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');args=parser.parse_args()
    result=generate();path=HERE/'threshold_initialization_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:need(json.loads(path.read_text(encoding='utf-8'))==result,'Initial-state record differs')
    print('PASS finite native initial state and conditional split bootstrap; full source remains open')


if __name__=='__main__':main()
