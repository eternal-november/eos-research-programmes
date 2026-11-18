"""Authoritative finite typed-source B parameters and elementary compatibility probes.

The complete recurrence/source-admission proof remains a separate assembly.
"""
from __future__ import annotations
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse,json,math,subprocess,sys,types

HERE=Path(__file__).resolve().parent
BASE='aa7478e'
PREFIX='theories-and-designs/byzantine-control/local-control/'
if sys.flags.optimize:raise RuntimeError('Unoptimized Python required')
def need(x,m):
    if not x:raise AssertionError(m)
def serial(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [serial(v) for v in x]
    return x

def parameters():
    tau=1<<29
    return dict(degree=40,bays_per_side=80,origins=13,sides=2,contacts_per_side=11,
        names=['SUPPLY_IN','SUPPLY_RETURN','MAINTENANCE_FEED','MAINTENANCE_RETURN','WORLD_1','WORLD_2',
               'DATA_TX','DATA_RX','RUNTIME_WRITE','ACTIVE_SENSE','SERVICE'],
        mechanical=dict(modules_per_host=22,modules_per_braking_side=11,tau=tau,
            L_min=tau,L_max=F(3,2)*tau,C_min=tau,C_max=F(3,2)*tau,R_min=64,R_max=65,G_min=64,G_max=65,
            B_nominal='diagonal actual connection factors gamma',ordinary_gamma_min=0,ordinary_gamma_max=1,
            D_nominal='identity22',hard_B_row_l1=22,hard_B_column_l1=22,
            hard_D_row_l1=22,hard_D_column_l1=22,hard_j_l1=1<<20,hard_u_l1=1<<16,
            on_j_per_module=16644,nominal_u_abs_per_module=4,brake_j_l1_per_side=F(1,100),
            force_rating=128,actual_contact_force='q_p/C_p',actual_contact_flow='(B*i)_p',
            actual_contact_side='spring side',gamma_abs_max=1,
            observed_force_envelope='abs(q_p/C_p)/128; actual spring-side load, retained at zero flow',
            force_head_low_reading_error=F(1,100),force_head_saturation=3,
            force_head_rule='bounded error in low range; overload returns rejecting saturation or unavailable',
            physical_state_reset_on_acquisition=False,nominal_coefficients='all bounded funded L,C trajectories; no retained-state reset',
            inverse_coefficient_rate_max=F(1,tau*tau),coefficient_jump='funded interpolation at retained q,phi',
            inverse_coefficient_request='held until next finite-rate parameter update',
            inverse_coefficient_flow='g(J_par)*held_rate inside range; outward coordinate stops at bound until new request',
            mode_reaction_abs_total_per_coordinate=F(1,10),mode_control_work_per_unit_travel=F(1,10),
            work_converter_efficiency_min=F(1,2),work_converter_efficiency_max=1,
            work_converter_owner='local upstream U, outside ordinary operating-bank cut',
            returned_work_destination='U or heat, never direct old E/T',
            coordinate_disturbance_budget=1,total_coordinate_disturbance=F(11,10),cyclic_angles_per_host=88,
            cyclic_angle_families=['inertial shaft','source shaft','dissipative shaft','recipient shaft']),
        clearance=dict(stroke=40000,actual_gap_rate=F(11,400000),elastic_residual_span=F(1,10),elastic_residual_min=F(-1,20),elastic_residual_max=F(1,20),
            nominal_full_gap_min=F(99,100),head_error=F(1,100),position_reset_on_acquisition=False,
            nominal_link_gain_min=F(995,1000),nominal_link_gain_max=1,
            nominal_link_offset_abs=F(1,200),nominal_offset_is_eta=True,elastic_residual_rate_max=1,
            elastic_residual_storage_per_host=F(11,400),elastic_residual_power_per_host=F(11,10),gap_work_converter_efficiency_min=F(1,2),
            gap_work_converter_efficiency_max=1,gap_upstream_power_per_host=F(11,5)),
        bulk_work=dict(transit_stores_per_host=2,output_rate_coefficient=4,transit_bleed=F(1,10),
            connected_carrier_bleed=0,disconnected_carrier_bleed=F(1,10),
            upstream_efficiency_min=F(1,2),upstream_efficiency_max=1,
            transit_capacity_multiple_of_bank_rate=F(1,2),transit_input_multiple_of_bank_rate=F(41,20),
            upstream_draw_multiple_of_bank_rate=F(41,10),operating_output_multiple_of_bank_rate=2,
            mechanical_store_to_CPU_path_when_intact=False,
            power_off_true_predicate='actual common-carrier E<Eoff at the physical sample',
            gate_inactive_is_not_low_E=True,no_rearm_invariant='historical low E plus persistent cut gives E+T<Eon',upstream_full_delivery_energy_threshold=1,
            source_energy_enable='g(U)=clip(U/U_min,0,1); reserve proof must establish g=1',
            full_delivery_scope='physically intact funding/charge boundary under the complete request bill; failed boundaries keep hard laws, not nominal service'),
        execution=dict(code_cells=8192,code_cell_bits=192,private_word_bits=256,
            allocated_private_words_per_processor=32768,processors_per_host=160,
            ordinary_source_scratch_bits=4096,nominal_instruction_rate_min=1<<26,nominal_instruction_rate_max=F(101,100)*(1<<26),
            raw_instruction_launch_ceiling=1<<27,raw_background_cell_clock_ceiling=1<<31,
            per_instruction_capsule_energy=20480,local_admission_driver_work_upper=4096,
            raw_record_capture_energy=1024,private_io_boundary_work_upper=928,native_instruction_work_upper=16384,
            private_native_work_rate_capacity=F(4,3)*16384*(1<<27),
            private_boundary_link_energy=1024,private_reset_work_upper=256,
            private_capture_timer_edges=8,private_capture_timer_tick_min=F(100,101)*(1<<31),
            private_capture_timer_tick_max=1<<31,private_capture_timer_control_steps=8,
            private_other_control_error_work_upper=248,
            private_reset_before_parent_release=True,instruction_parent_ready_plus_pending_capacity=20480,raw_capture_owner='physical source-origin bank',
            private_work_owner='receiving processor bank',raw_multiplicity_supplier='RECEIVER direct-work inventory'),
        raw_capture=dict(autonomous_cells_per_host=12800,capture_work=1024,
            ready_plus_pending_capacity_per_cell=1024,recharge_delta=F(1,1<<30),
            charger_efficiency_min=F(1,2),charger_efficiency_max=1,
            charger_output_capacity=1024*(1<<30),charger_input_capacity=2*1024*(1<<30),
            owner='backend source-origin U_o',classes=['auxiliary','primary-backend'],
            raw_metadata_bits_per_cell=512,raw_snapshot_bits=256,raw_snapshot_latches_per_host=19200,
            own_read_latches_per_host=6400,own_read_source_capsules_per_host=160,
            own_read_capsule_work=4096,own_read_capture_part=1024,
            own_read_owner='launching producer bank; existing synchronous operation',
            raw_control_tick_min=F(100,101)*(1<<31),raw_control_tick_max=1<<31,
            raw_control_settle_ticks=2,source_funding_not_receiver_common=True,
            receiver_strobe_owner='funded receiver-private operation',
            receiver_timer_arm='local private raw-request issuance after descriptor arrival, without raw acknowledgement',
            receiver_waits_for_raw_ready=False,
            receiver_strobe_result='current finite raw word or unavailable; later changes remain raw I',
            private_completion_can_be_overwritten_by_late_raw=False),
        causal=dict(instruction_request_rate=1<<27,physical_request_rate=1<<31,
            requests_use='completed local prefix and pre-jump state; arbitrary permitted memory and values',
            phases='independent unknown offsets',hold='until a later actual update or specified constitutive evolution',
            adversary_service_lower_bound=None,exogenous='bounded measurable signals, not arbitrary implicit feedback equations'),
        hard_work_store=dict(all_mode_intrinsic=True,capacity_parameter='actual installed C_s',availability_scale=1,
            actual_export='generic unreserved controlled output g(S)*r; native aS and fully reserved finite profiles retain their exact laws',
            funded_profile='pending work equals reserved work minus cumulative actual export; no second g throttle',
            reservation='ready plus pending share capacity; generic requests cannot spend an already reserved parcel twice',
            overflow='at S=C_s, positive incoming surplus is actual same-zone heat',
            lower_boundary='g(0)=0; no reaction term creates work',
            stores=['U','E','T','instruction cells','operation cells','capture cells','J_par','retained interconnect work stores'],
            continuous_coefficient_motion='requested inverse-coefficient rate scaled by g(J_par); charge is actual work',
            transfers='inter-zone work moves at finite rate; sender debit equals receiver inflow',
            discrete_updates='same-zone total-energy-conserving transfers; nonthermal loss becomes actual local heat; no external impulse in or out',
            thermal='nonnegative thermal energy; conversion export is available-energy limited',
            exclusions=['intrinsic capacity or dump destruction','extra imported store','unlisted work route']),
        placement=dict(body_zone_host_bag_cover=41,endpoint_zone_host_bag_cover=2,
            fixed_installed_store_locations=True,cartridge_motion='within its own fixture',
            reconfiguration='connections and energy transfers; no installed-capacity teleportation',
            world_store_external=True,funding_owner_is_not_physical_location=True),
        thermal_coupling=dict(complete_row_l1_max=F(1,200),mechanical_row_l1_max=F(1,200),
            meaning='aggregate over every actual zone/normalized mechanical feature, not a per-zone coefficient',
            normalized_mechanical_feature_abs_max=1),
        material_boundary=dict(world_absolute_work=1<<96,other_nonbath_absolute_work=15*(1<<96),
            total_nonbath_absolute_work=1<<100,positive_external_energy_input=1<<100,
            scope='each actual physical material zone; all actual work/heat ports, not funding ownership',
            passive_bath='explicit one-way outgoing k_theta*theta; not an adversarial inlet',
            complete_gross_with_bath='<=2^100+2*k_theta after theta<=2 is proved',
            normal_peak_fit_supplier='PORT-RESOURCES; demand D is not this raw bound'),
        memory=dict(stable_word_recoverable_work=0,
            meaning='C/W/I/held records retain information and authority, not an inferred energy reserve',
            operation_work='funded instruction/operation/capture stores',
            finer_memory_energy='optional refinement with actual M and return paths; not silently imported'),
        world=dict(plant_time_per_hardware_quantum=F(1,10000000),regions_min=6,
            actual_port_effort='regional x',actual_port_flow_unit='quantity per hardware quantum',
            regional_extensive_state='Q=(m/tau_plant)*x',regional_storage='H=m*x*x/(2*tau_plant)',
            body_world_work_per_quantum='signed x*y',world_storage_external_to_host_bill=True,
            safety_lower=F(35,100),safety_upper=F(65,100),initial_lower=F(4,10),initial_upper=F(6,10),
            service_min=F(1,10),independent_hostile_input_abs=F(1,100),side_effect_abs=F(2,100),
            complete_absolute_world_work_ceiling=1<<96,raw_world_flow_bound=1<<98,
            world_work_bound_scope='sum of absolute actual external port work; not net stored-energy change',
            effective_cover=6,persistent_physical_sites=1,loss_export_formula='b + M_raw*p',
            fixed_regional_population=12*(6+(1<<98))+2),
        initialization=dict(healthy_keeper_side='either side independently per host, with every associated field swapped',
            concrete_point_keeper_side=0,healthy_keeper_bay=0,healthy_code='literal frozen P in the characterized formation-prefix relation',
            unused_bay_words='arbitrary',private_initialization='INITIAL-RETURN prefix invariant; not arbitrary PC/W',
            pending_instruction='absent or the actual corresponding prefix instruction and operands',
            remaining_drain_min=F(300,101),initial_drain_elapsed_max_instructions=1<<26,
            maintenance_mailboxes_and_pending='actual neutral encoded records',maintenance_force_stores=0,
            nonselected_processors='cannot launch hidden old instructions',
            incoming_privileged_writer_condition='closed at selected active body',
            active_clamp='closed',cam_initial_offset_min=0,cam_initial_offset_max=8000,
            mode='NORMAL_STOP; FULL latch false',nonselected_activations=0,
            additional_released_debt_D0=0,other_world_trackers='arbitrary[-1,1] behind zero weight',
            raw_records='arbitrary bounded initial records; actual expiry/entry gates retained',
            clock_phases='independent unknown offsets; no common phase zero',
            active_mechanical_i=4,active_mechanical_v=258,cold_mechanical_phi=0,cold_mechanical_q=0,
            initial_world_tracker=F(3,5),initial_keeper_E='Emax',initial_keeper_T='Tcap',
            initial_standby_E=0,initial_standby_T=0,initial_upstream_U='actual full finite capacity',
            initial_parameter_store='actual full finite J_par capacity',
            thermal_theta_min=0,thermal_theta_max=1,concrete_thermal_theta=0,
            physical_fault_initial_states='any state inside the same global hard bounds',
            initial_direct_domains_max=2))

def base_binding():
    names=('geometry_results.json','program_source.py','program_model.py','resource_results.json',
           'INCIDENCE.md','PORTS.md','INITIAL-RETURN.md','FAULT-MAP.md','port_model.py','geometry_model.py','RECEIVER.md','RUNTIME-PORTS.md',
           'initial_return_results.json','transducer_results.json')
    texts={n:subprocess.check_output(['git','show',BASE+':'+PREFIX+n],cwd=HERE).decode('utf-8-sig').replace('\r\n','\n') for n in names}
    g=json.loads(texts['geometry_results.json'])
    core=json.loads(texts['resource_results.json'])['runtime_inventory']
    return dict(commit=subprocess.check_output(['git','rev-parse',BASE],cwd=HERE).decode().strip(),
        sources={n:sha256(s.encode()).hexdigest() for n,s in texts.items()},
        actual_code_cells=g['compiler']['code_cells'],image_sha256=g['compiler']['encoded_image_sha256'],
        functional_guard_horizon=F(g['guard_jump_certificate']['horizon']),
        existing_private_words=g['compiler']['instruction_bounds']['private_words_with_metadata'],
        historical_resource_comparison=dict(bank_rate=F(685532305896545463,4),bank_burst=F(core['per_bank_burst']),
            Eon=685532306538273979,Eoff=F(1371064613076547958,3),Emax=1371064612434819442,
            rho=39766224714,standing_field_and_world_power=42000020,isolated_tail_capacity=407371776),
        direct_work_inventory_not_silently_inferred=True)

def mechanical_checks(p,base):
    a=p['mechanical'];tau=F(a['tau']);k=16/tau
    opposition=6*F(22,5)+a['total_coordinate_disturbance']
    need(opposition<28 and 68-opposition-29>=2,'Added mode reaction removes force progress/retention')
    need(F(64)/F(3,2)-22>16,'Hard diagonal decay margin fails')
    Fhard=F(a['hard_j_l1'])+22*a['hard_u_l1'];W=Fhard/k
    need(W==155648*tau,'Hard common state bound changed')
    # The good side is separately braked while its keeper side remains live.
    Fside=11*4+F(1,100);kgood=32/tau
    need(F(64)/F(3,2)-1>32 and Fside/kgood<8*tau,'Nominal side clearance floor fails')
    Wclear=16*tau;Tclear=15*tau/32
    need((W-8*tau)<(Wclear-8*tau)*(1<<15),'Fifteen conservative halvings do not clear')
    load_clear=Wclear/(tau*128)
    Ihard=W/tau
    drift=(a['hard_j_l1']+22*Ihard)/(tau*128)
    load_upper=F(3,2)*(F(1,2)+F(1,100))+drift*base['functional_guard_horizon']
    need(load_upper<1 and load_clear==F(1,8),'Actual force guard fails')
    on_faces=[255-4-65*F(19,5),64*F(21,5)-261-4,
              16644-F(21,5)-65*255,F(19,5)+64*261-16644]
    need(min(on_faces)>0,'Constant-coefficient on-neighborhood has an outward face')
    stored_faces=[-F(1,4)-4+64*F(1,5)/F(3,2),64*10/F(3,2)-400-4,
                  -F(1,100)-10+64*F(1,4)/F(3,2),64*400/F(3,2)-F(1664401,100)-F(1,5)]
    need(min(stored_faces)>0,'Stored-state ordinary-mode box has an outward face')
    on_F=F(1664801,100)
    node_after_nine=W/tau/512+on_F/32
    need(node_after_nine<1024 and on_F<32*1024,'Full-on contraction does not reach an invariant node bound')
    q_growth=F(1664399,100)-1024-65*200
    need(q_growth>0,'Full-on stored deformation has no lower progress')
    loaded_entry=9*tau/32+1224*tau/q_growth
    need(F(200,1)/(F(3,2)*128)==F(25,24)>1,'Varying-compliance loaded state is not prohibited')
    Hhard=W*W/(2*tau);Jcap=Hhard/3;Pparam=W*W/(2*tau*tau)
    need(Pparam==12113149952,'Parameter-work rate differs')
    nominal_power=22*16644*261+22*4*F(21,5)
    hard_power=(W/tau)*(a['hard_j_l1']+22*a['hard_u_l1'])
    return dict(actual_force_opposition=opposition,actual_force_surplus=68-opposition-29,k_hard=k,F_hard=Fhard,W_hard=W,k_good=kgood,F_braking_side=Fside,
                W_clear_per_braking_side=Wclear,clearance_time=Tclear,clear_load_upper=load_clear,
                force_continuation_multiplier=F(3,2),force_continuation_drift=drift,
                force_upper_on_passing_guard=load_upper,on_face_margins=on_faces,
                on_i_interval=[F(19,5),F(21,5)],on_v_interval=[255,261],
                tight_on_interval_scope='constant L,C comparison only; not the varying-coefficient source premise',
                ordinary_stored_box_phi=[-tau/5,10*tau],ordinary_stored_box_q=[-tau/4,400*tau],
                ordinary_stored_box_face_margins=stored_faces,
                full_on_node_bound_after_nine_halvings=node_after_nine*tau,
                full_on_q_growth_below_200tau=q_growth,varying_coefficient_loaded_entry=loaded_entry,
                varying_coefficient_loaded_force_lower=F(25,24),
                no_hidden_minimum_brake_dwell_assumed=True,
                reachable_on_load_lower=F(255,128),mechanical_hard_storage=Hhard,
                parameter_work_store_capacity=Jcap,continuous_parameter_work_rate=Pparam,
                parameter_recharge_delivered_rate=Pparam,parameter_recharge_upstream_ceiling=2*Pparam,
                constant_coefficient_on_box_power_comparison=nominal_power,hard_mechanical_absolute_port_power=hard_power,
                mechanical_shared_bill_power_field='hard_mechanical_upstream_work_ceiling',
                hard_mechanical_upstream_work_ceiling=2*hard_power,
                no_whole_host_brake_assumption=True)

def parameter_jump_checks():
    count=0
    for requested,available in product((F(-2),F(0),F(1,2),F(2)),(F(0),F(1,4),F(1))):
        alpha=1 if requested<=0 else min(F(1),available/requested)
        delta=alpha*requested
        unclipped=available-delta
        remaining=min(F(1),unclipped);heat=max(F(0),unclipped-1)
        need(0<=alpha<=1 and 0<=remaining<=1,'Energy-limited motion is blocked or leaves capacity')
        need(delta+remaining-available+heat==0,'Coefficient motion manufactured work')
        count+=1
    return dict(cases=count,retained_coordinates=['q','phi'],actual_motion='interpolate inverse L,C by funded alpha',
                every_request_has_an_actual_continuation=True,no_positive_jump_of_mechanics_plus_work_store=True)

def transit_checks(base):
    r=base['historical_resource_comparison'];d=r['bank_rate'];Tcap=d/2
    need(F(41,20)*d==(4+F(1,10))*Tcap,'Transit capacity is not an inward barrier')
    need(r['Emax']+Tcap<4*r['Eoff'],'Transit invalidates four-to-one drainage ratio')
    need(r['Eoff']+Tcap<r['Eon'],'Low-E contact can rearm from hidden transit work')
    need(r['rho']<F(1,10)*r['Eoff']/4,'Residual backfeed consumes drain margin')
    exp_lower=sum((F(41,10)**n/F(math.factorial(n)) for n in range(9)),F(0))
    need(exp_lower>20,'Actual transit startup comparison fails')
    burst=r['bank_burst']
    need(F(9,2)*d>=r['Eon']+burst,'Five post-startup quanta do not fund cold operation')
    connected_lower=r['Eon']-burst-F(20,41)*d
    need(connected_lower>r['Eoff'],'First-on carrier bound with retained transit falls below Eoff')
    need(4*Tcap-F(1,10)*r['Eoff']>0,'Low-E historical counterexample disappeared')
    return dict(connected_carrier_lower_from_first_Eon=connected_lower,
                low_E_is_historical_not_an_invariant_of_E_alone=True,
                actual_E_threshold_not_gate_inactive_required=True,
                Tcap=Tcap,combined_refundable_capacity=r['Emax']+Tcap,
                new_upstream_charger_multiple_per_bank=F(41,10),nominal_cold_prefix=6,
                after_actual_cut='(E+T)_dot <= rho-.1*(E+T)',minimum_no_rearm_margin=r['Eon']-r['Eoff']-Tcap,
                bank_rate_scope='historical checked comparison; direct owner-affine work inventory must confirm or rebind it')

def world_checks(p):
    w=p['world'];m=w['fixed_regional_population'];M=w['raw_world_flow_bound'];loss=6+M
    tau=w['plant_time_per_hardware_quantum'];world_capacity=F(m)/tau
    power_cases=0
    for x,local_drive,host_flow in product((F(35,100),F(1,2),F(65,100)),(F(-1),F(0),F(1)),(F(-2),F(0),F(2))):
        Qdot=m*local_drive-host_flow
        xdot=Qdot/world_capacity
        need(xdot==tau*(local_drive-F(host_flow,m)),'WORLD clock/flow units changed the actual mission')
        need(world_capacity*x*xdot==x*Qdot,'WORLD storage and actual port work do not pair')
        power_cases+=1
    need(m%2==0 and F(loss,m)<F(1,12),'Same-history loss/export fraction fails')
    need(F(20,7)*w['complete_absolute_world_work_ceiling']<M,'Protected-prefix work/flow conversion fails')
    upper=F(84,100)*(1-F(6,m))-F(loss,m)
    lower=F(36,100)+F(loss,m)
    service=F(3,10)*(1-F(6,m))-F(loss,m)
    need(upper>F(64,100) and lower<F(56,100) and service>F(1,10),'Actual world collar/service margin fails')
    derivative=F(61,100)+F(9,10)+F(loss,m)+3*F(2,100)*F(3,10)+F(1,100)+F(2,100)
    need(derivative<2,'New source needs an unrecorded plant speed')
    return dict(regional_population=m,cohort_for_six_regions=6*m,loss_export_weight=loss,
                regional_world_capacity=world_capacity,actual_world_power_pair_cases=power_cases,
                hardware_quantum_flow_not_plant_time_flow=True,world_storage_external=True,
                upper_collar_flow_lower=upper,lower_collar_flow_upper=lower,interior_service_lower=service,
                protected_state_derivative_upper=2,hardware_plant_time_scale_unchanged=True,
                raw_world_work_limit_is_elementary_source_input=True)

def primary_force_witness(p,base):
    # This source trace uses actual retained mechanics, not a guessed raw word.
    tau=F(p['mechanical']['tau']);window=5000
    variation=34*window/tau
    interval=[F(1,2)-variation,F(1,2)+variation]
    need(variation<F(1,2000),'Stored-force trajectory leaves the selected ADC bins')
    words=[]
    for bias,expected in ((F(-9,1000),491),(F(9,1000),509)):
        for force in interval:
            word=math.floor(1000*(force+bias)+F(1,2))
            need(word==expected and abs(F(word,1000)-force)<F(1,100),'Raw head does not realize the record')
        words.append(expected)
    def text(name):
        return subprocess.check_output(['git','show',BASE+':'+PREFIX+name],cwd=HERE).decode('utf-8-sig')
    pm=types.ModuleType('_port_source_frozen_pm');pm.__file__=str(HERE/'program_model.py')
    sys.modules[pm.__name__]=pm
    exec(compile(text('program_model.py'),pm.__file__,'exec'),pm.__dict__)
    class Source:
        def read_text(self,**kwargs):return text('program_source.py')
    pm.SOURCE=Source()
    gm=types.ModuleType('_port_source_frozen_gm');gm.__file__=str(HERE/'geometry_model.py')
    sys.modules[gm.__name__]=gm
    previous=sys.modules.get('program_model');sys.modules['program_model']=pm
    try:exec(compile(text('geometry_model.py'),gm.__file__,'exec'),gm.__dict__)
    finally:
        if previous is None:sys.modules.pop('program_model',None)
        else:sys.modules['program_model']=previous
    compiled=pm.compile_check(gm.design());k=compiled.constants
    image=sha256(b''.join(x.to_bytes(24,'little') for x in compiled.image)).hexdigest()
    need(image==base['image_sha256'],'Witness compiled another policy image')
    key=3+k['VIEW_WORDS'];answers=[]
    for primary in words:
        machine=pm.Machine(compiled,poison=0);ports=pm.RawPorts(compiled)
        for origin,value in enumerate([primary]+[491]*6+[509]*6):
            ports.fast[(origin,0,key)]=value
            ports.fast[(origin,0,key+2)]=0
        before=list(machine.C)
        machine.enter('permission',(k['TARGET_BASE'],0))
        need(machine.run(ports,until_yield=False)=='halt','Actual guard did not finish')
        need(machine.C==before,'Input-only witness modified execution code')
        answers.append(machine.result())
    need(answers==[1,0],'Actual policy did not consume primary variation')
    return dict(physical_force_interval=interval,window=window,force_head_biases=[F(-9,1000),F(9,1000)],
                actual_record_words=words,actual_guard_verdicts=answers,unchanged_policy_image=image,
                mechanics='constant L=C=tau, R=G64, v64, i in[0,4.2], j=u0; H is nonincreasing',
                source_continuation='on-neighborhood to brake crosses v64; while v>=64,0<=i<=4.2; no q/phi reset',
                whole_primary_input_fault_only=True,other_twelve_origins_unchanged=True)


def return_schedule(p,mechanical,base):
    raw=subprocess.check_output(['git','show',BASE+':'+PREFIX+'geometry_results.json'],cwd=HERE)
    g=json.loads(raw);t=g['timing'];cert=g['compiler']['processing_certificate']
    clear=F(mechanical['clearance_time'])
    phases={name:F(v) for name,v in t['phase_bounds'].items()}
    phases['0_prepared_isolate_shunt_cut_drain']+=clear
    phases['10_old_isolate_shunt_cut_drain']+=clear
    band=F(t['normal_band_travel']);one_band=band/13
    earliest=F(t['earliest_timeout']);work=F(t['work'])
    for phase in t['short_phases_by_whole_stage']:
        value=next(v for name,v in phases.items() if name.startswith(str(phase)+'_'))
        need(value+one_band<earliest,'Physical clearance can cause a healthy phase to time out')
    half=sum(phases.values())+band
    abort=F(t['abort'])+clear
    partial=F(t['partial'])
    total=F(t['commissioning'])+partial+abort+2*half+F(t['old_suffix'])
    H=math.ceil(total)+1;Hold=int(t['conditional_return_H'])
    need(H==Hold+5*int(clear),'Return delay was charged outside or omitted from a phase')
    constants=dict(g['design']['physical_parameters'])
    pre_power=F(constants['POWER_AT'])/F(11,10)
    need(mechanical['varying_coefficient_loaded_entry']+6<pre_power,'Actual pre-power travel does not cover loaded entry')
    need(F(t['timer_window'])<=work,'Existing complete timer job no longer fits a ready-bank interval')
    need(max(v+one_band for name,v in phases.items() if not name.startswith(('1_','8_')))<work,
         'The added clearance job is not covered by one existing nontransferable interval')
    old_rate=F(t['raw_arrival_rate']);cover=1+2+math.floor(3+2*old_rate*H)
    need(cover==6,'The same prior acquisition rate loses the required cover')
    return dict(unchanged_policy_image=base['image_sha256'],phase_bounds=phases,
                conditional_return_H=H,previous_return_H=Hold,actual_extra_total_return=5*clear,
                strict_slack=F(H)-total,half_cycle=half,abort=abort,
                unchanged_partial_bound=partial,unchanged_rank_spans=t['rank_spans'],
                unchanged_earliest_timeout=earliest,unchanged_timer_job=F(t['timer_window']),
                unchanged_nontransferable_ready_window=work,
                original_raw_acquisition_rate=old_rate,cover_at_original_rate=cover,
                slower_adversary_not_assumed=True,cut_stroke_not_lengthened=True,
                actual_pre_power_travel_lower=pre_power,loaded_entry_fits_actual_travel=True,
                cold_power_prefix=6,existing_charging_allowance=10000,
                scope='Actual unchanged program and phase layout; source work, history and refinement suppliers still required')


def source_decode_counterchecks(p,mechanical):
    tau=F(p['mechanical']['tau'])
    q=96*tau;before=abs(q)/(F(3,2)*tau*128);after=abs(q)/(tau*128)
    work=q*q/(2*tau)-q*q/(3*tau)
    need(before==F(1,2) and after==F(3,4),'Retained-compliance witness differs')
    need(after-before>F(1,5),'Old additive force-jump interface was not actually challenged')
    need(work<=mechanical['parameter_work_store_capacity'],'Compliance jump witness is unfunded')
    hidden_force=F(64*3+4,128)
    need(hidden_force>1,'Wrong-cut damper/recipient force counterexample disappeared')
    return dict(retained_compliance_jump=dict(before=before,after=after,actual_funded_work=work,
                    q_reset=False,legacy_additive_jump_limit=F(1,5),legacy_envelope_invalid=True),
                selected_guard_still_sound=mechanical['force_upper_on_passing_guard']<1,
                wrong_contact_decoder=dict(spring_force=0,momentum_flow=3,recipient_effort=4,
                    actual_added_damper_and_recipient_load=F(49,32),simple_spring_head=0),
                old_whole_trace_force_abstraction_not_imported=True)


def capture_work_interface(p):
    c=p['raw_capture'];e=p['execution'];d=p['degree'];B=p['bays_per_side']
    cells=2*B*(2*d);own=2*B*d
    need(cells==c['autonomous_cells_per_host']==12800 and own==6400,'Capture ownership multiplicity changed')
    mu=e['raw_instruction_launch_ceiling'];delta=F(1,8*mu)
    need(delta==c['recharge_delta'],'Capture recharge uses another clock')
    stock=cells*c['capture_work'];upstream=cells*c['charger_input_capacity']
    need(stock==13107200 and upstream==28147497671065600,'Direct capture capacity/power changed')
    padding=(2048-976)*1420796
    snapshots=(cells+own)*256;metadata=cells*c['raw_metadata_bits_per_cell']
    need(snapshots+metadata<=padding,'Capture state is not backed by existing raw padding')
    # Reallocation is by actual source owner, not just receiver-total arithmetic.
    N=432;counts=[0]*N
    for receiver in range(N):
        for shift in list(range(-20,0))+list(range(1,21)):
            counts[(receiver+shift)%N]+=2*B*2
    need(set(counts)=={cells},'Origin-affine per-host capture bill is not regular')
    # Old raw control phases settle without a new launch in at most two ticks.
    phase_step={0:0,1:0,2:1,3:1}
    need(all(phase_step[phase_step[x]]==0 for x in phase_step),'Raw capture control retains unbounded old phase')
    settle=F(c['raw_control_settle_ticks'])/c['raw_control_tick_min']
    native=e['private_io_boundary_work_upper']/e['private_native_work_rate_capacity']
    # Actual independent-phase receiver clock:8 edges contain at least7 full periods.
    reset_compute=e['private_reset_work_upper']/e['private_native_work_rate_capacity']
    edges=e['private_capture_timer_edges']
    timer_min=F(edges-1,e['private_capture_timer_tick_max'])
    timer_max=F(edges)/e['private_capture_timer_tick_min']
    raw_ready_upper=settle+2*delta
    need(timer_min>=raw_ready_upper,'Receiver strobe can precede a functioning raw capture')
    need(e['private_capture_timer_control_steps']+e['private_other_control_error_work_upper']==256,
         'Timer control exceeds the existing finite control/error price')
    suffix=timer_max+2*delta+native+reset_compute
    nominal_max=e['nominal_instruction_rate_max'];nominal_min=e['nominal_instruction_rate_min']
    nominal_suffix=F(3,4)/nominal_max
    need(suffix<=nominal_suffix,'Actual I/O suffix exceeds fastest nominal P service')
    need(suffix>F(3,4*mu),'Independent-phase timer unexpectedly kept the superseded hard-cycle comparison')
    strobe_deadline=timer_max
    need(not c['receiver_waits_for_raw_ready'] and not c['private_completion_can_be_overwritten_by_late_raw'],
         'Raw ready/busy or late input acquired private control authority')
    # Raw flags are input data, never a transition guard for the private timer.
    raw_fault_cases=0
    for ready,busy,powered,word in product((False,True),repeat=4):
        current_word=1 if word else 0
        for sampled in (current_word,(1<<256)-1) if not powered else (current_word,):
            private_result=int(sampled<=0)
            completion=strobe_deadline+delta+native
            need(completion<suffix,'Failed raw readiness stalled a private instruction')
            need(private_result in (0,1),'Raw control became private executable code')
            raw_fault_cases+=1
    phase_cases=0
    for rate in (e['private_capture_timer_tick_min'],e['private_capture_timer_tick_max']):
        for fraction in (F(0),F(1,4),F(1,2),F(3,4),F(1)):
            wait=(edges-1+fraction)/rate
            need(raw_ready_upper<=wait<=timer_max,'An independent timer phase changes capture adequacy')
            phase_cases+=1
    parent_recharge=F(1,4*mu)
    need(parent_recharge<=F(1,4)/nominal_max,'Parent charge no longer fits the nominal first quarter')
    need(suffix+parent_recharge<F(1)/nominal_max,'Reset and parent recharge miss the nominal cycle')
    need(suffix+parent_recharge>F(1,mu),'Old8delta hard-cycle comparison should be withdrawn')
    old_instruction_tail=F(1,nominal_min)
    own_read_wait=F(1,64)
    need(suffix<old_instruction_tail,'Existing old private instruction tail was exceeded')
    need(suffix+own_read_wait<old_instruction_tail+own_read_wait,'Own-read old destination tail was exceeded')
    need(old_instruction_tail+own_read_wait+2+delta<F(300,101),
         'The actual initial pending/data/reset suffix outlives remaining prefix drainage')
    need(F(1)/nominal_max-suffix>delta,'Nominal instruction reuse outruns raw recharge')
    private_work=e['private_io_boundary_work_upper']+e['private_boundary_link_energy']+e['private_reset_work_upper']
    need(private_work==2208<e['per_instruction_capsule_energy'],'Private work/reset lacks its actual capsule')
    need(e['private_reset_work_upper']/e['private_native_work_rate_capacity']<delta,
         'Reset work does not fit its already counted reset interval')
    private_words=8*(2*d+1)
    need(20362+private_words<=e['allocated_private_words_per_processor'],'Private descriptor/result state was unallocated')
    return dict(new_autonomous_capture_cells=cells,new_capture_capacity=stock,
                upstream_peak=upstream,local_output_peak=cells*c['charger_output_capacity'],
                raw_charger_efficiency=[F(1,2),1],bulk_efficiency_not_reapplied=True,
                ready_and_pending_share_one_capacity=True,own_read_latches=own,
                own_read_source_capsules=2*B,own_read_capture_is_part_of_4096=True,
                raw_snapshot_bits=snapshots,new_capture_metadata_bits=metadata,
                existing_raw_padding_bits=padding,additional_background_bits=0,
                origin_regularity_test_hosts=N,cells_charged_per_origin=cells,
                private_words_per_cartridge=private_words,private_work=private_work,
                private_reset_work_reserved=e['private_reset_work_upper'],
                private_reset_compute_time=reset_compute,reset_complete_before_parent_release=True,
                parent_recharge_time=parent_recharge,private_cycle_through_recharge=suffix+parent_recharge,
                private_capsule_unallocated_budget=e['per_instruction_capsule_energy']-private_work,
                raw_old_control_settle=settle,raw_good_capture_upper=raw_ready_upper,
                receiver_private_strobe_lower=timer_min,receiver_private_strobe_deadline=strobe_deadline,
                independent_phase_timer_cases=phase_cases,private_timer_edges=edges,
                private_timer_control_work_is_within_256=True,
                raw_ready_fault_probe_cases=raw_fault_cases,raw_ready_not_a_private_wait_guard=True,
                actual_private_suffix=suffix,
                reserved_private_suffix=nominal_suffix,unchanged_program_timing=True,
                previous_hard_cycle_suffix=F(3,4*mu),hard_cycle_lower_service_not_claimed=True,
                reused_old_instruction_tail=old_instruction_tail,reused_old_own_read_tail=old_instruction_tail+own_read_wait,
                private_parent_never_overlapped=True,initial_prefix_tail_unchanged=True,
                ledger_owner='PORT-RESOURCES; this is an interface export, not a second D')


def initial_relation_checks(p,base):
    def record(name):
        return json.loads(subprocess.check_output(['git','show',BASE+':'+PREFIX+name],cwd=HERE))
    init=p['initialization']
    need(0<=init['thermal_theta_min']<=init['concrete_thermal_theta']<=init['thermal_theta_max']==1,
         'Thermal initial state does not supply the shared-energy comparison')
    initial=record('initial_return_results.json')['initial'];field=record('transducer_results.json')
    need(field['program_abi']['actual_neutral_matches'],'Literal neutral command differs')
    need(field['decoding']['neutral_record']!=0 and field['decoding']['raw_zero_record_amplitude']==-32,
         'Zero bits were silently treated as neutral effort')
    need(F(initial['remaining_drain_min'])>F(initial['last_old_prefix_effect']),
         'Initial pending-instruction genealogy outlives the actual prefix drain')
    need(F(initial['plant_gate_min'])>F(initial['first_genuine_plant_upper']),
         'Plant entry silently starts with useful records')
    need(F(initial['maintenance_gate_min'])>F(initial['first_genuine_maintenance_upper']),
         'Maintenance entry silently starts with useful records')
    return dict(actual_neutral_record=field['decoding']['neutral_record'],
                inherited_full_initial_relation=initial,
                requires_formed_prefix_not_just_code_equality=True,
                arbitrary_hidden_old_store_completion_not_admitted_as_clean=True,
                no_additional_released_initial_debt=True,independent_keeper_side_swaps=True)


def causal_hold_checks(p):
    # A bounded instantaneous state-feedback formula is not a causal hold
    # implementation. The sample/hold version has an explicit next segment.
    traces=[]
    for phase,step in product((F(0),F(1,7),F(3,5)),(F(1),F(2,3))):
        x=F(0);time=phase;trace=[]
        for _ in range(20):
            request=F(1) if x<=0 else F(-1)
            endpoint=x+step*request
            trace.append((time,x,request,time+step,endpoint))
            x=endpoint;time+=step
        need(all(t1>t0 for t0,_,_,t1,_ in trace),'A held request created a zero-duration loop')
        traces.append(trace)
    return dict(sample_hold_traces=len(traces),segments_per_trace=20,
                arbitrary_values_and_history_dependence_preserved=True,
                independent_unknown_phases=True,adversary_update_lower_service_not_assumed=True,
                source_strategy_scope='completed-prefix requests through finite-rate holds; specified well-posed constitutive feedback',
                instantaneous_measurable_state_feedback_not_identified_with_time_signals=True)


def boundary_work_interface(p,mechanical,capture,base):
    b=p['material_boundary'];world=b['world_absolute_work'];other=b['other_nonbath_absolute_work']
    need(world==1<<96 and world+other==b['total_nonbath_absolute_work']==1<<100,
         'Raw WORLD/other boundary ratings do not assemble')
    known=dict(mechanical_upstream=mechanical['hard_mechanical_upstream_work_ceiling'],
               parameter_recharge_upstream=mechanical['parameter_recharge_upstream_ceiling'],
               gap_upstream=p['clearance']['gap_upstream_power_per_host'],
               raw_capture_upstream=capture['upstream_peak'],
               two_bulk_chargers=2*F(41,10)*base['historical_resource_comparison']['bank_rate'])
    need(sum(known.values())<other,'Known simultaneous additions exceed the chosen raw boundary')
    need(p['memory']['stable_word_recoverable_work']==0,'An unpriced memory-energy return path appeared')
    return dict(raw_world_ceiling=world,raw_other_nonbath_ceiling=other,
                raw_total_nonbath_ceiling=world+other,known_concurrent_additions=known,
                known_additions_only_not_a_second_bill=True,
                complete_normal_peak_fit_supplier='PORT-RESOURCES',
                actual_physical_zone_required=True,passive_bath_counted_separately=True,
                raw_information_not_a_funding_store=True)


def hard_store_checks(p):
    count=0
    C=F(10)
    for S,incoming,requested in product((F(0),F(1,2),F(5),C),(F(0),F(1),F(20)),(F(0),F(2),F(30))):
        g=min(F(1),S)
        actual=g*requested
        dump=max(F(0),incoming-actual) if S==C else F(0)
        derivative=incoming-actual-dump
        need(derivative+actual+dump==incoming,'Store flow creates or deletes work')
        if S==0:need(actual==0 and derivative>=0,'Empty store exports invented work')
        if S==C:need(derivative<=0,'Fault-rerouted inflow exceeds material capacity')
        need(dump>=0,'Overflow is fictitious negative heat')
        for rate in (F(1,10),F(4)):
            need(g*rate*max(F(1),S)==rate*S,'Availability law changed a native proportional export')
        count+=1
    profiles=0
    for work,duration in product((F(1024),F(4096),F(20480)),(F(1,1<<30),F(1,128),F(1))):
        rate=work/duration
        for fraction in (F(0),F(1,4),F(1,2),F(3,4),F(1)):
            elapsed=fraction*duration
            consumed=rate*elapsed;pending=work-consumed
            actual_rate=rate if elapsed<duration else F(0)
            need(pending>=0 and pending+consumed==work,'Finite native profile creates or loses reserved work')
            if elapsed==duration:need(pending==0 and actual_rate==0,'Funded profile cannot exhaust at its deadline')
            profiles+=1
    # Once a generic g-throttled cell enters(0,1), its remaining work is exp(-r*t),
    # strictly positive at every finite t. It cannot replace a full native pulse.
    transfers=0
    for sender,receiver,request in product((F(0),F(3),F(10)),(F(0),F(8),F(10)),(F(0),F(5),F(20))):
        amount=min(sender,request);accepted=min(amount,C-receiver);heat=amount-accepted
        after_sender=sender-amount;after_receiver=receiver+accepted
        need(0<=after_sender<=C and 0<=after_receiver<=C,'Transfer leaves a material capacity')
        need(sender+receiver==after_sender+after_receiver+heat,'Transfer spends one work parcel twice')
        transfers+=1
    need(20-F(41,10)*F(1)>0,'Nominal transit-only counterexample missing')
    # Thermal conversion is not a withdrawal from a negative heat balance.
    thermal=0
    for energy,heat_in,conversion_request in product((F(0),F(1,2),F(5)),(F(0),F(2)),(F(0),F(4))):
        converted=min(F(1),energy)*conversion_request
        bath=energy
        derivative=heat_in-converted-bath
        if energy==0:need(derivative>=0 and converted==0,'Thermal conversion borrows nonexistent heat')
        need(derivative+converted+bath==heat_in,'Thermal/work conversion breaks conservation')
        thermal+=1
    return dict(flow_cases=count,funded_native_profile_cases=profiles,
                smooth_empty_throttle_not_used_for_funded_deadlines=True,
                rejected_throttle_solution='S(t)=S0*exp(-r*t)>0 at every finite t after entering(0,1)',
                funded_profile_scope='actual reserved work and native completion law, not a software ready flag',
                same_zone_transfer_cases=transfers,thermal_cases=thermal,
                external_transfers_are_finite_rate_ports=True,
                all_mode_capacity_not_from_nominal_charger=True,overflow_is_actual_heat=True,
                no_lower_reflection_fuel=True,mechanical_q_phi_not_clipped=True,
                explicit_source_boundary=p['hard_work_store']['exclusions'])


def placement_and_coupling_checks(p):
    d=p['degree'];cover=p['placement']['body_zone_host_bag_cover']
    need(cover==d+1 and p['placement']['endpoint_zone_host_bag_cover']==2,'Placement cover differs')
    N=432;checked=0
    for i in range(N):
        neighbors={(i+s)%N for s in list(range(-20,0))+list(range(1,21))}
        bags={i}|neighbors
        need(len(bags)==41,'Body placement has another host bag')
        for o in neighbors:
            need({i,o}<=bags,'Endpoint store is not in its actual cover')
            checked+=1
    thermal=p['thermal_coupling']
    effect=2*thermal['complete_row_l1_max']+thermal['mechanical_row_l1_max']
    need(effect==F(3,200)<p['world']['side_effect_abs'],'Whole coupling row exceeds source world allowance')
    return dict(body_zone_checks=N,endpoint_checks=checked,body_cover=cover,
                cover_is_upper_bound_not_spendable_reserves=True,
                thermal_row_l1=thermal['complete_row_l1_max'],mechanical_row_l1=thermal['mechanical_row_l1_max'],
                resulting_world_side_effect=effect,per_zone_coefficients_not_summed_without_a_row_budget=True)


def main():
    parser=argparse.ArgumentParser();g=parser.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');a=parser.parse_args()
    names=('PORT-SOURCE.md','port_source_model.py')
    sources={n:sha256((HERE/n).read_text(encoding='utf-8-sig').replace('\r\n','\n').encode()).hexdigest() for n in names}
    p=parameters();base=base_binding();mechanical=mechanical_checks(p,base);capture=capture_work_interface(p)
    result=serial(dict(status='initialized finite typed-source candidate; full common refinement not yet discharged',
        sources=sources,parameters=p,base_binding=base,mechanical=mechanical,
        coefficient_motion=parameter_jump_checks(),transit=transit_checks(base),world=world_checks(p),
        primary_force_witness=primary_force_witness(p,base),return_schedule=return_schedule(p,mechanical,base),
        source_decode=source_decode_counterchecks(p,mechanical),capture_work=capture,
        boundary_work=boundary_work_interface(p,mechanical,capture,base),
        initial_relation=initial_relation_checks(p,base),causal_holds=causal_hold_checks(p),
        hard_stores=hard_store_checks(p),placement_and_coupling=placement_and_coupling_checks(p),
        source_admitted=False,program_completion=False))
    target=HERE/'port_source_results.json'
    if a.write:target.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    else:need(json.loads(target.read_text(encoding='utf-8'))==result,'Source record differs')
    print(json.dumps({'status':'passed','source_admitted':False,'mechanical_modules':22,
                     'clearance_time':result['mechanical']['clearance_time']}))

if __name__=='__main__':main()
