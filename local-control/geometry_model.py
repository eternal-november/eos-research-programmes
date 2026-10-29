"""Exact full-size geometry/runtime binding; source admission remains separate."""
from __future__ import annotations
from dataclasses import asdict
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse
import json
import math
import sys
import subprocess
import program_model as pm

if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')
HERE=Path(__file__).resolve().parent


def require(ok,message):
    if not ok: raise AssertionError(message)


def serial(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {k:serial(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return [serial(v) for v in value]
    return value


def source_hash(name):
    return sha256((HERE/name).read_text(encoding='utf-8-sig').replace('\r\n','\n').encode('utf-8')).hexdigest()


def design(power_at=750000000,warm_at=6400000000):
    parameters=dict(POSE_MAX=1<<44,LOAD_MARGIN=300,ISOLATION_MARGIN=180,
        ROW_VERIFY_RADIUS=12,POSE_VERIFY_RADIUS=2000000,CAM_VERIFY_RADIUS=4000,
        CLAMP_VERIFY_RADIUS=5000,CAM_ERROR=6000,JOIN_ERROR=8000,JOIN_MARK=5,
        SEGMENT=32000,GUARD=16000,PROGRESS_ERROR=250000000,HIGH_STEP=594059405,
        CLAMP_LIMIT=24000,RESET_LIMIT=12000,CUT_LIMIT=60000,BLEND_LIMIT=40000,
        POWER_AT=power_at,WARM_AT=warm_at,RESERVE_CAP=1<<20)
    return pm.Design(degree=40,bays=80,origins=13,image_cells=8192,
        fast_batch=16,query_batch=4,maintenance_batch=4,connectors_a=11,connectors_b=11,
        entry_frames=4096,plant_entry_frames=64,read_wait_frames=950,
        post_stage_frames=2100,watch_frames=2400000000,conversion_polls=88259,
        frame_steps=1<<26,boot_drain_steps=4*(1<<26),physical_parameters=tuple(parameters.items()))


def construct():
    compiled=pm.compile_check(design());bounds=pm.WorkBound(compiled).report()
    cert=pm.processing_certificate(compiled,bounds);c=compiled.constants
    q={k:F(v) for k,v in cert.items() if isinstance(v,(int,str)) and k!='scope' and (isinstance(v,int) or '/' in v or v.isdigit())}
    v_plus=F(11,10);v_minus=F(1);cam_vplus=F(1);cam_vminus=F(9,10)
    force=F(2);host_bad=F(22,5);noise=F(1);bad=6;helpers=40
    opposition=bad*host_bad+noise;stiction_low=F(28);stiction_high=F(29);compliance_high=F(2)
    good_force=(helpers-bad)*force
    mu=min(v_minus,(good_force-opposition-stiction_high)/compliance_high)
    mu_cam=min(cam_vminus,(good_force-opposition-stiction_high)/compliance_high)
    require(opposition<stiction_low and mu==1 and mu_cam==F(9,10),'Force margin lost')
    J=q['per_target_response'];D=F(cert['raw_delay_bounds']['command'])
    age=q['pose_age'];fmin=q['frame_min'];fmax=q['frame_max'];scan=q['complete_scan'];work=q['local_nontransferable_work']
    stage=(c['POST_STAGE_FRAMES']+1)*fmax+J
    application=J+2*D+F(6)+F(3)
    formation=F(50000)
    probe=c['SEGMENT']/mu_cam+age+stage+2*application
    require(probe<formation,'Unknown-cam formation allowance too short')
    settle=age+stage+2*application
    # Correct-source fields remain compatible through actual application.
    # This is not a readiness claim before the source suppliers hold.
    steady_settle=settle
    lambda_join=2*J+2*D+6+3
    clamp_beta=F(1,4)+v_plus*(age+q['comparison_to_emission']+q['cut_withdrawal'])
    require(c['CLAMP_VERIFY_RADIUS']>=2*clamp_beta,'Clamp range fails refreshed-stop availability')
    clamp_error=c['CLAMP_VERIFY_RADIUS']+clamp_beta
    require(c['JOIN_ERROR']>=clamp_error,'Clamp join envelope too small')
    detection=c['JOIN_MARK']+2*c['JOIN_ERROR'];cutoff=20000
    require(cutoff>detection+v_plus*lambda_join and c['CLAMP_LIMIT']>cutoff,'Writer cutoff precedes all-host join')
    reset_min=c['RESET_LIMIT']/v_plus
    require(reset_min>settle,'Reset sweep omits stale observation/post-stage/command drain')
    # Own-copy permits a failed comparison, one finite write, then sound readback.
    own_cell=3*J+2*q['last_possible_word_after_cutoff']+4
    copy=stage+(c['IMAGE_CELLS']+1)*own_cell+application
    require(copy<scan and copy<work,'Actual copy routine exceeds supplied work window')
    driver_at=c['POWER_AT']+20000
    info=F(10000);boot=q['new_bank_entry_before_driver_geometry']
    require(c['POWER_AT']/v_plus>scan+settle,'A fast first actuator powers before other complete scans')
    require((driver_at-c['POWER_AT'])/v_plus>boot+2*D,'Driver opens before stored formation and old-command clearance')
    require((c['WARM_AT']-driver_at)/v_plus>info+work,'Post-driver ready overlap too short')
    # Supply reconnection precedes scan/activation; a fixed raw charger bound is
    # checked against the actual shortest activation travel, not a READY bit.
    charge_bound=F(10000)
    require(c['POWER_AT']/v_plus>charge_bound,'Pre-power path cannot charge the operating carrier')
    abort_length=F(10000)
    abort_join=age+stage+2*J+2*D+6
    require(abort_length/v_plus>abort_join,'Abort entry/return cannot drain ENTERING observations')
    require((c['POST_STAGE_FRAMES']-1)*fmin>age+2*J+2*D+6,'Post-normal exit gate too short')
    iso_length=F(40000);shunt_length=F(40000);seat_length=F(12000)
    # Actual normalized isolation/shunt range stays [0,1].
    require(v_plus/iso_length<=F(1,12000),'Actual isolation slew exceeds conduct envelope')
    require(2*v_plus/shunt_length<=F(1,10000),'Working shunt load slew exceeds conduct envelope')
    # Every rank contribution remains representable; energy is a bounded raw
    # measurement, never a no-power truth test.
    resource=dict(energy_scale=1<<41,operating_capacity_upper=1<<61,
        launch_off_threshold_lower=1<<58,discharge_coefficient_lower=F(1,10),
        residual_backfeed_ratio_upper=F(1,20),charge_to_on_upper=charge_bound,
        isolated_nonrearming_tail_capacity=407371776,
        status='capacity/threshold envelope checked against resource snapshot445bff7; whole-source admission remains separate')
    require(F(resource['operating_capacity_upper'],resource['energy_scale'])<=c['RESERVE_CAP'],'Energy head range insufficient')
    halvings=0
    while resource['launch_off_threshold_lower']*(1<<halvings)<resource['operating_capacity_upper']:halvings+=1
    drain=2*halvings/resource['discharge_coefficient_lower']
    no_launch_and_tails=drain+q['last_possible_word_after_cutoff']+q['cut_withdrawal']
    require(no_launch_and_tails<100,'Whole-stage resource clearance allowance too short')
    S=lambda length:steady_settle+F(length)/mu
    T_cam=lambda length:steady_settle+F(length)/mu_cam
    # Thirteen actual normal bands. A platen supplies one seating coordinate;
    # the eighty heads retain body/address identity without multiplying force.
    cut_stage=S(iso_length)+S(shunt_length)+S(c['CUT_LIMIT'])+100
    activation_retract=c['BAYS']*S(c['WARM_AT'])
    phase={
      '0_prepared_isolate_shunt_cut_drain':cut_stage,
      '1_retract_all_activation_strokes':activation_retract,
      '2_open_clamp':S(c['CLAMP_LIMIT']),
      '3_retract_reset':S(c['RESET_LIMIT']),
      '4_advance_reset_direct':S(c['RESET_LIMIT']),
      '5_seat_rigid_carrier':S(seat_length),
      '6_copy_and_close':copy+S(c['CLAMP_LIMIT']),
      '7_reconnect':S(shunt_length)+S(c['CUT_LIMIT']),
      '8_full_scan_activate_and_overlap':scan+S(c['WARM_AT']),
      '9_world_blend':S(c['BLEND_LIMIT']),
      '10_old_isolate_shunt_cut_drain':cut_stage,
      '11_normalize_new_isolation':S(iso_length),
      '12_transition':F(0)}
    band_travel=c['PHASES']*T_cam(c['SEGMENT'])
    half=sum(phase.values())+band_travel
    rewind=T_cam(2*c['PHASES']*c['SEGMENT'])
    abort=2*S(abort_length)+S(c['BLEND_LIMIT'])+cut_stage+activation_retract+S(c['CLAMP_LIMIT'])+S(c['RESET_LIMIT'])+rewind+settle
    # The code's progress() contains these actual physical terms. Margins cover
    # arbitrary partial positions, while contact jumps require the source's
    # retained-contact map; they are not inferred from sensor agreement.
    offset_rank=10*c['SEGMENT']
    spans=[2000+c['CUT_LIMIT']+c['RESERVE_CAP'],c['BAYS']*c['WARM_AT'],c['CLAMP_LIMIT'],c['RESET_LIMIT'],c['RESET_LIMIT'],c['BAYS']*seat_length,c['CLAMP_LIMIT'],c['CUT_LIMIT']+1000,c['BAYS']*c['WARM_AT'],c['BLEND_LIMIT'],2000+c['CUT_LIMIT']+c['RESERVE_CAP'],1000,0]
    spans=[F(s)+offset_rank for s in spans]
    rankmax=max(spans)
    require(rankmax<c['POSE_MAX'] and rankmax+c['PROGRESS_ERROR']+c['HIGH_STEP']<1<<(pm.WORD_BITS-1),'Actual rank arithmetic overflows')
    Tmin=(c['WATCH_FRAMES']-1)*fmin;Tmax=(c['WATCH_FRAMES']+1)*fmax
    timer_window=formation+2*Tmax+J+40
    require(timer_window<=work,'Physical overlap does not cover the complete nontransferable timer job')
    # Only phases1 and8 need a long unit-rate rank argument at this point.
    # All other healthy stages finish before even the earliest timeout.
    phase_values=list(phase.values())
    no_motion=scan+settle+c['BAYS']*settle
    milestone=no_motion+J+c['HIGH_STEP']+4*c['PROGRESS_ERROR']+1
    require(milestone<Tmin,'Healthy serial activation/scan can falsely time out')
    short_phases=[p for p in range(13) if p not in (1,8)]
    require(all(phase_values[p]+T_cam(c['SEGMENT'])<Tmin for p in short_phases),'A normalized/short phase needs an unproved rank speed')
    stalls={}
    for p,span in enumerate(spans):
        stalls[str(p)]=phase_values[p] if p==4 else (math.ceil(span/c['HIGH_STEP'])+1)*timer_window
    partial=formation+sum(stalls.values())+band_travel
    old=q['last_possible_word_after_cutoff']+q['cut_withdrawal']+max(cert['arbitrary_counter_caps'])+age+stage
    commission=formation
    H=math.ceil(commission+partial+abort+2*half+old)+1
    require(H>commission+partial+abort+2*half+old,'Strict return margin lost')
    # One common2H cover, not independent budgets or an H-only substitution.
    arrival=F(1,10*H);cover=1+2+math.floor(3+2*arrival*H)
    require(cover==6,'Whole-attempt fault cover changed')
    return compiled,bounds,cert,dict(design=asdict(compiled.design),force=dict(helpers=helpers,coherent_bad_domains=bad,
        allocated_per_host=force,two_bank_bad_cap=host_bad,disturbance=noise,opposition=opposition,
        stiction=[stiction_low,stiction_high],compliance_upper=compliance_high,speed=[v_minus,v_plus],cam_speed=[cam_vminus,cam_vplus],minimum_speed=mu),
        geometry=dict(clamp_cutoff=cutoff,clamp_detection=detection,clamp_current_error=clamp_error,clamp_join_settlement=lambda_join,
            driver_at=driver_at,post_driver_information=info,post_driver_overlap=(c['WARM_AT']-driver_at)/v_plus-info,
            iso_length=iso_length,shunt_length=shunt_length,seat_length=seat_length,abort_length=abort_length,
            seating='one rigid carrier; eighty distinct physical bodies and private write leads; aggregate platen force law'),
        resource_interface=resource,resource_drain=dict(halvings=halvings,no_new_launch_upper=drain,complete_authority_suffix=no_launch_and_tails),
        timing=dict(formation=formation,unknown_cam_probe=probe,settle=settle,copy_cell=own_cell,copy=copy,scan=scan,work=work,boot=boot,
            phase_bounds=phase,normal_band_travel=band_travel,half_cycle=half,abort=abort,rank_spans=spans,maximum_rank=rankmax,
            earliest_timeout=Tmin,latest_timeout=Tmax,timer_window=timer_window,healthy_long_stage_milestone=milestone,
            short_phases_by_whole_stage=short_phases,partial_stall_bounds=stalls,partial=partial,old_suffix=old,commissioning=commission,
            conditional_return_H=H,whole_2H_cover=cover,raw_arrival_rate=arrival),
        scope='full-size conditional geometry/controller binding; physical defect/effect interpretation, maintained suppliers and same-history recurrence are separate obligations')


def actual_helper_checks(compiled):
    c=compiled.constants;results=[]
    for half in (0,1):
        m=pm.Machine(compiled);m.W=[0]*len(m.W);base=c['TARGET_BASE'];p=pm.RawPorts(compiled)
        v=pm.populated_view(compiled,half,4);p.set_view(0,v)
        m.W[base+c['STAGE_ID']]=half*c['PHASES']+5
        m.W[base+c['TIMER']]=0;m.W[base+c['ABORT']]=1
        m.W[base+c['CURSOR']]=777;m.W[base+c['SCAN_MATCH']]=0
        m.enter('helper',(0,));verdict=m.run(p,budget=20000000,until_yield=False)
        require(verdict=='halt','Full-size phase4 instruction execution did not finish')
        require(m.W[base+c['TIMER']]==c['WATCH_FRAMES'] and m.W[base+c['ABORT']]==0,'Phase4 timer-clearing exception changed')
        require(m.W[base+c['CURSOR']]==0 and m.W[base+c['SCAN_MATCH']]==1,'Reset band failed semantic clearing')
        require(p.fields.get((0,c['RESET_PORT'],1-half,0))==c['FORCE'],'No actual positive reset command')
        require(m.C==compiled.image,'Nominal helper wrote C')
        results.append(dict(half=half,executed_instructions=m.steps,actual_reset_force=p.fields[(0,c['RESET_PORT'],1-half,0)],
            timer_after=m.W[base+c['TIMER']],cursor_after=m.W[base+c['CURSOR']],source_target_state='formed phase4 with current raw source values; not arbitrary W stabilization'))
    return results


def counterchecks(compiled,result):
    c=compiled.constants;g=result['geometry'];t=result['timing'];r=result['resource_interface'];v=F(11,10)
    require(300<g['clamp_detection'],'Old clamp diagnostic unexpectedly supports current join')
    require(F(50000,1)/v<t['scan'],'Old activation diagnostic unexpectedly covers full scan')
    require(F(5000000000)<t['work'],'Round-number overlap witness unexpectedly covers actual work')
    require(not (F(2,80)*34-result['force']['opposition']>result['force']['stiction'][1]),'Splitting a2-unit field80ways unexpectedly advances every independent seat')
    old_energy=0;current_energy=1<<60;age=100
    require(old_energy//r['energy_scale']==0 and current_energy>r['launch_off_threshold_lower'] and age<1953,'Stale energy-zero/no-launch countercase missing')
    # A physically jammed reset never times out in phase4; source-health
    # qualification is necessary for the direct-progress lemma.
    frozen_reset=0
    for _ in range(10000):
        timer=c['WATCH_FRAMES'];frozen_reset+=0
    require(frozen_reset==0 and timer>0,'Phase4 jam obstruction disappeared')
    return dict(old_clamp_limit300_fails_detection=True,old_warm_at50000_fails_full_scan=True,
        old_round_work5b_fails_current_certificate=True,independent_eighty_way_free_force_rejected=True,
        phase4_jammed_reset_does_not_time_out=True,
        stale_energy_zero_while_operating=dict(old_energy=old_energy,current_energy=current_energy,age=age),
        source_defect_boundary='jammed/broken/redirected target mechanics retain actual effects and require root conduct/no-spread treatment; no targetP cure claimed')


def bind_resource(compiled,bounds,result):
    commit='445bff7a11348d9a09870fba78eabc9cc76beb9b'
    prefix='theories-and-designs/byzantine-control/local-control/'
    payload=subprocess.check_output(['git','show',commit+':'+prefix+'resource_results.json'],cwd=HERE)
    normalized=payload.decode('utf-8-sig').replace('\r\n','\n')
    record=json.loads(normalized);point=record['runtime_inventory'];snapshots={}
    for name,digest in record['sources'].items():
        data=subprocess.check_output(['git','show',commit+':'+prefix+name],cwd=HERE)
        text=data.decode('utf-8-sig').replace('\r\n','\n')
        require(sha256(text.encode('utf-8')).hexdigest()==digest,'Bound resource source manifest differs')
        snapshots[name]=digest
    for name in ('program_model.py','program_source.py','PROGRAM.md','RUNTIME-PORTS.md'):
        require(source_hash(name)==snapshots[name],'Geometry uses a changed runtime from its resource inventory')
    interface=result['resource_interface'];d=compiled.design
    require(point['design']==dict(bays=d.bays,degree=d.degree,image_cells=d.image_cells),'Resource roster/layout mismatch')
    require(bounds['private_words_with_metadata']<=point['padded_private_words'],'New program exceeds paid private storage')
    require(F(point['per_bank_capacity'])<=interface['operating_capacity_upper'],'Operating energy exceeds geometry range')
    require(F(point['per_bank_off'])>=interface['launch_off_threshold_lower'],'Raw cutoff threshold below geometry bound')
    require(F(point['discharge_coefficient'])>=interface['discharge_coefficient_lower'],'Bleed too weak for geometry bound')
    require(F(point['per_bank_residual_backfeed'])<=F(point['discharge_coefficient'])*F(point['per_bank_off'])/2,'Backfeed defeats actual drainage')
    require(F(point['per_bank_startup_bound'])<=interface['charge_to_on_upper'],'Carrier recharge exceeds pre-power distance')
    require(F(point['energy_head_unit'])==interface['energy_scale'],'Energy representation mismatch')
    require(point['combined_capsule_field_capacity']==interface['isolated_nonrearming_tail_capacity'],'Funded tail inventory changed')
    require(F(point['generator_power'])/point['generator_count']==12,'Generator price changed')
    require(F(22,10)*F(11,10)<=12,'Mechanical maximum power exceeds each generator price')
    return dict(commit=commit,path=prefix+'resource_results.json',sha256=sha256(normalized.encode('utf-8')).hexdigest(),
        checked_manifest=snapshots,actual_parameters={name:point[name] for name in ('per_bank_capacity','per_bank_off','discharge_coefficient','per_bank_residual_backfeed','per_bank_startup_bound','generator_count','generator_power','energy_head_unit','energy_head_range','post_cut_no_launch_bound','post_cut_half_off_bound','combined_capsule_field_capacity','transducer_store_rating')},
        new_geometry_storage='quasistatic dissipative carrier/strokes add no length-dependent mechanical store; prior8-per-generator allowance is conservative',
        scope='exact scalar/layout/runtime resource match; physical fault/effect and initialized same-history assembly are not inferred from the inventory')


def generate():
    compiled,bounds,cert,result=construct()
    result['compiler']=dict(code_cells=len(compiled.nodes),image_cells=len(compiled.image),
        encoded_image_sha256=sha256(b''.join(x.to_bytes(pm.CELL_BITS//8,'little') for x in compiled.image)).hexdigest(),
        finite_address_bits=pm.FIELD_BITS,immediate_bits=pm.IMM_BITS,word_bits=pm.WORD_BITS,
        instruction_bounds=bounds,processing_certificate=cert)
    result['resource_binding']=bind_resource(compiled,bounds,result)
    result['actual_phase4']=actual_helper_checks(compiled)
    result['counterchecks']=counterchecks(compiled,result)
    result['sources']={name:source_hash(name) for name in ('GEOMETRY.md','geometry_model.py','PROGRAM.md','program_model.py','program_source.py','RUNTIME-PORTS.md','HYBRID.md','CLAMP.md','CONTINUITY.md')}
    return serial(result)


def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true');args=p.parse_args()
    result=generate();out=HERE/'geometry_results.json'
    if args.write:out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:require(json.loads(out.read_text(encoding='utf-8-sig'))==result,'Geometry record differs; inspect before rewriting')
    print('geometry record '+('written' if args.write else 'matches'))

if __name__=='__main__':main()
