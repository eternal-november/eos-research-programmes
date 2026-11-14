"""Changed threshold geometry: exact joins and actual instruction checks.

The source-local phase and time arithmetic is conditional on the named physical,
information, interval and fault maps. It does not import the old winning theorem.
"""
from __future__ import annotations
import argparse
from dataclasses import asdict
from fractions import Fraction as Q
from hashlib import sha256
import json
from math import ceil
from pathlib import Path
import sys
import publication_timing
import pulse_model
import threshold_design
import threshold_program_model as program

HERE=Path(__file__).resolve().parent
need=program.need
if sys.flags.optimize or sys.version_info[:2]!=(3,12):
    raise RuntimeError("Unoptimized Python 3.12 required")


def serial(value):
    if isinstance(value,Q):return str(value)
    if isinstance(value,dict):return {str(k):serial(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return [serial(v) for v in value]
    return value


def joins(compiled,bounds,publication,pulse):
    c=compiled.constants;physical=threshold_design.physical_parameters(compiled)
    mu_cpu=Q(2**26);fast=Q(101,100);field_wait=physical["field_extra_latency"]
    fmin=Q(c["FRAME_STEPS"])/mu_cpu/fast
    fmax=Q(bounds["padded_frame_upper"])/mu_cpu+c["VECTOR_UPDATES"]*field_wait
    need(fmax==Q(publication["frames"]["max"]) and
         fmin==Q(publication["frames"]["min"]),"Changed design altered frame assumptions")
    J=(ceil(Q(c["DEGREE"],c["MAINT_BATCH"]))+1)*fmax
    age=Q(publication["receipts"]["maintenance"]["singleton_age"])
    need(J==Q(publication["functional"]["per_target"]),"Visit count disagreement")
    post=c["POST_STAGE_FRAMES"];watch=c["WATCH_FRAMES"]
    stage=(post+1)*fmax+J
    application=J+2*3+6+3
    settle=age+stage+2*application
    vmax=physical["stroke_max"];cam_min=physical["cam_lower_candidate"]
    opposition=Q(55,2)+physical["extra_reaction"]
    surplus=68-opposition-29
    mu=min(Q(1),surplus/2)
    need(opposition<28 and mu==1 and surplus>11,"Conditional force margins failed")
    formation=physical["local_recognition_allocation"]
    probe=Q(c["SEGMENT"])/cam_min+settle
    need(probe<formation,"Unknown-cam recognition allocation failed")
    tmin=(watch-1)*fmin;tmax=(watch+1)*fmax
    timer_job=formation+2*tmax+J+40
    # Boot includes the current publication calculation's 16-instruction reserve.
    boot=Q(bounds["boot_padded_upper"]+16)/mu_cpu
    need(boot==Q(publication["initialization"]["boot"]),"Boot reserve mismatch")
    scan=(ceil(Q(c["VECTOR_SLOTS"],c["VECTOR_UPDATES"]))+1)*fmax
    pool=pulse["inhibited_initial_pool_drain_refill"]
    freshness=pulse["stable_setting_to_field"]
    first=pulse["sample_max"]+Q(1)+Q(1000)
    prepare=boot+scan+pool
    u=Q(1,1000)/c["IMAGE_BITS"]
    bad_field=6*Q(202,100)*u
    disturbance=Q(1,4)*u
    sibling=34*Q(1,100)*u
    unattended=bad_field+disturbance+sibling
    threshold=13*u
    write_surplus=34*Q(99,100)*u-bad_field-disturbance-threshold
    need(unattended<threshold and write_surplus>0,"Threshold field margins failed")
    write=2/write_surplus
    full_preparation=prepare+freshness+write
    cutoff_min=physical["clamp_cutoff"]/vmax
    enable_min=physical["vector_driver_offset"]/vmax
    # Latest engagement is a separate conditional rank/progress bound.
    enable_max=settle+physical["vector_driver_offset"]/mu
    vector_ready_max=enable_max+first
    overlap=(physical["warm_at"]-physical["vector_driver_at"])/vmax-first
    old_overlap=(Q(6400000000)-physical["vector_driver_at"])/vmax-first
    two_watch_only=2*watch*fmax
    need(old_overlap<two_watch_only,"Old failed overlap comparison disappeared")
    need(overlap>timer_job and overlap>scan,"New complete job overlap failed")
    need(prepare<enable_min,"Data/pool formation can be overtaken by engagement")
    need(full_preparation<cutoff_min,"Actual threshold corridor is too short")
    # This stronger arithmetic comparison carries all known vector preparation
    # twice; it is not needed when readiness boundaries are mapped correctly.
    repeated_preparation_job=timer_job+prepare+freshness
    need(repeated_preparation_job<overlap,"Known preparation terms exhaust overlap")
    all_emitter=age+2*(post+1)*fmax+3*J+15
    reset_min=Q(c["RESET_LIMIT"])/vmax
    abort_join=age+stage+2*J+12
    abort_min=Q(10000)/vmax
    post_min=(post-1)*fmin
    post_need=age+2*J+12
    need(all_emitter<reset_min,"Phase4 sweep cannot cover conditional clearing")
    need(abort_join<abort_min and post_need<post_min,"Abort/exit age join failed")
    # Existing instructions select one body, so long ACT progress is one stroke.
    need(c["BAYS"]==1,"One-body progress supplier was replaced")
    S=lambda length:settle+Q(length)/mu
    C=lambda length:settle+Q(length)/cam_min
    clear=physical["bank_clearance_candidate"]
    cut=S(40000)+S(40000)+clear+S(c["CUT_LIMIT"])+physical["energy_clearance_candidate"]
    phase_names=(
        "0_isolate_shunt_cut_drain","1_retract_one_activation",
        "2_open_clamp","3_retract_reset","4_advance_reset_direct",
        "5_seat_one_body","6_threshold_write_and_close","7_reconnect",
        "8_activate_and_overlap","9_blend","10_old_cut_drain",
        "11_normalize","12_transition")
    phase_values=(cut,S(c["WARM_AT"]),S(c["CLAMP_LIMIT"]),S(c["RESET_LIMIT"]),
        S(c["RESET_LIMIT"]),S(12000),S(c["CLAMP_LIMIT"]),
        S(40000)+S(c["CUT_LIMIT"]),S(c["WARM_AT"]),S(c["BLEND_LIMIT"]),
        cut,S(40000),Q(0))
    phases=dict(zip(phase_names,phase_values))
    short=[i for i in range(13) if i not in (1,8)]
    need(all(phase_values[i]+C(c["SEGMENT"])<tmin for i in short),
         "A short stage lacks a sufficient whole-stage timeout bound")
    h=c["HIGH_STEP"];error=c["PROGRESS_ERROR"]
    no_motion=prepare+freshness+2*settle
    milestone=no_motion+J+(h+4*error+1)/mu
    need(milestone<tmin,"Healthy ACT milestone can outlast its timer")
    offset_rank=10*c["SEGMENT"]
    spans=[2000+c["CUT_LIMIT"]+c["RESERVE_CAP"],c["WARM_AT"],
        c["CLAMP_LIMIT"],c["RESET_LIMIT"],c["RESET_LIMIT"],12000,
        c["CLAMP_LIMIT"],c["CUT_LIMIT"]+1000,c["WARM_AT"],c["BLEND_LIMIT"],
        2000+c["CUT_LIMIT"]+c["RESERVE_CAP"],1000,0]
    spans=[Q(x)+offset_rank for x in spans]
    need(max(spans)<c["POSE_MAX"] and max(spans)+h+error<2**255,
         "Rank representation overflow")
    stalls={str(i):(phase_values[i] if i==4 else
                   (ceil(spans[i]/h)+1)*timer_job) for i in range(13)}
    band_travel=13*C(c["SEGMENT"])
    half=sum(phase_values)+band_travel
    partial=formation+sum(stalls.values())+band_travel
    abort=(2*S(10000)+S(c["BLEND_LIMIT"])+cut+S(c["WARM_AT"])+
           S(c["CLAMP_LIMIT"])+S(c["RESET_LIMIT"])+C(2*13*c["SEGMENT"])+settle)
    old=(pulse["cutoff_to_zero"]+
         publication["receipts"]["maintenance"]["arbitrary_counter_cap"]+
         age+stage)
    # Reconstruction startup is separate from early world feedback; no claim
    # is made that fallback can safely hold the plant for this longer interval.
    reconstruction_startup=formation+prepare+freshness
    sequence=reconstruction_startup+partial+abort+2*half+old
    H=Q(2*10**13);rate=Q(1,104548602495950)
    raw_cover=1+2+(3+2*rate*H).__floor__()
    need(sequence<H and raw_cover==6,"Illustrative H/raw-token arithmetic failed")
    # A near-cutoff interrupted state cannot inherit the full fresh corridor.
    remaining_from_partial=Q(1)/vmax
    need(remaining_from_partial<freshness+write,
         "Partial-entry timing obstruction disappeared")
    return dict(
        scope="conditional local timing/phase arithmetic; no achieved-return or work certificate",
        physical_inputs=physical,force=dict(opposition=opposition,surplus=surplus,
            minimum_stroke_speed=mu,hard_extra_reaction_is_open_supplier=True),
        frames=dict(min=fmin,max=fmax),polling=J,post_stage=stage,
        ordinary_application=application,ordinary_settle=settle,
        unknown_cam_probe=probe,recognition_allocation=formation,
        watchdog=dict(earliest=tmin,latest=tmax,two_watch_only=two_watch_only,
            complete_timer_job=timer_job,rank_quantum=h,rank_error=error,
            ACT_no_motion_allocation=no_motion,ACT_milestone=milestone,
            ACT_milestone_slack=tmin-milestone),
        vectors=dict(boot=boot,scan=scan,pool_entry=pool,freshness=freshness,
            first_after_route_engagement=first,data_and_pool_prepare=prepare,
            amplitude=u,threshold=threshold,unattended_bound=unattended,
            write_surplus=write_surplus,write_time=write,
            full_fresh_write_preparation=full_preparation),
        geometry=dict(earliest_cutoff=cutoff_min,
            cutoff_slack=cutoff_min-full_preparation,
            earliest_vector_engagement=enable_min,
            data_before_enable_slack=enable_min-prepare,
            latest_engagement_after_power=enable_max,
            latest_useful_vector_after_power=vector_ready_max,
            latest_bounds_require_actual_progress=True,
            overlap_after_first_useful_vector=overlap,
            timer_overlap_slack=overlap-timer_job,
            overlap_after_recounting_preparation=overlap-repeated_preparation_job,
            old_overlap=old_overlap,old_two_watch_shortage=two_watch_only-old_overlap,
            old_failure_is_sufficient_inequality_not_impossibility=True),
        local_clearing=dict(two_post_wait_all_emitter_bound=all_emitter,
            reset_sweep_min=reset_min,reset_slack=reset_min-all_emitter,
            abort_join=abort_join,abort_stroke_min=abort_min,
            abort_slack=abort_min-abort_join,post_normal_min=post_min,
            post_normal_required=post_need,post_normal_slack=post_min-post_need,
            scope="formed helper histories with current-age normal/phase4 predicates; arbitrary W excluded"),
        phase_bounds=phases,short_phases=short,
        max_short_phase_with_band=max(phase_values[i]+C(c["SEGMENT"]) for i in short),
        rank_spans=spans,partial_bin_multipliers={
            str(i):ceil(spans[i]/h)+1 for i in range(13) if i!=4},
        partial_stall_allocations=stalls,band_travel=band_travel,
        fresh_half_time=half,partial_time_allocation=partial,
        abort_time_allocation=abort,old_suffix_allocation=old,
        reconstruction_startup_allocation=reconstruction_startup,
        complete_sequence_allocation=sequence,candidate_H=H,
        candidate_H_slack=H-sequence,raw_rate=rate,raw_token_cover=raw_cover,
        raw_token_cover_is_not_seven_slot_certificate=True,
        interrupted_near_cutoff=dict(remaining_time=remaining_from_partial,
            freshness_and_write=freshness+write,
            scope="failure of fresh-entry certificate; joint reachability/mission counterexample not asserted"),
        work_bounds_supplied=False,all_mode_source_map_complete=False)


def special_helper_checks(isa,c,b,Ports):
    k=c.constants;out=[]
    for half in (0,1):
        ports=Ports(c);m,view=program.helper_fixture(isa,c,ports,half,4)
        base=k["TARGET_BASE"];m.W[base+k["ABORT"]]=1;m.W[base+k["TIMER"]]=0
        m=program.call(isa,c,ports,"helper",(0,),b["instruction_upper_bounds"]["helper"]+100,m)
        need(m.W[base+k["ABORT"]]==0 and
             m.W[base+k["TIMER"]]==k["WATCH_FRAMES"],"Phase4 clearing exception failed")
        need(ports.fields[(0,k["RESET_PORT"],1-half,0)]==k["FORCE"],
             "Phase4 emitted no actual reset command")
        out.append(dict(half=half,phase=4,instructions=m.steps,
                        reset_after_existing_abort=True))
    # Direct local routine projection of a stable-rank expired timer.
    ports=Ports(c);m,view=program.helper_fixture(isa,c,ports,0,6)
    base=k["TARGET_BASE"]
    m=program.call(isa,c,ports,"read_view",(0,),b["instruction_upper_bounds"]["read_view"]+100,m)
    cam=m.W[base+k["VIEW"]+k["CAM"]]
    m=program.call(isa,c,ports,"progress",(base,0,6,cam%k["SEGMENT"]),
                   b["instruction_upper_bounds"]["progress"]+100,m)
    rank=m.result()
    m.W[base+k["WATCH_HALF"]]=1;m.W[base+k["LAST_PHASE"]]=6
    m.W[base+k["HIGH"]]=rank+k["PROGRESS_ERROR"]
    m.W[base+k["RANK_VALID"]]=1;m.W[base+k["TIMER"]]=0
    m.W[base+k["ABORT"]]=0
    m=program.call(isa,c,ports,"helper",(0,),b["instruction_upper_bounds"]["helper"]+100,m)
    need(m.W[base+k["ABORT"]]==1,"Expired stable-rank timer did not abort")
    event=next(e for e in reversed(ports.events) if e[0]=="command")
    need(event[5]==k["FORCE"],"Abort request absent from actual command")
    return dict(phase4=out,expired_timer_aborts=True,
                timer_fixture_scope="stable rank/private state fixture; no claim that a healthy moving source stalls this way")


def generate(full=True):
    isa=program.load_isa()
    old=program.production_design(isa)
    d=threshold_design.design(isa);c=program.compile_program(isa,d)
    b=program.bounds(isa,c);Ports=program.ports_class(isa)
    old_compiled=program.compile_program(isa,old);old_bounds=program.bounds(isa,old_compiled)
    need(b==old_bounds,"Changed constants altered a consumed syntax bound")
    need(c.image!=old_compiled.image,"Design did not change the installed image")
    need(len(c.nodes)<=d.image_cells and b["padded_frame_upper"]<2**64
         and b["boot_padded_upper"]<2**64,"Finite image/counter bounds failed")
    publication=publication_timing.generate()
    need(json.loads((HERE/"publication_timing_results.json").read_text())==publication,
         "Publication record is stale")
    pulse=pulse_model.construct(pulse_model.base_design())
    need(pulse_model.serial(pulse_model.generate())==
         json.loads((HERE/"pulse_results.json").read_text()),"Pulse record is stale")
    arithmetic=joins(c,b,publication,pulse)
    print("Checking changed-design helper, guard, scanner and entry paths",flush=True)
    local=program.local_checks(isa,c,b,Ports)
    scanner=program.scanner_checks(isa,c,b,Ports)
    special=special_helper_checks(isa,c,b,Ports)
    fixtures=program.fixture_frames(isa,d,Ports)
    boot=program.production_boot_prefix(isa,c,b,Ports)
    paced=None
    if full:
        print("Executing one complete changed-design paced frame",flush=True)
        paced=program.production_frame(isa,c,b,Ports)
    files=("threshold_design.py","threshold_geometry.py","THRESHOLD-GEOMETRY.md",
        "threshold_program_source.py","threshold_program_model.py","THRESHOLD-PROGRAM.md",
        "publication_timing.py","publication_timing_results.json","THRESHOLD-PUBLICATION.md",
        "pulse_model.py","pulse_results.json","PULSE-FIELDS.md","constructors.py","THRESHOLD-JOIN.md")
    return serial(dict(
        status="first-pass changed-design instruction and conditional geometry evidence",
        scope="local programme/phase/time join; physical and all-history source realization remains open",
        base=program.BASE,frozen_isa_sha256=isa.source_hash,
        frozen_geometry_sha256=program.hash_text(program.frozen("geometry_results.json")),
        old_design=asdict(old),changed_design=asdict(d),
        old_image_sha256=program.hash_text(json.dumps(old_compiled.image)),
        changed_image_sha256=program.hash_text(json.dumps(c.image)),
        code_cells=len(c.nodes),registers=c.next_register,working_words=c.constants["DATA_WORDS"],
        syntax_bounds_unchanged=True,bounds=b,arithmetic=arithmetic,
        local_checks=local,special_checks=special,scanner=scanner,
        fixture_frames=fixtures,production_boot_prefix=boot,
        production_boot_fully_executed=False,changed_paced_frame=paced,
        complete_paced_frame_executed=full,
        sources_sha256_lf={name:program.digest(HERE/name) for name in files},
        python_version=sys.version,baseline_global_winning_imported=False,
        open_suppliers=[
            "same-history seven-slot and six-execution-host support; two paired islands can violate the former",
            "actual reaction/force, threshold-cell and pulse/native-operation source laws",
            "all-mode physical gate/event and forced-boundary map",
            "fresh zero-entry, resident-writer exclusion and old destinations",
            "continuous compatible host fields across bank handover",
            "guarded access, source-reachable interrupted-state and all-emitter map",
            "complete shared work, energy, heat, stock and refill account",
            "world/tracker/service proof and actual RP3 common-response pair",
            "generic-core all-history assembly and independent verification"],
        physical_source_admitted=False,achieved_return=False,program_completion=False))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write",action="store_true")
    mode.add_argument("--check",action="store_true")
    mode.add_argument("--quick",action="store_true")
    args=parser.parse_args()
    result=generate(not args.quick)
    path=HERE/"threshold_geometry_results.json"
    if args.write:
        path.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",
                        encoding="utf-8",newline="\n")
    elif args.check:
        need(json.loads(path.read_text(encoding="utf-8"))==result,
             "Changed geometry record differs")
    print("PASS changed-design "+("development checks; full paced frame omitted"
          if args.quick else "bound instruction/conditional geometry evidence"))


if __name__=="__main__":
    main()
