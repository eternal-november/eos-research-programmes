"""Check local normal-orbit control, timing and handover obligations.

Each probe runs compiled ordinary instructions at a declared local fixture.
The numerical phase table requires an actual source-to-edge map.
"""
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import subprocess
import sys

import threshold_program_model as program
import threshold_design as design

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
BASE="4e5c770ff6cc6b2970a16ebe5714e88c90cc04f4"
FROZEN="fb85a7606f45e52d0cd48e023ab9776dd526640c"
PREFIX="theories-and-designs/byzantine-control/"
GATE_SOURCE="ea3b2478d9d3adff7340fda2a40989ab0fdaa257"
INITIAL_SOURCE="089d821dedfdbf6cd03195b07dc5cea12a6c5bc2"


def need(ok,why):
    if not ok:raise ValueError(why)


def bind(commit,part,name):
    path=PREFIX+part+"/"+name
    data=subprocess.check_output(["git","show",commit+":"+path],cwd=REPO).replace(b"\r\n",b"\n")
    need((REPO/path).read_bytes().replace(b"\r\n",b"\n")==data,"Source binding differs: "+name)
    return sha256(data).hexdigest()


def load(path):
    return json.loads(path.read_text(encoding="utf-8"))


def timer_budget(k,age,Fmax,J,band,stage_values,milestone,sample,whole_job,overlap):
    # Each sample wait is attached to a possible actual cam release, not each bit.
    post=(k["POST_STAGE_FRAMES"]+1)*Fmax+J
    crossing=3*(band+sample)+post+2*J+40
    short=max(Q(v) for phase,v in stage_values.items() if int(phase.split("_")[0]) not in (1,8))
    earliest=(k["WATCH_FRAMES"]-1)*Q(100,101)
    need(k["CAM_ERROR"]==6000 and k["SEGMENT"]==32000 and k["GUARD"]==16000,
         "Central phase chart geometry changed")
    # Integer rounding and completion of one whole issued helper included.
    cam_read_error=k["SENSE_ERROR"]+age+Fmax+1
    need(2*cam_read_error+1<k["CAM_VERIFY_RADIUS"],"Genuine center cam rows may fail the test")
    need(k["CAM_VERIFY_RADIUS"]+cam_read_error<k["CAM_ERROR"],"A valid estimate may cross the wrong guard")
    need(k["CAM_ERROR"]+k["CAM_ERROR"]<12500
         and 19500+k["CAM_ERROR"]<k["SEGMENT"]-k["CAM_ERROR"],"Core interval too close to edge")
    needed_core=post+2*J+Fmax
    need(needed_core<7000,"A formed emitter can pass the chart before qualification")
    need(short+crossing<earliest and milestone+crossing<earliest,
         "A last in-band reset can expire before next qualified phase")
    need(overlap>whole_job,"A private timer cannot remain on one actual bank")
    return dict(degree=k["DEGREE"],bodies=k["BAYS"],watch=k["WATCH_FRAMES"],minimum_timeout=earliest,
        cam_read_error_upper=cam_read_error,central_true_offset=[12500,19500],
        minimum_core_dwell=7000,core_qualification_upper=needed_core,
        post_stage=post,visit=J,nominal_band_upper=band,sample_wait=sample,
        transition_allowance=crossing,short_plus_transition=short+crossing,
        short_margin=earliest-short-crossing,long_milestone=milestone,
        long_plus_transition=milestone+crossing,long_margin=earliest-milestone-crossing,
        private_job_window=whole_job,whole_bank_overlap=overlap)


def threshold_cases(i,c,b):
    k=c.constants;P=program.ports_class(i);base=k["TARGET_BASE"];limit=b["instruction_upper_bounds"]["helper"]+100
    fixtures=(("newborn_at_wrap",0,0,0,0,0,0,(0,2400000000,3,0)),
        ("newborn_inner_starts_wait",0,1,None,0,0,0,(0,0,0,2100)),
        ("expired_old_watch_at_wrap",0,0,0,1,12,0,(20,0,1,0)),
        ("sentinel_then_mature_inner",0,1,None,3,0,2,(0,2400000000,1,0)),
        ("opposite_half_mature_inner",1,0,None,1,12,14,(0,2400000000,2,0)))
    results=[]
    for tag,half,phase,cam,wh,last,stage,expected in fixtures:
        ports=P(c);m,v=program.helper_fixture(i,c,ports,half,phase)
        if cam is not None:v[k["CAM"]]=cam;ports.set_view(0,v)
        for field,value in (("WATCH_HALF",wh),("LAST_PHASE",last),("TIMER",0),("STAGE_ID",stage),
                            ("STAGE_WAIT",0),("ABORT",0),("EXITING_ABORT",0)):
            m.W[base+k[field]]=value
        program.call(i,c,ports,"helper",(0,),limit,m)
        event=next(e for e in reversed(ports.events) if e[0]=="command")
        got=(event[5],m.W[base+k["TIMER"]],m.W[base+k["WATCH_HALF"]],m.W[base+k["STAGE_WAIT"]])
        need(got==expected and m.W[base+k["ABORT"]]==0,tag+" does not match literal helper")
        results.append(dict(case=tag,issued=list(event[2:]),timer=got[1],watch_half=got[2],stage_wait=got[3],
                            private_abort=0,instructions=m.steps))
    next_rows=[];work=[];stride=k["TARGET_WORDS"];b1=base+stride
    for mode in ("exiting","entering","missing"):
        ports=P(c);m,v=program.helper_fixture(i,c,ports,0,0)
        ports.set_view(1,i.populated_view(c,1,4));program.fill_permission(c,ports,1)
        m.W[b1+k["STAGE_ID"]]=k["PHASES"]+5
        m.W[base+k["STAGE_ID"]]=27
        before=tuple(m.W[b1:b1+stride])
        if mode!="missing":
            for key,value in (("CAM",0),("MODE",1),("CAM_ENTRY_A",0),("ABORT_FULL",0),("NORMAL_STOP",0)):
                v[k[key]]=value
            ports.set_view(0,v);m.W[base+k["EXITING_ABORT"]]=int(mode=="exiting")
        else:
            for key in list(ports.fast):
                if all(type(a) is int for a in key) and key[2]<3+k["FAST_TARGET_KEYS"]:
                    del ports.fast[key]
        program.call(i,c,ports,"helper",(0,),limit,m)
        need(tuple(m.W[b1:b1+stride])==before,"Focal invocation changed other target's private row")
        used=m.steps
        program.call(i,c,ports,"helper",(1,),limit,m)
        record=next(e for e in reversed(ports.events) if e[0]=="command")
        next_rows.append((tuple(m.W[b1:b1+stride]),tuple(record[2:])))
        work.append((mode,used,m.steps-used))
    need(len(set(next_rows))==1 and next_rows[0][1]==(17,0,20,0,8,0,20),
         "A stuck focal target changed the other target's mature reset command")
    return dict(timer_paths=results,successive_two_target_work=work,target_stride=stride,
                second_row_and_command_agree=True,second_command=next_rows[0][1])


def primary_countercase(isa,c,b):
    k=c.constants;base=k["TARGET_BASE"];m=isa.Machine(c);m.W=[0]*len(m.W);p=isa.RawPorts(c)
    view=isa.populated_view(c,0,9)
    view[k["ACT_POWER_A"]+k["BAYS"]]=1
    p.set_view(0,view)
    for field,value in (("STAGE_ID",10),("ABORT",0),("WATCH_HALF",1),("LAST_PHASE",9),
            ("TIMER",1234567),("PENDING",1),("CELL_KEY",k["BAYS"]*k["IMAGE_CELLS"]),
            ("CELL_WAIT",0),("RANK_VALID",1),("HIGH",2**100)):
        m.W[base+k[field]]=value
    m.enter("helper",(0,))
    need(m.run(p,budget=b["instruction_upper_bounds"]["helper"]+100,until_yield=False)=="halt",
         "Primary phase9 call did not return")
    ev=next(e for e in reversed(p.events) if e[0]=="command")
    need(m.W[base+k["TIMER"]]==1234567 and m.W[base+k["ABORT"]]==1 and ev[5]==20,
         "Missing mature byte verification no longer raises a non-timeout request")
    return dict(phase=9,missing_reply=True,timer=m.W[base+k["TIMER"]],abort=1,
                command=list(ev[2:]),instructions=m.steps,fixture_admitted_as_healthy=False)


def serial(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,(list,tuple)):return [serial(y) for y in x]
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    return x


def generate():
    need(sys.version_info[:2]==(3,12) and __debug__,"Unoptimized Python 3.12 required")
    bound={}
    for name in ("program_source.py","program_model.py","geometry_results.json","port_source_results.json"):
        bound[name]=bind(FROZEN,"local-control",name)
    local_names=("threshold_program_model.py","threshold_program_source.py","threshold_design.py",
                 "threshold_geometry_results.json","gate_source_completion_results.json",
                 "threshold_initialization_results.json","interrupted_renewal_results.json","watchdog_progress_results.json")
    sources={"gate_source_completion_results.json":GATE_SOURCE,"threshold_initialization_results.json":INITIAL_SOURCE}
    for name in local_names:bound[name]=bind(sources.get(name,BASE),"portability",name)
    spec=importlib.util.spec_from_file_location("_orbit_primary",HERE.parent/"local-control/program_model.py")
    old=importlib.util.module_from_spec(spec);sys.modules[spec.name]=old;spec.loader.exec_module(old)
    legacy=load(HERE.parent/"local-control/geometry_results.json")
    design_data=dict(legacy["design"]);design_data["physical_parameters"]=tuple(map(tuple,design_data["physical_parameters"]))
    ac=old.compile_check(old.Design(**design_data));bb=legacy["compiler"]["instruction_bounds"]
    gates=load(HERE/"gate_source_completion_results.json")
    a_hash=sha256(b"".join(w.to_bytes(24,"little") for w in ac.image)).hexdigest()
    need(a_hash==legacy["compiler"]["encoded_image_sha256"]==gates["actual_machine"]["frozen_image_sha256"],
         "Primary instruction image changed")
    a=legacy["timing"];ap=load(HERE.parent/"local-control/port_source_results.json")["return_schedule"]
    mx=Q(1114113,1048576)
    ap_budget=timer_budget(ac.constants,Q(1953),mx,11*mx,Q(a["normal_band_travel"])/13,
        ap["phase_bounds"],Q(a["healthy_long_stage_milestone"]),
        Q(gates["predecessor_sampling"]["period"][1]),Q(a["timer_window"]),Q(legacy["geometry"]["post_driver_overlap"]))
    i=program.load_isa();c=program.compile_program(i,design.design(i));b=program.bounds(i,c)
    point=load(HERE/"threshold_geometry_results.json");phase=point["arithmetic"];g=phase["geometry"]
    b_hash=program.hash_text(json.dumps(c.image))
    need(b_hash==point["changed_image_sha256"] and b==point["bounds"],"Threshold image/work bound changed")
    b_budget=timer_budget(c.constants,Q(517),Q(phase["frames"]["max"]),Q(phase["polling"]),
        Q(phase["band_travel"])/13,phase["phase_bounds"],Q(phase["watchdog"]["ACT_milestone"]),
        0,Q(phase["watchdog"]["complete_timer_job"]),Q(g["overlap_after_first_useful_vector"]))
    gate_name="threshold_gate_source_results.json"
    gate_digest=bind(GATE_SOURCE,"portability",gate_name)
    candidate=load(HERE/gate_name)
    need(candidate["image_sha256"]==b_hash,"B sampler supplies a different image")
    for name,sha in candidate["sources_sha256_lf"].items():
        need(bind(GATE_SOURCE,"portability",name)==sha,"B sampler source binding differs")
    cc=candidate["costs"]
    delay=Q(cc["sample_delay_addition"])/cc["maximum_conditional_added_sample_waits"]
    need(delay==Q(101,100) and Q(cc["combined_joint_reaction"])<=Q(324,1000),
         "Candidate sampler delay/reaction exceeds the compared point")
    sampled_budget=timer_budget(c.constants,Q(517),Q(phase["frames"]["max"]),Q(phase["polling"]),
        Q(phase["band_travel"])/13,phase["phase_bounds"],Q(phase["watchdog"]["ACT_milestone"]),
        delay,Q(phase["watchdog"]["complete_timer_job"]),Q(g["overlap_after_first_useful_vector"]))
    stop=Q(28)-Q(3478,125)
    need(stop==Q(22,125) and stop<2,"No-motion polarity boundary disappeared")
    half=Q(phase["fresh_half_time"]);init=load(HERE/"threshold_initialization_results.json")["bootstrap"]
    startup=Q(init["all_role_commissioning"])
    need(startup+2*half<2*10**13,"Conditional donor half budget too large")
    return serial(dict(base=BASE,frozen_primary=FROZEN,primary_image_little_endian_sha256=a_hash,
        threshold_image_json_sha256=b_hash,primary_timer=ap_budget,threshold_timer=b_budget,
        B_sampled_candidate=dict(commit=GATE_SOURCE,record_sha256_lf=gate_digest,
            timer=sampled_budget,fresh_half_bound=half+13*delay,
            first_half_from_initial_upper=startup+half+13*delay,
            two_half_cut_bound=2*(half+13*delay),reaction=cc["combined_joint_reaction"],
            full_source_admitted=candidate["full_B_source_admission"]),
        threshold_control=threshold_cases(i,c,b),primary_non_timeout_source=primary_countercase(old,ac,bb),
        no_motion_bad_effort_margin=stop,threshold_first_half_from_initial_upper=startup+half,
        threshold_two_half_cut_bound=2*half,threshold_nominal_phase2_revisit_from_fresh_handoff=half,
        startup_counted_once=True,phase_rank_does_not_trust_energy_monotonicity=True,
        computed_budget_scope="The unsampled B column is the geometry-only comparison. Use the sampled column for the integrated contact source. Rebind if contact or visibility changes.",
        normal_reachable_orbit_certified=False,program_complete=False,
        inputs_sha256_lf=bound,own_sha256_lf={n:sha256((HERE/n).read_bytes().replace(b"\r\n",b"\n")).hexdigest()
                                  for n in ("NORMAL-ORBIT.md","normal_orbit.py")}))


def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument("--write",action="store_true");g.add_argument("--check",action="store_true");arg=p.parse_args()
    value=generate();path=HERE/"normal_orbit_results.json"
    if arg.write:path.write_text(json.dumps(value,indent=2,sort_keys=True)+"\n",encoding="utf-8",newline="\n")
    else:need(value==load(path),"Normal orbit receipt record changed")
    print("PASS normal-orbit compiler/conditional timing checks; physical orbit admission remains open")


if __name__=="__main__":main()
