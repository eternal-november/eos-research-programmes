"""Regional-B candidate's proper-prefix itinerary and local bank-birth packing."""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path

import gate_source_completion as gates
import legacy_realization as legacy
import return_seat as seat
import threshold_program_model as program


HERE=Path(__file__).resolve().parent
PIN="f90a57d119286ca90aa245e902c59fad27aa1890"


def need(ok,why):
    if not ok:
        raise ValueError(why)


def frozen(name):
    return legacy.text_at(PIN,"portability/"+name)


def source_rows(isa,c,bounds):
    k=c.constants
    probes=[]
    for half in (0,1):
        for phase in range(5):
            ports=program.ports_class(isa)(c)
            m,view=program.helper_fixture(isa,c,ports,half,phase)
            base=k["TARGET_BASE"]
            for name,val in (("EXITING_ABORT",0),("ABORT",1),("WATCH_HALF",half+1),
                             ("LAST_PHASE",phase),("TIMER",500),("STAGE_WAIT",0)):
                m.W[base+k[name]]=val
            ports.set_view(0,view)
            program.call(isa,c,ports,"helper",(0,),bounds["instruction_upper_bounds"]["helper"]+32,m)
            packet=next(e for e in reversed(ports.events) if e[0]=="command")[2:]
            cam,mode,action=packet[2:5]
            need(cam==20 and m.C==c.image and m.code_writes==0,"Old ABORT silenced actual CAM")
            if phase<4:
                need(mode==20 and not action and m.W[base+k["ABORT"]]==1,"Old request did not persist")
            else:
                need(mode==0 and action==k["RESET_PORT"] and packet[6]==20
                     and m.W[base+k["ABORT"]]==0 and m.W[base+k["TIMER"]]==k["WATCH_FRAMES"],
                     "Actual phase4 sweep failed to clear/drive")
            probes.append(dict(keeper=half,phase=phase,packet=list(packet),instructions=m.steps,
                               retained_abort=m.W[base+k["ABORT"]]))
    return probes


def numerical(data,c,b):
    phase=data["threshold_geometry_results.json"]["arithmetic"]
    orbit=data["normal_orbit_results.json"]["B_sampled_candidate"]
    prior=data["interrupted_renewal_results.json"]
    stop=data["return_seat_results.json"]
    need(program.hash_text(json.dumps(c.image))==stop["candidate_image"] and c.constants["BAYS"]==1
         and b["padded_frame_upper"]==stop["padded_frame_upper"],"Wrong B candidate or clock")
    k=c.constants
    form=Q(prior["all_role_initialization"])
    partial=Q(prior["corrected_partial_allocation"])
    half=Q(orbit["fresh_half_bound"])
    ordinary_tail=Q(prior["old_effect_suffix"])
    R=Q(phase["ordinary_settle"])
    delta=Q(101,100)
    f=Q(b["padded_frame_upper"],2**26)+Q(k["VECTOR_UPDATES"],64)
    fmin=Q(k["FRAME_STEPS"]*100,101*2**26)
    J=11*f
    W=517+2*J+f+15+1
    S=lambda x:R+x
    C=lambda x:R+Q(x)/Q(9,10)
    E=W+(k["POST_STAGE_FRAMES"]+1)*f+J+R+10000+delta
    rebound=Q(stop["resources"]["wrong_pose_to_full_conditional"])
    returning=60+2*R+10000+2*delta
    # One allowance follows the FIRST real seat into phases 0..4. Charge
    # an initial backwards excursion and five whole bands/clock stops.
    short_normal=R+R/Q(9,10)+5*(C(k["SEGMENT"])+delta)+S(k["RESET_LIMIT"])+delta
    short_full=2*W+S(k["BLEND_LIMIT"])+S(k["RESET_LIMIT"])+S(2*13*k["SEGMENT"])+5*(R+delta)+60
    quick=short_normal+E+short_full+returning
    # A full generic cleanup may initially have a WARM cold activation,
    # whereas a subsequent early restart from a genuine seat cannot.
    generic_full=2*W+Q(prior["abort_allocation"])+60+5*(R+delta)
    deg=k["DEGREE"]
    physical_banks=2*deg
    max_births=2*physical_banks
    dwell=Q(k["POWER_AT"])/Q(11,10)
    quiet=2*quick+2  # Strict interior operation window, allowing tied endpoint events.
    stripe=(max_births+1)*quiet
    max_soft=0
    while (max_births+2+max_soft)*quiet<dwell:
        max_soft+=1
    H=Q(prior["H"]);rate=Q(phase["raw_rate"])
    total=form+partial+14*delta+max(E,rebound)+generic_full+returning+quick+stripe+2*half+ordinary_tail
    max_extra_visits=max(len(x["visits"]) for x in prior["normal_entry_cases"])
    need(max_extra_visits==14 and qfloor(3+2*H*rate)+3==6 and total<H
         and stripe<dwell and qfloor((dwell-1)/quiet)-max_births-1==max_soft,
         "Overlap, physical packing or target deadline failed")
    # Receiving and actually acting after PC0: the commissioning word's
    # ENTRY counter also applies to independently formed newborns.
    boot=Q(data["publication_timing_results.json"]["initialization"]["boot"])
    birth_join=boot+4097*f+2*J+2101*f+2*J+15
    full_min=Q(10000)/Q(11,10)
    # The stronger unformed-arrival check also charges an extra 60q for
    # persistent half-off and one additional fresh seat strobe.
    need(birth_join+60+delta<full_min and (k["POST_STAGE_FRAMES"]-1)*fmin>W+J,
         "Whole stroke cannot buy the local join and positive posthold")
    need(short_normal<Q(phase["watchdog"]["earliest"]) and R<k["SEGMENT"]/4
         and R<Q(k["RESET_LIMIT"])/Q(11,10),"A clean-stop or posthold margin failed")
    # Compatible local Trip transitions, including a failed high without arm.
    trip=gates.Trip(enabled=False,armed=False)
    no,_=trip.transition(10,2,5,power=True)
    _,_=trip.transition(0,2,5,zero=True)
    yes,_=trip.transition(10,2,5,power=True)
    replay,_=trip.transition(10,2,5,power=True)
    need((no,yes,replay)==(False,True,False),"Power event lacks actual consumed zero arm")
    return dict(T_full_initial=form,partial_normal=partial,partial_sample_slack=14*delta,
                sampled_fresh_half=half,remote_or_ordinary_tail=ordinary_tail,generic_FULL=generic_full,
                initial_ENTERING=E,initial_wrong_RETURN=rebound,qualified_RETURN=returning,
                screening_wash=W,settle=R,posthold_min=(k["POST_STAGE_FRAMES"]-1)*fmin,
                formed_from_PC0_join=birth_join,strong_join_with_energy=birth_join+60+delta,
                full_return_min=full_min,short_normal_or_abort=short_normal,short_FULL=short_full,
                one_quick_cycle=quick,quiet_gap=quiet,actual_helper_hosts=deg,actual_bank_slots=physical_banks,
                max_uninterrupted_or_new_epochs=max_births,max_postseat_restarts=1+max_births,guaranteed_quiet_gap_search_span=stripe,
                same_bank_power_separation=dwell,conditional_additional_soft_interruptions_margin=max_soft,
                candidate_entry_to_ready_and_outgoing_retirement=total,strict_H_slack=H-total,
                H=H,lambda_per_q=rate,two_H_cover=qfloor(3+2*H*rate)+3,
                early_commissioning_abort_departures=1+qfloor(form/(2*full_min)),
                all_postrelease_departures_including_early_and_initial_normal=2+max_births+1+qfloor(form/(2*full_min)),
                scope="Bound conditioned on the physical local interval, seal, epoch and passive response suppliers; not global admission.")


def qfloor(x):
    return x.numerator//x.denominator


def outer_phase_probe(isa,c):
    s,test=seat.fixture(isa,c,x=1,wrong=None)
    car=s.abort_carrier
    car.phase="FULL";car.full=True;car.active=True;car.normal=False
    stages=[]
    for effort in (-68,68):
        test.constant_arc([Q(effort,34)]*34,1)
        stages.append(test.strobe(effort))
    need(stages==["observed/held"]*2 and car.position==1 and car.phase=="FULL",
         "The inconsistent FULL-away-from-M product unexpectedly escapes")
    return dict(position=str(car.position),phase=car.phase,strobe_results=stages,paid_U=str(test.work),
                countercase_scope="Cartesian software state product only; physical FULL-at-end coherence excludes this tuple at a mechanically intact site.")


def generate():
    names=("threshold_geometry_results.json","normal_orbit_results.json","interrupted_renewal_results.json",
           "return_seat_results.json","publication_timing_results.json")
    data={name:json.loads(frozen(name)) for name in names}
    isa=program.load_isa()
    c,b=seat.candidate(isa)
    print("checking both actual normal half orientations",flush=True)
    return dict(base=PIN,input_sha256_lf={name:sha256(frozen(name).encode()).hexdigest() for name in names},
                image_sha256=program.hash_text(json.dumps(c.image)),source_branches=source_rows(isa,c,b),
                inconsistent_latch=outer_phase_probe(isa,c),budget=numerical(data,c,b),
                raw_horizon_fixed=True,full_source_admitted=False)


def render(value):
    if isinstance(value,Q):
        return str(value)
    raise TypeError(type(value))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--write",action="store_true")
    args=parser.parse_args()
    payload=json.dumps(generate(),indent=2,sort_keys=True,default=render)+"\n"
    target=HERE/"return_itinerary_results.json"
    if args.write:
        target.write_text(payload,encoding="utf8",newline="\n")
    else:
        need(target.read_text(encoding="utf8")==payload,"Return itinerary changed")
    print("conditional itinerary, restart packing and real helper branches reproduced")


if __name__=="__main__":
    main()
