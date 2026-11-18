"""Isolated B abort-policy comparison. The actual source and compiler image are retained."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

import legacy_realization as legacy
import threshold_design as design
import threshold_program_model as program


HERE=Path(__file__).resolve().parent
PIN="003d9e7f92874ff32ce405eaea788f7bff82f0fa"


def need(ok,message):
    if not ok:
        raise ValueError(message)


def replace_once(body,old,new):
    need(body.count(old)==1,"Unexpected comparison source")
    return body.replace(old,new)


def edited(body):
    # enter this helper only after a positive NORMAL_STOP read in helper()
    start=body.index("    if contact(t, NORMAL_STOP):",body.index("def exiting_abort"))
    end=body.index("\ndef helper(t):",start)
    body=body[:start]+"""    if not w[base + EXIT_OBSERVED]:
        w[base + EXIT_OBSERVED] = 1
        w[base + EXIT_WAIT] = POST_STAGE_FRAMES
    elif w[base + EXIT_WAIT] == 0:
        w[base + EXITING_ABORT] = 0
        w[base + EXIT_OBSERVED] = 0
        w[base + ABORT] = 0
        w[base + WATCH_HALF] = 0
        w[base + STAGE_ID] = 0
        w[base + RANK_VALID] = 0

"""+body[end:]
    old="""    if w[base + EXITING_ABORT]:
        exiting_abort(t, base)
        flush(t)
        return 0
    if contact(t, ABORT_FULL):
"""
    new="""    old_exit = w[base + EXITING_ABORT]
    full = 0
    if old_exit:
        w[base + CMD_ROUTE] = 26
        if w[base + EXIT_WAIT] < 0 or w[base + EXIT_WAIT] > POST_STAGE_FRAMES:
            w[base + EXIT_WAIT] = POST_STAGE_FRAMES
        if contact(t, NORMAL_STOP):
            exiting_abort(t, base)
            flush(t)
            return 0
        if w[base + EXIT_OBSERVED]:
            w[base + EXIT_OBSERVED] = 0
            w[base + EXIT_WAIT] = POST_STAGE_FRAMES
        full = contact(t, ABORT_FULL)
        if not full:
            emit(t, MODE_PORT, cold, 0, -FORCE)
            if w[base + EXIT_WAIT] == 0 and contact(t, MODE):
                w[base + EXITING_ABORT] = 0
                w[base + ABORT] = 0
                w[base + WATCH_HALF] = 0
                w[base + STAGE_ID] = 0
                w[base + RANK_VALID] = 0
                emit(t, MODE_PORT, cold, 0, FORCE)
            flush(t)
            return 0
        w[base + EXIT_WAIT] = POST_STAGE_FRAMES
    else:
        full = contact(t, ABORT_FULL)
    if full:
"""
    body=replace_once(body,old,new)
    body=replace_once(body,"""        if w[base + STAGE_WAIT] > 0:
            flush(t)
            return 0
        abort_action(t, base)
""","""        if w[base + STAGE_WAIT] > 0:
            if old_exit:
                emit(t, MODE_PORT, cold, 0, -FORCE)
            flush(t)
            return 0
        abort_action(t, base)
""")
    return replace_once(body,"""                w[base + CMD_AMPLITUDE] = 0
        flush(t)
        return 0
    if contact(t, MODE):
""","""                w[base + CMD_AMPLITUDE] = 0
        if old_exit:
            emit(t, MODE_PORT, cold, 0, -FORCE)
        if w[base + EXITING_ABORT]:
            w[base + EXIT_WAIT] = POST_STAGE_FRAMES
        flush(t)
        return 0
    if contact(t, MODE):
""")


class Text:
    def __init__(self,body):
        self.body=body
    def read_text(self,encoding):
        return self.body


def execute(isa,c,b,scenario):
    k=c.constants
    p=program.ports_class(isa)(c)
    m,v=program.helper_fixture(isa,c,p,0,0)
    base=k["TARGET_BASE"]
    cold=1
    # The fixture is a complete compiled invocation from a particular paid
    # observation/private projection, not an initialized mechanical history.
    for label,value in scenario["view"].items():
        index=k[label[:-1]+"A"]+1 if label.endswith("_B") else k[label]
        v[index]=value
    p.set_view(0,v)
    prior={"STAGE_ID":27,"STAGE_WAIT":0,"EXITING_ABORT":1,
           "EXIT_OBSERVED":0,"EXIT_WAIT":17,"ABORT_WAIT":0,"ABORT_SIGNATURE":0}
    for label,value in (prior|scenario.get("private",{})).items():
        m.W[base+k[label]]=value&isa.WORD_MASK
    if "armed" in scenario:
        port=k[scenario["armed"]]
        m.W[base+k["ABORT_SIGNATURE"]]=port+k["PORTS"]*cold
    if scenario.get("bad_load"):
        key=3+k["VIEW_WORDS"]+cold
        for slot in range(15):
            for bank in range(2):
                p.fast[slot,bank,key]=1500
    program.call(isa,c,p,"helper",(0,),b["instruction_upper_bounds"]["helper"]+32,m)
    cmd=next(x for x in reversed(p.events) if x[0]=="command")
    return dict(packet=list(cmd[2:]),instructions=m.steps,fast_equal=m.io_counts["fast_equal"],
                fast_cmp=m.io_counts["fast_cmp"],state=[m.W[base+k[x]] for x in ("EXITING_ABORT","EXIT_OBSERVED","EXIT_WAIT","ABORT_SIGNATURE","ABORT_WAIT")],
                image_unchanged=m.C==c.image and m.code_writes==0)


def generate():
    isa=program.load_isa()
    old=isa.SOURCE
    source=old.read_text(encoding="utf8")
    need(source==legacy.text_at(PIN,"portability/threshold_program_source.py"),"Production source no longer matches the analysis")
    initial=program.compile_program(isa,design.design(isa))
    original_bounds=program.bounds(isa,initial)
    try:
        isa.SOURCE=Text(edited(source))
        c=program.compile_program(isa,design.design(isa))
        b=program.bounds(isa,c)
    finally:
        isa.SOURCE=old
    k=c.constants
    full={"ABORT_FULL":1,"MODE":0,"NORMAL_STOP":0,"CAM_ENTRY_A":0}
    entering={"ABORT_FULL":0,"MODE":1,"NORMAL_STOP":0,"CAM_ENTRY_A":0}
    quiet={"ABORT_FULL":0,"MODE":0,"NORMAL_STOP":0,"CAM_ENTRY_A":0}
    at_normal={"ABORT_FULL":1,"MODE":1,"NORMAL_STOP":1,"CAM_ENTRY_A":1}
    views={
        "old_X_unqualified_action":dict(view=full),
        "old_X_rewind":dict(view=full,armed="REWIND_PORT"),
        "fresh_rewind":dict(view=full,armed="REWIND_PORT",private={"EXITING_ABORT":0}),
        "qualified_new_X_renews":dict(view=full|{"CAM_ENTRY_A":1},private={"EXITING_ABORT":0}),
        "old_X_stage_wait":dict(view=full,private={"STAGE_WAIT":2}),
        "old_X_cut":dict(view=full|{"CUT_OPEN_B":0},armed="CUT_PORT"),
        "old_X_cut_refused":dict(view=full|{"CUT_OPEN_B":0},armed="CUT_PORT",bad_load=True),
        "expired_entering":dict(view=entering,private={"EXIT_WAIT":0}),
        "last_tick_entering":dict(view=entering,private={"EXIT_WAIT":1}),
        "contaminated_count":dict(view=entering,private={"EXIT_WAIT":2**250}),
        "posthold_lost_once":dict(view=entering,private={"EXIT_WAIT":0,"EXIT_OBSERVED":1}),
        "unknown_expired":dict(view=quiet,private={"EXIT_WAIT":0}),
        "normal_priority":dict(view=at_normal,private={"EXIT_WAIT":0}),
        "normal_post_complete":dict(view=at_normal,private={"EXIT_WAIT":0,"EXIT_OBSERVED":1}),
    }
    rows={tag:execute(isa,c,b,row) for tag,row in views.items()}
    actual=lambda label:rows[label]["packet"]
    # route, side, cam, mode, action, index, amplitude: independent payload
    # fields in the SAME emitted record, including its original paid action.
    need(actual("old_X_rewind")==[26,1,0,-20,k["REWIND_PORT"],0,20]
         and actual("fresh_rewind")==[26,1,0,20,k["REWIND_PORT"],0,20],"Lost concurrent signed mode and rewind")
    need(actual("old_X_cut")==[26,1,0,-20,k["CUT_PORT"],0,20] and actual("old_X_cut_refused")[4]==0,
         "Independent negative MODE bypassed or prevented factual CUT qualification")
    for tag in ("old_X_unqualified_action","old_X_stage_wait","normal_priority","unknown_expired","last_tick_entering","posthold_lost_once"):
        need(actual(tag)[3]==-20 and actual(tag)[4]==0,tag)
    need(actual("expired_entering")[3]==20 and rows["expired_entering"]["state"][0]==0
         and rows["qualified_new_X_renews"]["state"][:3]==[1,0,k["POST_STAGE_FRAMES"]],"Lease birth or expiry changed")
    need(rows["contaminated_count"]["state"][2]==k["POST_STAGE_FRAMES"]
         and rows["normal_priority"]["state"][:3]==[1,1,k["POST_STAGE_FRAMES"]]
         and rows["normal_post_complete"]["state"][0:2]==[0,0],"Clamping/post-NORMAL hold failed")
    fmin=Q(k["FRAME_STEPS"]*100,2**26*101)
    fmax=Q(b["padded_frame_upper"],2**26)+Q(k["VECTOR_UPDATES"],64)
    J=11*fmax
    P=k["POST_STAGE_FRAMES"]
    wash=517+2*J+fmax+15+1
    issue=wash+(P+1)*fmax+J
    settled=issue+15
    retain=(P-1)*fmin
    need(retain>wash+J and b["active_frame_upper"]<=k["FRAME_STEPS"],"The candidate no longer fits the scheduling regime")
    timing=json.loads(legacy.text_at(PIN,"portability/threshold_gate_source_results.json"))["costs"]
    # A separate target force/withdrawal supplier is required for this R*
    # allowance; the changed code does not predeclare it achieved.
    settle=Q(2748532811,524288)
    pressure=Q(2)*33-Q(22,5)*7-Q(11,10)-Q(324,1000)
    pub=json.loads(legacy.text_at(PIN,"portability/publication_timing_results.json"))
    functional=pub["functional"]
    increment=Q(b["instruction_upper_bounds"]["helper"]-original_bounds["instruction_upper_bounds"]["helper"],2**26)
    compare=Q(b["instruction_upper_bounds"]["helper"]+64,2**26)+Q(1,64)
    need(compare==Q(functional["helper_compare_to_emit"])+increment,"Comparison horizon drifted")
    horizon=Q(functional["full_horizon"])+increment
    load=Q(3,2)*(1-Q(k["LOAD_MARGIN"],1000)+Q(1,100))+horizon/10000
    deficit=Q(1,5)-Q(k["ISOLATION_MARGIN"],1000)+Q(1,100)+Q(1,10)+Q(11,400000)*horizon
    need(load==Q(functional["force_upper"])+increment/10000 and load<1 and
         deficit==Q(functional["deficit_upper"])+Q(11,400000)*increment and deficit<Q(1,5),
         "Changed helper deadline defeats factual guard")
    need(b["padded_frame_upper"]==original_bounds["padded_frame_upper"] and pressure>31,
         "Timing or surviving force needs a new bound")
    return dict(source=PIN,production_image=program.hash_text(json.dumps(initial.image)),candidate_image=program.hash_text(json.dumps(c.image)),
                occupied_cells=[len(initial.nodes),len(c.nodes)],registers=[initial.next_register,c.next_register],
                instruction_helper_upper=[original_bounds["instruction_upper_bounds"]["helper"],b["instruction_upper_bounds"]["helper"]],
                frame_active_upper=[original_bounds["active_frame_upper"],b["active_frame_upper"]],
                frame_padded_upper=[original_bounds["padded_frame_upper"],b["padded_frame_upper"]],
                constants=dict(Fmin=str(fmin),Fmax=str(fmax),J=str(J),P=P,hold_min=str(retain),wash=str(wash),
                               last_stale_X_issue=str(issue),stable_application_with_15q=str(settled),
                               conditional_ENTERING_to_FULL_using_R_star=str(issue+settle+10000),
                               surviving_force_at_most_one_adverse_pair=str(pressure),stiction_max=29,compliance_max=2),
                current_gate_rewind_scope="FULL only",current_gate_recoverable_stock=timing["new_recoverable_storage"],
                candidate_factual=dict(compared_helper_q=str(compare),horizon_q=str(horizon),
                                       load_upper=str(load),clearance_deficit_upper=str(deficit)),
                outcomes=rows,full_source_change_adopted=False)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--write",action="store_true")
    args=parser.parse_args()
    content=json.dumps(generate(),sort_keys=True,indent=2)+"\n"
    path=HERE/"abort_protocol_alternative_results.json"
    if args.write:
        path.write_text(content,encoding="utf8",newline="\n")
    else:
        need(path.read_text(encoding="utf8")==content,"Comparison record differs")
    print("candidate abort packets and timing reproduced")


if __name__=="__main__":
    main()
