"""Ordinary normal-arm correspondence and causal acquisition of a phase-10 stage."""
import argparse
import ast
from fractions import Fraction as Q
from pathlib import Path
import json

import common_response as prior
import image_transport as transport
import return_seat as seat

HERE=Path(__file__).resolve().parent
need=seat.checks
program=seat.program


def regions(c):
    h=c.functions["helper"]
    row=lambda s: ast.unparse(s).splitlines()[0]
    start=next(j for j,s in enumerate(h.body) if row(s) in
               ("if w[base + EXITING_ABORT]:","old_exit = w[base + EXITING_ABORT]"))
    finish=next(j for j,s in enumerate(h.body) if row(s)=="if contact(t, MODE):")
    def addr(j):
        return c.line_spans[f"helper:{h.body[j].lineno}"][0]
    a,b=transport.segments(c)["helper"]
    return a,addr(start),addr(finish),b,[ast.dump(s) for s in h.body[:start]],[ast.dump(s) for s in h.body[finish:]]


def middle(isa,c,lo,hi):
    # Execute the two guards symbolically on arbitrary formed local base/t.
    # Arguments to contact are actual registers and its zero return is the
    # explicit normal-arm condition.
    regs={c.registers["helper","base"]:("base",),c.registers["helper","t"]:("t",)}
    used=set()
    effects=[]
    pc=lo
    get=lambda k:regs[k]
    while pc!=hi:
        need(lo<=pc<hi and pc not in used,"Outside normal finite guard route")
        used.add(pc)
        op,a,b,n,i=isa.decode(c.image[pc])
        pc+=1
        if op==isa.MOV:
            regs[a]=get(b)
        elif op==isa.LI:
            regs[a]=i
        elif op==isa.ADD:
            regs[a]=("add",get(b),get(n))
        elif op==isa.LOAD:
            need(get(b)==("add",("base",),c.constants["EXITING_ABORT"]),
                 "Middle branch consulted another word")
            effects.append("read EXITING_ABORT")
            regs[a]=0
        elif op==isa.JZ:
            v=get(a)
            need(type(v) is int,"Unknown symbolic condition selected control")
            if not v:pc=i
        elif op==isa.JMP:
            pc=i
        elif op==isa.CALL:
            need(i==c.labels["contact"] and tuple(map(get,c.formals["contact"]))
                 ==(("t",),c.constants["ABORT_FULL"]),"Unmatched physical query in the normal guard")
            effects.append("contact(t, ABORT_FULL)")
            regs[2]=0
        else:
            raise ValueError(f"Unmatched effect or instruction in middle: {op}")
    need(effects==["read EXITING_ABORT","contact(t, ABORT_FULL)"],"Changed guard observations")
    return used,regs,effects


def correspondence(isa,left,right):
    oa,ob,oc,od,opre,opost=regions(left)
    na,nb,nc,nd,npre,npost=regions(right)
    need(opre==npre and opost==npost and ob-oa==nb-na and od-oc==nd-nc,
         "Nominal outer procedure changed")
    closed,renamed=transport.compare_code(isa,left,right)
    seen=renamed.copy()
    back={v:k for k,v in seen.items()}
    def link(a,b):
        need(seen.setdefault(a,b)==b and back.setdefault(b,a)==a,"Aliased physical registers")
    for key in set(left.registers)&set(right.registers):
        if key[0]=="helper":
            link(left.registers[key],right.registers[key])
    dest_ops={isa.LI,isa.MOV,isa.ADD,isa.SUB,isa.MUL,isa.DIV,isa.MOD,isa.SHL,
              isa.AND,isa.OR,isa.EQ,isa.LT,isa.LE,isa.NOT,isa.LOAD}
    allowed=dest_ops|{isa.STORE,isa.JMP,isa.JZ,isa.CALL,isa.RET}
    ma=seat.parent.ParentMachine(isa,left);mb=seat.parent.ParentMachine(isa,right)
    loc={**{k:na+k-oa for k in range(oa,ob)},**{k:nc+k-oc for k in range(oc,od)}}
    transport_pc={**loc,ob:nb,od:nd}
    named={left.labels[f]:f for f in left.functions}
    calls=set()
    # Basic-block liveness at the common suffix, including exactly what each
    # static callee reads as its actual formals. Live stack slots are separate.
    instructions={}
    for pc,npc in loc.items():
        one=isa.decode(left.image[pc]);two=isa.decode(right.image[npc])
        op,a,b,k,imm=one
        need(op==two[0] and op in allowed,"Uncovered nominal helper instruction")
        reads=set(ma.capture_indices(*one))
        for x,y in zip(ma.capture_indices(*one),mb.capture_indices(*two),strict=True):
            link(x,y)
        writes=set()
        if op in dest_ops:
            link(a,two[1]);writes.add(a)
        if op==isa.CALL:
            f=named[imm];calls.add(f)
            need(f in closed["closed"] and right.labels[f]==two[4],"Untransported callee")
            reads.update(left.formals[f]);writes.add(2)
        elif op in (isa.JZ,isa.JMP):
            need(transport_pc[imm]==two[4],"Different reachable continuation")
        else:
            need(imm==two[4],"Changed literal")
        nxt=(() if op==isa.RET else (imm,) if op==isa.JMP else
             (pc+1,imm) if op==isa.JZ else (pc+1,))
        if pc>=oc:
            instructions[pc]=(reads,writes,nxt)
    live={pc:set() for pc in instructions}
    changed=True
    while changed:
        changed=False
        for pc in reversed(instructions):
            reads,writes,nxt=instructions[pc]
            # R2 is observable by a caller after RET.
            old=live[pc]
            needed=reads|((set.union(*(live[j] for j in nxt)) if nxt else {2})-writes)
            if needed!=old:
                live[pc]=needed;changed=True
    old_path,old_regs,eff=middle(isa,left,ob,oc)
    new_path,new_regs,_=middle(isa,right,nb,nc)
    for r in live[oc]:
        rr=seen[r]
        ov=old_regs.get(r,("entry",r))
        nv=new_regs.get(rr,("entry",r))
        need(ov==nv,"Extra private guard operation overwrote downstream live value")
    # No unrepresented register in a called routine may write the caller's
    # live variables. Compiler locals/temps are disjoint; R2 and call argument
    # locations keep their explicit effects.
    live_named={r for r in live[oc] if r not in (1,2)}
    for f in closed["closed"]:
        lo,hi=transport.segments(left)[f]
        for pc in range(lo,hi):
            op,a,*_=isa.decode(left.image[pc])
            if op in dest_ops or op==isa.IO:
                need(a not in live_named,"Closed callee overwrites live helper state")
    return dict(old_helper=oa,new_helper=na,old_normal_suffix=oc,new_normal_suffix=nc,
                common_cells=len(loc),suffix_live_registers=sorted(live[oc]),closed_calls=sorted(calls),
                normal_guard_effects=eff,old_intermediate_cells=len(old_path),new_intermediate_cells=len(new_path),
                extra_nominal_retirements=len(new_path)-len(old_path),mid_path_old=sorted(old_path),mid_path_new=sorted(new_path))


def check_tick(isa,c):
    fn=c.functions["frame"]
    tick=next(s for s in fn.body if isinstance(s,ast.While) and ast.unparse(s.test)=="target < DEGREE")
    before=fn.body[fn.body.index(tick)-1]
    need(ast.unparse(before)=="target = 0","Counter sweep missing at frame exit")
    text=ast.unparse(tick)
    fields=("TIMER","STAGE_WAIT","ABORT_WAIT","EXIT_WAIT")
    expected=["while target < DEGREE:","    base = TARGET_BASE + target * TARGET_WORDS"]
    for f in fields:
        expected+=["    if w[base + "+f+"] > 0:","        w[base + "+f+"] -= 1"]
    expected+=["    target += 1"]
    need(text.splitlines()==expected,"Frame tail no longer performs the four bounded decrements")
    lo=c.line_spans[f"frame:{before.lineno}"][0];hi=c.line_spans[f"frame:{tick.lineno}"][1]
    # An executed one-step check at all forty addresses and three value classes.
    m=program.initialized(isa,c)
    k=c.constants
    for j in range(k["DEGREE"]):
        for ix,f in enumerate(fields):
            m.W[k["TARGET_BASE"]+j*k["TARGET_WORDS"]+k[f]]=(0,1,2100)[(ix+j)%3]
    old=m.W[:]
    p=program.ports_class(isa)(c)
    m.pc=lo
    while m.pc!=hi:
        need(m.steps<10000 and m.step(p),"Did not complete the real frame clock sweep")
    expected_state=old[:]
    for j in range(k["DEGREE"]):
        for f in fields:
            pos=k["TARGET_BASE"]+j*k["TARGET_WORDS"]+k[f]
            expected_state[pos]=max(0,old[pos]-1)
    need(m.W==expected_state,"Real frame sweep changed another row or missed a counter")
    return dict(start=lo,end=hi,actual_retirements=m.steps,fields=fields,rows=k["DEGREE"])


def stage(isa,c,b,Ports,previous,high,low,exact):
    k=c.constants
    row=39
    base=k["TARGET_BASE"]+row*k["TARGET_WORDS"]
    machine=program.initialized(isa,c)
    functional=3+row*k["FAST_TARGET_KEYS"]+k["VIEW_WORDS"]
    class Observed(Ports):
        def perform(self,name,args,m):
            if name in ("fast_cmp","fast_equal","fast_range") and functional<=args[2]<functional+4:
                self.used.add(tuple(args[:3]))
            return super().perform(name,args,m)
    ports=Observed(c)
    ports.used=set()
    prior.publication.install(ports,previous)
    def read(f):
        return machine.W[base+k[f]]
    def write(f,v):
        machine.W[base+k[f]]=v
    # At this local entry ordinary initialized row contents have not yet
    # acquired phase nine. A reached running code/healthy source remains
    # the outer precondition.
    need(all(read(f)==0 for f in ("ABORT","EXITING_ABORT","WATCH_HALF","LAST_PHASE","STAGE_ID")),
         "Unexpected ordinary entry row")
    def visit():
        begin=machine.steps
        ports.used.clear()
        # enter() installs only the call/return harness, preserving target W.
        program.call(isa,c,ports,"helper",(row,),b["instruction_upper_bounds"]["helper"]+10,machine)
        packet=next(e for e in reversed(ports.events) if e[0]=="command")
        return dict(steps=machine.steps-begin,action=packet[6],cam=packet[4],amplitude=packet[8],
                    functional_bank_reads=len(ports.used),functional_keys=sorted({key-functional for _,_,key in ports.used}),
                    timer=read("TIMER"),high=read("HIGH"),stage=read("STAGE_ID"),
                    wait=read("STAGE_WAIT"),last_phase=read("LAST_PHASE"),rank_valid=read("RANK_VALID"))
    # A full frame's per-target decrement is the closed form of the actual
    # compiled sweep. Ordinary visits during the wait retain its boundary.
    def pass_frames(n):
        for f in ("TIMER","STAGE_WAIT","ABORT_WAIT","EXIT_WAIT"):
            write(f,max(0,read(f)-n))
    phase9_entry=visit()
    need(phase9_entry["stage"]==10 and phase9_entry["wait"]==k["POST_STAGE_FRAMES"],
         "The actual preceding stage was not acquired")
    pass_frames(k["POST_STAGE_FRAMES"])
    phase9=visit()
    need(phase9["last_phase"]==9 and phase9["timer"]==k["WATCH_FRAMES"] and read("ABORT")==0,
         "Previous phase did not form a real watchdog state")
    prior.publication.install(ports,high)
    pass_frames(10)
    first=visit()
    need(first["stage"]==11 and first["wait"]==k["POST_STAGE_FRAMES"] and first["last_phase"]==9
         and first["action"]==0 and first["high"]==phase9["high"],"Stage ten was supplied as the result")
    pass_frames(k["POST_STAGE_FRAMES"]-10)
    early=visit()
    need(early["wait"]==10 and early["last_phase"]==9 and early["action"]==0,
         "A waiting helper skipped physical stage qualification")
    pass_frames(10)
    hold=visit()
    need(hold["wait"]==0 and hold["last_phase"]==10 and hold["rank_valid"]==1
         and hold["timer"]==k["WATCH_FRAMES"] and hold["high"]==250162000
         and hold["cam"]==k["FORCE"] and hold["action"]==0,
         "Normal phase10 record did not form from earlier private data")
    # Retain the actual formed WHOLE target state across the later read.
    current_call=Q(b["instruction_upper_bounds"]["helper"]+64,2**26)+Q(1,64)
    postclear=(Q(exact["clearance"])+Q(exact["fresh_data_and_action_after_clearance"])
               -Q(exact["helper_allowance"])+current_call+Q(1))
    upper_frames=int(postclear/Q(exact["frame_min"]))+2
    need(upper_frames<k["WATCH_FRAMES"] and postclear<Q(exact["phase10_upper"]),
         "No time to acquire fresh post-clear evidence before the physical phase deadline")
    # In the still-at-stop branch, every intervening visit may renew TIMER
    # but cannot shorten the lower bound. Exercise that worst counter value.
    # The numerical projection is not an assumed exact run of N full frames.
    pass_frames(upper_frames)
    prior.publication.install(ports,low)
    later=visit()
    need(later["action"]==k["CUT_PORT"] and later["amplitude"]==k["FORCE"] and read("ABORT")==0,
         "Later admissible case failed to give the paid request on the same target state")
    need(not any(r["functional_bank_reads"] for r in (phase9_entry,phase9,first,early))
         and all(r["functional_bank_reads"]==60 and r["functional_keys"]==[0,2] for r in (hold,later)),
         "Stage guard consumed a functional word before qualification or omitted a sibling")
    return dict(selected_target=row,preceding_stage_entry=phase9_entry,preceding_stage_mature=phase9,
                postclear_time_upper=str(postclear),postclear_frame_count_upper=upper_frames,
                entry_last_phase=first["last_phase"],entry_timer=first["timer"],first=first,
                last_waiting=early,first_mature=hold,later_low=later,
                source_condition="resident row formed after fresh previous phase, proper physical stop and separately fresh receipts")


def delivery_comparison(isa,c,local,past):
    pairs=json.loads((HERE/"receiver_lease_results.json").read_text())
    interval=pairs["interval"]
    price=json.loads((HERE/"private_comparison_results.json").read_text())
    work=json.loads((HERE/"return_seat_results.json").read_text())["resources"]
    need(price["source_image"]==program.hash_text(json.dumps(c.image))==pairs["production_image"],
         "Source clock, private predicate and received words belong to different images")
    distances=[]
    for name in ("count_fast","count_range","contact","contact_zero"):
        lo,hi=transport.segments(c)[name]
        locations=[pc for pc in range(lo,hi) if (y:=isa.decode(c.image[pc]))[0]==isa.IO
                   and isa.PRIMITIVES[y[4]] in ("fast_cmp","fast_equal","fast_range")]
        need(len(locations)==2 and all(isa.decode(c.image[p])[0] in (isa.MOV,isa.LI,isa.ADD)
              for p in range(locations[0]+1,locations[1])),"Unpriced work between the two actual bank reads")
        distances.append(locations[1]-locations[0])
    # Include the entire first and second retiring CPU cycles to allow every
    # permitted timer phase and race at either sampled record. No raw clock
    # or oscillator of one endpoint is transported onto the other.
    pair_width=Q(max(distances)+1,2**26)
    need(pair_width<=Q(interval["pair_window"]) and all(pair_width<Q(row["no_worse_overwrite_bridge"])
             for row in interval["per_key"].values()),"Cannot cover both reads at one sound bank")
    base=past["exact"]
    horizon=Q(work["factual_horizon"])
    tau=Q(base["tau"]);derivative=Q(1,100)+Q(21,5)+64*261
    lo=Q(11,16)+Q(base["all_head_load_spread"])+derivative*horizon/(Q(3,2)*tau*128)
    hi=(132-Q(base["q_crossing_tube"])-derivative*horizon/tau)/128
    need(lo<1<hi and Q(work["load_upper"])<1 and
         Q(interval["first_all_keys_including_fold"])<1000,"Gate interval or complete prior fold missing")
    # Higher whole-helper cost is paid by the unchanged frame ceiling.
    # One restricted normal guard itself introduces just four retirements.
    need(local<Q(1,8) and Q(base["brake_time_lower"])>2101*Q(interval["Fmax"])+1000,
         "Phase qualification has no time before the contrasting observation")
    return dict(private_read_indices_apart=distances,sequential_pair_upper=str(pair_width),
                supplied_pair_window=interval["pair_window"],new_effect_horizon=str(horizon),
                old_effect_horizon=base["effect_horizon"],low_upper=str(lo),high_lower=str(hi),
                strictly_before_next_changed_receipt=str(Q(1,8)-local),
                whole_key_lease_from_arbitrary_fold=interval["first_all_keys_including_fold"])


def generate():
    isa=program.load_isa()
    old=program.compile_program(isa,seat.design.design(isa))
    c,b=seat.candidate(isa)
    cross=correspondence(isa,old,c)
    clock=check_tick(isa,c)
    ports=program.ports_class(isa)
    past=json.loads((HERE/"common_response_results.json").read_text())
    pop=12*(6+2**98)+2
    energy=past["keeper_energy"]["word"]
    need(energy==623488 and energy in past["keeper_energy"]["admissible_integer_words"],"Missing installed head bound")
    view=prior.physical_view(isa,c,energy)
    before=view[:]
    before[c.constants["CAM"]]=isa.populated_view(c,0,9)[c.constants["CAM"]]
    previous,phase9=prior.maintenance_receipts(isa,c,b,ports,pop,before,688)
    print("Replaying paired fifteen-origin folds and the previous stage",flush=True)
    high,upper=prior.maintenance_receipts(isa,c,b,ports,pop,view,688)
    low,lower=prior.maintenance_receipts(isa,c,b,ports,pop,view,135)
    achieved=stage(isa,c,b,ports,previous,high,low,past['exact'])
    f=Q(b["padded_frame_upper"],2**26)+Q(c.constants["VECTOR_UPDATES"],64)
    updated=Q(b["instruction_upper_bounds"]["helper"]+64,2**26)+Q(1,64)
    need(updated<Q(1,8) and f==Q(past["exact"]["frame_max"]) and cross["extra_nominal_retirements"]>=0,
         "Changed source timing was not paid")
    return dict(source_image=program.hash_text(json.dumps(c.image)),comparison=cross,frame_clock=clock,
                frame_max=str(f),guard_time_difference_upper=str(Q(cross["extra_nominal_retirements"],2**26)),
                generated_previous=phase9,generated_high=upper,generated_low=lower,formed_response=achieved,
                true_changed_helper_allowance=str(updated),source_receipt=delivery_comparison(isa,c,updated,past),
                complete_phase10_reachability=False,
                inputs={n:program.digest(HERE/n) for n in ("NORMAL-RESPONSE-TRANSPORT.md","normal_response_transport.py","common_response.py",
                    "common_response_results.json","image_transport.py","return_seat.py","world_channel_results.json",
                    "private_comparison_results.json","receiver_lease_results.json","threshold_program_model.py","threshold_publication_model.py")})


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--write",action="store_true");args=ap.parse_args()
    result=json.dumps(generate(),sort_keys=True,indent=2)+"\n"
    dst=HERE/"normal_response_transport_results.json"
    if args.write:dst.write_text(result,encoding="utf-8",newline="\n")
    else:need(dst.read_text(encoding="utf-8")==result,"Normal helper receipt differs")
    print("Verified compiled normal-arm correspondence, real counter sweep and formed phase-10 response")
