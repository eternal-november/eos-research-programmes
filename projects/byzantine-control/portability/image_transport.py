"""Certify the shared ordinary code and the image-dependent scanner of two B designs."""
import argparse
import ast
import json
import subprocess
from collections import defaultdict, deque
from fractions import Fraction as Q
from pathlib import Path

import native_clock_source as paced
import parent_realization as parent
import return_seat as seat
import threshold_incidence_model as incidence
import threshold_initialization as startup


HERE=Path(__file__).resolve().parent
SOURCE="041c5c975901c448a871344daf30ed15502ced15"
program=seat.program


def need(ok, message):
    if not ok:
        raise ValueError(message)


def segments(c):
    starts=sorted((c.labels[name],name) for name in c.functions)
    bounds={name:(address,starts[i+1][0] if i+1<len(starts) else len(c.nodes))
            for i,(address,name) in enumerate(starts)}
    bounds["<entry>"]=(0,starts[0][0])
    return bounds


def compare_code(isa, old, new):
    """Derive a single injective data-register map and named instruction map."""
    left,right=segments(old),segments(new)
    shared={"<entry>"} | {f for f in old.functions.keys() & new.functions.keys()
                            if ast.dump(old.functions[f])==ast.dump(new.functions[f])}
    old_parent=parent.ParentMachine(isa,old)
    new_parent=parent.ParentMachine(isa,new)
    renamed={}; reverse={}
    def match(a,b):
        need(0<=a<old.next_register and 0<=b<new.next_register,"Uninstalled register")
        need(renamed.setdefault(a,b)==b and reverse.setdefault(b,a)==a,"Register mapping is not one-to-one")
    for r in (0,1,2):
        match(r,r)
    for name in old.functions.keys() & new.functions.keys():
        need(len(old.formals[name])==len(new.formals[name]),"Changed calling convention for "+name)
        for a,b in zip(old.formals[name],new.formals[name]):
            match(a,b)
    D={isa.LI,isa.MOV,isa.ADD,isa.SUB,isa.MUL,isa.DIV,isa.MOD,isa.SHL,isa.AND,isa.OR,
       isa.EQ,isa.LT,isa.LE,isa.NOT,isa.LOAD,isa.LOADC,isa.IO}
    supported=D | {isa.STORE,isa.STOREC,isa.JMP,isa.JZ,isa.CALL,isa.RET,isa.HALT}
    address_name={addr:f for f,(addr,_) in left.items()}
    calls=defaultdict(set)
    code_readers=set()
    for name in sorted(shared):
        lo,end=left[name]; dest,limit=right[name]
        need(end-lo==limit-dest,"Different block lengths in "+name)
        for pc in range(lo,end):
            npc=dest+pc-lo
            old_op=isa.decode(old.image[pc]);new_op=isa.decode(new.image[npc])
            op=old_op[0]; imm=old_op[4]; imm2=new_op[4]
            need(op==new_op[0] and op in supported,"Unmatched opcode in "+name)
            src=old_parent.capture_indices(*old_op);tgt=new_parent.capture_indices(*new_op)
            need(len(src)==len(tgt),"Different captured register count")
            for a,b in zip(src,tgt):
                match(a,b)
            if op in D:
                match(old_op[1],new_op[1])
            if op==isa.CALL:
                called=address_name.get(imm)
                need(called in new.labels and new.labels[called]==imm2,"CALL changed physical routine")
                calls[name].add(called)
            elif op in (isa.JZ,isa.JMP):
                if name=="<entry>":
                    need(imm==old.labels["main"] and imm2==new.labels["main"],"Invalid startup target")
                    calls[name].add("main")
                else:
                    need(lo<=imm<end and imm2==dest+imm-lo,"Branch leaves its related block")
            else:
                need(imm==imm2,"Changed literal or primitive")
            if op==isa.IO:
                need(0<=imm<len(isa.PRIMITIVES) and old_op[3]==new_op[3]==isa.PRIM_ARITY[isa.PRIMITIVES[imm]],"Different IO signature")
            if op==isa.LOADC:
                code_readers.add(name)
            need(op!=isa.STOREC,"Nominal routine can change the compared code")
    need(code_readers=={"refresh_fields"},"The image observer set changed")
    # A finite fixed point finds precisely the unchanged, transitively closed,
    # non-self-reading routine bodies. Other unchanged bodies are open call sites.
    closed=shared-code_readers
    while True:
        smaller={f for f in closed if calls[f]<=closed}
        if smaller==closed:break
        closed=smaller
    return (dict(closed=sorted(closed),open_spines=sorted(shared-closed-code_readers),
                 self_readers=sorted(code_readers),changed=sorted(old.functions.keys()-shared),
                 added=sorted(new.functions.keys()-old.functions.keys()),
                 compared_cells=sum(left[f][1]-left[f][0] for f in shared),
                 mapped_registers=len(renamed)),renamed)


def scanner_dependencies(isa,c):
    """Changing the installed code payload may affect the offered value, never its address."""
    start,end=segments(c)["refresh_fields"]
    cpu=parent.ParentMachine(isa,c)
    states={start:frozenset()}
    queue=deque([start])
    readers=set();field_calls=set();exit_taint=set()
    while queue:
        pc=queue.popleft();taint=set(states[pc])
        op,a,b,k,imm=isa.decode(c.image[pc])
        src=cpu.capture_indices(op,a,b,k,imm)
        dirty=any(r in taint for r in src)
        if op==isa.LOADC:
            need(not dirty,"Code value controls its next read address")
            readers.add(pc)
            taint.add(a)
        elif op==isa.IO:
            need(isa.PRIMITIVES[imm]=="set_field" and k==4 and
                 all(r not in taint for r in src[:3]),"Self-read controls the field endpoint")
            if dirty:field_calls.add(pc)
            # A different sign or physical refusal can change the port response.
            taint.add(a)
        elif op==isa.STORE:
            need(not dirty,"Image-dependent cursor, address or persistent data")
        elif op in (isa.JZ,isa.JMP,isa.RET):
            need(not dirty,"Image-dependent scan control")
        else:
            need(op in (isa.LI,isa.MOV,isa.LOAD,isa.ADD,isa.SUB,isa.MUL,isa.DIV,isa.MOD,
                        isa.SHL,isa.EQ,isa.LT,isa.LE,isa.AND,isa.OR,isa.NOT),"Unclassified scanner opcode")
            need(op!=isa.LOAD or not dirty,"Image-dependent W lookup")
            if dirty:taint.add(a)
            else:taint.discard(a)
        if op==isa.RET:
            exit_taint.update(taint)
            successors=(start,)  # Abstract next invocation with the same private scratch.
        elif op==isa.JMP:
            successors=(imm,)
        elif op==isa.JZ:
            successors=(pc+1,imm)
        else:
            successors=(pc+1,)
        for nxt in successors:
            need(start<=nxt<end,"Unexpected outward scanner edge")
            updated=frozenset(taint)|states.get(nxt,frozenset())
            if nxt not in states or states[nxt]!=updated:
                states[nxt]=updated
                queue.append(nxt)
    need(len(readers)==len(field_calls)==1,"Scanner has different self-read/output sites")
    for pc,word in enumerate(c.image[:len(c.nodes)]):
        if not start<=pc<end:
            need(exit_taint.isdisjoint(cpu.capture_indices(*isa.decode(word))),
                 "Another procedure consumes image-dependent scanner scratch")
    return dict(loadc=readers.pop(),set_field=field_calls.pop(),reached_opcodes=len(states),
                private_exit_scratch=sorted(exit_taint))


def field_probe(isa,c,cursor,bounds):
    ports=program.ports_class(isa)(c)
    machine=program.initialized(isa,c);k=c.constants
    machine.W[k["VECTOR_CURSOR"]]=cursor
    program.call(isa,c,ports,"refresh_fields",(),bounds["instruction_upper_bounds"]["refresh_fields"]+16,machine)
    expected={}
    for step in range(k["VECTOR_UPDATES"]):
        j=(cursor+step)%k["VECTOR_SLOTS"]
        target,local=divmod(j,2*k["IMAGE_BITS"])
        side,bit=divmod(local,k["IMAGE_BITS"]);address,shift=divmod(bit,k["SYMBOL_BITS"])
        expected[(ports.targets[target],side,bit)]=2*((c.image[address]>>shift)&1)-1
    need(ports.held_fields==expected and machine.W[k["VECTOR_CURSOR"]]==(cursor+7)%k["VECTOR_SLOTS"],
         "Field offers do not describe this actual installed image")
    return expected


def check_live_stack(isa,old,new):
    def one(c):
        lo,end=segments(c)["progress"]
        pc=next(k for k in range(lo,end) if isa.decode(c.image[k])[0]==isa.CALL)
        m=isa.Machine(c)
        ports=program.ports_class(isa)(c)
        m.pc=pc;m.R[1]=1;m.W[0]=len(c.image)
        need(m.step(ports) and m.W[1]==pc+1 and m.R[1]==2,"CALL did not store its actual continuation")
        callee=m.pc
        # Check the actual return primitive with precisely that retained stack.
        child=next(fn for fn in c.functions if c.labels[fn]==callee)
        _,stop=segments(c)[child];m.pc=stop-1
        need(isa.decode(c.image[m.pc])[0]==isa.RET and m.step(ports)
             and m.pc==pc+1 and m.R[1]==1 and m.W[1]==pc+1,"RET rewrote or ignored its saved return address")
        return (pc,child,m.W[1])
    a=one(old);b=one(new)
    need(a[0]-old.labels["progress"]==b[0]-new.labels["progress"] and a[1]==b[1] and a[2]!=b[2],
         "The relocated live-stack discriminator no longer applies")
    return dict(old_call=a[0],new_call=b[0],callee=a[1],old_return=a[2],new_return=b[2])


def paid_source_probe(isa,c,*,stale_binding=False):
    clock,cpu,source,ports=paced.native_fixture(isa,c,adc_first=8*paced.DELTA)
    address=c.labels["publish_plant"]+6
    opcode,_,arg,arity,kind=isa.decode(c.image[address])
    need(opcode==isa.IO and kind==isa.PRIM["source_start_fast"] and arity==1,"Different source aperture")
    cpu.pc=address
    cpu.R[1]=0
    cpu.R[arg]=0
    cpu.R[205 if stale_binding else arg]=1
    source.raw_heads[0]=731;source.raw_heads[1]=877
    cycle=paced.OrdinaryCycle(clock,ports,16*paced.DELTA)
    def move(to):
        clock.run_before(to,lambda due:due[0])
    move(4*paced.DELTA)
    need(cycle.capture()=="bound","Physical instruction capture failed")
    move(8*paced.DELTA)
    need(cycle.offer()=="issued","Physical conversion did not acquire its actual operand")
    clock.edge("ADC")
    claim=source.job
    clock.cut()
    stock=cpu.bank.stock
    move(16*paced.DELTA)
    need(cycle.retire()=="waiting" and cpu.steps==0,"Cut parent acquired a false retirement")
    count=source.adc_bits.get(2052,6)
    for _ in range(count):
        move(clock.clocks["ADC"].due)
        while clock.due():
            clock.edge(clock.due()[0])
    need(claim is not None and not claim.live and source.valid and source.I[1]==(731 if stale_binding else 877) and cpu.bank.stock==stock,
         "Charged ADC failed to use its actual captured operand across cutoff")
    clock.end_check()
    return dict(pc=address,source_argument=arg,count_after_tie=count,source_value=source.I[1],
                cpu_retirements=cpu.steps,parent_E_debit=str(cpu.bank.supplied))


def joined_point(old_registers,new_registers):
    """Use the rail inventory once, then add only the still-absent entries."""
    def ledger(name):
        return json.loads((HERE/name).read_text(encoding="utf8"))
    power=ledger("rx_power_results.json")["budget"]
    gate=ledger("return_seat_results.json")["resources"]
    selector=ledger("matched_publication_results.json")["common_envelope"]
    receiver=ledger("rx_product_results.json")["joined_charge"]
    source=ledger("threshold_gate_source_results.json")["costs"]
    legacy=ledger("legacy_realization_results.json")["inventory"]
    retirement=ledger("parent_retirement_results.json")["resources"]
    new_register_bits=2*(new_registers-old_registers)*256
    new_capture_bits=new_register_bits
    added_bits=new_register_bits+new_capture_bits
    need(new_register_bits>=0 and new_register_bits<=legacy["memory_by_owner"]["code_and_private"]["slack"],
         "Private register allocation does not fit")
    capture_start=gate["descriptor_interval"][1]
    capture_end=capture_start+new_capture_bits
    need(capture_end<=selector["high_metadata_interval"][0],"Capture metadata overlaps another owner")
    # Count an extra bounded update path per new bit even for the private words
    # already covered by the CPU, plus holding and a two-sided boundary burst.
    private_rate=2*added_bits*seat.gates.RATE+Q(added_bits,1024)
    private_burst=2*added_bits
    rate=Q(gate["added_rate"])+Q(selector["common_added_storage_rate"])+private_rate
    burst=Q(gate["added_burst"])+Q(selector["added_burst"])+private_burst
    floor=Q(power["minimum_U"])-burst-2*rate
    supply_slack=Q(power["offered_slack"])-rate
    net_cap=Q(power["new_U_cap"])
    # Independent construction from the seat instead of from the rail point.
    second=(Q(gate["remaining_U"])-Q(power["new_buffers_and_fronts"])-2*Q(power["gross_added_U_peak"])
            -Q(power["spill_free_loss"])-private_burst-2*private_rate)
    need(floor==second and Q(power["new_slope"])==Q(receiver["joined_rate"])+Q(power["gross_added_U_peak"]),
         "The two routes count different reservoirs or work")
    need(net_cap==Q(source["upstream_capacity"])-Q(power["new_buffers_and_fronts"])
         and floor>net_cap/4 and supply_slack>0,"Changed point lost transformed voltage or ordinary supply")
    reaction=Q(power["joined_reaction"])+Q(gate["stated_extra_pilot_reaction"])
    peak=Q(gate["combined_peak"])+Q(power["new_zone_peak_allowance"])+private_rate
    bank=Q(retirement["updated_actual_bank_rate"])+Q(added_bits+2*2048,2048)
    need(bank<=Q(legacy["retained_downrated_bank_allowance"]),"Register holding exceeds the transit design")
    need(Q(source["remaining_old_owner_rate_slack"])>rate,"New private ownership rates exceed incumbent headroom")
    need(reaction<seat.design.EXTRA_REACTION and 41*peak<2**93 and 4*41*peak<2**94,
         "Joined point exceeds the physical ratings")
    return dict(extra_register_bits=new_register_bits,extra_capture_bits=new_capture_bits,
                new_capture_interval=[capture_start,capture_end],extra_private_rate=str(private_rate),
                extra_private_burst=private_burst,bank_rate_upper=str(bank),
                upstream_capacity=str(net_cap),effective_reserve=str(floor),supply_rate_slack=str(supply_slack),
                voltage_floor_margin=str(floor-net_cap/4),reaction=str(reaction),
                reaction_slack=str(seat.design.EXTRA_REACTION-reaction),bath_margin=str(2**94-4*41*peak),
                resource_scope="RX power, return seat and identically installed optional publisher; before marker restoration")


def generate():
    isa=program.load_isa()
    old=program.compile_program(isa,seat.design.design(isa))
    new,b=seat.candidate(isa)
    a=program.bounds(isa,old)
    need(old.constants==new.constants and len(new.image)==len(old.image)==8192,"Different source layout")
    data,registers=compare_code(isa,old,new)
    need({"publish_plant","publish_fast","boot","read_view","permission","estimate"}<=set(data["closed"]),
         "Missing an asserted closed consumer")
    address=next(pc for pc,(x,y) in enumerate(zip(old.image,new.image)) if x!=y)
    bits=old.image[address]^new.image[address]
    changed_bit=192*address+((bits&-bits).bit_length()-1)
    cells_changed=sum(x!=y for x,y in zip(old.image,new.image))
    changed_bits=sum((x^y).bit_count() for x,y in zip(old.image,new.image))
    scans=[scanner_dependencies(isa,c) for c in (old,new)]
    for cursor in (changed_bit,new.constants["VECTOR_SLOTS"]-3):
        x=field_probe(isa,old,cursor,a); y=field_probe(isa,new,cursor,b)
        need(set(x)==set(y),"Addressed scan changed")
        if cursor==changed_bit:need(x!=y,"Lost the new image's material sign change")
    installed=json.loads((HERE/"regional_coupling_results.json").read_text(encoding="utf8"))["world"]["m"]
    point=joined_point(old.next_register,new.next_register)
    targets=tuple("region0/host"+str(t) for t in incidence.neighbors(installed,0))
    cap=Q(seat.record("parent_realization_results.json")["cost_bounds"]["actual_bank_capacity"])
    u=Q(point["upstream_capacity"])
    boot=startup.pc0_boot_prefix(isa,new,b,cap,targets,u,installed)
    need(new.next_register<2048 and 2048+new.constants["DATA_WORDS"]<=8192 and
         b["private_words_with_metadata"]+648<=32768 and b["stack_depth"]==6,"Physical register/W/stack overlay")
    probes=[paid_source_probe(isa,c) for c in (old,new)]
    need(registers[probes[0]["source_argument"]]==probes[1]["source_argument"],"Misplaced physical ADC operand")
    wrong=paid_source_probe(isa,new,stale_binding=True)
    need(wrong["source_value"]!=probes[1]["source_value"],"Stale fixture unexpectedly selected the transported key")
    stack=check_live_stack(isa,old,new)
    assignment=isa.definite_assignment(new)
    need(assignment["every_nominal_local_read_assigned"],"Candidate reads uninitialized nominal locals")
    sources={}
    for file in ("threshold_program_source.py","threshold_program_model.py","threshold_design.py",
                 "return_seat.py","return_seat_results.json","abort_protocol_alternative.py",
                 "parent_realization.py","parent_retirement.py","parent_retirement_results.json","legacy_realization_results.json",
                 "native_clock_source.py","shared_bank_charging.py",
                 "threshold_initialization.py","rx_power_results.json","matched_publication_results.json",
                 "rx_product_results.json","threshold_gate_source_results.json","regional_coupling_results.json"):
        committed=subprocess.check_output(["git","show",SOURCE+":theories-and-designs/byzantine-control/portability/"+file],
                                          cwd=HERE).decode("utf-8-sig").replace("\r\n","\n")
        sources[file]=program.digest(HERE/file)
        need(program.hash_text(committed)==sources[file],"Changed bound image supplier: "+file)
    return dict(base=SOURCE,sources=sources,joined_point=point,
                old_image=program.hash_text(json.dumps(old.image)),new_image=program.hash_text(json.dumps(new.image)),
                static=data,changed_cells=cells_changed,changed_bits=changed_bits,scanner_sites=scans,
                first_changed_bit=changed_bit,paid_adc=probes,old_register_on_new_image=wrong,live_stack=stack,
                assignment=assignment,paid_boot=boot["retired_instructions"],
                paid_boot_next_pc=boot["next_PC"],paid_boot_E=str(boot["paid_parent_prefix"]["actual_operating_transfer"]),
                padded_frame=b["padded_frame_upper"],active_frame=b["active_frame_upper"],new_registers=new.next_register,
                physical_seat_admission=False)


if __name__=="__main__":
    options=argparse.ArgumentParser(description=__doc__)
    options.add_argument("--write",action="store_true")
    args=options.parse_args()
    output=json.dumps(generate(),indent=2,sort_keys=True)+"\n"
    path=HERE/"image_transport_results.json"
    if args.write:path.write_text(output,encoding="utf8",newline="\n")
    else:need(path.read_text(encoding="utf8")==output,"Image transfer evidence changed")
    print("Shared code, image-dependent scan, paid bootstrap and captured ADC checked")
