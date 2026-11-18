"""Complete nominal B opcode timing inventory and the producer's local I-word operation."""
import argparse
from collections import Counter
from fractions import Fraction as Q
import json
from pathlib import Path

import native_clock_source as paced
import private_comparison as predicate
import return_seat as seat

HERE=Path(__file__).resolve().parent
need=seat.checks
program=seat.program
raw=seat.raw
parent=seat.parent
charging=seat.charging
D=parent.DELTA
RATE=parent.NATIVE_RATE
MASK=parent.MASK
READ_IMMEDIATE={"source_ieq","source_ilt"}
SCRATCH=READ_IMMEDIATE | {"source_iadd_constant","source_isub_constant","source_iconstant",
                         "source_icopy","source_ilt_register"}
ACQUIRE=paced.OrdinaryCycle.IO


class Scratch:
    def __init__(self, name, args, source, cpu, now):
        self.body=cpu.pending.body
        self.capture=cpu.pending
        self.token=cpu.fabric.token
        self.I=source.I
        self.source=source
        self.operation=name
        self.args=args
        self.destination=None
        self.result=0
        self.done=False
        self.output=None
        self.inputs=()
        self.due=now+Q(4096,1)/RATE
        self.qualified=(source.powered and source.admission and source.dispatch.get(1)
                        and not source.dispatch.get(0))
        if not self.qualified:
            return
        # Capture addressed I at the real source aperture once. The job never
        # uses the raw-word memory as executable instructions or a private PC.
        sources=()
        if name in READ_IMMEDIATE:
            sources=(args[0],)
        elif name=="source_ilt_register":
            sources=args
        else:
            self.destination=args[0]
            if name in ("source_icopy","source_iadd_constant"):
                sources=(args[1],)
            elif name=="source_isub_constant":
                sources=(args[2],)
        valid=lambda j: type(j) is int and 0<=j<8
        self.qualified=all(valid(i) for i in sources) and (self.destination is None or valid(self.destination))
        if self.qualified:
            self.inputs=tuple(self.I[i] for i in sources)

    def settle(self,t):
        need(t==self.due and not self.done,"Wrong or duplicate source-word completion")
        self.done=True
        if not self.qualified:
            return "refused"
        name,args,vs=self.operation,self.args,self.inputs
        if name=="source_iconstant":
            value=args[1]
        elif name=="source_icopy":
            value=vs[0]
        elif name=="source_iadd_constant":
            value=vs[0]+args[2]
        elif name=="source_isub_constant":
            value=args[1]-vs[0]
        elif name=="source_ieq":
            self.result=int(vs[0]==args[1]);value=None
        elif name=="source_ilt":
            self.result=int(vs[0]<args[1]);value=None
        else:
            need(name=="source_ilt_register","Unpriced source arithmetic")
            self.result=int(vs[0]<vs[1]);value=None
        if value is not None:
            # An opened destination cannot replay an earlier spent strobe.
            if not self.source.powered or not self.source.admission:
                return "output-cut"
            self.output=value&MASK
            self.I[self.destination]=self.output
            return "written"
        return "predicate"


class SourceParent(predicate.ComparedParent):
    def complete(self,ports,*,native_ticks=None,clock=True,pause_after_offer=False):
        info=self._io_info()
        if info is None or info[0] not in SCRATCH:
            return super().complete(ports,native_ticks=native_ticks,clock=clock,pause_after_offer=pause_after_offer)
        if not clock or self.return_inhibit or self.committing:
            return "waiting"
        if not self.io_paid:
            return super().complete(ports,pause_after_offer=True)
        op=self.child.physical_ports.scratch
        if not(op.done and op.token is self.fabric.token and op.token.live
               and not self.fabric.return_cut and op.capture is self.pending and self._body is op.body):
            return "waiting"
        self.child.result=op.result
        return super().complete(self.child.physical_ports,clock=clock)


class SourcePorts:
    def __init__(self,clock,ordinary):
        self.clock,self.ordinary=clock,ordinary
        self.source=ordinary.source
        self.scratch=None

    def perform(self,name,args,cpu):
        if name not in SCRATCH:
            return self.ordinary.perform(name,args,cpu)
        need(cpu is self.clock.cpu and cpu.bank is self.source.energy and cpu.io_paid and cpu.io_args is args
             and cpu.fabric.token.issued and (self.scratch is None or self.scratch.done),
             "Foreign RAM chip or overlapping scratch grant")
        self.scratch=Scratch(name,args,self.source,cpu,self.clock.now)
        return 0

    def advance(self,cpu):
        self.ordinary.advance(cpu)


class Cycle(paced.OrdinaryCycle):
    IO=paced.OrdinaryCycle.IO | SCRATCH | {"cpu_count"}


def boundaries(isa,c):
    sites={}
    for pc,cell in enumerate(c.image[:len(c.nodes)]):
        op,dst,reg,n,idx=isa.decode(cell)
        if op!=isa.IO:continue
        name=isa.PRIMITIVES[idx]
        need(n==isa.PRIM_ARITY[name] and reg+n<=c.next_register,"Out-of-range nominal IO")
        sites.setdefault(name,[]).append((pc,dst,reg))
    return sites


def make_source(isa,c,identity=(0,0)):
    er=json.loads((HERE/"parent_realization_results.json").read_text())
    cap=int(Q(er["cost_bounds"]["actual_bank_capacity"]))
    e=charging.OperatingBank(identity,cap,Q(cap))
    ucap=Q(json.loads((HERE/"world_channel_results.json").read_text())["source"]["reduced_U_capacity"])
    u=raw.SourceWork(identity[0],ucap,ucap)
    src=paced.TimedSource(e,u)
    need(src.reform()=="formed-unpowered" and src.begin_entry(e)
         and src.entry_flow(Q(src.ENTRY_WORK,raw.CLEAR_RATE)),"No actual source")
    cpu=SourceParent(isa,c,bank=e)
    clock=paced.NativeClock(cpu,src,external_receivers=True)
    return clock,SourcePorts(clock,paced.timed_ports(isa)(c,src))


def example(isa,c,sites):
    clock,ports=make_source(isa,c)
    cpu=clock.cpu;s=clock.source
    k=c.constants
    def edge(t):
        clock.run_before(t,lambda at:at[0])
        while clock.due():clock.edge(clock.due()[0])
    def call(name,args,interleave=None,stop=False):
        pc,dest,reg=sites[name][0]
        cpu.pc=pc
        for j,v in enumerate(args):
            cpu.R[reg+j]=v&MASK
        live=Cycle(clock,ports,Q(100,101*2**26))
        n=cpu.retired
        edge(live.time(1,4))
        need(live.capture()=="bound","Source parent failed to form")
        edge(live.time(1,2))
        need(live.offer()=="issued" and cpu.retired==n,"Missing split source issue")
        job=ports.scratch
        need(cpu.complete(ports)=="waiting","Premature raw result")
        before=list(s.I)
        if interleave:
            interleave(s)
        if stop:
            clock.cut()
        edge(job.due)
        outcome=job.settle(clock.now)
        edge(live.time(1))
        result=live.retire()
        need(result==("waiting" if stop else "retired") and cpu.retired==n+int(not stop),
             "Nonlocal or duplicate CPU return")
        return dict(name=name,pc=pc,inputs=[str(v) for v in job.inputs],dst=job.destination,
                    result=job.result,changed=[j for j,(a,b) in enumerate(zip(before,s.I)) if a!=b],
                    receipt=outcome,retired=not stop,raw_output=None if job.output is None else str(job.output))
    x=[]
    x.append(call("source_iconstant",(6,0)))
    s.I[1]=MASK-1
    x.append(call("source_iadd_constant",(6,1,5),lambda source:source.I.__setitem__(1,42)))
    need(s.I[6]==3 and s.I[1]==42,"Used a later I word, or a saturating addition")
    x.append(call("source_ilt",(6,4)))
    x.append(call("source_ieq",(6,3)))
    x.append(call("source_isub_constant",(6,1,6)))
    x.append(call("source_ilt_register",(1,6)))
    x.append(call("source_icopy",(1,6)))
    need(s.I[1]==MASK-1 and all(x[j]["result"]==1 for j in (2,3,5)),
         "Signed immediate or unsigned captured comparison changed")
    old=s.I[1]
    x.append(call("source_icopy",(1,10)))
    need(s.I[1]==old and x[-1]["receipt"]=="refused","Uninstalled address selected a stored word")
    s.dispatch.put(1,1,0)
    x.append(call("source_iconstant",(6,22)))
    need(s.I[6]==MASK-1 and x[-1]["receipt"]=="refused","Disabled source minted an observation")
    s.dispatch.put(1,1,1)
    x.append(call("source_iconstant",(6,32),stop=True))
    need(s.I[6]==MASK-1 and x[-1]["receipt"]=="output-cut","Raw strobe wrote through a closed receiving gate")
    oldjob=ports.scratch
    try:oldjob.settle(oldjob.due)
    except (ValueError,AssertionError):pass
    else:raise AssertionError("Spent source strobe replay")
    clock.end_check()
    return dict(source=s.owner if hasattr(s,"owner") else s.origin, bank=cpu.bank.owner,
                actual_retirements=cpu.retired,actual_parent_supply=str(cpu.bank.supplied),operations=x)


def check_math():
    # The original eight-word RAM stores unsigned 256-bit values. The CPU's
    # immediate operand is a signed 256-bit quantity at the IO boundary.
    from itertools import product
    for v,u,i,j in product((0,1,7,1<<127,(1<<255)-1,1<<255,MASK),(-3,0,1,7,1<<127),
                           (-1,0,7,8),(0,6,8)):
        old=[0]*8
        if 0<=j<8:old[j]=v
        for name in sorted(SCRATCH):
            # Each deterministic reference law is checked against the prior
            # independent RawPorts implementation using the actual ops below.
            if name in READ_IMMEDIATE:args=(j,u)
            elif name=="source_iconstant":args=(i,u)
            elif name in ("source_icopy","source_ilt_register"):args=(i,j)
            elif name=="source_isub_constant":args=(i,u,j)
            else:args=(i,j,u)
            yield old,name,args


def compare_reference(isa,c):
    # This fast finite check supplements the clocked source witness; all I
    # accesses below use the actual source's eight physical RAM words.
    from types import SimpleNamespace
    clock,_=make_source(isa,c)
    s=clock.source
    ref=program.ports_class(isa)(c)
    stub=SimpleNamespace(pending=SimpleNamespace(body=clock.cpu._body),fabric=clock.cpu.fabric)
    cnt=0
    for initial,name,args in check_math():
        for j,v in enumerate(initial):s.I[j]=v
        ref.I=list(initial)
        value=ref.perform(name,args,None)
        job=Scratch(name,args,s,stub,0)
        job.settle(job.due)
        need(job.result==value and list(s.I)==ref.I,"Changed local I-word law for "+name)
        cnt+=1
    return cnt

def tied_adc(isa,c,sites,adc_first):
    clock,ports=make_source(isa,c)
    source,cpu=clock.source,clock.cpu
    move=lambda t:clock.run_before(t,lambda at:at[0])
    move(2*D)
    source.raw_heads[0]=73;source.I[1]=11
    need(source.source_start("fast",(0,))=="accepted","Genuine ADC did not capture its raw head")
    count=source.adc_bits.get(2052,6)
    oscillator=clock.clocks["ADC"]
    last=oscillator.due+(count-1)*oscillator.period
    period=16*D
    move(last-period/2)
    pc,dest,reg=sites["source_iadd_constant"][0]
    cpu.pc=pc
    cpu.R[reg:reg+3]=[6,1,0]
    cycle=Cycle(clock,ports,period)
    move(cycle.time(1,4));need(cycle.capture()=="bound","Tie CPU capture missing")
    move(cycle.time(1,2));need("ADC" in clock.due() and clock.now==last and source.job.live,
                             "ADC was not really due with this funded parent")
    if adc_first:clock.edge("ADC")
    need(cycle.offer()=="issued","Missing scratch offer")
    if not adc_first:clock.edge("ADC")
    while clock.due():clock.edge(clock.due()[0])
    job=ports.scratch
    move(job.due);job.settle(clock.now)
    move(cycle.time(1));need(cycle.retire()=="retired","Clocked tie failed to retire")
    need(source.I[6]==(73 if adc_first else 11) and source.I[1]==73 and source.valid
         and cpu.retired==1,"Final values lost physical ADC/copy order")
    clock.end_check()
    return dict(adc_first=adc_first,source_word=source.I[1],saved_fold_word=source.I[6],
                adc_ticks=count,tied_at=str(last),elapsed_to_return=str(clock.now),cpu_retirements=cpu.retired)


def bound(isa,c,b,sites):
    native=ACQUIRE
    private=set(predicate.KINDS)
    special={"cpu_count","yield_frame","set_field","world","send_command"}
    groups={"raw arithmetic":SCRATCH,"source ADC and publication":native,
            "private predicate":private,"individual ports":special}
    require_sets=list(groups.values())
    need(sum(map(len,require_sets))==len(set.union(*require_sets))
         and set(sites)==set.union(*require_sets),"Compiled IO inventory changed")
    # No callee outside refresh_fields has a setter. Every frame enters
    # refresh_fields once; its literal loop has bounded count and no retry.
    import ast
    setters=[f for f,n in c.functions.items() if any(isinstance(x,ast.Call) and
             isinstance(x.func,ast.Name) and x.func.id=="set_field" for x in ast.walk(n))]
    calls=[n for n in c.functions["frame"].body if isinstance(n,ast.Expr) and
           isinstance(n.value,ast.Call) and n.value.func.id=="refresh_fields"]
    need(setters==["refresh_fields"] and len(calls)==1 and c.constants["VECTOR_UPDATES"]==7,
         "Incorrect additive blocking multiplier")
    ordinary={k:getattr(isa,k) for k in ("LI","MOV","ADD","SUB","MUL","DIV","MOD","SHL","AND","OR","EQ",
              "LT","LE","NOT","LOAD","STORE","LOADC","JMP","JZ","CALL","RET","IO")}
    actual=Counter(x[0] for x in c.nodes)
    need(set(actual)<=set(ordinary.values()) and isa.STOREC not in actual and isa.HALT not in actual,
         "Reached an unbudgeted stored-code/native operation in the reference image")
    k=c.constants
    fast=Q(100,101*2**26)
    slow=Q(1,2**26)
    price=json.loads((HERE/"private_comparison_results.json").read_text())["price"]
    selector=json.loads((HERE/"matched_publication_results.json").read_text())["common_envelope"]
    set_cost=json.loads((HERE/"parent_retirement_results.json").read_text())
    setter=json.loads((HERE/"parent_realization_results.json").read_text())["cost_bounds"]
    need(set_cost["checks"]["scanner_actual_setter_offers"]==7
         and Q(setter["setter_time_upper"])<=Q(1,64) and setter["setter_complete_work"]<2**20,
         "The actual source-local setter lacks a qualified finite recharge bound")
    # Two source-I tree walks at depth three, two validity tests on full
    # address operands, two independent latches, four-limb arithmetic/compare,
    # dst commit and stage cleanup. No current operation uses 2 reads AND a write.
    scratch_work=2*3*256+2*256+2*256+128+256+256
    need(scratch_work<=4096 and Q(4096,1)/RATE<fast/4
         and Q(parent.FRONT+4096,1)/RATE<fast/2,"Local scratch issue/result cannot fit")
    need(Q(price["suffix"])<3*fast/4 and Q(2,1)*D<fast/4,"Nominal private or charge interval fails")
    select_bound=Q(604,100)*D+Q(11008+1280,1)/RATE
    need(select_bound < 3*fast/4 and Q(8320+parent.FRONT,1)/RATE<3*fast/4,
         "Paid ALU or publication selector exceeds nominal cycle")
    words=b["padded_frame_upper"]
    extra=k["VECTOR_UPDATES"]*Q(1,64)
    F=words*slow+extra
    Fmin=k["FRAME_STEPS"]*fast
    need(b["active_frame_upper"]<=k["FRAME_STEPS"] and F==Q(1163265,1048576) and Fmin==Q(100,101),
         "Full qualified frame no longer fits the local service tables")
    boot=b["boot_padded_upper"]*slow
    need(b["boot_padded_upper"]<2**64 and words<2**64 and
         Q(12*(k["CONVERSION_POLLS"]-2),1)*fast>Q(1,64),"Modulo/poll deadline changed")
    image=json.loads((HERE/"image_transport_results.json").read_text())["joined_point"]
    world=json.loads((HERE/"world_channel_results.json").read_text())["source"]
    bits=2*1024
    lo=image["new_capture_interval"][1];hi=lo+bits
    need(hi<=selector["high_metadata_interval"][0],"Unassigned raw hold storage insufficient")
    rate=bits*(2*2**31+Q(1,1024));burst=2*bits
    new_floor=Q(world["qualified_voltage_floor_slack"])-2*rate-burst
    new_rate=Q(world["remaining_supply_rate"])-rate
    new_bath=Q(world["combined_bath_margin"])-4*41*2*rate
    need(new_floor>0 and new_rate>0 and new_bath>0,"Common source-I memory overhead exhausts existing margins")
    return dict(installed_reference_code_cells=len(c.nodes),ordinary_opcodes={name:actual[v] for name,v in ordinary.items() if v in actual},
                primitive_sites={name:[pc for pc,_,_ in v] for name,v in sorted(sites.items())},
                groups={key:sorted(v) for key,v in groups.items()},active_frame=b["active_frame_upper"],
                padded_frame_range=[b["padded_frame_lower"],words],qualified_frame_q=[str(Fmin),str(F)],
                clock_cycle_q=[str(fast),str(slow)],qualified_boot_upper=str(boot),source_indexed_work=scratch_work,
                source_read_to_write_upper=str(Q(4096,1)/RATE),scratch_bits=bits,allocation=[lo,hi],
                extra_U_rate=str(rate),extra_U_burst=burst,residual_U_pressure_slack=str(new_floor),
                residual_U_rate_slack=str(new_rate),residual_thermal_slack=str(new_bath),
                setter_count=7,maximum_setter_extra=str(extra),nominal_setter_requires_actual_recharge=True,
                bound_under_arbitrary_raw_values=True,globally_qualified_bank=False)


def generate():
    isa=program.load_isa()
    image,b=seat.candidate(isa)
    sites=boundaries(isa,image)
    costs=bound(isa,image,b,sites)
    return dict(image=program.hash_text(json.dumps(image.image)),certificate=costs,finite_comparison=compare_reference(isa,image),
                ordinary=example(isa,image,sites),
                tied_ADC=[tied_adc(isa,image,sites,order) for order in (False,True)],
                sources={n:program.digest(HERE/n) for n in ("FRAME-PACING.md","frame_pacing.py","private_comparison_results.json",
                    "native_clock_source.py","input_lifecycle.py","matched_publication_results.json",
                    "image_transport_results.json","world_channel_results.json","parent_retirement_results.json",
                    "receiver_lease_results.json","parent_realization_results.json","parent_realization.py","return_seat.py","threshold_program_model.py")})


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--write",action="store_true");args=ap.parse_args()
    result=json.dumps(generate(),sort_keys=True,indent=2)+"\n"
    path=HERE/"frame_pacing_results.json"
    if args.write:path.write_text(result,encoding="utf-8",newline="\n")
    else:need(path.read_text(encoding="utf-8")==result,"Frame receipt differs")
    print("Verified nominal frame timing inventory, bounded source I arithmetic and independent ADC ties")
