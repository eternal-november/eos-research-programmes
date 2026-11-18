"""Attach a native clock to an installed gate, without constructing another plant."""
from dataclasses import dataclass
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import argparse
import json
import subprocess

import cam_reformation as cam
import native_clock_source as paced
import parent_retirement as retirement
import shared_bank_charging as charging
import threshold_gate_source as gates
import threshold_initialization as initial
import threshold_incidence_model as incidence

HERE = Path(__file__).resolve().parent
BASE = "43d6674b8b4f7eac75bee7ea5d08ce12e3a83d29"
PACE_BASE = "861a173f668d33897a30aedc71cba41bcfcc93de"
INIT_BASE = "c3812e72db8a62f4ccc79cf88d436636fdfe0fce"
GATE_BASE = "ea3b2478d9d3adff7340fda2a40989ab0fdaa257"
raw = paced.raw
need = paced.need


@dataclass(frozen=True)
class Phases:
    """Rates and times to next edges at this cut, with the preceding RX aperture."""
    adc: tuple
    tx: tuple
    rx: tuple
    prior_return: object
    # Exact entries of the installed face. A pending service time is matched
    # to the retained kind and (for decrements) to the very same paid claim.
    records: dict
    jobs: dict


def attach(bank, phases):
    """Elaborate the retained phase cut over the same physical installation."""
    need(isinstance(bank,gates.LiveSourceBank)
         and bank.fixture.installed_source_ports.get(bank.side) is bank
         and bank.fixture.machines[bank.side] is bank.machine,
         "Require the existing fixture gate at its registered bank")
    cpu, source = bank.machine, bank.native_input
    need(isinstance(source,paced.TimedSource) and source.payer is bank.fixture.source_work
         and source.operating_bank is source.energy is cpu.bank
         and cpu.bank.owner == (bank.fixture.owner,bank.side)
         and all(b.bank is source for b in source.branches), "Source/E/U/parent disagreement")
    bus=getattr(cpu,"charging",None)
    need(bus is not None,"Install the original complete charger before adopting elapsed time")
    for key,(record,kind,claim,delay) in phases.jobs.items():
        lane=source.receivers_live.get(record.lane.identity)
        need(lane is record.lane and lane.records.get(key) is record and
             paced.NativeClock._selected_service(record)==kind and
             (claim is record.claim if kind=="tick" else claim is None),
             "Old service residual belongs to another operation")
    clock = paced.NativeClock(cpu,source,existing_bus=bus,installed_cut=bank.disconnect,
        adc_rate=phases.adc[0],adc_first=phases.adc[1],tx_base_rate=phases.tx[0],tx_first=phases.tx[1],
        rx_base_rate=phases.rx[0],rx_first=phases.rx[1],prior_rx_return=phases.prior_return,
        receipt_clock_specs=phases.records,pending_record_delays={k:v[3] for k,v in phases.jobs.items()})
    return clock


def snapshot(bank):
    """Equality projection over installed stocks, local records, owners and pending operations."""
    source=bank.native_input
    cpu=bank.machine
    bus=cpu.charging
    slot_states=tuple((id(s),id(s.cell),s.cell.stock,s.cell.spent,s.cell.received,
                       id(s.claim),s.claim.live if s.claim else False,s.progress_work)
                      for s in (*source.slots,source.adc))
    flights=tuple((id(b),id(f),id(f.claim),f.claim.live,f.physical_slot,f.remaining,f.stock,f.spent)
                  for b in source.branches for f in b.flights)
    raw_rows=tuple((id(l),id(l.payer),tuple(l.rx),tuple((k,id(rr),rr.value,rr.staged,rr.ttl,
                   tuple(rr.control),id(rr.claim)) for k,rr in l.records.items()))
                   for l in source.receivers_live.values())
    return (id(bank),id(source),id(cpu),id(cpu._body),id(bus),id(cpu.bank),id(source.payer),
            cpu.bank.stock,cpu.bank.supplied,source.payer.stock,source.payer.spent,
            tuple(bus.input_received),cpu.cell.stock,cpu.cell.spent,cpu.cell.dumped,id(cpu.pending),
            id(cpu.fabric.token),cpu.io_paid,cpu.pc,cpu.retired,tuple(source.engine.store),
            tuple(source.I),id(source.job),source.adc_completed,source.reset_work.stock,source.reset_work.spent,
            slot_states,raw_rows,flights,bank.gate,bank.arm,tuple((dest,id(r.pulse),id(r.control))
            for dest,r in bank.rows.items()),tuple((h,cell.stock) for h,cell in bank.fixture.escrow.items()))


def fixture(isa,image,reached):
    """Two source-local entry cuts. Only initialization and genuinely paid rearm produce the native state."""
    origin,side=2, int(reached)
    geom=gates.parameters(image)
    pop=int(gates.record("threshold_initialization_results.json")["population"])
    Ucap=Q(gates.record("threshold_gate_source_results.json")["costs"]["upstream_capacity"])
    cap=int(Q(gates.record("parent_realization_results.json")["cost_bounds"]["actual_bank_capacity"]))
    U=raw.SourceWork(origin,Ucap,Q(2**30))
    targets=tuple(f"region0/host{x}" for x in incidence.neighbors(pop,origin))
    cpus=[]
    for b in (0,1):
        e=charging.OperatingBank((origin,b),cap,Q(cap if b==side else 0))
        cpus.append(charging.FramedParent(isa,image,bank=e,targets=targets))
    cpu=cpus[side]; e=cpu.bank
    state=gates.SharedContacts(geom,origin,U,tuple(cpus),initial_driver=None if reached else side)
    other=1-side
    cpus[other].inhibit()
    state.positions[f"cut{other}"]=geom["CUT_LIMIT"]
    dest=gates.field.Destination(targets[0],1,10)
    def control():return cam.ControlLine(words=[10]*8,valid=[True]*8)
    if reached:
        source=paced.TimedSource(e,U,pop)
        need(source.reform()=="formed-unpowered","Later source failed its actual cold preparation")
    else:
        source=initial.local_source_at_initial_entry(U,e,True,False,pop)
    lane=raw.RawLane(pop,raw.LaneId(origin,side,0,0),U)
    source.attach(lane)
    bus=charging.JointCharge(e,cpu,(*source.slots,source.adc),paced.DELTA)
    if reached:
        need(source.begin_entry(e) and source.entry_flow(Q(source.ENTRY_WORK,raw.CLEAR_RATE))
             and source.reset_work.spent==566835,"Later source control was not physically paid")
        # The actual intact already powered CPU and empty retired-parent state
        # are inputs at this reached cut. This outlet does not create any CPU
        # rearm. The CPU and 10321 data cells share the funded interval.
        bus.flow_full_delivery(paced.DELTA,source_powered=True)
        need(cpu.cell.stock==10240,"Actual shared CPU half-charge missing")
        outgoing=cam.CamBank(gates.field.PulseSelector(),cpu.setter,
            cam.ResidentWord("outgoing frame",side,0,[Q(1)]*192,("frame",)))
        cam.finish(outgoing,cam.VMAX)
        outgoing.activation_to(cam.DRIVER,cam.DRIVER/cam.VMAX)
        state.positions[f"act{side}:0"]=cam.DRIVER
        bank=gates.LiveSourceBank(state,side,outgoing,dest,control())
        bank.wire_input(source)
    else:
        state.positions[f"act{side}:0"]=cam.WARM
        bank=gates.LiveSourceBank.at_initial(state,side,source,control(),
             ((dest,gates.InitialPulseRow(gates.field.PulseSelector(),control())),))
        need(source.reset_work.stock==0 and source.reset_work.spent==0,"Initially running bank rearmed")
    return bank,lane


def run_to(clock,end):
    clock.run_before(end,lambda due:due[0])
    while clock.due():clock.edge(clock.due()[0])


def expect_rejection(func):
    try:func()
    except (ValueError,AssertionError):return
    raise AssertionError("Incompatible wiring or retained choice accepted")


def examples(isa,image,reached):
    bank,lane=fixture(isa,image,reached)
    src=bank.native_input;cpu=bank.machine;bus=cpu.charging
    # Copy-free input state: the ADC, already emitted child, raw FIFO and two
    # concurrent record effects can exist independently of a CPU return.
    src.raw_heads[0]=752
    need(src.source_start("fast",(0,))=="accepted","Missing paid old conversion")
    adc=src.job
    branch=next(b for b in src.branches if b.destination==lane.identity)
    need(branch.offer(0,88)=="accepted" and branch.tick()=="symbol","No funded fixed flight")
    flight=branch.flights[0]
    key=next(k for k,r in lane.records.items() if r.lifetime==8)
    rr=lane.records[key];rr.set_ttl(5);rr.value=11
    need(rr.start_tick()=="started" and rr.stage_receipt(72)=="staged","Old record pair not retained")
    tick=rr.claim
    ordinary_ports=paced.timed_ports(isa)(image,src)
    if reached:
        bus.flow_full_delivery(2*paced.DELTA,source_powered=True)
        cpu.pc=267;cpu.R[205]=0;cpu.R[1]=0
        need(cpu.launch() and cpu.complete(ordinary_ports,pause_after_offer=True)=="waiting"
             and cpu.io_paid and src.job is adc,"Original funded parent/child split absent")
    else:
        bus.flow_full_delivery(paced.DELTA,source_powered=True)
        need(cpu.cell.stock==10240 and cpu.pending is None,"Partially funded parent cut missing")
    pre_interval=(2 if reached else 1)*paced.DELTA
    branch.advance_wire(pre_interval,src.deliver_symbol)
    need(flight.remaining==Q(1,4)-pre_interval and flight.stock==512*flight.remaining,
         "The pre-attachment paid flight lost its actual suffix")
    claim=cpu.pending
    specs={k:(Q(5001,5000),Q(5000,5001)) for k in lane.records}
    base=Q(1,4096);sig=Q(raw.RX_WORK,raw.RX_POWER);res=raw.RECORD_DELAY/3
    # Relative base residual exactly describes the preceding RX selection.
    # The partly spent wire, ADC and raw record retain their separate paid parts.
    phase=Phases((4096,base),(4096,base),(4096,base-sig/2),sig/2,specs,
                 {key:(rr,"tick",tick,res)})
    # Coherent old raw RX capture waiting to pop its existing head.
    need(lane.receive_symbol(raw.symbols(0,12)[0])=="accepted","Old raw head absent")
    need(lane.payer.debit(32),"Initial RX selection stock missing")
    lane.queue.set_number(609,9,lane.queue.number(0,9));lane.rx[608]=1
    before=snapshot(bank)
    foreign=Phases(phase.adc,phase.tx,phase.rx,None,specs,phase.jobs)
    expect_rejection(lambda:attach(bank,foreign))
    need(snapshot(bank)==before and getattr(bus,"native_dispatch",None) is None,
         "Failed phase validation changed the original world")
    wrong=Phases(phase.adc,phase.tx,phase.rx,phase.prior_return,specs,{key:(rr,"tick",None,res)})
    expect_rejection(lambda:attach(bank,wrong))
    clock=attach(bank,phase)
    need(clock.bus is bus and bus.native_dispatch is clock and clock.source is src
         and snapshot(bank)==before and src.job is adc and branch.flights[0] is flight
         and cpu.pending is claim and clock.read_jobs[key][2] is tick,"Attachment reset or duplicated its context")
    expect_rejection(lambda:attach(bank,phase))
    capture_stock=cpu.cell.stock
    if not reached:
        # A half-loaded existing parcel strictly prevents launch, even under
        # initial running controls. Another DELTA supplies its other half.
        need(not cpu.launch(),"Partial parent could already launch")
        clock.advance_to(paced.DELTA)
        need(cpu.cell.stock==20480 and bus.bank.supplied==20480,"Partial parent was replaced or charged twice")
    bank.fixture.positions[f"cut{bank.side}"]=bank.fixture.p["CUT_LIMIT"]
    clock.cut()
    need(bank.cut and not bank.gate and not src.powered and not cpu.powered and (cpu.pending is claim) and src.job is adc and
         branch.flights[0] is flight and lane.rx[608],"Gate cut canceled a paid child")
    bank_stock=cpu.bank.stock
    run_to(clock,sig/2)
    need(not lane.rx[608] and lane.queue.number(9,10)==0,"Old RX phase lost its committed head")
    run_to(clock,res)
    need((rr.value,rr.ttl)==(11,4) and not tick.live,"Wrong old raw decrement")
    run_to(clock,res+raw.RECORD_DELAY)
    need((rr.value,rr.ttl)==(72,8),"Receipt did not use the same raw cell")
    run_to(clock,Q(1,4))
    need(cpu.bank.stock==bank_stock and not adc.live and src.I[1]==752
         and flight.stock==0 and flight.spent==128 and not flight.claim.live
         and cpu.pending is claim and clock.source.receivers_live[lane.identity] is lane,
         "Gate/clock projections disagree on retained work")
    clock.end_check()
    return dict(entry="later paid rearm" if reached else "initial running, empty reset",
        reset_work=src.reset_work.spent,attached_parent_stock=capture_stock,
        originally_issued_cpu_preserved=bool(claim),same_native_E_U_and_bus=True,
        raw_selection_remaining_at_attach=sig/2,old_raw_tick_residual=res,ADC_result=src.I[1],
        old_record_after_pair=(rr.value,rr.ttl),flight_remaining_at_attach=Q(1,4)-pre_interval,flight_work=flight.spent,
        duplicate_driver_refused=True,no_new_E_draw_after_gate_cut=True)


def tied_cut(isa,image,cut_first):
    bank,lane=fixture(isa,image,False)
    src=bank.native_input
    b=next(x for x in src.branches if x.destination==lane.identity)
    need(b.offer(0,71)=="accepted","Source must already own the serializer operation")
    src.tx_phase=3
    period=Q(1,4096)
    phases=Phases((4096,period),(4096,0),(4096,period/2),None,
                  {k:(Q(5001,5000),Q(5000,5001)) for k in lane.records},{})
    clock=attach(bank,phases)
    # The position arrival and its actual disconnection are the one material
    # occurrence at the tied boundary. TX may be ordered before or after it.
    def arrive_at_cut():
        bank.fixture.positions[f"cut{bank.side}"]=bank.fixture.p["CUT_LIMIT"]
        clock.cut()
    if cut_first:arrive_at_cut()
    clock.edge("TX",Q(100,101*4096))
    if not cut_first:arrive_at_cut()
    need(len(b.flights)==int(not cut_first) and bank.cut and not bank.gate
         and not bank.machine.powered and not src.powered,"Tied material cut did not rebase TX")
    work=b.flights[0].stock if b.flights else Q(0)
    need(work==(0 if cut_first else 128),"Wrong retained child for the selected order")
    clock.end_check()
    return dict(cut_first=cut_first,retained_flight=work,TX_local_heat=src.local_heat)


def boundary_checks(isa,image):
    bank,lane=fixture(isa,image,False)
    source,cpu=bank.native_input,bank.machine
    no_source=charging.OperatingBank(cpu.bank.owner,cpu.bank.capacity,cpu.bank.stock)
    different_cpu=charging.FramedParent(isa,image,bank=no_source)
    U=raw.SourceWork(source.payer.origin,source.payer.capacity,source.payer.stock)
    alternative=initial.local_source_at_initial_entry(U,no_source,True,False,source.population)
    projected=charging.JointCharge(no_source,different_cpu,(),paced.DELTA)
    base=Q(1,4096); sigma=Q(raw.RX_WORK,raw.RX_POWER)
    kwargs=dict(adc_first=base,tx_first=base,rx_first=base/2,prior_rx_return=None)
    expect_rejection(lambda:paced.NativeClock(cpu,source,existing_bus=projected,
        receipt_clock_specs={k:(Q(5001,5000),Q(5000,5001)) for k in lane.records},**kwargs))
    expect_rejection(lambda:paced.NativeClock(different_cpu,alternative,existing_bus=projected,**kwargs))
    need(getattr(projected,"native_dispatch",None) is None,"Wrong or projected bus acquired authority")
    # The return of the preceding RX edge is exactly at time zero. Both
    # possible order cuts are retained, even when the head happens to be empty.
    outcomes=[]
    for prior in (None,Q(0)):
        b,l=fixture(isa,image,False)
        ps=Phases((4096,base),(4096,base),(4096,base-sigma),prior,
                  {k:(Q(5001,5000),Q(5000,5001)) for k in l.records},{})
        lookup=b.native_input.receivers_live
        clock=attach(b,ps)
        due=clock.due()
        outcomes.append("rx-commit" in due)
        # Negative control: a retained external alias to the original dict
        # rewires a physical lane. The positive fixed-routing calculation
        # has to reject that changed world before processing another event.
        del lookup[l.identity]
        expect_rejection(clock.next_boundary)
    need(outcomes==[False,True],"Same-time prior return was recreated or lost")
    return dict(foreign_E_refused=True,CPU_only_bus_refused=True,prior_return_due_at_zero=outcomes,
                changed_fixed_lookup_rejected=True)


def generate():
    isa,image,_=retirement.source_inputs()
    def file_at(commit,name):
        path=f"theories-and-designs/byzantine-control/portability/{name}"
        raw_bytes=subprocess.check_output(["git","show",commit+":"+path],cwd=HERE)
        return sha256(raw_bytes.replace(b"\r\n",b"\n")).hexdigest()
    predecessors={commit+":"+f:file_at(commit,f) for commit,files in
        ((PACE_BASE,("native_clock_source.py","native_clock_source_results.json")),
         (INIT_BASE,("threshold_initialization.py","threshold_initialization_results.json")),
         (GATE_BASE,("threshold_gate_source.py","threshold_gate_source_results.json")))
         for f in files}
    sources=("native_clock_source.py","native_clock_source_results.json","threshold_initialization.py",
             "threshold_initialization_results.json","threshold_gate_source.py","threshold_gate_source_results.json",
             "shared_bank_charging.py","SOURCE-CLOCK-WIRING.md","source_clock_wiring.py")
    return gates.normalize(dict(base=BASE,previous=predecessors,sources_sha256_lf={n:initial.program.digest(HERE/n) for n in sources},
        cases=[examples(isa,image,r) for r in (False,True)],
        tied_gate_TX=[tied_cut(isa,image,o) for o in (False,True)],
        wiring_boundaries=boundary_checks(isa,image),scope="single paced receiver and zero-inflow chart",
        whole_program_progress=False,all_history_H=False))


if __name__=="__main__":
    cmd=argparse.ArgumentParser(description=__doc__);options=cmd.add_mutually_exclusive_group(required=True)
    options.add_argument("--write",action="store_true");options.add_argument("--check",action="store_true")
    args=cmd.parse_args(); path=HERE/"source_clock_wiring_results.json"
    text=json.dumps(generate(),indent=2,sort_keys=True)+"\n"
    if args.write:path.write_text(text,encoding="utf-8",newline="\n")
    else:need(path.read_text(encoding="utf-8")==text,"Clock-wiring evidence differs")
    print("PASS retained clock, input, gate and parent world at both entry cuts; whole recurrent source remains open")
