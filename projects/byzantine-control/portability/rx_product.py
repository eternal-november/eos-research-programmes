"""Keyed receiver clocks on one origin's physical banks and raw funding boundary."""
import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from hashlib import sha256
import json
from heapq import heapify,heappop,heappush
from pathlib import Path
import subprocess
from types import MappingProxyType

import native_clock_source as native
import source_clock_wiring as wiring

raw=native.raw
charging=native.charging
gates=wiring.gates
need=native.need
HERE=Path(__file__).resolve().parent
BASE="ca2a00d56d6c5077bf63d148a130d5acb5f205ae"
DIVIDER=618
PRICE=32
BASE_PERIOD=Q(1,4096)
SIGMA=Q(raw.RX_WORK,raw.RX_POWER)
BASE_RANGE=(Q(100,101*4096),BASE_PERIOD)
RECORD_RANGE=(Q(5000,5049),Q(5000,5001))


@dataclass(frozen=True)
class SourcePhases:
    adc: tuple
    tx: tuple


@dataclass(frozen=True)
class LanePhases:
    base: tuple
    prior_return: object
    records: dict
    jobs: dict


class Receiver:
    """A single existing raw lane. No bank, transmitter or global time advance belongs here."""
    _needs_service=staticmethod(native.NativeClock._needs_service)
    _selected_service=staticmethod(native.NativeClock._selected_service)
    _arm_record=native.NativeClock._arm_record

    def __init__(self,lane,phases):
        self.lane=lane
        self.lanes=(lane,)  # Interface to the existing record arbitration law.
        ident=lane.identity
        expected=raw.legacy.ArrivalDecoder(lane.population,ident.receiver,ident.origin)
        need(type(lane.decoder) is raw.legacy.ArrivalDecoder and lane.decoder.tree==expected.tree
             and lane.decoder.words==expected.words,"Raw decoder no longer denotes this physical incidence")
        self.fixed_records=dict(lane.records)
        self.record_wires={}
        for source_key in range(raw.KEYS):
            branch=expected.decode(source_key)
            if branch is None:continue
            role,key=branch
            need(key in self.fixed_records and key not in self.record_wires,"Missing or repeated decoder leaf")
            r=self.fixed_records[key]
            self.record_wires[key]=(r,r.control,source_key,role)
        need(set(self.fixed_records)==set(self.record_wires) and type(lane.ordered) is tuple
             and len(lane.ordered)==len(self.fixed_records)
             and all(r is self.fixed_records[k] for k,r in zip(sorted(self.fixed_records),lane.ordered)),
             "Record lookup and ordered reset do not name the same installed leaves")
        self.ordered=lane.ordered
        self.structure=(ident,lane.payer,lane.queue,lane.rx,lane.queue.values,lane.decode_control,
                        lane.reset_control,lane.reset_work,lane.frame_words,lane.decoder,lane.decoder.tree)
        self.check_layout(all_records=True)
        self.now=Q(0)
        rate,first=phases.base
        self.base=native.Oscillator.at_rate(rate,first,4096,Q(4096*101,100))
        old=self.base.due-self.base.period+SIGMA
        if phases.prior_return is None:
            need(old<=0,"A previously scheduled RX return was lost")
        else:
            need(charging.natural_quantity(phases.prior_return)==old,"Forged old receiving aperture")
        self.aperture=phases.prior_return
        need(set(phases.records)==set(lane.records),"Every installed record has its own retained oscillator")
        self.clocks={k:native.Oscillator.at_rate(rate,first,Q(5001,5000),Q(5049,5000))
                     for k,(rate,first) in phases.records.items()}
        self.tick_times=[(clock.due,k) for k,clock in self.clocks.items()]
        heapify(self.tick_times)
        old_keys={k for k,r in lane.records.items() if self._needs_service(r)}
        need(set(phases.jobs)==old_keys,"Retain every pending raw service")
        self.read_jobs={}
        for k,(r,kind,claim,delay) in phases.jobs.items():
            need(lane.records[k] is r and kind==self._selected_service(r)
                 and (claim is r.claim if kind=="tick" else claim is None)
                 and charging.natural_quantity(delay)<=raw.RECORD_DELAY,"Old service changed owner or deadline")
            self.read_jobs[k]=(delay,kind,claim)
        self.divider_work=Q(0)
        self.edges=0

    def check_layout(self,key=None,*,all_records=False):
        lane=self.lane
        physical=(lane.identity,lane.payer,lane.queue,lane.rx,lane.queue.values,lane.decode_control,
                  lane.reset_control,lane.reset_work,lane.frame_words,lane.decoder,lane.decoder.tree)
        need(all(u is v for u,v in zip(self.structure,physical)) and lane.queue.control is lane.rx
             and lane.ordered is self.ordered,"RX control/FIFO or fixed peripheral binding changed")
        if all_records:need(len(lane.records)==len(self.fixed_records),"A raw record leaf was added or removed")
        for k in (self.record_wires if all_records else (() if key is None else (key,))):
            r,control,source_key,role=self.record_wires[k]
            lifetime=8 if k<2 else 512
            need(type(r) is raw.Record and lane.records.get(k) is r and r.control is control
                 and r.lane is lane and r.key==k and r.source_key==source_key and r.role==role
                 and r.lifetime==lifetime and r.cap==(1<<lifetime.bit_length())-1
                 and r.width==lifetime.bit_length(),"A record no longer names its fixed physical decoder leaf")
            if r.claim is not None and r.claim.live:
                need(type(r.claim) is raw.Claim and r.claim.destination is r and type(r.claim.payload) is int
                     and 0<=r.claim.payload<=r.cap,"A live decrement lacks its physical target or bounded captured word")

    def first_tick(self):
        # Analyst-only index for the independent oscillator deadlines.
        while self.tick_times and self.clocks[self.tick_times[0][1]].due!=self.tick_times[0][0]:
            heappop(self.tick_times)
        return self.tick_times[0][0] if self.tick_times else None

    def next_time(self):
        dates=[self.base.due]+[job[0] for job in self.read_jobs.values()]
        if self.aperture is not None:dates.append(self.aperture)
        tick=self.first_tick()
        if tick is not None:dates.append(tick)
        return min(dates)

    def due(self):
        if self.base.due==self.now:yield ("base",None)
        if self.aperture==self.now:yield ("return",None)
        if self.first_tick()==self.now:
            for key,osc in self.clocks.items():
                if osc.due==self.now:yield ("tick",key)
        for key,job in self.read_jobs.items():
            if job[0]==self.now:yield ("commit",key)

    def act(self,event,next_period=None):
        tag,key=event
        lane=self.lane
        if tag=="base":valid=key is None and self.base.due==self.now
        elif tag=="return":valid=key is None and self.aperture==self.now
        elif tag=="tick":valid=key in self.clocks and self.clocks[key].due==self.now
        else:valid=tag=="commit" and key in self.read_jobs and self.read_jobs[key][0]==self.now
        need(valid,"No such due local event")
        self.check_layout(key,all_records=(tag=="return" and lane.rx[608]!=0))
        if tag in ("base","tick"):
            osc=self.base if tag=="base" else self.clocks[key]
            if next_period is not None:
                lo,hi=BASE_RANGE if tag=="base" else RECORD_RANGE
                value=charging.natural_quantity(next_period)
                need(lo<=value<=hi,"Local oscillator ran outside its envelope")
                osc.period=value
            osc.due+=osc.period
            if tag=="tick":heappush(self.tick_times,(osc.due,key))
        else:
            need(next_period is None,"A return has no new oscillator period")
        if tag=="base":
            self.edges+=1
            self.aperture=self.now+SIGMA
            # Receiver-local parity is native RX control. Its literal clear in
            # the pre-existing bitmap gives zero, not a free reset on release.
            if not lane.write_gate:return "divider-inhibited"
            if not lane.payer.debit(PRICE):return "divider-unfunded"
            self.divider_work+=PRICE
            lane.rx[DIVIDER]=1-lane.rx[DIVIDER]
            return "alternate" if lane.rx[DIVIDER] else native.rx_select(lane)
        if tag=="return":
            self.aperture=None
            result=native.rx_return(lane)
            if result is not None and result!="changed-or-empty-head/drop":
                for k in lane.records:self._arm_record(k)
            return result
        r=lane.records[key]
        if tag=="tick":
            if r.control[r.RECEIPT_VALID] or r.control[r.BUSY]:
                if not r.queued_tick and lane.write_gate and r.control[r.ENABLE] and lane.payer.debit(32):
                    r.queued_tick=True
            else:r.start_tick()
            self._arm_record(key)
            return "tick-opportunity"
        _,kind,claim=self.read_jobs.pop(key)
        funded=kind!="queue" or (lane.write_gate and r.control[r.ENABLE] and lane.payer.stock>=32)
        result=None
        if funded and self._selected_service(r)==kind and (kind!="tick" or r.claim is claim):
            result=r.service()
        self._arm_record(key)
        if kind=="queue" and key in self.read_jobs and self.read_jobs[key][0]==self.now:
            self.read_jobs[key]=(self.now+raw.RECORD_DELAY,*self.read_jobs[key][1:])
        return result

    def stage(self,key,value):
        self.check_layout(key)
        result=self.lane.records[key].stage_receipt(value)
        self._arm_record(key)
        return result


class OriginProduct:
    """Actual E and TX per bank, one U per origin, and one keyed lane at each receiver."""
    def __init__(self,banks,source_phases,lane_phases,*,complete=False):
        need(banks and len(banks)<=2,"One origin has one or two exposed banks")
        banks=tuple(banks)
        self.fixture=banks[0].fixture
        sides={b.side for b in banks}
        need(len(sides)==len(banks) and set(source_phases)==sides,"Missing or duplicated source phase")
        self.receivers={}
        self.banks={}
        captures={}
        private={}
        slots=set()
        outside={}
        registrations=[]
        for b in banks:
            s,cpu=b.native_input,b.machine
            need(b.fixture is self.fixture and b.fixture.installed_source_ports.get(b.side) is b
                 and b.fixture.machines[b.side] is cpu and isinstance(s,native.TimedSource)
                 and s.payer is self.fixture.source_work and s.energy is s.operating_bank is cpu.bank
                 and cpu.bank.owner==(self.fixture.owner,b.side),"Sources do not inhabit the same physical fixture")
            bus=getattr(cpu,"charging",None)
            need(bus is not None and getattr(bus,"native_dispatch",None) is None,
                 "Source bank has no free installed elapsed dispatcher")
            available={br.destination:br for br in s.branches}
            expected=tuple(raw.LaneId(self.fixture.owner,b.side,t,r)
                           for t in wiring.incidence.neighbors(s.population,self.fixture.owner) for r in (0,1))
            need(tuple(br.destination for br in s.branches)==expected and len(available)==80
                 and all(br.bank is s and br.ordinal==j for j,br in enumerate(s.branches)),
                 "The source lacks 80 fixed TX owners")
            outside[b.side]=frozenset(available)-set(s.receivers_live)
            need(not complete or not outside[b.side],"A closed endpoint family must contain all 80 fixed lanes")
            for ident,lane in s.receivers_live.items():
                need(lane.population==s.population and ident==lane.identity and ident in available and ident not in self.receivers
                     and ident in lane_phases and lane.payer is s.payer
                     and (ident.origin,ident.source_bank)==cpu.bank.owner,
                     "Wrong source, lane, U or endpoint")
                # Lane state disjointness, including physical decoder, record
                # cells, raw FIFO values/native control and reset reservoir.
                cells=(lane,lane.queue,lane.rx,lane.queue.values,lane.decode_control,lane.decoder,
                       lane.frame_words,lane.reset_control,lane.reset_work,*(r.control for r in lane.ordered),*lane.ordered)
                ids={id(x) for x in cells}
                need(len(ids)==len(cells) and ids.isdisjoint(slots),"Two sink rows alias installed work or memory")
                slots.update(ids)
                need(set(lane.captures)=={"primary","auxiliary"},"Incomplete capture interface")
                for role,c in lane.captures.items():
                    owner=(ident.origin,ident.receiver,ident.receiver_bank)
                    k=(owner,role)
                    need(type(c) is raw.SharedCapture and c.owner==owner and c.kind==role and c.payer is s.payer
                         and (k not in captures or captures[k] is c)
                         and all(oid not in private or private[oid]==k for oid in (id(c),id(c.cell))),
                         "Capture must be shared across source banks exactly at its physical owner and role")
                    captures[k]=c
                    private[id(c)]=private[id(c.cell)]=k
                self.receivers[ident]=Receiver(lane,lane_phases[ident])
            registrations.append((b,bus,s.receivers_live))
        need(set(lane_phases)==set(self.receivers),"A receiver phase was invented or omitted")
        need(set(private).isdisjoint(slots),"A shared comparison aliases a private receiving row")
        self.outside=MappingProxyType(outside)
        self.captures=MappingProxyType(captures)
        self.capture_bindings={}
        for cap in self.captures.values():
            self.check_capture(cap)
            if cap.pending is not None and cap.pending.live:
                self.capture_bindings[id(cap)]=(cap.pending,*cap.pending.destination)
        try:
            for b,bus,_ in registrations:
                phases=source_phases[b.side]
                self.banks[b.side]=native.NativeClock(
                    b.machine,b.native_input,existing_bus=bus,installed_cut=b.disconnect,external_receivers=True,
                    adc_rate=phases.adc[0],adc_first=phases.adc[1],tx_base_rate=phases.tx[0],tx_first=phases.tx[1])
        except Exception:
            # Construction has not executed an event or moved a resource.
            # Undo only this attempted elaboration's own administrative locks.
            for b,bus,lookup in registrations:
                if b.side in self.banks:
                    del bus.native_dispatch
                    b.native_input.receivers_live=lookup
            raise
        self.now=Q(0)

    def next_time(self):
        return min([c.next_boundary() for c in self.banks.values()]+
                   [r.next_time() for r in self.receivers.values()])

    def due(self):
        return tuple(("source",side,event) for side,c in self.banks.items() for event in c.due())+tuple(
            ("receiver",ident,e) for ident,r in self.receivers.items() for e in r.due())

    def advance(self,moment):
        moment=charging.natural_quantity(moment)
        need(self.now<=moment<=self.next_time(),"Intervening physical boundary")
        dt=moment-self.now
        # Validate every fixed-rate rational chart before mutating any side.
        # Different banks may be differently funded, but do not share E.
        for c in self.banks.values():
            for b in c.source.branches:
                for f in b.flights:
                    need(dt<=f.remaining and f.stock==512*f.remaining and b.flight_cells[f.physical_slot] is f,
                         "Malformed retained flight; no bank has yet advanced")
            if dt and c.bus.bank.stock and (c.cpu.powered or c.source.powered):
                cells,rates=c.bus.ports(c.source.powered)
                gross=sum(min(cell.capacity-cell.stock,rate*dt) for cell,rate in zip(cells,rates))
                need(not gross or c.bus.bank.stock-gross>=1,"A scarce E needs its real flow composition")
                c.bus.balance()
        for c in self.banks.values():c.advance_to(moment)
        self.now=moment
        for r in self.receivers.values():r.now=moment

    def edge(self,event,next_period=None):
        group,owner,action=event
        need((group=="source" and owner in self.banks) or (group=="receiver" and owner in self.receivers),
             "No such occurrence owner")
        if group=="source":
            c=self.banks[owner]
            if isinstance(action,tuple) and action[0]=="deliver":
                need(action in c.due(),"No such due physical arrival")
                branch=c.source.branches[action[1]]
                child=branch.flight_cells[action[2]]
                need(child.claim.destination==branch.destination,"An emitted flight cannot change its original lead")
                if child.claim.destination in self.receivers:
                    self.receivers[child.claim.destination].check_layout()
                if child.claim.destination in self.outside[owner]:
                    # The true emitted symbol crosses the named open port at
                    # this occurrence. This reports an already consumed flight,
                    # and does not confer another spendable sender-side claim.
                    exit_row=(child.claim.destination,child.claim.payload,child.physical_slot)
                    c.edge(action,next_period)
                    return ("external-arrival",exit_row)
            return c.edge(action,next_period)
        return self.receivers[owner].act(action,next_period)

    def check_capture(self,cap):
        claim=cap.pending
        if claim is None or not claim.live:return
        need(type(claim) is raw.Claim and type(claim.destination) is tuple
             and len(claim.destination)==2,"Malformed capture binding")
        lane,key=claim.destination
        saved=self.capture_bindings.get(id(cap))
        if saved is not None:
            need(saved[0] is claim and saved[1] is lane and saved[2]==key,
                 "A live comparison changed its original lane or captured key")
        face=self.receivers.get(lane.identity) if type(lane) is raw.RawLane else None
        need(face is not None and face.lane is lane and key in face.record_wires,
             "Unrepresented pending capture target or foreign physical lane")
        face.check_layout(key)
        owner=(lane.identity.origin,lane.identity.receiver,lane.identity.receiver_bank)
        need(cap.owner==owner and cap.payer is lane.payer and cap is self.captures[owner,cap.kind]
             and self.captures[owner,cap.kind] is lane.captures.get(cap.kind)
             and lane.records[key].role==cap.kind,"Captured read cannot move to another bank/role")

    def capture(self,ident,role,key):
        self.receivers[ident].check_layout(key)
        lane=self.receivers[ident].lane
        need(key in lane.records and lane.records[key].role==role,"Uninstalled raw capture target")
        owner=(ident.origin,ident.receiver,ident.receiver_bank)
        cap=self.captures[owner,role]
        need(lane.captures[role] is cap,"A fixed capture was rebound")
        self.check_capture(cap)
        outcome=cap.begin(lane,key)
        if outcome=="captured":
            self.capture_bindings[id(cap)]=(cap.pending,lane,key)
        elif cap.pending is None or not cap.pending.live:
            self.capture_bindings.pop(id(cap),None)
        return outcome

    def finish_capture(self,ident,role,claim):
        owner=(ident.origin,ident.receiver,ident.receiver_bank)
        cap=self.captures[owner,role]
        need(self.receivers[ident].lane.captures[role] is cap,"A fixed capture was rebound")
        self.check_capture(cap)
        value=cap.finish(claim)
        if cap.pending is None or not cap.pending.live:self.capture_bindings.pop(id(cap),None)
        return value


def phases(lanes, *, simultaneous=True,first=Q(0),pending=None):
    result={}
    for i,l in enumerate(lanes):
        rate=4096 if simultaneous or not i%2 else Q(4096*101,100)
        delay=first if simultaneous else Q(i+1,2**20)
        records={k:(Q(5001,5000),Q(5000,5001)) for k in l.records}
        result[l.identity]=LanePhases((rate,delay),None,records,(pending or {}).get(l.identity,{}))
    return result


def fixtures(isa,image,sides=(0,),additional=True):
    # Real initialized bank A plus optional cold bank B; receiver clocks and
    # raw reservations are origin-affine even when that source bank is cut.
    a,first=wiring.fixture(isa,image,False)
    main=a.native_input
    rows=[first]
    if additional:
        # Distinct receiver bank and a distinct receiver host, on actual fixed leads.
        for dst,db in ((0,1),(1,0)):
            l=raw.RawLane(main.population,raw.LaneId(main.origin,0,dst,db),main.payer)
            main.attach(l);rows.append(l)
    banks=[a]
    if 1 in sides:
        bcpu=a.fixture.machines[1]
        source=wiring.initial.local_source_at_initial_entry(main.payer,bcpu.bank,False,False,main.population)
        charging.JointCharge(bcpu.bank,bcpu,(*source.slots,source.adc),native.DELTA)
        other=raw.RawLane(main.population,raw.LaneId(main.origin,1,0,0),main.payer,first.captures)
        # Cold entry as declared by the initial product. Its later OPEN
        # belongs to the separate receiver reformation, even with source CPU cut.
        other.mode=raw.MASK_MODE;other.masked=True;other.ingress=other.write_gate=False
        other.line=raw.ReassertingControlLine(words=[raw.MASK_MODE]*8,valid=[True]*8)
        source.attach(other)
        endpoint=gates.field.Destination(bcpu.setter.targets[0],1,10)
        bcpu.setter.cut=bcpu.setter.reset_control_inhibit=True
        p=gates.field.PulseSelector(cut=True,reset_control_inhibit=True)
        def cold_line():return gates.cam.ControlLine(words=[0]*8,valid=[True]*8)
        b=gates.LiveSourceBank.at_initial(a.fixture,1,source,cold_line(),
              ((endpoint,gates.InitialPulseRow(p,cold_line())),))
        banks.append(b);rows.append(other)
    return banks,rows


def source_phases(banks,first=BASE_PERIOD):
    return {b.side:SourcePhases((4096,first),(4096,first)) for b in banks}


def cut_origin(banks):
    for b in banks:
        b.fixture.positions[f"cut{b.side}"]=b.fixture.p["CUT_LIMIT"]
        b.disconnect()


def receiver_event(row,name,key=None):
    return "receiver",row.identity,(name,key)


def debit_order(isa,image,reverse):
    banks,rows=fixtures(isa,image)
    U=banks[0].fixture.source_work
    for l in rows:
        need(l.rx[DIVIDER]==0 and l.receive_symbol(raw.symbols(0,73)[0])=="accepted","Fixed FIFO fill failed")
    product=OriginProduct(banks,source_phases(banks),phases(rows))
    cut_origin(banks)
    for l in rows:
        need(product.edge(receiver_event(l,"base"))=="alternate" and l.rx[DIVIDER]==1,
             "Prior funded strobe did not actually set the retained parity")
    previous=sum(r.divider_work for r in product.receivers.values())
    product.advance(SIGMA)
    for l in rows:product.edge(receiver_event(l,"return"))
    product.advance(BASE_PERIOD)
    # Consume other existing work from this very U at the observed cut.
    # It leaves enough for three toggles and two selections, under one order.
    need(U.debit(U.stock-160),"U boundary")
    order=rows[::-1] if reverse else rows
    for l in order:product.edge(receiver_event(l,"base"))
    selected=tuple(l.rx[608] for l in rows)
    need(sum(selected)==2 and U.stock==0,"Receiver acquisitions borrowed or duplicated U")
    while product.due():product.edge(product.due()[0])
    product.advance(BASE_PERIOD+SIGMA)
    for l in order:product.edge(receiver_event(l,"return"))
    need(tuple(l.rx[608] for l in rows)==selected and all(l.queue.number(9,10)==1 for l in rows),
         "Unfunded return removed a paid selection")
    return dict(selected=selected,remaining_U=U.stock,divider_work_at_tie=sum(r.divider_work for r in product.receivers.values())-previous,
                prior_divider_work=previous,old_selected_heads_after_failed_return=selected)


def cross_capture(isa,image,unfunded=False):
    banks,rows=fixtures(isa,image,(0,1))
    a,b=rows[0],rows[-1]
    # A preexisting faulty parity is genuine resettable receiver state. It
    # has no authority to override MASK. The full bitmap traversal clears it.
    b.rx[DIVIDER]=1
    b.fresh_traversal()
    need(b.certificate() and b.rx[DIVIDER]==0,"Existing cold bitmap did not physically clear parity")
    key=next(k for k,r in a.records.items() if k in b.records)
    role=a.records[key].role
    cap=a.captures[role]
    a.records[key].value=71;a.records[key].set_ttl(5)
    b.records[key].value=84;b.records[key].set_ttl(5)
    prod=OriginProduct(banks,source_phases(banks),phases(rows,simultaneous=False))
    need(prod.capture(a.identity,role,key)=="captured","Missing actual first capture")
    first=cap.pending
    first.destination=(b,key)
    wiring.expect_rejection(lambda:prod.finish_capture(a.identity,role,first))
    need(first.live,"Changing a captured sibling consumed the original operation")
    first.destination=(a,key)
    # A new requested bank settles the old captured bank before rebinding.
    if unfunded:
        payer=b.payer
        need(payer.debit(payer.stock-17),"Supply-boundary spend failed")
        result=prod.capture(b.identity,role,key)
        need(result=="unfunded" and cap.pending is None and not first.live and cap.snapshot==71
             and cap.cell.stock==0 and payer.stock==17,"Unfunded second request erased first settlement")
        return dict(result=result,post_snapshot=cap.snapshot,first_closed=True,second_open=False,remaining_U=payer.stock)
    need(prod.capture(b.identity,role,key)=="captured" and not first.live and cap.snapshot==71,
         "New bank overwrote an earlier physical capture")
    second=cap.pending
    need(second is not first and prod.finish_capture(a.identity,role,first)==71 and prod.finish_capture(b.identity,role,second)==84,
         "Old claim replay or wrong shared capture value")
    need(len(prod.banks)==2 and len({id(x.bus.bank) for x in prod.banks.values()})==2
         and prod.banks[0].source.payer is prod.banks[1].source.payer
         and len(prod.captures)==6,"Wrong cap/clock quotient")
    return dict(source_banks=2,distinct_E=2,actual_U=1,installed_lanes=len(rows),
                actual_capture_owners=len(prod.captures),restored_divider=b.rx[DIVIDER],
                charged_raw_reset_work=b.reset_work.spent,first=71,second=84)


def arrivals_and_records(isa,image):
    banks,rows=fixtures(isa,image)
    src=banks[0].native_input
    pending={}
    retained=[]
    for index,l in enumerate(rows[:2]):
        br=next(x for x in src.branches if x.destination==l.identity)
        need(br.offer(0,42+index)=="accepted" and br.tick()=="symbol","Funded fixed flight missing")
        flight=br.flights[0];retained.append((br,flight))
        # A local old stored configuration with matched physical parcel work.
        br.advance_wire(Q(1,4)-SIGMA,src.deliver_symbol)
        k=next(iter(l.records))
        record=l.records[k];record.value=100+index;record.set_ttl(4)
        need(record.start_tick()=="started" and record.stage_receipt(101+index)=="staged","Old jobs absent")
        pending[l.identity]={k:(record,"tick",record.claim,raw.RECORD_DELAY/3)}
        l.rx[DIVIDER]=1
    ph=phases(rows,first=SIGMA,pending=pending)
    prod=OriginProduct(banks,source_phases(banks),ph);cut_origin(banks)
    prod.advance(SIGMA)
    # Same absolute time: first receiver samples before its own arrival, second after.
    for idx,(br,f) in enumerate(retained):
        e=("source",0,("deliver",br.ordinal,f.physical_slot))
        start=receiver_event(rows[idx],"base")
        if idx==0:prod.edge(start);prod.edge(e)
        else:prod.edge(e);prod.edge(start,Q(100,101*4096))
        need(not f.claim.live and f.stock==0 and f.spent==128,"Lost or duplicated symbol work")
    prod.edge(receiver_event(rows[2],"base"))
    prod.advance(2*SIGMA)
    for l in rows:prod.edge(receiver_event(l,"return"))
    queues=[l.queue.number(9,10) for l in rows[:2]]
    need(queues==[1,0],"Different physical read/arrival orders collapsed")
    end=raw.RECORD_DELAY*Q(4,3)
    while prod.next_time()<=end:
        prod.advance(prod.next_time())
        while prod.due():prod.edge(prod.due()[-1])
    vals=[]
    for idx,l in enumerate(rows[:2]):
        key=next(iter(pending[l.identity]))
        r=l.records[key];vals.append((r.value,r.ttl))
        need(r.value==101+idx and r.ttl==r.lifetime,"Other lane interfered with retained record")
    return dict(flight_at_tie=SIGMA,paid_flight_work=256,queues_after_mixed_order=queues,
                post_receipt=vals,source_E_after_cut=src.operating_bank.stock,
                observed_receivers=len(rows))


def complete_roster(isa,image):
    banks,rows=fixtures(isa,image,additional=False)
    src=banks[0].native_input
    for br in src.branches:
        if br.destination in src.receivers_live:continue
        lane=raw.RawLane(src.population,br.destination,src.payer)
        src.attach(lane);rows.append(lane)
    ps=phases(rows,simultaneous=False)
    # The retained independent phases must be phases of their own base:
    # max 80/2^20 < 100/(101*4096). The nonempty raw locations differ by incidence.
    prod=OriginProduct(banks,source_phases(banks),ps,complete=True)
    need(len(prod.receivers)==80 and not prod.outside[0] and len(prod.banks)==1,
         "All eighty actual fixed branches did not bind to this same source")
    total=sum(len(l.records) for l in rows)
    operating=src.operating_bank
    stock=operating.stock
    prod.advance(native.DELTA)
    need(stock-operating.stock==10240 and banks[0].machine.cell.stock==10240
         and not sum(prod.banks[0].bus.input_received),"Receiver count multiplied the CPU's E transfer")
    cut_origin(banks)
    # Each receiver gets its own initial strobe; no source edge is due yet.
    for l in rows:
        prod.advance(prod.next_time())
        while prod.due():prod.edge(prod.due()[0])
        if all(x.edges==1 for x in prod.receivers.values()):break
    # Previous RX returns interleave with later RX starts; finish this slice.
    limit=max(v.base[1] for v in ps.values())
    while prod.next_time()<=limit:
        prod.advance(prod.next_time())
        while prod.due():prod.edge(prod.due()[-1])
    need(all(x.edges==1 and x.lane.rx[DIVIDER]==1 for x in prod.receivers.values())
         and prod.banks[0].edges["TX"]==prod.banks[0].edges["ADC"]==0,
         "Receiver clocks advanced their source or lost a local opportunity")
    return dict(complete_fixed_TX_leaves=80,real_receiver_rows=80,actual_record_clocks=total,
                local_bases_once=80,elapsed=prod.now,source_TX_edges=0,source_ADC_edges=0,
                actual_capture_owners=len(prod.captures),shared_CPU_transfer=stock-operating.stock)


def source_and_boundary(isa,image):
    banks,rows=fixtures(isa,image,additional=False)
    src=banks[0].native_input
    inside=next(x for x in src.branches if x.destination==rows[0].identity)
    outside=next(x for x in src.branches if x.destination!=rows[0].identity)
    need(inside.offer(0,78)=="accepted" and outside.offer(0,79)=="accepted","Two simultaneous TX claims missing")
    # A reached old open-boundary flight and two otherwise enabled branches
    # at the next TX edge. The external receiver is an explicitly open port.
    need(outside.tick()=="symbol","Old lead did not emit")
    child=outside.flights[0]
    outside.advance_wire(Q(1,4)-SIGMA,src.deliver_symbol)
    src.tx_phase=3
    product=OriginProduct(banks,{0:SourcePhases((4096,BASE_PERIOD),(4096,0))},
                          phases(rows,simultaneous=False))
    product.edge(("source",0,"TX"))
    need(src.tx_phase==0 and len(inside.flights)==1 and len(outside.flights)==2
         and product.banks[0].edges["TX"]==1,"One source TX tick was duplicated or lost")
    cut_origin(banks)
    while product.next_time()<SIGMA:
        product.advance(product.next_time())
        while product.due():product.edge(product.due()[0])
    product.advance(SIGMA)
    fact=product.edge(("source",0,("deliver",outside.ordinal,child.physical_slot)))
    need(fact==("external-arrival",(outside.destination,child.claim.payload,child.physical_slot))
         and not child.claim.live and child.spent==128 and len(outside.flights)==1,
         "External receiver responsibility or original work vanished")
    return dict(real_TX_edges=1,fixed_branches_issued=2,external_subroster_ports=len(product.outside[0]),
                old_open_exit=(outside.destination.__dict__,child.physical_slot,child.spent),original_claim_live=child.claim.live)


def shared_bit_discriminator():
    old=0;chosen=[0,0]
    for _ in range(4):
        for i in (0,1):
            old=1-old
            if old==0:chosen[i]+=1
    correct_shared_clock=sum(j%2==0 for j in range(1,5))
    need(chosen==[0,4] and correct_shared_clock==2,"Duplicate mutable source phase was hidden")
    return dict(naive_component_callbacks=chosen,correct_fixed_shared_strobe=[2,2])


def admission_discriminators(isa,image):
    banks,rows=fixtures(isa,image,(0,1))
    phases_in=phases(rows)
    # Two equal-labelled comparison units would mint an additional active
    # capture and break the consuming receiver's bank/key history.
    b=rows[-1];old=b.captures
    b.captures=dict(old)
    b.captures["primary"]=raw.SharedCapture(old["primary"].owner,"primary",b.payer)
    wiring.expect_rejection(lambda:OriginProduct(banks,source_phases(banks),phases_in))
    b.captures=old
    wiring.expect_rejection(lambda:OriginProduct(banks,source_phases(banks),phases_in,complete=True))
    # Fail after the first bank's ownership check. No second dispatcher or
    # published map may survive the failed product installation.
    bad=source_phases(banks)
    bad[1]=SourcePhases((4096,BASE_PERIOD+1),(4096,0))
    lookups=[gate.native_input.receivers_live for gate in banks]
    wiring.expect_rejection(lambda:OriginProduct(banks,bad,phases_in))
    need(all(getattr(gate.machine.charging,"native_dispatch",None) is None
             and gate.native_input.receivers_live is lookup for gate,lookup in zip(banks,lookups)),
         "Partial product installation stranded a bank")
    return dict(equal_label_capture_clone_refused=True,closed_subroster_refused=True,
                late_invalid_source_rolls_back_binding=True)


def protected_wiring(isa,image):
    banks,rows=fixtures(isa,image)
    a,b=rows[:2];p0=source_phases(banks)
    def make(opts=None):return OriginProduct(banks,p0,phases(rows) if opts is None else opts)
    def reject_build(op):
        wiring.expect_rejection(op)
        need(getattr(banks[0].machine.charging,"native_dispatch",None) is None,
             "Rejected physical layout changed elapsed authority")
    original=b.queue.control;b.queue.control=a.rx
    reject_build(make);b.queue.control=original
    key=next(k for k in a.records if k in b.records)
    ra,rb=a.records[key],b.records[key]
    b.records[key]=ra
    reject_build(make);b.records[key]=rb
    original=b.reset_control;b.reset_control=a.reset_control
    reject_build(make);b.reset_control=original
    old=rb.source_key;rb.source_key=raw.KEYS+1
    reject_build(make);rb.source_key=old
    rb.set_ttl(1);ra.set_ttl(5)
    need(ra.start_tick()=="started","Missing genuine old decrement")
    claim=ra.claim
    opts=phases(rows,pending={a.identity:{key:(ra,"tick",claim,Q(0))}})
    claim.destination=rb
    reject_build(lambda:make(opts));claim.destination=ra
    claim.payload=ra.cap+1
    reject_build(lambda:make(opts));claim.payload=4
    prod=make(opts)
    claim.destination=rb
    cost=a.payer.spent
    wiring.expect_rejection(lambda:prod.edge(receiver_event(a,"commit",key)))
    need(a.payer.spent==cost and (ra.ttl,rb.ttl)==(5,1) and claim.live,"Foreign target was written or charged")
    claim.destination=ra
    need(prod.edge(receiver_event(a,"commit",key))=="tick" and (ra.ttl,rb.ttl)==(4,1),"Genuine target was lost")
    # A different legal value of writable control metadata: BUSY with no
    # actual completion. It can stall and retry; it obtains no write anywhere.
    ra.control[ra.BUSY]=1;ra.control[ra.TICK_VALID]=1;ra.claim=None
    face=prod.receivers[a.identity];face._arm_record(key)
    face.now=face.read_jobs[key][0]
    before=a.payer.spent
    need(face.act(("commit",key))=="stale-busy" and a.payer.spent==before
         and (ra.ttl,rb.ttl)==(4,1) and face.read_jobs[key][0]>face.now,
         "A stale busy flag minted a physical decrement")
    return dict(foreign_live_tick_refused=True,foreign_lookup_refused=True,foreign_queue_controls_refused=True,
                foreign_reset_controls_refused=True,wrong_decode_leaf_refused=True,wide_claim_refused=True,
                post_install_foreign_target_refused=True,real_stale_busy="stale-busy")


def full_queue_rank(isa,image):
    banks,rows=fixtures(isa,image,additional=False)
    lane=rows[0];payer=lane.payer
    for _ in range(512):
        need(lane.receive_symbol(1<<80)=="accepted","Initial fully occupied raw FIFO unavailable")
    # Bounded old selected address no longer equals current FIFO head. The
    # preceding return was unfunded before this cut; its claim persists.
    need(payer.debit(32),"Old header annotation lacked real work")
    lane.queue.set_number(609,9,1);lane.rx[608]=lane.rx[DIVIDER]=1
    ps=phases(rows,first=BASE_PERIOD-SIGMA)[lane.identity]
    r=Receiver(lane,ps)
    selects=pops=drops=0
    while lane.queue.number(9,10):
        r.now=r.next_time()
        for e in tuple(r.due()):
            out=r.act(e)
            selects+=int(out=="selected");drops+=int(out=="changed-or-empty-head/drop")
            pops+=int(out=="malformed")
    need(selects==pops==512 and drops==1 and r.now==1025*BASE_PERIOD,
         "Exact stale-fibre FIFO rank missed its physical bound")
    return dict(rank=512,pops=pops,old_dropped=drops,terminal=r.now,base_edges=r.edges)


def money_and_delay():
    host_lanes=2*2*40
    new_burst=2*host_lanes*PRICE
    new_rate=2*host_lanes*PRICE/BASE_RANGE[0]
    gate=gates.record("threshold_gate_source_results.json")["costs"]
    native_point=gates.record("native_clock_source_results.json")["rates"]
    reserve=(Q(gate["minimum_U_after_additions"])-Q(native_point["additional_RX_U_burst"])
             -2*Q(native_point["additional_RX_U_rate"])-new_burst-2*new_rate)
    rate=Q(gate["combined_upstream_rate"])+Q(native_point["additional_RX_U_rate"])+new_rate
    need(reserve>2048 and rate<Q(gate["offered_supply"]),"Receiver clock work omitted or exceeds the offer")
    n=512
    ordinary=2*n*BASE_PERIOD+SIGMA
    retained=(2*n+1)*BASE_PERIOD
    need(retained<Q(513,2048),"Stale aperture can consume the old FIFO bound")
    native_slot=32+32+32+64+11584+512
    need(native_slot<=raw.RX_WORK and DIVIDER>=609+9 and DIVIDER<raw.RX_BITS,
         "Divider overlaps an aperture, exceeds its receiver, or overruns the return allowance")
    return dict(bank_branches=80,per_host_lanes=host_lanes,additional_control_bits=0,repurposed_bit=DIVIDER,
                per_host_divider_burst=new_burst,per_host_divider_rate=new_rate,joined_rate=rate,
                maximum_single_accepted_symbol_work=native_slot,existing_RX_WORK=raw.RX_WORK,
                minimum_joined_U=reserve,ordinary_rank512=ordinary,old_selection_rank512=retained,
                slack_with_old_selection=Q(513,2048)-retained)


def generate():
    isa,image,_=wiring.retirement.source_inputs()
    unit=debit_order(isa,image,False);rev=debit_order(isa,image,True)
    need(unit["selected"]!=rev["selected"],"Shared U failed to distinguish scheduling")
    names=("rx_product.py","RX-PRODUCT.md","native_clock_source.py","native_clock_source_results.json",
           "source_clock_wiring.py","source_clock_wiring_results.json","input_lifecycle.py",
           "threshold_gate_source.py","threshold_gate_source_results.json","threshold_initialization.py")
    return gates.normalize(dict(base=BASE,joined_charge=money_and_delay(),tied_U=[unit,rev],
        cross_bank_capture=cross_capture(isa,image),unfunded_capture=cross_capture(isa,image,True),arrival=arrivals_and_records(isa,image),
        full_roster=complete_roster(isa,image),incompatible_divider_projection=shared_bit_discriminator(),
        full_queue_rank=full_queue_rank(isa,image),
        admission_discriminators=admission_discriminators(isa,image),protected_wiring=protected_wiring(isa,image),
        source_and_open_exit=source_and_boundary(isa,image),
        sources_sha256_lf={n:wiring.initial.program.digest(HERE/n) for n in names},
        prior_clock_sha256=sha256(subprocess.check_output(["git","show",BASE+":theories-and-designs/byzantine-control/portability/native_clock_source.py"],cwd=HERE).replace(b"\r\n",b"\n")).hexdigest(),
        shipped_B_source_complete=False,whole_program_progress=False))


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__);opt=p.add_mutually_exclusive_group(required=True)
    opt.add_argument("--write",action="store_true");opt.add_argument("--check",action="store_true")
    args=p.parse_args();path=HERE/"rx_product_results.json"
    text=json.dumps(generate(),indent=2,sort_keys=True)+"\n"
    if args.write:path.write_text(text,encoding="utf-8",newline="\n")
    else:need(text==path.read_text(encoding="utf-8"),"RX product results changed")
    print("PASS keyed receiving product, actual U collisions, aperture rank and retained captures; source admission open")
