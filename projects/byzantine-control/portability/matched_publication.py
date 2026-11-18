"""Matched source-side publication policies at fixed external plant and resources.

The executable compares two physical source gating choices, without merging
their traffic, heat, queue histories or all-history guarantees.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path
import subprocess

import input_lifecycle as raw
import legacy_realization as legacy
import parent_realization as parent
import threshold_design as design
import threshold_incidence_model as incidence
import threshold_program_model as program

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = "theories-and-designs/byzantine-control/portability/"
BASE = "61120855ba10eb97e86ce630fdeb1d1355635e97"
GATE_SOURCE = "bb3c68feb4777b1f98ae9e1056176c4525d5be43"
BANK_SOURCE = "e92a77636f43ad6d4ac22cd263f7f32eea5b504b"
charging, BANK_TEXT = legacy.module_at(BANK_SOURCE,"portability/shared_bank_charging.py","_matched_shared_charging")
POPULATION = 12 * (6 + 2**98) + 2
CYCLE = F(1, 2**26)
DELTA = parent.DELTA
NATIVE = parent.NATIVE_RATE
PRICE = 4096
PASS = "forward-all"
SELECT = "subscribed-plant"
MASK = (1 << 256) - 1


def need(condition, message):
    if not condition:
        raise ValueError(message)


def installed_mask(m, origin):
    """Design-time ROM for actual branch ordinals and the two plant keys."""
    receivers = incidence.neighbors(m, origin)
    words = []
    for receiver in receivers:
        pair = tuple(int(origin in incidence.plant_group(m, receiver, key)) for key in (0, 1))
        # Separate physical copies/endpoints for the two receiving banks.
        words.extend((pair, pair))
    return tuple(words)


def cohort_counts(m):
    incidence.check_population(m)
    def number(origin):
        return sum(sum(pair) for pair in installed_mask(m, origin))
    if m < 85:
        h = Counter(number(o) for o in range(m))
    else:
        h = Counter(number(o) for o in (*range(40), *range(m-40,m)))
        # Radius40 covers a receiver's twenty-neighbor radius around a
        # source's twenty-neighbor receiver. Interior translation by4 preserves XXYY.
        for o in range(40,44):
            if o <= m-41:
                h[number(o)] += (m-41-o)//4+1
    need(sum(h.values()) == m and sum(n*v for n,v in h.items()) == 60*m,
         "Source-owner histogram differs from receiver incidence")
    return h


class Selector:
    """Bounded port in the source owner's IO path. The actual CPU pays each read.

    gate_fault is an analytic setting of a local physical series pole.
    Mutable table bits and a changed captured address have this source's
    scope. They never become a client/address writer on the outgoing DATA lead.
    """
    def __init__(self, population, origin, mode):
        need(mode in (PASS, SELECT), "Unknown design wiring")
        self.origin, self.mode = origin, mode
        self.words = [b for pair in installed_mask(population,origin) for b in pair]
        self.gate_fault = "ordinary"
        self.snapshot = [[0]*256 for _ in range(2)]
        self.nodes = [0]*512
        self.mux = [0]*255
        self.clock_open = True
        self.paid = 0
        self.inspected = self.suppressed = self.forwarded = 0

    def decide(self, cpu, client, key):
        need(cpu.pending is not None and cpu.committing and cpu.io_paid
             and cpu.fabric.token is not None and cpu.fabric.token.issued
             and cpu.io_args == (client,key), "Lookup lacks the actual paid IO parent and its captured wires")
        need(self.gate_fault in ("ordinary","pass","drop"),"Out-of-wire fault setting")
        need(all(type(v) is int and -(1<<255)<=v<1<<255 for v in (client,key)), "Not two signed256 ISA operands")
        # Preserve the original result-write/retirement reserve. An unformed
        # short parent can refuse before selecting or offering any DATA slot.
        if cpu.cell.stock < PRICE + parent.FRONT-cpu.pending.launch_work:
            return "lookup-unfunded"
        need(cpu.cell.debit(PRICE),"Lookup exceeds actual parent")
        cpu.lookup_work += PRICE
        self.inspected += 1;self.paid += PRICE
        for row,value in zip(self.snapshot,(client,key)):
            value &= MASK
            for j in range(256):
                row[j]=(value>>j)&1
        if not self.clock_open:
            # The pulse was already dissipated, and the original parent
            # consumes its one issue. No delayed asynchronous grant remains.
            return "interrupted"
        # Independent fixed high-bit reductions. The same buffers are
        # overwritten before consumption even after an earlier bad input.
        cursor=0;high=[]
        for row,skip in zip(self.snapshot,(7,1)):
            level=row[skip:]
            while len(level)>1:
                next_level=[]
                for j in range(0,len(level),2):
                    value=level[j] | (level[j+1] if j+1<len(level) else 0)
                    self.nodes[cursor]=value;cursor+=1;next_level.append(value)
                level=next_level
            high.append(level[0])
        # All 255 local one-bit multiplexers evaluate, including every
        # distributed selection tap. No runtime geometry/membership oracle.
        controls=[self.snapshot[1][0],*self.snapshot[0][:7]]
        level=[*self.words,*([0]*96)];cursor=0
        for select in controls:
            next_level=[]
            for j in range(0,len(level),2):
                v=((1-select) & level[j]) | (select & level[j+1])
                self.mux[cursor]=v;cursor+=1;next_level.append(v)
            level=next_level
        need(cursor==255,"Unpriced mux topology")
        # For a seven-bit index the first invalid value is 64+16.
        low=self.snapshot[0]
        valid_client=not high[0] and not (low[6] and (low[5] or low[4]))
        plant=not high[1]
        bit=level[0]
        grant=(not plant or bit==1 or self.mode==PASS)
        if self.gate_fault=="drop":grant=False
        if self.gate_fault=="pass":grant=True
        for row in self.snapshot:
            for j in range(256):row[j]=0
        if not valid_client:
            return "invalid-client"
        if not grant:
            self.suppressed+=1;return "source-suppressed"
        self.forwarded+=1
        return "forward"


class PublicationParent(charging.FramedParent):
    """The captured instruction retains all existing frontend/result costs."""
    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self.lookup_work=0
    def finish_parent(self,extra_work,native=False):
        extra=self.lookup_work
        self.lookup_work=0
        return super().finish_parent(extra_work+extra,native)
    def step(self,ports):
        # Fixed nominal 2^26/q trace, allowing the full two-delta CPU refill
        # before launch. The source native clock also advances if the CPU waits.
        ports.clock.advance(2*DELTA)
        if self.pending is not None or not self.recharge() or not self.launch():
            return False
        ports.clock.advance(CYCLE-2*DELTA)
        return self.complete(ports) is True


class ComparedSource(raw.LocalSourceBank):
    def recharge_elapsed(self):
        # The common timed chart already advanced to this exact event.
        return F(0)


class SparseFullDelivery(charging.JointCharge):
    """Exact full-rate chart on the coherent traces, with a fixed complete inventory."""
    def __init__(self,bank,cpu,source):
        self.source=source
        self.data_transferred=F(0)
        super().__init__(bank,cpu,source.slots+[source.adc],source.DELTA)

    def charge_time(self,dt):
        need(dt>=0,"Negative elapsed source time")
        if dt==0:return
        p=self.parent
        cpu_open=(p.powered and not p.recharge_inhibit and p.pending is None
                  and p.fabric.token is None and not p.cell.busy)
        cpu_charge=min(p.cell.capacity-p.cell.stock,p.cell.capacity*dt/(2*self.delta)) if cpu_open else F(0)
        charges=[]
        if self.source.powered:
            for slot in self.source.recharge_needed:
                if slot.claim is None or not slot.claim.live:
                    amount=min(slot.cell.capacity-slot.cell.stock,slot.cell.capacity*dt/self.delta)
                    charges.append((slot,amount))
        total=cpu_charge+sum((v for _,v in charges),F(0))
        need(self.bank.stock-total>=1,"Trace leaves the documented full-delivery chart")
        self.bank.stock-=total;self.bank.supplied+=cpu_charge;p.cell.stock+=cpu_charge
        for slot,v in charges:
            slot.cell.stock+=v;slot.cell.received+=v
            self.input_received[slot.native_index]+=v;self.data_transferred+=v
            if slot.cell.stock==slot.cell.capacity:self.source.recharge_needed.discard(slot)
        self.balance()

    def balance(self):
        p=self.parent
        supplied=self.bank.supplied-self.initial_parent_supplied
        need(self.bank.stock+supplied+self.data_transferred==self.initial_bank,"Shared E transfer lost")
        need(p.cell.stock+p.cell.spent+p.cell.dumped==supplied,"Unmatched CPU parcel")

    def full_audit(self):
        # Reconstruct the sparse frame from every actual cell. A non-full,
        # unindexed free capacitor would invalidate the acceleration.
        eligible=[s for s in self.slots if (s.claim is None or not s.claim.live) and s.cell.stock<s.cell.capacity]
        need(all(s in self.source.recharge_needed for s in eligible),"Missing open charger")
        super().balance()


class Timeline:
    def __init__(self,source,bus):
        self.source,self.bus=source,bus
        self.now=F(0);self.period=F(1,4096);self.next=self.period
        self.last_wire=F(0)
    def advance(self,dt):
        dt=F(dt);need(dt>=0,"Negative source interval")
        end=self.now+dt
        while self.next<=end:
            self.bus.charge_time(self.next-self.now)
            self.now=self.next
            for branch in self.source.branches:
                # A full idle lead has zero observable flow. Every live
                # parcel or depleted credit executes the actual lead flow.
                if branch.flights or branch.wire_credit<raw.WIRE_BURST:
                    branch.advance_wire(self.now-self.last_wire,self.source.deliver_symbol)
            self.last_wire=self.now
            self.source.native_tick()
            self.next+=self.period
        self.bus.charge_time(end-self.now)
        self.now=end


def ports_for(isa):
    base=raw.native_source_ports(isa)
    class MatchedPorts(base):
        def __init__(self,c,source,clock,selector):
            super().__init__(c,source)
            self.clock,self.selector=clock,selector
            self.receipts=[]
        def advance(self,machine):
            pass  # PublicationParent.step drives the shared physical timeline.
        def source_operation(self,name,args,machine):
            if name!="source_offer_fast":
                return super().source_operation(name,args,machine)
            client,key=args
            # A physical short across the added series component can pass the
            # original native issue even with its own clock and power absent.
            if self.selector.gate_fault=="bypass":
                outcome="bypass-forward" if 0<=client<80 else "invalid-client"
            else:
                outcome=self.selector.decide(machine,client,key)
            accepted=None
            if outcome in ("forward","bypass-forward"):
                accepted=self.source.branches[client].offer(key,self.source.I[1])
            self.receipts.append((client,key,outcome,accepted))
            return 0
    return MatchedPorts

def record(name):
    return json.loads((HERE/name).read_text(encoding="utf8"))


def fixture(isa,c,origin,mode):
    budget=1<<60
    payer=raw.SourceWork(origin,budget,budget)
    source=ComparedSource(origin,1,payer,POPULATION)
    need(source.reform()=="formed-unpowered","Failed paid source formation")
    capacity=int(record("parent_realization_results.json")["cost_bounds"]["actual_bank_capacity"])
    energy=charging.OperatingBank((origin,1),capacity,budget)
    cpu=PublicationParent(isa,c,bank=energy)
    bus=SparseFullDelivery(energy,cpu,source)
    clock=Timeline(source,bus)
    need(source.begin_entry(energy) and source.entry_flow(F(source.ENTRY_WORK,raw.CLEAR_RATE)),
         "Native cell gates did not form")
    clock.advance(2*DELTA)
    return cpu,ports_for(isa)(c,source,clock,Selector(POPULATION,origin,mode))


def convert(ports,key,value):
    source=ports.source
    source.raw_heads[key]=value
    need(source.source_start("fast",(key,))=="accepted","Input ADC refused")
    ports.clock.advance(F(1,64))
    need(source.valid and source.I[1]==value and source.job is None,"Conversion incomplete")


def wire_lane(ports,receiver):
    source=ports.source
    identity=raw.LaneId(source.origin,source.bank,receiver,1)
    lane=raw.RawLane(POPULATION,identity,source.payer)
    source.attach(lane)
    return lane,2*source.receivers.index(receiver)+1


def nominal(isa,c,mode,origin,receiver):
    cpu,p=fixture(isa,c,origin,mode)
    lane,client=wire_lane(p,receiver)
    for key in (0,1):
        value=(450,1050)[incidence.head_type(origin)]
        convert(p,key,value)
        # Enter the very same compiled fanout helper on the charged parent.
        program.call(isa,c,p,"publish_value",(key,),1000,cpu)
    p.clock.advance(F(1,3))
    s=p.source
    mask=installed_mask(POPULATION,origin)
    admitted=160 if mode==PASS else sum(sum(pair) for pair in mask)
    need(p.selector.inspected==160 and p.selector.paid==160*PRICE and s.publications==admitted,
         "Ordinary healthy publisher did not discharge the expected offers")
    need(all((status=="forward" and admitted=="accepted") if mode==PASS or mask[client][key]
             else (status=="source-suppressed" and admitted is None)
             for client,key,status,admitted in p.receipts), "Lookup and native claims disagree")
    need(s.local_heat==2*4096+3584*admitted and s.transferred_flight==s.flight_heat==512*admitted,
         "Source/lead work partition failed")
    need(sum(branch.sent for branch in s.branches)==4*admitted and not any(b.flights for b in s.branches),
         "Serializer or wire retained an uncounted record")
    need(all(lane.records[k].readable()==value for k in (0,1) if k in lane.records),
         "Installed binding did not receive its physical report")
    p.clock.bus.full_audit()
    return dict(origin=origin,receiving_host=receiver,receiving_bank=1,installed_for_observed_client=list(mask[client]),
                instructions=cpu.steps,clock_q=str(p.clock.now),offers=p.selector.inspected,
                extra_parent_work=p.selector.paid,parent_E_supplied=int(cpu.bank.supplied),source_affine_U_spent=str(s.payer.spent),
                total_native_DATA=admitted,launched_symbols=sum(b.sent for b in s.branches),
                source_local_heat_including_two_conversions=int(s.local_heat),lead_heat=int(s.flight_heat),
                E_delivered_to_DATA_and_ADC=str(p.clock.bus.data_transferred),
                retained_E=str(cpu.bank.stock),attached_lane_plant={str(k):lane.records[k].readable() for k in (0,1) if k in lane.records})


def malicious_offers(isa,cpu,p,offers):
    # Fixed physical C/R corruption in this one publisher. Reuses three
    # actual IO instructions with the client's unchanged original numbers.
    # Other producers and the tested receiver execute the intact image.
    for idx,(client,key) in enumerate(offers):
        cpu.C[idx]=isa.encode(isa.IO,2,3+2*(idx%3),2,isa.PRIM["source_offer_fast"])
        cpu.R[3+2*(idx%3)]=client
        cpu.R[4+2*(idx%3)]=key
    cpu.pc=0;cpu.halted=False
    for _ in offers:
        need(cpu.step(p),"Funded malicious source instruction failed")


def receiver_world(isa,c,primary):
    receiver=0
    lanes={}
    for key in (0,1):
        group=incidence.plant_group(POPULATION,receiver,key)
        for i,origin in enumerate(group):
            if key==1 and i==0:
                need(primary.identity.origin==origin,"Wrong primary")
                lanes[(origin,1)]=primary
            else:
                payer=raw.SourceWork(origin,1<<60,1<<60)
                lane=raw.RawLane(POPULATION,raw.LaneId(origin,1,receiver,1),payer)
                value=450 if key==0 else (1000 if i<8 else 999)
                need("frame" in lane.offer_frame(key,value) and lane.read(key)==value,"Prior framed row failed")
                lanes[(origin,1)]=lane
    class ActualRows(program.ports_class(isa)):
        def perform(self,name,args,machine):
            if name in ("fast_cmp","fast_equal","fast_range"):
                slot,bank,key,*bounds=args
                if key in (0,1) and 0<=slot<15 and bank in (0,1):
                    origin=incidence.plant_group(POPULATION,receiver,key)[slot]
                    lane=lanes.get((origin,bank))
                    self.fast[slot,bank,key]=(raw.MASK if lane is None else lane.private_capture(
                        key,"primary" if slot==0 else "auxiliary"))
            return super().perform(name,args,machine)
    ports=ActualRows(c)
    ports.fast[("head",0)]=ports.fast[("head",1)]=450
    cpu=program.initialized(isa,c);cpu.W[c.constants["ENTRY"]]=1;cpu.enter("frame")
    while not cpu.io_counts["world"] and cpu.steps<100000:
        need(cpu.step(ports),"Intact receiver blocked")
    need(cpu.io_counts["world"]==1 and cpu.C==c.image and not cpu.code_writes,"Receiver C or output changed")
    return list(ports.world_latch),cpu.steps


def saturation(isa,c,mode):
    origin=incidence.plant_group(POPULATION,0,1)[0]
    cpu,p=fixture(isa,c,origin,mode)
    s=p.source;lane,client=wire_lane(p,0);branch=s.branches[client]
    need(lane.decoder.decode(0) is None and lane.decoder.decode(1)==("primary",1),"Wrong fixture binding")
    need("frame" in lane.offer_frame(1,1000),"Old primary failed")
    convert(p,1,999)
    # Phase is just past an ADC edge. All129 captured instructions complete
    # before the next TX edge. Key2 is a real, uninstalled native DATA key.
    malicious_offers(isa,cpu,p,[(client,2)]*127)
    previous=tuple(slot.claim for slot in branch.slots if slot.claim and slot.claim.live)
    need(len(previous)==127 and branch.bits.get(7,8)==127 and s.publications==127,"Old queue incomplete")
    malicious_offers(isa,cpu,p,[(client,0),(client,1)])
    need(all(token.live and token.payload==(2,999) for token in previous),"Old child touched by source filter")
    need(branch.bits.get(7,8)==128 and s.publications==128,"Wrong full-queue effect")
    last=p.receipts[-2:]
    status="full" if mode==PASS else "accepted"
    need(last[-1][-1]==status and last[0][-1]==("accepted" if mode==PASS else None),"Saturation priority failed")
    # No source ATP/true-state reset or gate mutation can cancel buffered work.
    p.selector.gate_fault="drop"
    p.clock.advance(F(1))
    need(branch.sent==512 and not branch.flights and all(not x.live for x in previous),"Old queue failed to drain")
    need(lane.read(1)==(1000 if mode==PASS else 999),"Framed primary mismatch")
    payer_before=s.payer.spent
    world,steps=receiver_world(isa,c,lane)
    need(world==([50,70] if mode==PASS else [50,69]),"Changed row did not reach compiled WORLD")
    p.clock.bus.full_audit()
    return dict(old_real_paid_claims=len(previous),two_results=last,installed_value=lane.read(1),
                native_DATA=s.publications,launched_symbols=branch.sent,receiver_WORLD=world,
                receiver_instructions_to_WORLD=steps,source_local_heat=int(s.local_heat),lead_heat=int(s.flight_heat),
                elapsed_q=str(p.clock.now),source_affine_U_before_WORLD=str(payer_before),
                primary_source_U_after_WORLD=str(s.payer.spent),selector_inhibit_during_old_drain=True)


def stress(isa,c):
    origin=incidence.plant_group(POPULATION,0,1)[0]
    cpu,p=fixture(isa,c,origin,SELECT)
    lane,client=wire_lane(p,0)
    convert(p,1,999)
    def one(key,who=client):
        malicious_offers(isa,cpu,p,[(who,key)])
        return p.receipts[-1][2:]
    outcomes=[one(0),one(-1),one(2003),one(2),one(3),one(0,-1),one(1,80)]
    need(outcomes==[("source-suppressed",None),("forward","malformed"),("forward","malformed"),
                    ("forward","accepted"),("forward","accepted"),("invalid-client",None),
                    ("invalid-client",None)],"Malformed/pass-through paths changed")
    p.selector.clock_open=False
    need(one(1)==("interrupted",None) and p.selector.snapshot[1][0]==1,"Interrupted lookup lost its trace")
    p.selector.gate_fault="bypass"
    paid=p.selector.paid
    need(one(0)==("bypass-forward","accepted") and p.selector.paid==paid,"Physical bypass required a functioning selector")
    need(one(0,80)==("invalid-client",None),"Physical bypass changed the original branch address space")
    p.selector.clock_open=True
    p.selector.gate_fault="pass";need(one(0)==("forward","accepted"),"Force-pass ceased to exist")
    p.selector.gate_fault="drop";need(one(3)==("source-suppressed",None),"Hostile inhibit cannot deny maintenance")
    p.selector.gate_fault="ordinary";p.selector.words[2*client+1]=0
    need(one(1)==("source-suppressed",None),"Source-local corrupt subscription repaired itself")
    old=p.source.publications
    p.source.branches[client].bits.put(28,1,0)
    need(one(3)==("forward","cut") and p.source.publications==old,"Downstream physical cut bypassed")
    p.clock.bus.full_audit()
    return dict(mixed_results=outcomes,malformed_reached_native=True,force_pass_admits_uninstalled=True,
                force_drop_denies_maintenance=True,altered_source_bit_denies_installed=True,
                branch_admission_cut_retained=True,paid_interruption_retained_snapshot=True,actual_bypass_with_stopped_selector=True)



def parser_challenge():
    origin=incidence.plant_group(POPULATION,0,1)[0]
    def run(extra_uninstalled):
        payer=raw.SourceWork(origin,1<<60,1<<60)
        lane=raw.RawLane(POPULATION,raw.LaneId(origin,1,0,1),payer)
        valid=raw.symbols(1,999)
        for value in valid[:2]:
            lane.receive_symbol(value);lane.process_one()
        if extra_uninstalled:
            lane.receive_symbol(raw.symbols(0,17)[0]);lane.process_one()
        for value in valid[2:]:
            lane.receive_symbol(value);lane.process_one()
        for rec in lane.ordered:rec.service()
        return (lane.read(1),lane.parser_number(21,3))
    interrupted=run(True);complete=run(False)
    need(interrupted==(raw.MASK,0) and complete==(999,0),"Uninstalled header lost its parser effect")
    return dict(uninstalled_header_invalidates_installed_partial=True,
                fixed_primary_no_extra_header=complete[0],fixed_primary_with_extra_header="unavailable",
                comparison_scope="Actual charged receiver parser on interrupted input; a source-gate change cannot erase an old header.")

def footprint():
    inv=record("legacy_realization_results.json")["inventory"]["memory_by_owner"]["local_route_metadata"]
    i=record("input_lifecycle_results.json")["resources"]
    r=record("parent_retirement_results.json")["resources"]
    gate_text=legacy.text_at(GATE_SOURCE,"portability/threshold_gate_source_results.json")
    gate_record=json.loads(gate_text)
    for name,digest in gate_record['sources_sha256_lf'].items():
        need(program.hash_text(legacy.text_at(GATE_SOURCE,"portability/"+name))==digest,"Gate record lost its source binding")
    gate=gate_record["costs"]
    # Two private source banks. Ceiling covers all scratch, ROM and constant wiring modes.
    bits=2*2048
    private_per_bank=512+512+160+255+255+128
    need(private_per_bank<2048 and inv["old_owner_allocation"]-inv["new_owner_upper"]>=bits,"Insufficient source metadata")
    rate=2*bits*2**31+F(bits,1024)
    burst=2*bits
    added_stock=F(gate["new_recoverable_storage"])
    U=F(gate["upstream_capacity"])
    need(added_stock==2013265968 and U==F(i["updated_upstream_capacity"])-added_stock,
         "Recoverable gate parcels missing from the common U balance")
    preburst=F(i["updated_upstream_burst"])+F(gate["upstream_burst_added"])
    prerate=F(gate["combined_upstream_rate"])
    need(prerate==F(i["updated_upstream_rate"])+F(gate["upstream_rate_added"])
         and U-preburst-2*prerate==F(gate["minimum_U_after_additions"]),"Prior gate reserve failed to reproduce")
    total_rate=prerate+rate
    total_burst=preburst+burst
    remaining=F(gate["offered_supply"])-total_rate
    reserve=U-total_burst-2*total_rate
    owner_rate_margin=F(gate["remaining_old_owner_rate_slack"])-rate
    gate_start,gate_end=gate["first_descriptor"],gate["end_descriptor_exclusive"]
    selector_start=inv["old_owner_allocation"]-bits
    need((gate_start,gate_end)==(68870516,70402420) and gate_end<=selector_start
         and selector_start-gate_end==gate["owner_slack"]-bits,"Selector overlaps the gate or prior metadata")
    bank_margin=F(record("legacy_realization_results.json")["inventory"]["retained_downrated_bank_allowance"])-F(r["updated_actual_bank_rate"])-F(bits,2048)
    reaction=F(gate["combined_joint_reaction"])
    need(reaction==F(i["complete_joint_reaction"])+F(r["added_parent_gate_reaction"])+F(gate["added_joint_reaction"]),
         "Combined contact loading lost a source stage")
    peak=F(gate["existing_input_combined_peak"])+F(gate["additional_native_service_envelope"])+rate+2*NATIVE
    need(bank_margin>0 and reaction<design.EXTRA_REACTION and 41*peak<2**93
         and 4*41*peak<2**94,"Combined bank, reaction or physical rating failed")
    need(remaining>0 and reserve>2048 and owner_rate_margin>0,"Lost full-host supply envelope")
    lookup_work=512+512+8*255+512+128
    need(lookup_work==3704 and lookup_work<=PRICE,"Mux field price insufficient")
    parent_work=parent.FRONT+4096+PRICE
    latency=F(604,100)*DELTA+F(parent_work+1280,NATIVE)
    need(parent_work<parent.PARENT and latency<F(3,4)*F(100,101)*CYCLE,"Lookup cannot fit the source clock")
    return dict(gate_source=GATE_SOURCE,gate_record_sha256_lf=program.hash_text(gate_text),
                gate_recoverable_stock=int(added_stock),combined_U_capacity=str(U),gate_metadata=[gate_start,gate_end],
                gap_between_gate_and_selector=selector_start-gate_end,combined_upstream_rate=str(total_rate),
                combined_upstream_burst=str(total_burst),remaining_owner_rate=str(owner_rate_margin),
                additional_bits_per_bank_ceiling=2048,explicit_bits_per_bank=private_per_bank,
                high_metadata_interval=[inv["old_owner_allocation"]-bits,inv["old_owner_allocation"]],
                lookup_work_upper=lookup_work,event_work=PRICE,frontend_IO_and_selector=parent_work,available_parent=parent.PARENT,
                service_upper_q=str(latency),shortest_CPU_cycle_q=str(F(100,101)*CYCLE),
                common_added_storage_rate=str(rate),added_burst=burst,remaining_upstream_rate=str(remaining),
                remaining_inventory_reserve=str(reserve),combined_mechanical_reaction=str(reaction),old_E_demand_margin=str(bank_margin),
                native_peak_upper=str(peak),bath_peak_margin=str(2**94-4*41*peak))


def scarce_boundary():
    # CPU and one depleted DATA cell are eligible; all other cells are full,
    # held, or gated. No inflow, bleed or other draw during this short chart.
    deficits=(parent.PARENT,4096)
    rates=(F(parent.PARENT)/(2*DELTA),F(4096)/DELTA)
    dt=1/sum(rates)
    for stock,expected in ((0,0),(2,dt)):
        b=charging.exposure_at_time(stock,deficits,rates,dt,dt/4096)
        need(b.lower==b.upper==expected,"Terminal exposure boundary changed")
    b=charging.exposure_at_time(F(1,2),deficits,rates,dt,dt/4096)
    need(0<b.lower<=b.upper<dt and b.upper-b.lower<=dt/4096,"Scarce duration bracket failed")
    credits=[(r*b.lower,r*b.upper) for r in rates]
    need(all(hi<deficit for (_,hi),deficit in zip(credits,deficits))
         and sum(hi for _,hi in credits)<F(1,2),"A scarce interval funded a new complete parent or created work")
    return dict(source=BANK_SOURCE,shared_bank_sha256_lf=program.hash_text(BANK_TEXT),
                elapsed_q=str(dt),full_stock_two_exposure=str(dt),empty_stock_exposure="0",
                half_stock_exposure_bounds=[str(b.lower),str(b.upper)],credit_bounds=[list(map(str,pair)) for pair in credits],
                neither_initially_empty_capacitor_full_at_end=True,
                no_statement_about_preexisting_funded_children=True)

def collect():
    isa=program.load_isa()
    c=program.compile_program(isa,design.design(isa))
    origin=incidence.plant_group(POPULATION,0,1)[0]
    hist=cohort_counts(POPULATION)
    k=c.constants
    fmin=F(k['FRAME_STEPS'],2**26)*F(100,101)
    levels={}
    for plant in (0,1,2):
        n=k['FAST_BATCH']+plant
        rate=F(n)/fmin
        backlog=2*n+rate/256
        need(backlog<128,"Nominal empty/qualified TX branch exceeds its capacity")
        levels[plant]=dict(records_per_frame=n,arrival_burst=2*n,rate=str(rate),backlog=str(backlog))
    need(levels[2]["backlog"]==record("publication_timing_results.json")["traffic"]["TX_backlog"],"Original traffic import changed")
    image_sha=program.hash_text(json.dumps(c.image))
    for small in (82,84,86,400):
        explicit=Counter(sum(sum(w) for w in installed_mask(small,o)) for o in range(small))
        need(cohort_counts(small)==explicit,"Compressed count failed on a complete small population")
    decoders=0
    for receiver in incidence.neighbors(POPULATION,origin):
        mask=installed_mask(POPULATION,origin)[2*incidence.neighbors(POPULATION,origin).index(receiver)]
        decoder=legacy.ArrivalDecoder(POPULATION,receiver,origin)
        for key in (0,1):
            need(bool(mask[key])==(decoder.decode(key) is not None),"Receiver ROM mismatches source incidence")
            decoders+=1
    ordinary={};saturated={}
    for mode in (PASS,SELECT):
        print("checking physical publisher",mode,flush=True)
        ordinary[mode]=nominal(isa,c,mode,origin,0)
        print("checking saturated receiver",mode,flush=True)
        saturated[mode]=saturation(isa,c,mode)
    a,b=ordinary[PASS],ordinary[SELECT]
    for key in ("instructions","clock_q","offers","extra_parent_work","parent_E_supplied","attached_lane_plant"):
        need(a[key]==b[key],"Changed nominal invariant "+key)
    need(F(b["retained_E"])-F(a["retained_E"])==4096*(a["total_native_DATA"]-b["total_native_DATA"]),
         "Freed slot visits did not preserve actual operating stock")
    dependencies=("input_lifecycle.py","legacy_realization.py","parent_realization.py","parent_retirement.py",
                  "threshold_design.py","threshold_incidence_model.py",
                  "threshold_program_model.py","threshold_program_source.py","publication_timing_results.json",
                  "input_lifecycle_results.json","parent_realization_results.json","parent_retirement_results.json",
                  "legacy_realization_results.json")
    sources={}
    for name in dependencies:
        here=(HERE/name).read_text(encoding="utf8").replace("\r\n","\n")
        at=subprocess.check_output(["git","show",BASE+":"+PREFIX+name],cwd=REPO).decode().replace("\r\n","\n")
        need(here==at,"Different source from the compared point: "+name)
        sources[name]=sha256(here.encode()).hexdigest()
    return dict(base=BASE,source_sha256_lf=sources,source_checker_sha256_lf=sha256(Path(__file__).read_text().encode()).hexdigest(),
                scope="Matched physical source policies and conditional receiver prefixes. Positive-family admission and full RP5 remain open.",
                image_sha256=image_sha,branch_traffic_by_admitted_plant_keys=levels,
                population=POPULATION,forward_DATA=160*POPULATION,subscribed_DATA=60*POPULATION,
                conditional_eliminated_DATA=100*POPULATION,conditional_eliminated_symbols=400*POPULATION,
                conditional_source_heat_difference=358400*POPULATION,
                conditional_flight_heat_difference=51200*POPULATION,
                conditional_gross_work_difference=409600*POPULATION,
                origin_histogram={str(k):v for k,v in sorted(hist.items())},
                small_complete_populations=[82,84,86,400],native_decoder_key_checks=decoders,
                nominal=ordinary,saturation=saturated,challenges=stress(isa,c),partial_frame=parser_challenge(),common_envelope=footprint(),shared_bank=scarce_boundary(),
                RP5_program_PASS=False)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--write",action="store_true")
    args=parser.parse_args()
    payload=json.dumps(collect(),indent=2,sort_keys=True)+"\n"
    target=HERE/"matched_publication_results.json"
    if args.write:
        target.write_text(payload,encoding="utf8",newline="\n")
    else:
        need(target.read_text(encoding="utf8")==payload,"Committed comparison differs from regeneration")
    print("matched publication comparison reproduced",flush=True)


if __name__=="__main__":
    main()
