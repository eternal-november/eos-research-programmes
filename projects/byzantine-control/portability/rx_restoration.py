"""Marker retirement by actual local passive phase, with an original receiver attached."""
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from pathlib import Path
import argparse
import json

import rx_power as power

rx=power.rx
raw=rx.raw
need=rx.need
HERE=Path(__file__).resolve().parent
BASE="46420801ee20a28b6b460b921f7c08e63b12845a"
C=power.SMALL
DELTA=power.DELTA
REARM=DELTA/8
IDLE=300*C/REARM
LEAK=200*C/(power.STAGE*300*1024)
HOLD=1200*(IDLE+300*LEAK)
M=power.METER
D=power.dec


@dataclass
class Front:
    v: Q
    live: bool=False

    def __post_init__(self):
        self.v=Q(self.v)
        need(0<=self.v<=300 and type(self.live) is bool,"Outside the retained front/selector coordinates")
        if self.v<=100:self.live=False

    def energy(self):
        return C*self.v*self.v/2

    def remaining(self,h):
        return (self.v-100)*h/200 if self.live else Q(0)

    def coast(self,t,h,qualified):
        # The active cap is physically isolated from its charger. The
        # compensated passive sink draws 200C/h while v>=100.
        if self.live:
            rem=self.remaining(h)
            active=min(t,rem)
            self.v-=200*active/h
            if active==rem:self.live=False
            t-=active
        if t and not self.live:
            if qualified:
                # Fixed front regulator + bleed compensation below upper
                # stop. At 300 the bounded excess goes to the local shunt.
                self.v=min(Q(300),self.v+IDLE*t/C)
            else:
                # This operation's qualification is the actual main pressure;
                # unpowered idle fronts never create a new LIVE contact.
                self.v=self.v/(1+t*(LEAK/300)*self.v/C)


@dataclass
class Slot:
    fronts: tuple
    amount: Q=Q(0)
    sink: object=None
    net: Q=Q(0)
    completion: object=None

    @property
    def live(self):
        return all(f.live for f in self.fronts)

    def remaining(self,h):
        return min(f.remaining(h) for f in self.fronts)


class MeteredCell(power.LocalCell):
    """Same terminal energy and fixed local roles; physical fronts decide reuse."""
    def __init__(self,kind,owner,site,voltage,*,front_voltage=300):
        super().__init__(kind,owner,site,voltage)
        self.slots={(name,j):Slot((Front(front_voltage),Front(front_voltage)))
                    for name,(n,_) in power.SLOTS[kind.name].items() for j in range(n)}
        self.padding=[Front(front_voltage) for _ in range(2*(power.MARKERS[kind.name]-len(self.slots)))]
        self.headers={key:0 for key in self.slots}
        self.elapsed_front_input=Q(0);self.front_heat=Q(0)
        # Existing source field; no independent ordinary call or reinitialization.
        self.profile=kind.profile
        self.due_returns=[]
        self.last_outcome=None

    def all_fronts(self):
        for slot in self.slots.values():yield from slot.fronts
        yield from self.padding

    def qualifying(self):
        return self.W>=D(self.s.capacitor*99**2/2)

    @property
    def encumbered(self):
        if not self.profile:return Q(0)
        return sum((s.amount*s.remaining(self.profile)/self.profile for s in self.slots.values()),Q(0))

    def physical_loads(self):
        active=[]
        for (name,index),s in self.slots.items():
            if not s.live:continue
            need(0<=s.amount<=M+power.SLOTS[self.s.name][name][1] and 0<=s.net<=s.amount,
                 "Out-of-range true physical output")
            need(s.sink is None and s.net==0 or (name=="capture-fill"
                 and s.sink is getattr(self,"capture_sink",None) and s.sink is not None),
                 "Old work cannot leave a different physical port")
            active.append(s)
        return active

    def reserve(self,cost,horizon,tag,*,sink=None,net=0):
        name=tag[0] if isinstance(tag,tuple) else tag
        cost,net=Q(cost),Q(net)
        cls=power.SLOTS[self.s.name]
        need(name in cls and cls[name][1]==cost and horizon==self.profile and 0<=net<=cost,
             "No such physical class/price/period")
        need((sink is None)==(net==0) and (sink is None or sink.stock+net<=sink.capacity),
             "Incoherent retained physical sink")
        if sink is not None:
            need(self.s.name=="capture" and name=="capture-fill" and
                 getattr(self,"capture_sink",None) is sink,"Capture lead cannot be rebound")
        word=self.cursor[name];n=cls[name][0]
        need(type(word) is int and 0<=word<512,"Not a nine-wire native value")
        # Unused physical decoder leaves select zero of THIS class. The
        # bounded successor comes back from the selected leaf.
        index=word if word<n else 0
        slot=self.slots[name,index]
        if slot.live or not all(not f.live and f.v==300 for f in slot.fronts):
            self.last_outcome="busy-or-rearming";return False
        if sink is not None and any(s.live and s.sink is sink for s in self.slots.values()):
            self.last_outcome="capture-busy";return False
        available=self.W-D(self.s.floor+self.s.sealed)
        if available<D(M):
            self.last_outcome="underpressure";return False
        accepted=available>=D(M+cost)
        self.cursor[name]=(index+1)%n
        self.headers[name,index]=1 if accepted else 0  # overwrite consumed header before use
        slot.amount=M+(cost if accepted else 0)
        slot.sink=sink if accepted else None;slot.net=net if accepted else Q(0);slot.completion=None
        for f in slot.fronts:f.live=True  # same precharged cap; no energy impulse
        self.last_outcome="granted" if accepted else "paid-refusal"
        return accepted

    def settle_due(self):
        if not self.due_returns:return False
        action,powered=self.due_returns.pop(0)
        action(powered)
        return True

    def unpowered(self,dt,*,defer_at_end=False):
        """No incoming main feed, over the qualified main-pressure subarc.
        Fronts still draw real current from that same local capacitor.
        """
        dt=Q(dt);need(dt>=0 and (dt==0 or not self.due_returns),"Settle the physical return before advancing")
        while dt:
            boundaries=[f.remaining(self.profile) for f in self.all_fronts() if f.live]
            h=min([dt]+boundaries);need(h>0,"Unconsumed front boundary");dt-=h
            active=self.physical_loads()
            payload=sum((s.amount/self.profile for s in active),Q(0))
            fronts=list(self.all_fronts())
            aux=HOLD*len(fronts)
            main_rate=payload+aux
            k=D(2*self.s.bleed/self.s.capacitor)
            W=(self.W+D(main_rate)/k)*(-k*D(h)).exp()-D(main_rate)/k
            need(W>=D(self.s.capacitor*99**2/2),"Split at the main material low-pressure boundary")
            self.leak_heat+=self.W-W-D(main_rate*h);self.W=W
            delivered=Q(0)
            for s in active:
                if s.sink is not None:
                    q=s.net*h/self.profile
                    need(s.sink.stock+q<=s.sink.capacity,"Occupied capture destination")
                    s.sink.stock+=q;s.sink.received+=q;delivered+=q
            self.native_heat+=D(payload*h-delivered)
            before=sum((f.energy() for f in fronts),Q(0))
            for f in fronts:f.coast(h,self.profile,True)
            self.time+=h
            for s in active:
                if not s.live and s.completion is not None:
                    action=s.completion;s.completion=None
                    if defer_at_end and not dt:self.due_returns.append((action,True))
                    else:action(True)
            after=sum((f.energy() for f in fronts),Q(0))
            heat=aux*h-(after-before)
            need(heat>=0,"Fronts generated energy")
            self.elapsed_front_input+=aux*h;self.front_heat+=heat

    def low_unpowered(self,dt):
        """Closed-form no-feed chart at 0..99 V, down to the physical diode."""
        dt=Q(dt);voltage=(2*self.W/D(self.s.capacitor)).sqrt()
        need(not self.due_returns and 0<=voltage<=99 and dt>=0,"Split at the main pressure guard")
        while dt:
            fronts=list(self.all_fronts())
            h=min([dt]+[f.remaining(self.profile) for f in fronts if f.live])
            active=self.physical_loads()
            rate=sum((s.amount/self.profile for s in active),Q(0))
            g=D(self.s.bleed+len(fronts)*HOLD/99**2)
            c=D(self.s.capacitor);d=D(rate/99)
            duration=D(h)
            if d and voltage:
                duration=min(duration,c/g*((voltage+d/g)/(d/g)).ln())
            elif not voltage:duration=Decimal(0)
            v1=max(Decimal(0),(voltage+d/g)*(-g*duration/c).exp()-d/g)
            integral=max(Decimal(0),(c*(voltage-v1)-d*duration)/g)
            primary_energy=self.W-c*v1*v1/2
            service=D(rate/99)*integral
            leak=max(Decimal(0),primary_energy-service)
            self.leak_heat+=leak*D(self.s.bleed)/g
            self.front_heat+=Q(leak*(g-D(self.s.bleed))/g)
            delivered=Q(0)
            for slot in active:
                if slot.sink is not None:
                    received=Q(D(slot.net/(99*self.profile))*integral)
                    need(slot.sink.stock+received<=slot.sink.capacity,"Low-pressure old work escaped its sink")
                    slot.sink.stock+=received;slot.sink.received+=received;delivered+=received
            self.native_heat+=service-D(delivered)
            self.W=c*v1*v1/2;voltage=v1
            before=sum((f.energy() for f in fronts),Q(0))
            for f in fronts:f.coast(h,self.profile,False)
            self.time+=h
            for s in active:
                if not s.live and s.completion is not None:
                    action=s.completion;s.completion=None;action(False)
            self.front_heat+=before-sum((f.energy() for f in fronts),Q(0))
            dt-=h

    def corrupt_headers(self):
        for k in self.headers:self.headers[k]=2**32-1
        for k in self.cursor:self.cursor[k]=511


class ResetCap:
    """Native work interface to one real capacitor. During a CLEAR interval,
    the slot debits are projected at their actual elapsed work clock."""
    def __init__(self,ident,payer,point):
        self.capacity=Q(raw.RESET_CAP)
        self.cell=power.LocalCell(power.catalogue()["reset"],(ident,"reset"),(ident.receiver,ident.receiver_bank),0)
        self.payer=payer;self.point=point;self.spent=Q(0);self.received=Q(0)
        self.window=False;self.start_credit=Q(0);self.slice_used=Q(0)
        self.energy_bounds=None

    @property
    def stock(self):
        if self.window:return self.start_credit-self.slice_used
        if self.energy_bounds is not None:
            lo,hi=self.energy_bounds
            lower=max(0,min(self.capacity,lo-self.cell.s.floor))
            upper=max(0,min(self.capacity,hi-self.cell.s.floor))
            need(lower==upper,"This observation requires a refined actual reset stock")
            return lower
        return Q(max(Decimal(0),min(D(self.capacity),self.cell.W-D(self.cell.s.floor))))

    def charge(self,t,payer):
        need(payer is self.payer and not self.window,"Different reset origin or intervening CLEAR")
        before=self.stock
        self.last_rail=power.held_rail(self.cell,payer,self.point,t)
        self.received+=self.stock-before
        return self.stock-before

    def qualified_charge(self,t):
        spec=self.cell.s
        need(t>=spec.energy200/spec.gain+spec.inlet()["front_time"],"Live pressure interval too short")
        # The real voltage comparison reaches 200 and is inward there on
        # every such rail trajectory. Observe its interval, not a new fill.
        self.energy_bounds=(spec.energy200,spec.ceiling)
        need(self.stock==self.capacity,"Pressure did not entail the complete old usable credit")

    def coast_bounds(self,t,work=0):
        lo,hi=self.energy_bounds
        self.energy_bounds=(max(Q(0),lo-300**2*self.cell.s.bleed*t-work),hi-work)
        self.cell.time+=t

    def debit(self,amount):
        amount=Q(amount)
        need(self.window and amount>=0,"Raw reset work has no elapsed interval")
        if self.stock<amount:return False
        self.slice_used+=amount;return True

    def clear(self,lane,t):
        t=Q(t)
        need(lane.reset_work is self and lane.mode==raw.CLEAR and lane.clear_phase==0 and
             not self.window,"Use a genuine reset phase cut before the unchanged literal sweep")
        interval=self.energy_bounds is not None
        self.start_credit=(max(0,min(self.capacity,self.energy_bounds[0]-self.cell.s.floor))
                           if interval else self.stock)
        self.slice_used=Q(0);self.window=True
        lane.consume(t)
        self.window=False
        z=self.slice_used;self.spent+=z
        h=z/raw.CLEAR_RATE
        if interval:
            need(h<=t and self.start_credit-z>300**2*self.cell.s.bleed*t and lane.cursor==lane.bitmap_bits,
                 "The actual unknown W could alter a native min, clock or terminal")
            self.coast_bounds(t,z);self.cell.native_heat+=D(z)
            return z
        need(h<=t and self.cell.W-D(self.cell.s.floor+z)>D(1),
             "Split the charged reset at its true stock boundary")
        k=D(2*self.cell.s.bleed/self.cell.s.capacitor)
        before=self.cell.W;P=D(raw.CLEAR_RATE)
        self.cell.W=(before+P/k)*(-k*D(h)).exp()-P/k
        self.cell.native_heat+=D(z);self.cell.leak_heat+=before-self.cell.W-D(z)
        self.cell.time+=h
        self.cell.unpowered(t-h)
        return z


def first_bank():
    isa,image,_=rx.wiring.retirement.source_inputs()
    point=power.budgets();origin=2
    U=raw.SourceWork(origin,point["new_U_cap"],point["new_U_cap"]*Q(25,36))
    limits=rx.gates.parameters(image);pop=rx.gates.record("threshold_initialization_results.json")["population"]
    cap=int(Q(rx.gates.record("parent_realization_results.json")["cost_bounds"]["actual_bank_capacity"]))
    targets=tuple(f"region0/host{t}" for t in rx.wiring.incidence.neighbors(pop,origin))
    machines=[];sources=[];rows=[];banks=[]
    for side in (0,1):
        e=rx.charging.OperatingBank((origin,side),cap,Q(cap if not side else 0))
        m=rx.charging.FramedParent(isa,image,bank=e,targets=targets)
        src=rx.wiring.initial.local_source_at_initial_entry(U,e,not side,False,pop)
        if side:
            m.inhibit();m.setter.cut=m.setter.reset_control_inhibit=True
        lane=raw.RawLane(pop,raw.LaneId(origin,side,0,0),U,rows[0].captures if rows else None)
        lane.reset_work=ResetCap(lane.identity,U,point) # the installed cell at allocation
        mode=raw.MASK_MODE if side else raw.OPEN
        lane.mode=mode;lane.masked=bool(side);lane.ingress=lane.write_gate=not side
        lane.line=raw.ReassertingControlLine(words=[mode]*8,valid=[True]*8)
        src.attach(lane);rx.charging.JointCharge(e,m,(*src.slots,src.adc),DELTA)
        machines.append(m);sources.append(src);rows.append(lane)
    fx=rx.gates.SharedContacts(limits,origin,U,tuple(machines),initial_driver=0)
    fx.positions["act0:0"]=rx.gates.cam.WARM;fx.positions["cut1"]=limits["CUT_LIMIT"]
    for side in (0,1):
        mode=0 if side else 10
        line=lambda:rx.gates.cam.ControlLine(words=[mode]*8,valid=[True]*8)
        dest=rx.gates.field.Destination(targets[0],1,10)
        pulse=rx.gates.field.PulseSelector(cut=bool(side),reset_control_inhibit=bool(side))
        banks.append(rx.gates.LiveSourceBank.at_initial(fx,side,sources[side],line(),
                     ((dest,rx.gates.InitialPulseRow(pulse,line())),)))
    world=rx.OriginProduct(banks,rx.source_phases(banks),rx.phases(rows))
    return banks,rows,world


class LiveFaces(power.ReceiverFaces):
    def __init__(self,lane,world):
        self.face=world.receivers[lane.identity];self.face.check_layout(all_records=True)
        key=next(iter(lane.records));spec=power.catalogue()
        self.l=lane;self.r=lane.records[key];self.key=key;self.source=lane.payer
        ident=lane.identity;site=(ident.receiver,ident.receiver_bank)
        self.lane=MeteredCell(spec["rx"],(ident,"rx"),site,200)
        self.records={k:MeteredCell(spec["record"],(ident,k),site,200) for k in lane.records}
        self.record=self.records[key]
        self.stages=[MeteredCell(spec["control"],(ident,j),site if j>=4 else (ident.origin,ident.source_bank),200)
                     for j in range(8)]
        self.stage=self.stages[7]


def bind(lane,world):return LiveFaces(lane,world)


def marker_trace(face):
    cell=face.lane; r=face.l
    initial_W=cell.W
    need(face.base()=="alternate","No true initial RX grant")
    old=cell.slots["divider",0];q=cell.profile
    cell.unpowered(q/3)
    old_phase=old.remaining(q)
    cell.corrupt_headers()
    # Digital corruption can stop an ordinary clock. Keep the actual already
    # committed expenditure and both fractional electrodes in their old state.
    need(old_phase==2*q/3 and old.live and cell.encumbered==(32+M)*Q(2,3),"Lost fractional old grant")
    raw_headers=cell.headers.copy()
    need(face.apply_control(raw.MASK_MODE)=="applied","No paid material MASK")
    oldU=r.payer.stock
    need(face.base()=="divider-inhibited","Old native interval reissued through MASK")
    cell.unpowered(old_phase)
    need(not old.live and cell.encumbered==0 and cell.native_heat==32+M
         and r.payer.stock==oldU and cell.headers==raw_headers,
         "Old work/reset bits confused with true output authority")
    cell.unpowered(REARM)
    need(all(f.v==300 and not f.live for f in old.fronts) and cell.cursor["divider"]==511,
         "Quiescence forged an initialization")
    # Keep MASK while the same final-stage slot really recharges. A new OPEN
    # is its own separately qualified physical contact, not an expiry event.
    face.stage.unpowered(2*power.STAGE)
    need(face.apply_control(raw.OPEN)=="applied" and not old.live,"OPEN itself launched the stale marker")
    need(face.base()!="divider-unfunded" and old.live and cell.cursor["divider"]==0,
         "Paid ingress failed to overwrite an invalid nine-bit address in its one-slot class")
    need(cell.W<initial_W and cell.front_heat>=0,"Restoration was unfunded")
    return dict(old_remaining=old_phase,old_work=32+M,stale_headers_survive=len(raw_headers),
                total_old_to_fully_rearmed=old_phase+REARM,actual_dropouts=2,new_slot_index=0,
                front_work=str(cell.front_heat))


def row_clear(face):
    # The original real bitmap still owes its own paid reset. The local
    # physical source supplies this stocked reset after its qualified CHARGE.
    l=face.l
    l.poison(include_shared=False)
    for x in (face.lane,face.record,*face.stages):x.corrupt_headers()
    need(face.apply_control(raw.MASK_MODE)=="applied","Unfunded MASK")
    for cell in (face.lane,face.record):cell.unpowered(power.STAGE+REARM)
    # Enter and execute the original local RESET-work operation. No new
    # marker bytes have been appended to its serialized addresses.
    face.stage.unpowered(2*power.STAGE)
    need(face.apply_control(raw.CHARGE)=="applied","CHARGE not funded")
    point=power.budgets();reset=l.reset_work;capacity=reset.capacity
    need(reset.payer is l.payer and reset.stock==0,"Existing local reset carrier or source changed")
    duration=reset.cell.s.energy200/reset.cell.s.gain
    l.consume(duration)
    need(reset.stock==capacity and reset.last_rail["upstream_debit"]>0,"Missing interior rail flow")
    before=reset.spent
    face.stage.unpowered(2*power.STAGE)
    need(face.apply_control(raw.DUMP)=="applied","DUMP not funded")
    face.stage.unpowered(2*power.STAGE)
    need(face.apply_control(raw.CLEAR)=="applied","CLEAR not funded")
    reset.clear(l,Q(1,2))
    spent=reset.spent-before
    need(0<spent<=point["remote_reset_clear_bound"]*raw.CLEAR_RATE and l.cursor==l.bitmap_bits,
         "Existing reset bitmap not actually traversed")
    face.stage.unpowered(2*power.STAGE)
    need(face.apply_control(raw.OPEN)=="applied" and l.certificate(),"Incomplete live receiver entry")
    # Previously corrupt ordinary record bits now perform the actual fresh
    # operation, with metering headers lazily overwritten in this same store.
    face.r.set_ttl(3)
    need(face.tick()=="started","Fresh old store could not create a real held operation")
    face.record.unpowered(raw.RECORD_DELAY)
    need(face.service()=="tick" and face.r.ttl==2,"Fresh record acted on a stale destination")
    return dict(old_serial_work=spent,old_bitmap=l.bitmap_bits,new_marker_sweep_work=0,
                actual_reset_usable=capacity,hot_fresh_post=face.r.ttl)




def stage_event(face,i,code):
    l=face.l.line;meter=face.stages[i]
    actual=[slot for slot in meter.slots.values() if slot.live and slot.completion is not None]
    if actual or meter.due_returns:return "busy"
    n=power.SLOTS["control"]["copy"][0];j=meter.cursor["copy"]
    need(type(j) is int and 0<=j<512,"Out-of-width physical stage cursor")
    j=j if j<n else 0
    if not meter.reserve(raw.cam.STAGE_PRICE,power.STAGE,("copy",i)):return "unavailable"
    # A genuine new financed ingress overwrites its consumed header. A stale
    # BUSY bit has no path to the old physical copy's return strobe.
    l.snapshots[i]=None;l.remaining[i]=0
    l.capture(i,code)
    claim=raw.Claim((l,i),None);meter.last_stage_outcome="pending"
    def terminal(powered):
        returned=l.snapshots[i]
        def settle(bound,_):
            line,k=bound
            if powered and returned is not None:
                value,valid=returned
                line.words[k]=value;line.valid[k]=valid
                meter.last_stage_outcome=value if valid else 15
                if k==7:meter.application=face.apply_control(meter.last_stage_outcome)
            else:meter.last_stage_outcome="withdrawn"
            line.snapshots[k]=None;line.remaining[k]=0
        need(claim.destination==(l,i) and claim.dispatch(settle),"Old copy's captured return was rebound")
    meter.slots["copy",j].completion=terminal
    return "captured"


def stage_return(face,i):
    # Observation only; the physical endpoint forced and consumed the strobe.
    return getattr(face.stages[i],"last_stage_outcome","no-operation")


def control_trace(face):
    line=face.l.line;h=power.STAGE
    for i,cell in enumerate(face.stages):
        cell.corrupt_headers()
        line.words[i]=15;line.valid[i]=False
        # A source-legal dirty digital BUSY/snapshot and fractional elapsed
        # field need not be a separately funded physical copy.
        line.snapshots[i]=(3,True);line.remaining[i]=h*Q(17,31)
    need(stage_return(face,7)=="no-operation","Writable dirty stage manufactured a commit")
    input_mode=raw.MASK_MODE;p=Q(1,8)
    # True independent base phases need not coincide. This example staggers
    # them so each stage sees the actual previous output, never an oracle.
    staggers=[Q(i+1,16)*p for i in range(8)]
    for i,s in enumerate(face.stages):
        t=staggers[i]
        s.unpowered(t-s.time)
        need(stage_event(face,i,input_mode)=="captured" and stage_return(face,i)=="pending",
             "Paid stage failed to take its prior wire or published early")
        # Writable phase can still be stale; it does not create another return.
        s.unpowered(h/3);line.remaining[i]=h*Q(29,31)
        s.unpowered(2*h/3)
        need(stage_return(face,i)==input_mode,"Propagated mode was guessed")
    need(face.stage.application=="applied" and face.l.masked,"No receiving MASK")
    return dict(first_actual_strobe=staggers[0],last_commit=staggers[-1]+h,
                admitted_staggered_stages=8,mapped_mode=line.words[7])


def old_return_at_boundary(face):
    stage=face.stages[0]
    need(stage_event(face,0,raw.DUMP)=="captured","No genuine pending final strobe")
    stage.unpowered(power.STAGE,defer_at_end=True)
    need(stage.due_returns and not any(s.live for s in stage.slots.values()),
         "A true issued return vanished at voltage cutoff")
    need(stage_event(face,0,raw.OPEN)=="busy","New stage overwrote an already issued same-time return")
    rx.wiring.expect_rejection(lambda:stage.unpowered(REARM))
    need(stage.settle_due() and stage_return(face,0)==raw.DUMP and not stage.settle_due(),
         "True paid prior return was not consumed exactly once")
    stage.unpowered(REARM)
    need(stage_event(face,0,raw.OPEN)=="captured","Physical rearm not available after old return")
    return dict(old_return_survived_material_cut=True,old_result=raw.DUMP,new_strobe=raw.OPEN)


def captured_sibling(world,a,b,mode):
    l,r=a.l,b.l;k=next(k for k in l.records if k in r.records);role=l.records[k].role
    cap=l.captures[role]
    need(r.captures[role] is cap and cap.payer is l.payer is r.payer and
         b.l.write_gate and world.banks[r.identity.source_bank].cpu.powered,
         "Split shared physical capture or missing genuinely serving sibling")
    r.records[k].value=84;r.records[k].set_ttl(5)
    feeder=MeteredCell(power.catalogue()["capture"],(cap.owner,cap.kind),b.lane.site,200)
    feeder.capture_sink=cap.cell;feeder.corrupt_headers()
    # These are two different local windows, not one read lasting 1000q.
    # A real stage-6 predecessor holds the mode on this last-stage aperture.
    l.line.words[6]=mode;l.line.valid[6]=True
    need(stage_event(a,7,mode)=="captured","Missing authentic last-stage action")
    h=power.STAGE
    start=h-(DELTA/2 if mode==raw.MASK_MODE else 3*DELTA/2)
    a.stage.unpowered(start);feeder.unpowered(start)
    need(feeder.reserve(2048,DELTA,"capture-fill",sink=cap.cell,net=1024),"No funded shared feeder")
    a.stage.unpowered(DELTA/2);feeder.unpowered(DELTA/2)
    if mode==raw.MASK_MODE:
        need(a.stage.application=="applied" and not l.write_gate and r.write_gate and cap.cell.stock==512,
             "MASK canceled the other bank's earlier half-filled capsule")
    need(not feeder.reserve(2048,DELTA,"capture-fill",sink=cap.cell,net=512),"Already funded sink reused")
    a.stage.unpowered(DELTA/2);feeder.unpowered(DELTA/2)
    need(cap.cell.stock==1024 and world.capture(r.identity,role,k)=="captured","Missing true B read")
    claim=cap.pending
    need(claim.destination==(r,k) and cap.cell.debit(512),"Missing fixed, half-spent raw read")
    cap.cell.heat+=512
    a.stage.unpowered(DELTA/2)
    if mode==raw.CLEAR:
        need(a.stage.application=="applied" and not l.write_gate and r.write_gate and
             cap.pending is claim and claim.live and cap.cell.stock==512,"CLEAR disturbed a real sibling read")
    need(cap.cell.debit(512) and claim.dispatch(lambda dest,_:setattr(cap,"snapshot",dest[0].read(dest[1]))),
         "Original live read failed its one-shot")
    cap.cell.heat+=512;cap.pending=None
    need(cap.snapshot==84 and not claim.live and cap.finish(claim)==84,"Old capture replay or sibling data loss")
    return dict(actual_mode=mode,overlap="fill" if mode==raw.MASK_MODE else "read",
                actual_fill_start=start,mode_strobe=h,receiver_result=84,source_CPU_still_serving=True,
                final_work=1024,independent_feeder_work=str(feeder.native_heat))


def dirty_low():
    c=MeteredCell(power.catalogue()["rx"],("representative","rx"),"sink",200)
    need(c.reserve(32,rx.SIGMA,"select"),"No captured old grant")
    c.unpowered(rx.SIGMA/4)
    slot=c.slots["select",0]
    # A local physical discharge changes one retained clock front; the
    # amount actually lost belongs to this boundary's heat, not to a helper.
    v=slot.fronts[1];e=v.energy();v.v=Q(207,2);released=e-v.energy()
    old=c.encumbered
    c.corrupt_headers()
    rem=slot.remaining(c.profile)
    need(rem==Q(7,400)*rx.SIGMA and old==(32+M)*Q(7,400),
         "Fractional physical extent was replaced by corrupt control bits")
    c.unpowered(rem)
    need(not slot.live and c.encumbered==0 and released>0,"Independent timer pressure could not disconnect")

    # Two explicit corrupted-placement cuts only. Old energization is a
    # charged input; a busy flag alone cannot generate it. Even when main W
    # is now depleted, the real charged timer capacitors drain autonomously.
    out=[]
    for voltage in (0,50):
        q=MeteredCell(power.catalogue()["rx"],("old","rx"),"sink",voltage)
        dying=q.slots["divider",0]
        dying.amount=Q(32+M)
        for f in dying.fronts:f.live=True;f.v=Q(799,4)
        q.corrupt_headers(); initial=q.W
        q.low_unpowered(2*q.profile)
        need(not dying.live and q.encumbered==0 and q.W<=initial and q.front_heat>0
             and q.cursor["divider"]==511,"Underpressure manufactured or indefinitely held an old right")
        out.append((voltage,str(q.native_heat),str(q.W)))
    return dict(old_fraction=Q(7,400),charged_front_discharge_heat=released,
                low_pressure_old_strobes=out)


def joined_budgets():
    base=power.budgets();kinds=power.catalogue();rows={}
    extra_current=Q(0);maximum=Q(0);front_count=0;old_front_peak=Q(0)
    worst_rec=Q(0)
    for name,s in kinds.items():
        fronts=2*power.MARKERS[name];load=fronts*HOLD
        extra_current+=s.number*load;front_count+=s.number*fronts
        if s.profile:old_front_peak+=s.number*fronts*300*(200*C/s.profile)
        need(100*s.current-200**2*s.bleed-load>=s.gain
             and s.current-200*s.bleed-load/99>=s.gain/100,
             "Extra controller-front holding erased the old continuing-dose bound")
        # Normal profiles retain exactly the original native budget. Every
        # prior potential slot drops authority within h; full precharge takes
        # at most REARM after the local main working pressure is reestablished.
        req=s.profile
        dirty_fill=s.energy200/(2*s.gain)+(s.energy200-s.floor+s.burst+s.sealed)/(s.gain-s.rate)+s.inlet()["front_time"]
        if req:worst_rec=max(worst_rec,dirty_fill)
        if req:
            need(300*LEAK<200*C/req and Q(1200,1)/(IDLE+300*LEAK)<2**64,
                 "Material front gain or resistor failed")
            maximum=max(maximum,req)
        rows[name]=dict(fronts=fronts,main_ballast_upper=load,old_end=req,
                        rearm_after_full_working_pressure=REARM,retained_gain=s.gain,low_start_all_slots_bound=dirty_fill)
    need(maximum==power.STAGE and maximum+REARM<Q(1,1000),"Local retirement exceeded existing clear interval")
    # Pre-existing physical sampling law, not a wall-clock-driven reset.
    fast=raw.VMAX;delay=raw.CONTROL_DELAY
    formation=max(worst_rec,maximum)+REARM
    startup=rx.gates.record("threshold_initialization_results.json")["bootstrap"]
    need(formation<Q(startup["prepublication_native_slack"]),"Even the separately charged initial old-input margin failed")
    for mode,l,r,work in raw.MODES:
        need((r-l)/fast>delay+work+formation,"Dirty marker rectification consumed the mode corridor")
    need(base["remote_reset_clear_bound"]<Q(1,2) and
         base["rows"]["reset"]["quiet_empty_to_200"]+base["rows"]["reset"]["front_time"]<1000,
         "Remote row lost the preparatory/bitmap budget")
    # Strong earliest reuse per class. Nominal coherent starts during a
    # qualified interval need a free physical slot after h+REARM.
    need(rx.BASE_RANGE[0]>rx.SIGMA+REARM and rx.BASE_RANGE[0]>raw.RECORD_DELAY+REARM
         and Q(1,2**27)>DELTA+REARM and Q(1)/raw.cam.CONTROL_MAX>power.STAGE+REARM
         and raw.WIRE_RATE*(rx.SIGMA+REARM)<1,"A normal callback can catch its own still-unarmed slot")
    # At an already-funded formed shared raw receiver, an old native read
    # settles by 1.01delta, separately from one original fill. A new honest
    # caller cannot overlap the preceding genuine full request at >=8delta.
    need(Q(101,100)*DELTA+2*DELTA < Q(7,2)*DELTA and
         max(rows["capture"]["low_start_all_slots_bound"],DELTA)+REARM+2*DELTA < Q(7,2)*DELTA,
         "Cold feeder/old read can spoil the private comparison margin")
    need(Q(7,2)*DELTA<Q(1,2**27) and 2*DELTA+REARM<Q(1,2**27),
         "The ordinary receiver can revisit a still-occupied previous genuine capture")
    # Explicitly add the revised local figure to the gross work checks;
    # the old rail's confirmed intake cap remains unchanged.
    reaction=4*41*front_count*Q(1,2**48)
    remaining=base["reaction_slack"]-reaction
    additional=8*(extra_current+old_front_peak)+reaction*Q(11,10)
    need(remaining>0 and base["zone_slack"]-4*41*additional>0,
         "Timer hardware exceeds physical loss or reaction envelope")
    need(base["meter_operation_bound"]+8<=M and REARM<=DELTA/8,
         "Two grant poles or true selected-leaf successor exceed paid entry")
    return dict(classes=rows,front_count=front_count,updated_meter_work=base["meter_operation_bound"]+8,
                charged_extra_reaction=reaction,remaining_reaction=remaining,
                remaining_zone_margin=base["zone_slack"]-4*41*additional,per_host_front_work_rate_upper=extra_current,
                extra_installed_capacity=0,new_upstream_rate=0,
                why_no_extra_U="local added holding fits the paid current margin of each existing inlet",
                source_recovery_plus_front_cut=formation,remaining_initial_margin=Q(startup["prepublication_native_slack"])-formation,
                topped_source_earliest_window=Q(1,2**27),full_sweep_remaining=Q(1,2)-base["remote_reset_clear_bound"],
                discharge_time_max=maximum,all_sources_complete=False)





def band_schedule(isa_face):
    """Actual phase/word/bitmap observations for the whole fastest corridor.
    Main-cap fluxes are carried as proven intervals, not fictional exact stocks."""
    f=isa_face;l=f.l;line=l.line
    l.poison(include_shared=False)
    point=power.budgets()
    rho=Q(1,8);h=power.STAGE
    stage=f.stages
    for j,m in enumerate(stage):
        m.corrupt_headers()
        need(m.W>=D(m.s.energy200) and m.s.energy200-m.s.burst-m.s.pending>
             m.s.floor+m.s.sealed+max(v[1]+M for v in power.SLOTS["control"].values()),
             "No strict common-world pressure margin for all ordinary control strobes")
        line.words[j]=15;line.valid[j]=False;line.snapshots[j]=(3,True);line.remaining[j]=Q(17,31)*h
    # A true forced overflow/cold reset controller is already isolated here.
    # Initial and terminal state of each physical control primitive is still
    # executed below. Only the independent analogue W is projected.
    last_use={};stage_work=[Q(0)]*8;apps=[];mode_start=None;last_mode=None
    # Simultaneously attach the selected two raw lanes, their private and
    # shared power terminals, each operating on the feeder's ACTUAL U. Other
    # source ports/inflow are open boundary inputs, held at zero in this
    # narrow no-inflow chart. The general lower-voltage proof admits their
    # actual supplied values. Front current saturates on this entire chart.
    sites=power.catalogue()
    count=dict(rx=2,record=2*len(l.records),control=16,capture=2,reset=2)
    shared_current=sum(number*sites[k].inlet()["limit"] for k,number in count.items())
    U=l.payer;cu=point["U_C"];tr=point["transformer_ratio"];start_U=U.stock
    need(U is l.reset_work.payer and U.stock==cu*(500*tr)**2/2,"Wrong shared starting pressure")
    rail_time=Q(0);u=Q(500);native_clear=[];low_reset=None
    def settle_interval(mode,a,b):
        nonlocal rail_time,u,low_reset
        # Admission current remains the same from the prior cut to b, including
        # the initial front offset. All selected rails have actual fronts <=300.
        dt=b-rail_time
        new=u-shared_current*dt/(cu*tr*tr)
        need(400<new<=u<=500 and U.stock==cu*(u*tr)**2/2 and
             U.debit(dt*shared_current*(new+u)/2) and U.stock==cu*(new*tr)**2/2,
             "Different-source interval or loss of the actual transformer pressure")
        rail_time=b;u=new;elapsed=b-a;rs=l.reset_work
        if mode==raw.CHARGE:rs.qualified_charge(elapsed)
        elif mode==raw.DUMP and rs.energy_bounds is not None:rs.coast_bounds(elapsed)
        elif mode==raw.CLEAR:
            need(rs.energy_bounds is not None,"CLEAR has no physical charged predecessor")
            lo,_=rs.energy_bounds;low_reset=lo-rs.cell.s.floor
            native_clear.append(rs.clear(l,elapsed))
        l.time=b
    def granted(i,role,t):
        m=stage[i];count,price=power.SLOTS["control"][role]
        word=m.cursor[role];need(0<=word<512,"Wide native header")
        j=word if word<count else 0
        stamp=(i,role,j)
        need(stamp not in last_use or t-last_use[stamp]>=h+REARM,
             "Bound physical slot has not yet withdrawn and rearmed")
        last_use[stamp]=t;m.cursor[role]=(j+1)%count;m.headers[role,j]=1
        stage_work[i]+=price+M
    changed=[]
    def install(mode,when):
        nonlocal last_mode,mode_start
        if last_mode==mode:
            # Idempotent only at the stated stage. Real reassertions are
            # still priced and counted; no caller may silently skip their work.
            if mode==raw.MASK_MODE:
                l.reset_control[:]=[0]*raw.ENGINE_BITS;l.clear_phase=Q(0);l.cursor=0;l.setup_paid=False
                for c in l.captures.values():c.set_clock_one()
            return
        if mode_start is not None:
            settle_interval(last_mode,mode_start,when)
            changed.append((last_mode,mode_start,when))
        last_mode=mode;mode_start=when
        l.mode=mode
        if mode in (raw.MASK_MODE,raw.CHARGE,raw.DUMP,raw.CLEAR):
            l.masked=True;l.ingress=l.write_gate=False
        if mode==raw.MASK_MODE:
            l.reset_control[:]=[0]*raw.ENGINE_BITS;l.clear_phase=Q(0);l.cursor=0;l.setup_paid=False
            for c in l.captures.values():c.set_clock_one()
        elif mode==raw.OPEN:l.masked=False;l.ingress=l.write_gate=True

    speed=raw.VMAX
    total_periods=(int(Q(raw.MODES[-1][2])/speed/rho)+1)+10
    for n in range(total_periods):
        t=n*rho;pos=min(Q(raw.MODES[-1][2]),t*speed)
        code=next((c for c,left,right,_ in raw.MODES if left<=pos<right),raw.OPEN)
        for j in range(8):
            granted(j,"copy",t)
            # The old writable snapshot can be overwritten only at this
            # genuine paid slot ingress. No previous live return remains at
            # these period-separated cuts (including the stipulated entry).
            line.snapshots[j]=None;line.remaining[j]=0
            line.capture(j,code)
        for j in range(8):line.remaining[j]=0;word=line.commit(j)
        granted(7,"mode-commit",t+h)
        install(word,t+h)
        apps.append(word)
    end=(total_periods-1)*rho+h
    settle_interval(last_mode,mode_start,end)
    changed.append((last_mode,mode_start,end))
    need(l.certificate() and len(native_clear)==1 and native_clear[0]>0,
         "The sampled control itinerary never produced the real original bitmap/OPEN")
    runs={mode:(a,b) for mode,a,b in changed if mode in (raw.MASK_MODE,raw.CHARGE,raw.DUMP,raw.CLEAR,raw.OPEN)}
    need(set(runs)=={raw.MASK_MODE,raw.CHARGE,raw.DUMP,raw.CLEAR,raw.OPEN} and
         all(runs[mode][1]==runs[mode+1][0] for mode in range(4)),"Missed or reordered physical level")
    charge=runs[raw.CHARGE][1]-runs[raw.CHARGE][0]
    dump=runs[raw.DUMP][1]-runs[raw.DUMP][0]
    clear=runs[raw.CLEAR][1]-runs[raw.CLEAR][0]
    reset=power.catalogue()["reset"]
    need(charge>=1000 and clear>=Q(1,2) and reset.energy200/reset.gain+reset.inlet()["front_time"]<charge,
         "Actual control history omitted its storage/bitmap interval")
    worst_leak=300**2*reset.bleed*(dump+Q(1,2))
    need(raw.RESET_CAP-worst_leak>point["remote_reset_clear_bound"]*raw.CLEAR_RATE,
         "Actual interval leakage can defeat the original literal work")
    return dict(real_periods=total_periods,copies=8*total_periods,actual_mode_applications=len(apps),
                shared_stage_work=sum(stage_work),per_stage_work=stage_work,first_funded_MASK=runs[raw.MASK_MODE][0],
                charge_received_duration=charge,dump_received_duration=dump,clear_received_duration=clear,
                reset_lower_after_wait=raw.RESET_CAP-worst_leak,actual_clear_work=native_clear[0],
                minimum_reset_before_clear=low_reset,shared_U_continuous_outflow=start_U-U.stock,
                raw_rail_ending_drive=u,all_returned_controls_on_one_U=True,
                first_funded_OPEN=runs[raw.OPEN][0],
                ghost_status_not_read_as_permission=True)

def generate():
    with localcontext() as ctx:
        ctx.prec=70
        b,l,w=first_bank()
        m=marker_trace(bind(l[0],w))
        b,l,w=first_bank();f=bind(l[0],w)
        word=control_trace(f)
        sibling=[]
        for mode in (raw.MASK_MODE,raw.CLEAR):
            b,l,w=first_bank();sibling.append(captured_sibling(w,bind(l[1],w),bind(l[0],w),mode))
        b,l,w=first_bank();clear=row_clear(bind(l[0],w))
        b,l,w=first_bank();band=band_schedule(bind(l[1],w))
        b,l,w=first_bank();tie=old_return_at_boundary(bind(l[0],w))
        return rx.gates.normalize(dict(base=BASE,source_hashes={n:rx.wiring.initial.program.digest(HERE/n) for n in
            ("RX-RESTORATION.md","rx_restoration.py","RX-POWER.md","rx_power.py","rx_power_results.json",
             "input_lifecycle.py","cam_reformation.py","rx_product.py","source_clock_wiring.py")},
            retained_miss=dirty_low(),old_return_at_boundary=tie,genuine_control=word,real_row_clear=clear,shared_capture=sibling,
            initiated_marker=m,bill=joined_budgets(),full_band_control=band,full_family_source=False,all_history_H=False))


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__);g=ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--write",action="store_true");g.add_argument("--check",action="store_true")
    a=ap.parse_args();path=HERE/"rx_restoration_results.json"
    text=json.dumps(generate(),sort_keys=True,indent=2)+"\n"
    if a.write:path.write_text(text,encoding="utf-8",newline="\n")
    else:need(path.read_text(encoding="utf-8")==text,"Marker restoration record differs")
    print("PASS passive marker retirement, funded re-entry and sibling-capture preservation; whole source remains open")
