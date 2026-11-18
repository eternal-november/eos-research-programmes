"""Actual physical power placement for the receiving faces of candidate B."""
import argparse
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction as Q
import json
from pathlib import Path

import rx_product as rx

HERE=Path(__file__).resolve().parent
BASE="5e9c5df5ad6f824b88b568422ac4426bd105e24e"
raw=rx.raw
SMALL=Q(1,2**64)
BLEED=Q(1,2**20)
BASE_RATE=1/rx.BASE_RANGE[0]
STAGE=raw.cam.CONTROL_STEP
STAGES=raw.cam.CONTROL_MAX
DELTA=rx.native.DELTA
TICK_RATE=Q(101,100)
METER=512
# One guaranteed finite owner marker for every overlapping native grant in a
# hard clock/flight envelope. Native owner/kind is fixed by the terminal.
# Fixed positional channels. A full or fused slot cannot be retriggered
# until its physical release; none of these tables consults remote U.
SLOTS={
    "rx":{"arrival":(268,8),"divider":(1,32),"select":(1,32),"return":(1,32),
          "pop":(1,64),"decode":(1,11584)},
    "record":{"stage-receipt":(1,512),"queue-tick":(1,32),"start-tick":(2,32),
              "finish-tick":(2,96),"commit-receipt":(2,1536),"start-queued-tick":(2,32)},
    "control":{"copy":(2,2048),"mode-commit":(2,256)},
    "capture":{"capture-fill":(2,2048)},
    "reset":{}
}
MARKERS={"rx":288,"record":12,"control":4,"capture":4,"reset":8}
need=rx.need


@dataclass(frozen=True)
class Terminal:
    name: str
    number: int
    energy200: Q
    gain: Q
    profile: Q
    burst: Q
    rate: Q
    pending: Q
    old_stock: Q=Q(0)

    @property
    def capacitor(self):return self.energy200/20000
    @property
    def floor(self):return self.energy200/4
    @property
    def ceiling(self):return self.energy200*9/4
    @property
    def marker_bits(self):return 32*MARKERS[self.name]
    @property
    def sealed(self):
        return sum(n*(amount+METER) for n,amount in SLOTS[self.name].values())

    @property
    def bleed(self):return BLEED+Q(self.marker_bits,1024*100**2)
    @property
    def current(self):return (self.gain+1+4*Q(self.marker_bits,1024))/100
    @property
    def resistance(self):return Q(99,2)/self.current

    def inlet(self):
        load=300*self.current+1
        j=load/299+1
        head=j+1
        limit=2*j+3
        shift=2*SMALL*head
        # Operative line law on all good voltages; its high-drop foldback is
        # a material source restriction on the surviving two-ended termination.
        need(shift<Q(1,2) and shift+SMALL*limit<1 and limit-head-Q(3,10)>=Q(1,2)
             and head-j-Q(3,10)>=Q(1,2),"No nominal inward raw-voltage region")
        need(2*limit+2-3*limit-Q(3,10)<0 and max(30*limit,1/self.resistance)<=2**64,
             "Upper pressure/current protection or material coefficient fails")
        cold=2*SMALL*(299+shift)
        need(cold<DELTA and self.capacitor>=SMALL and self.capacitor<2**64,
             "Rated capacitor or startup latency fails")
        return dict(raw_load=load,raw_load_current=j,limit=limit,shift=shift,front_time=cold,
                    gross_U=600*limit,hard_hot_crossing=900*limit)

    def facts(self):
        rail=self.inlet()
        largest=max((p+METER for _,p in SLOTS[self.name].values()),default=0)
        need(sum(n for n,_ in SLOTS[self.name].values())<=MARKERS[self.name]
             and self.gain>self.rate and self.energy200-self.floor>self.burst+self.pending+self.sealed+largest,
             "No headroom for the fixed, local, worst-pending pressure gate")
        lower_gain=100*self.current-200**2*self.bleed
        need(lower_gain>=self.gain and self.current-200*self.bleed>=self.gain/100,
             "Receiver capacitor leakage spent twice")
        peak=self.pending/self.profile if self.profile else Q(0)
        need(not self.profile or (peak/99 < 2**31*self.ceiling/300),
             "Native drive cannot fit local current limiter at the working pressure")
        # Before the cold capacitor's first funded action it admits nothing
        # below the voltage floor. Once above it the same load envelope applies.
        dynamic=self.burst+self.pending
        recovery=(self.energy200-self.floor+dynamic)/(self.gain-self.rate)
        healthy_from_empty=self.energy200/(2*self.gain)+recovery+rail["front_time"]
        return dict(count=self.number,hard_storage=self.ceiling,old_reused_storage=self.old_stock,
                    live_floor=self.floor,usable_nominal=self.energy200-self.floor,
                    C=self.capacitor,I=self.current,R=self.resistance,leak_bound=300**2*self.bleed,
                    phase_marker_bits=self.marker_bits,work_per_native_grant=METER,fixed_custody_bound=self.sealed,
                    largest_voltage_gate=self.floor+self.sealed+largest,
                    nominal_gain=self.gain,demand_burst=self.burst,demand_slope=self.rate,
                    active_unspent_upper=self.pending,local_paid_power_peak=peak,
                    cold_empty_to_100=self.energy200/(2*self.gain),quiet_empty_to_200=self.energy200/self.gain,
                    recovery_from_working_floor=recovery,healthy_fill_from_empty_bound=healthy_from_empty,
                    lower_useful_available=self.energy200-dynamic,
                    **rail)


def catalogue():
    # For raw RX, 268 includes up to 264 old flight cells and the next
    # independent four-symbol wire burst. A receipt's 512 work belongs to
    # its own record rather than the parser's private account.
    rxburst=64+11680+268*8+METER*(268+2+3)
    rxrate=Q(11744+5*METER)*BASE_RATE+(8+METER)*1040
    recburst=1568+32+32+512+5*METER
    recrate=Q(1568+2*METER)/raw.RECORD_DELAY+(512+METER)*BASE_RATE+(32+METER)*TICK_RATE
    return {
        "rx":Terminal("rx",160,Q(2**20),Q(2**31),rx.SIGMA,rxburst,rxrate,
                      Q(rxburst)+(8+METER)*1040*rx.SIGMA),
        "record":Terminal("record",320480,Q(2**16),Q(2**26),raw.RECORD_DELAY,recburst,recrate,Q(3712+6*METER)),
        "control":Terminal("control",1280,Q(2**15),Q(2**26),STAGE,Q(4608+4*METER),Q(2304+2*METER)*STAGES,Q(4608+4*METER)),
        # This *feeder* supplies the old, distinct 1,024-work capture capsule
        # at half efficiency. Its actual ready/pending cell remains counted.
        "capture":Terminal("capture",160,Q(2**15),Q(2**46),DELTA,Q(4096+2*METER),Q(2048+METER)*2**27,Q(4096+2*METER)),
        # The old 2^20 usable reset stock is retained as an identified slice
        # [E100,E200]; its physical hard stock includes the unexposed remainder.
        # DUMP/CLEAR have their own debit; recovery uses the actual quiet CHARGE.
        "reset":Terminal("reset",160,Q(4*2**20,3),Q(2**11),0,0,0,0,Q(2**20)),
    }


def phi(voltage,r,limit):
    """Two-terminal signed drop/current law; power is bounded even on a hot fault."""
    d=Q(voltage)
    if not d:return Q(0)
    return (1 if d>0 else -1)*min(abs(d)/r,limit,600*limit/abs(d))


def budgets():
    specs=catalogue(); rows={k:s.facts() for k,s in specs.items()}
    n=sum(x.number for x in specs.values())
    # Both raw front capacitors are charged to the single origin inventory.
    front=n*90000*SMALL
    markers=sum(s.number*MARKERS[s.name] for s in specs.values())
    marker_fronts=2*markers*(300**2)*SMALL/2
    hard=sum(x.number*x.ceiling for x in specs.values())
    new=front+marker_fronts+sum(x.number*(x.ceiling-x.old_stock) for x in specs.values())
    peak=sum(s.number*rows[k]["gross_U"] for k,s in specs.items())
    hot=sum(s.number*rows[k]["hard_hot_crossing"] for k,s in specs.items())
    local_peak=sum(s.number*rows[k]["local_paid_power_peak"] for k,s in specs.items())+160*raw.CLEAR_RATE
    meter_bound=2*9*20+3*9+2*32+32+16
    need(meter_bound<=METER and max(max((n for n,_ in row.values()),default=0)
         for row in SLOTS.values())<=2**9,"New aperture selector exceeds its allocated width or price")
    norm=rx.gates.record("rx_product_results.json")["joined_charge"]
    gate=rx.gates.record("threshold_gate_source_results.json")["costs"]
    Ucap=Q(gate["upstream_capacity"])-new
    Vtop=Q(2**64); CU=2*Ucap/Vtop**2; M=Ucap/4
    spill=Ucap*(1-(1-1/Vtop)**2)
    Umin=Q(norm["minimum_joined_U"])-new-2*peak-spill
    slope=Q(norm["joined_rate"])+peak
    supply=Q(gate["offered_supply"])
    need(SMALL<=CU<=2**64 and Umin>M and slope<supply and 2**96/Vtop<2**64,
         "Actual reservoir voltage floor or total demand failed")
    need(Ucap<=2**96 and Vtop<2**81 and Vtop/600<=2**64,
         "Transformer/store point exceeds selected bounds")
    existing=Q(gate["existing_input_combined_peak"])+Q(gate["additional_native_service_envelope"])
    # A conservative full-price allowance for hard hidden cap discharge and
    # both ends/returns. It requires actual independent surviving outer gates.
    mechanical_power=16*n*Q(1,2**42)*Q(11,10)
    extra=16*(hot+peak+local_peak)+8*2**31*(front+hard+marker_fronts)+mechanical_power
    need(41*(existing+extra)<2**93 and 4*41*(existing+extra)<2**94,
         "New local/remote heat and work exceed the actual enlarged ratings")
    old_reaction=Q(gate["combined_joint_reaction"])
    per_terminal_force=Q(1,2**42)
    extra_reaction=16*41*n*per_terminal_force
    need(old_reaction+extra_reaction<Q(81,250),"Mechanical force/pose clearance over budget")
    reset_price=Q(rx.gates.record("input_lifecycle_results.json")["resources"]["lane_reset_work_upper"])
    need(rows["reset"]["quiet_empty_to_200"]+rows["reset"]["front_time"]<1000 and
         reset_price<2**20 and reset_price/raw.CLEAR_RATE<Q(1,2),"The actual remote reset band is insufficient")
    healthy=max(rows[k]["healthy_fill_from_empty_bound"] for k in ("rx","record","control","capture"))
    need(healthy<Q(5,1000) and rows["capture"]["healthy_fill_from_empty_bound"]<DELTA,
         "Existing prepublication or private read horizon must be rebound")
    lane_bits=specs["rx"].marker_bits+raw.KEYS*specs["record"].marker_bits+8*specs["control"].marker_bits
    serial_extra=2*lane_bits+lane_bits//2+1281
    parallel_prices={k:2*t.marker_bits+t.marker_bits//2+1281 for k,t in specs.items()}
    need(serial_extra+reset_price>raw.RESET_CAP and (serial_extra+reset_price)/raw.CLEAR_RATE>Q(1,2),
         "An old serial reset budget was reused for new marker states")
    need(max(parallel_prices.values())/Q(raw.CLEAR_RATE)<Q(1,32),
         "Provisional independent local reset prices exceed their comparison")
    for k,s in specs.items():
        row=rows[k];I=row["limit"]
        need(0<=phi(2**81,SMALL,I)*2**81<=600*I
             and abs(phi(-2**81,SMALL,I))<=I and phi(300,SMALL,I)==I,
             "Limiter lost nominal voltage or hot-end absorbed power bound")
    return dict(rows=rows,physical_rails=n,new_upper_terminals=16*n,new_buffers_and_fronts=new,
                paid_marker_bits=sum(s.number*s.marker_bits for s in specs.values()),
                local_hard_stock=hard,front_stock=front,one_shot_timer_front_capacity=marker_fronts,gross_added_U_peak=peak,gross_hot_one_end=hot,
                new_slope=slope,old_offer=supply,offered_slack=supply-slope,
                new_U_cap=Ucap,spill_free_loss=spill,minimum_U=Umin,quarter_capacity=M,
                voltage_margin=Umin-M,U_C=CU,U_Vmax=Vtop,transformer_ratio=Vtop/600,
                new_zone_peak_allowance=extra,meter_price=METER,meter_operation_bound=meter_bound,priced_mechanical_port_rating=per_terminal_force,
                joined_reaction=old_reaction+extra_reaction,reaction_slack=Q(81,250)-old_reaction-extra_reaction,
                qualified_nonreset_recovery=healthy,remote_reset_clear_bound=reset_price/raw.CLEAR_RATE,
                added_parasitic_work_upper=mechanical_power,old_serial_plus_new_markers=serial_extra+reset_price,
                conjectured_parallel_marker_prices=parallel_prices,full_marker_reformation=False,
                zone_slack=2**94-4*41*(existing+extra))


def dec(v):
    v=Q(v)
    return Decimal(v.numerator)/Decimal(v.denominator)


class LocalCell:
    """All energy is in the same far-end capacitor: a grant tags an existing share."""
    def __init__(self,kind,owner,site,voltage):
        need(0<=voltage<=300,"Capacitor pressure out of range")
        self.s=kind;self.owner=owner;self.site=site
        self.W=dec(kind.capacitor*Q(voltage)**2/2)
        self.jobs=[]
        self.cursor={name:0 for name in SLOTS[kind.name]}
        self.native_heat=self.leak_heat=self.converter_heat=Decimal(0)
        self.remote_input=Decimal(0)
        self.time=Q(0)

    @property
    def encumbered(self):
        return sum((price*remain for price,remain,_,_,_ in self.jobs),Q(0))

    def reserve(self,cost,horizon,tag,*,sink=None,net=0):
        cost,horizon,net=Q(cost),Q(horizon),Q(net)
        need(0<=net<=cost and ((sink is None)==(net==0)) and
             (sink is None or sink.stock+net<=sink.capacity),"Invalid receiving work conversion")
        need(cost>0 and horizon>0,"A native work share needs a finite positive discharge interval")
        name=tag[0] if isinstance(tag,tuple) else tag
        family=SLOTS[self.s.name]
        need(name in family and family[name][1]==cost,"Not an installed native work face")
        idx=self.cursor[name]
        if type(idx) is not int or not 0<=idx<family[name][0]:return False
        if any(job[2]==(name,idx) or (sink is not None and job[3] is sink) for job in self.jobs):return False
        # Fixed pressure gates. No distributed subtraction of outstanding work:
        # their total is physically bounded by the originally installed slots.
        available=self.W-dec(self.s.floor+self.s.sealed)
        if available<dec(METER):return False
        self.cursor[name]=(idx+1)%family[name][0]
        if available<dec(METER+cost):
            self.jobs.append((Q(METER)/horizon,horizon,(name,idx),None,Q(0)))
            return False
        self.jobs.append(((cost+METER)/horizon,horizon,(name,idx),sink,net/horizon))
        return True

    def unpowered(self,dt):
        """Exact constant-power/ohmic-leak solution up to each genuine job endpoint."""
        dt=Q(dt);need(dt>=0,"Negative physical interval")
        while dt:
            h=min([dt]+[r for _,r,_,_,_ in self.jobs]);dt-=h
            P=sum((price for price,_,_,_,_ in self.jobs),Q(0))
            k=dec(2*self.s.bleed/self.s.capacitor)
            work=dec(P*h); before=self.W
            self.W=(before+dec(P)/k)*(-k*dec(h)).exp()-dec(P)/k
            need(self.W>=0 and (not P or self.W>=dec(self.s.capacitor*99**2/2)),
                 "Split at the real current/low-pressure boundary")
            delivered=Q(0)
            for _,_,_,sink,net_rate in self.jobs:
                if sink is not None:
                    amount=net_rate*h
                    need(sink.stock+amount<=sink.capacity,"Busy capture sink changed its available space")
                    sink.stock+=amount;sink.received+=amount;delivered+=amount
            self.native_heat+=work-dec(delivered);self.leak_heat+=before-self.W-work
            self.jobs=[(price,remaining-h,tag,sink,net_rate) for price,remaining,tag,sink,net_rate in self.jobs
                       if remaining>h]
            self.time+=h

    def charged_idle(self,dt,rail_voltage=299):
        """One exact saturated-current chart, including resistor and holding heat."""
        dt=Q(dt);need(not self.jobs and 299<=rail_voltage<=300 and dt>=0,"Idle rail chart")
        C=dec(self.s.capacitor);I=dec(self.s.current);L=dec(self.s.bleed)
        before=self.W;w0=(2*before/C).sqrt()
        t=dec(dt);w1=I/L+(w0-I/L)*(-L*t/C).exp()
        need(0<=w0<=w1<=dec(rail_voltage-Q(99,2)),"Split at actual end of the saturated-current chart")
        int_w=(I*t-C*(w1-w0))/L
        self.W=C*w1*w1/2
        delivered=dec(rail_voltage)*I*t
        self.converter_heat+=delivered-I*int_w
        self.leak_heat+=I*int_w-(self.W-before)
        self.remote_input+=delivered;self.time+=dt


class ReceiverFaces:
    """Prepaid physical realization for one bound lane and its selected record and last control stage."""
    def __init__(self,face,key,source,voltage=200):
        self.face=face;face.check_layout(all_records=True)
        lane=face.lane
        self.l=lane;self.r=lane.records[key];self.source=source
        need(lane.payer is source and self.r.lane is lane and lane.queue.control is lane.rx,
             "Power belongs to another data lane")
        self.key=key
        i=lane.identity;site=(i.receiver,i.receiver_bank);kinds=catalogue()
        self.lane=LocalCell(kinds["rx"],(i,"rx"),site,voltage)
        self.records={k:LocalCell(kinds["record"],(i,k),site,voltage) for k in lane.records}
        self.record=self.records[key]
        # Each stage can have its own physical housing on this fixed line;
        # stage 7 and mode application must be at the actual receiving end.
        self.stages=[LocalCell(kinds["control"],(i,j),site if j>=4 else (i.origin,i.source_bank),voltage)
                     for j in range(8)]
        self.stage=self.stages[7]

    def receive(self,value):
        self.face.check_layout()
        raw.nat(value,1<<96,"physical symbol")
        if not self.lane.reserve(8,rx.SIGMA,"arrival"):return "unfunded"
        if not self.l.ingress:self.l.drop_count+=1;return "masked"
        return self.l.queue.offer(value)

    def base(self):
        self.face.check_layout()
        l=self.l
        if not l.write_gate:return "divider-inhibited"
        if not self.lane.reserve(32,rx.SIGMA,"divider"):return "divider-unfunded"
        l.rx[rx.DIVIDER]=1-l.rx[rx.DIVIDER]
        if l.rx[rx.DIVIDER]:return "alternate"
        if l.rx[608]:return "busy"
        if not (l.queue.enabled and l.decode_control[1] and not l.servicing and not l.decode_control[0]):return "stopped"
        if not 0<l.queue.number(9,10)<=512:return "empty"
        if not self.lane.reserve(32,rx.SIGMA,"select"):return "unfunded"
        l.queue.set_number(609,9,l.queue.number(0,9));l.rx[608]=1
        return "selected"

    def receive_return(self):
        self.face.check_layout(all_records=bool(self.l.rx[608]))
        l=self.l
        if not l.write_gate or not l.rx[608] or not self.lane.reserve(32,rx.SIGMA,"return"):return None
        head=l.queue.number(609,9);l.rx[608]=0
        if head!=l.queue.number(0,9) or not 0<l.queue.number(9,10)<=512:return "changed-or-empty-head/drop"
        if l.servicing or l.rx[20]:return "busy"
        if not l.decode_control[1] or l.decode_control[0]:return "stopped"
        if not self.lane.reserve(64,rx.SIGMA,"pop"):return "unfunded"
        value=l.queue.pop()
        if value is None:return "empty"
        l.servicing=True
        try:
            key=(value>>64)&2047;part=(value>>75)&3;kind=(value>>77)&3
            phase=l.parser_number(21,3);prior=l.parser_number(24,11)
            if value>>79 or kind!=1:l.parser_set(21,3,0);return "malformed"
            chunk=value&((1<<64)-1)
            if part==0:
                l.frame_words[0]=chunk;l.parser_set(24,11,key);l.parser_set(21,3,1);return "start"
            if phase!=part or prior!=key:l.parser_set(21,3,0);return "bad-order"
            l.frame_words[part]=chunk
            if part!=3:l.parser_set(21,3,part+1);return "partial"
            l.parser_set(21,3,0)
            if not self.lane.reserve(11584,rx.SIGMA,"decode"):return "unfunded"
            payload=sum(v<<(64*j) for j,v in enumerate(l.frame_words))
            token=l.frame_claim=raw.Claim((l.identity,key),payload)
            dest=l.decoder.decode(key)
            def stage(_owner,value):
                if dest is not None:
                    role,k=dest
                    need(l.records[k].source_key==key and l.records[k].role==role and l.records[k].lane is l,
                         "Decoder did not bind its installed receiving record")
                    self.receipt(value,k)
            token.dispatch(stage)
            return "frame" if dest is not None else "uninstalled"
        finally:l.servicing=False

    def receipt(self,value,key=None):
        k=self.key if key is None else key
        self.face.check_layout(k)
        r=self.l.records[k];cell=self.records[k];raw.nat(value,1<<256,"receipt")
        if not self.l.ingress:return "masked"
        if r.control[r.RECEIPT_VALID]:return "full"
        if not cell.reserve(512,raw.RECORD_DELAY,"stage-receipt"):return "unfunded"
        r.staged=value;r.control[r.RECEIPT_VALID]=1
        return "staged"

    def tick(self,key=None):
        k=self.key if key is None else key
        self.face.check_layout(k)
        r=self.l.records[k];cell=self.records[k]
        if not self.l.write_gate or not r.control[r.ENABLE]:return "stopped"
        if r.control[r.RECEIPT_VALID] or r.control[r.BUSY]:
            if not r.queued_tick and cell.reserve(32,raw.RECORD_DELAY,"queue-tick"):r.queued_tick=True
            return "queued" if r.queued_tick else "unfunded"
        if not cell.reserve(32,raw.RECORD_DELAY,"start-tick"):return "unfunded"
        r.control[r.BUSY]=r.control[r.TICK_VALID]=1;r.claim=raw.Claim(r,max(r.ttl-1,0));return "started"

    def service(self,key=None):
        k=self.key if key is None else key
        self.face.check_layout(k)
        r=self.l.records[k];cell=self.records[k]
        if not self.l.write_gate or not r.control[r.ENABLE]:return "stopped"
        if r.control[r.BUSY]:
            if r.claim is None or not r.claim.live or not r.control[r.TICK_VALID]:return "stale-busy"
            need(r.claim.destination is r and type(r.claim.payload) is int and 0<=r.claim.payload<=r.cap,
                 "Decrement cannot write a different physical counter")
            if not cell.reserve(raw.TICK_WORK-32,raw.RECORD_DELAY,"finish-tick"):return "unfunded"
            r.claim.dispatch(lambda bound,word:bound.set_ttl(word))
            r.claim=None;r.control[r.BUSY]=r.control[r.TICK_VALID]=0;return "tick"
        if r.control[r.RECEIPT_VALID]:
            if not cell.reserve(1536,raw.RECORD_DELAY,"commit-receipt"):return "unfunded"
            r.value=r.staged;r.set_ttl(r.lifetime);r.control[r.RECEIPT_VALID]=0;return "receipt"
        if r.queued_tick:
            if not cell.reserve(32,raw.RECORD_DELAY,"start-queued-tick"):return "unfunded"
            r.queued_tick=False
            r.control[r.BUSY]=r.control[r.TICK_VALID]=1;r.claim=raw.Claim(r,max(r.ttl-1,0));return "started"
        return "idle"

    def capture_control(self,which,code):
        if type(which) is not int or not 0<=which<8:return "uninstalled"
        line=self.l.line
        if line.snapshots[which] is not None:return "busy"
        if not self.stages[which].reserve(raw.cam.STAGE_PRICE,STAGE,("copy",which)):return "unfunded"
        return line.capture(which,code)

    def apply_control(self,mode):
        l=self.l;raw.nat(mode,16,"control mode")
        if not self.stage.reserve(256,STAGE,"mode-commit"):return "control-unfunded"
        if mode!=l.mode or not l.mode_trace:l.mode_trace.append((mode,l.time))
        l.mode=mode;l.mode_applications+=1
        if mode in (raw.MASK_MODE,raw.CHARGE,raw.DUMP,raw.CLEAR):
            l.masked=True;l.ingress=False;l.write_gate=False
        if mode==raw.MASK_MODE:
            l.reset_control[:]=[0]*raw.ENGINE_BITS;l.cursor=0;l.setup_paid=False;l.clear_phase=Q(0)
            for capture in l.captures.values():capture.set_clock_one()
        elif mode==raw.OPEN:l.masked=False;l.ingress=True;l.write_gate=True
        return "applied"


def held_rail(cell,U,point,dt):
    """Saturated source current, both front capacitor voltages stationary, real U falling."""
    dt=Q(dt)
    s=cell.s; I=s.current;lim=s.inlet()["limit"]; r=SMALL; K=30*lim
    A=K+Q(1,1000); B=K*Q(2999,10); housekeeping=Q(1,300)
    vr=(lim-(1+A*r)*(I+housekeeping-B)+B)/(A*(2+A*r))
    current=I+housekeeping+A*vr-B
    vs=vr+r*current
    need(Q(2999,10)<=vr<=vs<=300 and 0<current<lim
         and phi(vs-vr,r,lim)==current,"Wrong stationary raw receiving branch")
    ratio=point["transformer_ratio"];cu=point["U_C"]
    u0=Q(500);v0=u0*ratio
    need(U.capacity==point["new_U_cap"] and U.stock==cu*v0*v0/2,
         "The actual source stock does not realize this voltage chart")
    u1=u0-lim*dt/(ratio*ratio*cu)
    need(300<=u1<=u0<600 and phi(u0-vs,r,lim)==phi(u1-vs,r,lim)==lim,
         "Split at the actual source-limiter pole")
    old=U.stock;debit=lim*(u0+u1)*dt/2
    need(U.debit(debit) and U.stock==cu*(u1*ratio)**2/2,"Unmatched finite-time U outflow")
    source_heat=((u0+u1)/2-vs)*lim*dt
    link_heat=(vs-vr)*current*dt
    local_front=(vs*(lim-current)+vr*(current-I-housekeeping)+vr*housekeeping)*dt
    need(source_heat>=0 and link_heat>=0 and local_front>=0 and
         debit==source_heat+link_heat+local_front+vr*I*dt,"Rail work/heat did not balance at both ends")
    w0=cell.W;cell.charged_idle(dt,vr)
    need(U.stock<old and cell.W>w0,"No actual cross-zone transfer over this positive interval")
    return dict(v_source_front=vs,v_receiver_front=vr,source_drive_initial=u0,source_drive_final=u1,
                upstream_debit=debit,source_resistor_heat=source_heat,line_resistor_heat=link_heat,
                shunt_bleed_and_standby=local_front,far_end_input=vr*I*dt,duration=dt)


def specialized_ports(faces,point):
    l=faces.l;src=faces.source
    cap=l.captures[faces.r.role]
    need(cap.payer is src and cap.cell.stock==0 and cap.pending is None,"Need the existing idle empty capture")
    feeder=LocalCell(catalogue()["capture"],(cap.owner,cap.kind),faces.lane.site,200)
    old=src.stock
    need(feeder.reserve(2048,DELTA,"capture-fill",sink=cap.cell,net=1024),"Missing physical capture feeder")
    feeder.unpowered(DELTA/2);need(cap.cell.stock==512,"A partial refill already made the capture ready")
    feeder.unpowered(DELTA/2)
    need(cap.cell.stock==1024 and feeder.native_heat==1024+METER and src.stock==old,
         "Capture filled twice or took a remote impulse")
    # Original bind on its own full cell. Zero requested refill carries zero work.
    need(cap.begin(l,faces.key)=="captured","Funded actual capture did not bind fixed owner")
    claim=cap.pending
    need(claim.destination==(l,faces.key) and claim.live,"Wrong captured body")
    # Uniform 1024/delta native work on this particular already bound read.
    # Half time does not publish a result. The same one-shot commits at its own final strobe.
    before=cap.snapshot
    for j in range(2):
        need(cap.cell.debit(512),"Previously funded raw read lost its physical energy")
        cap.cell.heat+=512
        if j==0:need(cap.snapshot==before and claim.live,"A half spent read published")
    claim.dispatch(lambda bound,_:setattr(cap,"snapshot",bound[0].read(bound[1])))
    cap.pending=None
    need(cap.snapshot==l.read(faces.key) and not claim.live and src.stock==old,"Old captured read was rebound")

    reset=LocalCell(catalogue()["reset"],(l.identity,"reset"),faces.lane.site,0)
    U=raw.SourceWork(src.origin,point["new_U_cap"],point["new_U_cap"]*Q(25,36))
    # Zero other loads is a scoped physical chart. Every joule below crosses a
    # true finite-power U transformer/series-line path over this interval.
    duration=reset.s.energy200/reset.s.gain
    rail=held_rail(reset,U,point,duration)
    usable=min(dec(raw.RESET_CAP),reset.W-dec(reset.s.floor))
    need(usable==dec(raw.RESET_CAP) and duration+reset.s.inlet()["front_time"]<raw.RESET_REFILL,
         "Reset reserve did not physically refill inside its real inhibited CHARGE band")
    return dict(capture_preexisting_capacity=cap.cell.capacity,half_credit=512,completed_local_credit=1024,
                capture_work_heat=1024,converter_heat=1024,meter_heat=METER,shared_capture_result=cap.snapshot,
                empty_source_no_draw=src.stock==old,reset_positive_duration=rail["duration"],
                reset_usable_at_endpoint=int(usable),reset_real_upstream_debit=rail["upstream_debit"])


def reference_record(lane,key,rawkey,value):
    u=raw.SourceWork(lane.payer.origin,lane.payer.capacity,Q(2**30))
    l=raw.RawLane(lane.population,lane.identity,u)
    d=raw.RECORD_DELAY
    final=13*rx.BASE_PERIOD+rx.SIGMA
    ph=rx.phases([l])[l.identity]
    rc=dict(ph.records);rc[key]=(Q(5001,5000),final)
    clock=rx.Receiver(l,rx.LanePhases(ph.base,ph.prior_return,rc,{}))
    clock.act(("base",None))
    clock.now=rx.SIGMA;clock.act(("return",None))
    syms=raw.symbols(rawkey,value)
    for j in range(1,14):
        clock.now=j*rx.BASE_PERIOD
        if (j-1)%4==0:need(l.receive_symbol(syms[(j-1)//4])=="accepted","Reference offer missing")
        clock.act(("base",None));clock.now+=rx.SIGMA;clock.act(("return",None))
    clock.act(("tick",key));clock.now+=d
    need(clock.act(("commit",key))=="receipt" and clock.act(("commit",key))=="started",
         "Reference did not settle the same staged/queued order")
    clock.now+=d;need(clock.act(("commit",key))=="tick","Reference old tick did not complete")
    return (l.records[key].value,l.records[key].ttl)


def witnesses(isa,image):
    banks,lanes=rx.fixtures(isa,image,additional=False)
    gate,lane=banks[0],lanes[0];U=gate.fixture.source_work
    prod=rx.OriginProduct(banks,rx.source_phases(banks),rx.phases(lanes))
    key=next(iter(lane.records));f=ReceiverFaces(prod.receivers[lane.identity],key,U)
    W=f.lane.W;initial_U=U.stock
    # This old source would debit a remote 32 at the exact base time.
    front=SMALL*300**2/2
    need(front<32 and 2**94*Q(1,2**94)==1<32,"No impulse separation")
    need(f.base()=="alternate" and U.stock==initial_U and f.lane.W==W
         and f.lane.encumbered==32+METER and f.lane.native_heat==0,"A local tag moved inter-zone energy")
    f.lane.unpowered(rx.SIGMA)
    need(f.lane.native_heat==32+METER and f.lane.encumbered==0 and f.lane.W<W,"No physical heat in the local interval")
    # Separate scarce cut with precharged actual receiver energy. Do not
    # introduce a fictitious impulse draining the preceding example's U.
    U=raw.SourceWork(U.origin,U.capacity,0)
    lane=raw.RawLane(lane.population,lane.identity,U)
    face=rx.Receiver(lane,rx.phases([lane])[lane.identity])
    f=ReceiverFaces(face,key,U)
    need(f.base()=="alternate","Independent local aperture failed at depleted origin")
    rawkey=f.r.source_key;value=88
    def at(t):
        # The selected record, lane and final stage are the active projections
        # in this zero-inflow local witness. The other raw stocks have no events.
        for cell in (f.lane,f.record,f.stage):cell.unpowered(t-cell.time)
    syms=raw.symbols(rawkey,value)
    for j in range(1,14):
        when=j*rx.BASE_PERIOD
        at(when)
        if (j-1)%4==0:
            need(f.receive(syms[(j-1)//4])=="accepted","Funded physical symbol refused")
        response=f.base()
        need(response==("selected" if (j-1)%4==0 else "alternate" if j%2==0 else "empty"),
             "Independent receiving parity/head failed")
        at(when+rx.SIGMA)
        outcome=f.receive_return()
    need(outcome=="frame" and f.r.control[f.r.RECEIPT_VALID] and U.stock==0,"Word did not enter the real decoder")
    t=13*rx.BASE_PERIOD+rx.SIGMA
    old_observation=reference_record(lane,key,rawkey,value)
    need(f.tick()=="queued","Older received work lost its relative order")
    at(t+raw.RECORD_DELAY)
    need(f.service()=="receipt" and f.service()=="started","New tick failed to capture the committed receipt")
    at(t+2*raw.RECORD_DELAY)
    need(f.service()=="tick" and (f.r.value,f.r.ttl)==old_observation==(value,f.r.lifetime-1),"Bound countdown failed")
    # The final stage samples its physical preceding wire on a genuine independent
    # aperture. All earlier nonconsumed prior pipeline phases are outside this cut.
    lane.line.words[6]=raw.MASK_MODE;lane.line.valid[6]=True
    need(f.capture_control(7,raw.MASK_MODE) is not False and lane.line.snapshots[7] is not None,"No funded mode")
    rem=lane.line.remaining[7]
    at(t+2*raw.RECORD_DELAY+rem)
    lane.line.remaining[7]-=rem
    old=lane.line.commit(7)
    need(old==raw.MASK_MODE and f.apply_control(old)=="applied" and not lane.write_gate,
         "Local funded control copy or sink lost its real effect")
    at(t+2*raw.RECORD_DELAY+rem+STAGE)
    need(f.tick()=="stopped" and f.base()=="divider-inhibited","Mask did not inhibit ordinary paths")
    # Poor prospective point; standing charge, fixed eligibility and event timing differ.
    poor=LocalCell(f.lane.s,f.lane.owner,f.lane.site,100)
    need(not poor.reserve(32,rx.SIGMA,"divider") and not poor.jobs and poor.native_heat==0,
         "An empty usable floor paid a strobe")
    empty=LocalCell(f.lane.s,f.lane.owner,f.lane.site,0)
    empty.unpowered(1)
    need(empty.W==0 and empty.leak_heat==0 and not empty.reserve(8,rx.SIGMA,"arrival"),"Empty standby draws phantom energy")
    # Below the functional price but above the metering threshold, the refused
    # probe consumes its local metering price; the requested 512 never gets a grant.
    failed=LocalCell(f.record.s,f.record.owner,f.record.site,100)
    failed.W+=dec(failed.s.sealed+METER+8)
    before=failed.W
    invalid=LocalCell(f.lane.s,f.lane.owner,f.lane.site,200)
    invalid.cursor["divider"]=511
    need(not invalid.reserve(32,rx.SIGMA,"divider") and not invalid.jobs and
         f.capture_control(-1,raw.OPEN)=="uninstalled","Uninstalled selector acquired funded work")
    need(not failed.reserve(512,raw.RECORD_DELAY,"stage-receipt") and failed.encumbered==METER
         and failed.W==before,"A paid negative aperture got a functional claim")
    failed.unpowered(raw.RECORD_DELAY)
    need(failed.native_heat==METER and U.stock==0,"A failed probe was paid at the wrong place")
    point=budgets()
    e=raw.SourceWork(U.origin,point["new_U_cap"],point["new_U_cap"]*Q(25,36))
    start=poor.W
    rail=held_rail(poor,e,point,rx.SIGMA/4)
    need(poor.W>start and poor.remote_input>0 and poor.converter_heat>0 and poor.leak_heat>=0
         and abs((poor.W-start)+poor.converter_heat+poor.leak_heat-poor.remote_input)<Decimal("1e-36"),
         "Heterogeneous work path did not balance")
    return dict(functional_divider=32,metering_work=METER,tagged_at_strobe=32+METER,interzone_jump=0,far_end_native_heat_after_profile=32+METER,
        cold_source_after_precharge=0,new_data_value=f.r.value,new_countdown=f.r.ttl,
        funded_original_record_at_same_cuts=old_observation,
        fixed_receiver_site=f.lane.site,captured_stage=old,empty_floor_no_grant=True,empty_passive_heat=0,
        failed_probe_local_work=METER,no_functional_claim_on_refusal=True,
        correct_tag_underfunding_no_source_debit=True,nonstoring_local_profile=True,
        positive_two_ended_subarc=rail,specialized_ports=specialized_ports(f,point),
        rail_current_example_input=str(+poor.remote_input),rail_current_example_new_stock=str(+poor.W))


def generate():
    isa,img,_=rx.wiring.retirement.source_inputs()
    with localcontext() as context:
        context.prec=70
        manifest={n:rx.wiring.initial.program.digest(HERE/n) for n in
            ("RX-POWER.md","rx_power.py","rx_product.py","rx_product_results.json","input_lifecycle.py",
             "cam_reformation.py","threshold_gate_source_results.json","../local-control/RECEIVER-POWER.md",
             "../local-control/receiver_power_model.py","../local-control/PORT-SOURCE.md")}
        return rx.gates.normalize(dict(base=BASE,source_manifest=manifest,budget=budgets(),examples=witnesses(isa,img),
            remote_point_debit_realized_as_interzone_work=False,all_modes_realized=False,whole_source_admission=False))


if __name__=="__main__":
    opts=argparse.ArgumentParser(description=__doc__);group=opts.add_mutually_exclusive_group(required=True)
    group.add_argument("--write",action="store_true");group.add_argument("--check",action="store_true")
    args=opts.parse_args();path=HERE/"rx_power_results.json"
    out=json.dumps(generate(),sort_keys=True,indent=2)+"\n"
    if args.write:path.write_text(out,encoding="utf-8",newline="\n")
    else:need(path.read_text(encoding="utf-8")==out,"RX rail result differs")
    print("PASS conditioned far-end rail/store/heat and native effects; physical global admission remains open")
