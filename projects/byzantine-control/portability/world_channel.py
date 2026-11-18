"""Paid local WORLD mailbox, fixed sampler and retained tracker for the B program."""
import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path

import a_prime_source_assembly as assembly
import native_clock_source as paced
import return_seat as seat
import private_comparison as compare

HERE=Path(__file__).resolve().parent
raw, charging, parent, program = seat.raw, seat.charging, seat.parent, seat.program
need=seat.checks
D=parent.DELTA
SIGMA=Q(1,4096)
PERIOD=Q(1,64)
FAST=Q(100,101)*PERIOD
SLOTS=128
ROUTES=41
WORLD=ROUTES-1
PRICE=4096


def clamp(v):
    return min(100,max(-100,v))


def encode(args):
    need(len(args)==2 and all(type(v) is int for v in args),"Invalid WORLD parent arguments")
    return sum((clamp(v)%(1<<64)) << (64*j) for j,v in enumerate(args))


def decode(word):
    need(type(word) is int and 0<=word<1<<128,"Outside fixed WORLD mailbox")
    values=[]
    for j in range(2):
        x=(word>>(64*j))% (1<<64)
        values.append(clamp(x if x<1<<63 else x-(1<<64)))
    return tuple(values)


class WorkBank(charging.JointCharge):
    """One physical E for CPU, ADC/DATA and the forty-one fixed output rows."""

    def __init__(self,cpu,source):
        self.source=source
        self.cells=tuple(raw.Work(PRICE) for _ in range(ROUTES*SLOTS))
        self.blocked=set()
        self.dirty=set(range(len(self.cells)))
        self.route_received=Q(0)
        super().__init__(cpu.bank,cpu,(*source.slots,source.adc),D)
        self.world_gate=lambda:True
        self.native_total=Q(0)

    def routes(self):
        if not self.world_gate():
            return []
        return sorted(self.dirty-self.blocked)

    def charging_faces(self,source_powered):
        p=self.parent
        refs=[]
        if p.powered and not p.recharge_inhibit and p.pending is None and p.fabric.token is None and not p.cell.busy:
            if p.cell.stock<p.cell.capacity:
                refs.append(("cpu",0,p.cell,p.cell.capacity/(2*D)))
        if source_powered:
            for s in self.source.recharge_needed:
                if not (s.claim is not None and s.claim.live) and s.cell.stock<s.cell.capacity:
                    refs.append(("native",s.native_index,s.cell,s.cell.capacity/D))
        refs.extend(("route",j,self.cells[j],PRICE/D) for j in self.routes())
        return refs

    def transfer(self,refs,exposure):
        result=charging.closed_segment(self.bank.stock,[c.capacity-c.stock for _,_,c,_ in refs],
                                      [r for *_,r in refs],exposure)
        self.bank.stock=result.retained
        for (kind,j,cell,_),q in zip(refs,result.credits):
            cell.stock+=q
            if kind=="cpu":
                self.bank.supplied+=q
            else:
                cell.received+=q
                if kind=="native":
                    self.input_received[j]+=q
                    self.native_total+=q
                    if cell.stock==cell.capacity:
                        self.source.recharge_needed.discard(self.slots[j])
                else:
                    self.route_received+=q
                    if cell.stock==cell.capacity:
                        self.dirty.discard(j)
        self.balance()
        return result.clock

    def apply_exposure(self,exposure,*,source_powered):
        return self.transfer(self.charging_faces(source_powered),exposure)

    def flow_full_delivery(self,duration,*,source_powered):
        refs=self.charging_faces(source_powered)
        gross=sum(min(c.capacity-c.stock,r*duration) for _,_,c,r in refs)
        need(not gross or self.bank.stock-gross>=1,"Use the depleted common-work chart")
        return self.transfer(refs,duration)

    def balance(self):
        n=self.bank.supplied-self.initial_parent_supplied
        need(self.bank.stock+n+self.native_total+self.route_received==self.initial_bank,
             "Duplicate E stock or source-fee attribution")
        p=self.parent
        need(p.cell.stock+p.cell.spent+p.cell.dumped==n,"CPU energy lost across a WORLD capture")
        p.fabric.link_balance()
    def audit(self):
        self.balance()
        need(self.native_total==sum(self.input_received) and all(
             s.cell.stock+s.cell.spent==self.slot_initial[i]+self.input_received[i]
             and (s.cell.stock==s.cell.capacity or s in self.source.recharge_needed or (s.claim is not None and s.claim.live))
             for i,s in enumerate(self.slots)), "Native stock/charge mismatch")
        need(sum(c.stock+c.spent for c in self.cells)==self.route_received,"Unbound port charge")


@dataclass(frozen=True)
class Packet:
    # sent is proof data. The receiving level never sorts by this time.
    slot:int
    owner:tuple
    word:int
    sent:Q
    written:object  # analytic owner of the captured word, not a wire timestamp
    arrives:Q
    applies:Q


class WorldRoute:
    def __init__(self,bus,working,initial,first=PERIOD):
        self.bus,self.working=bus,working
        self.owner=(*bus.bank.owner,"WORLD")
        self.now=Q(0)
        self.mail=self.level=encode(initial)
        self.age_stamp=None
        self.mail_written=self.level_written=None
        self.next_sample=Q(first)
        self.cursor=0
        self.live={}
        self.calendar={}
        self.tx_heat=self.rx_heat=self.in_line=Q(0)
        self.commits=[]
        self.samples=0
        self.qualification_work=Q(0)
        self.receiver_enabled=True

    def store(self,args,cpu):
        need(cpu is self.bus.parent and cpu.pending is not None and cpu.io_paid
             and cpu.committing and cpu._io_info()[0]=="world"
             and cpu.fabric.token is not None and cpu.fabric.token.issued and cpu.io_args is args,
             "No funded ordinary WORLD write at this cartridge")
        self.mail=encode(args)
        self.mail_written=self.now
        return 0

    def sample(self,*,flight,decode_time,next_period):
        need(self.now==self.next_sample and FAST<=next_period<=PERIOD,"No local clock edge")
        need(2*SIGMA<=flight<=Q(1,2) and SIGMA<=decode_time<=Q(1,2),"Unrated finite signal delay")
        self.next_sample+=next_period
        payer=self.bus.source.payer
        paid=min(64,payer.stock)
        need(payer.debit(paid),"Unmatched co-located sampler qualification")
        self.qualification_work+=paid
        if paid<64:
            return "refused"
        if not self.working():
            return "unpowered"
        pos=self.cursor
        need(type(pos) is int and 0<=pos<SLOTS,"Outside the physical seven-bit cursor")
        self.cursor=(pos+1)%SLOTS
        j=WORLD*SLOTS+pos
        cell=self.bus.cells[j]
        if j in self.bus.blocked or cell.stock<PRICE:
            return "busy-or-unfunded"
        p=Packet(j,self.owner,self.mail,self.now,self.mail_written,self.now+flight,self.now+flight+decode_time)
        self.live[j]=p
        self.samples+=1
        self.bus.blocked.add(j)
        self.bus.dirty.add(j)
        # 3072 for source capture/encoding and 1024 carried by the real issued
        # pulse. The fixed destination receives and consumes those 1024 over
        # the last SIGMA of its decoder interval.
        for t,kind in ((p.sent+SIGMA,"sent"),(p.arrives,"header"),(p.applies-SIGMA,"decoder"),(p.applies,"apply")):
            self.calendar.setdefault(t,[]).append((j,kind))
        return "issued"

    @staticmethod
    def overlap(a,b,start):
        return max(Q(0),min(b,start+SIGMA)-max(a,start))

    def flow_to(self,end):
        end=Q(end)
        need(self.now<=end<=min([self.next_sample,*self.calendar]),"Skipped an actual WORLD strobe")
        for j,p in self.live.items():
            issue=self.overlap(self.now,end,p.sent)/SIGMA
            final=self.overlap(self.now,end,p.applies-SIGMA)/SIGMA
            if issue:
                need(self.bus.cells[j].debit(PRICE*issue),"A captured pulse lost its paid work")
            self.tx_heat+=3072*issue
            self.rx_heat+=1024*final
            self.in_line+=1024*(issue-final)
        self.now=end

    def dispatch(self,event):
        j,kind=event
        bucket=self.calendar[self.now]
        need(event in bucket and j in self.live,"Missing paid event")
        p=self.live[j]
        if kind=="apply":
            need(p.owner==self.owner and p.applies==self.now,"Changed physical WORLD destination")
            if self.receiver_enabled:
                self.level,self.age_stamp,self.level_written=p.word,p.sent,p.written
                self.commits.append((self.now,p.sent,p.word))
            self.bus.blocked.remove(j)
            del self.live[j]
        bucket.remove(event)
        if not bucket:
            del self.calendar[self.now]

    def balance(self):
        expended=sum(c.spent for c in self.bus.cells[WORLD*SLOTS:])
        need(expended==self.tx_heat+self.rx_heat+self.in_line and self.in_line>=0,
             "WORLD carrier work was dropped or dissipated twice")


class WorldPorts:
    def __init__(self,native,route):
        self.native,self.route=native,route
        self.source=native.source

    def perform(self,name,args,cpu):
        if name=="world":
            return self.route.store(args,cpu)
        need(name in paced.OrdinaryCycle.IO,"Missing actual port")
        return self.native.perform(name,args,cpu)

    def advance(self,cpu):
        self.native.advance(cpu)


class WorldCycle(paced.OrdinaryCycle):
    IO=paced.OrdinaryCycle.IO | {"world","cpu_count"}


class PairedClock:
    def __init__(self,native,route,periods):
        need(native.bus is route.bus and native.source is route.bus.source,"Different bank dispatchers")
        self.native,self.route,self.periods=native,route,periods
        self.count=0

    def next(self):
        return min(self.native.next_boundary(),self.route.next_sample,*self.route.calendar)

    def to(self,t):
        while self.native.now<t:
            stop=min(t,self.next())
            self.native.advance_to(stop)
            self.route.flow_to(stop)
            if stop<t:
                self.settle()

    def settle(self,*,reverse=False):
        while self.native.due():
            self.native.edge(self.native.due()[0])
        route=self.route
        if route.now in route.calendar:
            # Different live slot completions can use either physical order.
            for event in sorted(route.calendar[route.now][:],reverse=reverse):
                route.dispatch(event)
        if route.next_sample==route.now:
            self.count+=1
            flight,dec,period=self.periods(self.count)
            route.sample(flight=flight,decode_time=dec,next_period=period)

def plus(*exprs):
    return assembly.ThermalZone.plus(*exprs)


def times(a,b):
    out={}
    for k,v in a.items():
        for j,w in b.items():
            out[k+j]=out.get(k+j,0)+v*w
    return {k:v for k,v in out.items() if v}


def scalar(x):
    return {} if not x else {Q(0):Q(x)}


class Tracker:
    """Exact sums of rational multiples of exponentials along a constant-effort subarc."""
    def __init__(self,initial):
        self.y=scalar(initial)
        self.resistor_heat={}
        self.dac_work={}
        self.quantity={}
        self.world_work={}

    def advance(self,dt,command,resistance,weight,effort):
        dt,command,resistance,weight,effort=map(Q,(dt,command,resistance,weight,effort))
        need(dt>=0 and -1<=command<=1 and Q(1,2)<=resistance<=1 and 0<=weight<=1 and abs(effort)<=1,
             "Outside the powered tracker chart")
        g=1/(100*resistance)
        error=plus((self.y,1),(scalar(command),-1))
        final=plus((scalar(command),1),({k-g*dt:v for k,v in error.items()},1))
        # C*y'=I, p_DAC=c I, heat=R I². Integrate independently.
        port=plus((final,100*command),(self.y,-100*command))
        square=times(error,error)
        heat=plus((square,50),({k-2*g*dt:v for k,v in square.items()},-50))
        stored=plus((times(final,final),50),(times(self.y,self.y),-50))
        need(not plus((stored,1),(heat,1),(port,-1)),"WORLD RC energy imbalance")
        delivered=plus((scalar(command*dt),weight),(self.y,weight/g),(final,-weight/g))
        self.resistor_heat=plus((self.resistor_heat,1),(heat,1))
        self.dac_work=plus((self.dac_work,1),(port,1))
        self.quantity=plus((self.quantity,1),(delivered,1))
        self.world_work=plus((self.world_work,1),(delivered,effort))
        self.y=final


def route_trial(isa,image):
    owner=(0,0)
    cap=int(Q(json.loads((HERE/"parent_realization_results.json").read_text())["cost_bounds"]["actual_bank_capacity"]))
    e=charging.OperatingBank(owner,cap,Q(cap)-1000)
    cpu=compare.ComparedParent(isa,image,bank=e)
    ucap=Q(json.loads((HERE/"image_transport_results.json").read_text())["joined_point"]["upstream_capacity"])
    ucap-=2*SLOTS*1024
    u=raw.SourceWork(owner[0],ucap,ucap)
    source=paced.TimedSource(e,u)
    need(source.reform()=="formed-unpowered" and source.begin_entry(e)
         and source.entry_flow(Q(source.ENTRY_WORK,raw.CLEAR_RATE)), "Local source entry")
    bus=WorkBank(cpu,source)
    enabled=lambda: source.powered and cpu.powered and not cpu.recharge_inhibit
    bus.world_gate=enabled
    clock=paced.NativeClock(cpu,source,external_receivers=True,existing_bus=bus,
                            adc_first=8*D,tx_first=13*D)
    first=8*D
    route=WorldRoute(bus,enabled,(60,60),first)
    # An old snapshot can reach the level after a later source record.
    def clock_values(j):
        if j==1:
            return (Q(1,2),Q(1,2),PERIOD)
        return (2*SIGMA,SIGMA,PERIOD)
    common=PairedClock(clock,route,clock_values)
    ports=WorldPorts(paced.timed_ports(isa)(image,source),route)
    pc=next(i for i,word in enumerate(image.image[:len(image.nodes)])
            if isa.decode(word)[0]==isa.IO and isa.decode(word)[4]==isa.PRIM["world"])
    _,_,reg,n,_=isa.decode(image.image[pc])
    need(n==2,"Changed WORLD arity")
    common.to(first)
    common.settle()
    saved=next(iter(route.live.values()))
    need(decode(saved.word)==(60,60) and bus.cells[saved.slot].stock==PRICE,"No real funded old record")
    cpu.pc=pc
    cpu.R[reg:reg+2]=[42,78]
    cycle=WorldCycle(clock,ports,16*D)
    for t,operation in ((cycle.time(1,4),cycle.capture),(cycle.time(1,2),cycle.offer),(cycle.time(1),cycle.retire)):
        common.to(t);common.settle()
        if operation==cycle.retire:
            cpu.R[reg:reg+2]=[99,99]
        operation()
    original_write=route.mail_written
    need(original_write==first+8*D and cpu.retired==1 and decode(route.mail)==(42,78) and decode(route.level)==(60,60)
         and route.live[saved.slot] is saved, "CPU changed an already paid WORLD signal or DAC")
    # No superseded dispatcher is frozen. Every native ADC/TX edge and
    # outstanding WORLD application remains in the same elapsed ledger.
    def run(t,reverse=False):
        common.to(t)
        common.settle(reverse=reverse)
    run(Q(1,4))
    need(decode(route.level)==(42,78),"New word did not arrive")
    run(saved.applies)
    need(decode(route.level)==(60,60) and route.age_stamp==saved.sent and route.level_written is None,
         "Earlier word failed to arrive at its true later strobe")
    run(first+95*PERIOD)
    need(decode(route.level)==(42,78) and route.level_written==original_write and route.samples==96
         and cpu.retired==1,"Steady level required further CPU retirements")
    bus.audit();route.balance()
    stamp=route.age_stamp
    # A genuinely issued last sample is independent of the next CPU power
    # gate. Corresponding raw slots keep their source and target.
    last=next(p for p in route.live.values() if p.sent==route.now)
    cpu.inhibit()
    source.cold_cut()
    run(last.applies)
    need(route.age_stamp==last.sent and route.age_stamp!=stamp and cpu.retired==1,
         "Source power gate erased an already funded physical WORLD update")
    route.balance();bus.audit()
    physical=integrated_output(route,cut_at=last.sent,bank=bus)
    return dict(physical_output=physical,physical_outlet=WORLD,pairs=ROUTES*SLOTS,actual_WORLD_pc=pc,
                applied_in_order=[[str(at),str(sent),list(decode(word))] for at,sent,word in route.commits
                                  if sent==saved.sent or at==last.applies or sent==first+PERIOD],
                ordinary_retirements=cpu.retired,source_mail=list(decode(route.mail)),nominal_captures=route.samples,
                E_for_parents=e.supplied,E_for_all_route_caps=bus.route_received,
                outstanding_signal=route.in_line,source_qualification=route.qualification_work,actual_cpu_write=original_write,last_snapshot=last.sent,
                last_value_origin=route.level_written,
                heat_of_world_transmission=route.tx_heat+route.rx_heat)


def integrated_output(route,cut_at,bank):
    # Constant external efforts are the open plant chart here. The true
    # E includes actual signed tracker and effector work throughout the chart.
    effort=Q(1,2)
    rc=[Tracker(Q(3,5)),Tracker(Q(3,5))]
    held=(60,60)
    at=Q(0)
    def interval(t):
        nonlocal at
        for tracker,v in zip(rc,held):
            tracker.advance(t-at,Q(v,100),Q(1),1,effort)
        at=t
    for time,_,word in route.commits:
        if time>cut_at:
            break
        replacement=decode(word)
        if replacement!=held:
            interval(time)
            held=replacement
    interval(cut_at)
    # Positive delivered quantity leaves the external plant capacitor,
    # so its conjugate work enters the fixture's closed energy boundary.
    gross_heat=plus(*[(tracker.resistor_heat,1) for tracker in rc])
    actual_E=plus((scalar(bank.bank.stock),1),*[(tracker.dac_work,-1) for tracker in rc],
                  *[(tracker.world_work,1) for tracker in rc])
    qty=plus(*[(tracker.quantity,1) for tracker in rc])
    need(not plus((qty,1),(scalar(-Q(6,5)*cut_at),1)),
         "Two equal-gain coordinates with conserved sum lost protected quantity")
    # The omitted differential powers in the charging coordinate are bounded
    # by ten per active bank; the actual operating store remains in the
    # full-delivery chart at EVERY earlier transfer and below its capacity.
    E0=bank.initial_bank
    max_credit=10*cut_at
    # At the first charged microinterval the bank starts strictly inside the
    # capacity. Subsequent transfers only lower its charging coordinate.
    need(E0+max_credit<bank.bank.capacity and bank.bank.stock-max_credit>1,
         "Full-delivery projection stopped preserving true E decisions")
    need(bank.parent.io_counts.get("world",0)==1 and bank.source.samples==0,
         "An actual E-head read needs the true work observer at its own aperture")
    def show(expr):
        return {str(k):str(v) for k,v in sorted(expr.items())}
    return dict(positive_weight_time=cut_at,held_at_cut=held,protected_quantity=show(qty),
                true_final_E=show(actual_E),resistor_heat=show(gross_heat),
                true_E_lower=bank.bank.stock-max_credit,physical_world_port_work=show(plus(*[(z.world_work,1) for z in rc])),
                retained_y=[show(z.y) for z in rc],nominal_age_does_not_reset_trackers=True)


def stream_receipt():
    # With adjacent successful launches at most p apart and elapsed delay
    # in [0,T], the latest applied word can be reordered by up to 2T+p.
    # On every realized sequence the bounds involve ACTUAL launch times.
    T=Q(1)
    b=json.loads((HERE/"return_seat_results.json").read_text())
    f=Q(b["padded_frame_upper"],2**26)+Q(7,64)
    age_pre=13+3*f
    old=age_pre+12
    physical=age_pre+2*T+PERIOD
    need(-1+Q(2)/(1+Q(2,2))**2==-Q(1,2), "Retained-state ceiling on a constant input changed")
    need(physical<old and old-physical==Q(639,64),"New physical age exceeds reference allocation")
    need(128*FAST>T+D and 64*FAST<T+D,"Round-robin slot service wrongly priced")
    for xs in ((42,78),(-100,100),(0,0),(200,123),(1<<200,-(1<<200))):
        need(decode(encode(xs))==tuple(clamp(x) for x in xs),"Incorrect finite WORLD decoder")
    ceiling=2*SLOTS*1024  # conservative extra room for all outstanding carrier work, even if previously counted
    stored=Q(json.loads((HERE/"image_transport_results.json").read_text())["joined_point"]["effective_reserve"])
    old_supply=Q(json.loads((HERE/"image_transport_results.json").read_text())["joined_point"]["supply_rate_slack"])
    trigger_rate=2*64/FAST
    trigger_burst=2*64
    reserve=stored-ceiling-trigger_burst-2*trigger_rate
    extra_force=2*2*SLOTS*Q(1,2**48)*41
    reaction=Q(json.loads((HERE/"private_comparison_results.json").read_text())["price"]["marker_and_seat_reaction_left"])
    need(reserve>2**50 and old_supply>trigger_rate and reaction>extra_force,
         "WORLD storage, co-located qualification or physical side effect exceeds headroom")
    # Inlet must still achieve 300 V after a small real capacity reduction.
    # With the same fixed top voltage adapt CU to 2(Ucap-ceiling)/Vtop².
    previous=json.loads((HERE/"image_transport_results.json").read_text())["joined_point"]
    cap=Q(previous["upstream_capacity"])-ceiling
    floor=reserve-cap/4
    need(floor>0,"Cannot support receiver pressure after carving out signal capacity")
    rail=json.loads((HERE/"rx_power_results.json").read_text())["budget"]
    markers=json.loads((HERE/"rx_restoration_results.json").read_text())["bill"]
    added_marker_heat=Q(rail["zone_slack"])-Q(markers["remaining_zone_margin"])
    signal_peak=2*SLOTS*PRICE/SIGMA
    bath_left=Q(previous["bath_margin"])-added_marker_heat-4*41*(2*signal_peak+trigger_rate+40)
    # The receiving sign/magnitude clamp compares only the seven low bits
    # once it has ORed all high non-sign bits, then commits both bounded DACs.
    sink_work=128+2*(63+55+7*4+7*3+8+8)+128+32
    sender_work=128+7*40+2*128+128+64
    cpu_args_work=2*(255+247+7*4+7*3+64+64)+256
    need(sink_work<=1024 and sender_work<=3072 and cpu_args_work<=4096 and bath_left>0,
         "Finite WORLD word operations or simultaneous heat exceed the proposed allocation")
    env=dict(maximum_world_snapshot_period=PERIOD,maximum_physical_delay=T,
             CPU_clip_and_write_bound=cpu_args_work,solo_sender_bound=sender_work,
             receiver_decode_bound=sink_work,combined_bath_margin=bath_left,
             actual_word_age_upper=physical,retained_design_word_age_bound=old,
             margin_to_prior_bound=old-physical,stable_replacement_bound=2*T+PERIOD,minimum_revisit=128*FAST,
             pending_children_at_arbitrary_cut_upper=2*SLOTS,
             source_to_sink_gross_peak_per_all_two_bank_slots=2*SLOTS*PRICE/SIGMA,
             message_hard_count_per_bank_horizon="128 prior + 1 + (6464/100)L",
             useful_duration_from_word_to_scalar_range=200,
             held_minus_one_tracker_ceiling_after_200=-1+Q(2)/(1+Q(2,2))**2,
             unused_initial_or_pending_tolerance=False,
             emitting_bank_total_routes=ROUTES,source_caps_per_route=SLOTS,
             charged_signal_capacity=ceiling,reduced_U_capacity=cap,qualified_voltage_floor_slack=floor,
             additional_qualification_burst=trigger_burst,qualification_rate=trigger_rate,
             remaining_supply_rate=old_supply-trigger_rate,remaining_reaction=reaction-extra_force)
    # Four scalar trackers in two banks: two constant-effort segments with
    # different commands, and a real weight change that preserves y.
    trackers=[Tracker(Q(3,5)),Tracker(Q(3,5)),Tracker(-1),Tracker(1)]
    initial=[v.y.copy() for v in trackers]
    for i,(tr,cmd) in enumerate(zip(trackers,[Q(42,100),Q(78,100),Q(3,5),Q(3,5)])):
        tr.advance(200,cmd,Q(1),Q(i<2),Q(1,2))
    first=[tr.y.copy() for tr in trackers]
    for i,tr in enumerate(trackers):
        tr.advance(140,Q(3,5),Q(1,2),Q(i>=2),Q(1,2))
        need(not plus((tr.dac_work,1),(tr.resistor_heat,-1),(times(tr.y,tr.y),-50),(times(initial[i],initial[i]),50)),
             "Second interval lost the first bank's stored energy")
    need(initial[0]!=first[0] and initial[2]!=first[2] and not trackers[0].quantity=={},
         "Physical tracker or blend had no consequence")
    def show(a):
        return {str(k):str(v) for k,v in sorted(a.items())}
    env["retained_RC_sample"]=[dict(after_first=show(first[i]),after_second=show(tr.y),world_work=show(tr.world_work),
                                     delivered_quantity=show(tr.quantity)) for i,tr in enumerate(trackers)]
    return env


def serialize(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:serialize(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serialize(v) for v in x]
    return x


def generate():
    isa=program.load_isa()
    image,_=seat.candidate(isa)
    return serialize(dict(image=program.hash_text(json.dumps(image.image)),sender=route_trial(isa,image),
                          source=stream_receipt(),complete_regional_implementation=False,
                          files={n:sha256((HERE/n).read_bytes().replace(b"\r\n",b"\n")).hexdigest() for n in
                                 ("WORLD-CHANNEL.md","world_channel.py","private_comparison_results.json","rx_power_results.json","rx_restoration_results.json","return_seat_results.json",
                                  "image_transport_results.json","native_clock_source.py","shared_bank_charging.py",
                                  "a_prime_source_assembly.py","../local-control/port_model.py",
                                  "../local-control/resource_model.py","../local-control/hard_boundary_model.py")}))


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--write",action="store_true")
    a=p.parse_args()
    result=json.dumps(generate(),indent=2,sort_keys=True)+"\n"
    path=HERE/"world_channel_results.json"
    if a.write:path.write_text(result,encoding="utf8",newline="\n")
    else:need(path.read_text(encoding="utf8")==result,"WORLD channel receipt differs")
    print("Verified real WORLD capture, reordered delivery, rolling age and retained tracker work")
