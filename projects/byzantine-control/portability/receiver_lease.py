"""Receiver-line recovery and lease coverage on one fixed publication incidence."""
import argparse
from decimal import localcontext
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path

import rx_restoration as restoration
import legacy_realization as legacy

rx=restoration.rx
raw=rx.raw
need=rx.need
HERE=Path(__file__).resolve().parent
BASE="4bbd749178643ad7a9416df6b17a3486cdba41b4"
PEER="c5bfc5d38d6f3b6cf8b7169c20310d3c2c502be8"
PREFIX="portability/"


def pinned(name):return legacy.text_at(PEER,PREFIX+name)
def evidence(name):return json.loads(pinned(name))


def compiled():
    legacy.module_at(PEER,PREFIX+"abort_protocol_alternative.py","abort_protocol_alternative")
    seat,_=legacy.module_at(PEER,PREFIX+"return_seat.py","_lease_seat")
    matched,_=legacy.module_at(PEER,PREFIX+"matched_publication.py","_lease_matched")
    isa=seat.program.load_isa()
    image,bounds=seat.candidate(isa)
    ir=evidence("image_transport_results.json")
    need(seat.program.hash_text(json.dumps(image.image))==ir["new_image"] and
         {"publish_value","publish_plant","publish_fast","boot","wait_conversion"}<=set(ir["static"]["closed"])
         and bounds["padded_frame_upper"]==ir["padded_frame"],"Wrong funded source/publisher image")
    return isa,image,matched


class LeafArray:
    """The mutable selector and literal source reset writer address these same bits."""
    def __init__(self,words,first,extent):
        self.words=words;self.first=first;self.extent=extent
    def __len__(self):return self.extent
    def __getitem__(self,index):
        if type(index) is not int or not 0<=index<self.extent:raise IndexError(index)
        return self.words[self.first+index]
    def __setitem__(self,index,value):
        need(type(index) is int and 0<=index<self.extent and type(value) is int and value in (0,1),
             "Not an installed literal selector cell")
        self.words[self.first+index]=value


def recovery_classes(m):
    class Source(rx.native.TimedSource):
        FIRST=80*2048+4096+2
        CLOCK=FIRST+160

        def __init__(self,operating,payer,population):
            super().__init__(operating,payer,population)
            self._stencil=tuple(v for pair in m.installed_mask(population,self.origin) for v in pair)
            # Initial design data only. Later calls to begin_entry/release do
            # not execute the constructor. Raw overlays may change these bits.
            self.control[self.FIRST:self.CLOCK]=self._stencil
            self.control[self.CLOCK]=1
            self.faces={}
            need(len(self.stencil)==160 and self.CLOCK<self.BITS and self.dispatch.store is self.control,
                 "Source, reset and physical layout disagree")

        @property
        def stencil(self):return self._stencil

        def clear_value(self,index):
            if self.FIRST<=index<self.CLOCK:return self.stencil[index-self.FIRST]
            if index==self.CLOCK:return 1
            return super().clear_value(index)

        def native_tick(self):
            # Receiving clocks are active separately. One actual TX divider
            # belongs to the source even when many remote lanes are installed.
            self.adc_tick();self.tx_phase=(self.tx_phase+1)%4
            if self.tx_phase==0:
                for branch in self.branches:branch.tick()

        def deliver_symbol(self,destination,value):
            lane=self.receivers_live.get(destination)
            if lane is not None:
                face=self.faces[destination]
                need(face.l is lane and lane.payer is self.payer,"Rebound physical arrival")
                face.receive(value)

    class Selector(m.Selector):
        @property
        def clock_open(self):
            return self.physical_clock and (self.source is None or bool(self.source.control[self.source.CLOCK]))
        @clock_open.setter
        def clock_open(self,value):
            self.physical_clock=value
        def __init__(self,source,mode):
            self.source=None
            super().__init__(source.population,source.origin,mode)
            self.source=source
            self.words=LeafArray(source.control,source.FIRST,160)
    return Source,Selector


def priced_classes(m):
    # The frozen comparison loaded an equivalent bank module under a fresh
    # Python name. Base the actual new installation on the present timed CPU/E.
    local=(HERE/"shared_bank_charging.py").read_bytes().replace(b"\r\n",b"\n")
    need(m.BANK_TEXT.encode()==local,"Different operating bank law")
    class Parent(rx.charging.FramedParent):
        def __init__(self,*args,**kwargs):
            super().__init__(*args,**kwargs);self.lookup_work=0
        step=m.PublicationParent.step
        def finish_parent(self,extra_work,native=False):
            extra=self.lookup_work;self.lookup_work=0
            return super().finish_parent(extra_work+extra,native)
    class Bus(rx.charging.JointCharge):
        def __init__(self,bank,cpu,source):
            self.source=source;self.data_transferred=Q(0)
            super().__init__(bank,cpu,(*source.slots,source.adc),source.DELTA)
        charge_time=m.SparseFullDelivery.charge_time
        balance=m.SparseFullDelivery.balance
        def full_audit(self):
            need(all(slot in self.source.recharge_needed for slot in self.slots if
                     (slot.claim is None or not slot.claim.live) and slot.cell.stock<slot.cell.capacity),
                 "True source-slot charger outside observed frame")
            rx.charging.JointCharge.balance(self)
    return Parent,Bus


class ObservedClock:
    """A physical trace with one selected receiving lane; other exits stay external."""
    def __init__(self,source,bus):
        self.source=source;self.bus=bus;self.now=Q(0);self.next=Q(1,4096)
        self.face=None;self.record=None;self.rx_next=None;self.commit=None;self.rc=None
        self.records_at=[]

    def observe(self,face,key):
        need(self.face is None and face.l is self.source.receivers_live[face.l.identity],"Uninstalled RX clock")
        self.face=face;self.record=key;self.rx_next=self.now+Q(1,8192)
        face.lane.time=face.records[key].time=self.now  # observer's relative origin at this physical cut
        self.source.faces[face.l.identity]=face
        self.next_tick=self.now+Q(5000,5001) # no countdown edge in the short DATA capture trace

    def advance(self,dt):
        end=self.now+Q(dt)
        need(end>=self.now,"Negative interval")
        while self.now<end:
            k=self.record;f=self.face
            due=[end,self.next]
            if f is not None:
                due.extend([self.rx_next,self.next_tick])
                if self.commit is not None:due.append(self.commit)
                if self.rc is not None:due.append(self.rc)
            for b in self.source.branches:
                if b.flights:due.append(self.now+b.flights[0].remaining)
            t=min(due);elapsed=t-self.now
            self.bus.charge_time(elapsed)
            # No raw RX/record aperture is hidden in the following wire flow.
            # For this trace choose already emitted arrivals before tied RX.
            if f is not None and (t in (self.rx_next,self.commit,self.rc,self.next_tick)
                    or any(b.flights and b.destination==f.l.identity and b.flights[0].remaining==elapsed
                           for b in self.source.branches)):
                # Exact passive frame over the skipped CPU-only substeps.
                f.lane.unpowered(t-f.lane.time);f.records[k].unpowered(t-f.records[k].time)
            self.now=t
            for b in self.source.branches:
                if b.flights or b.wire_credit<raw.WIRE_BURST:
                    b.advance_wire(elapsed,self.source.deliver_symbol)
            if t==self.next:
                self.source.native_tick();self.next+=Q(1,4096)
            if f is None:continue
            if self.rx_next==t:
                f.base();self.commit=t+rx.SIGMA;self.rx_next+=Q(1,4096)
            if self.commit==t:
                self.commit=None
                result=f.receive_return()
                if result=="frame":self.rc=t+raw.RECORD_DELAY
            if self.next_tick==t:
                f.tick(k);self.rc=self.rc or t+raw.RECORD_DELAY
                self.next_tick+=Q(5000,5001)
            if self.rc==t:
                result=f.service(k);self.rc=None
                if result=="receipt":self.records_at.append((t,f.l.records[k].readable()))
                r=f.l.records[k]
                if r.control[r.BUSY] or r.control[r.RECEIPT_VALID] or r.queued_tick:
                    self.rc=t+raw.RECORD_DELAY


def selector_residue(isa,image,m):
    cpu,ports=m.fixture(isa,image,2,m.SELECT)
    s=ports.source;tap=ports.selector
    client,key=next((j,k) for j,pair in enumerate(m.installed_mask(s.population,2)) for k,v in enumerate(pair) if v)
    tap.words[2*client+key]=0
    # Real old-source reset at its actual owner, followed by genuine rearm.
    need(s.reform()=="formed-unpowered" and s.begin_entry(cpu.bank)
         and s.entry_flow(Q(s.ENTRY_WORK,raw.CLEAR_RATE)),"Old source failed to reach its own reset terminal")
    need(tap.words[2*client+key]==0,"Standalone source reset already restores the separate table")
    ports.clock.advance(2*m.DELTA)
    m.convert(ports,key,855)
    def offer():
        before=len(ports.receipts)
        m.program.call(isa,image,ports,"publish_value",(key,),1000,cpu)
        matches=[v for v in ports.receipts[before:] if v[0]==client]
        need(len(matches)==1,"Wrong destination")
        return matches[0][2:]
    one=offer();two=offer()
    tap.mode=m.PASS
    pass_result=offer()
    tap.clock_open=False
    stopped=offer()
    need(one==two==("source-suppressed",None) and pass_result==("forward","accepted")
         and stopped==("interrupted",None),"Wrong silent-supplier branches")
    return dict(target=client,key=key,post_reform_leaf=tap.words[2*client+key],
                repeated_ordinary_outcomes=(one,two),forward_all=pass_result,stopped_clock=stopped,
                missing_subscription_restored_by_old_source=False)


def stopped_receiver(isa,image,m):
    origin=2;pop=m.POPULATION
    j,key=next((j,k) for j,p in enumerate(m.installed_mask(pop,origin)) for k,v in enumerate(p) if v)
    target=rx.wiring.incidence.neighbors(pop,origin)[j//2];side=j%2
    U=raw.SourceWork(origin,2**40,2**36)
    lhs=raw.RawLane(pop,raw.LaneId(origin,0,target,side),U)
    rhs=raw.RawLane(pop,raw.LaneId(origin,1,target,side),U,lhs.captures)
    r=lhs.records[key];r.value=17;r.set_ttl(1);r.control[r.ENABLE]=0
    counterpart=rhs.records[key]
    c=rx.Receiver(lhs,rx.phases([lhs])[lhs.identity])
    # Those stopped calls have no effect on the bad row; other keyed clocks
    # and sibling traffic can continue. This is a local commuting projection.
    need(c.stage(key,855)=="staged","No actual new offered receiver data")
    skipped=0
    for n in range(1025):
        t=c.clocks[key].due;first,kind,binding=c.read_jobs[key]
        # Every due service on this intact-but-disabled record returns stopped
        # and re-arms the same stage for another positive RECORD_DELAY. Fold
        # exactly those retries, with no effect on the independent raw word.
        if first<=t:
            steps=1+(t-first)//raw.RECORD_DELAY
            c.now=first;need(c.act(("commit",key))=="stopped","An old receipt wrote through disable")
            c.read_jobs[key]=(first+steps*raw.RECORD_DELAY,kind,binding);skipped+=steps
        c.now=t;c.act(("tick",key))
        need(counterpart.start_tick()=="started" and counterpart.service()=="tick","Healthy sibling clock stopped")
    # Supply one genuine independently serviced sibling word at this cut.
    need(counterpart.stage_receipt(855)=="staged" and counterpart.service()=="receipt",
         "A good sibling receipt was not actually acquired")
    need(r.readable()==17 and r.ttl==1 and r.staged==855 and counterpart.readable()==855,
         "A fresh sibling or an elapsed counter wall time overwrote the bad row")
    return dict(old_exposed=r.readable(),new_staged=r.staged,nominal_elapsed_ticks=1025,
                failed_scheduled_receipt_services=skipped,old_ttl=r.ttl,other_bank_value=counterpart.readable(),actual_origin=origin,
                same_role_capture=lhs.captures[r.role] is rhs.captures[r.role])


def interval_calculation():
    timing=json.loads((HERE/"publication_timing_results.json").read_text())
    F=Q(timing["frames"]["max"]);fmin=Q(timing["frames"]["min"])
    sensor=Q(1); fanout=Q(2);R=raw.RECORD_DELAY
    source_tx=Q(129,256);flight=raw.WIRE_DELAY;array=Q(1025,4096)
    delivery=source_tx+flight+array+2*R
    need(delivery==Q(8227,8192)<Q(timing["primitive_assumptions"]["data_delivery"]),"New physical suffix misses published budget")
    mintick=rx.RECORD_RANGE[0]-2*R;maxtick=rx.RECORD_RANGE[1]+2*R
    need(mintick>=Q(100,101) and maxtick<=1 and 2*R<rx.BASE_RANGE[0],
         "True ongoing decrement bounds failed")
    rows={}
    for name,E,P in (("plant",8,2*F),("maintenance",512,226*F)):
        old=timing["receipts"][name]
        length=(E-1)*Q(100,101); maximum_gap=P+delivery
        need(Q(timing["publication_periods"][name])==P and length>maximum_gap
             and sensor+fanout+delivery+E<=Q(old["singleton_age"]),
             "No strictly positive genuine observation interval")
        rows[name]=dict(offer_gap=P,commit_gap=maximum_gap,min_readable=length,
                        no_worse_overwrite_bridge=length-maximum_gap,source_to_visible_age=sensor+fanout+delivery+E,
                        expiry_after_last_old_issue=flight+array+2*R+old["arbitrary_counter_cap"],
                        expiry_after_last_scheduled_old_offer=delivery+old["arbitrary_counter_cap"])
    acquisition=228*F+delivery
    need(acquisition==Q(66569369,262144),"Incomplete functional first-fold span")
    control=rx.gates.record("rx_restoration_results.json")["bill"]
    wait=Q(control["source_recovery_plus_front_cut"])
    mask_native=raw.MODES[0][3]
    cutoff=4-raw.VMAX*(raw.CONTROL_DELAY+wait+mask_native)
    need(Q(2)<cutoff<4,"No guaranteed early-partial MASK or false late-partial certificate")
    it=evidence("return_itinerary_results.json")["budget"];normal=Q(it["sampled_fresh_half"])
    cap=Q(it["candidate_entry_to_ready_and_outgoing_retirement"])
    H=Q(it["H"])
    need(cap+acquisition<H and 3*normal+acquisition<H,"Raw acquisition no longer fits the reported envelope")
    geometry=rx.gates.record("threshold_geometry_results.json")["arithmetic"]["physical_inputs"]
    warm=Q(geometry["warm_at"])
    # Recheck from the actual immutable source image/point instead of
    # manufacturing a new controller state at this numerical orientation.
    need(warm==6800000000,"Rebind the post-power geometric distance")
    preloss=(warm-Q(geometry["power_at"]))/raw.VMAX
    boot=Q(timing["initialization"]["boot"])
    native=Q(rx.gates.record("input_lifecycle_results.json")["resources"]["local_source_entry_time"])
    guarded=boot+native+acquisition+Q(7,2)*rx.native.DELTA
    need(guarded<preloss,"Data commissioning cannot lead old-bank loss")
    pair=Q(rx.gates.record("input_lifecycle_results.json")["resources"]["pair_read_window"])
    need(pair>0 and guarded+pair<preloss,"Actual replacement cannot cover the pair-read window")
    return dict(Fmax=F,Fmin=fmin,flight=flight,TX=source_tx,RX=array,staging=2*R,delivery=delivery,
                min_completed_tick=mintick,max_completed_tick=maxtick,per_key=rows,
                first_all_keys_including_fold=acquisition,early_MASK_max_remaining_coordinate=cutoff,
                sufficient_partial_coordinate=2,worst_clean_normal_row_pair=3*normal+acquisition,
                charged_itinerary_plus_acquisition=cap+acquisition,strict_margin_H=H-cap-acquisition,
                available_POWER_to_WARM=preloss,post_power_information_upper=guarded,pair_window=pair,
                raw_handoff_separation=preloss-guarded-pair,initial_itinerary_is_conditional=True)


def mask_boundary(isa,image,m):
    src_cls,selector_cls=recovery_classes(m); U=raw.SourceWork(2,2**40,2**35)
    e=rx.charging.OperatingBank((2,1),2**60,Q(2**60));s=src_cls(e,U,m.POPULATION);sel=selector_cls(s,m.SELECT)
    for j in range(160):sel.words[j]=1-s.stencil[j]
    s.control[s.CLOCK]=0
    wanted=next(j for j,x in enumerate(s.stencil) if x)
    target=s.FIRST+wanted
    old=sel.words[wanted]
    # A contaminated native suffix just before the physical bit write.
    need(s.begin_reset()=="masked" and s.apply_native_mode(3),"No genuine mode prefix")
    s.cursor=target; s.reset_setup=0;s.abort_cursor=len(s.slots)+1;s.reset_micro=0
    s.reset_work.stock=Q(1)
    s.reset_native(Q(2,raw.CLEAR_RATE))
    need(s.cursor==target and s.reset_micro==1 and sel.words[wanted]==old,
         "Capture-only/unfunded edge counted as completed restoration")
    s.reset_native(Q(1000));need(s.cursor==target and sel.words[wanted]==old,"Unfunded time bought a rewrite")
    return dict(old_subscription=old,required_subscription=s.stencil[wanted],actual_work_spent=s.reset_work.spent,
                retained_half_write=s.reset_micro,unchanged_after_unfunded_time=True,
                actual_source_dispatch_offset=target-(80*2048+4096),source_bitmap=s.BITS,
                reset_control_bits=len(s.engine.store))





class SharedOrigin(raw.SourceWork):
    """Interval observation of one physical U on the held rail chart.
    No unconstrained component can spend the endpoints as two reservoirs."""
    def __init__(self,origin,cap,opening):
        super().__init__(origin,cap,opening)
        self.lower=self.upper=Q(opening);self.rail_lo=self.rail_hi=Q(0)
        self.origin_events=Q(0)
    def debit(self,value):
        value=Q(value);need(value>=0,"Negative debit")
        if self.upper<value:return False
        need(self.lower>=value,"Refine the shared world to decide this U admission")
        self.lower-=value;self.upper-=value;self.spent+=value;self.origin_events+=value
        self.stock=self.lower  # Lower credit projection; no differently resolved read is used.
        need(self.lower>Q(4,9)*self.capacity,"Source-local work invalidated the rail-pressure bracket")
        return True
    def rails(self,dt,limit):
        dt=Q(dt)
        # Source-side drive is between 400 and 500 on this no-inflow
        # finite slice. Integrate the actual bounded current. The new lower
        # bound below verifies the assumed lower voltage by first crossing.
        lo,hi=400*limit*dt,500*limit*dt
        self.rail_lo+=lo;self.rail_hi+=hi;self.lower-=hi;self.upper-=lo
        self.stock=self.lower
        need(self.lower>Q(4,9)*self.capacity and self.upper<=Q(25,36)*self.capacity,
             "The other outlets invalidate the nominated common saturated-rail chart")
    def fill_source(self,cell,dt):
        q=min(cell.capacity-cell.stock,cell.capacity*dt/raw.RESET_REFILL)
        need(self.debit(2*q),"No actual same-origin source refill")
        cell.stock+=q;cell.received+=q;cell.heat+=q


def jointly_clear(s,selector,lane,U):
    """Fresh phase-6 operation on the original source and receiving row.
    Sample every physical period, fold only disjoint elapsed/native work,
    and keep whichever terminal relation the actual capacitor bounds force."""
    line=lane.line
    s.control[s.CLOCK]=0
    for j,v in enumerate(s.stencil):selector.words[j]=1-v
    lane.poison(include_shared=False)
    for j in range(8):
        line.words[j]=15;line.valid[j]=False
        line.snapshots[j]=(3,True);line.remaining[j]=raw.cam.CONTROL_STEP*Q(19,31)
    reset=lane.reset_work;need(reset.payer is s.payer is U,"Cannot join proxy costs on different physical U")
    stage_spec=restoration.power.catalogue()["control"]
    need(stage_spec.energy200-stage_spec.burst-stage_spec.pending>stage_spec.floor+stage_spec.sealed+2048+restoration.M,
         "Control banks can enter below physical admission pressure")
    # Eight fixed control stages plus the endpoint's own raw/record/reset
    # rails and its shared primary/auxiliary comparison feeders. One U.
    shapes=restoration.power.catalogue()
    charges=dict(rx=1,record=len(lane.records),control=8,capture=2,reset=1)
    I=sum(charges[k]*shapes[k].inlet()["limit"] for k in charges)
    cur=None;start=Q(0);last=Q(0);p=Q(1,8);h=raw.cam.CONTROL_STEP
    applications=0;work=Q(0);clock_clear=0;row_work=0;spans={};tx_edges=0
    last_use={}
    def level_elapsed(mode,left,right):
        nonlocal clock_clear,row_work
        dt=right-left
        if mode==raw.CHARGE:
            U.fill_source(s.reset_work,dt)
            reset.qualified_charge(dt)
        elif mode==raw.DUMP:
            lead=Q(s.reset_setup+8*(len(s.slots)+1-s.abort_cursor)-s.reset_micro,raw.CLEAR_RATE)
            s.reset_native(lead)
            need(dt>=lead+100,"Old source claims or dump did not fit")
            for cell in s.slots+[s.adc]:cell.cell.dump(100)
            if reset.energy_bounds is not None:reset.coast_bounds(dt)
        elif mode==raw.CLEAR:
            s.reset_native(dt)
            clock_clear=s.cursor
            need(reset.energy_bounds is not None,"No reset charge")
            row_work=reset.clear(lane,dt)
        spans[mode]=dt
    for n in range(1+int(Q(raw.MODES[-1][2])/raw.VMAX/p)+10):
        t=n*p;pos=t*raw.VMAX;fund=t+h
        U.rails(fund-last,I);last=fund
        # Base oscillator starts with one whole period left at the initial
        # cut; the finitely many intervening unpowered TX edges have no
        # emit or input authority. Its writable phase still evolves.
        ticks=int(fund*4096)-tx_edges
        need(not s.powered and not s.emit_gate,"An unexplained producer could spend this prefix")
        s.tx_phase=(s.tx_phase+ticks)%4;tx_edges+=ticks
        code=next((mode for mode,left,right,_ in raw.MODES if left<=pos<right),raw.OPEN)
        for j in range(8):
            # Actual predecessor wire before any of these simultaneous captures.
            # No genuine earlier return remains at these well-separated native
            # apertures. Dirty writable BUSY still cannot manufacture a return.
            need((j,n%2) not in last_use or t-last_use[j,n%2]>=h+restoration.REARM,"Occupied physical control slot")
            last_use[j,n%2]=t
            line.snapshots[j]=None;line.remaining[j]=0;line.capture(j,code)
        for j in range(8):line.remaining[j]=0;new=line.commit(j)
        if new!=cur:
            level_elapsed(cur,start,fund)
            cur=new;start=fund
        need(s.apply_native_mode(new),"Underfunded/stopped local mode")
        # Receiver's positive voltage stock is a derived observation on this
        # rail, not a second debit from U at the native return.
        work+=8*(raw.cam.STAGE_PRICE+restoration.M)+256+restoration.M;applications+=1
        lane.mode=new;lane.mode_applications+=1;lane.time=fund
        if new in (raw.MASK_MODE,raw.CHARGE,raw.DUMP,raw.CLEAR):
            lane.masked=True;lane.ingress=lane.write_gate=False
        if new==raw.MASK_MODE:
            lane.reset_control[:]=[0]*raw.ENGINE_BITS;lane.cursor=0;lane.setup_paid=False;lane.clear_phase=Q(0)
            for cap in lane.captures.values():cap.set_clock_one()
        if new==raw.OPEN:lane.masked=False;lane.ingress=lane.write_gate=True
    need(cur==raw.OPEN and lane.certificate() and clock_clear==s.BITS
         and tuple(selector.words)==s.stencil and s.control[s.CLOCK]==1 and not s.admission
         and s.reset_work.spent==504329,"A level label did not re-form both native sources")
    need(all(r.ttl==0 for r in lane.records.values()),"Reformation left an unproved live sample")
    return dict(physical_control_strobes=applications,control_work_with_local_metres=work,
        source_clear_slots=clock_clear,source_reset_work=s.reset_work.spent,receiver_clear_work=row_work,
        unpowered_source_TX_base_edges=tx_edges,retained_TX_phase=s.tx_phase,
        next_TX_base=Q(tx_edges+1,4096)-last,
        reset_charge_elapsed=spans[raw.CHARGE],clear_elapsed=spans[raw.CLEAR],set_to_unavailable=True,
        U_lower_at_OPEN=U.lower,U_upper_at_OPEN=U.upper,actual_local_U_work=U.origin_events,
        rail_work_interval=(U.rail_lo,U.rail_hi),receiving_identity=lane.identity.__dict__)


class LeaseMeter(restoration.MeteredCell):
    """Lower comparison only for an already physically supplied interval.

    The exact unknown main energy is never read by the publisher or exposed
    as the sampled word. Every functional pressure test must hold even at
    the lower bound; otherwise this observer cannot certify its branch.
    """
    def enter_observation(self,lo):
        need(self.s.floor<lo<=self.s.energy200 and not self.encumbered,
             "Not a quiescent legitimately pre-funded observation cut")
        self.upper=self.s.ceiling;self.W=restoration.D(lo)
    def reserve(self,cost,horizon,tag,*,sink=None,net=0):
        need(self.W>=restoration.D(self.s.floor+self.s.sealed+cost+restoration.M),
             f"Insufficient lower observation for {self.s.name} {tag} at {self.time}: {self.W}")
        return super().reserve(cost,horizon,tag,sink=sink,net=net)


def install_receiving_faces(l,U):
    # One-time allocation of the raw/intermediate evidence. No later reset
    # replaces the raw queue, the capture, a cell, its owner or its press.
    layout=rx.Receiver(l,rx.phases([l])[l.identity]);types=restoration.power.catalogue()
    class FixedFaces(restoration.power.ReceiverFaces):pass
    face=FixedFaces.__new__(FixedFaces)
    face.face=layout;face.l=l;face.source=U
    face.key=next(iter(l.records));face.r=l.records[face.key]
    i=l.identity;site=(i.receiver,i.receiver_bank)
    face.lane=LeaseMeter(types["rx"],(i,"rx"),site,200)
    face.records={k:LeaseMeter(types["record"],(i,k),site,200) for k in l.records}
    face.record=face.records[face.key]
    face.stages=[LeaseMeter(types["control"],(i,j),site if j>=4 else (i.origin,i.source_bank),200)
                 for j in range(8)]
    face.stage=face.stages[-1]
    cap=l.captures[face.r.role]
    feeder=LeaseMeter(types["capture"],(cap.owner,cap.kind),site,200);feeder.capture_sink=cap.cell
    return face,feeder


def joint_offer(isa,image,m):
    Source,Selector=recovery_classes(m);origin=2;side=1
    point=restoration.power.budgets()
    integrated=evidence("image_transport_results.json")["joined_point"]
    # Budgeted relocated leaves add neither a store nor an energy draw.
    capU=Q(integrated["upstream_capacity"])
    U=SharedOrigin(origin,capU,capU*Q(25,36))
    cap=int(Q(rx.gates.record("parent_realization_results.json")["cost_bounds"]["actual_bank_capacity"]))
    operating=rx.charging.OperatingBank((origin,side),cap,Q(2**60))
    s=Source(operating,U,m.POPULATION);sel=Selector(s,m.SELECT)
    # A source-cut, no-local-claims representative at contact entry. Its
    # true TX base keeps ticking; no branch may act while its circuit is cut.
    for branch in s.branches:branch.bits.put(27,1,0);branch.bits.put(28,1,0)
    s.adc_bits.put(2050,1,0)
    client,key=next((j,k) for j,pair in enumerate(m.installed_mask(s.population,origin))
                    for k,v in enumerate(pair) if v)
    target=s.branches[client].destination
    lane=raw.RawLane(m.POPULATION,target,U)
    lane.reset_work=restoration.ResetCap(target,U,point)
    s.attach(lane)
    f,feeder=install_receiving_faces(lane,U)
    need(f.key==key and feeder.capture_sink is lane.captures[lane.records[key].role].cell,
         "Observed key and fixed receiving store mismatch")
    after=jointly_clear(s,sel,lane,U)
    # The canonical handoff's long open, empty source-silent interval exceeds
    # the cold-pressure bound. On that interval the RX only pays for its
    # alternate/empty divider (544); the selected empty record has at most
    # a normal tick's start/finish and a queued capture. After reaching S
    # the last-hit storage comparison gives S minus burst and outstanding
    # work. Other branch/capture users retain the full installed bound.
    f.lane.enter_observation(f.lane.s.energy200-4*(32+restoration.M))
    f.record.enter_observation(f.record.s.energy200-2*(128+3*restoration.M))
    feeder.enter_observation(feeder.s.energy200-feeder.s.burst-feeder.s.pending)
    # Separate physical POWER context after confirmed code formation and true
    # zero-arm crossing. The transition never reinitializes the completed rows.
    Parent,Bus=priced_classes(m)
    cpu=Parent(isa,image,bank=operating)
    bus=Bus(operating,cpu,s);clock=ObservedClock(s,bus)
    # Upper first/new receipt laws are for every actual later TX divider
    # and phase. The illustrated POWER cut has the same cycle residual
    # as the earlier endpoint (intervening phase difference zero modulo four).
    clock.next=after["next_TX_base"]
    need(s.begin_entry(operating) and s.entry_flow(Q(s.ENTRY_WORK,raw.CLEAR_RATE))
         and s.reset_work.spent==566835,"Earlier remote OPEN became an unfunded power-up")
    clock.advance(2*m.DELTA)
    ports=m.ports_for(isa)(image,s,clock,sel)
    # Earlier formation paid for these pre-existing receiving stores. Later
    # zero-inflow comparison throughout this short trace is conservative.
    clock.observe(f,key)
    m.convert(ports,key,913)
    moment=clock.now
    m.program.call(isa,image,ports,"publish_value",(key,),1000,cpu)
    need((client,key,"forward","accepted") in ports.receipts and sel.paid==80*m.PRICE,
         "New source emitted no accepted offer on the subscribed branch")
    stop=clock.now+Q(3,10)
    while not clock.records_at:
        need(clock.now<stop,"Genuine source frame did not arrive in its admissible interval")
        clock.advance(Q(1,4096))
    need(len(clock.records_at)==1 and lane.records[key].readable()==913,"No actual delivered retrievable sample")
    t,word=clock.records_at[0]
    capture=lane.captures[lane.records[key].role]
    need(feeder.capture_sink is capture.cell,"Feeder was rebound")
    need(feeder.reserve(2048,restoration.DELTA,"capture-fill",sink=capture.cell,net=1024),
         "Real earlier descriptor/stock missing")
    for _ in range(2):
        feeder.unpowered(restoration.DELTA/2);clock.advance(restoration.DELTA/2)
    need(capture.cell.stock==1024 and source_identity(capture,lane) and
         capture.begin(lane,key)=="captured","Wrong receiving owner or raw request")
    read=capture.pending
    for _ in range(2):
        clock.advance(restoration.DELTA/2)
        need(capture.cell.debit(512),"Actual bound read lost its own work")
        capture.cell.heat+=512
    need(read.destination==(lane,key) and read.dispatch(lambda pair,_:setattr(capture,"snapshot",
         pair[0].read(pair[1]))) and capture.snapshot==word,"Wrong settled raw value")
    capture.pending=None;bus.full_audit()
    return dict(physical_repair=after,incidence=target.__dict__,key=key,return_seat_image_offer=True,
                offered_from=moment,committed=t,obtained=capture.snapshot,receipt=lane.records[key].ttl,
                source_owner_id=s.payer.origin,source_reset_combined=s.reset_work.spent,
                changed_visible_selector_bits=160,main_WARM_release_is_external=True,
                capture_owner=capture.owner,original_fixed_read_retired=not read.live)


def source_identity(c,l):
    i=l.identity
    return c.owner==(i.origin,i.receiver,i.receiver_bank) and c.payer is l.payer

def premature_unmask():
    banks,rows,world=restoration.first_bank()
    f=restoration.bind(rows[0],world);l=f.l;key=f.key;r=f.r
    r.value=17;r.set_ttl(1);r.control[r.ENABLE]=0
    A,B=f.stages[6],f.stages[7];h=restoration.power.STAGE;p=Q(1,8)
    l.line.words[5]=raw.OPEN;l.line.valid[5]=True
    l.line.words[6]=raw.MASK_MODE;l.line.valid[6]=True
    need(restoration.stage_event(f,7,raw.MASK_MODE)=="captured","Missing the first real final copy")
    A.unpowered(h/2);B.unpowered(h/2)
    need(restoration.stage_event(f,6,raw.MASK_MODE)=="captured","No retained upstream OPEN wire")
    A.unpowered(h/2);B.unpowered(h/2)
    need(l.masked and r.readable()==raw.MASK and r.ttl==1,"MASK was treated as a data/TTL reset")
    A.unpowered(h/2);B.unpowered(h/2)
    need(l.line.words[6]==raw.OPEN,"The older upstream history did not reach stage 6")
    B.unpowered(p-B.time)
    need(restoration.stage_event(f,7,raw.MASK_MODE)=="captured","Missing real later copy")
    B.unpowered(h)
    need(not l.masked and not r.control[r.ENABLE] and r.readable()==17,
         "A transient MASK was mistaken for irreversible retirement")
    return dict(mask_at=h,reopened_at=p+h,old_payload_again=r.readable(),real_source_bank=f.l.identity.source_bank)


def intersection_and_order():
    # The strongest exact coverage test on obtained bank values is evaluated
    # on the same chronological path. A sufficient reusable test carries
    # one physical bank throughout the whole possible pair span.
    w=Q(33,2**26)
    first,second=Q(0),w
    intervals={0:(w/3,2*w),1:(-w,2*w/3)}
    contains=lambda t,b:intervals[b][0]<=t<=intervals[b][1]
    need(not contains(first,0) and not contains(second,1)
         and intervals[0][0]<intervals[1][1],"Sequential/instantaneous coverage obstruction disappeared")
    # A prior clean committed signal can bridge a handoff gap strictly
    # inside its TTL; at equality decrement-first and capture-first differ.
    origin=2;pop=12*(6+2**98)+2
    U=raw.SourceWork(origin,2**40,2**32)
    lane=raw.RawLane(pop,raw.LaneId(origin,0,0,0),U)
    k=next(k for k,v in lane.records.items() if v.lifetime==8)
    r=lane.records[k]
    outcomes=[]
    for decrement_first in (False,True):
        r.value=441;r.set_ttl(1)
        need(r.start_tick()=="started","Missing real decrement")
        if decrement_first:r.service()
        snapshot=lane.private_capture(k,r.role)
        if not decrement_first:r.service()
        outcomes.append(snapshot)
    need(outcomes==[441,raw.MASK],"Expiry and capture were incorrectly made commutative")
    return dict(sequential_pointwise_pair_can_miss=True,abstract_overlap=w/3,
                real_capture_first=outcomes[0],real_decrement_first=outcomes[1])


def initial_entry(m):
    Source,Selector=recovery_classes(m);out=[]
    for active in (False,True):
        side=int(not active)
        payer=raw.SourceWork(2,2**48,2**40)
        e=rx.charging.OperatingBank((2,side),2**50,Q(2**50 if active else 0))
        s=Source(e,payer,m.POPULATION);selector=Selector(s,m.SELECT)
        # This is the actual one-time active/cold physical product. Merely
        # passing a new constructor to the older bulk-zero recipe would
        # erase the new source's installed nonzero terminal values.
        s.control[:]=[0]*s.BITS
        for slot in (*s.slots,s.adc):
            slot.admission=slot.output=active;slot.reset=not active
        for b in s.branches:
            b.bits.put(27,1,int(active));b.bits.put(28,1,int(active))
        s.adc_bits.put(2050,1,int(active));s.dispatch.put(1,1,int(active))
        s.engine.store[:]=[0]*96;s.engine.put(89,4,4 if active else 0);s.engine.put(93,1,1)
        s.powered=s.admission=s.emit_gate=active;s.energy=e;s.reset_work.stock=Q(0)
        for j in range(8):s.I[j]=raw.MASK if j%2 else 0
        kept=tuple(s.control)
        for j,z in enumerate(s.stencil):selector.words[j]=z if active else 1-z
        s.control[s.CLOCK]=int(active)
        need(all(s.control[j]==old for j,old in enumerate(kept) if not s.FIRST<=j<=s.CLOCK)
             and s.energy is e and s.payer is payer and s.reset_work.spent==0 and not s.engine.get(94),
             "Initial selector data funded another entry or altered an existing field")
        need(tuple(selector.words)==(s.stencil if active else tuple(1-v for v in s.stencil)),
             "Initial active and arbitrary cold tapes were confused")
        out.append(dict(active=active,selector_clock=selector.clock_open,paid_reset_work=s.reset_work.spent,
                        correct_taps=sum(int(x==y) for x,y in zip(selector.words,s.stencil))))
    return out


def stencil_bill():
    size=raw.LocalSourceBank.BITS;first=80*2048+4096+2;last=first+160
    # Immutable electrical addresses; these are NOT a new root that tests
    # image equality, membership health or runtime truth.
    occupied={0,1};uses=set(range(2,163))
    need(not occupied & uses and last<size and size==168192,"New reset layout aliases a live field")
    matched=evidence("matched_publication_results.json")["common_envelope"]
    shadow=matched["explicit_bits_per_bank"]+161
    current=evidence("image_transport_results.json")["joined_point"]
    marker=rx.gates.record("rx_restoration_results.json")["bill"]
    reaction_margin=Q(current["reaction_slack"])-Q(marker["charged_extra_reaction"])
    need(shadow<=matched["additional_bits_per_bank_ceiling"] and matched["event_work"]==4096
         and Q(matched["service_upper_q"])<Q(matched["shortest_CPU_cycle_q"])
         and reaction_margin>0 and Q(current["supply_rate_slack"])>0,
         "Reset terminals no longer fit the physically joined selector timing/stock point")
    m=legacy.module_at(PEER,PREFIX+"matched_publication.py","_lease_geometry")[0]
    mask=m.installed_mask(m.POPULATION,2)
    checked=0
    for n,t in enumerate(rx.wiring.incidence.neighbors(m.POPULATION,2)):
        decoder=raw.legacy.ArrivalDecoder(m.POPULATION,t,2)
        for side in (0,1):
            for key in (0,1):
                need(mask[2*n+side][key]==int(decoder.decode(key) is not None),
                     "Independent physical subscription stencil differs from its actual fixed destination")
                checked+=1
    return dict(checked_fixed_taps=checked,old_clear_addresses=size,changed_preset_addresses=161,old_source_terminal_bits=1822,
                conservatively_used_high_bits=shadow,high_bit_ceiling=2048,extra_bitmap_steps=0,
                reset_work_per_bank=504329,reset_plus_entry=566835,offer_work=4096,
                joined_U_capacity=Q(current["upstream_capacity"]),joined_supply_slack=Q(current["supply_rate_slack"]),
                joined_reaction_slack=reaction_margin,
                stencil_scope="same physical origin and bank; sink route, local clock and force/drop/bypass remain fallible")


def generate():
    isa,image,m=compiled()
    with localcontext() as ctx:
        ctx.prec=70
        return rx.gates.normalize(dict(base=BASE,external_point=PEER,
            production_image=m.program.hash_text(json.dumps(image.image)),
            interval=interval_calculation(),unrepaired_selector=selector_residue(isa,image,m),
            stopped=stopped_receiver(isa,image,m),real_offer=joint_offer(isa,image,m),
            partial_write=mask_boundary(isa,image,m),initial_selector=initial_entry(m),interrupted_pipeline=premature_unmask(),
            adjacent_banks=intersection_and_order(),selector_repair_price=stencil_bill(),source_hashes={f:rx.wiring.initial.program.digest(HERE/f)
             for f in ("receiver_lease.py","RECEIVER-LEASE.md","RX-RESTORATION.md","rx_restoration.py",
             "publication_timing.py","publication_timing_results.json","input_lifecycle.py","legacy_realization.py",
             "shared_bank_charging.py","threshold_incidence_model.py","threshold_initialization_results.json",
             "input_lifecycle_results.json","threshold_geometry_results.json","threshold_gate_source.py",
             "rx_product.py","rx_power.py","rx_restoration_results.json")},
            external_hashes={name:sha256(pinned(name).encode()).hexdigest() for name in
             ("return_seat.py","abort_protocol_alternative.py","matched_publication.py",
              "image_transport.py","image_transport_results.json","return_itinerary.py","return_itinerary_results.json",
              "matched_publication_results.json","RecurrentSupport.lean","RECURRENT-SUPPORT.md")},
            global_mission=False,all_source_histories_instantiated=False))


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    g.add_argument("--write",action="store_true");g.add_argument("--check",action="store_true")
    o=p.parse_args();path=HERE/"receiver_lease_results.json"
    data=json.dumps(generate(),sort_keys=True,indent=2)+"\n"
    if o.write:path.write_text(data,encoding="utf-8",newline="\n")
    else:need(path.read_text(encoding="utf-8")==data,"Receiver lease result differs")
    print("PASS raw publication, control-field repair, paired-row exposure and source-cut timing; global closure open")
