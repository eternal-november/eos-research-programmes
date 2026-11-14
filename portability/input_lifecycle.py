"""Source-bank-owned ordinary input reset and coherent timed record leaves.

A mathematical local source construction and checked adapter candidate.
No whole-history restoration, truthful-data oracle or global READY is supplied.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import json
import random
from pathlib import Path
import sys
import cam_reformation as cam
import legacy_realization as legacy
import threshold_program_model as program
import threshold_design as design
import threshold_incidence_model as incidence
import fixed_island_model as islands

HERE=Path(__file__).resolve().parent
BASE="57e475c82d13267161f617ebf240791e89e152d3"
MASK=(1<<256)-1
KEYS=2003
REC_BITS=64
RX_BITS=8192
DEC_BITS=2047*32
ENGINE_BITS=96
RESET_CAP=1<<20
RESET_REFILL=F(1000)
CLEAR_RATE=1<<20
DUMP_TIME=F(100)
RECORD_DELAY=F(64,1<<20)
WIRE_DELAY=F(1,4)
TICK_WORK=128
RX_WORK=16384
TICK_POWER=1<<26
RX_POWER=1<<31
MASK_MODE,CHARGE,DUMP,CLEAR,OPEN=range(5)
CONTROL_DELAY=cam.CONTROL_DELAY
VMAX=F(11,10)
MODES=((MASK_MODE,F(0),F(4),F(1,4)+F(256,1<<20)),
       (CHARGE,F(4),F(1107),F(1000)),
       (DUMP,F(1107),F(1220),F(100)+F((80*2048+4096+256)//2+1281+8*(80*129+1),CLEAR_RATE)),
       (CLEAR,F(1220),F(1223),F(1,2)))
OPEN_AT=F(1223)
need=program.need

def nat(x,bound,label):
    need(type(x) is int and 0<=x<bound,label+" is outside its fixed wire")
    return x

@dataclass(frozen=True)
class LaneId:
    origin:int
    source_bank:int
    receiver:int
    receiver_bank:int

class Work:
    def __init__(self,capacity,stock=0):
        self.capacity=F(capacity);self.stock=F(stock)
        need(0<=self.stock<=self.capacity,"Work exceeds actual capacity")
        self.received=F(0);self.spent=F(0);self.heat=F(0)
    def debit(self,value):
        value=F(value);need(value>=0,"Negative work")
        if self.stock<value:return False
        self.stock-=value;self.spent+=value
        return True
    def charge(self,dt,payer):
        # Independent capped input, efficiency1/2; no fresh stock on reset.
        amount=min(self.capacity-self.stock,self.capacity*F(dt)/RESET_REFILL,payer.stock/2)
        need(amount>=0 and payer.debit(2*amount),"Charge not supplied")
        self.stock+=amount;self.received+=amount;self.heat+=amount
        return amount
    def dump(self,dt):
        loss=min(max(F(0),self.stock-F(1,2)),self.capacity*F(dt)/DUMP_TIME)
        self.stock-=loss;self.spent+=loss;self.heat+=loss
        return loss

class SourceWork(Work):
    def __init__(self,origin,capacity,stock):
        self._origin=origin
        super().__init__(capacity,stock)
    @property
    def origin(self):return self._origin

@dataclass
class Claim:
    destination:object
    payload:object
    live:bool=True
    def dispatch(self,callback):
        if not self.live:return False
        self.live=False  # Consume before external effects or callback reentry.
        callback(self.destination,self.payload)
        return True
    def retire(self):
        self.live=False

class DataSlot:
    """Existing4096 cell, with a new explicit consume-before-callback ordering."""
    def __init__(self,body,stock=4096):
        self.body=body;self.cell=Work(4096,stock);self.claim=None
        self.admission=True;self.output=True;self.reset=False;self.progress_work=F(0)
    def offer(self,payload):
        if not self.admission:return "cut"
        if self.claim is not None and self.claim.live:return "busy"
        if self.cell.stock<4096:return "unfunded"
        self.claim=Claim(self.body,payload);self.progress_work=F(0);return "accepted"
    def complete(self,callback,claim):
        if claim is not self.claim:return False
        if claim is None or not claim.live or not self.output:return False
        if not self.cell.debit(4096-self.progress_work):return False
        self.progress_work=F(4096)
        return claim.dispatch(callback)
    def mask(self):
        self.admission=False;self.output=False
    def abort_after_cut(self):
        need(not self.admission and not self.output,"Data abort lacks actual cut")
        if self.claim is not None:self.claim.retire()
        self.reset=True
    def refill_on_actual_bank_entry(self,payer):
        # Existing E-funded4096/2^-30 recharge supplier; source-row OPEN alone
        # never calls this physical source-bank entry operation.
        need(self.reset,"No formed slot control state")
        amount=self.cell.capacity-self.cell.stock
        if not payer.debit(amount):return False
        self.cell.stock+=amount;self.cell.received+=amount
        self.claim=None;self.admission=True;self.output=True;self.reset=False
        return True

class WireChild:
    """Already emitted data: fixed destination and independently retained work."""
    def __init__(self,destination,payload,energy):
        self.claim=Claim(destination,payload);self.initial=F(energy)
        self.stock=F(energy);self.spent=F(0);self.elapsed=F(0)
    def advance(self,dt,callback):
        end=min(WIRE_DELAY,self.elapsed+F(dt))
        used=self.initial*(end-self.elapsed)/WIRE_DELAY
        self.stock-=used;self.spent+=used;self.elapsed=end
        if end==WIRE_DELAY:self.claim.dispatch(callback)

class SharedCapture:
    """One existing raw capture per origin/receiver-bank/kind, shared by b_o.

    Source-row reset sets its clock-enable, preserving the committed snapshot
    and every real pending descriptor. The existing new-read settlement leaf
    does the bank/key/control overwrite; reset does not interrupt the sibling.
    """
    def __init__(self,owner,kind,payer):
        need(payer.origin==owner[0],"Raw capture changed its funding origin")
        self.owner=owner;self.kind=kind;self.payer=payer;self.cell=Work(1024);self.clock_enabled=True
        self.control_dirty=False;self.snapshot=MASK;self.pending=None
        self.normalizations=0
    def set_clock_one(self):
        self.clock_enabled=True
    def begin(self,lane,key):
        if not self.clock_enabled:return "stopped"
        # This is PORT-SOURCE:118's priced old-phase/new-request leaf, not an
        # assertion that receiving a publication resets a capture controller.
        if self.pending is not None and self.pending.live:self.finish(self.pending)
        self.control_dirty=False;self.normalizations+=1
        needed=self.cell.capacity-self.cell.stock
        if not self.payer.debit(2*needed):return "unfunded"
        self.cell.stock+=needed;self.cell.received+=needed;self.cell.heat+=needed
        self.pending=Claim((lane,key),None);return "captured"
    def finish(self,claim):
        if claim is not self.pending or not claim.live:return self.snapshot
        def take(destination,_):
            lane,key=destination
            if not self.control_dirty and self.cell.stock==1024:self.snapshot=lane.read(key)
        claim.dispatch(take)
        self.cell.debit(self.cell.stock)
        self.pending=None
        return self.snapshot
    def sample(self,lane,key):
        if self.begin(lane,key)!="captured":return self.snapshot
        return self.finish(self.pending)

class Record:
    """Committed data remain readable during staged receipt/tick operations."""
    ENABLE,MASKED,BUSY,TICK_VALID,RECEIPT_VALID=range(5)
    def __init__(self,lane,key,lifetime,source_key,role):
        self.lane=lane;self.key=key;self.lifetime=lifetime
        self.width=lifetime.bit_length();self.cap=(1<<self.width)-1
        self.source_key=source_key;self.role=role
        self.control=[0]*REC_BITS;self.control[self.ENABLE]=1
        self.value=MASK;self.staged=MASK
        self.claim=None;self.queued_tick=False
    @property
    def queued_tick(self):return bool(self.control[32])
    @queued_tick.setter
    def queued_tick(self,value):self.control[32]=int(value)
    @property
    def ttl(self):return sum(self.control[5+j]<<j for j in range(self.width))
    def set_ttl(self,value):
        nat(value,1024,"countdown")
        for j in range(10):self.control[5+j]=((value>>j)&1) if j<self.width else 0
    def readable(self):
        return self.value if not self.lane.masked and not self.control[self.MASKED] and self.ttl else MASK
    def start_tick(self):
        if not self.lane.write_gate or not self.control[self.ENABLE]:return "stopped"
        if self.control[self.BUSY]:
            self.queued_tick=True;return "busy"
        if not self.lane.payer.debit(32):return "unfunded"
        self.control[self.BUSY]=self.control[self.TICK_VALID]=1
        self.claim=Claim(self,max(self.ttl-1,0));return "started"
    def stage_receipt(self,value):
        nat(value,1<<256,"receipt")
        if not self.lane.ingress:return "masked"
        if self.control[self.RECEIPT_VALID]:return "full"
        if not self.lane.payer.debit(512):return "unfunded"
        self.staged=value;self.control[self.RECEIPT_VALID]=1
        return "staged"
    def service(self):
        if not self.lane.write_gate or not self.control[self.ENABLE]:return "stopped"
        if self.control[self.BUSY]:
            if self.claim is None or not self.claim.live or not self.control[self.TICK_VALID]:return "stale-busy"
            if not self.lane.payer.debit(TICK_WORK-32):return "unfunded"
            token=self.claim
            token.dispatch(lambda target,value:target.set_ttl(value))
            self.claim=None;self.control[self.BUSY]=self.control[self.TICK_VALID]=0
            return "tick"
        if self.control[self.RECEIPT_VALID]:
            if not self.lane.payer.debit(1536):return "unfunded"
            # Atomic local payload/countdown commit AFTER any older tick.
            self.value=self.staged;self.set_ttl(self.lifetime)
            self.control[self.RECEIPT_VALID]=0
            return "receipt"
        if self.queued_tick:
            self.queued_tick=False
            return self.start_tick()
        return "idle"
    def clear_bit(self,index):
        # Actual64-bit reset stencil. The selected lane's hard mask/write
        # inhibition precede it; already committed data are not erased.
        self.control[index]=int(index==self.ENABLE)
        if index==self.TICK_VALID:
            if self.claim is not None:self.claim.retire()
            self.claim=None
    def corrupt(self,value=0):
        self.value=value;self.control[:]=[1]*REC_BITS
        self.control[self.ENABLE]=0;self.control[self.MASKED]=0
        self.set_ttl(self.cap)
        self.staged=value
        if self.claim is not None:self.claim.payload=self.cap
    def prepared(self):
        desired=[int(i==self.ENABLE) for i in range(REC_BITS)]
        return self.control==desired and self.claim is None and not self.queued_tick

class SymbolFIFO:
    """Fixed-capacity native queue; data never choose a physical lane identity."""
    def __init__(self,control):
        self.control=control;self.values=[0]*512
    def number(self,start,width):
        return sum(self.control[start+j]<<j for j in range(width))
    def set_number(self,start,width,value):
        for j in range(width):self.control[start+j]=(value>>j)&1
    @property
    def enabled(self):return bool(self.control[19]) and not self.control[20]
    def offer(self,symbol):
        nat(symbol,1<<96,"raw symbol")
        if not self.enabled:return "stopped"
        head=self.number(0,9);count=self.number(9,10)
        if count>=512:return "full"
        at=(head+count)%512;self.values[at]=symbol
        self.control[64+at]=1;self.set_number(9,10,count+1)
        return "accepted"
    def pop(self):
        if not self.enabled:return None
        head=self.number(0,9);count=self.number(9,10)
        if not 0<count<=512:return None
        value=self.values[head];self.control[64+head]=0
        self.set_number(0,9,(head+1)%512);self.set_number(9,10,count-1)
        return value

def symbols(key,value,kind=1):
    nat(key,2048,"source key");nat(value,1<<256,"payload");nat(kind,4,"kind")
    return tuple(((value>>(64*i))&((1<<64)-1))|(key<<64)|(i<<75)|(kind<<77) for i in range(4))

class ReassertingControlLine(cam.ControlLine):
    """The unchanged paid pipeline, retaining level-action events when steady."""
    def flow(self,dt,code,consume,arrive):
        dt=F(dt);need(dt>=0,"Negative control interval")
        while dt:
            steady=(all(v==code for v in self.words) and all(self.valid)
                and all(q is None or q==(code,True) for q in self.snapshots)
                and all(r<p for r,p in zip(self.remaining,self.phases)))
            if steady:
                next_commit=(self.remaining[7] if self.snapshots[7] is not None
                             else self.phases[7]+cam.CONTROL_STEP)
                step=min(dt,next_commit)
                # Cam's exact constant-state formula retains all pending
                # snapshots and phases. Its omitted output event is restored.
                super().flow(step,code,consume,arrive)
                dt-=step
                if step==next_commit:arrive(code)
            else:
                event=min(self.phases+[r for q,r in zip(self.snapshots,self.remaining) if q is not None])
                step=min(dt,event)
                super().flow(step,code,consume,arrive)
                dt-=step

class RawLane:
    def __init__(self,population,identity,payer,captures=None,control_powered=True):
        need(isinstance(identity,LaneId),"Missing physical lane identity")
        for bank in (identity.source_bank,identity.receiver_bank):nat(bank,2,"bank")
        need(identity.receiver in incidence.neighbors(population,identity.origin),"Nonlocal lane")
        need(isinstance(payer,SourceWork) and payer.origin==identity.origin,
             "Lane cannot borrow another source's U")
        self.identity=identity;self.population=population;self.payer=payer
        self.decoder=legacy.ArrivalDecoder(population,identity.receiver,identity.origin)
        self.records={}
        for source_key in range(KEYS):
            destination=self.decoder.decode(source_key)
            if destination is not None:
                role,key=destination
                need(key not in self.records,"Physical key aliases")
                self.records[key]=Record(self,key,8 if key<2 else 512,source_key,role)
        self.ordered=tuple(self.records[k] for k in sorted(self.records))
        self.rx=[0]*RX_BITS;self.rx[19]=1
        self.decode_control=[0]*DEC_BITS;self.decode_control[1]=1
        self.queue=SymbolFIFO(self.rx)
        self.masked=False;self.ingress=True;self.write_gate=True
        self.mode=OPEN;self.reset_control=[0]*ENGINE_BITS
        self.reset_work=Work(RESET_CAP);self.setup_paid=False;self.cursor=0
        self.clear_phase=F(0);self.time=F(0)
        self.servicing=False;self.drop_count=0
        self.frame_words=[0]*4;self.frame_claim=None
        self.captures=captures if captures is not None else {
            role:SharedCapture((identity.origin,identity.receiver,identity.receiver_bank),role,payer)
            for role in ("primary","auxiliary")}
        self.line=ReassertingControlLine(words=[OPEN]*8,valid=[True]*8)
        self.mode_trace=[];self.mode_applications=0;self.wire_children=[]
        need(type(control_powered) is bool,"Control power is a physical Boolean")
        self.control_powered=control_powered
    @property
    def cursor(self):
        return sum(self.reset_control[j]<<j for j in range(18))
    @cursor.setter
    def cursor(self,value):
        nat(value,1<<18,"reset cursor")
        for j in range(18):self.reset_control[j]=(value>>j)&1
    @property
    def setup_paid(self):return bool(self.reset_control[18])
    @setup_paid.setter
    def setup_paid(self,value):self.reset_control[18]=int(value)
    def engine_get(self,start,width):
        return sum(self.reset_control[start+j]<<j for j in range(width))
    def engine_set(self,start,width,value):
        nat(value,1<<width,"reset engine field")
        for j in range(width):self.reset_control[start+j]=(value>>j)&1
    @property
    def setup_remaining(self):return self.engine_get(19,18)
    @setup_remaining.setter
    def setup_remaining(self,v):self.engine_set(19,18,v)
    @property
    def bit_pending(self):return bool(self.reset_control[37])
    @bit_pending.setter
    def bit_pending(self,v):self.reset_control[37]=int(v)
    @property
    def bit_address(self):return self.engine_get(38,18)
    @bit_address.setter
    def bit_address(self,v):self.engine_set(38,18,v)
    @property
    def tail_remaining(self):return self.engine_get(56,11)
    @tail_remaining.setter
    def tail_remaining(self,v):self.engine_set(56,11,v)
    def source_keys(self):return tuple(r.source_key for r in self.ordered)
    def parser_number(self,start,width):return self.queue.number(start,width)
    def parser_set(self,start,width,value):self.queue.set_number(start,width,value)
    @property
    def bitmap_bits(self):return len(self.ordered)*REC_BITS+RX_BITS+DEC_BITS
    @property
    def reset_price(self):return 2*self.bitmap_bits+self.bitmap_bits//2+1281
    def read(self,key):
        record=self.records.get(key)
        return MASK if record is None else record.readable()
    def private_capture(self,key,role):
        return self.captures[role].sample(self,key)
    def receive_symbol(self,value):
        if not self.payer.debit(8):return "unfunded"
        if not self.ingress:self.drop_count+=1;return "masked"
        return self.queue.offer(value)
    def process_one(self):
        if self.servicing or self.rx[20]:return "busy"
        if not self.write_gate or not self.decode_control[1] or self.decode_control[0]:return "stopped"
        if not self.payer.debit(64):return "unfunded"
        value=self.queue.pop()
        if value is None:return "empty"
        self.servicing=True
        try:
            key=(value>>64)&2047;part=(value>>75)&3;kind=(value>>77)&3
            phase=self.parser_number(21,3);old_key=self.parser_number(24,11)
            if value>>79 or kind!=1:
                self.parser_set(21,3,0);return "malformed"
            chunk=value&((1<<64)-1)
            if part==0:
                self.frame_words[0]=chunk;self.parser_set(24,11,key);self.parser_set(21,3,1)
                return "start"
            if phase!=part or old_key!=key:
                self.parser_set(21,3,0);return "bad-order"
            self.frame_words[part]=chunk
            if part!=3:
                self.parser_set(21,3,part+1);return "partial"
            self.parser_set(21,3,0)  # Consume the complete prefix BEFORE dispatch.
            payload=sum(v<<(64*i) for i,v in enumerate(self.frame_words))
            if not self.payer.debit(11584):return "unfunded"
            self.frame_claim=Claim((self.identity,key),payload)
            token=self.frame_claim
            destination=self.decoder.decode(key)
            def deliver(_bound,val):
                if destination is not None:
                    role,k=destination
                    self.records[k].stage_receipt(val)
            token.dispatch(deliver)
            return "frame" if destination is not None else "uninstalled"
        finally:self.servicing=False
    def offer_frame(self,key,value,kind=1):
        results=[]
        for symbol in symbols(key,value,kind):
            results.append(self.receive_symbol(symbol));results.append(self.process_one())
        for record in self.ordered:
            for _ in range(3):
                if record.service() in ("idle","stopped","stale-busy","unfunded"):break
        return results
    def poison(self,include_shared=True):
        for record in self.ordered:record.corrupt()
        self.rx[:]=[1]*RX_BITS;self.rx[19]=0
        self.decode_control[:]=[1]*DEC_BITS;self.decode_control[1]=0
        if include_shared:
            for capture in self.captures.values():
                capture.clock_enabled=False;capture.control_dirty=True;capture.snapshot=0
        self.reset_control[:]=[1]*ENGINE_BITS
        self.cursor=(1<<18)-1;self.setup_paid=True
    def apply_mode(self,mode):
        nat(mode,16,"control mode")
        if not self.payer.debit(256):return "control-unfunded"
        if mode!=self.mode or not self.mode_trace:self.mode_trace.append((mode,self.time))
        self.mode=mode;self.mode_applications+=1
        if mode in (MASK_MODE,CHARGE,DUMP,CLEAR):
            self.masked=True;self.ingress=False;self.write_gate=False
        if mode==MASK_MODE:
            # Maintained physical priority reset of the reset engine itself.
            self.reset_control[:]=[0]*ENGINE_BITS
            self.cursor=0;self.setup_paid=False;self.clear_phase=F(0)
            for capture in self.captures.values():capture.set_clock_one()
        elif mode==OPEN:
            # No completion/certificate/image test: failed traversals can open.
            self.masked=False;self.ingress=True;self.write_gate=True
        return "applied"
    def clear_one(self,index):
        count=len(self.ordered)*REC_BITS
        if index<count:
            record,bit=divmod(index,REC_BITS);self.ordered[record].clear_bit(bit)
        elif index<count+RX_BITS:
            bit=index-count;self.rx[bit]=int(bit==19)
            if bit==20:self.servicing=False
            if bit==35 and self.frame_claim is not None:self.frame_claim.retire()
        else:
            bit=index-count-RX_BITS;self.decode_control[bit]=int(bit==1)
    def consume(self,dt):
        dt=F(dt);need(dt>=0,"Negative local time")
        for child in self.wire_children:
            child.advance(dt,lambda destination,payload:destination.offer_frame(*payload))
        if self.mode==CHARGE:
            self.reset_work.charge(dt,self.payer)
        elif self.mode==CLEAR:
            if not self.setup_paid:
                # A fixed finite setup, followed by two actual native work
                # ticks per bit and a separately paid terminal suffix.
                self.setup_remaining=self.bitmap_bits//2+257
                self.tail_remaining=1024;self.setup_paid=True
            total=self.clear_phase+dt*CLEAR_RATE
            opportunities=int(total);self.clear_phase=total-opportunities
            take=min(opportunities,self.setup_remaining,int(self.reset_work.stock))
            if take:
                self.reset_work.debit(take);self.setup_remaining-=take;opportunities-=take
            if self.setup_remaining==0:
                while opportunities and self.cursor<self.bitmap_bits:
                    if not self.reset_work.debit(1):break
                    opportunities-=1
                    if not self.bit_pending:
                        self.bit_address=self.cursor;self.bit_pending=True
                    else:
                        if self.bit_address<self.bitmap_bits:self.clear_one(self.bit_address)
                        self.cursor=min(self.bit_address+1,(1<<18)-1);self.bit_pending=False
                if self.cursor==self.bitmap_bits and not self.bit_pending:
                    take=min(opportunities,self.tail_remaining,int(self.reset_work.stock))
                    if take:self.reset_work.debit(take);self.tail_remaining-=take
            # Missed native opportunities are discarded; only oscillator phase
            # remains. Recharge cannot replay a long unfunded past interval.
        self.time+=dt
    def hold(self,mode,dt):
        if self.control_powered:self.line.flow(F(dt),mode,self.consume,self.apply_mode)
        else:self.consume(F(dt))
    def fresh_traversal(self,speed=VMAX):
        need(F(0)<speed<=VMAX,"Invalid actual clamp speed")
        for mode,left,right,_native in MODES:self.hold(mode,(right-left)/speed)
        self.hold(OPEN,CONTROL_DELAY)
    def certificate(self):
        return (not self.masked and self.ingress and self.write_gate
            and self.cursor==self.bitmap_bits and self.setup_remaining==0
            and not self.bit_pending and self.tail_remaining==0
            and all(r.prepared() for r in self.ordered)
            and self.rx==[int(i==19) for i in range(RX_BITS)]
            and self.decode_control==[int(i==1) for i in range(DEC_BITS)])

class LocalSourceBank:
    """Only the cold source bank's DATA/ADC controls, never its sibling."""
    BITS=80*2048+4096+256
    def __init__(self,origin,bank,payer):
        need(isinstance(payer,SourceWork) and payer.origin==origin,"Local reset changed its U owner")
        self.origin=origin;self.bank=bank;self.payer=payer
        self.reset_work=Work(RESET_CAP);self.control=[1]*self.BITS
        self.admission=False;self.emit_gate=False;self.cursor=0
        self.slots=[DataSlot((origin,bank,"DATA",i),4096) for i in range(80*129)]
        self.adc=DataSlot((origin,bank,"ADC"),4096)
        self.independent_children=[];self.old_wire=[]
    def cold_cut(self):
        self.admission=False;self.emit_gate=False
        for slot in self.slots+[self.adc]:slot.mask()
    def reform(self):
        self.cold_cut()
        if not self.payer.debit(256):return "control-unfunded"
        self.cursor=0
        self.reset_work.charge(RESET_REFILL,self.payer)
        setup=self.BITS//2+1281
        if not self.reset_work.debit(setup):return "unfunded"
        for slot in self.slots+[self.adc]:
            if not self.reset_work.debit(8):return "partial-abort"
            slot.abort_after_cut();slot.cell.dump(DUMP_TIME)
        for index in range(self.BITS):
            if not self.reset_work.debit(2):return "partial"
            self.control[index]=0;self.cursor+=1
        return "formed-unpowered"
    def rearm(self):
        # A separate ACT/E/parent-entry supplier must supply this event.
        # No test of C=P or a successful-reset flag is inserted.
        self.admission=True;self.emit_gate=True

def support(population,receiver,providers,event):
    incidence.check_population(population);nat(receiver,population,"receiver")
    need(type(providers) is tuple and len(providers)==15 and len(set(providers))==15,
         "Consumer group is not15 distinct physical origins")
    actual=[incidence.plant_group(population,receiver,k) for k in (0,1)]
    actual += [tuple(o for o,_ in incidence.maintenance_group(population,receiver,k)[1]) for k in range(40)]
    need(providers in actual,"Caller changed the actual primary/group order")
    need(type(event) is tuple and len(event)>=2,"Untyped incident")
    kind,*args=event
    if kind in ("source","reset-root","primary","pair","execution"):
        need(len(args)==1,"Incident arity")
        nat(args[0],population,"incident host")
    elif kind=="lane":
        need(len(args)==2,"Incident arity")
        nat(args[0],population,"incident receiver");nat(args[1],population,"incident source")
        need(args[1] in incidence.neighbors(population,args[0]),"Uninstalled lane incident")
    if kind=="execution":
        origin=args[0]
        return {0} if origin==receiver else {providers.index(origin)} if origin in providers else set()
    if kind in ("source","reset-root"):
        origin=args[0];return {providers.index(origin)} if origin in providers else set()
    if kind=="primary":return {0} if args[0]==receiver else set()
    if kind=="lane":
        r,origin=args
        return {providers.index(origin)} if r==receiver and origin in providers else set()
    if kind=="pair":
        r=args[0]
        return {providers.index(o) for o in islands.installed_pair(population,r) if o in providers} if r==receiver else set()
    raise ValueError("Unmodeled fault capability")


def record_checks():
    payer=SourceWork(2,1<<50,1<<50);population=12*(6+2**98)+2
    lane=RawLane(population,LaneId(2,1,0,1),payer)
    key=next(k for k in lane.records if k<2);record=lane.records[key]
    record.value=1200;record.set_ttl(8)
    need(record.start_tick()=="started","Tick did not capture")
    old=record.claim
    need(record.stage_receipt(500)=="staged" and record.readable()==1200,
         "Staging erased the continuously readable committed record")
    need(record.service()=="tick" and record.ttl==7,"Older decrement did not retire first")
    need(record.service()=="receipt" and record.ttl==8 and record.readable()==500,
         "Atomic receipt did not follow the older tick")
    need(not old.dispatch(lambda target,value:target.set_ttl(value)),"Old tick overwrote a new receipt")
    # A new payload is not a stopped-clock/control repair.
    record.corrupt(0);lane.offer_frame(record.source_key,900)
    need(record.readable()==0 and not record.control[record.ENABLE],"Payload repaired a corrupt native clock")
    record.control[record.ENABLE]=1
    need(record.service()=="stale-busy","A new receipt repaired stale busy metadata")
    record.control[record.BUSY]=record.control[record.TICK_VALID]=0
    record.control[record.MASKED]=1
    record.service()
    need(record.readable()==MASK,"Payload silently reopened a stored mask")
    # Genuine receipts every2q still fail under the discarded stale-writeback rule.
    bad=8;wrong=[]
    for tick in range(1,11):
        stale=max(0,bad-1)
        if tick%2==0:bad=8
        bad=stale;wrong.append(bad)
    need(wrong[7:]==[0,0,0],"Stale decrement countercase disappeared")
    return dict(continuous_old_record_during_receipt=True,old_tick_consumed_before_receipt=True,
        stale_tick_replay_rejected=True,payload_does_not_repair_clock=True,
        discarded_stale_writeback_trace=wrong)

def slot_checks():
    slot=DataSlot(("source",0,"DATA",0));slot.offer((1,500))
    effects=[];current=slot.claim
    def callback(destination,payload):
        effects.append((destination,payload))
        need(not slot.complete(callback,current),"An old completion reentered")
    need(slot.complete(callback,current) and len(effects)==1 and slot.cell.spent==4096,
         "Once-only paid callback failed")
    slot.mask();slot.abort_after_cut();payer=Work(4096,4096)
    need(slot.refill_on_actual_bank_entry(payer),"Actual slot refill failed")
    slot.offer((1,900));new=slot.claim
    need(not slot.complete(callback,current) and new.live,"Old completion stole a reused slot")
    need(slot.complete(lambda d,v:None,new),"Fresh physical claim cannot complete")
    # Retain the original API countercase without using it as the new source.
    module,_=legacy.module_at(legacy.BASE,"local-control/port_model.py","_input_old_ports")
    reservoir=module.Reservoir.filled(4096);old=module.Slot(reservoir);old.recharge(module.DELTA)
    old.offer(0,("old-fixed-destination",),1);old_effects=[]
    def recurse(value):
        old_effects.append(value)
        if len(old_effects)==1:old.elapse(1,recurse)
    old.elapse(1,recurse)
    need(len(old_effects)==2 and old.paid==1,"Expected callback-order API countercase changed")
    # A wire child's stock is transferred from an existing source data cell.
    source=Work(4096,4096);need(source.debit(4096),"Wire child unfunded")
    wire=WireChild(("receiver",1),(0,123),4096);received=[]
    # A source reset does not cancel this child beyond its source cut.
    wire.advance(WIRE_DELAY/2,lambda d,p:received.append((d,p)))
    need(wire.stock==2048 and not received,"Wire energy was erased on reset")
    wire.advance(WIRE_DELAY/2,lambda d,p:received.append((d,p)))
    wire.advance(100,lambda d,p:received.append((d,p)))
    need(wire.stock==0 and wire.spent==4096 and len(received)==1,"Wire child copied or replayed work")
    return dict(new_completion_effects=len(effects),old_completion_after_reuse_rejected=True,old_API_reentrant_effects=len(old_effects),
        old_API_scope="Python callback countercase, not a claimed admitted physical history",
        independent_wire_child_preserved=True,wire_remaining_after_half=2048,wire_spent=wire.spent)

def reset_checks():
    population=12*(6+2**98)+2;payer=SourceWork(2,1<<60,1<<60)
    shared={role:SharedCapture((2,0,1),role,payer) for role in ("primary","auxiliary")}
    cold=RawLane(population,LaneId(2,0,0,1),payer,shared)
    serving=RawLane(population,LaneId(2,1,0,1),payer,shared)
    key=next(k for k in serving.records if k<2);r=serving.records[key]
    r.value=500;r.set_ttl(8)
    capture=shared[r.role];capture.begin(serving,key);pending=capture.pending
    before=(r.value,r.ttl,tuple(r.control))
    cold.poison(include_shared=False)  # Noninterference probe: serving capture remains conforming.
    # Restore only the serving record for the nominal noninterference probe;
    # its capture descriptor and snapshot remain the same physical objects.
    r.control[:]=[0]*REC_BITS;r.control[r.ENABLE]=1;r.set_ttl(8)
    capture.pending=pending;capture.clock_enabled=True
    before=(r.value,r.ttl,tuple(r.control))
    cold.fresh_traversal()
    need(cold.certificate(),"Fresh source-row traversal failed")
    full_reset_spent=cold.reset_work.spent
    need(before==(r.value,r.ttl,tuple(r.control)) and capture.pending is pending,
         "Cold row reset altered serving-bank state or its capture")
    need(capture.finish(pending)==500,"Shared capture reset interrupted the serving read")
    need(all(x.readable()==MASK for x in cold.ordered),"Reset invented genuine input")
    target=cold.records[key];need(cold.offer_frame(target.source_key,500)[-1]=="frame","Fresh frame failed")
    need(target.readable()==500,"Real post-reset receipt did not become readable")
    target.start_tick();stale=target.claim
    cold.apply_mode(MASK_MODE)
    # This short probe executes the actual reset stencil after write inhibition,
    # retaining the old claim for a later replay challenge.
    for bit in range(REC_BITS):
        need(cold.reset_work.debit(2),"Single-record reset probe unfunded")
        target.clear_bit(bit)
    cold.apply_mode(OPEN);cold.offer_frame(target.source_key,500)
    target.start_tick();fresh=target.claim
    need(not stale.dispatch(lambda dest,value:dest.set_ttl(value)) and fresh.live,
         "Old decrement acquired a new receipt/tick incarnation")
    target.service()
    capture=cold.captures[target.role]
    capture.clock_enabled=False;capture.control_dirty=True;capture.snapshot=0
    cold.offer_frame(target.source_key,500)
    need(capture.sample(cold,key)==0,"Payload silently restarted shared capture")
    # The physical MASK set-one operation preserves a pending descriptor; the
    # following actual new read performs the imported control normalization.
    cold.apply_mode(MASK_MODE);cold.apply_mode(OPEN)
    need(capture.sample(cold,key)==500,"Clock restart/new-read entry did not restore capture")
    # Later forged values are accepted as raw input, not recognized as false.
    cold.offer_frame(target.source_key,0);need(target.readable()==0,"A truth oracle rejected raw data")
    # Header kind cannot invoke the separate control plane or change identity.
    state=(cold.mode,cold.masked,cold.identity)
    cold.offer_frame(target.source_key,MASK,kind=2)
    need(state==(cold.mode,cold.masked,cold.identity),"Data acquired reset authority")
    # A partial traversal can unmask still-dirty state; no READY predicate saves it.
    partial=RawLane(population,LaneId(2,0,0,0),payer)
    partial.poison();partial.apply_mode(OPEN)
    need(not partial.certificate() and any(x.readable()==0 for x in partial.ordered),
         "Opening supplied successful reset by definition")
    # A held MASK must act even when all pipeline words already equal it.
    held=RawLane(population,LaneId(2,0,0,0),payer)
    held.poison();held.line=ReassertingControlLine(words=[MASK_MODE]*8,valid=[True]*8)
    held.hold(MASK_MODE,F(1,2))
    need(held.cursor==0 and not held.setup_paid and held.masked,
         "Steady MASK skipped real controller initialization")
    clockless=RawLane(population,LaneId(2,0,0,0),payer,control_powered=False)
    clockless.poison();clockless.fresh_traversal()
    need(not clockless.certificate() and clockless.line.edges==0,
         "Unpowered control path produced a fresh row")
    # Actual clear progress and expenditure survive a missing refill.
    starved=RawLane(population,LaneId(2,0,0,0),payer)
    starved.poison();starved.apply_mode(MASK_MODE);starved.apply_mode(CLEAR)
    starved.consume(10);starved.apply_mode(OPEN)
    need(starved.cursor==0 and not starved.certificate(),"Unfunded reset cleared metadata")
    local=LocalSourceBank(2,0,payer)
    sibling=DataSlot((2,1,"WORLD",0));sibling.offer((60,60))
    local.independent_children.append(sibling)
    sibling_state=(sibling.claim,sibling.cell.stock,sibling.claim.live)
    need(local.reform()=="formed-unpowered" and local.cursor==local.BITS,"Local TX/ADC reset incomplete")
    need(sibling_state==(sibling.claim,sibling.cell.stock,sibling.claim.live),
         "Cold source reset erased sibling/independent children")
    need(not local.admission and not local.emit_gate,"Source-row OPEN rearmed source execution")
    return dict(actual_lane=cold.identity.__dict__,selected_records=len(cold.records),
        literal_reset_bits=cold.bitmap_bits,literal_reset_work=full_reset_spent,additional_probe_reset_work=cold.reset_work.spent-full_reset_spent,
        reset_recharge=cold.reset_work.received,remaining_reset_stock=cold.reset_work.stock,
        fresh_time=cold.time,source_role_mode_trace=cold.mode_trace,
        actual_mode_applications=cold.mode_applications,
        control_transport_offered_work_upper=cold.line.offered_work_upper,
        steady_MASK_reassertion_checked=True,unpowered_control_has_no_fresh_row=True,
        sibling_record_unchanged=True,pending_sibling_capture_preserved=True,
        noninterference_probe_is_a_state_commutation_check_not_a_frozen_time_trace=True,
        old_tick_after_reset_and_reuse_rejected=True,
        payload_does_not_restart_capture=True,physical_set_one_plus_new_read_restores_capture=True,
        reset_gives_only_unavailable_until_receipt=True,raw_forgery_not_rejected=True,
        data_cannot_invoke_control=True,partial_open_can_remain_bad=True,unfunded_reset_waits=True,
        local_TX_ADC_bits=local.BITS,local_TX_ADC_reset_work=local.reset_work.spent,
        local_data_capsules=len(local.slots)+1,
        old_data_dump_heat=sum(x.cell.heat for x in local.slots+[local.adc]),
        independent_children_retained=True)

def control_checks():
    # Independent event-by-event continuation without the constant-word skip.
    # This checks the added level reassertions, including old pending snapshots.
    rng=random.Random(20261114)
    def reference(line,dt,code):
        out=[];now=F(0);dt=F(dt)
        while dt:
            event=min(line.phases+[r for q,r in zip(line.snapshots,line.remaining) if q is not None])
            step=min(dt,event);dt-=step;now+=step
            line.phases=[p-step for p in line.phases]
            line.remaining=[max(F(0),r-step) for r in line.remaining]
            for i in range(8):
                if line.snapshots[i] is not None and line.remaining[i]==0:
                    val=line.commit(i)
                    if i==7:out.append((now,val))
            for i in range(8):
                if line.phases[i]==0:line.capture(i,code);line.phases[i]=F(1,8)
        return out
    for case in range(128):
        code=rng.randrange(5)
        words=[code]*8 if case%2 else [rng.randrange(5) for _ in range(8)]
        a=ReassertingControlLine(words=words,valid=[True]*8)
        a.phases=[F(rng.randrange(1,1025),8192) for _ in range(8)]
        for i in range(8):
            if rng.randrange(2):
                a.snapshots[i]=(code,True) if case%2 else (rng.randrange(5),True)
                a.remaining[i]=F(rng.randrange(1,129),1048576)
        b=cam.ControlLine(words=a.words,valid=a.valid,snapshots=a.snapshots,remaining=a.remaining)
        b.phases=list(a.phases)
        duration=F(rng.randrange(1,2000),1000);events=[];now=[F(0)]
        a.flow(duration,code,lambda dt:now.__setitem__(0,now[0]+dt),
               lambda val:events.append((now[0],val)))
        need(events==reference(b,duration,code),"Repeated held control application differs")
        need((a.words,a.valid,a.snapshots,a.remaining,a.phases,a.edges)==
             (b.words,b.valid,b.snapshots,b.remaining,b.phases,b.edges),
             "Control adapter changed retained phase/snapshot state")
    return dict(independent_event_traces=128,level_actions_reassert_on_every_receiver_commit=True,
                old_pending_snapshots_and_independent_phase_checked=True)

def footprint_checks():
    population=12*(6+2**98)+2
    rows=[]
    for receiver in (0,1,population-1):
        groups=[incidence.plant_group(population,receiver,row) for row in (0,1)]
        groups += [tuple(o for o,_ in incidence.maintenance_group(population,receiver,t)[1]) for t in (0,19,20,39)]
        for providers in groups:
            for origin in incidence.neighbors(population,receiver):
                need(len(support(population,receiver,providers,("reset-root",origin)))<=1,
                     "Common source reset root crossed origins")
                need(len(support(population,receiver,providers,("lane",receiver,origin)))<=1,
                     "Lane state acquired another origin")
            pair=support(population,receiver,providers,("pair",receiver))
            need(len(pair)<=2,"Installed pair exceeds two origins")
            # One fixed pair and five singleton roots; repeated pair instances
            # do not acquire a new attacker-selected physical pair.
            chosen=[o for o in providers if providers.index(o) not in pair][:5]
            union=set(pair)
            for o in chosen:union|=support(population,receiver,providers,("reset-root",o))
            need(len(union)<=7,"Six-token support failed")
            rows.append(dict(receiver=str(receiver),pair_slots=sorted(pair),six_token_support=sorted(union)))
    providers=incidence.plant_group(population,0,0);rejected=0
    malformed=((population,0,providers[::-1],("source",providers[0])),
               (population,0,providers,("lane",0,population)),
               (population,0,providers,("source",0,1)),
               (population,0,providers,("pair",True)))
    for args in malformed:
        try:support(*args)
        except (ValueError,AssertionError):rejected+=1
        else:raise AssertionError("Malformed physical footprint accepted")
    try:RawLane(population,LaneId(2,0,0,1),SourceWork(3,1<<20,1<<20))
    except (ValueError,AssertionError):rejected+=1
    else:raise AssertionError("Cross-origin U borrowing accepted")
    return dict(contexts=rows,source_root_max_slots=1,local_fixed_pair_max_slots=2,
        malformed_identity_group_and_funding_cases_rejected=rejected,
        general_bound="k without a local pair; k-l+2 with l>=1 repeated occurrences of the one installed pair",
        primary_frame_is_union_of_origin_affine_cells=True,
        broader_lane_map_may_reach_that_origin_when_it_is_primary=True,
        this_expands_not_restricts_old_auxiliary_only_map=True,
        input_only_incidents_change_no_private_C_R_W=True,
        receiver_reset_root_not_installed=True,
        ancestry="raw clock debt at(r,o) requires actual source-o bank-row reformation; two-source pair requires each source's rows; no receiver-mechanics return is assumed")

def consumer_checks(isa,c,b):
    """Actual producer publications, framed lanes and intact compiled consumer."""
    population=12*(6+2**98)+2;receiver=0;rb=1
    providers=sorted(set(incidence.plant_group(population,receiver,0))|
                     set(incidence.plant_group(population,receiver,1)))
    lanes={};source_steps=0;payers={}
    for provider in providers:
        payers[provider]=SourceWork(provider,1<<60,1<<60)
        shared={role:SharedCapture((provider,receiver,rb),role,payers[provider]) for role in ("primary","auxiliary")}
        inactive=RawLane(population,LaneId(provider,0,receiver,rb),payers[provider],shared)
        inactive.masked=True;inactive.ingress=False;inactive.write_gate=False
        lanes[(provider,0)]=inactive
        lane=RawLane(population,LaneId(provider,1,receiver,rb),payers[provider],shared)
        ports=program.ports_class(isa)(c);value=(500,1000)[incidence.head_type(provider)]
        ports.fast[("head",0)]=value;ports.fast[("head",1)]=value
        m=program.call(isa,c,ports,"publish_plant",(),b["instruction_upper_bounds"]["publish_plant"]+10)
        source_steps+=m.steps;ports.elapse(2)
        client=2*incidence.neighbors(population,provider).index(receiver)+rb
        for _,kind,args,val in ports.delivered:
            if kind=="source_offer_fast" and args[0]==client:lane.offer_frame(args[1],val)
        lanes[(provider,1)]=lane
    Parent=program.ports_class(isa)
    class Inputs(Parent):
        def perform(self,name,args,machine):
            if name in ("fast_cmp","fast_equal","fast_range"):
                slot,bank,key,*bounds=args
                if not(0<=slot<15 and bank in (0,1) and 0<=key<2003 and key!=2):value=MASK
                else:
                    group=(incidence.plant_group(population,receiver,key) if key<2 else
                           tuple(o for o,_ in incidence.maintenance_group(population,receiver,(key-3)//50)[1]))
                    origin=group[slot];lane=lanes.get((origin,bank))
                    role="primary" if slot==0 else "auxiliary"
                    value=MASK if lane is None else lane.private_capture(key,role)
                if name=="fast_cmp":return int(value<=bounds[0])
                if name=="fast_equal":return int(value==bounds[0])
                return int(bounds[0]<=value<=bounds[1])
            return super().perform(name,args,machine)
    ports=Inputs(c);ports.fast[("head",0)]=500;ports.fast[("head",1)]=500
    m=program.initialized(isa,c);m.W[c.constants["ENTRY"]]=1;m.enter("frame")
    while not m.io_counts["world"] and m.steps<b["active_frame_upper"]:need(m.step(ports),"Input consumer stopped")
    need(m.C==c.image and ports.world_latch==(60,60),"Actual framed input did not reach WORLD")
    # Intact inference still consumes forged whole-primary input at a boundary.
    key=1;group=incidence.plant_group(population,receiver,1)
    for slot,origin in enumerate(group):
        lanes[(origin,1)].offer_frame(1,1000 if slot<8 else 999)
    def world_once():
        pp=Inputs(c);pp.fast[("head",0)]=pp.fast[("head",1)]=500
        mm=program.initialized(isa,c);mm.W[c.constants["ENTRY"]]=1;mm.enter("frame")
        while not mm.io_counts["world"]:need(mm.step(pp),"Intact inference stopped")
        need(mm.C==c.image and not mm.code_writes,"Input attack changed execution")
        return pp.world_latch
    before=world_once()
    lanes[(group[0],1)].records[1].value=999
    after=world_once()
    need(before==(60,60) and after==(60,59),"Primary frame is no longer genuinely consumed")
    need(len({id(payers[o]) for o in providers})==len(providers),"Source budgets were pooled")
    return dict(actual_producers=len(providers),distinct_source_U_ledgers=len(payers),source_bank=1,receiver_bank=rb,
        producer_instructions=source_steps,consumer_prefix_instructions=m.steps,
        actual_world=list(ports.world_latch),primary_before=list(before),primary_after=list(after),
        intact_receiver_C_R_W_not_corrupted=True,full_paced_frame_not_run=True,
        staged_records_and_clock_control_are_actual_input=True)

def resource_checks():
    cam_record=json.loads((HERE/"cam_reformation_results.json").read_text())["arithmetic"]
    field_record=json.loads((HERE/"threshold_field_source_results.json").read_text())["point"]
    legacy_record=json.loads((HERE/"legacy_realization_results.json").read_text())["inventory"]
    # Source inventory precedes initialization: initialization consumes this
    # resource result, so deriving it from an initialization report is circular.
    old=cam_record["resources"]
    lanes=2*40*2;records=320480;reset_cells=lanes+2
    new_stock=reset_cells*RESET_CAP
    # The192-bit pipelines and separate96-bit reset engines are new. Record
    # staging/controller bits fit each explicitly mapped old2048-bit unit.
    control_bits=cam.CONTROL_BITS*lanes+ENGINE_BITS*reset_cells
    record_bits=2*256+REC_BITS
    need(record_bits<2048,"Staged/committed record has no allocation")
    lane_max=KEYS*REC_BITS+RX_BITS+DEC_BITS
    lane_price=2*lane_max+lane_max//2+1281
    local_price=2*LocalSourceBank.BITS+LocalSourceBank.BITS//2+1281+8*(80*129+1)
    need(max(lane_price,local_price)<RESET_CAP,"Reset job cannot use its actual cell")
    need(max(lane_price,local_price)/F(CLEAR_RATE)<F(1,2),"Clear band understates complete work")
    for _mode,left,right,native in MODES:
        need((right-left)/VMAX>CONTROL_DELAY+native,"Physical mode overtakes its work")
    # New raw engines have explicit all-mode power ceilings, so corrupt native
    # control can spend work without relying on nominal packet/tick counts.
    native_rate=records*TICK_POWER+lanes*RX_POWER
    # A left-boundary tick AND a staged receipt can coexist. Do not price
    # the old receipt as if it were a128-work decrement.
    native_burst=2*records*(TICK_WORK+2048)+2*lanes*RX_WORK
    control_delivered_burst=4*cam.CONTROL_PRICE*lanes
    control_delivered_rate=2*cam.CONTROL_PRICE*lanes*cam.CONTROL_MAX
    action_burst=2*256*lanes;action_rate=256*lanes*cam.CONTROL_MAX
    reset_charge=2*reset_cells*RESET_CAP/RESET_REFILL
    holding=F(control_bits,1024)
    added_rate=2*(native_rate+control_delivered_rate+action_rate)+reset_charge+holding
    added_burst=2*(native_burst+control_delivered_burst+action_burst)
    new_U=F(old["unchanged_upstream_capacity"])-new_stock
    D=F(old["upstream_rate"])+added_rate;B=F(old["upstream_burst"])+added_burst
    reserve=new_U-B-2*D;supply=F(cam_record["resources"]["unchanged_supply_rate"])
    need(D<supply and reserve>added_burst+1,"Same supply/capacity cannot fund raw reset")
    physical_peak=(native_rate+2*lanes*cam.CONTROL_PRICE*2**20+
                   2*256*lanes*2**20+reset_cells*2**21+holding)
    combined=F(cam_record["resources"]["combined_native_peak"])+physical_peak
    need(41*combined<2**93 and 4*41*combined<2**94,"Added raw circuits exceed physical ratings")
    reaction=F(2*lanes+2)*cam.f.U_BIT/1000
    total_reaction=F(cam_record["resources"]["complete_joint_reaction"])+reaction
    need(total_reaction<F(81,250),"Additional reset/control reaction exceeds .324")
    pair=F(33,2**26);fmax=F(1163265,1048576)
    periods=dict(plant=2*fmax,maintenance=226*fmax)
    lives=dict(plant=8,maintenance=512)
    for kind in lives:need(F(lives[kind]-1)/F(101,100)>periods[kind]+3,"Receipt availability slack vanished")
    need(TICK_POWER*RECORD_DELAY>=2048,
         "The priced receipt cannot finish at the declared native power")
    need(RX_POWER*F(100,101*2048)>=RX_WORK,
         "The priced RX path cannot finish before its service opportunity")
    # One pending tick plus one receipt job; ordinary RX serializes four symbols.
    need(2*RECORD_DELAY+F(11584+128,2**31)*F(101,100)<F(100,101*2048),
         "Record update serialization breaks RX service")
    clock_delay=2*RECORD_DELAY
    need(F(5000,5001)+clock_delay<=1 and F(5000,5049)-clock_delay>=F(100,101),
         "Completed receipt ticks miss their [1,1.01] rate interface")
    prepared_upper=cam.R+OPEN_AT+CONTROL_DELAY
    need(prepared_upper<F(cam_record["physical_prepared_upper"]),
         "Input row reformation no longer fits inside existing fresh field preparation")
    return dict(lanes_per_source_owner=lanes,owner_record_upper=records,
        new_reset_cells=reset_cells,new_reset_stock=new_stock,reset_capacity_each=RESET_CAP,
        record_data_control_bits=record_bits,existing_record_unit_bits=2048,
        additional_control_bits=control_bits,lane_reset_bitmap_upper=lane_max,
        lane_reset_work_upper=lane_price,local_source_reset_work_upper=local_price,
        controller_clear_rate=CLEAR_RATE,actual_modes=MODES,prepared_position=OPEN_AT,
        source_row_prepared_upper=prepared_upper,old_field_preparation=cam_record["physical_prepared_upper"],
        added_upstream_rate=added_rate,added_upstream_burst=added_burst,
        updated_upstream_capacity=new_U,updated_upstream_rate=D,updated_upstream_burst=B,
        usable_reserve_lower=reserve,unchanged_supply_rate=supply,
        unchanged_total_host_capacity=legacy_record["total_host_capacity_upper"],
        additional_recoverable_stock_is_subtracted_from_U=True,unused_legacy_stock_not_borrowed=True,
        old_data_flight_capacity_retained=legacy_record["retained_flight_capacity"],
        new_native_peak=physical_peak,combined_native_peak=combined,
        added_joint_reaction=reaction,complete_joint_reaction=total_reaction,
        receipt_job_delay=RECORD_DELAY,record_native_power=TICK_POWER,record_receipt_work=2048,
        native_left_boundary_burst=native_burst,
        insufficient_2_to_22_receipt_work_in_delay=(1<<22)*RECORD_DELAY,
        completed_tick_interval=[F(100,101),F(1)],
        receipt_periods=periods,pair_read_window=pair,
        owner_and_physical_heat_location_are_distinct=True)

def serial(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [serial(v) for v in x]
    return x

def generate():
    need(sys.version_info[:2]==(3,12) and not sys.flags.optimize,"Unoptimized Python3.12 required")
    inputs=("cam_reformation.py","CAM-REFORMATION.md","cam_reformation_results.json",
        "threshold_field_source.py","threshold_field_source_results.json","THRESHOLD-FIELD-SOURCE.md",
        "legacy_realization.py","legacy_realization_results.json","LEGACY-REALIZATION.md",
        "parent_realization.py","parent_realization_results.json","PARENT-REALIZATION.md",
        "threshold_program_model.py","threshold_program_source.py","threshold_design.py",
        "threshold_incidence_model.py","threshold_publication_model.py","constructors.py",
        "fixed_island_model.py","FIXED-ISLANDS.md","publication_timing.py","publication_timing_results.json")
    hashes={}
    for name in inputs:
        frozen=legacy.text_at(BASE,"portability/"+name)
        need(program.digest(HERE/name)==program.hash_text(frozen),"Input changed: "+name)
        hashes[name]=program.hash_text(frozen)
    for name in ("RUNTIME-PORTS.md","ACQUISITION.md","RECEIVER.md","RECEIVER-POWER.md","PORT-SOURCE.md"):
        hashes["../local-control/"+name]=program.hash_text(legacy.text_at(BASE,"local-control/"+name))
    isa=program.load_isa();c=program.compile_program(isa,design.design(isa));b=program.bounds(isa,c)
    need((c.constants["FAST_KEYS"],c.constants["ORIGINS"],c.constants["BAYS"])==(2003,15,1),"Wrong finite layout")
    print("checking coherent records, retained effects and actual source-row reset",flush=True)
    record=record_checks();slots=slot_checks();reset=reset_checks();footprints=footprint_checks();control=control_checks()
    print("executing actual publications and compiled input consumption",flush=True)
    consumed=consumer_checks(isa,c,b)
    return serial(dict(scope="Constructed source-row ordinary input lifecycle; full source/return admission remains open",
        base=BASE,python_version=sys.version,image_sha256=program.hash_text(json.dumps(c.image)),
        frozen_ISA_sha256=isa.source_hash,record_checks=record,slot_checks=slots,reset_checks=reset,
        fault_footprints=footprints,control_checks=control,compiled_consumers=consumed,resources=resource_checks(),
        sources_sha256_lf={n:program.digest(HERE/n) for n in ("INPUT-LIFECYCLE.md","input_lifecycle.py")},
        immutable_inputs_sha256_lf=hashes,
        initial_relation="One-time active raw engines have running clocks/coherent native entry; payloads/countdowns/queued symbols may be arbitrary. Later broad control corruption is never initialized by release.",
        residuals=["actual source-bank cold/data-gate contact and immutable fanout/fault containment",
            "actual source-sibling continuous publication and complete pair-read interval cover",
            "source-root renewal ancestry for every recurrent lane/primary/pair incident",
            "parent retirement and local accepted-child/capsule reset/rearm composition",
            "initial ordinary control-state relation or a separately executed initial normalization",
            "full all-history source/core/world and independent frozen-transfer contracts"],
        full_hybrid_energy_trace=False,full_source_admission=False,program_completion=False,
        independent_review_pending=True))

def main():
    ap=argparse.ArgumentParser(description=__doc__);g=ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--write",action="store_true");g.add_argument("--check",action="store_true")
    args=ap.parse_args();result=generate();path=HERE/"input_lifecycle_results.json"
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8",newline="\n")
    else:need(json.loads(path.read_text(encoding="utf-8"))==result,"Input lifecycle record differs")
    print("PASS source-row input lifecycle construction; source/core admission remains open")

if __name__=="__main__":main()
