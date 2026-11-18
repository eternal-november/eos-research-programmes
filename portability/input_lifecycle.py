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
WIRE_BURST=4
WIRE_RATE=1040
FLIGHT_CAPACITY=264
FLIGHT_PROBE_WORK=208
FLIGHT_DROP_WORK=32
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
        reported_remaining=4096-self.progress_work
        if reported_remaining<0 or not self.cell.debit(max(F(32),reported_remaining)):return False
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


class Bits:
    """A view of already allocated native bits; it owns no second array."""
    def __init__(self,store,start,width):self.store=store;self.start=start;self.width=width
    def get(self,start,width=1):
        need(0<=start and start+width<=self.width,"Native field outside allocation")
        return sum(self.store[self.start+start+j]<<j for j in range(width))
    def put(self,start,width,value):
        nat(value,1<<width,"Native field")
        need(0<=start and start+width<=self.width,"Native field outside allocation")
        for j in range(width):self.store[self.start+start+j]=(value>>j)&1

class IWords:
    def __init__(self,bits):self.bits=bits
    def __len__(self):return 8
    def __iter__(self):return (self[i] for i in range(8))
    def __getitem__(self,index):nat(index,8,"Source I index");return self.bits.get(256*index,256)
    def __setitem__(self,index,value):nat(index,8,"Source I index");self.bits.put(256*index,256,value&MASK)

class BankEnergy(Work):
    def __init__(self,origin,bank,capacity,stock):
        self.identity=(origin,bank);super().__init__(capacity,stock)

class SourceSlot(DataSlot):
    """One existing1024-bit descriptor and4096 ready/pending work cell."""
    def __init__(self,body,bits):
        self.bits=bits;super().__init__(body)
        self.admission=False;self.output=False;self.reset=False
    @property
    def progress_work(self):return F(self._progress)
    @progress_work.setter
    def progress_work(self,v):
        v=F(v);need(v.denominator==1,"Fractional native work counter")
        self._progress=nat(v.numerator,1<<13,"Source descriptor work counter")
    def complete(self,callback,claim):
        if hasattr(self,"source_bank_owner") and (not self.source_bank_owner.powered or not self.source_bank_owner.emit_gate):return False
        return super().complete(callback,claim)
    @property
    def admission(self):return bool(self.bits.get(0))
    @admission.setter
    def admission(self,v):self.bits.put(0,1,int(v))
    @property
    def output(self):return bool(self.bits.get(1))
    @output.setter
    def output(self,v):self.bits.put(1,1,int(v))
    @property
    def reset(self):return bool(self.bits.get(2))
    @reset.setter
    def reset(self,v):self.bits.put(2,1,int(v))

class SymbolFlight:
    """One already emitted symbol with actual transferred, finite work."""
    def __init__(self,destination,symbol):
        self.claim=Claim(destination,symbol);self.stock=F(128);self.spent=F(0)
        self.remaining=F(1,4)
    def flow(self,dt,deliver):
        dt=min(F(dt),self.remaining)
        work=512*dt;self.stock-=work;self.spent+=work;self.remaining-=dt
        if self.remaining==0:self.claim.dispatch(deliver)

class SourceBranch:
    #129*15+113=2048 native bits, inside existing descriptor allocations.
    def __init__(self,bank,ordinal):
        self.bank=bank;self.ordinal=ordinal
        self.bits=Bits(bank.control,ordinal*2048+1935,113)
        self.slots=bank.slots[129*ordinal:129*(ordinal+1)]
        self.fifo=[0]*128  #8-bit selectors in the existing128*384 TX array.
        # Existing physical serial lead and fixed flight cells. The native
        # selector may address a busy or absent cell but cannot create one.
        self.flight_cells=[None]*FLIGHT_CAPACITY
        self.flights=[]         # Sparse simulation index of the same objects.
        self.wire_credit=F(WIRE_BURST)
        self.sent=0;self.rejected=0
    def advance_wire(self,dt,deliver):
        need(dt>=0,"Negative elapsed lead time")
        if self.wire_credit<WIRE_BURST:
            self.wire_credit=min(F(WIRE_BURST),self.wire_credit+WIRE_RATE*dt)
        for child in tuple(self.flights):
            old_spent=child.spent;child.flow(dt,deliver)
            self.bank.flight_heat+=child.spent-old_spent
            # Dead delivery authority does not discard positive residual work.
            if child.remaining==0 and child.stock==0 and not child.claim.live:
                need(self.flight_cells[child.physical_slot] is child,"Flight lost its physical binding")
                self.flight_cells[child.physical_slot]=None
                self.flights.remove(child)
    @property
    def destination(self):
        return LaneId(self.bank.origin,self.bank.bank,
                      self.bank.receivers[self.ordinal//2],self.ordinal%2)
    def offer(self,key,value):
        if not self.bank.powered or not self.bank.admission or not self.bits.get(28):return "cut"
        if not(0<=key<KEYS and 0<=value<=MASK):self.rejected+=1;return "malformed"
        self.bank.recharge_elapsed()
        count=self.bits.get(7,8);head=self.bits.get(0,7)
        if count>=128:self.rejected+=1;return "full"
        for index,slot in enumerate(self.slots):
            if slot.claim is None or not slot.claim.live:
                if slot.admission and slot.cell.stock==4096:break
        else:self.rejected+=1;return "unfunded"
        need(slot.offer((key,value))=="accepted","Native selector chose unavailable cell")
        need(slot.cell.debit(1280),"Captured publication lacks admission work")
        slot.progress_work=F(1280)
        self.fifo[(head+count)%128]=index;self.bits.put(7,8,count+1)
        self.bank.publications+=1;self.bank.local_heat+=1280
        return "accepted"
    def tick(self):
        if not self.bits.get(27):return "stopped"
        if not self.bits.get(26):
            count=self.bits.get(7,8);head=self.bits.get(0,7)
            if not 0<count<=128:return "idle"
            index=self.fifo[head]
            self.bits.put(0,7,(head+1)%128);self.bits.put(7,8,count-1)
            self.bits.put(15,8,index);self.bits.put(23,3,0);self.bits.put(26,1,1)
        index=self.bits.get(15,8);part=self.bits.get(23,3)
        if index>=129 or part>=4:return "invalid-state"
        slot=self.slots[index];token=slot.claim
        if token is None or not token.live:return "stale-busy"
        if not self.bank.powered or not self.bank.emit_gate:
            #A funded local claim can be dropped after the real source cut.
            #Only the32-work control action dissipates now; unused residue
            #stays in its actual cell for the subsequent rated dump.
            if slot.progress_work+32>4096 or not slot.cell.debit(32):return "unfunded-cut-drop"
            slot.progress_work+=32;self.bank.local_heat+=32;token.retire()
            self.bits.put(26,1,0);self.bits.put(23,3,0)
            self.bank.recharge_needed.add(slot)
            return "cut-drop"
        suffix=768 if part==3 else 0
        if slot.progress_work+512+suffix>4096:return "invalid-work-counter"
        # Reserve the defined unsuccessful outcome before even probing. No
        # other actor can consume this private reservation during this step.
        if not slot.output or slot.cell.stock<FLIGHT_PROBE_WORK+FLIGHT_DROP_WORK:return "unfunded"
        need(slot.cell.debit(FLIGHT_PROBE_WORK),"Missing flight qualification work")
        slot.progress_work+=FLIGHT_PROBE_WORK;self.bank.local_heat+=FLIGHT_PROBE_WORK
        index_on_lead=self.bits.get(29,9)
        if index_on_lead>=FLIGHT_CAPACITY:refusal="invalid-flight-selector"
        elif self.flight_cells[index_on_lead] is not None:refusal="flight-busy"
        elif self.wire_credit<1:refusal="lead-busy"
        elif slot.cell.stock<512-FLIGHT_PROBE_WORK+suffix:refusal="unfunded-symbol"
        else:refusal=None
        if refusal is not None:
            need(slot.cell.debit(FLIGHT_DROP_WORK),"Missing reserved rejection work")
            slot.progress_work+=FLIGHT_DROP_WORK;self.bank.local_heat+=FLIGHT_DROP_WORK
            token.retire();self.bits.put(26,1,0);self.bits.put(23,3,0)
            self.bank.recharge_needed.add(slot)
            return refusal+"/drop"
        need(slot.cell.debit(512-FLIGHT_PROBE_WORK),"Missing reserved symbol work")
        key,value=token.payload
        symbol=symbols(key,value)[part]
        child=SymbolFlight(self.destination,symbol);child.physical_slot=index_on_lead
        self.flight_cells[index_on_lead]=child;self.flights.append(child);self.wire_credit-=1
        self.bits.put(29,9,(index_on_lead+1)%FLIGHT_CAPACITY)
        slot.progress_work+=512-FLIGHT_PROBE_WORK;self.sent+=1
        self.bank.local_heat+=384-FLIGHT_PROBE_WORK;self.bank.transferred_flight+=128
        self.bits.put(23,3,part+1)
        if part==3:
            need(slot.cell.debit(suffix),"Missing reserved serializer retirement")
            slot.progress_work+=768;self.bank.local_heat+=768
            token.retire()  #No source callback can dispatch it after slot reuse.
            self.bits.put(26,1,0);self.bits.put(23,3,0)
            self.bank.recharge_needed.add(slot)
        return "symbol"

class LocalSourceBank:
    """Finite TX/ADC state with separate U-reset and E-operation funding."""
    BITS=80*2048+4096+256
    # The final gate strobe has its own fixed price, regardless of the
    # writable work countdown. Both suffix parts fit the original 256.
    ENTRY_COMMIT_WORK=128
    ENTRY_WORK=6*(80*129+1)+4*80+4+256
    CPU_RATE=1<<26
    TX_TICKS=CPU_RATE//1024
    ADC_TICKS=CPU_RATE//4096
    DELTA=F(1,1<<30)
    def __init__(self,origin,bank,payer,population=None):
        nat(bank,2,"Source bank")
        need(isinstance(payer,SourceWork) and payer.origin==origin,"Local reset changed its U owner")
        self.origin=origin;self.bank=bank;self.payer=payer
        self.population=population if population is not None else 12*(6+2**98)+2
        self.receivers=incidence.neighbors(self.population,origin)
        self.reset_work=Work(RESET_CAP);self.control=[1]*self.BITS
        self.engine=Bits([0]*96,0,96)
        self.dispatch=Bits(self.control,80*2048+4096,256)
        self.admission=False;self.emit_gate=False;self.powered=False;self.energy=None
        self.cursor=0;self.reset_phase=F(0);self.entry_cursor=0
        self.slots=[SourceSlot((origin,bank,"DATA",i//129),Bits(self.control,(i//129)*2048+(i%129)*15,15))
                    for i in range(80*129)]
        self.adc_bits=Bits(self.control,80*2048,4096)
        self.I=IWords(self.adc_bits)
        self.adc=SourceSlot((origin,bank,"ADC"),Bits(self.control,80*2048+3000,15))
        self.branches=[SourceBranch(self,j) for j in range(80)]
        for index,slot in enumerate(self.slots+[self.adc]):
            slot.native_index=index;slot.source_bank_owner=self
        self.independent_children=[];self.old_wire=[]
        self.recharge_needed=set();self.native_time=0;self.next_tick=self.ADC_TICKS;self.flow_time=0;self.charge_time=0
        self.adc_elapsed=0;self.tx_phase=0;self.rx_phase=0
        self.receivers_live={};self.raw_heads={};self.functional={}
        self.publications=0;self.samples=0;self.adc_completed=0
        self.local_heat=F(0);self.transferred_flight=F(0);self.flight_heat=F(0)
        self.reset_setup=0;self.abort_cursor=0;self.reset_stage="idle"
        self.entry_remaining=0;self.entry_phase=F(0);self.elapsed_entry=F(0)
    @property
    def cursor(self):return self.engine.get(0,18)
    @cursor.setter
    def cursor(self,v):self.engine.put(0,18,v)
    @property
    def abort_cursor(self):return self.engine.get(18,14)
    @abort_cursor.setter
    def abort_cursor(self,v):self.engine.put(18,14,v)
    @property
    def reset_setup(self):return self.engine.get(32,18)
    @reset_setup.setter
    def reset_setup(self,v):self.engine.put(32,18,v)
    @property
    def entry_cursor(self):return self.engine.get(50,16)
    @entry_cursor.setter
    def entry_cursor(self,v):self.engine.put(50,16,v)
    @property
    def entry_remaining(self):return self.engine.get(66,16)
    @entry_remaining.setter
    def entry_remaining(self,v):self.engine.put(66,16,v)
    @property
    def tx_phase(self):return self.engine.get(82,2)
    @tx_phase.setter
    def tx_phase(self,v):self.engine.put(82,2,v)
    @property
    def rx_phase(self):return self.engine.get(84,1)
    @rx_phase.setter
    def rx_phase(self,v):self.engine.put(84,1,v)
    @property
    def reset_micro(self):return self.engine.get(85,3)
    @reset_micro.setter
    def reset_micro(self,v):self.engine.put(85,3,v)
    @property
    def entry_micro(self):return self.engine.get(88,1)
    @entry_micro.setter
    def entry_micro(self,v):self.engine.put(88,1,v)
    @property
    def native_mode(self):return self.engine.get(89,4) if self.engine.get(93) else 15
    def apply_native_mode(self,mode):
        nat(mode,16,"Local source native mode")
        if mode==0:return self.begin_reset()=="masked"
        if not self.payer.debit(256):return False
        self.engine.put(89,4,mode);self.engine.put(93,1,1)
        return True
    @property
    def valid(self):return bool(self.adc_bits.get(2049))
    @valid.setter
    def valid(self,v):self.adc_bits.put(2049,1,int(v))
    @property
    def job(self):
        return self.adc.claim if self.adc.claim is not None and self.adc.claim.live else None
    def attach(self,lane):
        need(lane.population==self.population and lane.identity.receiver in self.receivers and
             lane.identity.origin==self.origin and lane.identity.source_bank==self.bank,
             "Source attached a foreign origin/bank")
        self.receivers_live[lane.identity]=lane
    def cold_cut(self):
        self.admission=False;self.emit_gate=False;self.powered=False
        self.recharge_needed.clear()
    def clear_value(self,index):
        if index<80*2048:
            local=index%2048
            return int(local<1935 and local%15==2)
        return int(index==80*2048+3002)
    def begin_reset(self):
        self.cold_cut()
        if not self.payer.debit(256):return "control-unfunded"
        self.engine.store[:]=[0]*96
        self.engine.put(93,1,1)  #MASK: no old reset or entry clock remains selected.
        self.cursor=0;self.reset_phase=F(0);self.abort_cursor=0
        self.reset_setup=self.BITS//2+1281;self.reset_micro=0;self.reset_stage="setup"
        return "masked"
    def reset_native(self,dt):
        if self.native_mode not in (2,3):return False
        if self.abort_cursor>len(self.slots)+1 or self.cursor>self.BITS:return False
        if self.abort_cursor==len(self.slots)+1 and self.reset_micro>1:return False
        total=self.reset_phase+F(dt)*CLEAR_RATE
        opportunities=int(total);self.reset_phase=total-opportunities
        take=min(opportunities,self.reset_setup,int(self.reset_work.stock))
        if take:self.reset_work.debit(take);self.reset_setup-=take;opportunities-=take
        slots=self.slots+[self.adc]
        if self.reset_setup==0 and self.abort_cursor<len(slots):
            take=min(opportunities,8*(len(slots)-self.abort_cursor)-self.reset_micro,
                     int(self.reset_work.stock))
            if take:
                self.reset_work.debit(take);opportunities-=take
                funded=self.reset_micro+take;complete=funded//8;self.reset_micro=funded%8
                start=self.abort_cursor
                for i in range(start,start+complete):
                    slots[i].mask();slots[i].abort_after_cut()
                self.abort_cursor+=complete
        if self.native_mode==3 and self.abort_cursor==len(slots) and self.cursor<self.BITS:
            take=min(opportunities,2*(self.BITS-self.cursor)-self.reset_micro,
                     int(self.reset_work.stock))
            if take:
                self.reset_work.debit(take);opportunities-=take
                funded=self.reset_micro+take;complete=funded//2;self.reset_micro=funded%2
                start=self.cursor
                for index in range(start,start+complete):self.control[index]=self.clear_value(index)
                self.cursor+=complete
        #Only already PAID partial operation steps survive, never unused time.
        return self.cursor==self.BITS
    def reform(self):
        if self.begin_reset()!="masked":return "control-unfunded"
        if not self.apply_native_mode(1):return "charge-control-unfunded"
        self.reset_work.charge(RESET_REFILL,self.payer)
        if not self.apply_native_mode(2):return "dump-control-unfunded"
        #The paid abort/setup prefix precedes the actual parallel dump.
        prefix=F(self.BITS//2+1281+8*(80*129+1),CLEAR_RATE)
        self.reset_native(prefix)
        for slot in self.slots+[self.adc]:slot.cell.dump(DUMP_TIME)
        if not self.apply_native_mode(3):return "clear-control-unfunded"
        self.reset_native(F(2*self.BITS,CLEAR_RATE))
        return "formed-unpowered" if self.cursor==self.BITS else "partial"
    def begin_entry(self,energy):
        need(isinstance(energy,BankEnergy) and energy.identity==(self.origin,self.bank),
             "Source entry borrowed another operating bank")
        self.energy=energy;self.powered=True
        #The physical connection is real even if its native request cannot
        #be paid. It grants no free overwrite of retained entry control.
        if not self.apply_native_mode(4):return False
        self.entry_cursor=0;self.entry_remaining=self.ENTRY_WORK-self.ENTRY_COMMIT_WORK
        self.entry_phase=F(0);self.entry_micro=0
        self.elapsed_entry=F(0);self.engine.put(94,1,1)
        return True
    def entry_flow(self,dt):
        #Fixed native entry sequence, not a success/correct-code gate.
        dt=F(dt)
        need(dt>=0 and 0<=self.entry_phase<1,"Invalid elapsed time or entry clock phase")
        self.elapsed_entry+=dt
        if not self.powered or self.native_mode!=4 or not self.engine.get(94):return False
        total=self.entry_phase+dt*CLEAR_RATE;steps=int(total);self.entry_phase=total-steps
        slots=self.slots+[self.adc];writes=3*len(slots)+2*80+2
        if self.entry_cursor>writes:return False
        if self.entry_cursor<writes:
            take=min(steps,2*(writes-self.entry_cursor)-self.entry_micro,
                     self.entry_remaining,int(self.reset_work.stock))
            if take:
                self.reset_work.debit(take);steps-=take;self.entry_remaining-=take
                funded=self.entry_micro+take;complete=funded//2;self.entry_micro=funded%2
                start=self.entry_cursor
                for i in range(start,start+complete):
                    if i<3*len(slots):
                        slot=slots[i//3];which=i%3
                        if which==0:slot.admission=True
                        elif which==1:slot.output=True
                        else:slot.reset=False
                    elif i<3*len(slots)+160:
                        j=i-3*len(slots);self.branches[j//2].bits.put(27+j%2,1,1)
                    elif i==3*len(slots)+160:self.adc_bits.put(2050,1,1)
                    else:self.dispatch.put(1,1,1)
                self.entry_cursor+=complete
        if self.entry_cursor==writes and self.entry_remaining:
            take=min(steps,self.entry_remaining,int(self.reset_work.stock))
            if take:
                self.reset_work.debit(take);steps-=take;self.entry_remaining-=take
        # A terminal control word selects the strobe. Only an actual clock
        # edge with actual local work can drive it. A forged request can buy
        # a premature opening under the same physical guards and price.
        if (steps==0 or self.entry_remaining!=0 or self.entry_cursor!=writes
                or self.entry_micro!=0 or not self.reset_work.debit(self.ENTRY_COMMIT_WORK)):
            return False
        self.reset_work.heat+=self.ENTRY_COMMIT_WORK
        # The request-gated clock stops on its actual completion edge.
        # Unused time after that edge cannot advance this stopped phase.
        self.entry_phase=F(0)
        self.engine.put(94,1,0)
        self.admission=True;self.emit_gate=True
        # Sparse simulation index of idle physical chargers. They each have
        # their own busy/power/cap guards and draw from the same actual E.
        self.recharge_needed.update(slot for slot in slots if slot.claim is None or not slot.claim.live)
        return True
    def recharge(self,dt):
        if not self.powered or self.energy is None:return F(0)
        delivered=F(0);cap=4096*F(dt)/self.DELTA
        for slot in sorted(self.recharge_needed,key=lambda x:x.native_index):
            if slot.claim is not None and slot.claim.live:continue
            amount=min(4096-slot.cell.stock,cap,self.energy.stock)
            need(amount>=0 and self.energy.debit(amount),"E recharge overdrew its real stock")
            slot.cell.stock+=amount;slot.cell.received+=amount;delivered+=amount
            if slot.cell.stock==4096:self.recharge_needed.discard(slot)
        return delivered
    def recharge_elapsed(self):
        dt=F(self.native_time-self.charge_time,self.CPU_RATE)
        self.charge_time=self.native_time
        return self.recharge(dt)
    def rearm(self,energy=None):
        if energy is None:return "missing-physical-E-entry"
        if not self.begin_entry(energy):return "entry-control-unfunded"
        committed=self.entry_flow(F(self.ENTRY_WORK,CLEAR_RATE))
        self.recharge(self.DELTA)
        return "entered" if committed else "partial-entry"
    def source_start(self,kind,args):
        if not self.powered or not self.admission or not self.adc_bits.get(2050):return "cut"
        if self.job is not None or self.adc_bits.get(2048):return "busy"
        self.recharge_elapsed()
        if kind=="fast":
            key=args[0]
            valid=0<=key<KEYS and key!=2 and (key<2 or (key-3)%50<46)
            value=self.raw_heads.get(key,MASK) if valid else MASK
            self.I[0]=key
            desc=(0,key,0,0,0,0,value)
        else:
            target,side,member,metric=args
            valid=0<=target<40 and side in (0,1) and 0<=member<11 and metric in (0,1)
            value=self.functional.get(tuple(args),MASK) if valid else MASK
            desc=(1,0,target if valid else 0,side if valid else 0,member if valid else 0,metric if valid else 0,value)
        if self.adc.offer(self.adc_bits)!="accepted":return "unfunded"
        kind,key,target,side,member,metric,value=desc
        for at,width,v in ((2060,1,kind),(2061,11,key if 0<=key<2048 else 2047),
                           (2072,6,target),(2078,1,side),(2079,4,member),(2083,1,metric),(2084,256,value)):
            self.adc_bits.put(at,width,v)
        need(self.adc.cell.debit(1280),"ADC admission lacks funded work")
        self.adc.progress_work=F(1280);self.local_heat+=1280;self.valid=False
        self.adc_bits.put(2048,1,1);self.adc_bits.put(2052,6,63)
        self.samples+=1
        return "accepted"
    def adc_tick(self):
        if not self.adc_bits.get(2050) or not self.adc_bits.get(2048):return
        token=self.job
        if token is None:return  #A forged busy bit creates no completion claim.
        count=self.adc_bits.get(2052,6)
        if count:
            if self.adc.progress_work+16>4096:return
            if not self.adc.cell.debit(16):return
            self.adc.progress_work+=16;self.local_heat+=16;count-=1;self.adc_bits.put(2052,6,count)
        if count==0:
            reported_remaining=4096-self.adc.progress_work
            if reported_remaining<0:return
            remaining=max(F(768),reported_remaining)
            if not self.adc.cell.debit(remaining):return
            self.adc.progress_work=F(4096);self.local_heat+=remaining
            def commit(_destination,payload):
                self.I[1]=payload.get(2084,256);self.valid=True
            token.dispatch(commit)
            self.adc_bits.put(2048,1,0);self.adc_completed+=1
            self.recharge_needed.add(self.adc)
    def deliver_symbol(self,destination,value):
        lane=self.receivers_live.get(destination)
        if lane is not None:lane.receive_symbol(value)
    def native_tick(self):
        self.adc_tick();self.tx_phase=(self.tx_phase+1)%4
        self.rx_phase=(self.rx_phase+1)%2
        if self.tx_phase==0:
            for branch in self.branches:branch.tick()
        if self.rx_phase==0:
            for lane in self.receivers_live.values():
                lane.process_one()
                for record in lane.ordered:
                    for _ in range(3):
                        if record.service() in ("idle","stopped","stale-busy","unfunded"):break
    def advance_cpu(self,ticks=1):
        need(type(ticks) is int and ticks>=0,"Invalid local elapsed instruction ticks")
        end=self.native_time+ticks
        while self.next_tick<=end:
            self.native_time=self.next_tick;self.recharge_elapsed()
            dt=F(self.next_tick-self.flow_time,self.CPU_RATE)
            for branch in self.branches:
                branch.advance_wire(dt,self.deliver_symbol)
            self.flow_time=self.next_tick;self.next_tick+=self.ADC_TICKS
            self.native_tick()
        self.native_time=end

def native_source_ports(isa):
    Parent=program.ports_class(isa)
    class NativeSourcePorts(Parent):
        """Actual source-I/ADC/TX operations; old ideal due lists stay unused."""
        def __init__(self,compiled,source):
            super().__init__(compiled);self.source=source;self.I=source.I
        def advance(self,machine):self.source.advance_cpu()
        def elapse(self,quanta):
            ticks=F(quanta)*self.source.CPU_RATE
            need(ticks.denominator==1,"Native trace uses exact CPU-tick durations")
            self.source.advance_cpu(ticks.numerator)
        def perform(self,name,args,machine):
            source=self.source
            if name in program.FORBIDDEN:
                if name=="source_capture_request" and source.admission:source.I[0]=MASK
                return 0
            if name.startswith("source_"):
                if not source.powered or not source.admission or not source.dispatch.get(1) or source.dispatch.get(0):return 0
                source.dispatch.put(0,1,1)
                try:return self.source_operation(name,args,machine)
                finally:source.dispatch.put(0,1,0)
            return super().perform(name,args,machine)
        def source_operation(self,name,args,machine):
            source=self.source
            if name=="source_start_fast":
                source.source_start("fast",args);return 0
            if name=="source_start_functional":
                source.source_start("functional",args);return 0
            if name=="source_ready":return int(source.powered and source.admission and source.valid and source.job is None and not source.adc_bits.get(2048))
            if name=="source_offer_fast":
                client,key=args
                if type(client) is int and 0<=client<80:
                    source.branches[client].offer(key,source.I[1])
                return 0
            if name=="source_invalidate":
                if source.admission:source.valid=False;source.I[5]=MASK
                return 0
            if name.startswith("source_") and not source.admission:return 0
            return super().perform(name,args,machine)
    return NativeSourcePorts



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



def source_partition_checks():
    population=12*(6+2**98)+2
    pair=[LocalSourceBank(2,0,SourceWork(2,1<<60,1<<60),population) for _ in range(2)]
    for bank in pair:
        bank.begin_reset();bank.apply_native_mode(1);bank.reset_work.charge(1000,bank.payer)
        bank.apply_native_mode(2)
    setup=LocalSourceBank.BITS//2+1281;aborts=80*129+1
    chunks=[setup-1,1,1,7,1,7,8*(aborts-2)]
    pair[0].reset_native(F(setup+8*aborts,CLEAR_RATE))
    for ticks in chunks:
        for _ in range(3):pair[1].reset_native(F(ticks,3*CLEAR_RATE))
    for bank in pair:
        for slot in bank.slots+[bank.adc]:slot.cell.dump(100)
        bank.apply_native_mode(3)
    pair[0].reset_native(F(2*LocalSourceBank.BITS,CLEAR_RATE))
    for ticks in (1,1,2*LocalSourceBank.BITS-2):
        for _ in range(3):pair[1].reset_native(F(ticks,3*CLEAR_RATE))
    need(pair[0].control==pair[1].control and pair[0].cursor==pair[1].cursor==LocalSourceBank.BITS
         and pair[0].reset_micro==pair[1].reset_micro==0
         and pair[0].reset_work.spent==pair[1].reset_work.spent==504329,
         "Reset depends on the caller's time partition")
    for bank in pair:bank.begin_entry(BankEnergy(2,0,1<<60,1<<60))
    price=LocalSourceBank.ENTRY_WORK
    pair[0].entry_flow(F(price,CLEAR_RATE))
    for ticks in (1,1,1,1,1,price-5):
        for _ in range(3):pair[1].entry_flow(F(ticks,3*CLEAR_RATE))
    need(pair[0].control==pair[1].control and pair[0].admission and pair[1].admission
         and pair[0].entry_cursor==pair[1].entry_cursor
         and pair[0].entry_micro==pair[1].entry_micro==0
         and pair[0].reset_work.spent==pair[1].reset_work.spent==566835,
         "Entry depends on the caller's time partition")
    #A later physical cut cannot be undone by an old entry completion.
    late=pair[1];late.begin_entry(BankEnergy(2,0,1<<60,1<<60));late.cold_cut()
    late.entry_flow(F(price,CLEAR_RATE))
    need(late.branches[0].offer(0,500)=="cut","Old entry completion reopened a physical cut")
    late.begin_reset();stock=late.reset_work.stock;late.entry_flow(1000)
    need(late.reset_work.stock==stock and late.native_mode==0,
         "Old entry job consumed reset recharge or survived MASK")
    unpaid=pair[0];unpaid.cold_cut()
    unpaid.entry_cursor=17;unpaid.entry_remaining=9;unpaid.engine.put(94,1,0)
    unpaid.payer.stock=F(0)
    before=(list(unpaid.engine.store),unpaid.entry_phase,unpaid.payer.spent)
    new_E=BankEnergy(2,0,1<<60,1<<60)
    need(unpaid.begin_entry(new_E) is False and unpaid.powered and unpaid.energy is new_E
         and before==(list(unpaid.engine.store),unpaid.entry_phase,unpaid.payer.spent),
         "Unfunded mode action minted or overwrote an entry request")
    need(unpaid.rearm(new_E)=="entry-control-unfunded" and
         before==(list(unpaid.engine.store),unpaid.entry_phase,unpaid.payer.spent),
         "Rearm bypassed failed native entry control")
    return dict(reset_partition_subintervals=30,entry_partition_subintervals=18,
        unfunded_entry_preserves_control_but_keeps_actual_E_connection=True,
        paid_reset_micro_bits=3,paid_entry_micro_bits=1,
        source_engine_used_bits=95,source_engine_allocated_bits=96,
        held_local_mode_disables_old_reset_and_entry=True,
        late_entry_cannot_reopen_actual_power_cut=True,
        whole_and_partitioned_control_work_equal=True)


def source_entry_strobe_checks():
    """Source of work, gate, clock and old bindings at final opening."""
    source=LocalSourceBank(2,0,SourceWork(2,1<<60,1<<60))
    need(source.reform()=="formed-unpowered","Missing genuine cold reset for strobe probe")
    energy=BankEnergy(2,0,1<<60,1<<60)
    need(source.rearm(energy)=="entered","Genuine source entry failed")
    # Keep an accepted, independently funded ADC job and one emitted symbol.
    source.raw_heads[0]=333
    need(source.source_start("fast",(0,))=="accepted","Missing live ADC job")
    claim=source.job;adc_stock=source.adc.cell.stock
    branch=source.branches[0]
    need(branch.offer(0,500)=="accepted" and branch.tick()=="symbol","Missing real transmitted parcel")
    flight=branch.flights[0];flight_claim=flight.claim;flight_stock=flight.stock
    writes=3*(len(source.slots)+1)+2*len(source.branches)+2
    price=source.ENTRY_COMMIT_WORK
    source.admission=False;source.emit_gate=False
    source.entry_cursor=writes;source.entry_remaining=0;source.entry_micro=0;source.engine.put(94,1,1)
    source.entry_phase=F(0);source.reset_work.stock=F(0)
    spent=source.reset_work.spent
    need(not source.entry_flow(0) and not source.entry_flow(1000) and not source.admission
         and not source.emit_gate and source.engine.get(94) and source.reset_work.spent==spent,
         "Forged terminal controls created a free opening")
    # Distinct retained-stock cases on this same digital control tuple.
    # These are boundary fixtures, not free recharge during native mode 4.
    source.reset_work.stock=price-1
    need(not source.entry_flow(F(1,CLEAR_RATE)) and source.reset_work.spent==spent
         and source.reset_work.stock==price-1,
         "A partial parcel energized a complete terminal strobe")
    source.reset_work.stock=F(price);heat=source.reset_work.heat
    # A genuinely powered controller with forged terminal controls may open
    # on the next funded edge; opening does not certify slot preparation.
    source.slots[-1].admission=False
    need(not source.entry_flow(0) and not source.entry_flow(F(1,3*CLEAR_RATE))
         and not source.entry_flow(F(1,3*CLEAR_RATE)) and not source.admission
         and source.reset_work.spent==spent,"Unfunded past time bought the terminal strobe")
    need(source.entry_flow(F(1,3*CLEAR_RATE)) and source.admission and source.emit_gate
         and source.reset_work.spent==spent+price and source.reset_work.stock==0
         and source.reset_work.heat==heat+price and not source.engine.get(94) and not source.slots[-1].admission,
         "Actual paid edge failed its exact gate/stock transition")
    need(not source.entry_flow(1000) and source.reset_work.spent==spent+price,
         "An already consumed request replayed")
    need(source.job is claim and claim.live and source.adc.cell.stock==adc_stock
         and flight.claim is flight_claim and flight.claim.live and flight.stock==flight_stock
         and source.energy is energy,"Entry changed other accepted work, binding or destination")
    source.cold_cut();source.engine.put(94,1,1);source.reset_work.stock=price
    need(not source.entry_flow(1000) and not source.admission and not source.emit_gate
         and source.reset_work.spent==spent+price and source.reset_work.stock==price,
         "Paid terminal fields bypassed the physical source cut")
    # Probe a future fault as a consumer of the *retained oscillator phase*.
    # A whole 1.5-tick call and a call split at the commit edge must leave
    # the same clock state, even if request 94 is later corrupted again.
    continuations=[]
    for segments in ((F(3,2),),(F(1),F(1,2))):
        other=LocalSourceBank(2,0,SourceWork(2,1<<60,1<<60))
        other.begin_entry(BankEnergy(2,0,1<<60,1<<60))
        other.entry_cursor=writes;other.entry_remaining=0
        other.reset_work.stock=F(2*price)
        for ticks in segments:other.entry_flow(ticks/CLEAR_RATE)
        need(other.admission and not other.engine.get(94) and other.entry_phase==0,
             "A blocked clock retained time beyond its actual strobe")
        other.engine.put(94,1,1)
        first=other.entry_flow(F(1,2*CLEAR_RATE))
        second=other.entry_flow(F(1,2*CLEAR_RATE))
        continuations.append((first,second,other.reset_work.stock,other.entry_phase))
    need(continuations==[(False,True,0,0)]*2,
         "Time subdivision changed a future forged request's affordances")
    # One successful clear/entry sequence pays the same total; quiescence
    # and time partition are checked separately on the real native state.
    return dict(strobe_work=price,zero_stock_terminal_request_rejected=True,
        zero_clock_and_subtick_rejected=True,partial_stock_retained=True,
        paid_edge_can_open_with_corrupt_ordinary_controls=True,admission_is_not_formation=True,
        consumed_request_not_replayed=True,stopped_clock_partition_under_later_recorruption=True,
        cold_power_cut_dominates=True,
        fixed_E_accepted_ADC_and_emitted_symbol_preserved=True)


def finite_flight_checks():
    """Exercise the raw divider, the physical limiter, and actual old stock."""
    bank=LocalSourceBank(2,0,SourceWork(2,1<<60,1<<60))
    bank.reform();bank.rearm(BankEnergy(2,0,1<<60,1<<60))
    lane=bank.branches[0]
    for i in range(67):
        need(lane.offer(0,i)=="accepted","Unfunded saturated-flight setup")
    # Each iteration represents a distinct raw divider overwrite, with the
    # underlying physical tick and lead propagation still advancing in time.
    for i in range(265):
        bank.tx_phase=3;bank.advance_cpu(bank.ADC_TICKS)
        need(lane.sent<=WIRE_BURST+WIRE_RATE*F(i+1,4096)
             and len(lane.flights)<=FLIGHT_CAPACITY,"Mutable divider bypassed the physical lead")
    need(lane.sent<265 and all(f.stock+f.spent==128 for f in lane.flights),
         "Divider pressure copied a symbol or lost its parcel")
    b=bank.branches[1]
    need(b.offer(0,23)=="accepted" and b.tick()=="symbol","Missing original physical flight")
    old=b.flights[0];old_token=old.claim
    active=b.slots[b.bits.get(15,8)];source_claim=active.claim
    # Price a full retained-state boundary fixture explicitly. This tests
    # the native port on full input without assuming its whole prefix.
    supply=Work(128*(FLIGHT_CAPACITY-1),128*(FLIGHT_CAPACITY-1))
    for j in range(1,FLIGHT_CAPACITY):
        need(supply.debit(128),"Initial retained symbol has no stock")
        child=SymbolFlight(b.destination,j);child.physical_slot=j
        b.flight_cells[j]=child;b.flights.append(child)
    before=(active.cell.stock,bank.local_heat,bank.transferred_flight)
    refusal_price=FLIGHT_PROBE_WORK+FLIGHT_DROP_WORK
    need(b.tick()=="flight-busy/drop" and len(b.flights)==FLIGHT_CAPACITY
         and not b.bits.get(26) and not source_claim.live and old.claim is old_token and old_token.live
         and active.cell.stock==before[0]-refusal_price
         and bank.local_heat==before[1]+refusal_price
         and bank.transferred_flight==before[2],"A full carrier lost or copied work")
    need(b.tick()=="idle" and active.cell.stock==before[0]-refusal_price,
         "The rejected local claim could retire itself twice")
    need(b.offer(0,24)=="accepted","Failed to queue a new record after refusal")
    b.bits.put(29,9,511);need(b.tick()=="invalid-flight-selector/drop","An absent physical slot accepted work")
    b.bits.put(29,9,0)
    old_token.retire();received=[]
    b.advance_wire(F(1,8),lambda dst,value:received.append((dst,value)))
    need(b.offer(0,25)=="accepted" and old.stock==64 and old.remaining==F(1,8)
         and b.flight_cells[0] is old and b.tick()=="flight-busy/drop",
         "A half-drained physical slot was recycled")
    b.advance_wire(F(1,8),lambda dst,value:received.append((dst,value)))
    need(old.stock==0 and old.spent==128 and b.flight_cells[0] is None and not b.flights
         and len(received)==FLIGHT_CAPACITY-1,"A retired flight was delivered twice or lost work")
    need(b.offer(0,26)=="accepted","Fresh data claim could not use the drained branch")
    transferred=bank.transferred_flight
    for _ in range(4):need(b.tick()=="symbol","Fresh coherent record could not complete after actual drain")
    need(not b.bits.get(26) and len(b.flights)==4 and b.flights[0] is not old
         and b.flights[0].physical_slot==0 and bank.transferred_flight==transferred+512,
         "Paid record reuse failed after actual flight drainage")
    # The 5th immediate symbol cannot use nominal timing merely because it
    # is funded. Reject once; preserve all older flights. At the next
    # nominal symbol time the physical rate residual admits one again.
    need(b.offer(0,27)=="accepted" and b.tick()=="lead-busy/drop"
         and not b.bits.get(26) and len(b.flights)==4,"Rate refusal stranded old sender state")
    need(b.offer(0,28)=="accepted","Fresh record could not follow a rate refusal")
    for _ in range(4):
        b.advance_wire(F(100,101*1024),lambda dst,val:None)
        need(b.tick()=="symbol","First fresh record following rate refusal remained poisoned")
    # Unfund the terminal suffix after three actual emissions. A refusal
    # before the fourth preserves all old symbols, consumes the source
    # claim and leaves its actual unused work on the elected DATA cell.
    b.advance_wire(F(1,4),lambda dst,val:None)
    need(b.offer(0,29)=="accepted","No DATA claim for the short-terminal probe")
    for _ in range(3):need(b.tick()=="symbol","Short-terminal preparation failed")
    current=b.slots[b.bits.get(15,8)];claim=current.claim;old_symbols=tuple(b.flights)
    need(current.cell.stock==1280 and current.cell.debit(1),"Short-terminal countercase lost its physical debit")
    bank.local_heat+=1
    need(b.tick()=="unfunded-symbol/drop" and not claim.live and not b.bits.get(26)
         and current.cell.stock==1279-refusal_price and tuple(b.flights)==old_symbols,
         "A doomed terminal attempt started a fourth parcel or left a stuck serializer")
    return dict(physical_slots=FLIGHT_CAPACITY,elapsed_divider_override_ticks=265,
        emitted_under_divider_pressure=lane.sent,first_old_failure_time=F(265,4096),
        full_reject_work=refusal_price,old_partial_work_preserved=64,
        grant_before_emit=True,old_delivery_revocation_retains_work=True,
        full_or_rate_refusal_retires_only_the_local_claim=True,
        valid_record_after_flight_drain_and_after_rate_refusal=True,
        terminal_suffix_qualified_before_fourth_symbol=True,
        true_drain_before_reuse=True,invalid_9_bit_flight_selector_rejected=True,
        initial_full_fixture_work=supply.spent+128)


def source_native_checks():
    population=12*(6+2**98)+2;u=SourceWork(2,1<<60,1<<60)
    bank=LocalSourceBank(2,0,u,population)
    need(bank.reform()=="formed-unpowered","Literal source reset failed")
    cold_work=bank.reset_work.spent
    need(cold_work==504329 and all(v==0 for v in bank.I),"Source I was not literally cleared")
    need(all(not s.admission and not s.output and s.reset and s.cell.stock==F(1,2)
             for s in bank.slots+[bank.adc]),"Cold reset silently rearmed source cells")
    need(bank.rearm()=="missing-physical-E-entry","U row OPEN fabricated operating E")
    bank.admission=True;bank.emit_gate=True
    need(bank.branches[0].offer(0,500)!="accepted","Bank flags alone restored source service")
    bank.admission=False;bank.emit_gate=False
    E=BankEnergy(2,0,1<<60,1<<60)
    need(bank.rearm(E)=="entered","Actual source E entry failed")
    entry_work=bank.reset_work.spent-cold_work
    need(entry_work==bank.ENTRY_WORK==62506,"Source entry writes were not counted")
    need(E.spent==F(84539311,2),"Full source refill debit differs from actual floor stock")
    need(all(s.admission and s.output and not s.reset and s.cell.stock==4096
             for s in bank.slots+[bank.adc]),"Bank entry left slots masked/unfunded")
    branch=bank.branches[0]
    #Literal bit identity: a stale scheduler clock cannot be cured by an offer.
    branch.bits.put(27,1,0)
    need(branch.offer(0,500)=="accepted" and branch.tick()=="stopped",
         "A data offer repaired the serializer clock")
    branch.bits.put(27,1,1)
    for j in range(127):need(branch.offer(0,j)=="accepted","Native128 queue rejected prematurely")
    need(branch.offer(0,1)=="full","Native queue exceeded128")
    need(branch.tick()=="symbol" and branch.offer(0,999)=="accepted",
         "One active plus128 queued claims did not fit129 cells")
    need(sum(s.claim is not None and s.claim.live for s in branch.slots)==129,
         "Queue/serializer duplicated or dropped claim ownership")
    old_flight=branch.flights[0];old_claim=branch.slots[0].claim
    stock_before=old_flight.stock;bank.cold_cut();energy_before=E.stock
    need(old_claim.live,"Source cut erased a still-local claim without its paid drop")
    need(not branch.slots[0].complete(lambda d,p:None,old_claim),
         "Per-slot callback bypassed the actual source cut")
    bank.advance_cpu(bank.CPU_RATE//4)
    need(stock_before==128 and old_flight.stock==0 and old_flight.spent==128,
         "CPU/source cut froze or erased emitted work")
    need(E.stock==energy_before,"Cold source recharged an operating cell")
    need(not old_claim.live and branch.slots[0].cell.stock>0,
         "Nominal cut drop did not consume the claim while retaining unused work")
    need(bank.reform()=="formed-unpowered" and not old_claim.live,
         "Native cold reset left an old local publication claim")
    need(not old_claim.dispatch(lambda d,p:(_ for _ in ()).throw(AssertionError("old child"))),
         "Old queue claim replayed after native clear")
    need(bank.rearm(E)=="entered","Repeated actual source entry failed")
    initial_slots=sum(s.cell.stock for s in bank.slots+[bank.adc])
    initial_E=E.stock;initial_heat=bank.local_heat;initial_flight=bank.flight_heat
    bank.raw_heads[0]=42;bank.raw_heads[1]=900
    need(bank.source_start("fast",(0,))=="accepted","ADC rejected actual source request")
    token=bank.job;bank.I[1]=777;bank.valid=False
    need(bank.source_start("fast",(1,))=="busy" and bank.job is token,
         "Busy start replaced an actual captured descriptor")
    bank.adc_bits.put(2050,1,0);remaining=bank.adc_bits.get(2052,6)
    bank.advance_cpu(bank.CPU_RATE//64)
    need(bank.job is token and bank.adc_bits.get(2052,6)==remaining,
         "Stopped ADC clock progressed or a payload restarted it")
    bank.adc_bits.put(2050,1,1);bank.advance_cpu(bank.CPU_RATE//64)
    need(bank.valid and bank.I[1]==42 and bank.job is None,
         "ADC did not return its captured raw sample")
    need(not token.dispatch(lambda d,p:None),"Consumed ADC claim replayed")
    branch=bank.branches[1]
    for j in range(3):need(branch.offer(j,500+j)=="accepted","Post-reset publication unavailable")
    bank.advance_cpu(bank.CPU_RATE)
    final_slots=sum(s.cell.stock for s in bank.slots+[bank.adc])
    live_flight=sum(child.stock for b in bank.branches for child in b.flights)
    need(initial_slots+(initial_E-E.stock)==final_slots+(bank.local_heat-initial_heat)+
         (bank.flight_heat-initial_flight)+live_flight,"Native E/heat/flight balance failed")
    #Partial/faulted reset and entry are real retained states, not READY gates.
    poor=LocalSourceBank(2,1,u,population);poor.begin_reset();poor.apply_native_mode(2)
    poor.reset_native(10**18)
    need(poor.cursor==0 and poor.reset_phase<1,"Unfunded reset replayed clock credit")
    empty=BankEnergy(2,1,0,0);poor.begin_entry(empty)
    poor.entry_flow(10**18)
    need(not poor.admission and poor.entry_cursor==0 and poor.entry_phase<1,
         "Unfunded entry opened native service")
    need(poor.reset_work.charge(1,u)>0,"Actual partial reset recharge failed")
    before=poor.entry_cursor;poor.entry_flow(F(1,2*CLEAR_RATE))
    need(poor.entry_cursor<=before+1,"A past starved interval became present native work")
    #Malformed digital scheduler state cannot invent a funded claim.
    bank.branches[2].bits.put(26,1,1);bank.branches[2].bits.put(15,8,255)
    need(bank.branches[2].tick()=="invalid-state","Invalid selector acquired another slot")
    wrong=BankEnergy(3,0,1<<20,1<<20)
    try:bank.begin_entry(wrong)
    except AssertionError:pass
    else:raise AssertionError("Source rearm pooled another bank's E")
    #A funded ADC continues without CPU/source recharge; only its own clock
    #or work failure may stall it. The later literal reset still owns its claim.
    bank.raw_heads[0]=123
    need(bank.source_start("fast",(0,))=="accepted","Fresh ADC did not rearm")
    accepted=bank.job;bank.cold_cut();E_before=E.stock
    bank.advance_cpu(bank.CPU_RATE//64)
    need(not accepted.live and bank.I[1]==123 and E.stock==E_before,
         "Source power loss cancelled a funded ADC or refilled its cell")
    bank.adc_bits.put(2048,1,1)
    #This stale control has no physical job and cannot be normalized by start.
    bank.admission=True;bank.powered=True
    need(bank.source_start("fast",(0,))=="busy","A new ADC request repaired stale busy state")
    bank.admission=False;bank.powered=False
    lane=RawLane(population,LaneId(2,0,0,0),u)
    record=next(r for r in lane.ordered if r.key<2)
    for symbol in reversed(symbols(record.source_key,500)):
        lane.receive_symbol(symbol);lane.process_one()
    need(record.readable()==MASK,"Reordered raw limbs were a complete nominal frame")
    lane.offer_frame(record.source_key,500)
    need(record.readable()==500,"A fresh ordered frame failed to replace an old partial prefix")
    poor.apply_native_mode(3);poor.abort_cursor=(1<<14)-1
    need(poor.reset_native(1) is False,"Malformed reset selector was interpreted as an operation")
    poor.begin_entry(empty);poor.entry_remaining=0
    need(not poor.entry_flow(1) and not poor.admission,"Zero forged entry work produced service")
    #A writable progress counter is neither work nor a paid return strobe.
    forged=LocalSourceBank(2,1,SourceWork(2,1<<60,1<<60),population)
    forged.reform();forged.rearm(BankEnergy(2,1,1<<60,1<<60))
    forged.raw_heads[0]=333;forged.source_start("fast",(0,))
    pending=forged.job;forged.adc_bits.put(2052,6,0)
    forged.adc.progress_work=4096;forged.adc.cell.stock=F(0)
    before=(forged.I[1],forged.valid,forged.adc_completed)
    forged.adc_tick()
    need(pending.live and before==(forged.I[1],forged.valid,forged.adc_completed),
         "A forged work counter paid an unfunded ADC commit")
    slot=DataSlot(("fixed","source"));slot.offer(9);slot.progress_work=4096;slot.cell.stock=F(0)
    need(not slot.complete(lambda d,v:None,slot.claim) and slot.claim.live,
         "A logical counter funded the generic return strobe")
    partition=source_partition_checks()
    partition["final_entry_strobe"]=source_entry_strobe_checks()
    partition["finite_flight"]=finite_flight_checks()
    return dict(TX_branches=80,
        mutable_counter_cannot_fund_ADC_or_slot_completion=True,
        ADC_physical_commit_floor=768,generic_physical_commit_floor=32,queue_capacity_each=128,claim_cells_each=129,
        partition=partition,stale_ADC_busy_requires_reset=True,
        funded_ADC_continues_after_source_power_cut=True,malformed_native_control_has_bounded_wait=True,
        independent_symbol_reordering_is_not_nominal_FIFO_service=True,
        live_claim_max=129,TX_state_bits_per_branch=2048,
        descriptor_allocation="129*15 live/reset fields +113 scheduler bits in existing1024-bit descriptor units; queue selectors use existing TX payload array",
        ADC_I_words=8,ADC_I_bits=2048,ADC_block_bits=4096,
        source_shared_dispatch_bits=256,separate_reset_engine_bits=96,
        cold_reset_work=cold_work,source_entry_work=entry_work,combined_work=cold_work+entry_work,
        E_initial_refill_work=F(84539311,2),
        entry_time=F(entry_work,CLEAR_RATE)+bank.DELTA,
        power_contact_to_source_entry_upper=CONTROL_DELAY+F(entry_work,CLEAR_RATE)+bank.DELTA,
        source_clock_stop_survives_payload=True,ADC_busy_does_not_replace_capture=True,
        old_ADC_and_TX_claims_consumed=True,emitted_child_survives_cut=True,
        no_cold_E_recharge=True,paid_nominal_cut_drop_preserves_unused_stock=True,
        unfunded_reset_and_entry_wait=True,
        no_credit_replay=True,wrong_bank_E_rejected=True,native_energy_balance=True,
        work_scope="TX/ADC actual cells and reset/entry; funded CPU-parent invocation/native-I arithmetic remain explicit inherited leaf joins",
        physical_scope="constant admissible native clocks and exact finite state transitions; not a complete hybrid cam/parent/plant execution")


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
        source=LocalSourceBank(provider,1,payers[provider],population)
        need(source.reform()=="formed-unpowered","Actual producer source reset failed")
        energy=BankEnergy(provider,1,1<<60,1<<60)
        need(source.rearm(energy)=="entered","Actual producer source entry failed")
        source.attach(lane);value=(450,1050)[incidence.head_type(provider)]
        source.raw_heads[0]=source.raw_heads[1]=value
        ports=native_source_ports(isa)(c,source)
        m=program.call(isa,c,ports,"publish_plant",(),b["instruction_upper_bounds"]["publish_plant"]+10)
        source_steps+=m.steps;ports.elapse(1)
        print("native producer",provider,"instructions",m.steps,flush=True)
        need(source.samples==source.adc_completed==2 and source.publications==160,
             "Compiled source did not use actual ADC/TX operations")
        need(ports.job is None and ports.offer_pending==[],
             "Ideal RawPorts job/offer queue bypassed the source controller")
        need(all(r.value==value and r.ttl==8 for k,r in lane.records.items() if k<2),
             "Native source symbols did not reach their installed receiver record")
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
    ports=Inputs(c);ports.fast[("head",0)]=450;ports.fast[("head",1)]=450
    m=program.initialized(isa,c);m.W[c.constants["ENTRY"]]=1;m.enter("frame")
    while not m.io_counts["world"] and m.steps<b["active_frame_upper"]:need(m.step(ports),"Input consumer stopped")
    need(m.C==c.image and ports.world_latch==(50,80),"Actual framed input did not reach WORLD")
    # Intact inference still consumes forged whole-primary input at a boundary.
    key=1;group=incidence.plant_group(population,receiver,1)
    for slot,origin in enumerate(group):
        lanes[(origin,1)].offer_frame(1,1000 if slot<8 else 999)
    def world_once():
        pp=Inputs(c);pp.fast[("head",0)]=pp.fast[("head",1)]=450
        mm=program.initialized(isa,c);mm.W[c.constants["ENTRY"]]=1;mm.enter("frame")
        while not mm.io_counts["world"]:need(mm.step(pp),"Intact inference stopped")
        need(mm.C==c.image and not mm.code_writes,"Input attack changed execution")
        return pp.world_latch
    before=world_once()
    lanes[(group[0],1)].records[1].value=999
    after=world_once()
    need(before==(50,70) and after==(50,69),"Primary frame is no longer genuinely consumed")
    need(len({id(payers[o]) for o in providers})==len(providers),"Source budgets were pooled")
    return dict(actual_producers=len(providers),distinct_source_U_ledgers=len(payers),source_bank=1,receiver_bank=rb,
        producer_instructions=source_steps,consumer_prefix_instructions=m.steps,
        producers_use_native_ADC_TX_and_E_recharge=True,ideal_RawPorts_job_and_offer_pending_unused=True,
        native_nominal_trace_clock="one retired instruction per1/2^26q; ADC4096 ticks/q; TX1024 symbols/q; receiver2048 steps/q",
        source_traces_are_compatible_constant_head_fixtures_not_full_hybrid_history=True,
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
    need(max(lane_price,local_price+LocalSourceBank.ENTRY_WORK)<RESET_CAP,"Reset and later entry exceed their one actual cell")
    need((80*129+1)*4096/LocalSourceBank.DELTA<=F(legacy_record["actual_ordinary_recharge_peak"])/2,
         "Source E chargers exceed retained ordinary recharge inventory")
    need((1<<60)<=F(legacy_record["actual_keeper_energy_word"])*F(legacy_record["actual_energy_head_unit"]),
         "Native test bank exceeds the actual connected-cap lower bound")
    need(F(62)/(F(101,100)*4096)>F(1,128) and F(63,4096)<F(1,64),
         "Nominal ADC counter/clock misses conversion interval")
    need(F(1280+2816)/(F(4,3)*16384*2**27)<F(3,4)/(F(101,100)*2**26),
         "Source admission cannot fit the retained parent native interval")
    need(CONTROL_DELAY+F(LocalSourceBank.ENTRY_WORK,CLEAR_RATE)+LocalSourceBank.DELTA<F(300,101),
         "Source native entry can outlast the initial residual boot drain")
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
    action_burst=2*256*reset_cells;action_rate=256*reset_cells*cam.CONTROL_MAX
    reset_charge=2*reset_cells*RESET_CAP/RESET_REFILL
    holding=F(control_bits,1024)
    added_rate=2*(native_rate+control_delivered_rate+action_rate)+reset_charge+holding
    added_burst=2*(native_burst+control_delivered_burst+action_burst)
    new_U=F(old["unchanged_upstream_capacity"])-new_stock
    D=F(old["upstream_rate"])+added_rate;B=F(old["upstream_burst"])+added_burst
    reserve=new_U-B-2*D;supply=F(cam_record["resources"]["unchanged_supply_rate"])
    need(D<supply and reserve>added_burst+1,"Same supply/capacity cannot fund raw reset")
    # A local terminal strobe can release 128 local work on one native
    # edge. Count BOTH local sources even under repeated forged requests.
    # Fixed-coincidence qualification: 16 cursor, 16 remainder, 1
    # microstep, 1 request, 5 mode/valid and 1 physical power input.
    strobe_inputs=16+16+1+1+5+1
    strobe_price=2*strobe_inputs+(strobe_inputs-1)+3*2+3
    need(strobe_price==LocalSourceBank.ENTRY_COMMIT_WORK<=256,
         "Terminal stencil or differential suffix price changed")
    strobe_peak=2*LocalSourceBank.ENTRY_COMMIT_WORK*CLEAR_RATE
    physical_peak=(strobe_peak+native_rate+2*lanes*cam.CONTROL_PRICE*2**20+
                   2*256*reset_cells*2**20+reset_cells*2**21+holding)
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
        local_source_entry_work=LocalSourceBank.ENTRY_WORK,
        local_final_strobe_work=LocalSourceBank.ENTRY_COMMIT_WORK,
        local_final_strobe_inputs=strobe_inputs,local_final_strobe_qualification_work=strobe_price,
        local_final_strobe_peak_upper=strobe_peak,
        local_final_strobe_closed_interval_burst=2*LocalSourceBank.ENTRY_COMMIT_WORK,
        local_entry_nominal_edges=LocalSourceBank.ENTRY_WORK-LocalSourceBank.ENTRY_COMMIT_WORK+1,
        local_source_reset_plus_entry_work=local_price+LocalSourceBank.ENTRY_WORK,
        local_source_entry_time=CONTROL_DELAY+F(LocalSourceBank.ENTRY_WORK,CLEAR_RATE)+LocalSourceBank.DELTA,
        native_entry_execution_time=F(LocalSourceBank.ENTRY_WORK,CLEAR_RATE)+LocalSourceBank.DELTA,
        source_initial_E_refill_deficit=(80*129+1)*F(8191,2),
        source_all_cell_E_recharge_peak=(80*129+1)*4096/LocalSourceBank.DELTA,
        source_record_work=4096,source_record_emitted_work=512,source_record_local_heat=3584,
        actual_flight_slots_per_branch=FLIGHT_CAPACITY,physical_burst_symbols=WIRE_BURST,
        physical_symbol_rate=WIRE_RATE,clock_divider_override_attempt_rate=F(101,100)*4096,
        flight_admission_or_rejection_probe_work=FLIGHT_PROBE_WORK,
        refused_flight_closure_work=FLIGHT_DROP_WORK,
        actual_flight_selector_bits=9,
        source_TX_control_bits=80*2048,source_ADC_I_control_bits=4096,source_shared_control_bits=256,
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
    resources=resource_checks()
    print("checking coherent records, retained effects and actual source-row reset",flush=True)
    record=record_checks();slots=slot_checks();reset=reset_checks();footprints=footprint_checks();control=control_checks();native=source_native_checks()
    print("executing actual publications and compiled input consumption",flush=True)
    consumed=consumer_checks(isa,c,b)
    return serial(dict(scope="Constructed source-row ordinary input lifecycle; full source/return admission remains open",
        base=BASE,python_version=sys.version,image_sha256=program.hash_text(json.dumps(c.image)),
        frozen_ISA_sha256=isa.source_hash,record_checks=record,slot_checks=slots,reset_checks=reset,
        fault_footprints=footprints,control_checks=control,source_native_checks=native,compiled_consumers=consumed,resources=resources,
        sources_sha256_lf={n:program.digest(HERE/n) for n in ("INPUT-LIFECYCLE.md","input_lifecycle.py")},
        immutable_inputs_sha256_lf=hashes,
        initial_relation="One-time active raw engines have running clocks/coherent native entry; payloads/countdowns/queued symbols may be arbitrary. Later broad control corruption is never initialized by release.",
        residuals=["actual source-bank cold/data-gate contact and immutable fanout/fault containment",
            "actual source-sibling continuous publication and complete pair-read interval cover",
            "source-root renewal ancestry for every recurrent lane/primary/pair incident",
            "paid parent invocation/no-late-offer and actual source power/contact entry composition",
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
