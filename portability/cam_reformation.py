"""Position-driven fresh reformation; conditional local source, not admission."""
from __future__ import annotations
import argparse
from dataclasses import dataclass, field
from fractions import Fraction as Q
from hashlib import sha256
import json
from math import ceil
from pathlib import Path
import subprocess
import sys
import threshold_field_source as f

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
BASE="6a5f8aad0f0e5156edb21a054f8c72adcbf7120e"
PREFIX="theories-and-designs/byzantine-control/portability/"
FIELD_WORKER="215ecb755312f580cbd8c283b419f0958518766f"
INPUTS=("THRESHOLD-FIELD-SOURCE.md","threshold_field_source.py","threshold_field_source_results.json",
        "THRESHOLD-GEOMETRY.md","threshold_geometry.py","threshold_geometry_results.json",
        "threshold_design.py","threshold_program_source.py","THRESHOLD-PUBLICATION.md",
        "publication_timing.py","publication_timing_results.json")
VMAX=Q(11,10)
MU=Q(1)
CONTROL_STEP=Q(128,2**20)
CONTROL_DELAY=Q(1)+8*CONTROL_STEP
CONTROL_MIN=Q(8)
CONTROL_MAX=Q(202,25)
CONTROL_PRICE=Q(256)  # Each endpoint; includes dispatch-state entry clearing.
CONTROL_BITS=64
CUTOFF=Q(500000000)
CLAMP_END=Q(600000000)
POWER=Q(750000000)
DRIVER=Q(780000000)
ARM=DRIVER-3
WARM=Q(6800000000)
R=Q(2748532811,524288)
BOOT=Q(268456453,67108864)
SCAN=Q(10455187350675,524288)
OLD_POOL=Q(140681857,64)
NAMES=("tail","settle","precharge","isolate","dump","withdraw","clear","abort","refill")

def need(ok,message):
    if not ok:raise AssertionError(message)

def exact(x,name="quantity"):
    if type(x) not in (int,Q):raise ValueError(name+" must be an exact non-Boolean rational")
    return Q(x)

def flag(x,name="flag"):
    if type(x) is not bool:raise ValueError(name+" must be Boolean")
    return x

def digest(s):
    return sha256(s.lstrip('\ufeff').replace('\r\n','\n').encode('utf-8')).hexdigest()

def bindings():
    hashes={};texts={}
    for name in INPUTS:
        result=subprocess.run(['git','show',BASE+':'+PREFIX+name],cwd=REPO,
                              capture_output=True,check=True)
        frozen=result.stdout.decode('utf-8-sig').replace('\r\n','\n')
        current=(HERE/name).read_text(encoding='utf-8-sig').replace('\r\n','\n')
        need(current==frozen,"Frozen cam supplier changed: "+name)
        texts[name]=frozen;hashes[name]=digest(frozen)
    for doc,code,record in (("THRESHOLD-FIELD-SOURCE.md","threshold_field_source.py","threshold_field_source_results.json"),):
        data=json.loads(texts[record])
        for name in (doc,code):need(data['sources_sha256_lf'][name]==hashes[name],"Field record/source mismatch")
    geometry=json.loads(texts['threshold_geometry_results.json'])['arithmetic']
    need(Q(geometry['ordinary_settle'])==R and Q(geometry['vectors']['boot'])==BOOT
         and Q(geometry['vectors']['scan'])==SCAN,"Geometry supplier quantities changed")
    need(Q(geometry['physical_inputs']['clamp_cutoff'])==CUTOFF
         and Q(geometry['physical_inputs']['vector_driver_at'])==DRIVER,"Physical contacts changed")
    return hashes,json.loads(texts['threshold_field_source_results.json']),geometry

def band_table():
    b=f.reformation_bounds()
    durations=(b['old_parent_and_native_tail'],b['initial_reset_settling'],b['reset_reserve_refill'],
               b['mode_commutation'],b['dump'],b['withdrawal'],b['native_clear'],b['parent_abort'],b['final_refill'])
    rows=[];left=Q(0)
    for name,t in zip(NAMES,durations):
        width=ceil(VMAX*(t+CONTROL_DELAY))+1
        right=left+width
        need(width/VMAX>t+CONTROL_DELAY,"A mode may be overtaken by clamp travel")
        rows.append(dict(name=name,left=left,right=right,required=t,
                         minimum_dwell=width/VMAX,propagation=CONTROL_DELAY,
                         strict_slack=width/VMAX-CONTROL_DELAY-t))
        left=right
    return rows

BANDS=band_table()
PREPARED_AT=BANDS[-1]['right']

def contact(q):
    q=exact(q,"clamp")
    if not 0<=q<=CLAMP_END:raise ValueError("Clamp outside its installed stroke")
    return next((i for i,b in enumerate(BANDS) if q<b['right']),9)

@dataclass
class ControlLine:
    """Eight finite clocked copies; no absolute deadline or sequence number.

    Six transit latches plus source and receiver words. Each word is four data
    bits and one validity bit. Native price256 per endpoint also covers the
    actual initial clear of40 maintenance-dispatch bits; no clean state gift.
    """
    words:list=field(default_factory=lambda:[15]*8)
    valid:list=field(default_factory=lambda:[False]*8)
    until_edge:Q=Q(1,8)  # Analyst clock phase, not a stored global timestamp.
    edges:int=0          # Analyst operation counter only.

    def __post_init__(self):
        if type(self.words) is not list or len(self.words)!=8 or any(type(x) is not int or not 0<=x<16 for x in self.words):
            raise ValueError("Control line has eight actual four-bit payload registers")
        self.words=list(self.words)
        if type(self.valid) is not list or len(self.valid)!=8 or any(type(x) is not bool for x in self.valid):
            raise ValueError("Control line has eight actual validity bits")
        self.valid=list(self.valid)
        self.until_edge=exact(self.until_edge)
        if not 0<self.until_edge<=Q(1,8):raise ValueError("Invalid local clock phase")

    def tick(self,code):
        if type(code) is not int or not 0<=code<16:raise ValueError("Invalid control wire")
        old=list(self.words);old_valid=list(self.valid)
        # Bit copies explicitly refer to the prior latch, not the new value.
        for i in range(8):
            source=code if i==0 else old[i-1]
            self.words[i]=sum(((source>>j)&1)<<j for j in range(4))
            self.valid[i]=True if i==0 else old_valid[i-1]
        self.edges+=1
        return self.words[-1] if self.valid[-1] else 15

    def flow(self,dt,code,consume,arrive):
        dt=exact(dt)
        if dt<0:raise ValueError("Negative control time")
        while dt:
            # Constant-input pipeline has no further state changes. Count its
            # continued real clock work without iterating billions of ticks.
            if all(x==code for x in self.words) and all(self.valid):
                consume(dt)
                if dt>=self.until_edge:
                    rest=dt-self.until_edge;n=1+int(rest*8)
                    self.edges+=n;self.until_edge=Q(1,8)-(rest-Q(n-1,8))
                else:self.until_edge-=dt
                return
            step=min(dt,self.until_edge);consume(step)
            dt-=step;self.until_edge-=step
            if self.until_edge==0:
                arrive(self.tick(code));self.until_edge=Q(1,8)

    @property
    def delivered_work(self):
        # Declared padded clock step: each real endpoint spends256 work.
        # This is an export to the single U account, not a freshly minted cell.
        return 2*CONTROL_PRICE*self.edges

@dataclass
class ResidentWord:
    """An external native-operation owner, deliberately outside field reset."""
    body:str
    bank:int
    address:int
    coordinates:list
    parent:tuple

    def __post_init__(self):
        if type(self.body) is not str or not self.body or type(self.bank) is not int or self.bank not in (0,1):
            raise ValueError("Invalid resident physical bank")
        if type(self.address) is not int or not 0<=self.address<8192 or type(self.coordinates) is not list or len(self.coordinates)!=192:
            raise ValueError("Native word must retain its actual selected word")
        self.coordinates=[exact(x) for x in self.coordinates]
        if any(not -1<=x<=1 for x in self.coordinates) or type(self.parent) is not tuple:
            raise ValueError("Invalid resident word or immutable native parent")

class CamBank:
    """One actual outgoing channel plus its shared setter under physical contacts.

    This is a source-local witness dispatcher. The array theorem replicates the
    channel; the setter is installed once per bank, not once per bit. Runtime
    actions never inspect certificate(), a P image, or a scan-completion flag.
    """
    def __init__(self,pulse,setter,resident,*,q=Q(0),control_words=None,control_valid=None,reset_charging=True,
                 charger_bypass=False,reset_interlock=True,controller_residue=0,control_powered=True):
        if type(pulse) is not f.PulseSelector or type(setter) is not f.SettingWriter:
            raise ValueError("Actual hardware selector/setter required")
        if type(resident) is not ResidentWord:raise ValueError("Separate actual resident word owner required")
        self.p=pulse;self.s=setter;self.q=exact(q);contact(self.q)
        self.activation=Q(0);self.time=Q(0);self.trace=[]
        self.clamp_speed=Q(0);self.activation_speed=Q(0)
        self.reset_charging=flag(reset_charging);self.charger_bypass=flag(charger_bypass)
        self.reset_interlock=flag(reset_interlock)
        self.control_powered=flag(control_powered)
        self.raw=f.PulseReformation(pulse,setter)
        self.line=ControlLine([15]*8 if control_words is None else control_words,
                              [True]*8 if control_valid is None else control_valid)
        if type(controller_residue) is not int or not 0<=controller_residue<2**40:
            raise ValueError("Maintenance dispatch residue exceeds its40 physical bits")
        self.action_labels=('source-commutation','receiver-commutation','setter-commutation',
            'source-fanout','receiver-fanout','setter-fanout','receiver-reaction','source-reaction','setter-reaction')
        self.mode=self.line.words[-1] if self.line.valid[-1] else 15
        self.started={label for i,label in enumerate(self.action_labels) if controller_residue&(1<<(24+i))}
        self.pulse_i=controller_residue&2047;self.clear_i=(controller_residue>>11)&8191
        self.clear_credit=Q(0);self.pulse_credit=Q(0)
        self.abort_credit=Q(0);self.parent_aborted=bool(controller_residue&(1<<34))
        self.clear_paid=bool(controller_residue&(1<<33));self.control_entry_clears=0
        self.entry_clear_remaining=f.CONTROL_TAIL if self.mode==0 else None
        self.old_parent=setter.parent_record;self.held_before=dict(setter.held)
        self.dump_done=[bool(controller_residue&(1<<(35+i))) for i in range(3)]
        self.setter_dump_done=bool(controller_residue&(1<<38))
        self.setter_dumped=Q(0);self.setter_delivered=Q(0);self.setter_spent=Q(0)
        self.initial_setter_stock=setter.energy
        self.source_opened=False;self.receiver_armed=False;self.cpu_on=False
        self.abort_mask=False;self.native_c_launch=False
        self.resident=resident;self.native_c_parent=resident.parent
        # Actual compound cut, independent of corrupt pipeline/native words.
        pulse.cut=True;pulse.reset_control_inhibit=self.reset_interlock
        pulse.maintenance_control_enabled=False
        setter.cut=True;setter.reset_control_inhibit=self.reset_interlock
        self.cells=pulse.energy+pulse.trigger_energy+[pulse.reset_source_reserve,pulse.reset_reserve,setter.reset_reserve]
        self.initial=[(c.stock,c.delivered_input,c.spent,c.dumped) for c in self.cells]

    def _event(self,name):
        self.trace.append(dict(event=name,time=self.time,clamp=self.q,activation=self.activation))

    def _arrive(self,code):
        if code==self.mode:return
        self.mode=code;self._event('receiver-mode-'+str(code))
        # Contacts operate on the actual state, even in malformed partial
        # histories. There is no prior-stage-completion test here.
        if code==0:self.entry_clear_remaining=f.CONTROL_TAIL
        if code==3:
            self._commutate()
        if code==6:
            self._start_clear()
        if code==9 and self.q>=PREPARED_AT and not self.abort_mask:
            self.s.cut=False;self.s.native_inhibit=False
        if code==10 and self.activation>=ARM and not self.abort_mask:
            self.receiver_armed=True;self.p.reset_motor_owner=False;self.p.native_inhibit=False
            self.p.maintenance_control_enabled=False

    def _commutate(self):
        p=self.p;s=self.s
        if 'source-commutation' not in self.started and p.reset_source_reserve.debit(128):
            self.started.add('source-commutation');p.maintenance_control_enabled=True
        if 'receiver-commutation' not in self.started and p.reset_reserve.debit(128):
            self.started.add('receiver-commutation');p.ep_charging=self.charger_bypass
            p.native_inhibit=True;p.reset_motor_owner=True;p.reset_driver_disconnected=False
        if 'setter-commutation' not in self.started and s.reset_reserve.debit(128):
            self.started.add('setter-commutation');s.native_inhibit=True

    def _low(self):
        return all(c.stock<=f.DUMP_FLOOR for c in self.p.energy) and self.s.energy<=f.DUMP_FLOOR

    def _start_clear(self):
        if self.clear_paid or not self._low() or not self.p.native_inhibit or not self.s.native_inhibit:return
        p=self.p;s=self.s
        # A real low-energy/write-inhibit guard. No image, truth or completed
        # field predicate is tested. Each paid debit has its own retained state.
        for label,cell,work in (('source-fanout',p.reset_source_reserve,384),
                                ('receiver-fanout',p.reset_reserve,384),
                                ('setter-fanout',s.reset_reserve,2048)):
            if label not in self.started:
                if not cell.debit(work):return
                self.started.add(label)
        for slot in range(3):
            outcome=p.abort_pending(slot)
            if outcome not in ('absent','aborted'):return
        self.clear_paid=True

    def _ordinary_flow(self,dt):
        p=self.p
        if p.reset_motor_owner:p.advance_reset_with_charge(dt,connected=self.reset_charging)
        else:
            p.flow(dt,mode='jam');p.reset_reserve.charge(dt,connected=self.reset_charging)
        p.reset_source_reserve.charge(dt,connected=self.reset_charging)
        self.s.reset_reserve.charge(dt,connected=self.reset_charging)

    def _entry_control_clear(self):
        # The held CUT rail drives a fixed paid constant-zero control path.
        # This clears only the maintenance sequencer, never old pulse/control
        # registers, setter data, parents or work stocks. Its40 actual bits are
        # within the pre-existing64-per-channel/512-per-setter reset allocation.
        self.started.clear();self.clear_i=0;self.pulse_i=0
        self.clear_credit=Q(0);self.pulse_credit=Q(0);self.abort_credit=Q(0)
        self.clear_paid=False;self.parent_aborted=False
        self.dump_done=[False]*3;self.setter_dump_done=False
        self.control_entry_clears+=1

    def _dump_cell(self,c,dt,i):
        # A one-use physical low-floor dump; a bypassed charger may refill
        # after that stop. Its input is real work, not a zero-stock assignment.
        rate=c.capacity/f.RESET_REFILL if self.charger_bypass else Q(0)
        power=c.capacity/f.DUMP_TIME
        active=Q(0) if self.dump_done[i] else min(dt,max(Q(0),(c.stock-f.DUMP_FLOOR)/(power-rate)))
        incoming=rate*active;loss=power*active
        c.stock+=incoming-loss;c.delivered_input+=incoming;c.upstream_input+=2*incoming;c.dumped+=loss
        if c.stock<=f.DUMP_FLOOR:self.dump_done[i]=True
        rest=dt-active
        if rest and rate:
            incoming=min(c.capacity-c.stock,rate*rest)
            c.stock+=incoming;c.delivered_input+=incoming;c.upstream_input+=2*incoming

    def _consume(self,dt):
        p=self.p;s=self.s;dt=exact(dt)
        if self.mode in (0,1,2,3,15):
            if self.mode==0 and self.entry_clear_remaining is not None:
                self.entry_clear_remaining=max(Q(0),self.entry_clear_remaining-dt)
                if self.entry_clear_remaining==0:
                    self._entry_control_clear();self.entry_clear_remaining=None
            self._ordinary_flow(dt)
            if self.mode==3:self._commutate()
        elif self.mode in (4,5,6,7,8,9):
            # Reset charging is intentionally absent while the paid driver,
            # clear and abort work share these reserves. It resumes at refill.
            if self.mode in (8,9):
                p.advance_reset_with_charge(dt,connected=self.reset_charging)
                p.reset_source_reserve.charge(dt,connected=self.reset_charging)
                s.reset_reserve.charge(dt,connected=self.reset_charging)
            else:p.flow(dt)
            if self.mode==4 and p.native_inhibit:
                for i,c in enumerate(p.energy):self._dump_cell(c,dt,i)
                loss=min(max(Q(0),s.energy-f.DUMP_FLOOR),f.SET_ENERGY/f.DUMP_TIME*dt)
                s.energy-=loss;self.setter_dumped+=loss
            if self.mode==6:
                self._start_clear()
                if self.clear_paid:
                    self.clear_credit+=dt*2**20;self.pulse_credit+=dt*2**20
                    while self.pulse_credit>=1 and self.pulse_i<1024:
                        i=self.pulse_i
                        owner=p.reset_reserve if i<768 else p.reset_source_reserve
                        if not owner.debit(2):break
                        self.raw.clear_native_bit(i)
                        self.pulse_i+=1;self.pulse_credit-=1
                    while self.clear_credit>=1 and self.clear_i<4096:
                        i=self.clear_i
                        if not s.reset_reserve.debit(2):break
                        self.raw.setter_bits[i]=0
                        if i==0:s.parent_live=False
                        self.clear_i+=1;self.clear_credit-=1
                    if self.clear_i==4096 and self.pulse_i==1024:
                        for label,cell in (('receiver-reaction',p.reset_reserve),('source-reaction',p.reset_source_reserve),('setter-reaction',s.reset_reserve)):
                            if label not in self.started and cell.debit(1):self.started.add(label)
                        p.withdrawal_owner=None
            if self.mode==7 and self.clear_i==4096 and not self.parent_aborted:
                self.abort_credit+=dt*2**20
                if self.abort_credit>=64 and s.reset_reserve.debit(1024):
                    s.returned=False;s.generator=None;s.latched=None;s.parent_record=None
                    s.parent_live=False;s.phase='recharging';self.parent_aborted=True
            if self.mode in (8,9):
                p.ep_charging=True;p.refill(dt)
                before=s.energy;s.recharge(dt);self.setter_delivered+=s.energy-before
        # An invalid four-bit word requests no paid native reset action. The
        # actual source cut remains in force; retained ordinary force persists.
        else:self._ordinary_flow(dt)
        self.time+=dt
        self.q+=self.clamp_speed*dt;self.activation+=self.activation_speed*dt

    def advance(self,to_q,duration):
        to_q=exact(to_q);duration=exact(duration);contact(to_q)
        if duration<0 or to_q<self.q or to_q-self.q>VMAX*duration:
            raise ValueError("Not an admitted forward clamp segment")
        if duration==0:
            if to_q!=self.q:raise ValueError("Motion without time")
            return
        speed=(to_q-self.q)/duration
        self.clamp_speed=speed;self.activation_speed=Q(0)
        if speed==0:
            self._transport(duration,contact(self.q));return
        while self.q<to_q:
            right=min(to_q,next((b['right'] for b in BANDS if b['right']>self.q),CLAMP_END))
            code=contact(self.q);dt=(right-self.q)/speed
            self._transport(dt,code)
            self.q=right
        self.clamp_speed=Q(0)
        # A contact crossing changes the input rail, not the remote latch.

    def _transport(self,dt,code):
        if self.abort_mask:code=15  # Old pipeline contents still take real time to flush.
        if self.control_powered:self.line.flow(dt,code,self._consume,self._arrive)
        else:self._consume(dt)  # Actual retained controls, no fictitious clock progress.

    def abort(self):
        self.abort_mask=True;self.p.cut=True;self.s.cut=True
        self.p.reset_control_inhibit=True;self.s.reset_control_inhibit=True
        self.p.maintenance_control_enabled=False;self._event('actual-abort-cut')
        # No rewind, field erasure, parent return or store reset is invented.

    def activation_to(self,to_position,duration):
        to_position=exact(to_position);duration=exact(duration)
        if not 0<=self.activation<=to_position<=WARM or duration<0 or to_position-self.activation>VMAX*duration:
            raise ValueError("Invalid activation segment")
        speed=(to_position-self.activation)/duration if duration else Q(0)
        self.activation_speed=speed;self.clamp_speed=Q(0)
        if speed==0:
            self._transport(duration,10 if self.activation>=ARM else 9)
            return
        while self.activation<to_position:
            right=min(to_position,next((x for x in (POWER,ARM,DRIVER,WARM) if x>self.activation),WARM))
            self._transport((right-self.activation)/speed,10 if self.activation>=ARM else 9)
            self.activation=right
            if right==POWER:self.cpu_on=True;self.native_c_launch=True
            if right==DRIVER and not self.abort_mask:
                if self.p.reset_source_reserve.debit(32):
                    self.p.cut=False;self.p.reset_control_inhibit=False
                    self.s.reset_control_inhibit=False;self.source_opened=True
        self.activation_speed=Q(0)
        # CPU instruction execution is separately supplied; no scan/READY test
        # is performed at these physical contacts.

    def issue_setting(self,args):
        return self.s.issue(args) if self.cpu_on else 'power-off'

    def certificate(self):
        p=self.p;s=self.s
        return (p.force==0 and p.slots==[None]*3 and p.pending==[None]*3
                and all(x.stock==x.capacity for x in p.energy+p.trigger_energy)
                and p.reset_source_reserve.stock==p.reset_source_reserve.capacity
                and p.reset_reserve.stock==p.reset_reserve.capacity
                and s.reset_reserve.stock==s.reset_reserve.capacity
                and self.clear_i==4096 and self.pulse_i==1024 and self.parent_aborted and not s.parent_live
                and s.parent_record is None and s.phase=='ready' and s.energy==f.SET_ENERGY
                and p.cut and p.native_inhibit and not s.cut and not s.native_inhibit)

    def conservation(self):
        for c,(stock,received,spent,dumped) in zip(self.cells,self.initial):
            need(c.stock==stock+c.delivered_input-received-(c.spent-spent)-(c.dumped-dumped),"Physical work cell imbalance")
        need(self.s.energy==self.initial_setter_stock+self.setter_delivered-self.setter_dumped-self.setter_spent,
             "Setter work stock imbalance")
        need(self.p.motor_input==self.p.motor_output+self.p.motor_heat,"Motor work/heat imbalance")

def fixture(*,stock=Q(17),reset_stock=Q(0),owner=False,failed=False,**kwargs):
    p=f.PulseSelector(slots=[[1,f.PULSE_COUNTER_CAP],[-1,f.PULSE_COUNTER_CAP],None],
                      force=f.FORCE,initial_energy=(stock,stock,f.PULSE_ENERGY),
                      initial_reset_energy=(Q(0),reset_stock),reset_motor_owner=owner,
                      reset_actuator_failed=failed)
    for i in range(3):
        need(p.capture(i,-1)=='latched',"Old trigger capture")
        p.trigger_energy[i].debit(f.TRIGGER_ENERGY-17)
    s=f.SettingWriter(tuple('actual-neighbor-'+str(i) for i in range(40)))
    s.held[f.Destination(s.targets[0],0,0)]=-1
    parent=(0,0,1,1);need(s.issue(parent)=='latched',"Old setter parent")
    for _ in range(20):s.step()
    s.energy=Q(17)  # Initial state after an earlier accounted loss.
    resident=ResidentWord('actual-source-body',0,37,[Q(-1)]*192,('native-word-parent',37,1))
    return CamBank(p,s,resident,**kwargs)

def finish(bank,speed):
    bank.advance(PREPARED_AT,(PREPARED_AT-bank.q)/speed)
    # The last local release contact takes its own physical propagation time.
    bank.advance(PREPARED_AT,CONTROL_DELAY)
    return bank

def local_checks():
    cases=[]
    for speed in (Q(1),Q(21,20),VMAX):
        for owner,reset_stock in ((False,Q(0)),(True,Q(0)),(True,Q(4000)),(True,Q(12288))):
            a=fixture(owner=owner,reset_stock=reset_stock,controller_residue=2**40-1)
            held=dict(a.s.held);parent=a.s.parent_record
            resident=a.resident;resident_values=list(resident.coordinates);native_parent=resident.parent
            finish(a,speed)
            need(a.certificate(),"Fresh traversal failed to form actual endpoint state")
            need(a.s.held==held and a.old_parent is parent and a.resident is resident
                 and resident.coordinates==resident_values and resident.parent is native_parent,
                 "Reset erased held effects or the separate resident native parent")
            need(a.p.capture(0,1)=='cut' and a.p.clock_edge(0)=='inhibited-wait'
                 and a.issue_setting((0,0,1,-1))=='power-off',"Premature source launch")
            a.conservation()
            cases.append(dict(speed=speed,initial_reset_owner=owner,initial_reset_stock=reset_stock,
                elapsed=a.time,source_reset_spent=a.p.reset_source_reserve.spent,
                receiver_reset_spent=a.p.reset_reserve.spent,setter_reset_spent=a.s.reset_reserve.spent,
                additional_control_delivered_work=a.line.delivered_work,
                prepared=True,partial_setting_preserved=True,old_parent_consumed=True,
                actual_trace=a.trace if speed==VMAX and owner and reset_stock==4000 else None))
    # Slow and stopped motion cannot shorten dwell; one retained stop is also
    # an explicit control/holding-work interval, not a free skipped duration.
    stopped=fixture();stopped.advance(Q(1105),Q(1105));stopped.advance(Q(1105),Q(1234))
    finish(stopped,Q(1));need(stopped.certificate(),"A refill stop destroyed the state proof");stopped.conservation()
    mixed=[]
    for j in range(16):
        a=fixture(control_words=[(7*j+3*i)%16 for i in range(8)],
            controller_residue=(7919*(j+1)*1000003)%(2**40),
            owner=bool(j%2),reset_stock=Q((7919*j)%12289))
        for i,b in enumerate(BANDS):
            speed=Q(1000+(17*j+19*i)%101,1000)
            a.advance(b['right'],(b['right']-a.q)/speed)
        a.advance(PREPARED_AT,CONTROL_DELAY)
        need(a.certificate(),"Mixed speed/corrupt initial control prefix failed")
        a.conservation();mixed.append(a.time)
    partial=fixture(q=CUTOFF-1);partial.advance(CUTOFF,Q(10,11));partial.advance(CUTOFF,2)
    need(not partial.certificate() and partial.clear_i==0 and partial.s.parent_record is not None,
         "A partial entry inherited nonexistent reset history")
    unpowered=fixture(reset_charging=False);finish(unpowered,VMAX)
    need(not unpowered.certificate() and any(unpowered.raw.native_bits),"Unfunded reset became a clean state")
    unpowered.conservation()
    clockless=fixture(control_powered=False);finish(clockless,VMAX)
    need(not clockless.certificate() and clockless.line.edges==0,"Unpowered control line made progress")
    clockless.conservation()
    failed=fixture(failed=True,reset_stock=Q(12288));finish(failed,VMAX)
    need(not failed.certificate(),"A failed reset actuator was silently granted the intact episode")
    failed.conservation()
    uncut=fixture(reset_interlock=False);uncut.advance(Q(111110),Q(111110))
    need(uncut.p.native_reset_request(True)=='accepted',"Missing native-control bypass countercase")
    uncut.conservation()
    bypass=fixture(charger_bypass=True,stock=f.PULSE_ENERGY);finish(bypass,VMAX)
    need(not bypass.certificate(),"Bypassed recharge acquired a low-energy certificate");bypass.conservation()
    cut=fixture();cut.advance(Q(112330),Q(112330));cut.advance(Q(112330),CONTROL_DELAY)
    need(0<cut.clear_i<4096 and not cut.s.parent_live and cut.s.parent_record is cut.old_parent,
         "The partial-clear/retained-parent witness disappeared")
    before=(cut.p.force,dict(cut.s.held),cut.s.parent_record,list(cut.raw.setter_bits),cut.clear_i)
    cut.abort();need(cut.p.cut and cut.s.cut and before==(cut.p.force,dict(cut.s.held),cut.s.parent_record,list(cut.raw.setter_bits),cut.clear_i),
                    "Abort erased physical effects or old parent")
    no_scan=finish(fixture(),VMAX)
    no_scan.activation_to(DRIVER,DRIVER/VMAX)
    old_value=no_scan.s.held[f.Destination(no_scan.s.targets[0],0,0)]
    need(no_scan.p.trigger(0,old_value)=='active' and old_value==-1,
         "A hidden scan-completion gate prevented the actual wrong-setting branch")
    a=finish(fixture(),VMAX)
    a.activation_to(POWER,(POWER-a.activation)/VMAX)
    need(a.p.cut and a.issue_setting((0,0,1,-1))=='latched',"Setter/trigger gates not distinct")
    before=a.s.logical_cost
    while a.s.phase=='pending':a.s.step()
    a.setter_spent+=a.s.logical_cost-before
    old=a.s.energy;a.s.recharge(f.SET_REFILL);a.setter_delivered+=a.s.energy-old
    a.activation_to(ARM,(ARM-a.activation)/VMAX)
    need(a.p.cut and not a.receiver_armed,"Remote arm happened without propagation")
    a.activation_to(DRIVER,(DRIVER-a.activation)/VMAX)
    need(a.receiver_armed and a.source_opened and a.p.trigger(0,-1)=='active',"Real local ACT contact did not enable source")
    a.p.flow(1000);need(a.p.force==-f.U_BIT,"New actual held setting did not reach the motor");a.conservation()
    return dict(fresh_cases=cases,stopped_elapsed=stopped.time,
        mixed_initial_control_cases=len(mixed),mixed_duration_min=min(mixed),mixed_duration_max=max(mixed),
        interrupted_near_cutoff=dict(remaining=Q(10,11),formed=False,old_parent_retained=True),
        missing_charge='actual retained/unfunded state',charger_bypass='low guard or formation fails',
        failed_reset_actuator='no intact episode; actual work-floor and partial recharge retained',
        missing_control_power='no control edges or state formation',
        missing_reset_interlock='old native reset request actually accepted after precharge',
        omitted_scan='physical ACT still opens and an old held setting triggers; no READY oracle',
        partial_abort='cuts launches; no fictitious clearing or automatic successful rewind',
        actual_partial_setter_clear_bits=cut.clear_i,
        setter_release_before_cpu_does_not_launch=True,receiver_arm_does_not_trigger=True,
        full_scan_not_simulated=True,all_clock_interleavings_not_enumerated=True)

def line_checks():
    cases=0
    for initial in range(16):
        for target in range(10):
            a=ControlLine([initial]*8)
            for _ in range(8):a.tick(target)
            need(a.words==[target]*8,"Control prefix retained old register content")
            cases+=1
    a=ControlLine(list(range(8)),[True]*8)
    outputs=[a.tick(9) for _ in range(8)]
    need(outputs[:7]==[6,5,4,3,2,1,0] and outputs[7]==9,"Old control prefixes were erased")
    # Complete transition bound, including actual40-bit dispatch entry clear.
    work=2*(40+4+12+40)
    need(work<=CONTROL_PRICE and 8/CONTROL_MIN+8*CONTROL_STEP<=CONTROL_DELAY,"Control price/latency failed")
    need(40+4+8<=CONTROL_BITS,"Finite transport/control storage exceeds installed count")
    return dict(initial_target_cases=cases,old_pipeline_outputs=outputs,
                native_work_bound=work,priced_work_per_endpoint=CONTROL_PRICE,
                allocated_bits_per_pair=CONTROL_BITS,used_bits_upper=52,
                edges_to_flush=8,clock_min=CONTROL_MIN,clock_max=CONTROL_MAX,
                max_delay=CONTROL_DELAY,each_native_copy_latency=CONTROL_STEP,dispatch_entry_clear_bits=40,
                dispatch_entry_clear_work_is_in_price=True,clock_phase_is_not_global_time=True)

def arithmetic(point,geometry):
    # One extra propagation allowance releases the local setter after the
    # final refill contact. Taking it explicitly avoids an endpoint tie.
    upper=R+PREPARED_AT/MU+CONTROL_DELAY
    lower=PREPARED_AT/VMAX
    need(upper<OLD_POOL,"Position-driven preparation exceeds existing allowance")
    full=BOOT+SCAN+upper+2098153+Q(314572800000,829)
    need(full<CUTOFF/VMAX,"Fresh writing cannot finish before cutoff")
    scan_slack=(DRIVER-POWER)/VMAX-BOOT-SCAN
    need(scan_slack>0 and (DRIVER-ARM)/VMAX>CONTROL_DELAY,"ACT gate can overtake data or remote arm")
    need(BOOT+SCAN+CONTROL_DELAY<(ARM-POWER)/VMAX,"Receiver arm precedes full actual-C scan")
    # New circuits are billed additively. No unspecified old frontend headroom
    # or zero-cost reuse is assumed. N includes two local setter controls.
    N=4*f.DEGREE*f.L+2
    # One actual unfinished bounded job at each endpoint can overlap an
    # arbitrary interval's left boundary, in addition to newly launched work.
    work_burst=4*CONTROL_PRICE*N;work_rate=2*CONTROL_PRICE*N*CONTROL_MAX
    holding=Q(CONTROL_BITS*N,1024)
    upstream_burst=2*work_burst
    upstream_rate=2*work_rate+holding
    old=point['resources'];Dn=Q(old['upstream_rate'])+upstream_rate
    bn=Q(old['upstream_burst'])+upstream_burst
    U=Q(old['upstream_capacity']);reserve=U-bn-2*Dn
    need(Dn<Q(old['unchanged_supply_rate']) and reserve>upstream_burst+1,"New control work lacks unchanged-supply funding")
    # One step lasts at least2^-20q; its actual finite work port has this hard
    # peak. No new recoverable store is installed under the finite-word law.
    peak=2*N*CONTROL_PRICE*2**20+holding
    combined=Q(point['thermal']['new_native_peak_fit'])+peak
    need(41*combined<2**93 and 4*41*combined<2**94,"New local control exceeds retained gross work ratings")
    # Additional contact/transport reaction is added, not borrowed from an
    # already fully allocated old reset actuator. One joint endpoint column
    # per channel has l1 effort at most u/1000 during its paid switching job.
    added_reaction=Q(point['mechanics']['reset_reaction_bound'])
    total_reaction=(Q(point['mechanics']['field_reaction'])+2*f.NATIVE_FORCE
                    +2*added_reaction)
    need(total_reaction<f.REACTION,"New control force exceeds the actual joint .324 class")
    relative=f.BIT_SPEED+22*Q(point['mechanics']['W_over_tau'])+VMAX
    control_mechanical_work=f.U_BIT/1000*relative*Q(128,2**20)
    need(192+control_mechanical_work<CONTROL_PRICE,"Control bit/port work omitted")
    return dict(bands=BANDS,prepared_position=PREPARED_AT,
        source_fragment_sum=f.reformation_bounds()['prepared_bound'],
        physical_minimum_to_last_contact=lower,physical_prepared_upper=upper,
        upper_includes_one_normal_R_and_release_propagation=True,
        old_pool_slack=OLD_POOL-upper,full_fresh_write_bound=full,
        earliest_cutoff=CUTOFF/VMAX,cutoff_slack=CUTOFF/VMAX-full,
        boot_plus_scan=BOOT+SCAN,power_to_trigger_scan_slack=scan_slack,
        receiver_arm_position=ARM,trigger_enable_position=DRIVER,
        arm_propagation_slack=(DRIVER-ARM)/VMAX-CONTROL_DELAY,
        earliest_gate_is_not_latest_gate=True,
        resources=dict(channel_and_setter_pairs=N,added_control_bits=CONTROL_BITS*N,
            delivered_work_burst=work_burst,delivered_work_rate=work_rate,
            added_upstream_burst=upstream_burst,added_upstream_rate=upstream_rate,
            added_holding_rate=holding,upstream_rate=Dn,upstream_burst=bn,
            unchanged_upstream_capacity=U,usable_reserve_lower=reserve,
            unchanged_supply_rate=Q(old['unchanged_supply_rate']),added_hard_peak=peak,
            combined_native_peak=combined,additional_recoverable_capacity=0,
            ordinary_E_T_backfeed=0,added_joint_reaction=added_reaction,
            complete_joint_reaction=total_reaction,control_mechanical_work_per_step=control_mechanical_work,
            retained_conservative_reaction=Q(81,250)),
        control_demand_is_exported_to_single_U_account=True,full_U_flow_not_simulated=True,
        source_boundaries=dict(fresh_monotone_traversal=True,actual_U_charging=True,
            incoming_g34_b6_is_separate=True,resident_native_C_tail_is_separate=True,
            arbitrary_entry_return=False,program_admission=False))

def rejection_checks():
    rejected=0
    for fn in (lambda:contact(True),lambda:contact(-1),lambda:contact(CLAMP_END+1),
               lambda:ControlLine([0]*7),lambda:ControlLine([True]*8),
               lambda:ControlLine(valid=[1]*8),
               lambda:ControlLine(until_edge=0),lambda:fixture(q=True),
               lambda:fixture(reset_charging=1),lambda:fixture().advance(2,1),
               lambda:fixture(controller_residue=True),lambda:fixture(controller_residue=2**40),
               lambda:fixture().advance(-1,1),lambda:fixture().activation_to(WARM+1,WARM+1)):
        try:fn()
        except (ValueError,AssertionError):rejected+=1
        else:raise AssertionError("Malformed source input was accepted")
    return rejected

def serial(value):
    if isinstance(value,Q):return str(value)
    if isinstance(value,dict):return {str(k):serial(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [serial(v) for v in value]
    return value

def generate():
    need(not sys.flags.optimize and sys.version_info[:2]==(3,12),"Unoptimized Python3.12 required")
    hashes,field_point,geometry=bindings()
    return dict(scope="fresh local position/contact construction with retained state; no source or recurrent admission",
        base=BASE,field_worker_origin=FIELD_WORKER,frozen_inputs_sha256_lf=hashes,
        sources_sha256_lf={n:digest((HERE/n).read_text(encoding='utf-8-sig')) for n in ('cam_reformation.py','CAM-REFORMATION.md')},
        arithmetic=arithmetic(field_point['point'],geometry),control_line=line_checks(),
        executions=local_checks(),malformed_inputs_rejected=rejection_checks(),
        residuals=["full local controller/parent and legacy operation refinement remains upstream",
            "actual physical placement, control fault domains and bounded interlock support",
            "same-history maintained incoming donor field and ordinary mechanical helper windows",
            "resident native C power/no-new-launch and pending word refinement",
            "complete interrupted-entry itinerary through subsequent fresh traversals of both banks",
            "full heterogeneous clock/hybrid interleaving refinement; executed traces use clock8",
            "source-to-core, regional density, whole-history resource and family admission"],
        full_source_admitted=False,goal_complete=False)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    modes=parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    args=parser.parse_args();record=serial(generate());path=HERE/'cam_reformation_results.json'
    if args.write:path.write_text(json.dumps(record,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:need(json.loads(path.read_text(encoding='utf-8-sig'))==record,"Cam record or binding differs")
    print('PASS fresh cam/reformation construction; source admission and interrupted return remain open')

if __name__=='__main__':main()
