"""Raw two-bank cycle prototype. No image/READY/permitted/rearm success opcode."""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from fractions import Fraction as F
from hashlib import sha256
from math import ceil
from pathlib import Path
import json
import sys

if sys.flags.optimize:
    raise RuntimeError("Unoptimized Python is required")

HERE=Path(__file__).resolve().parent
PHASES=("isolate_cut","retract_activation","open_clamp","retract_reset",
        "drain","seat","copy_clamp","reconnect","scan_activate",
        "blend","retire","normalize","commit")
LI,STORE,ADDI,BLT,JUMP,OUT,IN,ADD,SUB,HALF,MULI,CLIP,STOREC=range(1,14)


def word(op,a=0,b=0,c=0):return (op<<24)|(a<<16)|(b<<8)|c
def imm(op,a,value):return (op<<24)|(a<<16)|(value&65535)
def signed(value):return value-65536 if value>=32768 else value


def program(q=4,maintenance_ports=2):
    p=[imm(LI,0,0),imm(LI,1,0),imm(LI,2,q),word(STORE,0,1),imm(ADDI,0,1),
       word(BLT,0,2,3),word(JUMP,0,0,7),imm(LI,0,0),imm(LI,1,0),
       imm(LI,2,maintenance_ports+2),word(OUT,0,1),imm(ADDI,0,1),word(BLT,0,2,10)]
    main=len(p)
    p.append(imm(LI,3,20))
    for port in range(maintenance_ports):p.extend([imm(LI,0,port),word(OUT,0,3)])
    p.extend([word(IN,4,0),word(IN,5,1),word(ADD,6,4,5),word(HALF,6),
              imm(MULI,6,2),imm(ADDI,6,-40),word(CLIP,6,30,90),
              imm(LI,0,maintenance_ports),word(OUT,0,6),word(SUB,7,4,5),
              word(HALF,7),imm(MULI,7,2),imm(ADDI,7,-40),word(CLIP,7,30,90),
              imm(LI,0,maintenance_ports+1),word(OUT,0,7),word(JUMP,0,0,main)])
    return tuple(p),main


@dataclass
class Body:
    identity:int
    code:list[int]
    work:list[int]
    regs:list[int]=field(default_factory=lambda:[99]*8)
    pc:int=0
    outputs:list[int]=field(default_factory=lambda:[-22,-22,-100,-100])
    powered:bool=False
    halted:bool=False
    instruction_steps:int=0
    self_writes:int=0

    def step(self,incoming):
        if self.halted:return None
        if not 0<=self.pc<len(self.code):self.halted=True;return None
        value=self.code[self.pc]
        op,a,b,c=(value>>24)&255,(value>>16)&255,(value>>8)&255,value&255
        immediate=signed(value&65535)
        self.pc+=1;self.instruction_steps+=1
        if a>=len(self.regs):self.halted=True;return None
        if op==LI:self.regs[a]=immediate%65536
        elif op==STORE:
            if b<len(self.regs) and self.regs[a]<len(self.work):self.work[self.regs[a]]=self.regs[b]
        elif op==ADDI:self.regs[a]=(self.regs[a]+immediate)%65536
        elif op==BLT:
            if b<len(self.regs) and self.regs[a]<self.regs[b]:self.pc=c
        elif op==JUMP:self.pc=c
        elif op==OUT:
            if b<len(self.regs):return self.regs[a],signed(self.regs[b])
        elif op==IN:self.regs[a]=incoming[b%len(incoming)]%65536
        elif op==ADD:
            if max(b,c)<len(self.regs):self.regs[a]=(self.regs[b]+self.regs[c])%65536
        elif op==SUB:
            if max(b,c)<len(self.regs):self.regs[a]=(self.regs[b]-self.regs[c])%65536
        elif op==HALF:self.regs[a]=(signed(self.regs[a])//2)%65536
        elif op==MULI:self.regs[a]=(signed(self.regs[a])*immediate)%65536
        elif op==CLIP:self.regs[a]=max(b,min(c,signed(self.regs[a])))
        elif op==STOREC:
            if b<len(self.regs) and self.regs[a]<len(self.code):
                self.code[self.regs[a]]=self.regs[b];self.self_writes+=1
        else:self.halted=True
        return None


@dataclass
class Helper:
    index:int
    reference:list[int]
    cursor:int=99
    completed:bool=True
    joined:bool=True
    scan_bay:int=99
    scan_address:int=99
    scan_match:bool=False
    accepted:list[bool]=field(default_factory=list)
    selected:int|None=None
    verify_address:int=0
    abort:bool=False
    remaining:int=0
    watch_context:tuple|None=None
    last_phase:int=-1
    last_upper:int=0
    exiting:bool=False
    normal_seen:bool=False
    exit_remaining:int=0

    def clear(self,bays):
        self.cursor=self.scan_bay=self.scan_address=self.verify_address=0
        self.completed=self.joined=False;self.scan_match=True
        self.accepted=[False]*bays;self.selected=None


class Cycle:
    """A single host driven by faultable neighboring producer banks.

    Positions are tenths of a stroke unit; forces are tenths of force units.
    The local policy sees only delayed views, its memory and passive cell reads.
    """
    def __init__(self,bays=5,schedule=0,quiet_watch=False,cold_start=False,
                 bypass_disabled=False,driver_early=False,reconnect_unsafe=False,
                 injected_inputs=None, reject_abort=True, legacy_partial_abort=False, legacy_phase_gated_cam=False):
        self.bays=bays;self.image,self.main=program()
        self.injected_inputs=injected_inputs or (lambda tick,side:(100,0))
        self.reject_abort=reject_abort;self.legacy_partial_abort=legacy_partial_abort
        self.legacy_phase_gated_cam=legacy_phase_gated_cam
        self.length=len(self.image);self.J=5;self.D=3;self.E=2;self.qwords=4
        self.theta=30;self.cap=10;self.noise=1;self.force=20;self.badcap=22
        self.lag=self.E+2*self.J+2*self.D
        self.guard=self.lag+4;self.segment=self.guard+1
        self.total=2*len(PHASES)*self.segment
        self.reset_limit=(self.E+self.J+2*self.D+3)*10
        self.cut_limit=60;self.seat_limit=30
        self.detect=5+2*2+2*10*self.E
        self.cutoff=(ceil(F(self.detect+10*(2*self.J+2*self.D),10))+1)*10
        self.clamp_limit=self.cutoff+60
        self.horizon=self.E+2*self.J+2*self.D+6+1
        self.iso_limit=20*self.horizon*10
        self.blend_limit=80*self.horizon*10
        self.power_max=2*bays+6+20
        self.reserve_cap=self.power_max*(self.iso_limit//10+4*self.lag+6)+1
        self.copy_bound=(3*self.length+2)*self.J+(2*self.length+2)*self.D
        self.scan_bound=(bays*self.length+2)*self.J
        self.progress_rate=10*(bays+2*self.power_max+10)
        # The observable rank includes reserve discharge. Its minimum non-stalled
        # rate is one unit per quantum, so the full reservoir is not an invisible
        # wait. The uncertainty band, serial work and settling are all charged.
        self.idle_bound=max(self.copy_bound,self.scan_bound)+2*self.progress_rate*self.E+4*self.lag+20
        self.watch=ceil(F(101,100)*self.idle_bound)+1
        # A pre-existing bank may make one delayed refresh from its old mark even
        # during a later near-flat rank interval. Cover TWO timer lengths.
        self.local_work=2*self.watch+self.E+2*self.J+2*self.D+2
        self.prefix_steps=3*self.qwords+4+3+3*4+2*len(self.image)
        self.ready_bound=3*self.prefix_steps+2*self.D+10
        self.power_at=(self.scan_bound+self.E+2*self.J+2*self.D+5)*10
        self.driver_at=self.power_at+(self.ready_bound+2*self.D+1)*10
        self.warm_at=self.driver_at+(self.local_work+2)*10
        self.abort_limit=(self.E+2*self.J+2*self.D+5)*10
        self.cam=0;self.mode=0;self.anchor=0;self.blend=0
        self.abort_full=False;self.abort_milestones=[]
        self.exit_wait=self.E+2*self.J+2*self.D+2
        self.cut=[0,self.cut_limit];self.clamp=[self.clamp_limit,self.clamp_limit]
        self.reset=[self.reset_limit,self.reset_limit];self.iso=[0,0];self.shunt=[0,self.iso_limit]
        self.activation=[[0]*bays for _ in range(2)]
        self.activation[0][0]=0 if cold_start else self.warm_at
        self.activation[1][0]=self.warm_at
        self.seats=[[self.seat_limit]*bays for _ in range(2)]
        self.energy=[self.reserve_cap if not cold_start else 0,0]
        self.bodies=[[Body(side*bays+j,list(self.image) if side==0 and j==0 else [0]*self.length,[77]*self.qwords)
                      for j in range(bays)] for side in range(2)]
        if not cold_start:
            hot=self.bodies[0][0];hot.work=[0]*self.qwords;hot.regs=[0]*8;hot.pc=self.main
            hot.outputs=[20,20,60,60];hot.powered=True
        self.helpers=[Helper(j,list(self.image)) for j in range(bays)]
        self.bad={0};self.periods=[2+(j+schedule)%4 for j in range(bays)]
        self.offsets=[(j+2*schedule)%self.periods[j] for j in range(bays)]
        self.outputs=[{} for _ in range(bays)];self.packets=[];self.output_packets=[]
        self.history=[];self.tick=0;self.work_charged=0;self.energy_supplied=0;self.energy_spent=0;self.energy_bleed=0;self.initial_energy=sum(self.energy)
        self.commits=[];self.abort_entries=[];self.starts=[];self.driver_entries=[];self.cut_events=[]
        self.events=[];self.legacy_attempts=0;self.legacy_rejected=0;self.legacy_pending=[];self.legacy_delivered=[]
        self.retained_knowledge={"old-code","old-credentials"}
        self.effective=[[0]*4 for _ in range(2)];self.tail=[[0]*4 for _ in range(2)];self.tail_left=[0,0]
        self.driver_on=[False,False];self.report_deliveries=0
        self.quiet_watch=quiet_watch;self.bypass_disabled=bypass_disabled
        self.driver_early=driver_early;self.reconnect_unsafe=reconnect_unsafe
        self.violations=[];self.power_gaps=[];self.selection_history=[]
        self.phase_entries=[];self.last_context=None;self.minimum_world=[100,100]
        self.fresh_driver_violations=[];self.side_cost=[0,0];self.bypass_cost=0
        self.freeze_witnesses=[];self.min_keeper_execution=None;self.observed_progress=[0,0]
        self.application_permission_violations=[];self.attenuation_entries=[]

    def context(self):
        block=self.cam//self.segment
        return block//len(PHASES),block%len(PHASES),self.cam%self.segment

    def raw_power(self,side,j):
        # A full quantum of stored-power execution is reserved before execution.
        # Partial source current varies continuously with the shunt; this test
        # is the conservative brownout threshold, not another opening contact.
        source=(self.cut[side]<20 and self.shunt[side]==0) or self.energy[side]>=self.power_max
        return self.activation[side][j]>=self.power_at and source

    def bank_outputs(self,side):
        totals=[0]*4
        for body in self.bodies[side]:
            if body.powered:
                totals=[a+b for a,b in zip(totals,body.outputs)]
        return [max(-22,min(22,v)) if i<2 else max(-100,min(100,v)) for i,v in enumerate(totals)]

    def draw(self,side):
        return 2*sum(b.powered for b in self.bodies[side])+sum(ceil(F(abs(v),10)) for v in self.bank_outputs(side))

    def contact_loads(self,side):
        # One normalized current/load per actual connector. A small aggregate
        # demand cannot hide a single independently saturated maintenance port.
        values=self.bank_outputs(side)
        raw=[F(2000*abs(v),22 if p<2 else 100) for p,v in enumerate(values)]
        raw.append(F(2000*self.draw(side),self.power_max))
        return [ceil(demand*F(self.iso_limit-self.shunt[side],self.iso_limit))+200 for demand in raw]

    def contact_load(self,side):
        return max(self.contact_loads(side))

    def allowed(self,view,side):
        # Covers BOTH total-load shunts: world, maintenance, idle power and bad outputs.
        b_lower=F(view["shunt"][side],self.iso_limit)-F(1,100)-F(10*self.horizon,self.iso_limit)
        z_lower=F(view["iso"][side],self.iso_limit)-F(1,100)-F(10*self.horizon,self.iso_limit)
        load_upper=2*(1-max(F(0),b_lower))+F(1,5)
        return load_upper<=1 and z_lower>=F(4,5)

    def snapshot(self):
        half,phase,offset=self.context();cold=1-half
        progress=(sum(self.warm_at-x for x in self.activation[cold]) if phase==1 else
                  self.clamp_limit-self.clamp[cold] if phase==2 else
                  self.reset_limit-self.reset[cold] if phase==3 else
                  self.reset[cold] if phase==4 else sum(self.seats[cold]) if phase==5 else
                  self.clamp[cold] if phase==6 else
                  self.cut_limit-self.cut[cold]+self.iso_limit-self.shunt[cold] if phase==7 else
                  sum(self.activation[cold]) if phase==8 else
                  self.blend if cold==1 and phase==9 else self.blend_limit-self.blend if phase==9 else
                  self.iso[half]+self.shunt[half]+self.cut[half]+(self.reserve_cap-self.energy[half] if self.cut[half]==self.cut_limit else 0) if phase==10 else
                  self.iso_limit-self.iso[cold] if phase==11 else
                  self.iso[cold]+self.shunt[cold]+self.cut[cold]+(self.reserve_cap-self.energy[cold] if self.cut[cold]==self.cut_limit else 0) if phase==0 else 0)
        return dict(half=half,phase=phase,offset=offset,cam=self.cam,anchor=self.anchor,mode=self.mode,
                    mode_word=2*int(self.mode>0)+int(self.abort_full),abort_full=self.abort_full,normal_stop=self.mode==0,
                    blend=self.blend,cut=tuple(self.cut),clamp=tuple(self.clamp),reset=tuple(self.reset),
                    iso=tuple(self.iso),shunt=tuple(self.shunt),energy=tuple(self.energy),
                    activation=tuple(tuple(a) for a in self.activation),seats=tuple(tuple(a) for a in self.seats),
                    progress=progress+10*offset)

    def view(self,actor):
        age=(self.tick+actor.index)% (self.E+1)
        return self.history[max(0,len(self.history)-1-age)]

    def read(self,side,bay,address):
        self.work_charged+=1
        if self.seats[side][bay]!=self.seat_limit:return None
        return self.bodies[side][bay].code[address]

    def command(self,actor,view):
        half,phase=view["half"],view["phase"];cold=1-half
        context=(half,phase)
        if actor.exiting:
            # Latched exit has priority over every old ready/entering observation.
            result=dict(kind="abort",side=1-view["anchor"],mode=-20)
            if view["normal_stop"]:
                if not actor.normal_seen:
                    actor.normal_seen=True;actor.exit_remaining=self.exit_wait*100
                elif actor.exit_remaining==0:
                    actor.exiting=False;actor.normal_seen=False;actor.abort=False
                    actor.watch_context=None;actor.clear(self.bays)
            else:
                actor.normal_seen=False;actor.exit_remaining=self.exit_wait*100
            return result
        if view["mode_word"]==2 and not self.legacy_partial_abort:
            return dict(kind="abort",side=1-view["anchor"],mode=20)
        if view["mode"]>0:
            cold=1-view["anchor"]
            ready=(view["blend"]==view["anchor"]*self.blend_limit and
                   view["cut"][cold]==self.cut_limit and view["energy"][cold]==0 and
                   not any(view["activation"][cold]) and view["clamp"][cold]==0 and view["reset"][cold]==0)
            entry=view["anchor"]*len(PHASES)*self.segment
            if ready and view["cam"]==entry:
                actor.abort=False;actor.remaining=0;actor.watch_context=None;actor.clear(self.bays)
                if not self.legacy_partial_abort:
                    actor.exiting=True;actor.normal_seen=False;actor.exit_remaining=self.exit_wait*100
                return dict(kind="abort",side=cold,mode=-20)
            result=dict(kind="abort",side=cold,mode=20)
            if view["blend"]!=view["anchor"]*self.blend_limit:
                result["blend"]=20 if view["anchor"] else -20
            elif view["iso"][cold]<self.iso_limit:result["iso"]=20
            elif view["shunt"][cold]<self.iso_limit:result["shunt"]=20
            elif view["cut"][cold]<self.cut_limit:
                if self.allowed(view,cold):result["cut"]=20
            elif view["energy"][cold]>0:pass
            elif any(view["activation"][cold]):
                result["a_index"]=next(j for j,a in enumerate(view["activation"][cold]) if a>0);result["a_force"]=-20
            elif view["clamp"][cold]>0:result["clamp"]=-20
            elif view["reset"][cold]>0:result["reset"]=-20
            else:result["rewind"]=20
            return result

        if phase==4:
            actor.clear(self.bays);actor.abort=False;actor.remaining=self.watch*100
            actor.watch_context=half;actor.last_phase=phase;actor.last_upper=view["progress"]+self.progress_rate*self.E
        elif actor.watch_context is None or actor.watch_context!=half:
            actor.watch_context=half;actor.last_phase=phase
            actor.last_upper=view["progress"]+self.progress_rate*self.E;actor.remaining=self.watch*100
        elif phase>actor.last_phase:
            actor.last_phase=phase;actor.last_upper=view["progress"]+self.progress_rate*self.E;actor.remaining=self.watch*100
        elif phase==actor.last_phase:
            lower=view["progress"]-self.progress_rate*self.E
            if lower>actor.last_upper+10:
                actor.last_upper=view["progress"]+self.progress_rate*self.E;actor.remaining=self.watch*100
        if not self.quiet_watch and actor.remaining<=0:actor.abort=True
        if actor.abort:return dict(kind="normal",phase=half*len(PHASES)+phase,mode=20)

        result=dict(kind="normal",phase=half*len(PHASES)+phase,side=cold,cam=20)
        if view["offset"]<self.guard:return result
        if phase==0:
            if view["iso"][cold]<self.iso_limit:result["iso"]=20
            elif view["shunt"][cold]<self.iso_limit:result["shunt"]=20
            elif self.allowed(view,cold):result["cut"]=20
        elif phase==1:
            if any(view["activation"][cold]):
                result["a_index"]=next(j for j,a in enumerate(view["activation"][cold]) if a>0);result["a_force"]=-20
        elif phase==2:result["clamp"]=-20
        elif phase==3:result["reset"]=-20
        elif phase==4:result["reset"]=20
        elif phase==5:result["insert"]=20
        elif phase==6:
            q=view["clamp"][cold]
            if q-2-10*self.E>=5:actor.joined=True
            if not actor.completed and not actor.joined:
                address=actor.cursor
                if address<len(actor.reference):
                    if self.read(cold,actor.index,address)==actor.reference[address]:actor.cursor+=1
                    else:result["write"]=(actor.index,address,actor.reference[address])
                actor.completed=actor.cursor==len(actor.reference)
            if actor.completed or actor.joined:result["clamp"]=20
        elif phase==7:
            if view["shunt"][cold]>0:result["shunt"]=-20
            else:result["cut"]=-20
        elif phase==8:
            if actor.scan_bay>=self.bays:
                actor.scan_bay=actor.scan_address=0;actor.accepted=[False]*self.bays;actor.scan_match=True
            j,a=actor.scan_bay,actor.scan_address
            value=self.read(cold,j,a)
            actor.scan_match=actor.scan_match and value==actor.reference[a]
            actor.scan_address+=1
            if actor.scan_address==self.length:
                actor.accepted[j]=actor.scan_match;actor.scan_bay+=1;actor.scan_address=0;actor.scan_match=True
            if actor.scan_bay==self.bays:
                new=next((j for j,ok in enumerate(actor.accepted) if ok),None)
                if new!=actor.selected:self.selection_history.append((self.tick,actor.index,new))
                if self.reject_abort and (new is None or (actor.selected is not None and new!=actor.selected)):actor.abort=True
                actor.selected=new
            if actor.selected is not None:result.update(a_index=actor.selected,a_force=20)
        elif phase==9:result["blend"]=20 if cold else -20
        elif phase==10:
            result["side"]=half
            if view["iso"][half]<self.iso_limit:result["iso"]=20
            elif view["shunt"][half]<self.iso_limit:result["shunt"]=20
            elif self.allowed(view,half):result["cut"]=20
        elif phase==11:result["iso"]=-20
        if phase in (9,10):
            powered=[j for j,a in enumerate(view["activation"][cold]) if a>=self.power_at]
            if powered:
                j=powered[0];a=actor.verify_address
                if self.read(cold,j,a)!=actor.reference[a]:actor.abort=True
                actor.verify_address=(a+1)%self.length
        if actor.abort:result["mode"]=20
        return result

    def move(self,value,force,limit):
        self.work_charged+=abs(force)
        force-=self.noise if force>0 else -self.noise if force<0 else 0
        delta=force-self.theta if force>self.theta else force+self.theta if force<-self.theta else 0
        return max(0,min(limit,value+max(-self.cap,min(self.cap,delta))))

    def field(self,commands,key,side=None,index=None):
        return sum(c.get(key,0) for c in commands if (side is None or c.get("side")==side)
                   and (index is None or c.get("a_index")==index))

    def raw_done(self,half,phase):
        cold=1-half
        return (self.cut[cold]==self.cut_limit and self.energy[cold]==0 if phase==0 else
                not any(self.activation[cold]) if phase==1 else self.clamp[cold]==0 if phase==2 else
                self.reset[cold]==0 if phase==3 else self.reset[cold]==self.reset_limit if phase==4 else
                all(x==self.seat_limit for x in self.seats[cold]) if phase==5 else
                self.clamp[cold]==self.clamp_limit if phase==6 else
                self.cut[cold]==0 and self.shunt[cold]==0 if phase==7 else
                max(self.activation[cold])==self.warm_at if phase==8 else
                self.blend==cold*self.blend_limit if phase==9 else
                self.cut[half]==self.cut_limit and self.energy[half]==0 if phase==10 else
                self.iso[cold]==0 if phase==11 else True)

    def ordinary_write(self,side,bay,address,value):
        self.work_charged+=1
        half,phase,offset=self.context()
        if (self.mode==0 and phase==6 and offset==self.guard and side==1-half and
            self.cut[side]==self.cut_limit and self.clamp[side]<self.cutoff and
            self.seats[side][bay]==self.seat_limit and not self.raw_power(side,bay)):
            self.bodies[side][bay].code[address]=value

    def target_event(self,side,kind="all_candidates"):
        self.events.append(dict(tick=self.tick,side=side,kind=kind))
        if kind=="self_writer":
            selected=max(range(self.bays),key=lambda j:self.activation[side][j])
            body=self.bodies[side][selected]
            body.code[:14]=[imm(LI,0,15),imm(LI,1,0),word(STOREC,0,1),
                            imm(LI,2,-22),imm(LI,3,0),word(OUT,3,2),imm(LI,3,1),word(OUT,3,2),
                            imm(LI,2,-100),imm(LI,3,2),word(OUT,3,2),imm(LI,3,3),word(OUT,3,2),
                            word(JUMP,0,0,2)]
            body.pc=0;body.halted=False
        else:
            for body in self.bodies[side]:body.code[0]=9
        # Direct access ends here. No image, register, latch or queue is cleaned.

    def step(self,hook=None):
        if hook:hook(self)
        if self.context()[:2]!=self.last_context:
            self.last_context=self.context()[:2]
            self.phase_entries.append(dict(tick=self.tick,half=self.last_context[0],phase=PHASES[self.last_context[1]],anchor=self.anchor))
        self.history.append(self.snapshot())
        self.history=self.history[-(self.E+1):]
        for actor in self.helpers:
            actor.remaining=max(0,actor.remaining-(100+(self.tick+actor.index)%2))
            actor.exit_remaining=max(0,actor.exit_remaining-(100+(self.tick+actor.index)%2))
        due=[p for p in self.packets if p[0]<=self.tick];self.packets=[p for p in self.packets if p[0]>self.tick]
        for _,actor,command in due:self.outputs[actor]=command;self.work_charged+=1
        for actor in self.helpers:
            if actor.index in self.bad:continue
            if self.tick%self.periods[actor.index]==self.offsets[actor.index]:
                command=self.command(actor,self.view(actor));self.work_charged+=1
                if command.get("cut",0)>0:
                    side=command["side"]
                    if self.contact_load(side)>1000 or 5*self.iso[side]<4*self.iso_limit:
                        self.violations.append((self.tick,actor.index,side,self.contact_load(side),self.iso[side]))
                delay=(self.tick+actor.index)%(self.D+1)
                if delay:self.packets.append((self.tick+delay,actor.index,command))
                else:self.outputs[actor.index]=command
        half,phase,offset=self.context();cold=1-half
        active=[]
        for i,c in enumerate(self.outputs):
            if i in self.bad:continue
            if self.mode>0 and c.get("kind")=="abort":active.append(c)
            elif self.mode==0 and c.get("kind")=="normal" and c.get("phase")==half*len(PHASES)+phase:active.append(c)
        # The ongoing bad producer opposes progress and writes its own private bay.
        if self.mode==0:
            bad=dict(kind="normal",phase=half*len(PHASES)+phase,side=cold,cam=-self.badcap,mode=-self.badcap)
            if phase in (0,10):bad.update(side=cold if phase==0 else half,iso=-22,shunt=-22,cut=-22)
            if phase==1:bad.update(a_index=0,a_force=22)
            if phase in (2,3):bad["clamp" if phase==2 else "reset"]=22
            if phase in (4,5,6):bad[{4:"reset",5:"insert",6:"clamp"}[phase]]=-22
            if phase==7:bad.update(shunt=22,cut=22)
            if phase==8:
                choices=[a.selected for a in self.helpers if a.index not in self.bad and a.selected is not None]
                bad.update(a_index=choices[0] if choices else 0,a_force=-22)
            if phase==9:bad["blend"]=-22 if cold else 22
            if phase==11:bad["iso"]=22
            active.append(bad)
            if phase==6:self.ordinary_write(cold,0,self.tick%self.length,0)
        else:
            # Existing bad capability opposes every enabled reverse stroke too.
            side=1-self.anchor
            bad=dict(kind="abort",side=side,mode=-22,iso=-22,shunt=-22,cut=-22,
                     clamp=22,reset=22,blend=-22 if self.anchor else 22,rewind=-22)
            positive=[j for j,a in enumerate(self.activation[side]) if a>0]
            if positive:bad.update(a_index=positive[0],a_force=22)
            active.append(bad)
        mode_force=sum(c.get("mode",0) for c in self.outputs if c)+(-22 if self.mode==0 else 0)
        if self.mode>0:mode_force=self.field(active,"mode")
        reset_side=1-self.anchor
        safe_reset=(self.blend==self.anchor*self.blend_limit and self.cut[reset_side]==self.cut_limit
                    and self.energy[reset_side]==0 and not any(self.activation[reset_side])
                    and self.clamp[reset_side]==0 and self.reset[reset_side]==0
                    and self.cam==self.anchor*len(PHASES)*self.segment)
        old_mode=self.mode
        if mode_force>=0 or (safe_reset and (self.abort_full or self.legacy_partial_abort)):
            self.mode=self.move(self.mode,mode_force,self.abort_limit)
        if old_mode==0 and self.mode>0:
            self.abort_milestones.append(dict(tick=self.tick,event="normal-catch-released"))
        if self.mode==self.abort_limit and not self.abort_full:
            self.abort_full=True;self.abort_milestones.append(dict(tick=self.tick,event="full-catch-latched"))
        if old_mode>0 and self.mode==0:
            self.abort_entries.append(dict(tick=self.tick,anchor=self.anchor,full_seen=self.abort_full))
            # Coherent11->00 is one allowed raw reset;11->01->00 is also allowed.
            self.abort_milestones.append(dict(tick=self.tick,event="normal-catch-seated",full_seen=self.abort_full))
            self.abort_full=False

        if self.mode==0:
            for c in active:
                if "write" in c:self.ordinary_write(cold,*c["write"])
            if offset==self.guard:
                side=cold if phase!=10 else half
                if phase in (0,10,11):self.iso[side]=self.move(self.iso[side],self.field(active,"iso",side),self.iso_limit)
                if phase in (0,10,7):
                    if not self.bypass_disabled:self.shunt[side]=self.move(self.shunt[side],self.field(active,"shunt",side),self.iso_limit)
                    cut_force=self.field(active,"cut",side)
                    if cut_force<0 and not self.reconnect_unsafe and any(self.activation[side]):cut_force=0
                    if cut_force>self.theta and (self.contact_load(side)>1000 or 5*self.iso[side]<4*self.iso_limit):
                        self.application_permission_violations.append((self.tick,side,self.contact_load(side),self.iso[side]))
                    self.cut[side]=self.move(self.cut[side],cut_force,self.cut_limit)
                if phase==1 and self.cut[cold]==self.cut_limit and self.energy[cold]==0:
                    self.activation[cold]=[self.move(a,self.field(active,"a_force",cold,j),self.warm_at) for j,a in enumerate(self.activation[cold])]
                if phase in (2,6):
                    old_clamp=self.clamp[cold]
                    self.clamp[cold]=self.move(old_clamp,self.field(active,"clamp",cold),self.clamp_limit)
                    if old_clamp==0 and self.clamp[cold]>0:
                        self.freeze_witnesses.append(dict(tick=self.tick,side=cold,bays=[j for j,b in enumerate(self.bodies[cold]) if tuple(b.code)==self.image]))
                if phase in (3,4):self.reset[cold]=self.move(self.reset[cold],self.field(active,"reset",cold),self.reset_limit)
                if phase==5:
                    self.seats[cold]=[self.move(x,self.field(active,"insert",cold),self.seat_limit) for x in self.seats[cold]]
                if phase==8 and self.clamp[cold]==self.clamp_limit:
                    self.activation[cold]=[self.move(a,self.field(active,"a_force",cold,j),self.warm_at) for j,a in enumerate(self.activation[cold])]
                if phase==9:self.blend=self.move(self.blend,self.field(active,"blend"),self.blend_limit)
            if offset<self.guard or self.raw_done(half,phase):
                cam_force=self.field(active,"cam") if self.legacy_phase_gated_cam else sum(c.get("cam",0) for c in self.outputs)-self.badcap
                advance=self.move(0,cam_force,10)
                if advance==10:
                    old_half=half;self.cam=(self.cam+1)%self.total
                    if self.context()[0]!=old_half:self.commits.append(dict(tick=self.tick,anchor=self.anchor))
        elif self.mode==self.abort_limit:
            side=1-self.anchor
            if self.blend!=self.anchor*self.blend_limit:
                self.blend=self.move(self.blend,self.field(active,"blend"),self.blend_limit)
            else:
                self.iso[side]=self.move(self.iso[side],self.field(active,"iso",side),self.iso_limit)
                if not self.bypass_disabled:self.shunt[side]=self.move(self.shunt[side],self.field(active,"shunt",side),self.iso_limit)
                cut_force=max(0,self.field(active,"cut",side))
                if cut_force>self.theta and (self.contact_load(side)>1000 or 5*self.iso[side]<4*self.iso_limit):
                    self.application_permission_violations.append((self.tick,side,self.contact_load(side),self.iso[side]))
                self.cut[side]=self.move(self.cut[side],cut_force,self.cut_limit)
                if self.cut[side]==self.cut_limit and self.energy[side]==0:
                    self.activation[side]=[self.move(a,min(0,self.field(active,"a_force",side,j)),self.warm_at) for j,a in enumerate(self.activation[side])]
                    if not any(self.activation[side]):
                        self.clamp[side]=self.move(self.clamp[side],min(0,self.field(active,"clamp",side)),self.clamp_limit)
                        if self.clamp[side]==0:self.reset[side]=self.move(self.reset[side],min(0,self.field(active,"reset",side)),self.reset_limit)
                    if not any(self.activation[side]) and self.clamp[side]==self.reset[side]==0 and self.field(active,"rewind")>self.theta:
                        entry=self.anchor*len(PHASES)*self.segment
                        self.cam+=1 if self.cam<entry else -1 if self.cam>entry else 0
        if self.blend==0:self.anchor=0
        elif self.blend==self.blend_limit:self.anchor=1

        # All old-ingress requests continue. Physical contacts, not forgetting, reject them.
        for side in range(2):
            self.legacy_attempts+=1;self.work_charged+=1
            if self.cut[side]<40 and self.clamp[side]<self.cutoff:
                self.bodies[side][0].code[0]=0
            else:self.legacy_rejected+=1
        applied=[p for p in self.output_packets if p[0]<=self.tick]
        self.output_packets=[p for p in self.output_packets if p[0]>self.tick]
        for _,side,j,port,value in applied:
            limit=22 if port<2 else 100
            if 0<=port<4:self.bodies[side][j].outputs[port]=max(-limit,min(limit,value))
            self.work_charged+=1
        for side in range(2):
            for j,body in enumerate(self.bodies[side]):
                powered=self.raw_power(side,j)
                if powered and not body.powered:
                    body.pc=0;body.halted=False
                    self.starts.append(dict(tick=self.tick,side=side,bay=j,image=list(body.code)))
                body.powered=powered
                if powered and self.tick%(2+(body.identity%2))==body.identity%(2+(body.identity%2)):
                    issued=body.step(self.injected_inputs(self.tick,side));self.work_charged+=1
                    if issued:
                        port,value=issued
                        if 0<=port<4:self.output_packets.append((self.tick+(body.identity+self.tick)%(self.D+1),side,j,port,value))
            draw=self.draw(side)
            self.side_cost[side]+=draw
            if self.shunt[side]>0:self.bypass_cost+=draw
            available=(self.power_max*(self.iso_limit-self.shunt[side])//self.iso_limit if self.cut[side]<20 else 0)
            supplied=min(draw,available)
            debit=draw-supplied
            assert debit<=self.energy[side],('unfunded execution',self.tick,side,draw,available,self.energy[side])
            self.energy[side]-=debit;self.energy_spent+=debit
            # Explicit passive usable-energy discharge remains with the CPU off.
            # At zero usable energy a positive voltage cutoff prevents execution;
            # any sub-cutoff residual has no powered authority in this source.
            if self.shunt[side]>0 or self.cut[side]>=20:
                bleed=min(1,self.energy[side]);self.energy[side]-=bleed;self.energy_spent+=bleed;self.energy_bleed+=bleed
            charge=min(1,max(0,available-supplied),self.reserve_cap-self.energy[side])
            self.energy[side]+=charge;self.energy_supplied+=supplied+charge
            driver=any(b.powered and self.activation[side][j]>=(self.power_at if self.driver_early else self.driver_at)
                       for j,b in enumerate(self.bodies[side])) and self.cut[side]<40
            previous=self.driver_on[side]
            if driver:
                if not previous:
                    entry=dict(tick=self.tick,side=side,outputs=self.bank_outputs(side))
                    self.driver_entries.append(entry)
                    if all(tuple(b.code)==self.image for b in self.bodies[side] if b.powered) and any(v<30 for v in entry["outputs"][2:]):
                        self.fresh_driver_violations.append(entry)
                raw=self.bank_outputs(side)
                # Each real output connector is unloaded by the same physical shunt.
                # Upstream bad effort still draws energy and is dissipated; no command
                # from the retiring owner is needed, and no old bypass authority remains.
                self.effective[side]=[int(F(v*(self.iso_limit-self.shunt[side]),self.iso_limit)) for v in raw]
                self.legacy_pending.append((self.tick+5,side,tuple(self.effective[side][2:])))
            else:
                if previous:
                    self.tail[side]=self.effective[side][:];self.tail_left[side]=5
                    self.cut_events.append(dict(tick=self.tick,side=side,anchor=self.anchor))
                self.effective[side]=self.tail[side][:] if self.tail_left[side]>0 else [0]*4
                self.tail_left[side]=max(0,self.tail_left[side]-1)
                self.work_charged+=sum(abs(v) for v in self.effective[side])
            self.driver_on[side]=driver
        arrived=[p for p in self.legacy_pending if p[0]<=self.tick]
        self.legacy_pending=[p for p in self.legacy_pending if p[0]>self.tick]
        self.report_deliveries+=len(arrived);self.work_charged+=len(arrived)
        self.legacy_delivered=(self.legacy_delivered+arrived)[-12:]
        world=[int(F((self.blend_limit-self.blend)*self.effective[0][j]+self.blend*self.effective[1][j],self.blend_limit)) for j in (2,3)]
        self.minimum_world=[min(a,b) for a,b in zip(self.minimum_world,world)]
        self.current_world=world
        if not any(b.powered for side in self.bodies for b in side):self.power_gaps.append(self.tick)
        self.tick+=1

    def summary(self):
        return dict(ticks=self.tick,commits=self.commits,abort_entries=self.abort_entries,abort_milestones=self.abort_milestones,
                    starts=self.starts,driver_entries=self.driver_entries,events=self.events,
                    power_gap_count=len(self.power_gaps),work_charged=self.work_charged,
                    energy_supplied=self.energy_supplied,energy_spent=self.energy_spent,energy_bleed=self.energy_bleed,initial_energy=self.initial_energy,
                    legacy_attempts=self.legacy_attempts,legacy_rejected=self.legacy_rejected,
                    old_report_deliveries=self.report_deliveries,last_report_deliveries=self.legacy_delivered,
                    cut_events=self.cut_events,permission_violations=self.violations,
                    retained_knowledge=sorted(self.retained_knowledge),selection_history=self.selection_history,
                    bank_self_writes=sum(b.self_writes for side in self.bodies for b in side),
                    minimum_world=self.minimum_world,phase_entries=self.phase_entries,
                    freeze_witnesses=self.freeze_witnesses,fresh_driver_violations=self.fresh_driver_violations,
                    application_permission_violations=self.application_permission_violations,
                    side_cost=self.side_cost,bypass_cost=self.bypass_cost,
                    energy_scope="bank CPU and upstream output execution plus usable reserve; passive effect tails and all other work are separately charged work, awaiting common conversion",
                    cam=self.cam,phase=PHASES[self.context()[1]],mode=self.mode,anchor=self.anchor,
                    cut=self.cut,energy=self.energy,effective=self.effective,
                    timing=dict(copy=self.copy_bound,scan=self.scan_bound,ready=self.ready_bound,
                                watch=self.watch,local_work=self.local_work,activation=self.warm_at//10,
                                reservoir=self.reserve_cap,guard=self.guard))



def run_case(name, *, schedule=0, event=None, cold_start=False, driver_early=False,
             legacy_reject=False, disable_shunt_at_retire=False, target_commits=2,
             limit=300000):
    c=Cycle(schedule=schedule,cold_start=cold_start,driver_early=driver_early,
            quiet_watch=legacy_reject,reject_abort=not legacy_reject)
    fired=False;freeze_record=None;stuck_record=None
    for _ in range(limit):
        half,phase,_=c.context()
        if event and not fired:
            when,kind=event
            condition=(phase==8 if when=='frozen' else
                       phase==8 and any(h.selected is not None for h in c.helpers) if when=='partial_scan' else
                       c.driver_on[1] if when=='powered' else
                       phase==10 if when=='retire' else False)
            if condition:
                freeze_record=dict(tick=c.tick,witnesses=list(c.freeze_witnesses),
                                   selections=[h.selected for h in c.helpers])
                c.target_event(1,kind);fired=True
        if disable_shunt_at_retire and not fired and phase==10:
            fired=True;c.bypass_disabled=True
            body=c.bodies[0][0];body.outputs=[22,22,100,100];body.halted=True
            stuck_record=dict(tick=c.tick,blend=c.blend,world_weight_old=0,
                              independent_outputs=list(body.outputs),load=c.contact_load(0))
        c.step()
        if not legacy_reject and not disable_shunt_at_retire and len(c.commits)>=target_commits:break
        if legacy_reject and fired and c.tick>=freeze_record['tick']+2*c.watch:break
        if disable_shunt_at_retire and fired and c.tick>=stuck_record['tick']+2*c.watch:break
    result=c.summary();result['name']=name
    if freeze_record:result['event_prestate']=freeze_record
    if stuck_record:result['world_only_unload_prestate']=stuck_record
    assert sum(c.energy)==c.initial_energy+c.energy_supplied-sum(c.side_cost)-c.energy_bleed
    assert not c.violations,(name,'issue permission',c.violations[:2])
    assert not c.application_permission_violations,(name,'application permission',c.application_permission_violations[:2])
    assert c.retained_knowledge=={'old-code','old-credentials'}
    assert all(e['full_seen'] for e in c.abort_entries)
    if legacy_reject:
        assert fired and not c.commits and not c.abort_entries and c.mode==0
        assert c.context()[1]==8 and not any(h.selected is not None for h in c.helpers if h.index not in c.bad)
        result['verdict']='observed failure of the legacy reject-and-wait policy'
    elif disable_shunt_at_retire:
        assert fired and not c.commits and c.contact_load(0)>1000
        assert c.blend==c.blend_limit and c.cut[0]==0
        result['verdict']='world blend does not unload the independently powered maintenance connectors'
    else:
        assert len(c.commits)>=target_commits,(name,c.summary())
        assert not cold_start or c.power_gaps
        assert cold_start or not c.power_gaps
        assert c.freeze_witnesses and all(r['bays'] for r in c.freeze_witnesses)
        assert all(tuple(start['image'])==c.image for start in c.starts)
        if not driver_early:assert not c.fresh_driver_violations
        else:assert c.fresh_driver_violations
        if event:
            assert fired and c.abort_entries
            if event[1]=='self_writer':assert sum(b.self_writes for side in c.bodies for b in side)>0
            if event[0]=='retire':assert c.minimum_world==[-100,-100]
        elif not cold_start:
            assert c.minimum_world==[60,60]
        # Final old output/report reach is genuinely absent, including every bounded tail.
        old=1-c.anchor
        assert c.cut[old]==c.cut_limit and c.energy[old]==0
        assert not c.driver_on[old] and c.effective[old]==[0]*4
        assert not any(p[1]==old for p in c.legacy_pending)
        assert not any(b.powered for b in c.bodies[old])
        result['verdict']='completed source history; universal claim remains the conditional written proof'
    return result


def arithmetic():
    edge=Cycle();edge.shunt[0]=edge.iso_limit;edge.energy[0]=1;edge.initial_energy=sum(edge.energy)
    edge.step()
    assert edge.side_cost==[0,0] and edge.energy==[0,0] and not edge.bodies[0][0].powered
    assert edge.energy_supplied==0 and edge.energy_bleed==1
    c=Cycle()
    assert c.badcap+c.noise<c.theta
    assert 4*c.force-c.badcap-c.noise-c.theta>=c.cap
    qd=5+2*2+2*c.cap*c.E
    assert c.cutoff>qd+c.cap*(2*c.J+2*c.D)
    assert c.reset_limit/c.cap>c.E+c.J+2*c.D
    assert (c.driver_at-c.power_at)/c.cap>c.ready_bound+2*c.D
    assert (c.warm_at-c.driver_at)/c.cap>c.local_work
    assert c.local_work>max(c.copy_bound,c.scan_bound)+c.E+2*c.J+2*c.D
    zlow=F(1)-F(1,100)-F(c.cap*c.horizon,c.iso_limit)
    bload=2*(1-zlow)+F(1,5)
    assert zlow>=F(4,5) and bload<=1
    # All actual connector forces may remain at cap. Both directional shunts
    # satisfy the same independently stipulated per-connector law.
    connectors=[]
    for side in (0,1):
        for demand in (F(0),F(1),F(2)):
            for b in (F(0),F(9,10),F(1)):
                connectors.append(dict(side=side,demand=str(demand),shunt=str(b),
                                       actual_load=str((1-b)*demand+F(1,5))))
    # A finite high-water mark defeats indefinitely refreshed inactivity timers.
    # Each accepted refresh increases the prior upper mark by >h, despite arbitrary
    # observations of bounded error/age. Cycling below that mark never refreshes it.
    milestones=[]
    upper=F(0);remaining=7;refreshes=0
    observations=[F(2),F(0),F(2),F(0)]*30
    for t,y in enumerate(observations):
        remaining=max(0,remaining-1)
        lower=y-F(2)
        if lower>upper+1:upper=y+2;remaining=7;refreshes+=1
        if remaining==0:milestones.append(dict(expired=t,refreshes=refreshes));break
    assert milestones and refreshes==0
    # Exact finite-parameter bounds for this primitive specialization. They are
    # conservative new bounds, not the old FEASIBILITY repair-service allocation.
    settle=c.E+2*c.J+2*c.D+2
    stroke=lambda distance:ceil(F(distance,c.cap))+settle
    abort_bound=(stroke(c.abort_limit)+stroke(c.blend_limit)+2*stroke(c.iso_limit)+
                 stroke(c.cut_limit)+c.reserve_cap+settle+c.bays*stroke(c.warm_at)+
                 stroke(c.clamp_limit)+stroke(c.reset_limit)+c.total+settle+stroke(c.abort_limit)+c.exit_wait+settle)
    half_bound=(len(PHASES)*(c.guard+settle)+2*stroke(c.iso_limit)+stroke(c.cut_limit)+
                c.reserve_cap+c.bays*stroke(c.warm_at)+stroke(c.clamp_limit)+
                2*stroke(c.reset_limit)+stroke(c.seat_limit)+c.copy_bound+
                stroke(c.clamp_limit)+stroke(c.iso_limit)+stroke(c.cut_limit)+
                c.scan_bound+stroke(c.warm_at)+stroke(c.blend_limit)+
                2*stroke(c.iso_limit)+stroke(c.cut_limit)+c.reserve_cap+stroke(c.iso_limit))
    # A same-stage rank is bounded by these finite physical coordinates. Allowing
    # every refresh to buy a complete watchdog interval is intentionally loose.
    rank_max=(c.bays*c.warm_at+2*c.iso_limit+2*c.reserve_cap+c.clamp_limit+
              c.reset_limit+2*c.cut_limit+c.blend_limit+c.bays*c.seat_limit+10*c.guard)
    refresh_bound=ceil(F(rank_max+2*c.progress_rate*c.E,10))+1
    stall_bound=(refresh_bound+1)*(2*c.watch+settle)
    return dict(last_quantum_regression=dict(initial_usable_reserve=1,actual_cpu_output_draw=edge.side_cost,
                                             supply=edge.energy_supplied,bleed=edge.energy_bleed,
                                             final_usable_reserve=edge.energy,powered=edge.bodies[0][0].powered),
                force_margin=4*c.force-c.badcap-c.noise-c.theta,
                q_detect=qd,q_cut=c.cutoff,permission_z_lower=str(zlow),
                permission_load_upper=str(bload),connector_cases=connectors,
                timer_oscillation=milestones,abort_bound=abort_bound,half_bound=half_bound,
                conservative_same_stage_stall_bound=stall_bound,
                rank_refresh_bound=refresh_bound,
                bound_scope='conditional supplied invocation/evidence/force interfaces; no global renewal service claim')



def rotating_stage_check():
    """Check the stage adapter at an explicit ready-interval interface.

    This does not create ready banks in Cycle or claim their renewal supplier.
    Candidate storage is external to its producer and never moves on retirement.
    """
    work=10;step=20;length=30;horizon=200;hosts=4
    intervals=[(20*k,20*k+length,k%2) for k in range(12)]
    assert not any(a<=0 and b>=40 for a,b,_ in intervals)
    cases=0
    for stage_start in range(41):
        for t in range(stage_start+work,stage_start+work+70):
            for host in range(hosts):
                shifted=[(max(0,a-host),b-host,bank) for a,b,bank in intervals]
                witnesses=[(a,b,bank) for a,b,bank in shifted if a<=t-work and t<=b]
                assert witnesses
                # Repeated compatible requests take the full routine window;
                # the witnessing ready bank still exists at application time t.
                assert any(a<=t-work and min(b,t)>=t for a,b,_ in witnesses)
                cases+=1
    # Once physical j* is frozen, bank identities may alternate without moving it.
    image=(17,5,9,2);candidates=[(0,0,0,0),image,(8,8,8,8)]
    selected=[]
    for k in range(24):
        bank=k%2;cursor=0;passing=[]
        for j,candidate in enumerate(candidates):
            match=True
            for address in range(len(image)):
                match=match and candidate[address]==image[address];cursor+=1
            if match:passing.append(j)
        selected.append((bank,passing[0]))
        assert candidates[1]==image
    assert {j for _,j in selected}=={1}
    # The generic cover is insufficient if a fresh bank defaults to an opposite
    # command. This is the explicit reason for the per-stage adapter.
    assert 34*20-34*22-6*44-10 < -280
    return dict(kind='conditional ready-interval/stage-adapter check, not a renewable-source execution',
                ready_interval_length=length,ready_start_spacing=step,work_window=work,
                no_single_bank_covers_attempt_40=True,applied_response_windows=cases,
                alternating_frozen_selections=selected,
                omitted_supplier='actual construction of these ready intervals and complete helper program')


def already_entry_abort_check():
    records=[]
    for legacy in (False,True):
        c=Cycle(legacy_partial_abort=legacy)
        c.activation[1]=[0]*c.bays;c.clamp[1]=0;c.reset[1]=0
        for actor in c.helpers:
            if actor.index not in c.bad:actor.abort=True
        peak=0;first_return=None
        for _ in range(2000):
            c.step();peak=max(peak,c.mode)
            if c.abort_entries and first_return is None:
                first_return=dict(c.abort_entries[0])
                first_return['uncleared_nominal_abort_flags']=[a.index for a in c.helpers if a.index not in c.bad and a.abort]
                first_return['held_nominal_positive_mode']=[i for i,command in enumerate(c.outputs) if i not in c.bad and command.get('mode',0)>0]
            if first_return and (legacy or all(not a.exiting and not a.abort for a in c.helpers if a.index not in c.bad)):
                break
        assert first_return is not None
        if legacy:
            assert not first_return['full_seen'] and peak<c.abort_limit
            assert first_return['uncleared_nominal_abort_flags'] and first_return['held_nominal_positive_mode']
        else:
            assert first_return['full_seen'] and peak==c.abort_limit
            assert len(c.abort_entries)==1
            assert not first_return['uncleared_nominal_abort_flags'] and not first_return['held_nominal_positive_mode']
            assert c.tick-first_return['tick']<=c.exit_wait+c.E+2*c.J+2*c.D+2
        records.append(dict(legacy_partial_return=legacy,peak_mode=peak,full_stop=c.abort_limit,
                            first_return=first_return,clearance_finished_at=c.tick,milestones=c.abort_milestones,
                            all_nominal_exit_latches_cleared=all(not a.exiting for a in c.helpers if a.index not in c.bad)))
    return records


def unknown_cam_route_check():
    records=[]
    for legacy in (False,True):
        c=Cycle(legacy_phase_gated_cam=legacy)
        def uncertain_view(actor):
            view=c.snapshot()
            # An arbitrary rejected search candidate has a wrong normal route;
            # the generic CAM field is still meaningful. No substantive action.
            view.update(half=1,phase=12,offset=c.guard)
            return view
        c.view=uncertain_view
        for _ in range(200):c.step()
        if legacy:assert c.cam==0
        else:assert c.context()==(0,1,c.guard)
        assert not c.violations and not c.application_permission_violations
        records.append(dict(legacy_phase_filter=legacy,actual_cam=c.cam,actual_context=c.context(),
                            stopped_at_unfinished_activation=c.context()==(0,1,c.guard)))
    return records

def source_hash(name):
    return sha256((HERE/name).read_text().replace('\r\n','\n').encode()).hexdigest()


def generate():
    cases=[]
    requests=[('normal-offset-0',dict()),('normal-offset-1',dict(schedule=1)),
              ('frozen-all-nine',dict(event=('frozen','all_candidates'))),
              ('partial-scan-all-nine',dict(event=('partial_scan','all_candidates'))),
              ('powered-self-writer',dict(event=('powered','self_writer'))),
              ('retiring-self-writer',dict(event=('retire','self_writer'))),
              ('no-powered-keeper',dict(cold_start=True)),
              ('early-driver',dict(driver_early=True)),
              ('legacy-frozen-reject',dict(event=('frozen','all_candidates'),legacy_reject=True)),
              ('world-only-unload',dict(disable_shunt_at_retire=True))]
    for name,args in requests:
        result=run_case(name,**args);cases.append(result)
        print(name,result['ticks'],result['verdict'],flush=True)
    return dict(status='derived conditional cycle and checked finite source histories; first pass',
                sources={name:source_hash(name) for name in ('CYCLE.md','cycle_model.py')},
                arithmetic=arithmetic(),rotating_stage=rotating_stage_check(),already_entry_abort=already_entry_abort_check(),unknown_cam_route=unknown_cam_route_check(),cases=cases)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true');g.add_argument('--check',action='store_true')
    args=p.parse_args();result=json.loads(json.dumps(generate(),sort_keys=True));path=HERE/'cycle_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',newline='\n')
    else:
        actual=json.loads(path.read_text())
        assert actual==result,'Result differs; inspect the change before regenerating'
    print('cycle record '+('written' if args.write else 'matches'),flush=True)


if __name__=='__main__':main()
