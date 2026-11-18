"""Explicit A-prime completion of the held physical-gate failure boundary.

Local source semantics and checks, not unchanged-A entailment or a family proof.
"""
from __future__ import annotations
import argparse
import ast
from dataclasses import dataclass
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import types

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
FROZEN='fb85a7606f45e52d0cd48e023ab9776dd526640c'
PREFIX='theories-and-designs/byzantine-control/local-control/'
RATE=2**31
WORD=(1<<256)-1
UPDATE_WORK=1024
LOCAL_ACTUATOR_LIMIT=68
PREDICATE_PERIOD_MAX=Q(101,100)
PREDICATE_WORK=2048


def need(value,message):
    if not value:raise AssertionError(message)


def natural(value,bound,name):
    need(type(value) is int and 0<=value<bound,name+' outside finite interface')


def frozen(name):
    return subprocess.check_output(['git','show',FROZEN+':'+PREFIX+name],cwd=REPO).decode('utf-8-sig').replace('\r\n','\n')


def digest(text):return hashlib.sha256(text.replace('\r\n','\n').encode()).hexdigest()


def parameters():
    geometry=json.loads(frozen('geometry_results.json'))
    resources=json.loads(frozen('port_resource_results.json'))
    for name,expected in resources['sources'].items():
        need(digest(frozen(name))==expected,'Frozen resource source changed: '+name)
    p=dict(geometry['design']['physical_parameters'])
    p.update(B=geometry['design']['bays'],D=geometry['design']['degree'],
             ABORT_LIMIT=10000,SEAT_LIMIT=12000,ISO_LIMIT=40000,
             DRIVER_AT=p['POWER_AT']+20000,
             EON=Q(resources['transit']['actual_Eon']),EOFF=Q(resources['transit']['actual_Eoff']),
             EMAX=Q(resources['transit']['actual_Emax']))
    need((p['B'],p['D'],p['CLAMP_LIMIT'],p['WARM_AT'])==(80,40,24000,6400000000),'Not the old-style point')
    need(p['GUARD']==p['SEGMENT']//2==16000 and p['SEGMENT']//4==8000,
         'Predecessor stop was confused with the working-band entry')
    return p,geometry,resources


@dataclass(frozen=True)
class Gate:
    name:str
    family:str
    coordinate:str|None
    level:Q|None=None
    side:int|None=None
    body:int|None=None


def catalogue(p):
    need(type(p["B"]) is int and p["B"]>0 and type(p["D"]) is int and p["D"]>0,"Positive finite body/degree counts required")
    coordinates={'cam':Q(2*13*p['SEGMENT']),'abort':Q(p['ABORT_LIMIT']),'blend':Q(p['BLEND_LIMIT'])}
    for family,length in (('clamp',p['CLAMP_LIMIT']),('reset',p['RESET_LIMIT']),('cut',p['CUT_LIMIT']),
                          ('iso',p['ISO_LIMIT']),('shunt',p['ISO_LIMIT']),('carrier',p['SEAT_LIMIT'])):
        for side in range(2):coordinates[f'{family}{side}']=Q(length)
    for side in range(2):
        for body in range(p['B']):coordinates[f'act{side}:{body}']=Q(p['WARM_AT'])
    driven=len(coordinates)
    need(driven==15+2*p['B'],'Controlled coordinate roster changed')
    # Separate body poses remain present after a carrier breaks. No duplicate actuator.
    for side in range(2):
        for body in range(p['B']):coordinates[f'seat{side}:{body}']=Q(p['SEAT_LIMIT'])
    gates=[]
    for band in range(26):
        gates.extend((Gate(f'cam-band:{band}','cam','cam'),Gate(f'cam-stop:{band}','predecessor','cam')))
    gates.append(Gate('normal-cam','normal-routing',None))
    for side in range(2):
        gates.append(Gate(f'writer{side}','writer',f'clamp{side}',Q(p.get('WRITER_CUTOFF',20000)),side))
        for family in ('clamp','reset','cut','iso','shunt'):
            for end in (0,1):gates.append(Gate(f'{family}{side}:end{end}','catch',f'{family}{side}',Q(end)*coordinates[f'{family}{side}'],side))
        gates.append(Gate(f'carrier{side}:seated','catch',f'carrier{side}',Q(p['SEAT_LIMIT']),side))
        for body in range(p['B']):gates.append(Gate(f'activation{side}:{body}','activation',f'act{side}:{body}',None,side,body))
        gates.append(Gate(f'trip{side}','trip',None,None,side))
    gates.extend((Gate('keeper','keeper','blend'),Gate('abort','abort','abort')))
    need(len(gates)==81+2*p['B'] and len(coordinates)==15+4*p['B'],'Gate or physical-pose inventory differs')
    return tuple(gates),coordinates,driven


@dataclass
class Trip:
    enabled:bool=True
    armed:bool=False
    rearms:int=0  # Analyst event count, not a source counter or epoch.
    def transition(self,energy,off,on,*,zero=False,power=False,old_done=True):
        need(not(zero and power),'Nominal actual zero and positive crossing cannot coincide')
        previous=(self.enabled,self.armed)
        if energy<off:self.enabled=False
        if zero:self.armed=True;self.enabled=False
        reset=False
        if power and self.armed and energy>=on and old_done:
            self.enabled=True;self.armed=False;self.rearms+=1;reset=True
        return reset,previous!=(self.enabled,self.armed)


def actual_activation_events(before,after,power,dt,speed,*,bays=80):
    """Actual zero-level closure plus POWER edges on a monotone linear subarc."""
    need(type(bays) is int and bays>0 and len(before)==len(after)==bays and dt>=0 and power>0 and speed>=0,'Wrong actual activation arc')
    need(all(abs(y-x)<=speed*dt for x,y in zip(before,after)),'Arc exceeds source speed')
    # Actual zero is a catch-level closure, also at initial/no-travel entry.
    # Trip.transition reports a discrete change only until it is disabled/armed.
    zero=all(y==0 for y in after)
    crossings=tuple(j for j,(x,y) in enumerate(zip(before,after)) if x<power<=y)
    need(not(zero and crossings),'Actual zero and POWER crossing alias')
    return zero,crossings


@dataclass
class Abort:
    length:Q
    position:Q=Q(0)
    phase:str='NORMAL'
    active:bool=False
    full:bool=False
    normal:bool=True
    def raw(self):return 2*int(self.active)+int(self.full)
    def advance(self,velocity,dt,cleanup,exit_at=Q(0),joint=False):
        """One actual held-direction arc. Reverse entry is prohibited before FULL."""
        need(0<=exit_at<self.length and dt>=0 and abs(velocity)<=Q(11,10),'Abort arc outside source')
        events=[];remaining=dt
        for _ in range(8):
            old=self.phase
            if self.phase=='NORMAL':
                if velocity<=0:break
                self.phase='ENTERING';self.normal=False;self.active=True;events.append('depart-normal')
            elif self.phase=='ENTERING':
                if velocity<=0:break
                duration=(self.length-self.position)/velocity
                if duration>remaining:self.position+=velocity*remaining;break
                self.position=self.length;remaining-=duration;self.phase='FULL';self.full=True;events.append('full-set')
            elif self.phase=='FULL':
                if velocity>=0 or not cleanup:break
                self.phase='RETURN';events.append('return-start')
            else:
                need(self.phase=='RETURN','Unknown abort phase')
                if velocity>=0:break
                if self.active and exit_at>0:
                    duration=max(Q(0),(self.position-exit_at)/(-velocity))
                    if duration<=remaining:
                        self.position=min(self.position,exit_at);remaining-=duration;self.active=False;events.append('active-open');continue
                duration=self.position/(-velocity)
                if duration>remaining:self.position+=velocity*remaining;break
                self.position=Q(0);remaining-=duration
                if not joint and self.active:self.active=False;events.append('active-open')
                self.active=False;self.full=False;self.normal=True;self.phase='NORMAL';events.append('normal-seat/full-clear')
            if remaining==0:break
            need(old!=self.phase,'Urgent unchanged-state abort loop')
        else:raise AssertionError('Abort closure did not consume its phase')
        return events


def keeper(previous,position,length):
    return 0 if position==0 else 1 if position==length else previous


def writer_available(position,cutoff,held=None):
    return position<cutoff if held is None else bool(held)


def cam_band_values(position,band,p,normal=True):
    if not normal:return frozenset({False})
    local=(position-band*p['SEGMENT'])%(26*p['SEGMENT'])
    if local in (Q(p['SEGMENT'],4),Q(3*p['SEGMENT'],4)):
        return frozenset({False,True})  # Actual before/after contact event views.
    return frozenset({Q(p['SEGMENT'],4)<local<Q(3*p['SEGMENT'],4)})


@dataclass(frozen=True)
class Captured:
    owner:int
    kind:str
    target:object
    value:object
    label:str  # Diagnostic label only; cannot rebind the physical target.


class Completion:
    """Only applied physical-site updates reach this interface; not an ISA port."""
    def __init__(self,p,owner=0,energy=Q(10**9),*,catalogue_factory=None):
        self.p=p;self.owner=owner;self.gates,self.limits,self.driven=(catalogue if catalogue_factory is None else catalogue_factory)(p)
        self.positions={name:Q(0) for name in self.limits}
        self.output={g.name:0 for g in self.gates};self.reports={};self.cleanup_sample=(False,False)
        self.held_plane=False;self.jammed=set();self.detached=set()
        self.route=[(i%self.driven,1) for i in range(2*p['D']*self.driven)]
        self.local_drive=[(-1,0),(-1,0)]
        self.local_actuator_heat=Q(0)
        self.U=Q(energy);self.initial_U=self.U;self.heat=Q(0)
        self.pc=[[17]*p['B'] for _ in range(2)]
        self.pending_ir=[[None]*p['B'] for _ in range(2)]
        self.old_parents=[]
        self.spring_q=(Q(3),Q(5));self.spring_phi=(Q(7),Q(11))
        self.E=[Q(19),Q(23)];self.T=[Q(29),Q(31)];self.J=Q(37)
        self.code_identity=object();self.knowledge=object();self.body_machines={}
        self.mechanical_input=Q(0);self.mechanical_heat=Q(0)
        self.events=[]  # Analyst annotations, excluded from source memory.
    def capture(self,kind,target,value,label='request'):
        # Existing held request; capture grants neither funding nor successful update.
        return Captured(self.owner,kind,target,value,label)
    def frame(self):
        return (self.spring_q,self.spring_phi,tuple(self.E),tuple(self.T),self.J,
                self.code_identity,self.knowledge,tuple(self.old_parents),tuple(tuple(x) for x in self.pending_ir),
                tuple((key,m.pending_instruction,tuple(m.C),tuple(m.W),tuple(m.R)) for key,m in sorted(self.body_machines.items())))
    def apply(self,request):
        before=self.frame();position_before=self.positions.copy()
        need(isinstance(request,Captured) and request.owner==self.owner,'Foreign physical update endpoint')
        entry=self._valid_entry(request) and not self.held_plane
        required=Q(UPDATE_WORK)*(1+int(entry))
        # No repeated failed attempt can spend a fresh plane-entry budget.
        paid=required if self.U>=required else min(self.U,Q(UPDATE_WORK))
        self.U-=paid;self.heat+=paid
        if paid<required:
            result='partial-work/no-gate-change'
        else:
            result=self._commit(request)
        self.events.append((request.label,request.kind,result))
        need(self.frame()==before and self.positions==position_before,'Gate update reset retained physical state')
        self.check_U_balance()
        return result
    def check_U_balance(self):
        need(self.U>=0 and self.U+self.heat==self.initial_U,"Gate work disappeared or was invented")
    def _valid_entry(self,r):
        if r.kind=='hold':return isinstance(r.target,str) and r.target in self.output and type(r.value) is int and 0<=r.value<=WORD
        if r.kind=='route':
            if type(r.target) is not int or not 0<=r.target<len(self.route) or not isinstance(r.value,tuple) or len(r.value)!=2:return False
            dest,sign=r.value
            return type(dest) is int and type(sign) is int and -1<=dest<len(self.positions) and sign in (-1,1)
        if r.kind=='local-actuator':return self._valid_local_drive(r)
        if r.kind=='pc':
            return isinstance(r.target,tuple) and len(r.target)==2 and type(r.target[0]) is int and type(r.target[1]) is int and r.target[0] in (0,1) and 0<=r.target[1]<self.p['B']
        return False

    def _valid_local_drive(self,r):
        if type(r.target) is not int or r.target not in (0,1) or type(r.value) is not tuple or len(r.value)!=2:return False
        dest,amplitude=r.value
        return (type(dest) is int and -1<=dest<len(self.positions) and type(amplitude) is int
                and -LOCAL_ACTUATOR_LIMIT<=amplitude<=LOCAL_ACTUATOR_LIMIT and (dest!=-1 or amplitude==0))

    def _commit(self,r):
        if r.kind=='report':
            if not isinstance(r.target,str) or r.target not in self.output or type(r.value) is not int or not 0<=r.value<=WORD:return 'reject'
            self.reports[r.target]=r.value;return 'reported-only'
        if r.kind=='hold':
            if not isinstance(r.target,str) or r.target not in self.output or type(r.value) is not int or not 0<=r.value<=WORD:return 'reject'
            # A gate-plane physical failure freezes actual present outputs first.
            gate=next(g for g in self.gates if g.name==r.target)
            width=4 if gate.family=='activation' else 3 if gate.family=='abort' else 1
            self.held_plane=True;self.output[r.target]=r.value&((1<<width)-1);return 'held'
        if r.kind=='jam':
            if not isinstance(r.target,str) or r.target not in self.positions or type(r.value) is not bool:return 'reject'
            if r.value:self.jammed.add(r.target)
            else:self.jammed.discard(r.target)
            return 'jam' if r.value else 'release-jam'
        if r.kind=='detach':
            if not isinstance(r.target,str) or not r.target.startswith('seat') or r.target not in self.positions or type(r.value) is not bool:return 'reject'
            side=int(r.target[4]);carrier=f'carrier{side}'
            if r.value:self.detached.add(r.target);self.jammed.add(r.target);return 'detached-held'
            if self.positions[r.target]!=self.positions[carrier]:return 'misaligned/hold'
            self.detached.discard(r.target);self.jammed.discard(r.target);return 'reattached'
        if r.kind=='route':
            if type(r.target) is not int or not 0<=r.target<len(self.route):return 'reject'
            if not isinstance(r.value,tuple) or len(r.value)!=2:return 'reject'
            dest,sign=r.value
            if type(dest) is not int or type(sign) is not int or not (-1<=dest<len(self.positions) and sign in (-1,1)):return 'reject'
            self.held_plane=True;self.route[r.target]=(dest,sign);return 'route/held-plane'
        if r.kind=='local-actuator':
            if not self._valid_local_drive(r):return 'reject'
            self.local_drive[r.target]=r.value;self.held_plane=True;return 'local-actuator/held-plane'
        if r.kind=='pc':
            if not isinstance(r.target,tuple) or len(r.target)!=2:return 'reject'
            side,body=r.target
            if type(side) is not int or type(body) is not int or not(side in (0,1) and 0<=body<self.p['B']):return 'reject'
            self.held_plane=True;self.pc[side][body]=0
            if (side,body) in self.body_machines:self.body_machines[(side,body)].reset_entry()
            return 'pc-reset/old-IR-retained'
        return 'reject'
    def held_flow(self,efforts,dt,theta=Q(29),compliance=Q(2),disturbances=None):
        need(self.held_plane and len(efforts)==len(self.route) and dt>=0,'Not a held-mode flow')
        need(all(a==0 for _d,a in self.local_drive),'Use the actual local-reservoir flow law for a live local feed')
        need(theta>=0 and 0<compliance<=2,'Invalid passive failed-mode stroke law')
        need(all(abs(f)<=Q(11,5) for f in efforts),'Incoming field rating exceeded')
        names=tuple(self.positions);before_positions=self.positions.copy()
        attached={name:'carrier'+name[4] for name in names if name.startswith('seat') and name not in self.detached}
        need(all(self.positions[name]==self.positions[carrier] for name,carrier in attached.items()),
             'Attached seating state violates the actual rigid-carrier constraint')
        blocked_carriers={carrier for name,carrier in attached.items() if name in self.jammed}
        forces={name:Q(0) for name in names};resolved=[]
        for force,(dest,sign) in zip(efforts,self.route):
            if dest<0:resolved.append(None);continue
            name=names[dest]
            if name.startswith('seat') and name not in self.detached:name='carrier'+name[4]
            forces[name]+=sign*force;resolved.append((name,sign))
        disturbances={} if disturbances is None else disturbances
        need(all(name in names[:self.driven] and abs(value)<=Q(11,10) for name,value in disturbances.items()),'New disturbance port or exceeded old bound')
        net={name:F+disturbances.get(name,Q(0)) for name,F in forces.items()}
        velocities={}
        for name,F in net.items():
            cap=Q(1) if name=='cam' else Q(11,10)
            v=min(cap,max(Q(0),(F-theta)/compliance))-min(cap,max(Q(0),(-F-theta)/compliance))
            if name in self.jammed or name in blocked_carriers:v=Q(0)
            if name!='cam':
                if self.positions[name]==0 and v<0:v=Q(0)
                if self.positions[name]==self.limits[name] and v>0:v=Q(0)
            velocities[name]=v
        for name in names:
            if name.startswith('seat') and name not in self.detached:velocities[name]=velocities['carrier'+name[4]]
        incoming=sum((f*(Q(0) if d is None else d[1]*velocities[d[0]]) for f,d in zip(efforts,resolved)),Q(0))
        disturbance_power=sum((disturbances.get(n,Q(0))*velocities[n] for n in names),Q(0))
        outgoing=sum((net[n]*velocities[n] for n in names),Q(0))
        need(incoming+disturbance_power==outgoing and outgoing>=0,'Nonduplicating effort/flow pairing failed')
        displacement={name:Q(0) for name in names}
        for name in names:
            if name.startswith('seat') and name not in self.detached:continue
            end=self.positions[name]+dt*velocities[name]
            displacement[name]=dt*velocities[name] if name=='cam' else min(self.limits[name],max(Q(0),end))-self.positions[name]
            self.positions[name]=end%self.limits[name] if name=='cam' else min(self.limits[name],max(Q(0),end))
        for name in names:
            if name.startswith('seat') and name not in self.detached:self.positions[name]=self.positions['carrier'+name[4]]
        need(all(0<=self.positions[n]<=self.limits[n] for n in names),'Material state escaped')
        need(all(self.positions[n]==before_positions[n] for n in self.jammed),'A jammed physical pose moved')
        actual_work=sum((net[n]*displacement[n] for n in names),Q(0))
        supplied=sum((f*(Q(0) if d is None else d[1]*displacement[d[0]]) for f,d in zip(efforts,resolved)),Q(0))
        supplied+=sum((disturbances.get(n,Q(0))*displacement[n] for n in names),Q(0))
        need(actual_work==supplied and actual_work>=0,'Finite displacement lost work at a stop or wrap')
        self.mechanical_input+=supplied;self.mechanical_heat+=actual_work
        return dict(port_power=incoming,independent_disturbance_power=disturbance_power,actual_input_work=supplied,pose_speed_max=max(map(abs,velocities.values())),
                    held_outputs_unchanged=True)


def actuator_rates(state,efforts,theta=Q(29),compliance=Q(2),disturbances=None,bank_ports=((0,0,0),(0,0,0))):
    """Actual ODE/port law on all E, including empty/depleted/backdriven banks."""
    need(state.held_plane and len(efforts)==len(state.route),'Wrong failed-actuator source')
    need(len(bank_ports)==2 and all(len(row)==3 and all(type(x) in (int,Q) and x>=0 for x in row) for row in bank_ports),
         'Expected actual incoming, generic-request and native-proportional bank port rates')
    need(theta>=0 and 0<compliance<=2 and all(abs(f)<=Q(11,5) for f in efforts),'Unrated actuator input')
    names=tuple(state.positions);attached={n:'carrier'+n[4] for n in names if n.startswith('seat') and n not in state.detached}
    need(all(state.positions[n]==state.positions[c] for n,c in attached.items()),'Unformed rigid actuator state')
    blocked={c for n,c in attached.items() if n in state.jammed}
    force={n:Q(0) for n in names};external=[]
    for f,(dest,sign) in zip(efforts,state.route):
        n=None if dest<0 else attached.get(names[dest],names[dest]);external.append((n,sign,f))
        if n is not None:force[n]+=sign*f
    disturbances={} if disturbances is None else disturbances
    need(all(n in names[:state.driven] and abs(v)<=Q(11,10) for n,v in disturbances.items()),'New or unrated disturbance')
    local=[]
    for side,(dest,amplitude) in enumerate(state.local_drive):
        E=state.E[side];need(0<=E<=state.p['EMAX'],'Actual bank stock outside installed capacity')
        g=min(Q(1),E);n=None if dest<0 else attached.get(names[dest],names[dest])
        f=Q(amplitude)*g if n is not None else Q(0)
        local.append((n,f,g if amplitude and n is not None else Q(0)))
        if n is not None:force[n]+=f
    velocities={}
    for n,F in force.items():
        F+=disturbances.get(n,Q(0));cap=Q(1) if n=='cam' else Q(11,10)
        v=min(cap,max(Q(0),(F-theta)/compliance))-min(cap,max(Q(0),(-F-theta)/compliance))
        if n in state.jammed or n in blocked:v=Q(0)
        if n!='cam' and (state.positions[n]==0 and v<0 or state.positions[n]==state.limits[n] and v>0):v=Q(0)
        velocities[n]=v
    for n,c in attached.items():velocities[n]=velocities[c]
    rows=[]
    for side,(n,f,hold) in enumerate(local):
        work=Q(0) if n is None else f*velocities[n]
        positive=max(Q(0),work);negative=max(Q(0),-work)
        draw=2*positive+hold;returned=negative/2;heat=positive+negative/2+hold
        other_incoming,other_request,proportional=map(Q,bank_ports[side])
        other_export=min(Q(1),state.E[side])*other_request+proportional*state.E[side]
        net=returned-draw+other_incoming-other_export
        spill=max(Q(0),net) if state.E[side]==state.p['EMAX'] else Q(0)
        derivative=net-spill
        need(derivative+work+heat+spill+other_export==other_incoming,'Shared reservoir/effort power identity failed')
        need(state.E[side]!=0 or derivative>=0,'Empty actual E exports free work')
        need(state.E[side]!=state.p['EMAX'] or derivative<=0,'Upper stock requires an unrecorded spill')
        rows.append(dict(side=side,endpoint=n,force=f,holding_power=hold,mechanical_power=work,
            draw=draw,returned=returned,heat=heat,overflow_heat=spill,energy_derivative=derivative,
            other_actual_inflow=other_incoming,other_actual_export=other_export))
    incoming=sum((sign*f*velocities[n] for n,sign,f in external if n is not None),Q(0))
    incoming+=sum((f*velocities[n] for n,f in disturbances.items()),Q(0))
    mechanical=sum(((force[n]+disturbances.get(n,Q(0)))*velocities[n] for n in names),Q(0))
    need(incoming+sum((r['mechanical_power'] for r in rows),Q(0))==mechanical and mechanical>=0,
         'Local reservoir force was duplicated or omitted from conjugate work')
    return dict(velocities=velocities,banks=rows,external_input_power=incoming,mechanical_dissipation=mechanical)


def advance_full_stock_actuator_segment(state,efforts,dt):
    """Exact constant-force subarc; callers split at stock1/material boundaries.

    This diagnostic integrator is not the all-stock source definition above.
    Its scope excludes other simultaneous E funding/draw; those ports sum in
    the source ODE. No C/IR/physical medium is reset.
    """
    dt=Q(dt);need(dt>=0,'Negative local drive segment')
    law=actuator_rates(state,efforts);before=state.frame();E0=state.E[:]
    need(all(0<=E0[r['side']]+dt*r['energy_derivative']<=state.p['EMAX']
             and (r['holding_power']==0 or E0[r['side']]>=1 and E0[r['side']]+dt*r['energy_derivative']>=1)
             and r['overflow_heat']==0 for r in law['banks']),'Split at the actual stock boundary')
    end={n:state.positions[n]+dt*v for n,v in law['velocities'].items()}
    need(all(n=='cam' or 0<=end[n]<=state.limits[n] for n in end),'Split at the actual material boundary')
    end['cam']%=state.limits['cam']
    state.positions.update(end)
    for r in law['banks']:state.E[r['side']]+=dt*r['energy_derivative']
    loss=dt*sum((r['heat']+r['overflow_heat'] for r in law['banks']),Q(0))
    state.local_actuator_heat+=loss
    state.mechanical_input+=dt*law['mechanical_dissipation'];state.mechanical_heat+=dt*law['mechanical_dissipation']
    need(sum(state.E)+loss+dt*law['mechanical_dissipation']==sum(E0)+dt*law['external_input_power'],
         'Existing E stock and actual actuator work do not balance')
    after=state.frame();need(before[:2]==after[:2] and before[3:]==after[3:],'Local actuator rewrote another store/parent')
    return dict(duration=dt,bank_before=E0,bank_after=state.E[:],actuator_heat=loss,
        mechanical_heat=dt*law['mechanical_dissipation'],external_work=dt*law['external_input_power'])


def physical_contact_snapshot(state):
    """The fixed22+6B actual contact wires captured at one local strobe."""
    p=state.p;z=state.positions;out={}
    for side in range(2):
        for kind,position,level in (('cut-end','cut',p['CUT_LIMIT']),('cut-zero','cut',0),
                ('clamp-end','clamp',p['CLAMP_LIMIT']),('clamp-zero','clamp',0),
                ('reset-end','reset',p['RESET_LIMIT']),('reset-zero','reset',0),
                ('shunt-zero','shunt',0),('iso-zero','iso',0)):
            out[(kind,side)]=z[position+str(side)]==level
        out[('blend',side)]=z['blend']==side*p['BLEND_LIMIT']
        out[('low-E',side)]=state.E[side]<p['EOFF']
        out[('cam-entry',side)]=z['cam']==side*13*p['SEGMENT']
        for body in range(p['B']):
            out[('zero',side,body)]=z[f'act{side}:{body}']==0
            out[('warm',side,body)]=z[f'act{side}:{body}']==p['WARM_AT']
            out[('seat',side,body)]=z[f'seat{side}:{body}']==p['SEAT_LIMIT']
    need(len(out)==22+6*p['B'],'Fixed physical contact input count changed')
    return out


def fold_contact_snapshot(snapshot,bays):
    zero=[all(snapshot[('zero',s,j)] for j in range(bays)) for s in range(2)]
    warm=[any(snapshot[('warm',s,j)] for j in range(bays)) for s in range(2)]
    seated=[all(snapshot[('seat',s,j)] for j in range(bays)) for s in range(2)]
    cutoff=[snapshot[('cut-end',s)] and snapshot[('low-E',s)] for s in range(2)]
    connected=[snapshot[('cut-zero',s)] and snapshot[('shunt-zero',s)] for s in range(2)]
    releases=[];cleanup=[]
    for half in range(2):
        cold=1-half
        releases.extend((cutoff[cold],zero[cold],snapshot[('clamp-zero',cold)],
            snapshot[('reset-zero',cold)],snapshot[('reset-end',cold)],seated[cold],
            snapshot[('clamp-end',cold)],connected[cold],warm[cold],snapshot[('blend',cold)],
            cutoff[half],snapshot[('iso-zero',cold)],True))
        cleanup.append(snapshot[('blend',half)] and cutoff[cold] and zero[cold]
            and snapshot[('clamp-zero',cold)] and snapshot[('reset-zero',cold)] and snapshot[('cam-entry',half)])
    # cut/off has already been folded, so each six-input cleanup uses5 ANDs.
    need(type(bays) is int and bays>0 and 6*(bays-1)+2+2+2*5==6*bays+8,'Fixed binary fold count changed')
    return tuple(releases),tuple(cleanup)


class PredecessorSampler:
    """One fixed physical oscillator and one paid28-output latch bank, not P."""
    def __init__(self,state,period=Q(1),remaining=None):
        period=Q(period);remaining=period if remaining is None else Q(remaining)
        need(1<=period<=PREDICATE_PERIOD_MAX and 0<remaining<=period,'Invalid local sampler phase')
        self.state=state;self.period=period;self.remaining=remaining
        self.samples=0;self.work=Q(0)  # Analyst counts, not runtime epochs.
    def clock_rate(self):
        need(self.state.U>=0,'Clock supply is outside its hard nonnegative domain')
        return Q(0) if self.state.held_plane else min(Q(1),self.state.U)
    def flow_clock(self,dt):
        # Exact constant-U segment; varying U uses integral g(U(t)) dt.
        dt=Q(dt);rate=self.clock_rate()
        need(dt>=0 and rate*dt<=self.remaining,'Split at the actual local sample strobe')
        self.remaining-=rate*dt
        if self.state.held_plane:return 'held-clock-stopped'
        if rate==0:return 'depleted-clock-stopped'
    def strobe(self):
        s=self.state
        if s.held_plane:return 'held-plane/no-autonomous-gate-update'
        need(self.remaining==0,'No physical predecessor strobe')
        self.remaining=self.period
        # One coherent pre-state capture of the fixed local contact inputs;
        # no intermediate mechanical update or writable raw-I read occurs.
        paid=min(s.U,Q(PREDICATE_WORK));s.U-=paid;s.heat+=paid;self.work+=paid
        if paid==PREDICATE_WORK:
            values,cleanup=fold_contact_snapshot(physical_contact_snapshot(s),s.p['B'])
            for j,value in enumerate(values):s.output['cam-stop:'+str(j)]=int(value)
            s.cleanup_sample=cleanup
        # Partial work cannot buy a free fail-closed rewrite. Old committed
        # contact data remain held until another actual fully funded strobe.
        self.samples+=1
        s.check_U_balance()
        return 'captured' if paid==PREDICATE_WORK else 'partial-work/held-releases'
    def cam_segment(self,effort,dt):
        """Actual held contact stop, with a zero-velocity boundary continuation."""
        F=Q(effort);dt=Q(dt);s=self.state
        need(not s.held_plane and abs(F)<=2*s.p['D']*Q(11,5) and dt>=0
             and self.clock_rate()*dt<=self.remaining,'Not one held nominal cam interval')
        v=min(Q(1),max(Q(0),(F-29)/2))-min(Q(1),max(Q(0),(-F-29)/2))
        if 'cam' in s.jammed or not s.output['normal-cam']:v=Q(0)
        position=s.positions['cam'];circ=s.limits['cam'];travel=v*dt
        if travel:
            direction=1 if travel>0 else -1;distance=abs(travel)
            for band in range(26):
                if s.output['cam-stop:'+str(band)]:continue
                stop=Q(band*s.p['SEGMENT']+s.p['GUARD'])
                gap=((stop-position)*direction)%circ
                distance=min(distance,gap)
            s.positions['cam']=(position+direction*distance)%circ
            actual_work=F*direction*distance
            need(actual_work>=0,'Predecessor contact created mechanical work')
            s.mechanical_input+=actual_work;s.mechanical_heat+=actual_work
        self.flow_clock(dt)
        return s.positions['cam']


def predecessor(state,half,phase):
    p=state.p;z=state.positions;cold=1-half
    off=lambda side:state.E[side]<p['EOFF']
    activation=lambda side:[z[f'act{side}:{j}'] for j in range(p['B'])]
    if phase==0:return z[f'cut{cold}']==p['CUT_LIMIT'] and off(cold)
    if phase==1:return all(a==0 for a in activation(cold))
    if phase==2:return z[f'clamp{cold}']==0
    if phase==3:return z[f'reset{cold}']==0
    if phase==4:return z[f'reset{cold}']==p['RESET_LIMIT']
    if phase==5:return all(z[f'seat{cold}:{j}']==p['SEAT_LIMIT'] for j in range(p['B']))
    if phase==6:return z[f'clamp{cold}']==p['CLAMP_LIMIT']
    if phase==7:return z[f'cut{cold}']==0 and z[f'shunt{cold}']==0
    if phase==8:return any(a==p['WARM_AT'] for a in activation(cold))
    if phase==9:return z['blend']==cold*p['BLEND_LIMIT']
    if phase==10:return z[f'cut{half}']==p['CUT_LIMIT'] and off(half)
    if phase==11:return z[f'iso{cold}']==0
    need(phase==12,'Unknown physical cam predecessor')
    return True


def abort_cleanup(state,anchor):
    p=state.p;z=state.positions;other=1-anchor
    return (z['blend']==anchor*p['BLEND_LIMIT'] and z[f'cut{other}']==p['CUT_LIMIT']
            and state.E[other]<p['EOFF']
            and all(z[f'act{other}:{j}']==0 for j in range(p['B']))
            and z[f'clamp{other}']==0 and z[f'reset{other}']==0
            and z['cam']==anchor*13*p['SEGMENT'])


def surviving_catch(engaged,position,endpoint,toward_force,threshold=Q(28)):
    # Same physical catch: open before reverse motion; no stale positive assertion.
    if position!=endpoint or toward_force < -threshold:return False
    if position==endpoint and toward_force>threshold:return True
    return engaged


def frozen_machine_and_parent_check(p,geometry):
    module=types.ModuleType('_gate_old_machine')
    module.__file__=str(HERE.parent/'local-control'/'program_model.py')
    sys.modules[module.__name__]=module
    exec(compile(frozen('program_model.py'),module.__file__,'exec'),module.__dict__)
    need(digest(module.SOURCE.read_text(encoding='utf-8-sig'))==digest(frozen('program_source.py')),'Local compiler source differs from frozen image')
    data=dict(geometry['design']);data['physical_parameters']=tuple(tuple(x) for x in data['physical_parameters'])
    compiled=module.Compiler(module.Design(**data)).compile()
    image_hash=hashlib.sha256(b''.join(x.to_bytes(24,'little') for x in compiled.image)).hexdigest()
    need(image_hash==geometry['compiler']['encoded_image_sha256'],'Nominal programme changed')
    need(not any('gate' in name or 'fixture' in name for name in module.PRIMITIVES),'Ordinary ISA acquired gate-mode access')
    portmod=types.ModuleType('_gate_old_ports');portmod.__file__=str(HERE.parent/'local-control'/'port_model.py')
    sys.modules[portmod.__name__]=portmod
    exec(compile(frozen('port_model.py'),portmod.__file__,'exec'),portmod.__dict__)
    machine=module.Machine(compiled);ports=module.RawPorts(compiled)
    actual_bank=portmod.Reservoir.filled(p['EON']+20480)
    cell=portmod.Slot(actual_bank,price=Q(20480),recharge_time=Q(1,4*2**26))
    cell.recharge(cell.recharge_time)
    need(cell.offer(cell.recharge_time,'captured native instruction',Q(3,4*2**26)),'Actual old parent was not funded')
    machine.C[0]=module.encode(module.STOREC,3,4)
    machine.R[3]=991;machine.R[4]=7
    need(machine.launch(funded=cell.active and cell.charge==20480),'Stored native parent did not latch')
    captured=machine.pending_instruction
    actual_before=(captured,tuple(machine.C),tuple(machine.W),tuple(machine.R),cell.charge)
    cold=[Q(0)]*p['B']
    zero,crossings=actual_activation_events(cold,cold,Q(p['POWER_AT']),Q(0),Q(11,10))
    zero_latch=Trip(False,False)
    reset,changed=zero_latch.transition(p['EON'],p['EOFF'],p['EON'],zero=zero,power=bool(crossings),old_done=False)
    need(changed and not reset and zero_latch.armed,'Initial zero did not close the physical arm catch')
    for _ in range(8):
        reset,changed=zero_latch.transition(p['EON'],p['EOFF'],p['EON'],zero=zero,old_done=False)
        need(not reset and not changed,'A held zero level minted another gate event')
    need(actual_before==(machine.pending_instruction,tuple(machine.C),tuple(machine.W),tuple(machine.R),cell.charge),
         'Actual zero closure erased or refilled a retained native parent')
    machine.C[:]=compiled.image[:]
    state=Completion(p);state.E[0]=actual_bank.energy;state.body_machines[(0,0)]=machine
    need(state.apply(state.capture('pc',(0,0),0))=='pc-reset/old-IR-retained','Gate override did not act on actual PC')
    need(machine.pending_instruction==captured and machine.C==compiled.image,'Physical PC reset erased a captured parent')
    state.apply(state.capture('hold','trip0',0));machine.powered=False
    need(cell.elapse(Q(1,2**26),lambda _:need(machine.complete(ports),'Old native parent stopped')),'Funded completion disappeared')
    portmod.conservation(actual_bank,[cell])
    need(machine.C[7]==991,'Old funded native write disappeared or rebound')
    need(not machine.complete(ports),'Old native parent completed twice')
    return dict(frozen_image_sha256=image_hash,encoded_cells=len(compiled.image),program_cells=len(compiled.nodes),
                ordinary_ISA_has_no_gate_mode_port=True,actual_captured_STOREC_survived_PC_reset=True,
                actual_captured_STOREC_survived_zero_level_closure=True,
                resulting_old_word=991,physical_address=7,actual_parent_work=actual_bank.spent,old_capsule_remaining=cell.charge,
                scope='Actual ordinary instruction, retained reservation and finite source-cell energy profile; not a whole source run')


def nominal_checks(p):
    # Exact frozen nominal TripLatch transition, with its illustrative energy scale removed.
    source=ast.parse(frozen('initial_return_model.py'))
    node=next(n for n in source.body if isinstance(n,ast.ClassDef) and n.name=='TripLatch')
    env={'require':need};exec(compile(ast.Module(body=[node],type_ignores=[]),'<frozen TripLatch>','exec'),env)
    cases=0
    for enabled in (False,True):
      for armed in (False,True):
       for energy in (Q(1),Q(5,2),Q(3),Q(4)):
        for zero,power in ((False,False),(True,False),(False,True)):
         for done in (False,True):
            a=Trip(enabled,armed);b=env['TripLatch']();b.enabled=enabled;b.armed=armed
            reset,_=a.transition(energy,Q(2),Q(3),zero=zero,power=power,old_done=done)
            b.event(energy,zero=zero,power_cross=power,old_instruction_done=done)
            need((a.enabled,a.armed,a.rearms)==(b.enabled,b.armed,b.resets),'Nominal TripLatch changed')
            cases+=1
    cold=[Q(0)]*80;high=cold.copy();high[0]=Q(p['POWER_AT'])
    zero,crossings=actual_activation_events(cold,cold,Q(p['POWER_AT']),Q(0),Q(11,10))
    need(zero and not crossings,'Already-zero/no-travel stop entry did not offer the arm closure')
    zero_cases=0
    for enabled in (False,True):
      for armed in (False,True):
        latch=Trip(enabled,armed)
        reset,changed=latch.transition(p['EON'],p['EOFF'],p['EON'],zero=zero,old_done=False)
        need(not reset and not latch.enabled and latch.armed and changed==(enabled or not armed),
             'Actual-zero closure lost its initial-state or idempotence law')
        for _ in range(16):
            reset,changed=latch.transition(p['EON'],p['EOFF'],p['EON'],zero=zero,old_done=False)
            need(not reset and not changed and latch.rearms==0,'Repeated actual zero minted a reset/event')
        zero_cases+=1
    # A cold all-zero bank with no previous retract edge now has a valid arm.
    cold_start=Trip(False,False)
    cold_start.transition(p['EON'],p['EOFF'],p['EON'],zero=zero)
    zero,powers=actual_activation_events(cold,high,Q(p['POWER_AT']),Q(p['POWER_AT'])/Q(11,10),Q(11,10))
    need(not zero and powers==(0,),'Real POWER edge not generated')
    reset,_=cold_start.transition(p['EON'],p['EOFF'],p['EON'],power=bool(powers))
    need(reset and cold_start.rearms==1 and not cold_start.armed,'Cold all-zero closure did not permit a later fresh POWER crossing')
    trip=Trip(False,True);reset,_=trip.transition(p['EON'],p['EOFF'],p['EON'],power=True,old_done=False)
    need(not reset,'Pending old instruction was ignored')
    zero,powers=actual_activation_events(high,high,Q(p['POWER_AT']),Q(1),Q(11,10))
    reset,_=trip.transition(p['EON'],p['EOFF'],p['EON'],zero=zero,power=bool(powers),old_done=True)
    need(not reset,'Held high level minted a second power event')
    zero,powers=actual_activation_events(high,cold,Q(p['POWER_AT']),Q(p['POWER_AT'])/Q(11,10),Q(11,10))
    trip.transition(p['EON'],p['EOFF'],p['EON'],zero=zero)
    zero,powers=actual_activation_events(cold,high,Q(p['POWER_AT']),Q(p['POWER_AT'])/Q(11,10),Q(11,10))
    reset,_=trip.transition(p['EON'],p['EOFF'],p['EON'],power=bool(powers))
    need(reset and trip.rearms==1,'Fresh zero/POWER cycle did not consume its arm')
    trip.transition(p['EOFF']-1,p['EOFF'],p['EON'])
    for _ in range(10):trip.transition(p['EON'],p['EOFF'],p['EON'])
    need(not trip.enabled and trip.rearms==1,'Energy rise at old high activation rearmed')
    abort_reports=[]
    for joint in (False,True):
        abort=Abort(Q(p['ABORT_LIMIT']))
        enter=abort.advance(Q(1),Q(1),True)
        abort.advance(Q(-1),Q(2),True)
        need(abort.position==1 and abort.phase=='ENTERING','Partial entry returned before FULL')
        enter+=abort.advance(Q(1),Q(p['ABORT_LIMIT']),True)
        abort.advance(Q(-1),Q(1),False)
        need(abort.phase=='FULL','Missing physical cleanup did not hold')
        ret=abort.advance(Q(-1),Q(p['ABORT_LIMIT']),True,exit_at=Q(0),joint=joint)
        need(abort.phase=='NORMAL' and abort.raw()==0 and abort.normal,'Abort return failed')
        abort_reports.append(dict(joint=joint,entry=enter,return_events=ret))
    path=[Q(0),Q(1,2),Q(1),Q(3,4),Q(1),Q(0),Q(0),Q(1)]
    K=0;changes=0;variation=Q(0)
    for a,b in zip(path,path[1:]):
        variation+=abs(b-a);new=keeper(K,b,Q(1));changes+=new!=K;K=new
    need(changes<=1+variation,'Keeper variation charge failed')
    fixture=Completion(p);physical_predicates=tuple(predecessor(fixture,h,s) for h in range(2) for s in range(13))
    fixture.code_identity=object()
    need(physical_predicates==tuple(predecessor(fixture,h,s) for h in range(2) for s in range(13)),'Predecessor gate inspected the programme image')
    fixture.positions['cut1']=Q(p['CUT_LIMIT'])
    need(abort_cleanup(fixture,0),'Actual cleanup geometry was not recognized')
    fixture.positions['act1:79']=Q(1)
    need(not abort_cleanup(fixture,0),'One actual live activation was omitted')
    catch=False
    for F in (Q(29),Q(0),Q(-29),Q(-29),Q(0),Q(29)):
        catch=surviving_catch(catch,Q(12000),Q(12000),F)
    need(catch,'Retained physical catch lost its positive end-stop branch')
    need(not surviving_catch(True,Q(11999),Q(12000),Q(0)),'Positive catch survived away from its actual endpoint')
    cutoff=Q(20000)
    need([writer_available(x,cutoff) for x in (cutoff-1,cutoff,cutoff+1)]==[True,False,False],'Writer predicate changed')
    for band in range(26):
        need(cam_band_values(Q(band*p['SEGMENT']+p['GUARD']),band,p)=={True},'Interior cam gate changed')
        need(cam_band_values(Q(band*p['SEGMENT']),band,p)=={False},'Dead travel disappeared')
    return dict(trip_transition_cases=cases,genuine_zero_and_power_events=True,
                already_zero_closure_cases=zero_cases,repeated_zero_is_idempotent=True,cold_zero_then_fresh_power=True,
                stale_or_pending_power_countercases=True,abort=abort_reports,
                keeper_changes=changes,keeper_variation=variation,
                writer_admission_is_predicate=True,cam_interior_and_deadband_cases=52,
                predecessor_cases=26,cleanup_uses_every_actual_activation=True,source_scope='Nominal local kernels and linear physical arcs, not full old-machine histories')


def failed_checks(p):
    retained=Completion(p)
    for g in retained.gates:retained.output[g.name]=1
    before_levels=retained.output.copy()
    retained.apply(retained.capture('hold','writer0',0))
    need(all(retained.output[k]==v for k,v in before_levels.items() if k!='writer0'),'Plane entry erased an unaddressed contact')
    model=Completion(p);original=model.frame();parents=[('word','body17',3,991),('instruction','body5',13),('packet','receiver9',7)]
    model.old_parents.extend(parents);original=model.frame()
    requests=[model.capture('hold',g.name,1,'held-'+g.family) for g in model.gates]
    for r in requests:need(model.apply(r)=='held','Failed gate family lacked a held outcome')
    need(model.held_plane,'Failed gate plane did not enter its held law')
    need(model.frame()==original,'Mode changes erased a retained parent or store')
    outputs=model.output.copy();frame=model.frame()
    F=[Q(0)]*len(model.route)
    # Thirty-four actual two-unit fields can be rerouted into the wrong B cut.
    target=list(model.positions).index('cut1')
    intended=list(model.positions).index('cut0')
    for contributor in range(34):
        i=contributor*model.driven+intended
        F[i]=Q(2);need(model.apply(model.capture('route',i,(target,1)))=='route/held-plane','Route update failed')
    result=model.held_flow(F,Q(1))
    need(model.positions['cut1']>0 and model.output==outputs,'Wrong held routing became harmless')
    need(model.frame()==frame,'Held flow reset unrelated physical stocks')
    model.apply(model.capture('jam','cut1',True));position=model.positions['cut1']
    model.held_flow(F,Q(100));need(model.positions['cut1']==position,'Jam did not allow time to pass')
    stop=Completion(p);stop.apply(stop.capture('hold','normal-cam',1))
    stop.positions['cut0']=Q(p['CUT_LIMIT'])
    positive=[Q(0)]*len(stop.route)
    positive[list(stop.positions).index('cut0')]=Q(11,5)
    need(stop.held_flow(positive,Q(100))['actual_input_work']==0,'Material stop invented displacement work')
    # Report corruption alone never changes actual gate state or selects held mechanics.
    reports=Completion(p);reports.apply(reports.capture('report','trip0',WORD))
    need(not reports.held_plane and reports.output['trip0']==0,'Raw report became a gate-control path')
    # Captured actual endpoint survives later caller-label changes; application order is real.
    late=Completion(p);captured=late.capture('hold','writer0',0,'old-captured')
    late.apply(late.capture('hold','writer0',1,'new-applied'))
    late.apply(captured);need(late.output['writer0']==0,'Old captured update was erased by a newer label')
    malformed=Completion(p);same=malformed.output.copy()
    for kind,target,value in (('hold',[],1),('report',{},0),('jam',[],True),('detach',[],False),('route',True,(0,1)),('route',0,(0,True)),('pc',([],0),0)):
        need(malformed.apply(malformed.capture(kind,target,value))=='reject','Malformed finite request escaped bounded rejection')
    need(malformed.apply(malformed.capture('hold','missing-gate',1))=='reject' and malformed.output==same,'Malformed update changed a gate')
    partial_entry=Completion(p,energy=Q(1536))
    need(partial_entry.apply(partial_entry.capture('hold','writer0',1))=='partial-work/no-gate-change' and partial_entry.heat==1024 and not partial_entry.held_plane,'Repeated partial plane-entry work exceeds the root bill')
    nofund=Completion(p,energy=Q(17));before=nofund.output.copy()
    need(nofund.apply(nofund.capture('hold','writer0',1))=='partial-work/no-gate-change','Unfunded work was granted')
    need(nofund.output==before and nofund.U==0 and nofund.heat==17,'Partial work did not retain a time-compatible state')
    native=Completion(p);token=object();native.pending_ir[0][3]=token
    need(native.apply(native.capture('pc',(0,3),0))=='pc-reset/old-IR-retained','Explicit PC override absent')
    need(native.pc[0][3]==0 and native.pending_ir[0][3] is token,'PC reset cancelled old IR')
    # Misaligned attachment cannot teleport a physical body.
    detach=Completion(p);detach.positions['seat0:0']=Q(7)
    need(detach.apply(detach.capture('detach','seat0:0',True))=='detached-held','Body pose lost')
    need(detach.apply(detach.capture('detach','seat0:0',False))=='misaligned/hold','Reattachment teleported a body')
    return dict(gate_family_counts={f:sum(g.family==f for g in model.gates) for f in sorted({g.family for g in model.gates})},
        held_gate_cases=len(requests),wrong_target_force=68,wrong_target_motion=result,
        persistent_jam_time=100,retained_parent_count=len(parents),late_captured_target_preserved=True,
        partial_work_consumed=17,malformed_update_rejected=True,malformed_type_countercases=7,unaddressed_contact_levels_preserved=True,report_is_not_actual_control=True,pc_keeps_pending_IR=True,
        body_reattachment_requires_actual_alignment=True,
        scope='All named gate-family held outcomes and exact pose/port-input continuations; full producer history is not simulated')


def rigid_jam_checks(p):
    """Real attached constraints, independent detachment, and the same port work."""
    rows=[]
    for side in range(2):
        state=Completion(p);state.apply(state.capture('hold','normal-cam',1))
        names=list(state.positions);carrier='carrier'+str(side)
        first='seat'+str(side)+':0';last='seat'+str(side)+':'+str(p['B']-1)
        target=names.index(carrier);source=names.index('cut'+str(side))
        efforts=[Q(0)]*len(state.route)
        for contributor in range(34):
            wire=contributor*state.driven+source;efforts[wire]=Q(2)
            need(state.apply(state.capture('route',wire,(target,1)))=='route/held-plane','Carrier route failed')
        state.apply(state.capture('jam',first,True))
        still=state.positions.copy();frame=state.frame()
        jam=state.held_flow(efforts,Q(1))
        need(state.positions==still and jam['actual_input_work']==0 and state.frame()==frame,
             'Attached-body jam moved the rigid carrier or created mechanical work')
        state.apply(state.capture('jam',last,True))
        state.apply(state.capture('jam',first,False))
        one_left=state.held_flow(efforts,Q(1))
        need(state.positions==still and one_left['actual_input_work']==0,
             'Releasing one body cancelled another attached jam')
        state.apply(state.capture('jam',last,False))
        release=state.held_flow(efforts,Q(1))
        need(state.positions[carrier]==Q(11,10) and release['actual_input_work']==Q(374,5),
             'Explicit jam release did not restore paid rigid motion')
        need(all(state.positions['seat'+str(side)+':'+str(j)]==state.positions[carrier] for j in range(p['B'])),
             'Released attached members lost rigid identity')
        # Detachment changes the attachment relation only, preserving every pose.
        state.apply(state.capture('jam',first,True));position=state.positions[first]
        before=state.positions.copy();state.apply(state.capture('detach',first,True))
        need(state.positions==before and first in state.jammed,'Detachment silently moved or released the held body')
        detach=state.held_flow(efforts,Q(1))
        need(state.positions[first]==position and state.positions[carrier]==Q(11,5)
             and detach['actual_input_work']==Q(374,5),'Detached jam incorrectly blocked or followed its former carrier')
        before=state.positions.copy()
        need(state.apply(state.capture('detach',first,False))=='misaligned/hold' and state.positions==before,
             'Reattachment reset an actual body pose')
        state.apply(state.capture('jam',first,False))
        need(first in state.detached,'Jam release silently reattached the body')
        rows.append(dict(side=side,applied_force=68,attached_jam_work=jam['actual_input_work'],
            remaining_member_jam_work=one_left['actual_input_work'],released_rigid_work=release['actual_input_work'],
            detached_carrier_work=detach['actual_input_work'],detached_body_position=position,
            final_carrier_position=state.positions[carrier],all_attached_members=p['B']))
    invalid=Completion(p);invalid.apply(invalid.capture('hold','normal-cam',1))
    invalid.positions['seat0:0']=Q(1);before=invalid.positions.copy()
    try:invalid.held_flow([Q(0)]*len(invalid.route),Q(1))
    except AssertionError:pass
    else:raise AssertionError('An inconsistent attached pose was silently synchronized')
    need(invalid.positions==before,'Rejected rigid-state input changed its poses')
    return dict(cases=rows,rigid_input_not_repaired_by_pose_reset=True,
        release_does_not_detach=True,detach_preserves_jam_and_pose=True,
        scope='Both actual carrier groups, first/last body jams, actual incoming-field work; no full-source geometry admission')


def force_variation_supplier(p):
    """Bound the adopted voltage-gated fixed-current primitive, not all faults."""
    boundary=json.loads(frozen('boundary_results.json'))
    transducer=json.loads(frozen('transducer_results.json'))
    for record in (boundary,transducer):
        for name,expected in record['sources'].items():
            need(digest(frozen(name))==expected,'Frozen field supplier changed: '+name)
    bp=boundary['parameters'];tp=transducer['parameters']
    bmax=Q(bp['source_full_interval'][1]);umax=Q(tp['source_voltage_cap'])
    rmin,rmax=map(Q,bp['actual_transducer_resistance'])
    need([rmin,rmax]==list(map(Q,tp['series_resistance_range'])),'Boundary changed the actual winding resistance')
    inductance=Q(bp['actual_transducer_L']);xmax=Q(tp['current_cap_derived'])
    kappa=Q(tp['fixed_force_gain']);velocity=Q(tp['uniform_velocity'])
    gmin=Q(tp['minimum_braking_drop']);gmax=Q(tp['maximum_braking_drop'])
    need(bmax==umax and Q(bp['field_cap'])==kappa*xmax,'Boundary/force ratings disagree')
    need(bp['installed_pairs']==transducer['addresses']['host_signed_pairs']==2*p['D']*(15+2*p['B']),'Fixed endpoint array count changed')
    need(gmin>kappa*velocity and umax-rmin*xmax-gmin+kappa*velocity<0,'Retained-current invariance does not hold')
    # Execute the frozen decoder, not its result flag. Gates select drive requests
    # before the one signed voltage drive; no current/force is multiplied here.
    module=types.ModuleType('_gate_field_supplier')
    module.__file__=str(HERE.parent/'local-control'/'transducer_model.py')
    sys.modules[module.__name__]=module
    exec(compile(frozen('transducer_model.py'),module.__file__,'exec'),module.__dict__)
    need((module.UMAX,module.R,module.RMAX,module.XMAX,module.KAPPA,module.VMAX)==
         (umax,rmin,rmax,xmax,kappa,velocity),'Supplier record does not match actual constants')
    cases=0
    for cam in range(-32,32):
      for rewind in range(-32,32):
       for normal in (False,True):
        for reverse in (False,True):
            record=(cam+32)*64+32*4096+10*262144+(rewind+32)*(1<<40)
            decoded=module.decode_requests(record,p['B'],normal_cam_gate=normal,rewind_gate=reverse)
            desired=(cam if normal else 0)-(rewind if reverse else 0)
            need(decoded[('cam',)]==desired and sum(bool(v) for v in decoded.values())<=1,'Gate/alias placement changed')
            need(max(module.drive_for(desired))<=umax,'Combined gate request escaped voltage bound')
            cases+=1
    pair=module.Pair();pair.advance(1,module.drive_for(20),0)
    previous_force=pair.force
    neutral=32*64+32*4096+10*262144+32*(1<<40)
    decoded=module.decode_requests(neutral,p['B'],normal_cam_gate=False,rewind_gate=False)
    need(decoded[('cam',)]==0 and pair.force==previous_force and previous_force>0,'Closing a drive gate erased retained force')
    current_slew=(bmax+rmax*xmax+gmax+kappa*velocity)/inductance
    field_variation=2*p['D']*2*kappa*current_slew
    return dict(current_slew=current_slew,field_variation=field_variation,
        supplier_parameters=dict(voltage_cap=bmax,resistance=[rmin,rmax],inductance=inductance,current_cap=xmax,
            braking_drop=[gmin,gmax],force_gain=kappa,velocity_cap=velocity),
        actual_gated_alias_cases=cases,closing_voltage_gate_retains_old_force=True,
        source_locators=['BOUNDARIES.md:13-35','TRANSDUCER.md:15-35','TRANSDUCER.md:58-62',
                         'transducer_model.py:357-370','boundary_results.json:parameters'],
        held_plane_required_for=['current-law or voltage-bound alteration outside this primitive',
            'endpoint/direction rebinding or downstream variable multiplication outside fixed-current placement',
            'gate-plane or force-routing alteration'],
        scope='Surviving plane only with the adopted bounded voltage before fixed endpoint currents; physical faults outside this class select explicit held-plane semantics')


def resource_and_event_bounds(p,r):
    gates,coordinates,driven=catalogue(p)
    routes=2*p['D']*driven
    entries=len(gates)+len(coordinates)+routes+2+1
    bits=1024*entries+PREDICATE_WORK  # Regular slots/header, one wider sampler.
    available=r['point']['receiver']['available_raw_padding']-r['point']['receiver']['consumed_raw_padding']
    need(bits<=available,'Mode descriptors exceed unconsumed owner padding')
    start=r['point']['receiver']['consumed_raw_padding']
    # Offset in each old record's1072 genuinely unused bits; live976 bits untouched.
    def address(bit):
        record,offset=divmod(start+bit,1072)
        return record,976+offset
    need(address(bits-1)[0]<1420796 and address(0)[1]>=976,'Descriptor injection escapes raw padding')
    # One fixed ingress channel covers malformed addresses; labels add no ports.
    channels=entries+1
    address_depth=(channels-1).bit_length()
    need(address_depth<=256,'Fixed physical address path exceeds control-work allocation')
    extra_burst=2*bits+UPDATE_WORK
    old_rate=Q(r['point']['upstream_rate']);old_burst=Q(r['point']['upstream_burst']);U=Q(r['point']['new_upstream_capacity'])
    removed_clock=bits*RATE;new_clock=bits*RATE
    new_rate=old_rate-removed_clock+new_clock
    new_burst=old_burst+extra_burst
    margin=U-new_burst-2*new_rate
    need(new_rate<=old_rate and margin>PREDICATE_WORK,'Unchanged harvest/capacity cannot fund the source completion')
    supplier=force_variation_supplier(p)
    current_slew=supplier['current_slew'];field_variation_rate=supplier['field_variation']
    reversal_gap=2*(Q(28)-Q(11,10))
    need(reversal_gap>0,'A small measurable disturbance removes the reversal charge')
    return dict(gates=len(gates),geometry_coordinates=len(coordinates),force_inputs=routes,control_entries=entries,physical_update_channels=channels,maximum_pending_requests=channels,
        mode_descriptor_bits=bits,fixed_address_path_depth=address_depth,available_unconsumed_padding=available,padding_first=address(0),padding_last=address(bits-1),
        added_recoverable_stock=0,added_operation_cells=0,added_sampler_clocks=1,
        local_existing_bank_actuator_ports=2,local_actuator_effort_limit=LOCAL_ACTUATOR_LIMIT,
        predecessor_capture_work=PREDICATE_WORK,predecessor_latched_outputs=28,
        applied_update_work=UPDATE_WORK,additional_burst=extra_burst,
        old_upstream_rate=old_rate,new_upstream_rate_upper=new_rate,new_upstream_burst=new_burst,
        same_upstream_capacity=U,usable_reserve_lower=margin,
        same_total_nonthermal_capacity=r['point']['total_nonthermal_inventory_upper'],
        ordinary_current_slew_upper=current_slew,ordinary_force_variation_rate=field_variation_rate,force_variation_supplier=supplier,
        ordinary_reversal_gap=reversal_gap,
        event_formula='R(T)<=(entries+1)*(1+2^31*T); held gates contribute0 autonomous jumps; each surviving primitive has the stated travel/consume bound; PC writes are finite descendants',
        ordinary_field_scope='Retained fixed-orientation post-gate current realization at surviving receivers; no rate inferred merely from a force cap',
        allocation_scope='Design-time relocation of unused source-owner padding into physical fixture-control cells; not raw-I write access')


def local_actuator_checks(p):
    state=Completion(p);target=list(state.positions).index('clamp0')
    need(state.apply(state.capture('local-actuator',0,(target,68)))=='local-actuator/held-plane','Local work path is absent')
    state.E[0]=Q(1000);state.E[1]=Q(0)
    # Control-feed loss is not loss of the existing separately retained E.
    state.heat+=state.U;state.U=Q(0)
    conserved=state.frame();zero=[Q(0)]*len(state.route)
    segment=advance_full_stock_actuator_segment(state,zero,Q(1))
    need(state.positions['clamp0']==Q(11,10) and state.E[0]==Q(4247,5),
         'Actual existing E did not fund the independent local actuator')
    need(state.U==0 and state.frame()[:2]==conserved[:2] and state.frame()[3:]==conserved[3:],
         'Local drive borrowed another reservoir or reset a retained parent')
    cases=0;shared_cases=0
    for stock in (Q(0),Q(1,4),Q(1),Q(19),p['EMAX']):
      for amplitude in (-68,-10,0,10,68):
        state.E[0]=stock;state.local_drive[0]=(target,amplitude)
        state.positions['clamp0']=Q(100)
        for external_sign in (-1,0,1):
            efforts=zero.copy()
            for contributor in range(34):efforts[contributor*state.driven+target]=Q(2*external_sign)
            law=actuator_rates(state,efforts);row=law['banks'][0]
            if amplitude in (-68,68) and external_sign==0 or amplitude==10 and external_sign==-1:
                shared=actuator_rates(state,efforts,bank_ports=((Q(3),Q(5),Q(1,10)),(Q(0),Q(7),Q(0))))
                need(shared['banks'][0]['other_actual_export']==min(Q(1),stock)*5+stock/10,
                     'Existing consumers spent a duplicate or unthrottled E balance')
                shared_cases+=1
            need(stock!=0 or row['force']==row['holding_power']==row['draw']==0,'Empty E supplied independent force')
            cases+=1
    jam=Completion(p);seat=list(jam.positions).index('seat0:0')
    jam.apply(jam.capture('local-actuator',0,(seat,68)));jam.apply(jam.capture('jam','seat0:0',True))
    holding=advance_full_stock_actuator_segment(jam,zero,Q(1))
    need(jam.positions['carrier0']==0 and jam.positions['seat0:0']==0 and jam.E[0]==18
         and holding['mechanical_heat']==0 and holding['actuator_heat']==1,
         'A retained static local actuator lost its real holding debit or rigid jam')
    state.E[0]=p['EMAX'];state.local_drive[0]=(target,10)
    efforts=zero.copy()
    for contributor in range(34):efforts[contributor*state.driven+target]=Q(-2)
    backdrive=actuator_rates(state,efforts)['banks'][0]
    need(backdrive['mechanical_power']==-11 and backdrive['overflow_heat']==Q(9,2),
         'Backdrive/upper spill was silently discarded')
    return dict(actual_E_driven_segment=segment,jammed_holding_segment=holding,instantaneous_stock_and_port_cases=cases,
        empty_stock_has_no_local_force=True,shared_existing_bank_port_cases=shared_cases,backdrive_at_actual_cap=backdrive,
        preserved_other_stocks_and_parents=True,added_recoverable_stock=0,
        scope='Explicit bounded conjugate-work source law on existing E; exact full-stock segment and all-stock algebra, not a full hybrid solver')


def predecessor_sampler_checks(p,g,r):
    state=Completion(p);state.output['normal-cam']=1;state.positions['cam']=Q(p['GUARD'])
    state.positions['cut1']=Q(p['CUT_LIMIT']);state.E[1]=p['EOFF']+1
    sample=PredecessorSampler(state,period=PREDICATE_PERIOD_MAX,remaining=Q(1,2))
    need(sample.cam_segment(Q(68),Q(1,2))==p['GUARD'],'Closed sampled predecessor lacked a stopped continuation')
    sample.strobe();need(state.output['cam-stop:0']==0,'High energy was silently called off')
    levels=[]
    for low in (True,False,True,False,True,False):
        state.E[1]=p['EOFF']-1 if low else p['EOFF']+1
        sample.flow_clock(sample.remaining);sample.strobe();levels.append(state.output['cam-stop:0'])
    need(levels==[1,0,1,0,1,0] and state.positions['cam']==p['GUARD'],
         'Recrossing energy needs the sampled event bound, not cam direction variation')
    state.E[1]=p['EOFF']-1;sample.flow_clock(sample.remaining);sample.strobe()
    state.E[1]=p['EOFF']+1
    moved=sample.cam_segment(Q(68),Q(1,2))
    need(moved==Q(p['GUARD'])+Q(1,2) and state.mechanical_input==34,
         'Held predecessor release did not consume its actual cam effort')
    # Physical held failure overrides actual output; periodic sampling does
    # not restore nominal truth at a failed fixture.
    state.apply(state.capture('hold','cam-stop:0',1));old=state.output.copy()
    sample.flow_clock(sample.remaining)
    need(sample.strobe()=='held-plane/no-autonomous-gate-update' and state.output==old,'Sampler repaired a physical gate fault')
    empty=Completion(p,energy=Q(17));off=PredecessorSampler(empty)
    off.flow_clock(Q(1));need(off.strobe()=='partial-work/held-releases' and empty.U==0 and empty.heat==17,
         'Unfunded predecessor capture invented work or a release')
    need(all(empty.output['cam-stop:'+str(j)]==0 for j in range(26)),'Partial capture opened a predecessor')
    empty.output['cam-stop:0']=1;remaining=off.remaining;off.flow_clock(remaining)
    need(off.remaining==remaining and empty.output['cam-stop:0']==1,'Empty U supplied clock work or a free fail-closed rewrite')
    low=Completion(p,energy=Q(1,4));slow=PredecessorSampler(low);slow.flow_clock(Q(1))
    need(slow.remaining==Q(3,4),'Unfunded oscillator silently retained nominal service')
    slow.flow_clock(Q(3));need(slow.remaining==0,'Positive fractional clock never reached its real strobe')
    need(slow.strobe()=='partial-work/held-releases' and low.U==0,'Fractional-stock strobe lost its actual outcome')
    slow.flow_clock(Q(100));need(slow.remaining==slow.period,'Empty stock blocked time or advanced clock phase')
    exact_low=Completion(p,energy=Q(1,4));exact_clock=PredecessorSampler(exact_low)
    exact_clock.flow_clock(Q(4));need(exact_clock.remaining==0,'One exact constant-U segment missed the strobe')
    overshoot=PredecessorSampler(Completion(p,energy=Q(1,4)))
    try:overshoot.flow_clock(Q(5))
    except AssertionError:pass
    else:raise AssertionError('A real sample boundary was skipped')
    need(overshoot.remaining==1,'Rejected overshoot changed clock phase')
    # GUARD names the16000 predecessor stop, not the8000 band entry g.
    edge=Completion(p);edge.output['normal-cam']=1;edge.positions['cam']=Q(p['GUARD'])-Q(1,2)
    boundary_clock=PredecessorSampler(edge)
    boundary_clock.cam_segment(68,Q(1,2));need(edge.positions['cam']==16000,'Wrong actual predecessor stop')
    boundary_clock.cam_segment(68,Q(1,2));need(edge.positions['cam']==16000 and edge.mechanical_input==34,'Closed stop lacks actual hold continuation')
    entry=Completion(p);entry.output['normal-cam']=1;entry.positions['cam']=Q(p['SEGMENT'],4)
    entry_clock=PredecessorSampler(entry);entry_clock.cam_segment(68,Q(1))
    need(entry.positions['cam']==8001,'Working-band entry was incorrectly installed as a predecessor stop')

    # Abort FULL uses a sample from the same coherent physical tuple.
    clean=Completion(p);clean.positions['cut1']=Q(p['CUT_LIMIT']);clean.E[1]=p['EOFF']+1
    clean.positions['abort']=Q(p['ABORT_LIMIT']);clean.output['abort']=3
    release=PredecessorSampler(clean);carrier=Abort(Q(p['ABORT_LIMIT']),Q(p['ABORT_LIMIT']),'FULL',True,True,False)
    raw=physical_contact_snapshot(clean);preds,cleanups=fold_contact_snapshot(raw,p['B'])
    need(preds==tuple(predecessor(clean,h,k) for h in range(2) for k in range(13))
         and cleanups==tuple(abort_cleanup(clean,h) for h in range(2)),'Fixed sampled folds changed raw predicates')
    release.flow_clock(Q(1));release.strobe()
    need(not clean.cleanup_sample[0],'Abort cleanup falsely sampled high energy as off')
    carrier.advance(Q(-1),Q(1,2),clean.cleanup_sample[0]);need(carrier.phase=='FULL','Unsatisfied cleanup lacked a hold continuation')
    clean.E[1]=p['EOFF']-1;release.flow_clock(release.remaining);release.strobe()
    need(clean.cleanup_sample[0],'Actual coherent cleanup sample was lost')
    clean.E[1]=p['EOFF']+1
    carrier.advance(Q(-1),Q(1,2),clean.cleanup_sample[0])
    clean.positions['abort']=carrier.position;clean.output['abort']=carrier.raw()
    need(carrier.phase=='RETURN' and carrier.position==Q(p['ABORT_LIMIT'])-Q(1,2),
         'Held sampled cleanup did not consume one abort return transition')
    source=json.loads(frozen('port_source_results.json'));timing=source['return_schedule']
    for name,expected in source['sources'].items():need(digest(frozen(name))==expected,'Frozen timing source differs: '+name)
    half_off=Q(r['transit']['half_off_upper']);cert=g['compiler']['processing_certificate']
    cut_clear=half_off+Q(cert['last_possible_word_after_cutoff'])+Q(cert['cut_withdrawal'])+PREDICATE_PERIOD_MAX
    need(502+488+28+502+256<=PREDICATE_WORK,'Sampler native bill exceeds its actual allocation')
    need(cut_clear<100,'Sample delay consumes the actual cut-tail allowance')
    recognition=Q(g['timing']['unknown_cam_probe'])+PREDICATE_PERIOD_MAX
    need(recognition<Q(g['timing']['formation']),'Existing recognition prefix does not cover the sampler')
    # A conservative positive-route update: one added sample wait per normal
    # band in the partial pass and each of two fresh halves. Abort rewind
    # uses its separate route. These remain conditional itinerary consumers.
    added_half=13*PREDICATE_PERIOD_MAX;extra=3*added_half+PREDICATE_PERIOD_MAX
    H0=timing['conditional_return_H'];H1=H0+(extra.numerator+extra.denominator-1)//extra.denominator
    rate=Q(timing['original_raw_acquisition_rate'])
    cover=1+2+int(3+2*rate*H1)
    need(cover==timing['cover_at_original_rate']==6,'Sampled releases change the actual incident cover')
    shortest=Q(timing['unchanged_earliest_timeout'])
    band=Q(g['timing']['normal_band_travel'])/13
    short_upper=max(Q(value)+band+PREDICATE_PERIOD_MAX for key,value in timing['phase_bounds'].items()
                    if int(key.split('_')[0]) not in (1,8))
    need(short_upper<shortest and short_upper<Q(timing['unchanged_nontransferable_ready_window']),
         'Added sample delay defeats a short-phase timeout or whole-bank job margin')
    return dict(period=[1,PREDICATE_PERIOD_MAX],sample_work=PREDICATE_WORK,one_actual_fixture_clock=True,
        coherent_physical_contact_inputs=502,contact_fold_operations=488,latched_outputs=28,
        capture_fold_scrub_control_upper=502+488+28+502+256,abort_cleanup_same_snapshot=True,
        energy_recross_samples=levels,recross_scope='finite event-map inputs, not an admitted E/T trajectory',cam_work_after_release=34,retained_wrong_held_gate=True,
        unfunded_capture_work=17,depleted_clock_stops=True,constant_quarter_stock_strobe_time=4,zero_stock_time_continuation=100,
        phase_overshoot_rejected=True,actual_predecessor_stop=p['GUARD'],working_band_entry=p['SEGMENT']//4,
        partial_capture_retains_old_levels=True,unknown_cam_with_sampling=recognition,cut_clear_with_sampling=cut_clear,
        added_half_bound=added_half,added_partial_bound=added_half,added_abort_bound=PREDICATE_PERIOD_MAX,conservative_return_addition=extra,
        old_conditional_H=H0,new_conditional_H=H1,original_raw_acquisition_rate=rate,unchanged_cover=cover,
        new_half_bound=Q(timing['half_cycle'])+added_half,new_partial_bound=Q(timing['unchanged_partial_bound'])+added_half,
        new_abort_bound=Q(timing['abort'])+PREDICATE_PERIOD_MAX,new_short_stage_with_cam_upper=short_upper,
        scope='Changed sample/hold predecessor interface; local clock/energy/stop checks and conditional timing rebinding, not unchanged-A trace equivalence')


def normalize(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:normalize(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [normalize(v) for v in x]
    return x


def generate():
    p,g,r=parameters()
    nom=nominal_checks(p);failed=failed_checks(p);rigid=rigid_jam_checks(p);bounds=resource_and_event_bounds(p,r)
    machine=frozen_machine_and_parent_check(p,g)
    actuator=local_actuator_checks(p);sampled=predecessor_sampler_checks(p,g,r)
    names=('PORT-SOURCE.md','PORT-RESOURCES.md','port_resource_results.json','HYBRID.md','INITIAL-RETURN.md',
           'initial_return_model.py','CLAMP.md','CYCLE.md','GEOMETRY.md','geometry_results.json',
           'RUNTIME-PORTS.md','FAULT-MAP.md','port_source_results.json','BOUNDARIES.md','TRANSDUCER.md','boundary_model.py','boundary_results.json','transducer_model.py','transducer_results.json','program_model.py','program_source.py','port_model.py')
    return normalize(dict(scope="Explicit minimal A-prime gate-failure completion; not frozen-A entailment or full-family admission",
        frozen_base=FROZEN,python_version=sys.version,
        frozen_sources_sha256_lf={n:digest(frozen(n)) for n in names},
        sources_sha256_lf={n:digest((HERE/n).read_text(encoding='utf-8-sig')) for n in ('GATE-SOURCE-COMPLETION.md','gate_source_completion.py')},
        nominal=nom,failed=failed,rigid_jam=rigid,local_actuator=actuator,predecessor_sampling=sampled,bounds=bounds,actual_machine=machine,
        unresolved=['independent source/fidelity review of the explicit A-prime failure restriction',
                    'complete gate/field energy and port embedding plus source-to-core composition under the pinned surviving-plane placement',
                    'physical descriptor-placement/writer map and same resource ledger integration',
                    'common initialized recurrence, full positive-family and same-A-prime proof-burden checks'],
        parameterization=dict(reusable_laws=['finite actual-body zero/POWER rule','stock-backed conjugate work on the same bank E',
            'rigid attachment/jam constraint','sample/hold event and work composition'],
            pre_extension_template_formulas=dict(gate_blocks='81+2B',controlled_coordinates='15+2B',
                represented_coordinates='15+4B',incoming_pairs='2*d*(15+2B)',physical_contact_inputs='22+6B',contact_folds='6B+8'),
            executable_bound_to=dict(bodies_per_bank=80,degree=40,primary_image_cells=8192),
            threshold_B_admitted=False,
            threshold_residuals=['actual new field/control/reset contact inventory and fault palette',
                'removed private-writer versus threshold field cutoff correspondence','B-specific E/U/parent/reset/alias funding map',
                'new contact/clock placement and descriptor-address injection','B timing and source-to-core interrupted-history composition']),
        no_correct_image_or_permission_gate=True,old_source_entails_completion=False,
        baseline_bytes_modified=False,full_family_complete=False,program_complete=False))


def main():
    parser=argparse.ArgumentParser(description=__doc__);choice=parser.add_mutually_exclusive_group(required=True)
    choice.add_argument('--write',action='store_true');choice.add_argument('--check',action='store_true');args=parser.parse_args()
    result=generate();path=HERE/'gate_source_completion_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
    else:need(json.loads(path.read_text(encoding='utf-8'))==result,'Gate source completion record differs')
    print('PASS minimal A-prime local gate completion; full-family/source-to-core proof remains open')


if __name__=='__main__':main()
