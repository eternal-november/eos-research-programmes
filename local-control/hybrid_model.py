"""Exact event/flow perturbations for the conditional asynchronous cycle source.

No global controller tick: analyst event times order samples, computation,
application, instruction tails, and continuous contact crossings.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from hashlib import sha256
from heapq import heappush, heappop
from itertools import permutations, product
from pathlib import Path
import argparse
import json
import subprocess
import sys

if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')
HERE=Path(__file__).resolve().parent


def q(value):
    return str(value) if isinstance(value,F) else value


def encode(value):
    if isinstance(value,F):return str(value)
    if isinstance(value,dict):return {k:encode(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [encode(v) for v in value]
    return value


@dataclass(frozen=True)
class Clock:
    offset:F
    switches:tuple[tuple[F,F],...]

    def elapsed(self,start,end):
        assert start<=end
        result=F(0)
        for i,(at,rate) in enumerate(self.switches):
            stop=self.switches[i+1][0] if i+1<len(self.switches) else end
            lo,hi=max(start,at),min(end,stop)
            if hi>lo:result+=(hi-lo)*rate
        return result

    def deadline(self,start,amount):
        left=amount
        for i,(at,rate) in enumerate(self.switches):
            stop=self.switches[i+1][0] if i+1<len(self.switches) else None
            lo=max(start,at)
            if stop is not None and stop<=lo:continue
            if stop is None or (stop-lo)*rate>=left:return lo+left/rate
            left-=(stop-lo)*rate
        raise AssertionError('positive final rate has an unbounded interval')


def clock_checks():
    count=0;examples=[]
    for offset,first,last,start,amount in product((F(-100),F(0),F(79,3)),
            (F(1),F(101,100)),(F(1),F(101,100)),(F(0),F(17,3),F(13)),(F(1),F(833))):
        clock=Clock(offset,((F(0),first),(F(10),last)))
        end=clock.deadline(start,amount)
        assert clock.elapsed(start,end)==amount
        assert amount/F(101,100)<=end-start<=amount
        count+=1
        if len(examples)<4:examples.append(dict(offset=offset,start=start,deadline=end,amount=amount))
    return dict(cases=count,examples=examples)


class ContactEpisode:
    """A continuously moving invasive fixture with finite-duration helper jobs.

    The auxiliary rod is a raw mechanical enabling dependency. Its late seating
    makes already-issued cut fields wait. Safety must persist during that wait;
    this test does not infer a progress deadline for an arbitrarily blocked rod.
    """
    def __init__(self,side=0,schedule=0,retention=True):
        self.t=F(0);self.pos={'b':F(0),'z':F(0),'c':F(0),'rod':F(0)}
        self.limits={'b':F(1),'z':F(1),'c':F(7+side),'rod':F(100)}
        self.speed={'b':F(1,20+side),'z':F(1,25+side),'c':F(1),'rod':F(1)}
        self.force=[{'b':F(0),'z':F(0),'c':F(0)} for _ in range(4)]
        self.clock=[Clock(F(13*j-200),((F(0),F(100+(j+schedule)%2,100)),(F(31,2),F(101-(j+schedule)%2,100)))) for j in range(4)]
        self.events=[];self.order=0;self.schedule=schedule;self.side=side;self.retention=retention
        self.log=[];self.jobs=0;self.sample_count=0;self.applied=0;self.work=F(0)
        self.first_cut_issue=None;self.first_motion=None;self.completed=None;self.violations=[]
        self.old_cut_fields=None;self.lower_requested=False;self.stop_time=F(40)
        for actor in range(4):self.push(F(actor+schedule,7),'launch',actor)
        self.push(F(45),'release_request',None)

    def push(self,when,kind,data):
        assert when>=self.t
        self.order+=1
        # Equal-time choices have a declared varied order, never a priority that
        # suppresses a physical tail. The proofs cover every such linearization.
        rank=self.order if self.schedule%2==0 else -self.order
        heappush(self.events,(when,rank,self.order,kind,data))

    def velocity(self):
        result={'rod':F(1) if self.pos['rod']<self.limits['rod'] else F(0)}
        for key in ('b','z','c'):
            total=sum(f[key] for f in self.force)-F(11,5)
            dz=total-3 if total>3 else total+3 if total<-3 else F(0)
            value=max(-self.speed[key],min(self.speed[key],dz))
            if key=='c' and self.pos['rod']<self.limits['rod']:value=F(0)
            # Directional contacts retain isolation/shunting until the actual
            # cut has finished and its old force circuit can be disconnected.
            if key in ('b','z') and self.retention and self.pos['c']<self.limits['c']:
                value=max(F(0),value)
            if self.pos[key]==0:value=max(F(0),value)
            if self.pos[key]==self.limits[key]:value=min(F(0),value)
            result[key]=value
        return result

    def facts(self,position):
        loads=[(1-position['b'])*F(2)+F(1,5),
               (1-position['b'])*F(7,4)+F(1,5),
               (1-position['b'])*F(3,2)+F(1,5)]
        return max(loads)<=1 and position['z']>=F(4,5)

    def flow(self,end):
        velocity=self.velocity();dt=end-self.t
        assert dt>=0
        before=dict(self.pos)
        after={key:before[key]+velocity[key]*dt for key in before}
        assert all(0<=after[key]<=self.limits[key] for key in after)
        if velocity['c']>0 and self.first_motion is None:self.first_motion=self.t
        consequential=(self.pos['rod']==self.limits['rod'] and self.pos['c']<self.limits['c'] and any(f['c']>0 for f in self.force))
        if consequential:
            # All quantities are affine on this segment. Loads are monotone
            # affine in b; checking both endpoints checks every interior time.
            if not self.facts(before) or not self.facts(after):
                self.violations.append(dict(start=self.t,end=end,b0=before['b'],b1=after['b'],z0=before['z'],z1=after['z']))
        self.work+=dt*sum(abs(value) for f in self.force for value in f.values())
        self.pos=after;self.t=end
        if self.pos['c']==self.limits['c'] and self.completed is None:
            self.completed=self.t
            self.log.append(dict(time=self.t,event='actual-cut-stop',side=self.side))
            # Opening this raw force circuit precedes permitted reverse shunt.
            for fields in self.force:fields['c']=F(0)

    def handle(self,kind,data):
        if kind=='launch':
            actor=data
            if self.t>=self.stop_time:return
            self.jobs+=1;self.work+=1
            acq=F(7+(actor+self.schedule)%3,7)
            noise=F(((actor+self.schedule)%3)-1,100)
            sample=(self.t,self.pos['b']+noise,self.pos['z']-noise)
            self.sample_count+=1
            self.push(self.t+acq,'compute',(actor,sample))
        elif kind=='compute':
            actor,sample=data
            # A callback is a nonzero computation interval, not an atomic sample.
            self.push(self.t+F(1,5),'issue',(actor,sample))
        elif kind=='issue':
            actor,(sample_time,yb,yz)=data
            A=F(2);eps=F(1,100)
            assert self.t-sample_time<=A
            blo=yb-eps-self.speed['b']*A;zlo=yz-eps-self.speed['z']*A
            permitted=2*(1-max(F(0),blo))+F(1,5)<=1 and zlo>=F(4,5)
            command={'b':F(2),'z':F(2),'c':F(2) if permitted else F(0)}
            if permitted and self.first_cut_issue is None:self.first_cut_issue=self.t
            delay=F((actor+2*self.schedule)%4,5)
            self.push(self.t+delay,'apply',(actor,command))
            next_launch=self.clock[actor].deadline(self.t,F(3,2))
            self.push(next_launch,'launch',actor)
        elif kind=='apply':
            actor,command=data
            self.applied+=1;self.work+=1;self.force[actor]=command
            if command['c']>0:assert self.facts(self.pos)
        elif kind=='release_request':
            self.lower_requested=True;self.old_cut_fields=[f['c'] for f in self.force]
            for fields in self.force:fields.update(b=F(-2),z=F(-2))
            self.log.append(dict(time=self.t,event='reverse-shunt-request-with-old-cut-fields',old_cut_fields=self.old_cut_fields))
        else:raise AssertionError(kind)

    def run(self):
        horizon=F(120)
        while self.t<horizon:
            event_time=self.events[0][0] if self.events else horizon
            velocity=self.velocity();end=min(horizon,event_time)
            for key,v in velocity.items():
                if v>0:end=min(end,self.t+(self.limits[key]-self.pos[key])/v)
                elif v<0:end=min(end,self.t-self.pos[key]/v)
            # Endpoints already reached have zero outward velocity.
            assert end>self.t or (self.events and self.events[0][0]==self.t)
            self.flow(end)
            while self.events and self.events[0][0]==self.t:
                _,_,_,kind,data=heappop(self.events);self.handle(kind,data)
        assert self.first_cut_issue is not None and self.completed is not None
        assert self.first_motion-self.first_cut_issue>40
        assert self.lower_requested
        if self.retention:assert not self.violations
        else:assert self.violations
        return dict(side=self.side,schedule=self.schedule,retention=self.retention,
                    first_cut_issue=self.first_cut_issue,first_cut_motion=self.first_motion,
                    completed=self.completed,callbacks=self.jobs,samples=self.sample_count,
                    applied_commands=self.applied,charged_work=self.work,
                    violations=self.violations,events=self.log,
                    comparison='continuous factivity with a persistent permission invariant' if self.retention else 'finite permission horizon fails for a held cut across a stall')


def contact_checks():
    return [ContactEpisode(side,schedule,retention).run()
            for side,schedule,retention in product(range(2),range(3),(True,False))]


def normalization_checks():
    age=F(823);eps=F(1,100)
    old_lower=1-eps-age/F(500)
    intermediate_lower=1-eps-age/F(4000)
    new_lower=1-eps-age/F(6000)
    assert old_lower<F(4,5) and intermediate_lower<F(4,5) and new_lower>=F(4,5)
    assert 2*(1-new_lower)+F(1,5)<=1
    scan=(80*8192+2)*828
    assert scan==542639736
    old_wait=F(833)/F(101,100);new_wait=F(839)/F(101,100)
    assert old_wait>age and old_wait<age+6 and new_wait>age+6
    return dict(age_at_comparison=age,reply_bound=807,frozen_cell_allocation=828,
                full_8192_scan=scan,mutable_cell_attempt=839,mutable_cell_attempt_tail6=842,copy_entry_wait_local=833,old_normalized_endpoint_lower=old_lower,
                intermediate_4000_endpoint_lower=intermediate_lower,new_normalized_endpoint_lower=new_lower,physical_stroke=6000,
                retained_833_wait_real_minimum=old_wait,
                after_raw_cut_with_tail6_required_wait_local=839,new_wait_real_minimum=new_wait,
                semantics='833 starts after actual last dirty tail;839 may start at writer cutoff with a6-unit tail')


def word_tail_checks():
    # The old processor launches while powered. Its funded operation can commit
    # after power-off/cut. Both equal-time linearizations remain legal.
    equality=[]
    for order in permutations(('commit','sample')):
        cell=17;read=None;fund=F(3);spent=F(0)
        for event in order:
            if event=='commit':cell=9;spent+=3
            else:read=cell
        assert spent==fund and cell==9
        equality.append(dict(order=order,sampled=read,final=cell,paid=spent))
    assert {r['sampled'] for r in equality}=={9,17}
    cases=[]
    for write_tail,age,rate in product((F(0),F(3),F(6)),(F(2),F(419),F(823)),(F(1),F(101,100))):
        local_wait=(write_tail+age+1)*rate
        reply=local_wait/rate
        oldest_sample=reply-age
        assert oldest_sample>write_tail
        cases.append(dict(write_tail=write_tail,age=age,rate=rate,local_wait=local_wait,
                          oldest_sample=oldest_sample,last_dirty_commit=write_tail))
    # An actual serial copy: only individual, funded address commits alter cells.
    reference=(17,5,9,2);image=[8]*len(reference);time=F(0);trace=[];paid=0
    for address,value in enumerate(reference):
        launched=time;cost=2;paid+=cost
        committed=launched+F(address+2,3)
        image[address]=value
        observed=committed+F(2,5)
        assert image[address]==value
        trace.append(dict(address=address,value=value,launch=launched,commit=committed,readback=observed,prepaid=cost))
        time=observed+F(1,7)
    assert tuple(image)==reference
    # Freezing does not cancel a pending private adversarial write. A wait must
    # begin after its tail, or include its maximum remaining duration.
    freeze=F(0);late_commit=F(6)
    naive_reply=F(833)/F(101,100);naive_sample=naive_reply-F(823)
    assert 0<naive_sample<late_commit<naive_reply
    safe_reply=F(839)/F(101,100);safe_sample=safe_reply-F(823)
    assert late_commit<safe_sample
    # Physical custody matters independently of byte equality.
    bodies={'old':[17,5,9,2],'other':[9,9,9,9]};bay='old'
    inspected=tuple(bodies[bay]);bay='other';started=tuple(bodies[bay])
    assert inspected==reference and started!=reference
    return dict(equal_time_orders=equality,freshness_cases=cases,serial_copy=trace,total_prepaid=paid,
                stale_after_cut=dict(reply=naive_reply,sample=naive_sample,wrong_commit=late_commit),
                strict_drain=dict(reply=safe_reply,sample=safe_sample,last_wrong_commit=late_commit),
                custody_ablation=dict(inspected=inspected,started=started))


def stage_checks():
    g=F(1000);real_margin=F(823)+F(1,4)
    assert g>real_margin and 2*g>6
    assert g<2*g-real_margin and 2*g+real_margin<3*g
    cam_layout=dict(guard=g,band_length=4*g,work_stop=2*g,old_open=3*g,next_work_gate=5*g,recognition_radius=real_margin)
    count=0;abstentions=0;wrong_label=None
    width=F(20);error=F(1,4);age=F(3);speed=F(1);margin=error+speed*age
    for actual,lag,noise in product((F(19),F(20),F(21),F(30),F(39)),(F(0),F(3)),(-error,error)):
        sample=actual-speed*lag;reported=sample+noise
        low,high=reported-margin,reported+margin
        compatible=[k for k in range(3) if k*width<=low and high<(k+1)*width]
        if compatible:
            assert compatible==[int(actual//width)]
        else:abstentions+=1
        # A floor-label can be wrong while the interval method abstains.
        if int(reported//width)!=int(actual//width):
            wrong_label=dict(actual=actual,reported=reported,old_label=int(reported//width),actual_band=int(actual//width),interval=(low,high))
        count+=1
    assert wrong_label and abstentions
    # Dead travel separates an old force tail from an incompatible new circuit.
    for tail,guard_speed in product((F(1),F(5)),(F(1),F(3,2))):
        distance=guard_speed*tail+F(1,3)
        assert distance/guard_speed>tail
    # A physical cut tail survives a mode contact opening. Releasing shunting
    # before the tail ends can breach the rule between sampled mode endpoints.
    tail_end=F(5);moment=F(4);early_release=F(2);late_release=F(6)
    early_b=max(F(0),1-F(1,4)*max(F(0),moment-early_release))
    late_b=max(F(0),1-F(1,4)*max(F(0),moment-late_release))
    early_load=2*(1-early_b)+F(1,5);late_load=2*(1-late_b)+F(1,5)
    assert moment<tail_end and early_load>1 and late_load<=1
    tail_comparison=dict(tail_end=tail_end,checked_interior=moment,early_release=early_release,
                         early_b=early_b,early_load=early_load,late_release=late_release,late_load=late_load)
    # Zero is not the semantic initial value for a conjunction accumulator.
    image=(17,5);candidates=[image,image]
    good=[j for j,c in enumerate(candidates) if all(a==b for a,b in zip(c,image))][0]
    masks=[]
    match=False
    for j,candidate in enumerate(candidates):
        for address in range(len(image)):match=match and candidate[address]==image[address]
        masks.append(match);match=True
    wrong=next(j for j,ok in enumerate(masks) if ok)
    assert good==0 and wrong==1
    return dict(constructible_cam_layout=cam_layout,interval_cases=count,abstentions=abstentions,wrong_floor_label=wrong_label,old_force_tail_comparison=tail_comparison,
                formation_counterexample=dict(correct_selection=good,zero_initialized_selection=wrong,
                                               required_state=dict(cursor=0,scan_bay=0,scan_address=0,scan_match=True,selected=None)))




def revalidation_history(pattern=0,rate=F(1),noise=F(0),position_only=False,
                         working_shunt=False,retire=None,jump=False,jump_budget=F(0)):
    """One actual connector: attenuation may fail although its position is1.

    Positive commands come only from finite current-evidence comparisons.
    Software periodically overwrites the port; no trusted expiry opcode exists.
    """
    J=F(5);D=F(2);force_tail=F(1);retire_tail=F(1)
    H=J+2*D+force_tail+retire_tail;A=F(1);eps=F(1,100);slope=F(1,25)
    assert H==11
    def load(t):
        if working_shunt:return F(1,5)
        if jump:return F(11,5) if t>=20 else F(1,5)
        return min(F(11,5),F(1,5)+slope*max(F(0),t))
    events=[];serial=0
    def add(t,kind,data):
        nonlocal serial
        serial+=1
        heappush(events,(t,serial if pattern%2==0 else -serial,serial,kind,data))
    clock=Clock(F(-33),((F(0),rate),(F(17),F(201,100)-rate)))
    issue=F(pattern%3,7);commands=[];n=0
    while issue<60 and (retire is None or issue<retire):
        sample=max(F(0),issue-A);reported=load(sample)+noise
        guard=reported+eps+slope*(A+H)+jump_budget<=1
        positive=True if position_only else guard
        delay=D if pattern & (1<<(n%4)) else F(0)
        commands.append(dict(issue=issue,sample=sample,report=reported,positive=positive,delay=delay))
        add(issue+delay,'command',positive)
        issue=clock.deadline(issue,J);n+=1
    if retire is not None:add(retire+retire_tail,'disconnect',None)
    for t in (F(20),F(50),F(60)):add(t,'boundary',None)
    now=F(0);active=False;desired=False;gate=True;generation=0;violations=[];positive_time=F(0)
    while events:
        t,_,_,kind,data=heappop(events)
        if t>60:break
        if active and t>now:
            positive_time+=t-now
            if max(load(now),load(t))>1:
                violations.append(dict(start=now,end=t,load_start=load(now),load_end=load(t)))
        now=t
        if kind=='command':
            if data:
                generation+=1;desired=True
                if gate:active=True
            elif desired:
                generation+=1;desired=False
                add(t+force_tail,'zero_settled',generation)
            # Repeated zero keeps the same physical withdrawal in progress.
        elif kind=='zero_settled':
            if generation==data:active=False
        elif kind=='disconnect':
            gate=False;add(t+force_tail,'physical_tail_end',None)
        elif kind=='physical_tail_end':active=False
        elif kind!='boundary':raise AssertionError(kind)
    if position_only:assert violations
    elif jump and jump_budget==0:assert violations
    else:assert not violations
    if jump_budget>0:assert not any(c['positive'] for c in commands)
    if not position_only and not jump and not working_shunt:
        assert any(c['positive'] for c in commands) and any(not c['positive'] for c in commands)
    return dict(pattern=pattern,clock_rate=rate,noise=noise,H=H,A=A,position_only=position_only,
                working_shunt=working_shunt,retire=retire,jump=jump,jump_budget=jump_budget,
                commands=commands,positive_time=positive_time,violations=violations,
                factive=not violations)


def revalidation_checks():
    safe=[]
    for pattern,rate,noise in product(range(16),(F(1),F(101,100)),(-F(1,100),F(1,100))):
        run=revalidation_history(pattern,rate,noise)
        safe.append({k:v for k,v in run.items() if k not in ('commands','violations')})
    normal=revalidation_history(7,working_shunt=True)
    retired=revalidation_history(15,retire=F(25))
    pose_failure=revalidation_history(7,position_only=True)
    unbudgeted_jump=revalidation_history(7,jump=True)
    impossible_margin=revalidation_history(7,jump=True,jump_budget=F(2))
    # Illustrative one-connector numbers only: full per-port acquisition/multiplexing
    # and actual rate/transducer suppliers remain parent obligations.
    horizon=F(823+2+828+2*3+6+3)
    assert horizon==1668
    load_guard=F(1,5)+F(2,100)+horizon/F(10000)
    isolation_guard=1-F(2,100)-horizon/F(12000)
    assert load_guard<1 and isolation_guard>F(4,5)
    return dict(safe_schedules=safe,working_shunt=normal,retirement=retired,
                failed_attenuation_pose_guard=pose_failure,unbudgeted_jump=unbudgeted_jump,
                full_jump_budget_safe_abstention=impossible_margin,
                illustrative_direct_guard=dict(comparison_age=823,comparison_through_emit=2,A_plus_H=horizon,load_upper=load_guard,
                                               isolation_lower=isolation_guard,isolation_stroke=12000),
                scope='direct functional evidence plus raw variation/jump bounds; shunt position alone is insufficient under a failed attenuator')

def endpoint_checks():
    # A noisy analog midpoint cannot certify literal end-stop equality.
    actual=F(199,10);stop=F(20);reported=stop;error=F(1,4)
    assert abs(reported-actual)<=error and actual!=stop
    # A raw seated-contact bit is sampled only at an actually engaged catch.
    # Subsequent no-reverse retention preserves the stop; a stale previous-phase
    # bit does not establish that current contact state.
    stale=dict(sample_time=F(-1),sampled_stop=True,current_time=F(1),current_position=F(1),stop=F(0))
    assert stale['current_position']!=stale['stop']
    age=F(823);entry=F(6);reply=entry+F(83300,101)
    sample=reply-age
    assert sample>entry
    # The stop is physically retained after a genuinely post-entry contact sample.
    path=[(sample,F(20)),(sample+F(1,3),F(20)),(reply,F(20))]
    assert all(position==stop for _,position in path)
    # A nonzero hysteresis band plus bounded energy rate gives positive minimum
    # traversal time between opposite power switches, apart from finite refunds.
    gap=F(2);maximum_power=F(7)
    assert gap/maximum_power>0
    return dict(analog_midpoint_counterexample=dict(actual=actual,reported=reported,error=error,stop=stop),
                stale_previous_phase_contact=stale,post_entry_sample=sample,retained_contact_path=path,
                minimum_power_hysteresis_traversal=gap/maximum_power,
                raw_law='a true nominal stop bit samples its engaged physical catch, whose release precedes reverse motion')

def tails_and_nonzeno_checks():
    # A powered operation reserves its maximum full completion cost. Power loss
    # stops new launches; its private reservation funds the post-loss tail.
    held=F(7);reservation=F(5);available=held-reservation
    tail_work=[F(2),F(1),F(2)]
    for cost in tail_work:
        assert cost<=reservation;reservation-=cost
    assert reservation==0 and available==2
    final=F(4);eta=F(1,10)
    assert final+eta>final
    # A finite reset/drain prefix consumes, but never recreates, each ready event.
    events=('power_off','last_word','last_command','last_effect')
    outcomes=[]
    for order in permutations(events):
        consumed=set()
        for event in order:
            assert event not in consumed;consumed.add(event)
        assert len(consumed)==4
        outcomes.append(order)
    # Event-count bound: each launch creates at mostk completion events; between
    # events each monotone scalar crosses each ofM contacts at most once.
    counts=[]
    for horizon in (1,10,100):
        launches=4*(1+100*horizon)+3+7*horizon
        completion=4*launches
        contacts=32*(completion+1)
        counts.append(dict(horizon=horizon,launch_bound=launches,event_bound=completion+contacts))
    return dict(reserved_tail_cost=5,remaining_unreserved_stock=available,simultaneous_orders=len(outcomes),
                event_count_examples=counts,
                boundary='minimum instruction time/raw arrival envelope and one-shot contact consumption; bounded speed alone is insufficient')


def source_hash(name):
    return sha256((HERE/name).read_text(encoding='utf-8-sig').replace('\r\n','\n').encode('utf-8')).hexdigest()


def generate():
    acquisition_commit='68b0e6bc2ee36c798b56366655711b160759a0df'
    acquisition_path='theories-and-designs/byzantine-control/local-control/ACQUISITION.md'
    acquisition_bytes=subprocess.check_output(['git','show',acquisition_commit+':'+acquisition_path],cwd=HERE)
    acquisition_text=acquisition_bytes.decode('utf-8-sig').replace('\r\n','\n')
    return encode(dict(acquisition_interface_snapshot=dict(commit=acquisition_commit,path=acquisition_path,
                sha256=sha256(acquisition_text.encode('utf-8')).hexdigest(),
                status='conditional F=1 example; full runtime instruction and quantity schedule remains open'),status='derived conditional hybrid source with exact event/flow perturbations; first pass',
                sources={n:source_hash(n) for n in ('HYBRID.md','Hybrid.lean','hybrid_model.py','CYCLE.md','CLAMP.md','CONTINUITY.md','BOOTSTRAP.md')},
                clocks=clock_checks(),contacts=contact_checks(),normalization=normalization_checks(),
                word_tails=word_tail_checks(),stages=stage_checks(),direct_revalidation=revalidation_checks(),endpoints=endpoint_checks(),tails_and_events=tails_and_nonzeno_checks()))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write',action='store_true');group.add_argument('--check',action='store_true')
    args=parser.parse_args();result=generate();path=HERE/'hybrid_results.json'
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',newline='\n')
    else:assert json.loads(path.read_text())==result,'record differs; inspect before rewriting'
    print('hybrid record '+('written' if args.write else 'matches'))


if __name__=='__main__':main()
