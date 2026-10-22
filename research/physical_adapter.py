"""Action-indexed, actor-local physical adapter; no file writes.

The operational carrier retains authenticated traffic and four protocol phases.
The abstract carrier uses validated report/interval meanings and physical registers.
Tests are finite; PHYSICAL-ASSEMBLY.md states the universal normalization and
honest-coverage argument and the continuous-time decoder.
"""
from __future__ import annotations
from dataclasses import dataclass, replace
from fractions import Fraction as F
from itertools import product, combinations
from typing import NamedTuple
import json
import evidence_model as ev
import timed_recovery_model as tr
import institution_model as inst

GATE=3
ACTORS=(0,1,2,GATE)


@dataclass(frozen=True)
class Public:
    mode: str
    context: tr.BatchContext
    pending: tuple
    remaining: tuple
    clean: bool
    drain_left: int


@dataclass(frozen=True)
class View:
    tick: int
    phase: int
    public: Public
    reading: F | None
    reports: tuple  # received (wire artifact, verification result)
    intervals: tuple


@dataclass(frozen=True)
class AbstractView:
    tick: int
    phase: int
    public: Public
    reading: F | None
    reports: tuple[ev.Report,...]
    intervals: tuple[tuple[int,ev.Interval],...]


@dataclass(frozen=True)
class Frame:
    state: tr.State
    phase: int
    tick: int
    readings: tuple[F,...]
    emitted: frozenset[inst.Signature] = frozenset()
    reports: tuple[tuple[inst.Signature,...],...] = ((),(),())
    intervals: tuple[inst.Signature,...] = ()
    selected: F | None = None
    actual_x: F = F(0)
    actual_service: F = F(0)
    disturbance_integral: F = F(0)
    histories: tuple[tuple[View,...],...] = ((),(),(),())


def initial_condition(state,p):
    """The actual Model.initial domain, not all raw Python State values."""
    try:p.validate()
    except (AssertionError,TypeError,ValueError):return False
    plant=state.plant
    common=(state.faults in tr.FAULT_FAMILY and plant.time==0 and plant.slot==0
            and len(plant.pending)==p.delay_slots and p.safe.contains(plant.inventory)
            and all(F(0)<=u<=p.capacity for u in plant.pending))
    if not common:return False
    if state.mode=="live":
        return (state.institution.status=="active" and state.institution.cap==p.capacity
                and ev.tube_is_safe(ev.pending_tube(plant,p),p))
    if state.mode=="ready":
        return (state.clean_ack and state.reservation is None and state.institution.status=="ready"
                and plant.pending==(p.demand,)*p.delay_slots and state.institution.cap==p.capacity)
    return False


def start(state,p,noises=(F(0),)*3):
    """Wrap a valid initial state or already-derived macro-boundary continuation."""
    assert state.faults in tr.FAULT_FAMILY
    assert len(noises)==3
    assert all(abs(v)<=p.other_error for v in noises)
    assert len(state.plant.pending)==p.delay_slots
    if state.mode=="ready":
        if not state.clean_ack or state.reservation is not None or state.plant.pending!=(p.demand,)*p.delay_slots:
            raise ValueError("ready context lacks clean constant-demand FIFO")
    if state.mode=="reserved" and (state.reservation is None or not state.reservation.remaining):
        raise ValueError("reserved context lacks an active reservation")
    readings=tuple(ev.quantize_rational(state.plant.inventory+v,p.quantization_step) for v in noises)
    return Frame(state,0,4*state.plant.slot,readings,actual_x=state.plant.inventory,
                 actual_service=state.plant.delivered)


def verified(frame,artifact):
    try:return isinstance(artifact,inst.Signature) and artifact in frame.emitted
    except TypeError:return False


def current_view(frame,i,p):
    s=frame.state
    public=Public(s.mode,tr.public_context(s,p),s.plant.pending,
                  s.reservation.remaining if i==GATE and s.reservation else (),s.clean_ack,s.drain_left)
    return View(frame.tick,frame.phase,public,frame.readings[i] if i!=GATE else None,
        tuple((sig,verified(frame,sig)) for sig in frame.reports[i]) if i!=GATE else (),
        tuple((sig,verified(frame,sig)) for sig in frame.intervals) if i==GATE else ())


def observe(frame,i,p):
    return frame.histories[i]+(current_view(frame,i,p),)


def history_map(i,history,p):
    """Componentwise map, using only the actor's current local record."""
    h=history[-1];c=h.public.context
    reports=[]
    for sig,authentic in h.reports:
        if (not authentic or sig.signer not in ev.ACTORS or sig.era!=c.era
            or sig.kind!="timed-report" or not isinstance(sig.payload,tuple) or len(sig.payload)!=3):continue
        r,s,y=sig.payload
        report=ev.Report(sig.signer,sig.era,r,s,y)
        empty=ev.LocalView(i,c.era,c.start_slot,c.start_at,c.round_at,(),c.pending_snapshot)
        if ev.current_report(report,empty,p): reports.append(report)
    kind="live-interval" if h.public.mode=="live" else "recenter"
    intervals=[];seen=set()
    for sig,authentic in h.intervals:
        if (not authentic or sig.signer not in ev.ACTORS or sig.era!=c.era or sig.kind!=kind
            or not isinstance(sig.payload,tuple) or len(sig.payload)!=3 or sig.payload[0]!=c):continue
        _,lo,hi=sig.payload
        if not isinstance(lo,F) or not isinstance(hi,F) or lo>hi or sig.signer in seen:continue
        clipped=ev.Interval(lo,hi).intersect(ev.Interval(F(0),min(c.restored_capacity,c.institution.cap)))
        if clipped is not None: intervals.append((sig.signer,clipped));seen.add(sig.signer)
    return AbstractView(h.tick,h.phase,h.public,h.reading,tuple(reports),tuple(intervals))


def allowed_interval(i,h,p):
    c=h.public.context
    view=ev.LocalView(i,c.era,c.start_slot,c.start_at,c.round_at,h.reports,c.pending_snapshot)
    if h.public.mode=="live":
        result=ev.local_policy(view,p)
        return None if result is None else result.allowed
    if (h.public.mode!="ready" or p.delay_slots==0 or not h.public.clean
        or min(c.restored_capacity,c.institution.cap)<p.demand+p.hostile):return None
    rp=replace(p,hostile=F(0),error=p.error+p.hostile*p.max_age)
    branches=ev.infer_branches(view,rp)
    if not branches:return None
    L=min(b.states.low for b in branches);U=max(b.states.high for b in branches)
    return ev.Interval(F(0),min(c.restored_capacity,c.institution.cap)).intersect(ev.Interval(
        p.demand+(p.release_region.low-L)/p.delay,p.demand+(p.release_region.high-U)/p.delay))


def abstract_policy(i,h,p):
    mode=h.public.mode
    active=mode in ("live","ready")
    if i!=GATE:
        if h.phase==0 and active:return ("reading",h.reading)
        if h.phase==1 and active:
            interval=allowed_interval(i,h,p)
            return ("permission",interval) if interval is not None else ("idle",)
        return ("idle",)
    if h.phase!=2:return ("idle",)
    candidates=[]
    for (i,a),(j,b) in combinations(h.intervals,2):
        lo=max(a.low,b.low);hi=min(a.high,b.high)
        if lo<=hi:candidates.append((lo,tuple(sorted((i,j)))))
    if active and candidates:
        u,support=min(candidates)
        return ("reserve" if mode=="ready" else "select",u,support)
    if mode=="live":return ("uncertified",p.demand)  # explicit failure branch, not deadlock
    return ("append",h.public.remaining[0] if mode=="reserved" else p.demand)


def lift(i,history,action,p):
    if action[0]=="reading":return ("send",action[1])
    if action[0]=="permission":return ("sign",action[1].low,action[1].high)
    return action


def policy(i,history,p):return lift(i,history,abstract_policy(i,history_map(i,history,p),p),p)


def follows(frame,requests,p):
    return (isinstance(requests,tuple) and len(requests)==4 and all(
        requests[i]==policy(i,observe(frame,i,p),p) for i in ACTORS if i not in frame.state.faults))


def _replay(request):
    return request[1] if isinstance(request,tuple) and len(request)==2 and request[0]=="replay" and isinstance(request[1],inst.Signature) else None


def advance(frame,requests,p,*,disturbance=F(0),noises=(F(0),)*3):
    """Action-indexed next; malformed Byzantine requests become admitted omission.

    Environment inputs are separately required to obey their physical bounds.
    No safety test filters the generated state. A nonfollowing correct command is
    outside Follows and returns None; every following profile has a successor.
    """
    if not follows(frame,requests,p):return None
    assert isinstance(disturbance,F) and abs(disturbance)<=tr.mode_radius(frame.state,p)
    assert len(noises)==3
    assert all(isinstance(v,F) and abs(v)<=p.other_error for v in noises)
    s=frame.state;c=tr.public_context(s,p);phase=frame.phase
    emitted=set(frame.emitted);reports=[list(row) for row in frame.reports];intervals=list(frame.intervals)
    selected=frame.selected
    def emit(signer,kind,payload):
        sig=inst.Signature(signer,c.era,kind,payload);emitted.add(sig);return sig
    active=s.mode in ("live","ready")
    if phase==0 and active:
        reports=[[] for _ in ev.ACTORS]
        for source in ev.ACTORS:
            req=requests[source]
            if isinstance(req,tuple) and len(req)==2 and req[0]=="send" and isinstance(req[1],F):
                values=(req[1],)*3
            elif (isinstance(req,tuple) and len(req)==2 and req[0]=="equivocate"
                  and isinstance(req[1],tuple) and len(req[1])==3): values=req[1]
            else: values=(_replay(req),)*3
            for recipient,value in enumerate(values):
                if isinstance(value,F):reports[recipient].append(emit(source,"timed-report",(c.round_at,c.round_at,value)))
                elif isinstance(value,inst.Signature):reports[recipient].append(value)
                # Every other decoded request is a legal omission, not a blocked round.
    elif phase==1 and active:
        intervals=[]
        kind="live-interval" if s.mode=="live" else "recenter"
        for source in ev.ACTORS:
            req=requests[source]
            if (isinstance(req,tuple) and len(req)==3 and req[0]=="sign"
                and isinstance(req[1],F) and isinstance(req[2],F)):
                intervals.append(emit(source,kind,(c,req[1],req[2])))
            else:
                replay=_replay(req)
                if replay is not None:intervals.append(replay)
    elif phase==2:
        gate=requests[GATE]
        if gate[0]=="reserve":
            oracle=inst.Authentication(s.faults);oracle.events=emitted
            # The raw request alphabet includes malformed forged objects. The
            # typed reservation component receives only verified wire artifacts.
            safe_packets=tuple(sig for sig in intervals if verified(frame,sig))
            after=tr.reserve_batch(s,oracle,p,safe_packets)
            assert after.reservation is not None
            assert after.reservation.certificate.control==gate[1]
            s=after;selected=gate[1]
        elif gate[0]=="select":
            decoded=history_map(GATE,observe(frame,GATE,p),p)
            messages=tuple(ev.Endorsement(i,c.era,c.start_slot,c.round_at,c.start_at,c.pending_snapshot,a)
                           for i,a in decoded.intervals)
            u,support=ev.gate_select(messages,c.era,c.start_slot,c.pending_snapshot,p,
                                    round_at=c.round_at,effect_at=c.start_at)
            assert (u,support)==gate[1:];selected=u
        else:selected=gate[1]
    dt=(p.period if phase==3 else F(0)) if p.delay_slots==0 else p.period/4
    applied=s.plant.pending[0] if p.delay_slots else (selected if phase==3 else p.demand)
    actual_x=frame.actual_x+dt*(applied-p.demand+disturbance)
    actual_service=frame.actual_service+dt*p.demand
    integral=frame.disturbance_integral+dt*disturbance
    histories=tuple(frame.histories[i]+(current_view(frame,i,p),) for i in ACTORS)
    if phase<3:
        return Frame(s,phase+1,frame.tick+1,frame.readings,frozenset(emitted),tuple(map(tuple,reports)),
                     tuple(intervals),selected,actual_x,actual_service,integral,histories)
    average=integral/p.period
    after=tr.step(s,p,disturbance=average,live_command=selected if s.mode=="live" else None)
    assert after.plant.inventory==actual_x and after.plant.delivered==actual_service
    readings=tuple(ev.quantize_rational(actual_x+n,p.quantization_step) for n in noises)
    return Frame(after,0,frame.tick+1,readings,frozenset(emitted),actual_x=actual_x,
                 actual_service=actual_service,histories=histories)


class AbstractPoint(NamedTuple):
    tick: int
    phase: int
    round_at: F
    sampled_inventory: F
    pending: tuple
    actual_inventory: F
    service: F
    selected: F | None
    mode: str
    views: tuple[AbstractView,...]
    issued: frozenset


def projection(frame,p):
    """Nonidentity carrier map: erase wire signatures/traffic, retain their meanings."""
    plant=frame.state.plant
    return AbstractPoint(frame.tick,frame.phase,plant.time,plant.inventory,plant.pending,frame.actual_x,
            frame.actual_service,frame.selected,frame.state.mode,
            tuple(history_map(i,observe(frame,i,p),p) for i in ACTORS),
            frozenset((s.signer,s.era,s.kind,s.payload) for s in frame.emitted))


def abstract_next_matches(before,after,image,gate_action,disturbance,p,faults):
    """Independent target relation on semantic phase/flow registers.

    Communication events carry attributed, provenance-checked values. The issued
    event ledger remains available for their generation; actors see only own inboxes.
    """
    if after.tick!=before.tick+1 or after.phase!=(before.phase+1)%4:return False
    if not before.issued<=after.issued:return False
    c=before.views[GATE].public.context
    for signer,era,kind,payload in after.issued-before.issued:
        if signer in faults:continue
        if before.phase==0 and before.mode in ("live","ready"):
            if (era,kind,payload)!=(c.era,"timed-report",(c.round_at,c.round_at,before.views[signer].reading)):return False
        elif before.phase==1 and before.mode in ("live","ready"):
            interval=allowed_interval(signer,before.views[signer],p)
            if interval is None:return False
            expected_kind="live-interval" if before.mode=="live" else "recenter"
            if (era,kind,payload)!=(c.era,expected_kind,(c,interval.low,interval.high)):return False
        else:return False
    for i in ACTORS:
        v=after.views[i]
        if v.tick!=after.tick or v.phase!=after.phase or v.public.mode!=after.mode:return False
        if v.public.context.era!=c.era or v.public.context.institution!=c.institution:return False
        if v.public.pending!=after.pending:return False
    dt=(p.period if before.phase==3 else F(0)) if p.delay_slots==0 else p.period/4
    applied=before.pending[0] if p.delay_slots else (before.selected if before.phase==3 else p.demand)
    if after.actual_inventory!=before.actual_inventory+dt*(applied-p.demand+disturbance):return False
    if after.service!=before.service+dt*p.demand:return False
    if before.phase==0 and image is not None:
        if tuple(after.views[i].reports for i in ev.ACTORS)!=image:return False
        # Operational reliable-delivery/unforgeability clauses, not the safety result.
        for receiver in ev.ACTORS:
            for source in ev.ACTORS:
                if source not in faults:
                    expected=ev.Report(source,before.views[source].public.context.era,
                        before.round_at,before.round_at,before.views[source].reading)
                    if expected not in image[receiver]:return False
            if any(r.signer not in faults and r.value!=before.views[r.signer].reading for r in image[receiver]):return False
            if any((r.signer,r.epoch,"timed-report",(r.round_at,r.sampled_at,r.value)) not in after.issued for r in image[receiver]):return False
    if before.phase==1 and image is not None:
        if after.views[GATE].intervals!=image:return False
        actual=dict(image)
        for i in ev.ACTORS:
            if i not in faults:
                interval=allowed_interval(i,before.views[i],p)
                if interval is not None and actual.get(i)!=interval:return False
        if any(i not in faults and a!=allowed_interval(i,before.views[i],p) for i,a in image):return False
    if before.phase==2:
        if after.selected!=gate_action[1]:return False
        if gate_action[0]=="reserve":
            if after.mode!="reserved" or after.views[GATE].public.remaining!=(gate_action[1],)*p.delay_slots+(p.demand,)*p.delay_slots:return False
        elif after.mode!=before.mode:return False
    if before.phase<3:
        return (after.round_at==before.round_at and after.sampled_inventory==before.sampled_inventory
                and after.pending==before.pending and all(v.public.context==c for v in after.views))
    public=before.views[GATE].public
    new=before.selected if before.mode=="live" else public.remaining[0] if before.mode=="reserved" else p.demand
    expected_pending=before.pending[1:]+(new,) if p.delay_slots else ()
    expected_mode=("isolated" if before.mode=="drain" and public.drain_left==1 else
                   "release_ready" if before.mode=="reserved" and len(public.remaining)==1 else before.mode)
    if any(abs(after.views[i].reading-after.actual_inventory)>p.error for i in ev.ACTORS if i not in faults):return False
    appended=ev.Segment(c.start_at,c.start_at+p.period,new)
    expected_schedule=ev.canonical_schedule(c.pending_snapshot+(appended,),
        *ev.snapshot_window(before.round_at+p.period,c.start_at+p.period,p))
    for v in after.views:
        nc=v.public.context
        if (nc.round_slot!=c.round_slot+1 or nc.start_slot!=c.start_slot+1
            or nc.round_at!=c.round_at+p.period or nc.start_at!=c.start_at+p.period
            or nc.pending_snapshot!=expected_schedule):return False
    return (after.round_at==before.round_at+p.period and after.sampled_inventory==after.actual_inventory
            and after.pending==expected_pending and after.mode==expected_mode)


def communication_image(frame,requests,p):
    """Analytic action projection computed before the successor or disturbance.

    This separate normalization transcribes wire requests into the abstract next
    relation's report/permission events. It does not read future plant state.
    """
    if frame.state.mode not in ("live","ready") or frame.phase not in (0,1):return None
    c=tr.public_context(frame.state,p);issued=[];inboxes=[[] for _ in ev.ACTORS]
    if frame.phase==0:
        for source,req in enumerate(requests[:3]):
            if isinstance(req,tuple) and len(req)==2 and req[0]=="send" and isinstance(req[1],F):
                row=(req[1],)*3
            elif isinstance(req,tuple) and len(req)==2 and req[0]=="equivocate" and isinstance(req[1],tuple) and len(req[1])==3:
                row=req[1]
            else:row=(_replay(req),)*3
            for recipient,item in enumerate(row):
                if isinstance(item,F):
                    sig=inst.Signature(source,c.era,"timed-report",(c.round_at,c.round_at,item))
                    issued.append(sig);inboxes[recipient].append(sig)
                elif isinstance(item,inst.Signature):inboxes[recipient].append(item)
        events=frame.emitted.union(issued)
        answer=[]
        for recipient,row in enumerate(inboxes):
            valid=[]
            view=ev.LocalView(recipient,c.era,c.start_slot,c.start_at,c.round_at,(),c.pending_snapshot)
            for sig in row:
                try:authentic=sig in events
                except TypeError:authentic=False
                if (not authentic or sig.signer not in ev.ACTORS or sig.era!=c.era or sig.kind!="timed-report"
                    or not isinstance(sig.payload,tuple) or len(sig.payload)!=3):continue
                r,s,y=sig.payload;report=ev.Report(sig.signer,sig.era,r,s,y)
                if ev.current_report(report,view,p):valid.append(report)
            answer.append(tuple(valid))
        return tuple(answer)
    kind="live-interval" if frame.state.mode=="live" else "recenter"
    row=[]
    for source,req in enumerate(requests[:3]):
        if (isinstance(req,tuple) and len(req)==3 and req[0]=="sign"
            and isinstance(req[1],F) and isinstance(req[2],F)):
            sig=inst.Signature(source,c.era,kind,(c,req[1],req[2]));issued.append(sig);row.append(sig)
        elif _replay(req) is not None:row.append(_replay(req))
    events=frame.emitted.union(issued);answer=[];seen=set()
    for sig in row:
        try:authentic=sig in events
        except TypeError:authentic=False
        if (not authentic or sig.signer not in ev.ACTORS or sig.era!=c.era or sig.kind!=kind
            or not isinstance(sig.payload,tuple) or len(sig.payload)!=3 or sig.payload[0]!=c):continue
        _,lo,hi=sig.payload
        if not isinstance(lo,F) or not isinstance(hi,F) or lo>hi or sig.signer in seen:continue
        interval=ev.Interval(lo,hi).intersect(ev.Interval(F(0),min(c.restored_capacity,c.institution.cap)))
        if interval is not None:answer.append((sig.signer,interval));seen.add(sig.signer)
    return tuple(answer)


REQUESTS=(None,(),("junk",),("send","bad"),("send",F(-100)),("send",F(100)),
          ("send",F(2)),("equivocate",(F(-8),None,F(8))),
          ("sign",F(-100),F(100)),("sign",F(0),F(0)),("sign",F(2),F(2)),
          ("sign",F(2),F(0)),("sign","bad",F(2)))


def profiles(frame,p,extras=()):
    honest=tuple(policy(i,observe(frame,i,p),p) for i in ACTORS)
    if not frame.state.faults:yield honest;return
    bad=next(iter(frame.state.faults))
    for request in REQUESTS+tuple(extras):yield tuple(request if i==bad else honest[i] for i in ACTORS)


@dataclass(frozen=True)
class Roles:
    sensors: tuple[int,int,int]
    authorizers: tuple[int,int,int]


def projected_family(family,role):
    return tuple(sorted({frozenset(j for j,i in enumerate(role) if i in B) for B in family},key=lambda x:tuple(sorted(x))))


def roles_admitted(roles,family):
    return (len(set(roles.sensors))==len(set(roles.authorizers))==3 and all(
        len(B.intersection(roles.sensors))<=1 and len(B.intersection(roles.authorizers))<=1 for B in family))


def role_round(plant,roles,global_B,family,p):
    """Role lifting uses one B; no independent replacement fault index is selected."""
    assert roles_admitted(roles,family) and global_B in family
    sensor_family=projected_family(family,roles.sensors)
    reading=ev.quantize_rational(plant.inventory,p.quantization_step)
    local_messages=[]
    for j,authorizer in enumerate(roles.authorizers):
        reports=tuple(ev.Report(k,plant.epoch,plant.time,plant.time,
            F(-8 if j%2 else 8) if sensor in global_B else reading) for k,sensor in enumerate(roles.sensors))
        view=ev.LocalView(j,plant.epoch,plant.slot+p.delay_slots,plant.time+p.delay,plant.time,reports,ev.schedule_of(plant,p))
        if authorizer not in global_B:
            message=ev.local_policy(view,p,sensor_family);assert message is not None;local_messages.append(message)
        else:local_messages.append(ev.Endorsement(j,plant.epoch,view.target_slot,view.round_at,view.effect_at,view.schedule,ev.Interval(F(-100),F(100))))
    u,support=ev.gate_select(tuple(local_messages),plant.epoch,plant.slot+p.delay_slots,
        ev.schedule_of(plant,p),p,round_at=plant.time,effect_at=plant.time+p.delay)
    assert any(roles.authorizers[j] not in global_B for j in support)
    for w in (-p.hostile,F(0),p.hostile):
        after=ev.plant_step(plant,u,w,p)
        assert ev.tube_is_safe(ev.pending_tube(after,p),p)
    return u,tuple(roles.authorizers[j] for j in support)


def run_checks():
    following=edges=macro_maps=local_actions=0
    locality={}
    for m,mode,x,faults in product((0,1,2),("live","ready"),(F(1),F(2),F(3)),tr.FAULT_FAMILY):
        p=tr.Parameters(delay_slots=m)
        plant=ev.TimedState(F(0),x,(p.demand,)*m)
        if mode=="live" and not ev.tube_is_safe(ev.pending_tube(plant,p),p):continue
        state=tr.State(plant,faults,tr.Institution("active" if mode=="live" else "ready",0,p.capacity),
                       mode=mode,clean_ack=mode=="ready",samples=((F(0),x),))
        assert initial_condition(state,p)
        frame=start(state,p,noises=(-p.other_error,F(0),p.other_error))
        for tick in range(8):
            c=tr.public_context(frame.state,p)
            forged=inst.Signature(1,c.era,"live-interval",(c,F(0),F(0)))
            stale=inst.Signature(0,c.era-1,"timed-report",(c.round_at,c.round_at,F(2)))
            unhashable=inst.Signature(0,c.era,"recenter",([],))
            extras=(("replay",forged),("replay",stale),("replay",unhashable))
            authentic_old=tuple(sig for sig in frame.emitted if sig.kind=="timed-report" and sig.payload[0]!=c.round_at)
            if authentic_old:extras+=(("replay",authentic_old[0]),)
            for requests in profiles(frame,p,extras):
                assert follows(frame,requests,p);following+=1
                for w in ((F(0),) if mode=="ready" else (-p.hostile,F(0),p.hostile)):
                    if frame.state.mode!="live":w=F(0)
                    nxt=advance(frame,requests,p,disturbance=w)
                    assert nxt is not None and nxt.tick==frame.tick+1
                    assert nxt.state.faults==faults
                    assert p.safe.contains(nxt.actual_x)
                    assert projection(nxt,p)[0]==nxt.tick
                    image=communication_image(frame,requests,p)
                    gate_action=abstract_policy(GATE,history_map(GATE,observe(frame,GATE,p),p),p)
                    assert abstract_next_matches(projection(frame,p),projection(nxt,p),image,gate_action,w,p,faults)
                    if image is not None and frame.phase==0:
                        assert tuple(history_map(i,observe(nxt,i,p),p).reports for i in ev.ACTORS)==image
                    if image is not None and frame.phase==1:
                        assert history_map(GATE,observe(nxt,GATE,p),p).intervals==image
                    edges+=1
                    for i in ACTORS:
                        if i in faults:continue
                        h=observe(frame,i,p);a=history_map(i,h,p)
                        assert policy(i,h,p)==lift(i,h,abstract_policy(i,a,p),p)
                        key=(i,a,p)
                        assert locality.setdefault(key,requests[i])==requests[i]
                        local_actions+=1
                    if frame.phase==3:
                        old=frame.state.plant
                        expected=old.inventory+p.period*((old.pending[0] if m else frame.selected)-p.demand)+(frame.disturbance_integral+(p.period/4 if m else p.period)*w)
                        assert nxt.state.plant.inventory==expected
                        assert nxt.state.plant.delivered-old.delivered==p.period*p.demand
                        macro_maps+=1
            # Follow a varied nontrivial request, preserving its generated inbox next.
            choices=tuple(profiles(frame,p))
            frame=advance(frame,choices[(tick+5)%len(choices)],p,
                          disturbance=(p.hostile if frame.state.mode=="live" else F(0)))
    # Complete recovery through the same action-indexed micro-step interface.
    p=tr.Parameters()
    ready=tr.State(ev.TimedState(F(0),F(2),(F(1),)),frozenset((0,)),tr.Institution("ready",2,F(2)),
                   mode="ready",clean_ack=True,samples=((F(0),F(2)),))
    assert initial_condition(ready,p)
    for invalid in (replace(ready,clean_ack=False),replace(ready,plant=replace(ready.plant,pending=(F(2),)))):
        assert not initial_condition(invalid,p)
        try:start(invalid,p);raise AssertionError("invalid ready initialization accepted")
        except ValueError:pass
    malformed_frame=start(ready,p)
    malformed=inst.Signature(0,0,"recenter",([],))
    for stage in range(4):
        req=list(next(profiles(malformed_frame,p)))
        req[0]=("replay",malformed)
        malformed_frame=advance(malformed_frame,tuple(req),p)
        assert malformed_frame is not None
    assert malformed_frame.state.mode=="reserved"
    recovery_rounds=0
    p=tr.Parameters(delay_slots=2)
    s=tr.initial(F(2),(F(2),F(0)),frozenset((0,)),p);auth=inst.Authentication(s.faults)
    s=tr.perform(s,auth,"isolate",p,effective=True)
    def round_step(s):
        f=start(s,p)
        for _ in range(4):f=advance(f,next(profiles(f,p)),p)
        return f.state
    while s.mode=="drain":s=round_step(s);recovery_rounds+=1
    # Corrected stronger drain invariant: recenter is not necessary for this entry.
    assert p.release_region.contains(s.plant.inventory)
    s=tr.perform(s,auth,"begin_repair",p)
    s=round_step(s);recovery_rounds+=1
    s=tr.perform(s,auth,"finish_repair",p,clean=True)
    s=tr.perform(s,auth,"grant_recenter",p,consent=True)
    while s.mode in ("ready","reserved"):
        s=round_step(s);recovery_rounds+=1
    assert s.mode=="release_ready" and p.release_region.contains(s.plant.inventory)
    s=tr.perform(s,auth,"release",p);assert s.mode=="live"
    # Joint global-family role mapping, not an independent-budget assumption.
    family=inst.finite_fault_family();role_cases=0
    for config,B in product(inst.CONFIGS,family):
        roles=Roles(config.sensors,config.authorizers)
        assert roles_admitted(roles,family)
        role_round(ev.TimedState(F(0),F(2),(F(1),)),roles,B,family,tr.Parameters())
        role_cases+=1
    assert not roles_admitted(Roles((0,6,7),(3,4,5)),family)
    colocated=Roles((0,1,2),(0,1,2))
    assert roles_admitted(colocated,tr.FAULT_FAMILY)
    for B in tr.FAULT_FAMILY:role_round(ev.TimedState(F(0),F(2),(F(1),)),colocated,B,tr.FAULT_FAMILY,tr.Parameters())
    return {"following_request_profiles":following,"micro_edges":edges,"macro_fifo_maps":macro_maps,
            "local_action_occurrences":local_actions,"local_policy_classes":len(locality),
            "recovery_macro_rounds":recovery_rounds,"global_role_lifting_cases":role_cases,
            "request_scope":"finite malformed/replay/numeric corpus; all decoded requests by analytic normalization proof",
            "same_global_fault_family":True,"actual_signature_pipeline":True,
            "four_phase_continuous_decoder":True,"certified_drain_already_in_J":True}


if __name__=="__main__":print(json.dumps(run_checks(),indent=2,sort_keys=True))
