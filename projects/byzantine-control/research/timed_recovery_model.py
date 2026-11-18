"""Queue-aware recovery of the timed scalar controller; standard library only.

Positive-delay cycles preserve the Evidence interface. Delay zero is a separate
instantaneous round-boundary idealization. No function writes files. Actor policies
receive public views and authenticated messages, never inventory or actual faults.
"""
from __future__ import annotations
from dataclasses import dataclass, replace, asdict
from fractions import Fraction as F
from itertools import product, combinations
import json
import evidence_model as ev
from institution_model import Authentication, Signature, OFFICER

ACTORS = ev.ACTORS
FAULT_FAMILY = ev.FAULT_FAMILY


@dataclass(frozen=True)
class Parameters(ev.Parameters):
    def validate_ideal(self):
        assert self.period > 0 and self.delay_slots >= 0
        assert self.hostile >= 0 and self.error >= 0 and self.max_age >= 0
        assert self.demand >= self.hostile and self.capacity >= self.demand + self.hostile
        assert self.safe.high - self.safe.low >= 4*self.radius + 2*self.hostile*self.period

    @property
    def release_region(self):
        return ev.Interval(self.safe.low+self.hostile*self.delay,
                           self.safe.high-self.hostile*self.delay)


@dataclass(frozen=True)
class Institution:
    status: str = "active"
    generation: int = 0
    cap: F = F(2)


@dataclass(frozen=True)
class BatchContext:
    era: int
    institution: Institution
    round_slot: int
    round_at: F
    start_slot: int
    start_at: F
    block_slots: int
    release_at: F
    pending_snapshot: tuple[ev.Segment, ...]
    isolation: bool
    restored_capacity: F


@dataclass(frozen=True)
class LocalView:
    observer: int
    context: BatchContext
    reports: tuple[Signature, ...]


@dataclass(frozen=True)
class BatchCertificate:
    context: BatchContext
    control: F
    signatures: tuple[Signature, ...]


@dataclass(frozen=True)
class Reservation:
    certificate: BatchCertificate
    remaining: tuple[F, ...]
    ticks: int = 0


@dataclass(frozen=True)
class State:
    plant: ev.TimedState
    faults: frozenset[int]
    institution: Institution
    mode: str = "live"
    drain_left: int = 0
    reservation: Reservation | None = None
    release_witness: str | None = None
    clean_ack: bool = False
    samples: tuple[tuple[F,F], ...] = ()
    last_isolation_slot: int = -1


def initial(inventory, pending, faults, p):
    p.validate()
    assert faults in FAULT_FAMILY and len(pending) == p.delay_slots
    assert all(F(0) <= u <= p.capacity for u in pending)
    plant = ev.TimedState(F(0), inventory, pending)
    assert ev.tube_is_safe(ev.pending_tube(plant,p),p)
    return State(plant,faults,Institution(cap=p.capacity),samples=((F(0),inventory),))


def mode_capacity(state,p):
    return p.demand if state.mode == "repair" else p.capacity


def mode_radius(state,p):
    return p.hostile if state.mode == "live" else F(0)


def public_context(state,p):
    """Protected metadata: neither the physical inventory nor actual coalition."""
    plant=state.plant
    return BatchContext(plant.epoch,state.institution,plant.slot,plant.time,
                        plant.slot+p.delay_slots,plant.time+p.delay,p.delay_slots,
                        plant.time+2*p.delay,ev.schedule_of(plant,p),state.mode != "live",
                        mode_capacity(state,p))


def order_signature(state,auth,order,actor=OFFICER):
    return auth.emit(actor,state.plant.epoch,"timed-order",
                     (state.institution,state.plant.slot,order))


def admin(state,auth,signature,order,p,*,effective=False,clean=False,consent=False):
    """Enforced organizational/physical interface; failed guards leave state intact.

    effective and clean are protected-root acknowledgments, not arbitrary payload
    statements authenticated by the office signature. Membership stays fixed.
    """
    if (not auth.verify(signature) or signature.signer != OFFICER
        or signature.era != state.plant.epoch or signature.kind != "timed-order"
        or signature.payload != (state.institution,state.plant.slot,order)):
        return state
    n=state.institution
    if (order == "isolate" and state.mode == "live" and effective
        and state.plant.slot > state.last_isolation_slot):
        # Already admitted FIFO leases survive status/generation change.
        mode="drain" if p.delay_slots else "isolated"
        return replace(state,mode=mode,drain_left=p.delay_slots,last_isolation_slot=state.plant.slot,
                       institution=replace(n,status="suspended",generation=n.generation+1))
    if order == "begin_repair" and state.mode == "isolated" and state.plant.pending == (p.demand,)*p.delay_slots:
        return replace(state,mode="repair",institution=replace(n,status="repairing",cap=p.demand))
    if order == "finish_repair" and state.mode == "repair" and clean:
        return replace(state,mode="ready",clean_ack=True,institution=replace(n,status="ready"))
    if (order == "grant_recenter" and state.mode == "ready" and consent
        and (n.cap < p.capacity or p.hostile == 0 or p.delay_slots == 0)):
        result=replace(state,institution=replace(n,cap=p.capacity,generation=n.generation+1))
        if p.hostile == 0 or p.delay_slots == 0:
            result=replace(result,mode="release_ready",release_witness="no-shrunken-region")
        return result
    if (order == "release" and state.mode == "release_ready" and state.clean_ack
        and state.release_witness is not None and state.plant.pending == (p.demand,)*p.delay_slots
        and n.cap >= p.demand+p.hostile):
        # Reissue the d warmup commitments under fresh scope; no state reset.
        return replace(state,mode="live",clean_ack=False,reservation=None,
                       release_witness=None,plant=replace(state.plant,epoch=state.plant.epoch+1),
                       institution=replace(n,status="active",generation=n.generation+1))
    return state


def report_round(state,auth,p,*,sample_at=None,noises=None,attacks=None):
    """Actual source events. Correct sources have one quantized reading per round."""
    sample_at=state.plant.time if sample_at is None else sample_at
    history=dict(state.samples)
    assert sample_at in history
    assert max(F(0),state.plant.time-p.max_age) <= sample_at <= state.plant.time
    noises={} if noises is None else noises
    attacks={} if attacks is None else attacks
    correct={}
    for s in ACTORS:
        if s not in state.faults:
            noise=noises.get(s,F(0));assert abs(noise) <= p.other_error
            value=ev.quantize_rational(history[sample_at]+noise,p.quantization_step)
            assert abs(value-history[sample_at]) <= p.error
            correct[s]=auth.emit(s,state.plant.epoch,"timed-report",
                (state.plant.time,sample_at,value))
    result={}
    for i in ACTORS:
        row=[]
        for s in ACTORS:
            if s not in state.faults: row.append(correct[s])
            elif attacks.get((s,i)) is not None:
                row.append(auth.adversary_emit(s,state.plant.epoch,"timed-report",
                    (state.plant.time,sample_at,attacks[s,i])))
        result[i]=tuple(row)
    return result


def recenter_policy(view,auth,p):
    """Purely local selector of a permission interval for one constant input block."""
    c=view.context
    if (p.delay_slots <= 0 or not c.isolation or c.institution.status != "ready" or c.block_slots != p.delay_slots
        or c.start_slot != c.round_slot+p.delay_slots or c.start_at != c.round_at+p.delay
        or c.release_at != c.start_at+p.delay
        or min(c.institution.cap,c.restored_capacity) < p.demand+p.hostile):
        return None
    reports=[]
    for sig in view.reports:
        if (not auth.verify(sig) or sig.kind != "timed-report" or sig.era != c.era
            or sig.signer not in ACTORS or len(sig.payload) != 3): continue
        round_at,sampled_at,value=sig.payload
        reports.append(ev.Report(sig.signer,c.era,round_at,sampled_at,value))
    base=ev.LocalView(view.observer,c.era,c.start_slot,c.start_at,c.round_at,tuple(reports),c.pending_snapshot)
    # The extra r*a covers pre-isolation history; future propagation is isolated.
    # This computational reuse does NOT assert that past disturbances were zero.
    rp=replace(p,error=p.error+p.hostile*p.max_age,hostile=F(0))
    try:
        canonical=ev.canonical_schedule(c.pending_snapshot,*ev.snapshot_window(c.round_at,c.start_at,rp))
        if canonical != c.pending_snapshot: return None
        branches=ev.infer_branches(base,rp)
    except (AssertionError,TypeError,ValueError): return None
    if not branches: return None
    L=min(b.states.low for b in branches);U=max(b.states.high for b in branches)
    J=p.release_region
    allowed=ev.Interval(F(0),min(c.institution.cap,c.restored_capacity)).intersect(
        ev.Interval(p.demand+(J.low-L)/p.delay,p.demand+(J.high-U)/p.delay))
    return allowed


def endorse(view,auth,p):
    allowed=recenter_policy(view,auth,p)
    if allowed is None: return None
    return auth.emit(view.observer,view.context.era,"recenter",
                     (view.context,allowed.low,allowed.high))


def collect_endorsements(state,auth,p,received,*,byzantine=True):
    c=public_context(state,p)
    out=[]
    for i in ACTORS:
        if i not in state.faults:
            signed=endorse(LocalView(i,c,received[i]),auth,p)
            assert signed is not None
            out.append(signed)
        elif byzantine:
            out.append(auth.adversary_emit(i,c.era,"recenter",(c,F(-100),F(100))))
    return tuple(out)


def reserve_batch(state,auth,p,messages):
    if state.mode != "ready" or state.reservation is not None or p.delay_slots <= 0:
        return state
    c=public_context(state,p)
    if not state.clean_ack or state.plant.pending != (p.demand,)*p.delay_slots:
        return state
    if min(c.institution.cap,c.restored_capacity) < p.demand+p.hostile: return state
    accepted={}
    for sig in messages:
        if (not auth.verify(sig) or sig.signer not in ACTORS or sig.signer in accepted
            or sig.era != c.era or sig.kind != "recenter" or len(sig.payload) != 3
            or sig.payload[0] != c): continue
        _,low,high=sig.payload
        if not isinstance(low,F) or not isinstance(high,F) or low > high: continue
        allowed=ev.Interval(low,high).intersect(ev.Interval(F(0),min(c.institution.cap,c.restored_capacity)))
        if allowed is not None: accepted[sig.signer]=(allowed,sig)
    candidates=[]
    for a,b in combinations(sorted(accepted),2):
        allowed=accepted[a][0].intersect(accepted[b][0])
        if allowed is not None: candidates.append((allowed.low,(a,b)))
    if not candidates: return state
    u,support=min(candidates)
    cert=BatchCertificate(c,u,tuple(accepted[i][1] for i in support))
    # One atomic reservation preserves the current queue and locks both future blocks.
    return replace(state,mode="reserved",reservation=Reservation(cert,(u,)*p.delay_slots+(p.demand,)*p.delay_slots))


def ordinary_write(state,new_command):
    """An ordinary controller cannot overwrite a reserved or maintenance schedule."""
    if state.mode != "live": raise ValueError("ordinary writes disabled in maintenance/reserved mode")
    return new_command


def step(state,p,*,disturbance=F(0),live_command=None):
    """One elapsed period; the service port delivers d*T in the same plant step."""
    assert abs(disturbance) <= mode_radius(state,p)
    plant=state.plant
    mode=state.mode
    reservation=state.reservation
    if mode == "live":
        if live_command is None: raise ValueError("live mode needs a current safe command")
        new=ordinary_write(state,live_command)
    elif mode == "reserved":
        assert reservation is not None and reservation.remaining
        new=reservation.remaining[0]
    else: new=p.demand
    applied=plant.pending[0] if p.delay_slots else new
    assert 0 <= applied <= mode_capacity(state,p)
    if mode != "drain": assert applied <= state.institution.cap
    assert 0 <= new <= p.capacity
    end=plant.time+p.period
    following=ev.TimedState(end,plant.inventory+p.period*(applied-p.demand+disturbance),
        plant.pending[1:]+(new,) if p.delay_slots else (),plant.delivered+p.period*p.demand,
        plant.epoch,plant.slot+1,plant.past+(ev.Segment(plant.time,end,applied),))
    result=replace(state,plant=following,samples=state.samples+((end,following.inventory),))
    if mode == "drain":
        left=state.drain_left-1
        result=replace(result,drain_left=left,mode="isolated" if left == 0 else "drain")
    if mode == "reserved":
        reservation=replace(reservation,remaining=reservation.remaining[1:],ticks=reservation.ticks+1)
        result=replace(result,reservation=reservation)
        if not reservation.remaining:
            assert reservation.ticks == 2*p.delay_slots
            assert following.time == reservation.certificate.context.release_at
            result=replace(result,mode="release_ready",release_witness="executed-recenter-certificate")
    # Safety is checked by the verifier, not used to filter the transition relation.
    return result


def normal_step(state,auth,p,disturbance):
    """Resume the Evidence fixed policy, under the unchanged actual coalition."""
    assert state.mode == "live"
    noise=(F(0),)*3
    values=tuple(ev.quantize_rational(state.plant.inventory+n,p.quantization_step) for n in noise)
    reports=ev.make_reports(state.plant.inventory,state.faults,
        tuple(v-state.plant.inventory for v in values),(F(-8),F(8),F(-8)))
    decision=ev.decide(state.plant,reports,state.faults,True,p)
    result=step(state,p,disturbance=disturbance,live_command=decision.control)
    assert ev.tube_is_safe(ev.pending_tube(result.plant,p),p)
    return result


def perform(state,auth,order,p,**kw):
    return admin(state,auth,order_signature(state,auth,order),order,p,**kw)


def cycle(state,auth,p,repair_rounds=2,*,collect_trace=False):
    trace=[]
    initial_faults=state.faults
    def record(label):
        assert p.safe.contains(state.plant.inventory)
        if collect_trace:
            trace.append({"event":label,"time":str(state.plant.time),"inventory":str(state.plant.inventory),
                "pending":[str(u) for u in state.plant.pending],"mode":state.mode,
                "capacity":str(mode_capacity(state,p)),"radius":str(mode_radius(state,p)),
                "service":str(state.plant.delivered),"era":state.plant.epoch})
    record("start")
    state=perform(state,auth,"isolate",p,effective=True);record("effective-isolation")
    while state.mode == "drain": state=step(state,p);record("drain")
    state=perform(state,auth,"begin_repair",p);assert state.mode == "repair";record("capacity-d")
    for _ in range(repair_rounds): state=step(state,p);record("repair-service")
    state=perform(state,auth,"finish_repair",p,clean=True);record("restored-capacity")
    state=perform(state,auth,"grant_recenter",p,consent=True);record("restored-permission")
    if state.mode == "ready":
        reports=report_round(state,auth,p,attacks={(s,i):F(8 if i%2 else -8) for s in state.faults for i in ACTORS})
        state=reserve_batch(state,auth,p,collect_endorsements(state,auth,p,reports));assert state.mode == "reserved"
        record("atomic-reservation")
        while state.mode == "reserved": state=step(state,p);record("reserved-service")
    assert state.mode == "release_ready" and p.release_region.contains(state.plant.inventory)
    assert state.plant.pending == (p.demand,)*p.delay_slots
    state=perform(state,auth,"release",p);assert state.mode == "live";record("release")
    assert state.faults == initial_faults
    assert ev.tube_is_safe(ev.pending_tube(state.plant,p),p)
    for i in range(2*p.delay_slots+2):
        state=normal_step(state,auth,p,p.hostile if i%2 else -p.hostile);record("resumed-live")
    return state,trace


def run_checks():
    cases=rounds=0
    examples={}
    for m in (0,1,2):
        p=Parameters(delay_slots=m);p.validate()
        for x,queue in product((F(k,2) for k in range(9)),product((F(k,2) for k in range(5)),repeat=m)):
            if not ev.tube_is_safe(ev.pending_tube(ev.TimedState(F(0),x,queue),p),p): continue
            for faults in FAULT_FAMILY:
                state=initial(x,queue,faults,p);auth=Authentication(faults)
                result,trace=cycle(state,auth,p,collect_trace=(m not in examples and x==F(2)))
                assert result.plant.delivered == result.plant.time*p.demand
                assert result.plant.epoch == 1 and result.faults == faults
                cases+=1;rounds+=result.plant.slot
                if trace: examples[m]=trace
    # Nonidentical quantized honest reports, equivocation, and optional bad support.
    recenter_profiles=certified_endpoints=0
    for m in (1,2):
        p=Parameters(delay_slots=m)
        for x,bad in product((F(k,8) for k in range(33)),ACTORS):
            faults=frozenset((bad,));good=tuple(i for i in ACTORS if i!=bad)
            for noises,attacks,send in product(product((-p.other_error,p.other_error),repeat=2),
                                               product((F(-8),F(0),F(8)),repeat=2),(False,True)):
                plant=ev.TimedState(F(0),x,(p.demand,)*m)
                state=State(plant,faults,Institution("ready",2,p.capacity),mode="ready",
                            clean_ack=True,samples=((F(0),x),))
                auth=Authentication(faults)
                received=report_round(state,auth,p,noises=dict(zip(good,noises)),
                    attacks={(bad,i):attacks[j] for j,i in enumerate(good)})
                signed=collect_endorsements(state,auth,p,received,byzantine=send)
                reserved=reserve_batch(state,auth,p,signed);assert reserved.mode == "reserved"
                recenter_profiles+=1
                for sig in signed:
                    if sig.signer in faults: continue
                    for u in sig.payload[1:]:
                        assert p.release_region.contains(x+p.delay*(u-p.demand))
                        certified_endpoints+=1
                while reserved.mode == "reserved": reserved=step(reserved,p)
                assert p.release_region.contains(reserved.plant.inventory)
    # Readiness/permission and old leases are checked before the physical effect.
    p=Parameters();s=initial(F(2),(F(2),),frozenset((0,)),p);auth=Authentication(s.faults)
    unchanged=perform(s,auth,"isolate",p,effective=False);assert unchanged == s
    isolated=perform(s,auth,"isolate",p,effective=True)
    assert isolated.plant.pending == s.plant.pending and isolated.institution != s.institution
    assert perform(isolated,auth,"begin_repair",p) == isolated
    drained=step(isolated,p);assert drained.plant.pending == (p.demand,)
    repair=perform(drained,auth,"begin_repair",p);assert repair.mode == "repair"
    assert perform(repair,auth,"finish_repair",p,clean=False) == repair
    ready=perform(repair,auth,"finish_repair",p,clean=True)
    bare_reports=report_round(ready,auth,p)
    assert all(recenter_policy(LocalView(i,public_context(ready,p),bare_reports[i]),auth,p) is None for i in (1,2))
    assert perform(ready,auth,"grant_recenter",p,consent=False) == ready
    held=ready
    for _ in range(3): held=step(held,p)
    assert held.plant.inventory == ready.plant.inventory
    assert held.plant.delivered-ready.plant.delivered == 3*p.period*p.demand
    assert perform(ready,auth,"release",p) == ready
    ready=perform(ready,auth,"grant_recenter",p,consent=True)
    assert perform(ready,auth,"grant_recenter",p,consent=True) == ready
    impostor=auth.adversary_emit(0,ready.plant.epoch,"timed-order",(ready.institution,ready.plant.slot,"release"))
    assert admin(ready,auth,impostor,"release",p) == ready
    received=report_round(ready,auth,p,attacks={(0,i):F(8) for i in ACTORS})
    signed=collect_endorsements(ready,auth,p,received,byzantine=False)
    for invalid in ((),signed[:1],signed[:1]*2): assert reserve_batch(ready,auth,p,invalid) == ready
    c=public_context(ready,p)
    malformed=auth.adversary_emit(0,c.era,"recenter",(c,"bad",F(9)))
    stale=auth.adversary_emit(0,c.era-1,"recenter",(c,F(0),F(2)))
    forged=Signature(2,c.era,"recenter",(c,F(0),F(0)))
    reserved=reserve_batch(ready,auth,p,(malformed,stale,forged)+signed)
    assert reserved.mode == "reserved" and reserved.plant.pending == ready.plant.pending
    assert reserve_batch(reserved,auth,p,signed) == reserved
    assert perform(reserved,auth,"release",p) == reserved
    try: ordinary_write(reserved,F(0));raise AssertionError("overwrote locked batch")
    except ValueError: pass
    while reserved.mode == "reserved": reserved=step(reserved,p)
    released=perform(reserved,auth,"release",p);assert released.mode == "live"
    assert reserve_batch(released,auth,p,signed) == released
    next_ready=perform(released,auth,"isolate",p,effective=True)
    while next_ready.mode == "drain": next_ready=step(next_ready,p)
    next_ready=perform(next_ready,auth,"begin_repair",p)
    next_ready=perform(next_ready,auth,"finish_repair",p,clean=True)
    next_ready=perform(next_ready,auth,"grant_recenter",p,consent=True)
    assert next_ready.mode == "ready" and reserve_batch(next_ready,auth,p,signed) == next_ready
    new_received=report_round(next_ready,auth,p)
    new_signed=collect_endorsements(next_ready,auth,p,new_received,byzantine=False)
    assert reserve_batch(next_ready,auth,p,signed+new_signed).mode == "reserved"
    # Old-key retention cannot turn old-era artifacts into current admissions.
    leaked=Authentication(frozenset(),frozenset(((0,0),)))
    old=leaked.adversary_emit(0,0,"recenter",(c,F(0),F(2)))
    assert old.era != released.plant.epoch
    # No central inventory leaks to the batch policy's public input.
    assert public_context(ready,p) == public_context(replace(ready,plant=replace(ready.plant,inventory=F(1))),p)
    other_oracle=Authentication(frozenset((1,)));other_oracle.events=set(auth.events)
    view=LocalView(1,public_context(ready,p),received[1])
    assert recenter_policy(view,auth,p) == recenter_policy(view,other_oracle,p)
    # Aged measurement can predate isolation. Its nominal history is retained.
    pa=Parameters(safe=ev.Interval(F(0),F(8)),max_age=F(2))
    sa=initial(F(4),(F(1),),frozenset((0,)),pa);aa=Authentication(sa.faults)
    sa=normal_step(sa,aa,pa,pa.hostile)
    sa=perform(sa,aa,"isolate",pa,effective=True);sa=step(sa,pa)
    sa=perform(sa,aa,"begin_repair",pa);sa=perform(sa,aa,"finish_repair",pa,clean=True)
    sa=perform(sa,aa,"grant_recenter",pa,consent=True)
    aged=report_round(sa,aa,pa,sample_at=F(0),attacks={(0,i):F(-8) for i in ACTORS})
    plan=reserve_batch(sa,aa,pa,collect_endorsements(sa,aa,pa,aged));assert plan.mode == "reserved"
    while plan.mode == "reserved":plan=step(plan,pa)
    assert pa.release_region.contains(plan.plant.inventory)
    # r=0 needs no recenter block, even with positive command latency.
    p0=Parameters(hostile=F(0),delay_slots=2)
    s0=initial(F(0),(F(1),F(1)),frozenset(),p0)
    _,trace0=cycle(s0,Authentication(frozenset()),p0,collect_trace=True)
    assert not any(row["event"] == "atomic-reservation" for row in trace0)
    # Even the instantaneous variant cannot repeat a valid zero-time cycle forever.
    pz=Parameters(delay_slots=0);sz=initial(F(2),(),frozenset(),pz);az=Authentication(frozenset())
    for order,kw in (("isolate",{"effective":True}),("begin_repair",{}),
                     ("finish_repair",{"clean":True}),("grant_recenter",{"consent":True}),("release",{})):
        sz=perform(sz,az,order,pz,**kw)
    assert sz.mode == "live" and perform(sz,az,"isolate",pz,effective=True) == sz
    # The three original compatibility failures remain visible.
    assert F(2)>p.demand  # old queue above repair capacity
    assert F(0)+p.period*(p.demand-p.demand-p.hostile)<p.safe.low  # false isolation
    assert p.safe.low-p.hostile*p.delay<p.safe.low  # premature release without J
    # Physical transition semantics expose that failure rather than filter it out.
    unsafe=replace(released,plant=replace(released.plant,inventory=p.safe.low,pending=(p.demand,)))
    failed=step(unsafe,p,disturbance=-p.hostile,live_command=p.demand)
    assert not p.safe.contains(failed.plant.inventory)
    return {"cycles":cases,"service_rounds":rounds,"delay_slots_checked":[0,1,2],
            "recenter_report_profiles":recenter_profiles,"honest_interval_endpoints":certified_endpoints,
            "static_fault_family_size":len(FAULT_FAMILY),"round_traces":examples,
            "reservation_replay_scope_malformed_checks":True,"old_fifo_authority_retained":True,
            "permission_wait_retains_service":True,
            "aged_preisolation_sample_checked":True,"zero_disturbance_skips_recenter":True,
            "membership":"fixed identities, guarded fresh era; no fault resampling",
            "service":"exactly d*T on every elapsed step; continuous interpretation in TIMED-RECOVERY.md"}


if __name__ == "__main__": print(json.dumps(run_checks(),indent=2,sort_keys=True))
