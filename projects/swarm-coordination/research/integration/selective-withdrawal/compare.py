"""Development model, not an openTCS controller, deployment, or holdout."""
from dataclasses import dataclass
from itertools import product
from receiver import Key, Kind, Fact, Job, choose

K = {k:Key(k,"work bay","old order 7","transfer 8") for k in Kind}
DURATION=2
CUT=9
LEASE_END=CUT+1
job=Job(frozenset(K.values()),0,CUT,DURATION)

@dataclass(frozen=True)
class Run:
    prefix: int     # physical clearance and evidence for the issued prefix
    callback: int   # successful prejob callback would send reserved next step
    fence: int      # serialized effective cutoff for that exact step
    quiet: int      # protected bay not affected by the peripheral by this time
    travel: int     # remaining reservation time of the new old-generation step
    overlaps: bool  # already-issued prefix may still affect the bay
    delay: int      # verification and new right acquisition
    cutoff_wins_tie: bool

def wins(t, p, tie):
    return t < p or (t == p and tie)

def facts(r, release, sent):
    # Facts require durable positive guarantees, not mere status reads. The
    # protocol takes physical evidence and gate confirmation before reserving.
    occupied = max(r.quiet, r.prefix if r.overlaps else 0,
                   r.callback+r.travel if sent else 0)
    ready=max(release,occupied)
    admitted=ready+r.delay
    return [
      Fact(K[Kind.QUIESCENT],occupied,occupied,LEASE_END),
      Fact(K[Kind.FENCED],release,release,LEASE_END),
      Fact(K[Kind.GRANTED],admitted,admitted,LEASE_END)
    ]

def receiver_finish(f):
    for t in range(CUT+1):
        if (s:=choose(job,t,f)) is not None:
            return s+DURATION
    return None

def direct_finish(r, mode):
    # Tick simulation with no receiver or interval aggregation. At each tick
    # the transport dispatcher acts before the candidate asks for authority.
    pending, old_sent, held, countdown = True, False, True, None
    for t in range(CUT+1):
        request = (mode=="scoped" and t==r.fence) or (mode=="native" and t==r.prefix)
        def cutoff():
            nonlocal pending, held
            if request and pending:
                pending=held=False
        def send():
            nonlocal pending, old_sent
            if t==r.callback and pending:
                pending=False
                old_sent=True
        if r.cutoff_wins_tie:
            cutoff();send()
        else:
            send();cutoff()
        if old_sent and t>=r.callback+r.travel:
            old_sent=held=False
        can_reserve = (not held and not old_sent and t>=r.quiet and
                       (not r.overlaps or t>=r.prefix))
        if can_reserve:
            if countdown is None:
                countdown=r.delay
            if countdown==0:
                return t+DURATION if t+DURATION<=CUT else None
            countdown-=1
    return None

def result(r, mode):
    cutoff={"native":r.prefix,"scoped":r.fence,"smooth":None}[mode]
    sent=cutoff is None or not wins(cutoff,r.callback,r.cutoff_wins_tie)
    release=r.callback+r.travel if sent else cutoff
    return receiver_finish(facts(r,release,sent))

counts={"scoped wins":0,"native wins":0,"tie":0}
max_gain=0
for args in product(range(7),range(1,7),range(7),range(7),range(1,5),(False,True),range(3),(False,True)):
    r=Run(*args)
    out={}
    for mode in ("native","scoped","smooth"):
        out[mode]=result(r,mode)
        assert out[mode]==direct_finish(r,mode),(r,mode,out[mode],direct_finish(r,mode))
    # Adding a scope gate as a choice never forces it in mode where it loses.
    native,scoped=(out[k] if out[k] is not None else CUT+1 for k in ("native","scoped"))
    counts["scoped wins" if scoped<native else "native wins" if scoped>native else "tie"]+=1
    if scoped<native and out["native"] is not None:
        max_gain=max(max_gain,native-scoped)
r=Run(6,4,1,2,5,False,1,False)
assert [result(r,m) for m in ("scoped","native","smooth")]==[5,None,None]
assert result(Run(6,4,1,2,5,True,1,False),"scoped")==9
assert result(Run(6,4,4,2,5,False,1,False),"scoped") is None
assert result(Run(6,4,4,2,5,False,1,True),"scoped")==7
assert result(Run(6,4,1,7,5,False,1,False),"scoped") is None
print(f'matched per-tick direct checks: {sum(counts.values())*3}')
print(f'scoped option faster than safe native choice: {counts["scoped wins"]} of {sum(counts.values())}')
print(f'native option faster than scoped only: {counts["native wins"]}; tie: {counts["tie"]}')
print(f'maximum gain when both finish by the deadline in this grid: {max_gain} ticks')
print('calibration: scoped finish 5; smooth and safe native choice miss deadline 9')
print('issued prefix touches bay: finish 9; late physical clearance: deadline missed')
print('fence and callback same tick: fence first finishes at 7; callback first misses')
