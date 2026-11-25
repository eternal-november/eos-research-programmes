"""Contingent fallback capacity for overlapping live duties.

All action IDs are physical. A fallback receiver at its own cut observes
only source-issued receipt state; no source-world index is available.
"""
from dataclasses import dataclass
from collections import defaultdict
from itertools import product,combinations
from functools import reduce
from random import Random

@dataclass(frozen=True)
class Trace:
    viable:tuple             # physically qualified per-duty helper choices
    old_active:frozenset     # other already committed resource effects
    received:tuple           # first actual mate/receipt observation, or none
    dispatch:int
    notice_at:int
    failed:frozenset=frozenset()
    denied:frozenset=frozenset()

def stock(h,scope):
    return tuple(frozenset(S) - h.old_active - h.failed - h.denied - set(scope) for S in h.viable)

def partition(T):
    classes=defaultdict(list)
    for t in T:
        key=t.received if t.notice_at<=t.dispatch else ()
        classes[key].append(t)
    return tuple(tuple(v) for v in classes.values())

def common(C,blocked=()):
    G=[stock(t,blocked) for t in C]
    return tuple(reduce(frozenset.intersection,row) for row in zip(*G))

def perfect(G):
    return next((m for m in product(*G) if len(set(m))==len(m)),None)

def all_feasible(T,blocked=()):
    return all(perfect(common(C,blocked)) is not None for C in partition(T))

def augment(G):
    owner={}
    def add(j,seen):
        for r in G[j]-seen:
            seen.add(r)
            if r not in owner or add(owner[r],seen):
                owner[r]=j;return True
        return False
    for j in range(len(G)):
        if not add(j,set()):return None
    m=[None]*len(G)
    for r,j in owner.items():m[j]=r
    return tuple(m)

def alternating_safe(G,m):
    """Release exactly those helpers that can be unused by a matching."""
    owner={r:j for j,r in enumerate(m)}
    free=frozenset().union(*G)-owner.keys()
    reachable=set(free);Q=list(free)
    # Follow swaps which move the unused position from an offered helper
    # to a duty's current assignment.
    inv=defaultdict(list)
    for j,S in enumerate(G):
        for r in S:inv[r].append(j)
    for r in Q:
        for j in inv[r]:
            p=m[j]
            if p not in reachable:reachable.add(p);Q.append(p)
    return reachable

def released(T,H):
    safe=set(H)
    for C in partition(T):
        G=common(C);m=augment(G)
        if m is None:return set()
        useful=frozenset().union(*G)
        safe &= (set(H)-useful)|alternating_safe(G,m)
    return safe

def meet(effect_tracks, first, dwell):
    """True plant-side handoff and a local observation delivered separately.

    Commit may not occur until every support point in the declared
    noninterruptible dwell interval is good.
    """
    return first+dwell if all(effect_tracks[k] for k in range(first,first+dwell)) else None

def authored(new_latency=0, certified=True, second_loss=False, method="socket"):
    # Foreground A/B obligations already exist. X is in physical use by a
    # different prior task, until after the fallback's common span. The
    # first attempted repair transfers the source of the next clearance
    # from a coupled dock to an alternate physical relay only if it mates.
    r=set(range(6))
    profiles=[tuple([True]*7),(True,True,False,True,True,True,True)]
    T=[]
    for effect_pairs in profiles:
        # Source preparations: the mate token becomes actual only after
        # continuous support. Installed activator changes the later
        # physically available helper, not just receipt metadata.
        t=meet(effect_pairs,1,2)
        relay=4 if t is not None else 2
        G=(frozenset({0,relay}),frozenset({1,relay}))
        if certified:
            # Independent readout protocols in this authored simulation
            # compute the same interpreted cut. A slow latch costs an
            # extra polling delay; sender cannot attest before true mate.
            proof=(t is not None if method=="socket" else
                            all(effect_pairs[1:3]))
            assert proof==(t is not None)
            a=("mate",t) if proof else ("declined",)
        else:
            a=("queued",) # commanded, not a true source settlement fact
        failed=frozenset({4}) if second_loss and t is not None else frozenset()
        T.append(Trace(G,frozenset({3}),a,4,3+new_latency,failed))
    return tuple(T),r

def authored_checks():
    T,R=authored()
    assert released(T,R)==R
    for r in range(6):assert all_feasible(T,{r})
    late,_=authored(new_latency=2)
    unknown,_=authored(certified=False)
    assert released(late,R)==released(unknown,R)=={2,3,4,5}
    # Physical second loss of helper 4 intersects with the first
    # completed mate but not with a proposal to transfer.
    w,_=authored(second_loss=True)
    assert released(w,R)=={2,3,4,5}
    assert all_feasible(w) and not all_feasible(w,{0})
    print("timely source witness allows a new task on 0 or 1; late or receipt-incompatible source does not")
    assert released(T+w,R)=={2,3,4,5}
    print("actual second loss after the completed first repair withdraws that allowance")
    print("if that second loss is still possible, the same first receipt cannot reserve helper 0")
    alternate,_=authored(1,method="latch")
    assert released(alternate,R)==released(T,R)
    for name,U in [("socket",T),("latch",alternate),("late",late),("loss",w)]:
        # Candidate extra task needs helper 0 and is already in flight
        # at the fallback cut. Helper 3 remains occupied by an old duty.
        can_run=(0 in released(U,R) and all(
                0 not in (h.old_active|h.failed) for h in U))
        print(name,"additional task on 0 while both foreground obligations protected",int(can_run))

def random_check():
    rng=Random(551967);k=0
    for _ in range(5000):
        P=range(rng.randint(2,8));m=rng.randint(1,4)
        T=[]
        for i in range(rng.randint(1,4)):
            G=tuple(frozenset(r for r in P if rng.randrange(3)) for j in range(m))
            A=frozenset(r for r in P if not rng.randrange(12))
            T.append(Trace(G,A,(str(rng.randrange(3)),),4,rng.randrange(8)))
        v=released(T,P)
        assert v=={r for r in P if all_feasible(T,{r})}
        k+=len(P)
    print(k,"strong matched fallback recomputation comparisons over 5000 source models")

if __name__=="__main__":authored_checks();random_check()
