"""Distinguishing acquisition failure from a lost delivery."""
from dataclasses import dataclass,replace
from collections import defaultdict
from itertools import product

WAIT,SHARED,REPLAY=range(3)
@dataclass(frozen=True)
class W:
    # True means stable record (private, not physically delivered).
    record:bool
    shared_can_fail:bool
    repeat_link:bool
    x:int
    y:int
    measured:str

def run_effect(w,act):
    # Report observation and cleanup are physically distinct. Shared
    # unguarded retry has an admissible failed action in this source.
    if act==SHARED and not w.shared_can_fail:return w.x
    if act==REPLAY and w.record and w.repeat_link:return w.x
    return None

def synth(W,verify_delay,D,observer=True,eligibility=True):
    if 3+verify_delay>D:return None
    seen=defaultdict(list)
    for w in W:
        # A read from a real local instrument, not a public fact to crew B.
        view=w.record if observer else None
        seen[view].append(w)
    return_plan={}
    for v,Q in seen.items():
        options=[act for act in (SHARED,REPLAY) if all(run_effect(w,act)==w.x for w in Q)]
        if not eligibility:options=[a for a in options if a!=REPLAY]
        if not options:return None
        return_plan[v]=options[0]
    return return_plan

def actual(W,P,observer):
    for w in W:
        action=P[w.record if observer else None]
        assert run_effect(w,action)==w.x
        # B uses only physically observed bit and its own private entry
        # type. An unreceived source-side value is not part of it.
        actual=run_effect(w,action)
        assert (actual^w.y)==(w.x^w.y)

def direct(W,L,T,record,perm):
    V=tuple(dict.fromkeys(w.record if record else None for w in W))
    if T<3+L:return False
    actions=(SHARED,REPLAY) if perm else (SHARED,)
    for a in product(actions,repeat=len(V)):
        P=dict(zip(V,a))
        if all(run_effect(w,P[w.record if record else None])==w.x for w in W):
            return True
    return False

def check():
    n=0
    base=(W(False,False,True,0,0,"physical isolated probe failed"),
          W(True,True,True,1,0,"record exists; observation link lost"))
    # Same "no cue" despite different physically committed record/hazard.
    assert synth(base,0,3,False) is None
    P=synth(base,1,4);actual(base,P,True)
    assert not synth(base,1,3) and not synth(base,1,4,True,False)
    base=tuple(replace(q,x=x,y=y) for q,x,y in product(base,range(2),range(2)))
    for delay,T,obs,perm,cap in product(range(3),range(3,8),
                                      (False,True),(False,True),(False,True)):
        X=base+((W(True,True,False,0,1,"replay link reserved by old service"),) if cap else ())
        p=synth(X,delay,T,obs,perm)
        assert bool(p)==direct(X,delay,T,obs,perm)
        if p:actual(X,p,obs)
        n+=1
    print(n,"direct policy comparisons for the no-cue equivalence classes")
    print("after a no-cue event, treating missing delivery as a failed acquisition can make an unguarded retry unsafe")
    print("a paid local storage read, plus authorized real retransmission, restores service only with deadline slack")
if __name__=="__main__":check()
