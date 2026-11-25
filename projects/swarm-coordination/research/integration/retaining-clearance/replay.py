"""Exact selected native RWARE execution with a frozen observer boundary."""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import hashlib
import numpy as np
import rware_rotation as rw
import isolated as iso

HERE=Path(__file__).resolve().parent
M=6
U=frozenset(range(M))
OLD_REWARD=.5

def subsets(X,k):
    return tuple(frozenset(x) for x in combinations(sorted(X),k))

def cover(m,q,k):
    u=frozenset(range(m))
    worlds=subsets(u,q)
    candidates=subsets(u,k)
    full=(1<<len(worlds))-1
    masks=[sum(1<<j for j,b in enumerate(worlds) if b<=cap) for cap in candidates]
    @lru_cache(None)
    def visit(rem):
        if not rem:return ()
        bit=rem & -rem
        return min(((i,)+visit(rem & ~mask) for i,mask in enumerate(masks) if bit&mask),
                   key=lambda result:(len(result),result))
    return tuple(candidates[i] for i in visit(full))

def full_feasible(B,Y,E=()):
    return set(Y)-set(B)-set(E)

def code_policy(block,Y,E=()):
    a=full_feasible(block,Y,E)
    return min(a) if a else None

def make(n):
    n.Agent.counter=n.Shelf.counter=0
    D=n.Direction
    pos=[(i,1) for i in range(1,M+1)]+[(i,0) for i in range(1,M+1)]
    agents=[n.Agent(*p,D.DOWN,0) for p in pos]
    shelves=[n.Shelf(*p) for p in pos]
    for a,s in zip(agents,shelves):
        a.carrying_shelf=s
    for a in agents[:M]:
        a.has_delivered=True  # installed old state: each shelf return is owed
    w=iso.NS(grid_size=(4,M+2),msg_bits=0,n_agents=2*M,agents=agents,shelfs=shelves,
      grid=np.zeros((2,4,M+2),dtype=int),goals=[],highways=np.zeros((4,M+2),dtype=bool),
      request_queue=[*shelves[M:]],reward_type=n.RewardType.TWO_STAGE,
      np_random=iso.NS(choice=lambda C:min(C,key=lambda s:s.id)),_cur_steps=0,
      _cur_inactive_steps=0,max_steps=20,max_inactivity_steps=None,
      _make_obs=lambda a:None,_get_info=lambda:{})
    w._recalc_grid=lambda:n._recalc_grid(w)
    w._is_highway=lambda x,y:n._is_highway(w,x,y)
    w._recalc_grid()
    return w

def run(n,initial_faults,Y,returner,chooser):
    w=make(n)
    a=n.Action
    def plant(old={},new={},old_only=True):
        cmd=[a.NOOP.value]*(2*M)
        for k,m in old.items():cmd[k]=m.value
        for k,m in new.items():cmd[M+k]=m.value
        result=n.step(w,cmd)
        xy=[(rob.x,rob.y) for rob in w.agents]
        assert len(xy)==len(set(xy))
        assert all(w.agents[i].carrying_shelf is w.shelfs[i] and w.agents[i].has_delivered
                   for i in range(M)), 'old rights remain outstanding'
        if old_only:assert sum(result[1])==0
        return result
    plant({i:a.FORWARD for i in U-initial_faults})
    def live_gate_occupants():
        return frozenset(i for i in U if w.grid[0,1,i+1]==w.agents[i].id)
    # The old observation adapter consumes actual plant positions / carrier identity.
    # Its view is not passed to the receiver except through the selected encoder.
    old_evidence=live_gate_occupants()
    assert old_evidence==initial_faults
    late_added=frozenset()
    if returner is not None:
        plant({returner:a.LEFT})
        plant({returner:a.LEFT})
        before_return=live_gate_occupants()
        plant({returner:a.FORWARD})
        after_return=live_gate_occupants()
        # A new-stage fixture monitor sees the exact native entrance edge.
        # It does not receive the old frozen occupancy or the encoder's tag.
        late_added=after_return-before_return
        assert w.agents[returner].y==1
    # At the late cut only the logged dock authorization + selected retained
    # summary reach the policy. For the visible-reentry control the late
    # sensor adapter emits only a fresh addition observed at the gate.
    assert late_added==({returner} if returner is not None else set())
    assert live_gate_occupants()==old_evidence|late_added
    w.goals=[(i+1,1) for i in sorted(Y)]
    for x,y in w.goals:w.highways[y,x]=True
    act=chooser(old_evidence,Y,late_added)
    assert act is None or act in Y
    result=plant(new={act:a.FORWARD} if act is not None else {},old_only=False)
    service=sum(result[1])==OLD_REWARD
    if service:
        assert act is not None and w.agents[M+act].y==1
        assert w.agents[M+act].has_delivered and w.agents[M+act].carrying_shelf is w.shelfs[M+act]
    elif act is not None:
        assert w.agents[M+act].y==0 and not w.agents[M+act].has_delivered
    # Matched independent physical oracle for selected one-step dispatch.
    assert service == (act is not None and act not in (initial_faults|late_added))
    return service,act

def main():
    n=rw.engine(HERE/'native_source.py')
    assert len(cover(3,1,2))==2
    for m in range(2,7):
        for q in range(1,m):
            for r in range(q+1,m+1):
                c=cover(m,q,r-1)
                B=subsets(range(m),q)
                assert all(any(b<=d for d in c) for b in B)
                if r==q+1:assert len(c)==len(B)
                if r==m:assert len(c)==q+1
    counts=Counter()
    C=cover(M,2,3)
    assert len(C)==6
    print('six cap triples', [sorted(c) for c in C])
    lookup=lambda b:next(c for c in C if b<=c)
    nominal=lambda b,y,e:code_policy(lookup(b),y)
    full=lambda b,y,e:code_policy(b,y)
    measured=lambda b,y,e:code_policy(lookup(b),y,e)
    exact=lambda b,y,e:code_policy(b,y,e)
    none=lambda b,y,e:min(y)
    blocked_example=None
    for B in subsets(U,2):
        for Y in subsets(U,4):
            for name,chooser in [('cover',nominal),('full',full),('no-memory',none)]:
                passed,act=run(n,B,Y,None,chooser)
                counts['nominal '+name]+=bool(passed)
            for z in U-B:
                for name,chooser in [('cover-blind',nominal),('full-blind',full),
                                     ('cover-visible',measured),('full-visible',exact)]:
                    passed,act=run(n,B,Y,z,chooser)
                    counts['reentry '+name]+=bool(passed)
                    if name=='cover-visible' and not passed:
                        assert act is None and (Y-(B|{z}))
                        if blocked_example is None:blocked_example=(sorted(B),sorted(lookup(B)),sorted(Y),z)
                    if name=='cover-blind' and not passed:assert act==z
    for B in subsets(U,2):
        for Y in subsets(U,3):
            for name,chooser in [('cover',nominal),('full',full)]:
                passed,_=run(n,B,Y,None,chooser)
                counts['narrow '+name]+=bool(passed)
    assert counts['nominal cover']==counts['nominal full']==225
    assert counts['reentry full-visible']==900
    assert counts['reentry full-blind']==counts['reentry cover-blind']==675
    assert counts['narrow full']==300
    assert counts['reentry cover-visible']<900
    print('checked nominal total per policy',225)
    print('checked reentry total per policy',900)
    print('checked narrow total per policy',300)
    for k,v in sorted(counts.items()):print(k,v)
    print('false refusal with visible reentry', blocked_example)
    print('maximum fixed-width code reduction','full 4 bits; nominal 3; visible reentry 4')
if __name__=='__main__':
    main()
