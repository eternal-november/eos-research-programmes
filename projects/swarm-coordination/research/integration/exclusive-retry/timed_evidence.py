"""Retirement timing as a genuine observation, with one fixed source history."""
from collections import defaultdict
from functools import lru_cache
from itertools import product
from random import Random
from math import inf

def result(state,i,t):
    # A test fixture supplies a positive action duration and finally proves
    # either one actual committed effect or scope-correct physical release.
    ok,length=state[i]
    return ok,t+length,length

def opt(worlds,measured):
    n=len(worlds[0])
    @lru_cache(None)
    def go(states,choices):
        # State cells contain same-local-view alternatives, not runtime truth.
        # Carry actual elapsed time separately for each source row.
        if not choices:return inf,None
        out=(inf,None)
        for i in choices:
            groups=defaultdict(list)
            worst=0
            for w,t in states:
                passed,end,duration=result(worlds[w],i,t)
                if passed:worst=max(worst,end)
                else:groups[duration if measured else None].append((w,end))
            sub={}
            for label,group in groups.items():
                v,p=go(tuple(group),tuple(k for k in choices if k!=i))
                worst=max(worst,v);sub[label]=p
            if worst<out[0]:out=(worst,(i,sub))
        return out
    return go(tuple((j,0) for j in range(len(worlds))),tuple(range(n)))

def at_deadline(worlds,measured,deadline):
    # Direct recursive existence, no cost recurrence or stored optimizer
    # values. Each branch replays concrete release/completion events.
    def reach(rows,remaining):
        for i in remaining:
            branching=defaultdict(list)
            for prior,state in rows:
                ok,t,duration=result(state,i,prior)
                if t>deadline:break
                if not ok:branching[duration if measured else None].append((t,state))
            else:
                left=set(remaining)-{i}
                if all(reach(next_states,left) for next_states in branching.values()):return True
        return False
    return reach([(0,w) for w in worlds],set(range(len(worlds[0]))))

def execution(plant,world,policy,measured):
    t=0;live=None;log=[]
    while policy:
        i,cont=policy
        assert live is None
        live=i;log.append((t,'physical hold',i))
        ok,end,duration=result(world,i,t)
        if ok:
            log.append((end,'actual settled effect',i))
            return end,log
        if plant=='dock':tag='old cradle physically unlatched'
        elif plant=='power':tag='capacitor at safe discharge threshold'
        else:raise ValueError(plant)
        log.append((end,tag,i));live=None
        t=end;policy=cont[duration if measured else None]
    return inf,log

def main():
    worlds=(
        ((False,1),(True,1),(False,5)),
        ((False,2),(False,5),(True,1)),
        ((True,1),(False,5),(False,5)))
    yes,p=opt(worlds,True)
    no,q=opt(worlds,False)
    assert yes==3 and no==7,(yes,no)
    for plant in ("dock","power"):
        assert max(execution(plant,w,p,True)[0] for w in worlds)==yes
        assert max(execution(plant,w,q,False)[0] for w in worlds)==no
    print('same attempts and holds; exact proved time bound is 3 with a local clock, 7 with only the untimed release')
    # Coarsening does not license multiplying or freely recombining times.
    joint=(((False,2),(True,1)),((False,1),(True,2)))
    assert max(sum(route[1] for route in w) for w in joint)==3
    assert max(w[0][1] for w in joint)+max(w[1][1] for w in joint)==4
    check=0
    rng=Random(432721)
    for _ in range(2040):
        n=rng.randrange(2,6)
        ws=tuple(tuple((bool(rng.randrange(3)),rng.randrange(1,5))
                       for a in range(n)) for w in range(rng.randrange(1,7)))
        for clock in (False,True):
            ans,p=opt(ws,clock)
            if ans==inf:assert not at_deadline(ws,clock,4*n)
            else:
                assert at_deadline(ws,clock,ans)
                assert not at_deadline(ws,clock,ans-1)
                assert max(execution('dock',w,p,clock)[0] for w in ws)==ans
            check+=1
    print(check,'direct-deadline and trustworthy-release policy checks')
if __name__=='__main__':main()
