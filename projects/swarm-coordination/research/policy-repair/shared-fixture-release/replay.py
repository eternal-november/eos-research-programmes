from collections import deque, Counter
from functools import lru_cache
from itertools import product, permutations
from random import Random
import json

def law(h,c,L,tau):
    commit=max(h,L,tau)+h+2*c
    wait=max(tau+2*h+c,L)+c
    info=max(max(h,tau)+c+h,L)+c
    return min(commit,wait),commit,wait,info

# An event is (phase, item, ticks remaining).  Idle item is -1.
IDLE=('idle',-1,0)
def step(state,t,h,c,L,tau,late):
    done,event=state
    phase,i,k=event
    out=[]
    if phase=='idle':
        out.append(state)
        for j in range(2):
            if not (done>>j)&1:
                out.append((done,('held',j,0) if h==1 else ('mount',j,h-1)))
    elif phase=='mount':
        out.append((done,('held',i,0) if k==1 else ('mount',i,k-1)))
    elif phase=='held':
        out.append(state)
        if t>=tau and (i!=late or t>=L):
            out.append((done|1<<i,IDLE) if c==1 else (done,('move',i,c-1)))
    else:
        assert phase=='move'
        out.append((done|1<<i,IDLE) if k==1 else (done,('move',i,k-1)))
    return out

def direct(h,c,L,tau):
    start=(0,IDLE)
    @lru_cache(None)
    def world(t0,state,late):
        q=deque([(t0,state)])
        seen=set()
        while q:
            t,s=q.popleft()
            if s[0]==3:
                return t
            key=(min(t,max(tau,L)),s)
            if key in seen:
                continue
            seen.add(key)
            for u in step(s,t,h,c,L,tau,late):
                q.append((t+1,u))
        raise AssertionError("reachable")
    common={start}
    for t in range(tau):
        after0={u for s in common for u in step(s,t,h,c,L,tau,0)}
        after1={u for s in common for u in step(s,t,h,c,L,tau,1)}
        assert after0==after1
        common=after0
    return min(max(world(tau,s,0),world(tau,s,1)) for s in common),world(0,start,0)

def close(t,job):
    r,h,a,c=job
    return max(max(t,r)+h,a)+c

def effective(job):
    r,h,a,_=job
    return max(r,a-h)

def schedule(t,jobs):
    for j in jobs:
        t=close(t,j)
    return t

def main():
    kinds=Counter()
    for h,c,L,tau in product(range(1,5),range(1,4),range(8),range(9)):
        opt,commit,wait,info=law(h,c,L,tau)
        actual,oracle=direct(h,c,L,tau)
        assert (opt,info)==(actual,oracle),(h,c,L,tau,opt,info,actual,oracle)
        kinds['commit' if commit<wait else 'wait' if wait<commit else 'tie']+=1
        if info<opt:kinds['real_information_gap']+=1
    assert law(3,1,5,1)==(9,10,9,8)
    assert law(3,1,9,1)==(10,14,10,10)
    assert law(3,1,1,9)==(14,14,17,14)
    rnd=Random(486540)
    for _ in range(1024):
        j=[(rnd.randrange(15),rnd.randrange(1,8),rnd.randrange(20),rnd.randrange(1,8))
           for k in range(rnd.randrange(1,7))]
        t=rnd.randrange(10)
        assert schedule(t,sorted(j,key=effective))==min(schedule(t,p) for p in permutations(j))
    print(json.dumps(dict(kinds=kinds,scenario_count=4*3*8*9,order_cases=1024),sort_keys=True))
if __name__=='__main__':
    main()
