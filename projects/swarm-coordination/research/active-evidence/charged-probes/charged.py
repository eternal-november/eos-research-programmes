"""Cost and physical side effects of fallible active observations."""
from dataclasses import dataclass
from functools import cache
from itertools import product
from math import inf

SHARED,SEPARATE="shared","separate"

@dataclass(frozen=True)
class Source:
    cooldown:int
    spare_dur:int
    battery_cost:int
    guard:bool
    max_erased:int
    battery:int

def exact(z):
    @cache
    def solve(k,B):
        best=inf
        # Send occupies tick [s,s+1). If failed, the same staffed bus
        # cannot accept another attempt before a real cleanup with d ticks.
        # A physically separate helper must support the retained old duty
        # during that cleanup; the absence of a cue never restores it.
        if k==0:best=1
        elif z.guard:best=1+z.cooldown+solve(k-1,B)
        if B>=z.battery_cost:
            best=min(best,z.spare_dur+(0 if k==0 else solve(k-1,B-z.battery_cost)))
        return best
    return solve(z.max_erased,z.battery)

def formula(z):
    k=z.max_erased
    available=z.battery//z.battery_cost
    if not z.guard:
        return 1+k*z.spare_dur if k<=available else inf
    fast=z.spare_dur<1+z.cooldown
    j=min(k,available) if fast else 0
    return 1+j*z.spare_dur+(k-j)*(1+z.cooldown)

def reference(z):
    # Direct enumerate all mode schedules along the maximal no-cue path,
    # including the final launch that consumes a real observation.
    m=z.max_erased
    ans=inf
    for probes in product((SHARED,SEPARATE),repeat=m+1):
        if any(p==SHARED and i<m and not z.guard for i,p in enumerate(probes)):continue
        if z.battery_cost*probes.count(SEPARATE)>z.battery:continue
        time=0
        for i,p in enumerate(probes):
            if p==SHARED:time+=1+(z.cooldown if i<m else 0)
            else:time+=z.spare_dur
        ans=min(ans,time)
    return ans

def checks():
    J=0
    for d,s,c,g,k,B in product(range(5),range(1,5),range(1,4),
                               [False,True],range(8),range(9)):
        p=Source(d,s,c,g,k,B)
        v=formula(p);out=exact(p)
        assert v==out,(p,v,out)
        if k<=4:assert v==reference(p)
        J+=1
    print(J,"active policy versus closed-form comparisons; shallow cases independently enumerated")

def derive_schedule(z):
    if formula(z)==inf:return None
    # Protocol hardcodes neither outcome nor row to the receiver; it
    # continues along this no-cue schedule only for admitted erasures.
    k=z.max_erased
    j=k if not z.guard else min(k,z.battery//z.battery_cost) if z.spare_dur<1+z.cooldown else 0
    return (SEPARATE,)*j+(SHARED,)*(k-j)+(SHARED,)

def actual(source,attempts,failures,x,y):
    """Trace both actual old support and later repair via acquired cue."""
    t=0;B=source.battery;journal=[]
    for q,typ in enumerate(attempts):
        d=1 if typ==SHARED else source.spare_dur
        if typ==SEPARATE:
            if B<source.battery_cost:return None
            B-=source.battery_cost
        host="primary" if typ==SHARED else "isolated port"
        t+=d;erased=q<failures
        if not erased:
            # A learns x locally. B's private geometric type y determines
            # how a validated receipt is consumed, not the readout string alone.
            cue=x;route=cue^y
            assert route==x^y
            journal.append(("actual receipt",host,t,route))
            return t,journal
        journal.append(("no receipt, charge paid",host,t,None))
        if typ==SHARED:
            if not source.guard:return None
            for tick in range(t,t+source.cooldown):
                journal.append(("cleanup holds primary; old duty on spare",host,tick,None))
            t+=source.cooldown
    return None

def fixture():
    z=Source(cooldown=3,spare_dur=2,battery_cost=1,guard=True,max_erased=2,battery=1)
    A=derive_schedule(z)
    times=[]
    for e,x,y in product(range(3),range(2),range(2)):
        out=actual(z,A,e,x,y);assert out
        times.append(out[0])
    assert max(times)==7 and actual(z,A,2,1,0)
    # Same marginal read quality with a nonexistent action cost would
    # report that 2 isolated attempts plus the final short sample fit 5.
    assert formula(z)==7
    assert formula(Source(3,2,1,True,2,2))==5
    assert formula(Source(3,2,1,False,2,1))==inf
    assert formula(Source(3,2,1,True,2,0))==9
    print("one charged isolated attempt and staffed cleanup: exact deadline 7, not 5")
    print("a second failed trial uses its reserve even though it creates no receipt")
if __name__=="__main__":checks();fixture()
