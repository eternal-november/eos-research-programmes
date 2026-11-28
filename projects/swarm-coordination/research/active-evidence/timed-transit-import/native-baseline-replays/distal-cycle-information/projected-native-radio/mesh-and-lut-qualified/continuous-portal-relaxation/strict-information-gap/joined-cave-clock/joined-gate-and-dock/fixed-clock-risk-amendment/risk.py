"""Fixed-law ex ante risk accounting on translated certified gate holds."""
from bisect import bisect_left,bisect_right
from itertools import combinations
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json,sys

class Planner:
    def __init__(self,states):
        self.x=states
    def risk(self,events):
        return min(1,Q(len(events),len(self.x)-1))
    def event(self,hold,stamp,d):
        lo,hi=hold
        return set(range(bisect_left(self.x,stamp-hi),bisect_right(self.x,stamp+d-1-lo)))

def play(n,portal):
    c0,c1=portal['cores'][1]
    h0,h1=portal['hulls'][1]
    base=(h0,h1)
    # Consecutive candidate offset worlds are two seconds apart; a
    # single decision's collision window is under one second.
    states=tuple(j*2_000_000 for j in range(n))
    p=Planner(states);d=250_000
    hard=10*n*10**6
    assert d+base[1]-base[0]<2_000_000
    def req(j,s):
        # Separate physical occurrences by more than the entire timing
        # uncertainty range. They never meet a neighbor's hold.
        delta=n*hard+s*hard
        return (h0+delta,h1+delta),c0+delta+states[j],d
    N=set(range(n))
    for s in (0,1,n):
      for j in N:
        hold,stamp,span=req(j,s)
        assert p.event(hold,stamp,span)=={j}
        test={i for i,t in enumerate(states)
              if max(hold[0],stamp-t)<=min(hold[1],stamp-t+span-1)}
        assert test=={j}
        for i,t in enumerate(states):
            actual=(stamp-t,stamp-t+span-1)
            if i==j:assert c0+hold[0]-h0<=actual[0]<=c1+hold[0]-h0
            assert actual[0]>hold[1]-hard and actual[1]<hold[0]+hard
    k=n//2
    sets=list(map(frozenset,combinations(range(n),k)))
    assert len(sets)==comb(n,k)
    sigs=set()
    tight=Q(k,n-1)
    changed=Q(k-1,n-1)
    scenarios=0
    for A in sets:
        local=[]
        for j in sorted(N):
            new=p.event(*req(j,n))
            full=A|new
            # Direct finite-support law extreme points: all but one world
            # carry mass 1/(n-1). Compute each full union and verify.
            direct=max(Q(len(full-{deleted}),n-1) for deleted in N)
            assert direct==p.risk(full)
            admit=p.risk(full)<=tight
            local.append(admit)
            assert admit==(j in A)
            assert p.risk(full)>changed
            # The separate prospectively revised requirement only covers
            # the new action, and makes no claim about the original risk.
            assert p.risk(new)<=changed
            scenarios+=1
        sigs.add(tuple(local))
    assert len(sigs)==len(sets)
    return dict(gate=portal['gate'],worlds=n,live_k=k,queries=scenarios,
                residual_classes=len(sigs),direct_ties=scenarios,cap_after=str(changed),old_cap=str(tight))
if __name__=='__main__':
    for line in (Path(sys.argv[1])/'PORTAL.jsonl').read_text().splitlines():
        for n in (4,6,8,10,12):
            print(json.dumps(play(n,json.loads(line)),sort_keys=True))
