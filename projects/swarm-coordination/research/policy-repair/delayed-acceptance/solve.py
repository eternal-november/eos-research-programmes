"""Finite physical alternatives; receipt observed before a same-tick start."""
from collections import defaultdict
from itertools import product
from random import Random

def compile_rule(rows):
    """Each (lower, upper, receipt tick, interpreted payload) is one source."""
    by_packet=defaultdict(list)
    for a,b,r,y in rows:by_packet[r,y].append((a,b))
    wait={}
    bad=[]
    bans=[]
    for (r,y),w in by_packet.items():
        lo=max([r]+[a for a,b in w]);hi=min(b for a,b in w)
        if lo>hi:
            bad.append(r)
        else:
            wait[r,y]=lo
    if not bad:return None,wait
    for a,b,r,y in rows:
        if min(a,r)>0:bans.append((0,min(a,r)-1))
        if b+1<r:bans.append((b+1,r-1))
    horizon=min(bad)
    s=0
    for a,b in sorted(bans):
        if b<s:continue
        if a>s:break
        s=b+1
    if s>=horizon:return False
    return s,wait

def play(rows,policy):
    s,wait=policy
    for a,b,r,y in rows:
        t=s if s is not None and r>s else wait[r,y]
        assert a<=t<=b,(rows,policy,(a,b,r,y),t)

def reference(rows):
    # Direct search branches only on actually observed receipts. Choices
    # for previously informed groups have no cross-group resources.
    ub=max(b for a,b,r,y in rows)
    def extend(t,W):
        groups=defaultdict(list)
        for item in W:
            a,b,r,y=item
            groups[("pending",) if r>t else ("arrived",r,y)].append(item)
        for G in groups.values():
            if all(a<=t<=b for a,b,r,y in G):continue
            if t==ub or not extend(t+1,G):return False
        return True
    return extend(0,rows)

def uniform_check():
    n=0
    for H,a,b,D in product(range(8),range(7),range(9),range(9)):
        if a>b:continue
        for stamped in [False,True]:
            rows=[(c+a,c+b,c+d,c if stamped else 0) for c in range(H+1) for d in range(D+1)]
            rule=compile_rule(rows)
            expect=(H<=b-a or D<=b) if stamped else min(H,D)<=b-a
            assert (rule is not False)==expect,(H,a,b,D,stamped)
            if rule is not False:play(rows,rule)
            n+=1
    return n

def rich_check():
    rng=Random(20261125)
    def row():
        l=rng.randrange(10)
        return l,l+rng.randrange(5),rng.randrange(14),rng.randrange(3)
    for i in range(20000):
        rows=tuple(row() for _ in range(rng.randint(1,10)))
        actual=compile_rule(rows)
        assert (actual is not False)==reference(rows),rows
        if actual is not False:play(rows,actual)
    return 20000

if __name__=="__main__":
    print("rectangular source cells",uniform_check())
    print("nonrectangular source cells",rich_check())
    # Clear is witnessed early, but the other mode's delayed telemetry
    # is too late. Silence can select a start when all still-possible
    # unseen worlds have already physically opened the gate.
    only_hybrid=((1,2,0,"clear"),(4,5,8,"slow"))
    v=compile_rule(only_hybrid);play(only_hybrid,v)
    assert v[0]==4 and reference(only_hybrid)
    print("only hybrid has guarantee",v)
    arrival_only=((1,2,2,0),(3,4,2,0))
    assert compile_rule(arrival_only) is False
    receipt_stamp=((1,2,2,0),(3,4,2,2))
    assert reference(receipt_stamp)
    print("physical timestamp can resolve equal arrival with disjoint legal windows")
