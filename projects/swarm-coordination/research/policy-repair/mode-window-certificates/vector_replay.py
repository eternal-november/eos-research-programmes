from itertools import product
from random import Random

# Constraint (u,v,w,h): t[v]-t[u] <= w, historically justified by h.
def compact(es):
    mins={}
    for u,v,w,h in es:
        if (u,v) not in mins or (w,h)<mins[u,v]:
            mins[u,v]=w,h
    return [(u,v,w,h) for (u,v),(w,h) in sorted(mins.items())]

def plan(vs,edges):
    d=[0]*vs;pred=[None]*vs
    x=None
    for _ in range(vs):
        x=None
        for u,v,w,h in edges:
            if d[u]+w<d[v]:
                d[v]=d[u]+w;pred[v]=(u,v,w,h);x=v
        if x is None:return [t-d[0] for t in d],None
    for _ in range(vs):x=pred[x][0]
    at=x;cycle=[]
    while True:
        e=pred[at]
        assert e[1]==at
        cycle.append(e);at=e[0]
        if at==x:break
        assert len(cycle)<vs
    assert sum(e[2] for e in cycle)<0
    assert len(cycle)<=vs
    return None,cycle

def respects(clock,edges):
    return all(clock[v]-clock[u]<=w for u,v,w,_ in edges)

def common_edges(vs,H):
    return [(0,i,H,-1) for i in range(1,vs)]+[(i,0,0,-1) for i in range(1,vs)]

def alternatives(vs,ambient,histories,n_modes):
    rejected=set()
    for m in range(n_modes):
        edges=ambient+[(u,v,w,h) for h,row in enumerate(histories) for u,v,w in row[m]]
        p,c=plan(vs,compact(edges))
        if p is not None:
            assert respects(p,edges)
            return (m,p),None
        rejected.update(h for _,_,_,h in c if h>=0)
    return None,rejected

rng=Random(20261125)
for _ in range(2400):
    vs=rng.randrange(2,5);H=rng.randrange(1,5);modes=rng.randrange(1,5)
    hs=[[[(rng.randrange(vs),rng.randrange(vs),rng.randrange(-3,5))
         for _ in range(rng.randrange(0,5))] for _ in range(modes)]
        for _ in range(rng.randrange(1,12))]
    ambient=common_edges(vs,H)
    raw=[]
    for m in range(modes):
        es=ambient+[(u,v,w,h) for h,row in enumerate(hs) for u,v,w in row[m]]
        raw.extend((m,t) for t in ((0,)+p for p in product(range(H+1),repeat=vs-1))
                   if respects(t,es))
    a,c=alternatives(vs,ambient,hs,modes)
    assert bool(a)==bool(raw)
    if a:assert (a[0],tuple(a[1])) in raw
    else:
        assert len(c)<=vs*modes
        assert alternatives(vs,ambient,[hs[i] for i in sorted(c)],modes)[0] is None

for vs in range(2,8):
    for m in range(1,7):
        cycle=[(i,i+1,0) for i in range(vs-1)]+[(vs-1,0,-1)]
        hs=[[([cycle[j]] if k==i else []) for k in range(m)]
            for i in range(m) for j in range(vs)]
        A=common_edges(vs,1)
        p,c=alternatives(vs,A,hs,m)
        assert p is None and len(c)==vs*m
        for skip in range(vs*m):
            assert alternatives(vs,A,[h for i,h in enumerate(hs) if i!=skip],m)[0]
print("2400 exact finite-graph comparisons with integer timeline enumeration")
print("tight multi-mode cycle certificates verified for 2..7 event vertices and 1..6 modes")

# I2 concrete timing projection: [origin, issue flag, listen, transfer,
# report at base]. The real source gave issue availability; the mode
# being compared fixes one route family and this established custody law.
def flag_mode(earliest_issue,setup,budget,receiver_frozen):
    es=common_edges(5,budget)
    es += [(1,0,-earliest_issue,0),  # must finish the old issue duty first
           (2,0,-2,1),              # B must first deliver its own report
           (2,1,-setup,2),          # flag physically ready by the reading
           (3,2,-2,3),              # read one full tick, move once
           (4,3,-3,4)]              # transfer one full tick, return twice
    if receiver_frozen:es.append((0,2,2,5))
    return plan(5,es)

for name,nd in [
    ("healthy, retained read cut", (0,2,7,True)),
    ("one extra earlier duty, retained read cut",(1,2,7,True)),
    ("new timing but old deadline",(1,2,7,False)),
    ("new timing and a revised deadline",(1,2,8,False))]:
    p,cy=flag_mode(*nd)
    print(name,"schedule" if p else "negative cycle",p or cy)
