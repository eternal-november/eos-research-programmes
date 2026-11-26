import json
import random
from itertools import combinations,product
from timed import Timing,execute,interval,stabbing,schedule

time_checks=0
for a,b,c,e,f,h,s,d in product(range(2),range(2),range(4),range(2,5),
                               range(3,7),range(1,3),range(1,3),range(4,8)):
    w=Timing(1,c,(a,e),(b,f),h,s,d)
    l,r=interval(w)
    for t in range(8):
        i,o=execute(w,t)
        assert i[-1]==(10,'separate-load-destination')
        assert (o=='delivered')==(l<=t<=r)
        time_checks+=1

# Exact minimum number of times stabbing each nonempty eligible family.
intervals=[(a,b) for a in range(5) for b in range(a,5)]
time_sets=[]
for k in range(1,6):
    for T in combinations(range(5),k):
        mask=sum(1<<i for i,(l,r) in enumerate(intervals) if any(l<=t<=r for t in T))
        time_sets.append((k,mask))
for family in range(1,1<<len(intervals)):
    k0=next(k for k,m in time_sets if m&family==family)
    xs=stabbing([w for i,w in enumerate(intervals) if family>>i&1])
    assert len(xs)==k0

def direct(rows,k):
    # Enumerate unrestricted maps and recipient's feasible times directly.
    zs=sorted({z for z,_,_ in rows})
    for m in product(range(k),repeat=len(zs)):
        messages=dict(zip(zs,m))
        feasible={}
        for z,v,(l,r) in rows:
            c=(messages[z],v)
            ticks=set(range(l,r+1))
            feasible[c]=feasible.get(c,ticks)&ticks
        if all(feasible.values()):
            return True
    return False

def graph_source(n,edges):
    it=[]
    for e,(u,v) in enumerate(edges):
        it.extend([(u,e,(2,2)),(v,e,(4,4))])
    for z in range(n):
        it.append((z,len(edges)+z,(2,4)))
    return it

graphs=0
for n in range(1,6):
    E=list(combinations(range(n),2))
    for es in range(1<<len(E)):
        rows=graph_source(n,[e for i,e in enumerate(E) if (es>>i)&1])
        enc,choices=schedule(rows)
        k=len(set(enc.values()))
        assert direct(rows,k) and not direct(rows,k-1)
        graphs+=1

# Each receiver view of a pentagon can be dealt with using 2 choices;
# one common sender encoding (which doesn't see the view) requires 3.
C5=graph_source(5,[(i,(i+1)%5) for i in range(5)])
assert len(set(schedule(C5)[0].values()))==3
assert all(direct([r for r in C5 if r[1]==v],2) for v in range(5))
# Same output width and send time, but only one producer observes a separable fact.
pos=[(0,0,(2,4)),(0,0,(4,6)),(1,0,(7,7))]
neg=[(0,0,(2,4)),(1,0,(4,6)),(0,0,(7,7))]
assert schedule(pos)[1]=={(0,0):4,(1,0):7}
assert schedule(neg) is None
assert schedule([(0,v,w) for z,v,w in pos]) is None # miss the decision cut
for start in (4,7):
    w=Timing(1,start,(1,start+2),(1,start+4),2,2,start+4)
    other,out=execute(w,start)
    assert out=='delivered'
    assert any(start<=tick<start+4 for tick,_ in other)
    assert other[-1]==(10,'separate-load-destination')
nonconvex=[{0,1},{1,2},{0,2}]
assert all(a&b for a,b in combinations(nonconvex,2)) and not set.intersection(*nonconvex)
# Material timed transfer realizes every narrow window used in the example.
for l,r in [(2,4),(4,6),(7,7)]:
    w=Timing(1,l,(1,r+2),(1,r+4),2,2,r+4)
    assert interval(w)==(l,r)
    assert [t for t in range(9) if execute(w,t)[1]=='delivered']==list(range(l,r+1))

partial=Timing(1,1,(0,3),(0,4),2,2,10)
assert execute(partial,1)[1]=='transferred'
assert not (interval(partial)[0]<=1<=interval(partial)[1])

# Independent schedule enumeration over authored overlapping history cells.
rng=random.Random(2653)
for _ in range(1200):
    n=rng.randint(1,5)
    occupied=rng.sample(list(product(range(n),range(4))),rng.randint(1,n*4))
    rows=[(z,v,rng.choice(intervals)) for z,v in occupied
          for __ in range(rng.randint(1,3))]
    solution=schedule(rows)
    if solution is None:
        assert not direct(rows,n)
    else:
        enc,choices=solution
        assert all(l<=choices[enc[z],v]<=r for z,v,(l,r) in rows)
        k=len(set(enc.values()))
        assert direct(rows,k) and not direct(rows,k-1)

print(json.dumps(dict(timed_execution_checks=time_checks,interval_families=32767,
    conflict_graphs=graphs,overlapping_history_tables=1200,pentagon_alphabet=3,good_notice_choices=[4,7]),
    sort_keys=True))
