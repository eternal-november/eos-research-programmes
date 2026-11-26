#!/usr/bin/env python3
"""Exact one-edge braking admission, with a full reclosure comparator."""
import heapq
import json
import random
from fractions import Fraction as Q
from itertools import product


def profiles(n,edges,p,q):
    f=[[] for _ in range(n)]
    b=[[] for _ in range(n)]
    for i,j,c in edges:
        assert c>=0
        f[i].append((j,c))
        b[j].append((i,c))
    def dijkstra(g,s):
        d={s:Q(0)}
        heap=[(Q(0),s)]
        while heap:
            z,i=heapq.heappop(heap)
            if z!=d[i]:
                continue
            for j,w in g[i]:
                u=z+w
                if j not in d or u<d[j]:
                    d[j]=u
                    heapq.heappush(heap,(u,j))
        return d
    return dijkstra(b,p),dijkstra(f,q)


def hull(lines):
    """Increasing slopes: (slope, intercept, witness index)."""
    unique={}
    for s,c,i in lines:
        if s not in unique or c>unique[s][0]:
            unique[s]=(c,i)
    out=[]
    for s,(c,i) in sorted(unique.items()):
        while out:
            p,b,j,start=out[-1]
            cut=(b-c)/(s-p)
            if start is None or cut>start:
                break
            out.pop()
        out.append((s,c,i,cut if out else None))
    return out


def separators(v,left,right):
    return (hull((-v[i],-d,i) for i,d in left.items()),
            hull((v[j],-d,j) for j,d in right.items()))


def best(v,left,right,h):
    return best_hulls(v,*separators(v,left,right),h)


def best_hulls(v,a,b,h):
    lo=Q(0)
    hi=(max(v)-min(v))/h
    i=sum(z is not None and z<=lo for _,_,_,z in a)
    j=sum(z is not None and z<=lo for _,_,_,z in b)
    opt=None
    segments=0
    while True:
        ar=a[i+1][3] if i+1<len(a) else hi
        br=b[j+1][3] if j+1<len(b) else hi
        r=min(ar,br,hi)
        s=a[i][0]+b[j][0]
        z=max(lo,min(r,s/h))
        val=a[i][1]+b[j][1]+s*z-h*z*z/2
        if opt is None or val>opt[0]:
            opt=(val,a[i][2],b[j][2],z)
        segments+=1
        if r==hi:
            return opt,segments
        i+=r==ar
        j+=r==br
        lo=r


def debt(u,v,h):
    return max(0,v-u)**2/(2*h)


def close(n,edges):
    d={(i,i):Q(0) for i in range(n)}
    for i,j,c in edges:
        d[i,j]=min(c,d.get((i,j),c))
    for k in range(n):
        for i,j in product(range(n),repeat=2):
            if (i,k) in d and (k,j) in d:
                u=d[i,k]+d[k,j]
                d[i,j]=min(u,d.get((i,j),u))
    return d


def safe(v,edges,h):
    return all(c>=debt(v[i],v[j],h) for (i,j),c in close(len(v),edges).items())


def admit_batch(v,e,batch,h):
    n=len(v)
    k=len(batch)
    if any(c<0 for _,_,c in batch):
        return False, None
    prof=[profiles(n,e,p,q) for p,q,_ in batch]
    hulls=[separators(v,l,r) for l,r in prof]
    cross=[]
    for r, (p,q,c) in enumerate(batch):
        for s,(pp,qq,new) in enumerate(batch):
            if q in prof[s][0]:
                cross.append((r,s,prof[s][0][q]+new))
    bridge=close(k,cross)
    for (r,s),d in bridge.items():
        thresh=best_hulls(v,hulls[r][0],hulls[s][1],h)[0][0]
        if batch[r][2]+d<thresh:
            return False, (r,s)
    return True, None


def replay():
    rng=random.Random(515)
    comparisons=segments=products=transitions=0
    strict_reject=batch_comparisons=batch_failures=0
    for case in range(420):
        n=rng.randrange(2,11)
        v=[Q(rng.randrange(9),2) for _ in range(n)]
        h=Q(rng.randrange(1,6))
        # Generate a valid starting system with both tight and slack bounds.
        e=[]
        for i,j in product(range(n),repeat=2):
            if i!=j and rng.random()<0.32:
                c=debt(min(v),max(v),h)+Q(rng.randrange(3),4)
                e.append((i,j,c))
        assert safe(v,e,h)
        for step in range(7):
            p,q=rng.sample(range(n),2)
            L,R=profiles(n,e,p,q)
            (val,i,j,z),nn=best(v,L,R,h)
            target=max(debt(v[ii],v[jj],h)-dd-ee for ii,dd in L.items() for jj,ee in R.items())
            assert val==target==debt(v[i],v[j],h)-L[i]-R[j]
            assert z==max(0,v[j]-v[i])/h
            assert safe(v,e+[(p,q,val)],h)
            assert not safe(v,e+[(p,q,val-Q(1,128))],h)
            assert safe(v,e+[(p,q,val+Q(1,128))],h)
            strict_reject+=val>debt(v[p],v[q],h)
            comparisons+=3
            products+=len(L)*len(R)
            segments+=nn
            if step%2==0:
                e.append((p,q,val))
                transitions+=1
        ps=rng.sample(list(product(range(n),repeat=2)),min(5,n*n))
        batch=[]
        for p,q in ps:
            L,R=profiles(n,e,p,q)
            x=best(v,L,R,h)[0][0]
            batch.append((p,q,x+Q(rng.randrange(3),8)))
        for k in range(1,len(batch)+1):
            yes,why=admit_batch(v,e,batch[:k],h)
            assert yes==safe(v,e+batch[:k],h)
            batch_comparisons+=1
            batch_failures+=not yes
    v=list(map(Q,[0,1,2]))
    assert safe(v,[(0,1,Q(1,4))],Q(2))
    assert safe(v,[(1,2,Q(1,4))],Q(2))
    assert not safe(v,[(0,1,Q(1,4)),(1,2,Q(1,4))],Q(2))
    assert best(v,*profiles(3,[(0,1,Q(1,4))],1,2),Q(2))[0][0]==Q(3,4)
    # All velocities equal and a zero-cost cycle.
    v=[Q(1)]*3
    assert best(v,*profiles(3,[(0,1,Q(0)),(1,0,Q(0))],1,2),Q(2))[0][0]==0
    assert admit_batch(v,[(0,1,Q(0)),(1,0,Q(0))],[(1,2,Q(0)),(2,0,Q(0))],Q(2))==(True,None)
    assert strict_reject>0 and batch_failures>0
    return dict(full_reclosure_checks=comparisons,applied_amendments=transitions,
                endpoint_only_false_passes=strict_reject,
                direct_pair_terms=products,envelope_intervals=segments,
                threshold_after_first_grant_in_three_robot_case="3/4",
                batch_reclosure_checks=batch_comparisons,batch_refusals=batch_failures)


if __name__=='__main__':
    print(json.dumps(replay(),indent=2))
