"""Compute a conservative tile adjacency for motion confined to lookup cubes."""
import sys, struct, re, json, math
from heapq import heappush,heappop
from pathlib import Path
from itertools import product
import numpy as np
from collections import Counter,deque

base=Path(sys.argv[1])
I=(103,104,105,106,107,108,114,115,116,117,118,119,121,122,124,128,130,132,156,157)
K=((115,118),(117,119))

def bulk():
    b=(base/"geom"/"cave_circuit_01.dat").read_bytes()
    n=struct.unpack_from("<Q",b)[0]
    P={}
    for x,y,z,v in struct.iter_unpack("<iiiQ",memoryview(b)[8:8+20*n]):
        if v in I:P[x,y,z]=v
        else:P.pop((x,y,z),None)
    pts=np.asarray(list(P),dtype=int)
    low=pts.min(0)
    up=pts.max(0)
    dense=np.zeros(tuple(up-low+1),dtype=np.int16)
    dense[tuple((pts-low).T)]=list(P.values())
    return dense,low,len(P)

def adjacent(A,lo):
    cnt=Counter();gate={}
    for d in product((-1,0,1),repeat=3):
        if d<=(0,0,0):continue
        beg=np.maximum(0,-np.array(d))
        end=np.minimum(A.shape,np.asarray(A.shape)-d)
        a=A[tuple(slice(i,j) for i,j in zip(beg,end))]
        b=A[tuple(slice(i+v,j+v) for i,j,v in zip(beg,end,d))]
        good=(a!=b)&(a>0)&(b>0)
        u,v=a[good],b[good]
        if not len(u):continue
        code=np.minimum(u,v).astype(int)*1000+np.maximum(u,v)
        ts,m=np.unique(code,return_counts=True)
        for o,q in zip(ts,m):cnt[divmod(int(o),1000)]+=int(q)
        for k in (divmod(int(code),1000) for code in ts):
            g=good&(((a==k[0])&(b==k[1]))|((a==k[1])&(b==k[0])))
            q=np.stack(np.where(g),axis=1)+beg+lo
            if len(q):
                # doubled integer coordinates are exact closed cube contacts.
                il=2*q.min(axis=0)+np.maximum(-1,2*np.array(d)-1)
                ih=2*q.max(axis=0)+np.minimum(1,2*np.array(d)+1)
                if k not in gate:gate[k]=(il,ih)
                else:gate[k]=np.minimum(il,gate[k][0]),np.maximum(ih,gate[k][1])
    return cnt,gate

def reach(E,remove):
    q=deque([103]);d={103:0}
    G={u:[] for u in I}
    for a,b in E-set(remove):G[a].append(b);G[b].append(a)
    while q:
        u=q.popleft()
        for v in G[u]:
            if v in d:continue
            d[v]=d[u]+1;q.append(v)
    return d.get(132)


S=(275,-175,2)
G=(350,-300,13)

def gap(A,B):
    q=[max(0,a-d,c-b) for a,b,c,d in zip(*A,*B)]
    return math.isqrt(1000**2*sum(x*x for x in q))//2

def point(x):return ([2*i for i in x],)*2

def routes(portals,allowed,v,B,halt=()):
    touch={i:[] for i in I}
    for e in allowed:
        a,b=e;touch[a].append((b,e));touch[b].append((a,e))
    d={(v,None):0};q=[(0,v,())]
    while q:
        s,t,k=heappop(q);k=k or None
        if d[t,k]!=s:continue
        if t in halt:continue
        X=portals[k] if k else B
        for u,j in touch[t]:
            r=s+gap(X,portals[j])
            if r<d.get((u,j),10**12):
                d[u,j]=r;heappush(q,(r,u,j))
    return d

def lower(portals):
    whole=set(portals)
    S0=point(S);G0=point(G)
    obs={x for k in K for x in k}
    unknown=routes(portals,whole-set(K),103,S0,obs)
    assert all(t!=132 for t,k in unknown)
    backward=[routes(portals,whole-{closed},132,G0) for closed in K]
    def residual(t,B):
        def goal(d,endi,b):
            return min(s+gap(portals[k] if k else G0,b) for (i,k),s in d.items() if i==endi)
        # Direction of all portal-lower transitions is symmetric.
        return [goal(d,t,B)+goal(d,103,S0) for d in backward]
    known=residual(103,S0)
    opts=[]
    for (t,k),s in unknown.items():
        if t not in obs:continue
        v=residual(t,portals[k])
        opts.append((s+max(v),t,k,s,v))
    return dict(known_mm=known,local_mm=min(opts)[0],witnesses=sorted(opts))


def main():
    A,lo,n=bulk()
    cnt,gate=adjacent(A,lo)
    drawn={tuple(sorted(map(int,ab))) for ab in re.findall(r'(\d+)\s*--\s*(\d+)\s*\[label=\d+\]',
             (base/"vis"/"world.dot").read_text()) if all(int(x) in I for x in ab)}
    G=set(cnt)
    print(json.dumps(dict(voxels=n,edges=len(G),graph_edges=len(drawn),
       added=[list(x) for x in sorted(G-drawn)],missing=[list(x) for x in sorted(drawn-G)],
       gates={str(k):[x.tolist() for x in gate[k]] for k in K}, relaxed=lower(gate),
       distances=[reach(G,d) for d in ((),(K[0],),(K[1],),K)],
       counts={str(k):v for k,v in sorted(cnt.items())}),sort_keys=True))
if __name__=="__main__":main()
