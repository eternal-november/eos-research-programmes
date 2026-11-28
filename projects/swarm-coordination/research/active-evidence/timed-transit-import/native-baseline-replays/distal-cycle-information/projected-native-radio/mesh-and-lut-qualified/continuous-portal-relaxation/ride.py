"""Find and independently verify selected motion witnesses, not a navigation lower bound."""
import json, sys, struct
from pathlib import Path
from heapq import heappush,heappop
from itertools import product
from fractions import Fraction as F
from math import sqrt,floor
import survey
from decimal import Decimal as D
from hashlib import sha256

data=survey.P
coords={int(n):tuple(v) for n,v in json.loads(Path(sys.argv[2]).read_text()).items()}
cases=[
 (103,104,{103,104}),
 (103,105,{103,105}),
 (105,107,{105,106,107}),
 (107,118,{107,118}),
 (104,117,{104,108,116,117}),
 (118,132,{118,115,114,122,128,130,132}),
 (117,132,{117,119,156,157,121,124,132}),
]
closures={
 (118,132):((D("317.5"),D("-237.55"),D("29.5")),(D("333.5"),D("-237.45"),D("39.5"))),
 (117,132):((D("312.45"),D("-257.5"),D("9.5")),(D("312.55"),D("-242.5"),D("20.5"))),
}
coords[132]=(350,-300,13)

def read_lut(tiles):
    b=(data/"cave_circuit_01.dat").read_bytes()
    assert len(b)==30667668
    n=struct.unpack_from("<Q",b)[0]
    rows={}
    for x,y,z,v in struct.iter_unpack("<iiiQ",memoryview(b)[8:8+20*n]):
        if v in tiles:rows[x,y,z]=v
        else:rows.pop((x,y,z),None)
    return rows

def explored(m,vertices,a,b):
    def goal(x):
        return sum(abs(x[i]-b[i]) for i in range(3))
    A=[(goal(a),0,a)]
    dist={a:0};prev={a:None}
    assert a in vertices and b in vertices and m.clear(a,a) and m.clear(b,b)
    while A:
        _,g,p=heappop(A)
        if dist[p]!=g:continue
        if p==b:
            r=[p]
            while prev[p] is not None:
                p=prev[p];r.append(p)
            return r[::-1],len(dist)
        if len(dist)>45000:return None,len(dist)
        for dim,sign in product(range(3),(-1,1)):
            q=tuple(x+(sign if i==dim else 0) for i,x in enumerate(p))
            if q not in vertices or dist.get(q,10**7)<=g+1:continue
            if not m.clear(*sorted((p,q))):continue
            prev[q]=p
            dist[q]=g+1
            heappush(A,(g+1+goal(q),g+1,q))
    return None,len(dist)

def compress(path):
    def diff(a,b):return tuple(y-x for x,y in zip(a,b))
    return [path[0]]+[path[i] for i in range(1,len(path)-1)
              if diff(path[i-1],path[i])!=diff(path[i],path[i+1])]+[path[-1]]

def within(u,v,voxels):
    # For integer endpoints each contributing voxel change is at half
    # an integer on some changing axis. A sample in every resulting
    # open parameter interval proves the segment stays in the union of
    # closed authorized unit cubes; continuity covers its endpoints.
    cuts={F(0),F(1)}
    for i in range(3):
       if u[i]==v[i]:continue
       for p in range(min(u[i],v[i]),max(u[i],v[i])):
          cuts.add(F(2*p+1-2*u[i],2*(v[i]-u[i])))
    order=sorted(cuts)
    for a,b in zip(order,order[1:]):
       q=(a+b)/2
       c=tuple(floor(u[i]+(v[i]-u[i])*q+F(1,2)) for i in range(3))
       if c not in voxels:return False
    return True

def shortest_verified_chart(m,way,voxels):
    n=len(way);d={0:0};pred={}
    for i in range(n):
        for j in range(i+1,min(i+9,n)):
            if not within(way[i],way[j],voxels) or not m.clear(*sorted((way[i],way[j]))):continue
            length=sqrt(sum((a-b)**2 for a,b in zip(way[i],way[j])))
            if d[i]+length<d.get(j,float("inf")):
                d[j]=d[i]+length;pred[j]=i
    a=n-1; q=[way[a]]
    while a:
        a=pred[a]
        q.append(way[a])
    return d[n-1],q[::-1]

def main():
    survey.verify()
    T,p,tt,by_tile=survey.source()
    m=survey.Map(T,[])
    lookup=read_lut(set().union(*(a[2] for a in cases)))
    out={}
    for a,b,tiles in cases:
        m.fences=[closures[a,b]] if (a,b) in closures else []
        m.clear.cache_clear()
        keys={p for p,v in lookup.items() if v in tiles}
        path,state=explored(m,keys,coords[a],coords[b])
        if path:
            way=compress(path)
            eps=min(m.certificate(a,b) for a,b in zip(way,way[1:]))
            assert eps>0
            used=[lookup[p] for p in path]
            assert used[0]==a and used[-1]==b
            changes=[used[0]]+[x for p,x in zip(used,used[1:]) if p!=x]
            for u,v in zip(way,way[1:]):assert within(u,v,keys)
            length,q=shortest_verified_chart(m,way,keys)
            confirm=min(m.certificate(u,v) for u,v in zip(q,q[1:]))
            assert length<=len(path)-1 and confirm>0
            result=[len(path)-1,len(way)-1,round(eps,8),changes,round(length,6),round(confirm,8),q]
        else:result=None
        out[f"{a}/{b}"]=[state,result]
        print(a,b,state,None if result is None else result[:4],file=sys.stderr,flush=True)
    roundtrips={}
    for label,leg_keys,closed in (
      ("117-119-closed",("103/105","105/107","107/118","118/132"),(118,132)),
      ("115-118-closed",("103/104","104/117","117/132"),(117,132))):
        if not all(out[k][1] is not None for k in leg_keys):
            continue
        m.fences=[closures[closed]]
        prefix=[]
        for k in leg_keys:
            Q=out[k][1][-1]
            assert not prefix or Q[0]==prefix[-1]
            prefix+=Q if not prefix else Q[1:]
        assert prefix[0]==coords[103] and prefix[-1]==coords[132]
        global_margin=min(m.certificate(u,v) for u,v in zip(prefix,prefix[1:]))
        assert global_margin>0
        two_way=2*sum(sqrt(sum((a-b)**2 for a,b in zip(u,v))) for u,v in zip(prefix,prefix[1:]))
        roundtrips[label]=[round(two_way,6),round(global_margin,8),len(prefix)-1]
    assert len(roundtrips)==2
    print(json.dumps(dict(legs=out,roundtrips=roundtrips),sort_keys=True))
if __name__=="__main__":main()
