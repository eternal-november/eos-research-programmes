"""Same aperture action with unknown affine calibration and a true pre-use cut."""
import json, sys
from itertools import combinations,product
from fractions import Fraction as F
from pathlib import Path
from core import Event, Row, admitted

def load(path):
    M={}
    for line in Path(path).read_text().splitlines():
        a,b,c,*p=line.split()
        M[tuple(map(int,(a,b,c)))]=(0,)+tuple(int(x.split(":")[0]) for x in p)
    return [M[x] for x in ((3,0,0),(3,3,3),(5,0,0),(5,5,2))]

def pair_overlap(a,b,times,e=F(7,4)):
    d={t:a[t]-b[t] for t in times}
    if len(times)<=1:return (-(d[times[0]]) if times else 0,0)
    lo=None;hi=None
    for l,r in combinations(times,2):
        c=F(d[l]-d[r],r-l)
        w=4*e/(r-l)
        lo=c-w if lo is None else max(lo,c-w)
        hi=c+w if hi is None else min(hi,c+w)
        if lo>hi:return None
    slope=lo
    vals=[d[t]+slope*t for t in times]
    intercept=-2*e-min(vals)
    assert all(abs(d[t]+intercept+slope*t)<=2*e for t in times)
    return intercept,slope

def audit_subsets(H):
    groups={"action":[0,1,1,1],"profile":[0,0,1,1]}
    result={}
    for name,labels in groups.items():
        pairs=[(a,b) for a,b in combinations(range(4),2) if labels[a]!=labels[b]]
        for lower in (0,1):
            for upper in (9,10):
                count=0;best=None
                for n in range(1,upper-lower+2):
                    for t in combinations(range(lower,upper+1),n):
                        ok=all(pair_overlap(H[a],H[b],t) is None for a,b in pairs)
                        count+=int(ok)
                        if ok and best is None:best=t
                result[f"{name}/{lower}/{upper}"]=[count,best]
    assert result["profile/1/10"]==[0,None]
    assert result["profile/0/10"][1]==(0,2,6,10)
    assert result["action/1/9"]==[0,None] and result["action/1/10"][1]==(1,7,10)
    return result

def model_admit(H):
    t=(1,7,10);w=(3,-9,6)
    assert sum(w)==sum(a*b for a,b in zip(w,t))==0
    raw=[sum(v*row[j] for v,j in zip(w,t)) for row in H]
    assert raw==[-6,-90,-78,-78]
    # Quarter-scaled numeric contrast. The native replay provides the
    # true deficits, not the generated sensor drift or transport.
    seen={}
    for i,a in enumerate(H):
        for noise4 in product(range(-7,8),repeat=3):
            y=[4*a[j]+17-13*j+e for j,e in zip(t,noise4)]
            k=sum(b*c for b,c in zip(w,y))
            holds=tuple(i for i,c in enumerate(raw) if abs(k-4*c)<=sum(map(abs,w))*7)
            assert i in holds and len({h!=0 for h in holds})==1
            seen[k]=holds
    results={}
    for delay in (0,1,2):
        total=offered=0
        for v,holds in seen.items():
            indices=holds if delay==0 else range(4)
            r=[Row(((10+delay,"gate",v),),frozenset({"safe"} if i else ()),(),{
                 "maintain":(Event(10,0,paid=("old",)),),
                 "issue":(Event(10,0,need=frozenset({"safe"}),paid=("old",)),)})
                for i in indices]
            a=next(iter(admitted(r,"gate",10,{"old":10},("maintain","issue")).values()))
            direct=delay==0 and 0 not in holds
            assert a==(("maintain","issue") if direct else ("maintain",))
            offered+=int(direct)
            total+=1
        results[delay]=[total,offered]
    assert results[0][1]>0 and results[1][1]==results[2][1]==0
    assert pair_overlap(H[0],H[2],t,F(2)) is not None
    return results

def main():
    H=load(sys.argv[1])
    proof={}
    for key,(a,b,times,delta) in {
      "late-action":(0,3,tuple(range(10)),(F(7,2),F(3))),
      "full-profile-postcut":(1,3,tuple(range(1,11)),(F(8),F(-1)))}.items():
        d,s=delta
        assert pair_overlap(H[a],H[b],times) is not None
        assert all(abs(H[a][t]-H[b][t]+d+s*t)<=F(7,2) for t in times)
        proof[key]=[a,b,times,[str(d),str(s)]]
    assert (H[0][2],H[1][2],H[2][2],H[3][2])==(6,6,14,14)
    # With independently unknown slopes per possible world in [-rho,rho],
    # the two values after normalizing the baseline can approach by 4 rho.
    # Gap 8, noise-overlap diameter 7, hence strict rho<1/4.
    assert F(8-7,4)==F(1,4)
    print(json.dumps(dict(subsets=audit_subsets(H),witnesses=proof,
                          timed_admission=model_admit(H)),sort_keys=True))
if __name__=="__main__":main()
