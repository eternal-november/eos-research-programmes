"""Prospective sensors for the single split aperture fibre."""
import json, sys
from itertools import product,combinations
from pathlib import Path
from core import Event, Row, admitted

def model(path):
    raw={}
    for line in Path(path).read_text().splitlines():
        k,t,d,*tokens=line.split()
        v=[tuple(map(int,x.split(":"))) for x in tokens]
        assert len(v)==24
        raw[tuple(map(int,(k,t,d)))]=v
    A=[raw[3,0,0],raw[3,3,3]]
    B=[raw[5,0,0],raw[5,5,2]]
    return A,B

def span(A,B,times):
    return min(max(a[t][0]-b[t][0] for t in times)-min(a[t][0]-b[t][0] for t in times)
               for a,b in product(A,B))

def collide(a,b,times,e4):
    # Integers are quarter-units, e4 = 4 * per-read error. Normalize
    # overlapping first reading to zero using the unbounded common shift.
    ds=[4*(a[t][0]-b[t][0]) for t in times]
    if max(ds)-min(ds)>4*e4:return None
    dz=-2*e4-min(ds)
    X=[4*a[t][0]+dz for t in times];Y=[4*b[t][0] for t in times]
    m=[max(v,u)-e4 for v,u in zip(X,Y)]
    assert all(abs(x-y)<=e4 for arr in (X,Y) for x,y in zip(arr,m))
    shift=m[0]
    return tuple(x-shift for x in m)

def feasible(y,a,times,e4):
    implied=[v-4*a[t][0] for v,t in zip(y,times)]
    return max(implied)-min(implied)<=2*e4

def verify_bounded_reads(A,B):
    H=A+B
    counts={}
    for purpose,ts in (("one-action",(0,3)),("profile",(0,1,4)),("late-profile",(2,7))):
        seen={}
        for i,a in enumerate(H):
            for eps in product(range(-7,8),repeat=len(ts)):
                raw=[4*a[t][0]+e for t,e in zip(ts,eps)]
                y=tuple(v-raw[0] for v in raw)
                group=tuple(j for j,b in enumerate(H) if feasible(y,b,ts,7))
                assert i in group
                seen[y]=group
                assert len({i!=0 for i in group})==1 if purpose=="one-action" else len({i>=2 for i in group})==1
        if purpose=="one-action":
            for token, group in seen.items():
                rows=tuple(Row(((4,"gate",token),),frozenset({"permit"} if i else ()),(),{
                    "refuse":(Event(10,0,paid=("old",)),),
                    "issue":(Event(10,0,need=frozenset({"permit"}),paid=("old",)),)})
                    for i in group)
                answer=next(iter(admitted(rows,"gate",10,{"old":10},("refuse","issue")).values()))
                assert answer==(("refuse","issue") if 0 not in group else ("refuse",))
        counts[purpose]=len(seen)
    return counts

def verify_admission(A,B):
    # Scoped to this old fibre and the singleton late request (0,11,4).
    # Recompute the actual aperture outcome under post-cut permit/refusal.
    # At the old cut a safety budget of 36 copes with both left histories
    # if this late right pulse is not admitted.
    case=Path(sys.argv[1]).read_text().splitlines()
    data={}
    for line in case:
        k,t,d,*tokens=line.split()
        data[tuple(map(int,(k,t,d)))]=[int(x.split(":")[0]) for x in tokens]
    Q=[data[0,0,0],data[0,11,4]]
    sets=(tuple((a,0) for a in A),tuple((b,1) for b in B))
    tally={}
    for n in (0,2,3,4,5,8):
        for kind in ("none","categorical","calibrated","biased"):
            if n==0 and kind!="none":continue
            if n>0 and kind=="none":continue
            if kind=="biased":times=(0,3) if n==5 else (3,7) if n==8 else None
            rows=[]
            for a,g in sum(sets,()):
                if kind=="categorical": key=a[n-1][1]
                elif kind=="calibrated": key=a[n-1][0]
                elif kind=="biased":
                    if times is None:continue
                    # The bound is e=7/4. This finite sensor control uses
                    # the exact shape only; collisions under all bounded
                    # errors are handled beside it, not by assuming zero noise.
                    key=tuple(a[t][0]-a[times[0]][0] for t in times)
                else:key=None
                aper=max(a[t][0]+r[t] for t in range(24) for r in Q)
                assert aper<=36 if g else aper<=38
                assert max(a[t][0]+Q[0][t] for t in range(24))<=36
                assert (aper<=36)==(a!=A[0])
                if kind=="biased":assert all(collide(a,b,times,7) is None for b in (([A[0]] if aper<=36 else [A[1],*B])))
                rows.append(Row(((n,"gate",key),),frozenset({"allow-late"} if aper<=36 else ()),(),
                    {"keep":(Event(10,0,paid=("old",)),),
                     "add":(Event(10,0,need=frozenset({"allow-late"}),paid=("old",)),)}))
            if not rows:continue
            views=admitted(rows,"gate",10,{"old":10},("keep","add"))
            direct={}
            for row in rows:
                key=((n,row.receipts[0][2]),)
                direct[key]=direct.get(key,True) and "allow-late" in row.facts
            assert all(actions==(("keep","add") if direct[k] else ("keep",)) for k,actions in views.items())
            count=sum(len(v)==2 for v in views.values())
            tally[f"{n}/{kind}"]=[len(views),count]
    assert tally["0/none"]==[1,0]
    assert tally["2/categorical"]==[1,0] and tally["3/categorical"]==[2,1]
    assert tally["4/categorical"]==[2,1]
    # At t3 the mixed OPEN group contains one safe and one unsafe
    # history. At t4 the native mode alone separates the action labels.
    assert A[0][2][1]==A[1][2][1] and all(B[i][2][1]!=A[0][2][1] for i in (0,1))
    assert all(h[3][1]!=A[0][3][1] for h in [A[1],*B])
    H=[A[0]]
    L=[A[1],*B]
    assert max(span(H,L,t) for t in combinations(range(5),2))==10
    assert span(H,L,(0,3))==10
    assert not any(collide(a,b,(0,3),9) is not None for a,b in product(H,L))
    assert any(collide(a,b,(0,3),10) is not None for a,b in product(H,L))
    return tally

def main():
    A,B=model(sys.argv[1])
    exact={}
    for t in range(10):
        dv=min(abs(a[t][0]-b[t][0]) for a,b in product(A,B))
        categorical=all(a[t][1]!=b[t][1] for a,b in product(A,B))
        exact[t+1]=(dv,categorical)
    assert exact[1]==(4,False) and exact[2]==(8,False) and exact[3]==(8,True)
    assert all(v[0]==0 for k,v in exact.items() if k>=5)
    ladder={}
    for dead in range(2,11):
        for n in range(1,min(dead,3)+1):
            best=max(((span(A,B,ts),tuple(-t for t in ts))
                      for ts in combinations(range(dead),n)))
            ladder[f"{dead}/{n}"]=(best[0],[-t+1 for t in best[1]])
    assert ladder["5/2"]==(6,[2,5]) and ladder["5/3"]==(8,[1,2,5])
    assert ladder["8/2"]==(8,[3,8])
    no_two=[]
    for times in combinations(range(5),2):
        pool=[collide(a,b,times,7) for a,b in product(A,B)]
        proof=next(y for y in pool if y is not None)
        assert proof[0]==0
        no_two.append(([t+1 for t in times],proof))
    assert all(collide(a,b,(0,1,4),7) is None for a,b in product(A,B))
    assert any(collide(a,b,(0,1,4),8) is not None for a,b in product(A,B))
    print(json.dumps(dict(exact=exact,ladder=ladder,gap5=no_two,admission=verify_admission(A,B),bounded=verify_bounded_reads(A,B)),sort_keys=True))
if __name__=="__main__":main()
