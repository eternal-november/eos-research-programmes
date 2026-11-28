"""Native leaf target recurrence with explicit kinematic aperture coupling."""
from itertools import product
import json
from pathlib import Path
import sys
from core import Event, Row, Use, admitted

T=24
opts=tuple(product((0,1),repeat=2))

def layout(left,right):
    # All 2² "which permitted maintenance pulse actually happens" patterns.
    adm={}
    aligned={}
    separate={}
    for k,m in opts:
        mask=(k,m)
        direct=max(sum(v) for l in left[:1+k] for r in right[:1+m] for v in zip(l,r))
        pl=tuple(max(z) for z in zip(*left[:1+k]))
        pr=tuple(max(z) for z in zip(*right[:1+m]))
        align=max(l+r for l,r in zip(pl,pr))
        old=max(pl)+max(pr)
        assert direct==align<=old
        adm[mask]=direct
        aligned[mask]=(pl,pr)
        separate[mask]=old
    return adm,aligned,separate

def core_select(profiles,cap):
    # One acquired horizon, simultaneous cuts only. Leaf scope weights
    # share the aperture-indexed meter; different t are separate meters.
    options={}
    for mask,(l,r) in profiles.items():
        options[mask]=(Event(0,0,uses=tuple(Use(("aperture",t),v,cap,0) for t,v in enumerate(l))),
                       Event(0,1,uses=tuple(Use(("aperture",t),v,cap,0) for t,v in enumerate(r)),
                             paid=("complete-traversal",)))
    z=Row(((0,"door","qualified-profile"),),frozenset(),(),options)
    return next(iter(admitted([z],"door",0,{"complete-traversal":0},opts).values()))

def best(allowed):return max(map(sum,allowed),default=-1)

def main():
    observed={}
    for line in Path(sys.argv[1]).read_text().splitlines():
        a,b,c,*v=map(int,line.split())
        assert len(v)==T and all(0<=x<=1024 for x in v)
        assert (a,b,c) not in observed
        observed[a,b,c]=tuple(v)
    assert len(observed)==203
    def pair(x):return (observed[x[0],0,0],observed[x])
    ac=[k for k in observed if k[1]]
    cases=core_calls=advantage=unsafe_once=0
    for i,(a,b) in enumerate(product(ac,repeat=2)):
        menu,aligned,separate=layout(pair(a),pair(b))
        values=sorted({x+e for x in (*menu.values(),*separate.values()) for e in (-1,0) if x+e>=0})
        for S in values:
            x=tuple(k for k in opts if menu[k]<=S)
            y=tuple(k for k in opts if separate[k]<=S)
            assert set(y)<=set(x)
            if i%211==0:
                assert core_select(aligned,S)==x
                core_calls+=1
            if best(x)>best(y):advantage+=1
            if (1,0) in x and (0,1) in x and (1,1) not in x:unsafe_once+=1
            cases+=1

    def case(L,R,cap):
        m,p,s=layout(pair(L),pair(R))
        allowed=tuple(k for k in opts if m[k]<=cap)
        assert core_select(p,cap)==allowed
        return dict(peak=m[1,1],sum_of_peaks=s[1,1],ok=[list(x) for x in allowed],
                    L_peak=max(p[1,1][0]),R_peak=max(p[1,1][1]))
    stagger=case((0,9,4),(2,1,3),44)
    old=case((0,9,4),(2,5,3),36)
    fresh=case((0,9,4),(2,11,3),36)
    same_cut=case((6,1,4),(6,1,4),162)
    assert (stagger["peak"],stagger["sum_of_peaks"])==(44,76) and [1,1] in stagger["ok"]
    assert old["L_peak"]==fresh["L_peak"]==32 and old["R_peak"]==fresh["R_peak"]==20
    assert (old["peak"],fresh["peak"])==(36,52)
    assert [1,1] in old["ok"] and [1,1] not in fresh["ok"]
    assert same_cut["peak"]==316 and same_cut["ok"]==[[0,0],[0,1],[1,0]]
    print(json.dumps(dict(source_profiles=len(observed),pairs=len(ac)**2,cases=cases,
                          core_calls=core_calls+4,greater_allowance=advantage,
                          noncomposing_individual_allowance=unsafe_once,
                          stagger=stagger,replacement=[old,fresh],same_cut=same_cut),sort_keys=True))
if __name__=="__main__":main()
