#!/usr/bin/env python3
from decimal import Decimal as D
from fractions import Fraction as F
from hashlib import sha1
import importlib.util
from itertools import pairwise
import json
from pathlib import Path
import sys

PINS={
 "egress.py":"d0268cca19bda41b4efa7c3bee019b1b9c0e54c5",
 "near.json":"5f640ab029a4cdbd080424cc4af182aa1e54261a",
 "far_short.json":"f53905b1bd1d7d42c460a262182d99384dbce88a",
}
ANCHOR=(100,100,6)
PROBE=(100,60,8)
END_R=(100,D("50.015625"),8)
GOAL=(0,0,6)

def verified(p,key):
    data=(p/key).read_bytes()
    assert sha1(f"blob {len(data)}\0".encode()+data).hexdigest()==PINS[key],key
    return data

def load(g,p):
    verified(g,"egress.py")
    s=importlib.util.spec_from_file_location("source_cave",g/"egress.py")
    v=importlib.util.module_from_spec(s)
    sys.modules["source_cave"]=v;s.loader.exec_module(v)
    v.verify();v.MODELS[18]="straight3"
    t,f,_=v.load_scene()
    near=list(map(tuple,json.loads(verified(p,"near.json"))))
    far=list(map(tuple,json.loads(verified(p,"far_short.json"))))
    return v,t,f,near,far

def exact_cross(a,b,box):
    # Positive-interior witness, not just bounding box overlap.
    enter,exit=F(0),F(1)
    for x,y,l,h in zip(a,b,*box):
        l,h=F(l)+F(1,1000),F(h)-F(1,1000)
        if x==y:
            if not l<=x<=h:return False
        else:
            lo,hi=sorted(((l-x)/(y-x),(h-x)/(y-x)))
            enter,exit=max(enter,lo),min(exit,hi)
    return enter<exit

def time(a,b):
    ell=sum(D(x-y)**2 for x,y in zip(a,b)).sqrt()
    return 2*ell.sqrt() if ell<=9 else ell/3+3

def chord(m,p):
    best=[D(0)]+[D("Infinity")]*(len(p)-1)
    parent={}
    for j in range(1,len(p)):
        for i in range(j):
            val=best[i]+time(p[i],p[j])
            if val>=best[j] or not m.clear(*sorted((p[i],p[j]))):continue
            best[j]=val
            parent[j]=i
    inds=[len(p)-1]
    while inds[-1]:
        j=inds[-1]
        assert j in parent,("blocked library",j,p[j])
        inds.append(parent[j])
    candidate=[p[j] for j in reversed(inds)]
    m0=min(m.certificate(a,b) for a,b in pairwise(candidate))
    assert m0>0 and candidate[0]==ANCHOR and candidate[-1]==GOAL
    return candidate,best[-1],m0

def solve(g,p):
    e,t,f,n,s=load(g,p)
    def body(pos):
        return tuple(D(z)-D(".30") for z in pos),tuple(D(z)+D(".30") for z in pos)
    poses=[(100,-25,6),(100,75,8),(75,100,6),PROBE,END_R]
    rf=e.Map(t,f+[body(z) for z in poses if z!=PROBE])
    assert rf.certificate(PROBE,(100,65,8),D(".001"))>0
    # Open-line observation under B, first intersection with A at y=62.45.
    assert exact_cross(PROBE,(100,65,8),e.GATE_A)
    assert not exact_cross(PROBE,(100,65,8),e.GATE_B)
    m0=e.Map(t,f+[body(z) for z in poses]+[e.GATE_A])
    m1=e.Map(t,f+[body(z) for z in poses]+[e.GATE_B])
    pn=[ANCHOR,(76,100,6),(76,99,6),(75,99,6)]+n[1:]
    assert s[:2]==[(100,75,8),(100,73,8)]
    ps=[ANCHOR,(101,83,6),(102,82,7),(102,75,8),(102,73,8)]+s[1:]
    out={}
    for M,path,code in [(m0,pn,256),(m1,ps,128)]:
        c,d,gap=chord(M,path)
        out[code]=dict(path=c,travel=round(d,8),margin=round(gap,8))
    assert any(exact_cross(a,b,e.GATE_B) for a,b in pairwise(out[256]["path"]))
    assert any(exact_cross(a,b,e.GATE_A) for a,b in pairwise(out[128]["path"]))
    # Return the constructed terrain-indexed model and certified route library.
    # The controller will only choose by returned code, not by this table index
    # as an observation. This two-state support assumes exactly one closed gate.
    return out,dict(blockedA=256,blockedB=128,mesh_triangles=len(t))

if __name__=="__main__":
    data,model=solve(Path(sys.argv[1]),Path(sys.argv[2]))
    print(json.dumps(dict(model=model,paths={k:{**v,"travel":str(v["travel"])}
                                            for k,v in data.items()}),sort_keys=True))
