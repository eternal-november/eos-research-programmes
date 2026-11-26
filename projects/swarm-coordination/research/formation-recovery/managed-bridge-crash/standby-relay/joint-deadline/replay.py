#!/usr/bin/env python3
"""Exact geometry check. Pass the pinned, unmodified upstream scenario.py."""
import ast
import hashlib
import itertools as it
import json
import math
import sys
from fractions import Fraction as Q
from pathlib import Path


def add(a, b):
    return tuple(x+y for x,y in zip(a,b,strict=True))


def sub(a, b):
    return add(a, scale(-1,b))


def scale(t, a):
    return tuple(t*x for x in a)


def dot(a, b):
    return sum(x*y for x,y in zip(a,b,strict=True))


def d2(a, b):
    z = sub(a,b)
    return dot(z,z)


def pair_radius2(pts):
    return max(d2(a,b) for a,b in it.combinations(pts,2))/4


def circumcircle(pts):
    a,b,c = pts
    u,v = sub(b,a),sub(c,a)
    U,W,V = dot(u,u),dot(u,v),dot(v,v)
    det = U*V-W**2
    assert det>0
    p,q = V*(U-W)/(2*det),U*(V-W)/(2*det)
    x = add(a,add(scale(p,u),scale(q,v)))
    return x, d2(x,a), (1-p-q,p,q)


def enumerated_radius2(pts):
    candidates=list(pts)
    candidates.extend(scale(Q(1,2),add(a,b)) for a,b in it.combinations(pts,2))
    candidates.append(circumcircle(pts)[0])
    return min(max(d2(x,p) for p in pts) for x in candidates)


def travel(T,a,V):
    t=min(T/2,V/a)
    return a*t*(T-t)


def main(path):
    raw=Path(path).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\x00'+raw).hexdigest() == '193319e4aba9814f8d6989409700ab3618d245d9'
    s=raw.decode()
    f=next(n for n in ast.parse(s).body if isinstance(n,ast.FunctionDef) and n.name=='_default_3d_data')
    n=next(e.value.args[0] for e in f.body if isinstance(e,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='initial' for t in e.targets))
    rows=tuple(tuple(Q(ast.get_source_segment(s,x)) for x in p.elts) for p in n.elts[:5])
    triples=[]
    for ids in it.combinations(range(len(rows)),3):
        pts=tuple(rows[i] for i in ids)
        ds=sorted(d2(a,b) for a,b in it.combinations(pts,2))
        if ds[0]+ds[1]>ds[2]:
            triples.append(ids)
    chosen=triples[0]
    assert chosen==(1,2,3)
    ps=tuple(rows[i] for i in chosen)
    center,r2,weights=circumcircle(ps)
    assert sum(weights)==1 and min(weights)>0
    assert tuple(sum(w*p[k] for w,p in zip(weights,ps,strict=True)) for k in range(3))==center
    assert all(d2(center,p)==r2 for p in ps)
    assert r2==enumerated_radius2(ps)
    # Verify the weighted identity off center, including outside the source plane.
    for x in it.product(range(-2,3),repeat=3):
        assert sum(w*d2(x,p) for w,p in zip(weights,ps,strict=True))==r2+d2(x,center)
    assert all(d2(ps[1],p)<=Q('1.65')**2 for p in ps)
    R,a,V=Q('.8'),Q(1),Q('.2')
    p2=pair_radius2(ps)
    # Find the first 0.01-grid time at which every pair passes but all three fail.
    candidates=[Q(k,100) for k in range(101)]
    times=[T for T in candidates if p2<=(R+travel(T,a,V))**2<r2]
    for T in candidates:
        d=travel(T,a,V)
        alternate=a*T*T/4 if T<=2*V/a else V*T-V*V/a
        assert d==alternate
    assert times
    T=times[0]
    after=next(T for T in candidates if r2<=(R+travel(T,a,V))**2)
    assert .4<float(T)<float(after)
    print(json.dumps(dict(indices=chosen,acute_triples=triples,center=[float(v) for v in center],
        support_weights=[str(w) for w in weights],diameter_over_two_sq=str(p2),enclosing_radius_sq=str(r2),
        all_pairs_min_time=(math.sqrt(float(p2))-float(R))/float(V)+float(V/a),
        joint_min_time=(math.sqrt(float(r2))-float(R))/float(V)+float(V/a),
        grid_pair_only_times=[str(T) for T in times],first_grid_joint_time=str(after),
        least_pair_only_displacement=str(travel(T,a,V)),weighted_identities=125),indent=2))


if __name__=='__main__':
    main(sys.argv[1])
