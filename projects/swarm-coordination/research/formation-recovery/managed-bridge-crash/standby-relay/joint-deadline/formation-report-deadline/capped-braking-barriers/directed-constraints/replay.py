#!/usr/bin/env python3
"""Rational tests of shortest-path braking constraints."""
import json
import random
from fractions import Fraction as Q
from itertools import product


def distances(n, edges):
    d = [[None]*n for _ in range(n)]
    for i in range(n):
        d[i][i] = Q(0)
    for i,j,w in edges:
        assert d[i][j] is None
        d[i][j] = w
    for k in range(n):
        for i,j in product(range(n), repeat=2):
            if d[i][k] is not None and d[k][j] is not None:
                s = d[i][k]+d[k][j]
                if d[i][j] is None or d[i][j]>s:
                    d[i][j]=s
    return d


def independent_distances(n, edges):
    out = []
    for i in range(n):
        d = [None]*n
        d[i] = Q(0)
        for _ in range(n-1):
            e = d.copy()
            for j,k,w in edges:
                if d[j] is not None and (e[k] is None or d[j]+w<e[k]):
                    e[k] = d[j]+w
            d = e
        out.append(d)
    return out


def points(d,x,v,h):
    for i,j in product(range(len(x)),repeat=2):
        if d[i][j] is not None:
            w=max(Q(0),v[j]-v[i])
            yield i,j,w,d[i][j]-(x[j]-x[i])-w*w/(2*h)


def witness(d,x,v,ap,am,W):
    n=len(x)
    ps=list(points(d,x,v,ap+am))
    if any(s<0 for _,_,_,s in ps):
        return None
    us=[Q(0)]*n
    for i,j,w,s in ps:
        if s==0 and w>0:
            assert us[i]>=0 and us[j]<=0
            us[i],us[j]=ap,-am
    if min(v)<max(v):
        for i in range(n):
            if v[i]==max(v):
                assert us[i]<=0
                us[i]=-am
            if v[i]==min(v):
                assert us[i]>=0
                us[i]=ap
    assert all(-am<=u<=ap and (s>0 or u>=0) and (s<W or u<=0) for s,u in zip(v,us))
    assert all(s>0 or -w-w*(us[j]-us[i])/(ap+am)>=0 for i,j,w,s in ps)
    return us


def replay():
    r=random.Random(513)
    feasible=failed=nonedge=mixed=negative=asym=disconnected=0
    for trial in range(2000):
        n=r.randrange(3,10)
        x=[Q(r.randrange(-11,12),2) for _ in range(n)]
        v=[Q(r.randrange(9),2) for _ in range(n)]
        ap,am,W=Q(r.randrange(1,4)),Q(r.randrange(1,4)),Q(4)
        edges=[]
        for i,j in product(range(n),repeat=2):
            if i!=j and r.random()<0.32:
                w=max(0,v[j]-v[i])
                margin=w*w/(2*(ap+am))+Q(r.choice([0,0,1,2]),4)
                if trial%3==0:
                    margin+=Q(4)
                edges.append((i,j,x[j]-x[i]+margin))
        d=distances(n,edges)
        assert d==independent_distances(n,edges)
        eu=witness(d,x,v,ap,am,W)
        if eu is None:
            assert all(w-(x[j]-x[i])>=max(0,v[j]-v[i])**2/(2*(ap+am)) for i,j,w in edges)
            failed+=1
            orig={(i,j) for i,j,_ in edges}
            nonedge+=any(s<0 and (i,j) not in orig for i,j,w,s in points(d,x,v,ap+am))
        else:
            feasible+=1
            mixed+=v not in (sorted(v),sorted(v,reverse=True))
            negative+=any(w<0 for _,_,w in edges)
            asym+=ap!=am
            disconnected+=any(y is None for row in d for y in row)
    # Endpoints need room 1 despite each edge individually needing only 1/4.
    d=distances(3,[(0,1,Q(1,4)),(1,2,Q(1,4))])
    assert witness(d,[Q(0)]*3,list(map(Q,[0,1,2])),Q(1),Q(1),Q(2)) is None
    # Heterogeneous actuators: all three span tests pass, but the middle robot
    # is forced in opposite directions by the two tight neighbors.
    aa=list(map(Q,[9,1,1]))
    vv=list(map(Q,[3,2,0]))
    zz=[Q(0),Q(1,20),Q(21,20)]
    assert all(zz[j]-zz[i]>=(vv[i]-vv[j])**2/(2*(aa[i]+aa[j]))
               for i,j in ((0,1),(1,2),(0,2)))
    assert zz[1]-zz[0]==(vv[0]-vv[1])**2/(2*(aa[0]+aa[1]))
    assert zz[2]-zz[1]==(vv[1]-vv[2])**2/(2*(aa[1]+aa[2]))
    assert feasible>0 and failed>0 and nonedge>0 and mixed>0 and negative>0 and asym>0 and disconnected>0
    return dict(shortest_path_crosschecks=2000,feasible_with_tangent=feasible,
                edge_tests_pass_but_closure_fails=failed,failed_at_absent_edge=nonedge,
                feasible_mixed_velocities=mixed,feasible_negative_edge_weight=negative,
                feasible_asymmetric_common_accelerations=asym,
                feasible_unreachable_pair=disconnected,
                heterogeneous_middle_forced_both_signs=True)


if __name__=='__main__':
    print(json.dumps(replay(),indent=2))
