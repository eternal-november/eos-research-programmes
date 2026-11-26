"""A warm planar cut: passive acquisition can be too late even with ideal range."""
from itertools import combinations, product
from math import sqrt
import json
import numpy as np
from warm import (default_open_formation_scenario, simulate, SmoothBacksteppingController,
                  ControllerConfig, connected_components, witness, linear_integral,min_chord)

def actual_cut():
    s=default_open_formation_scenario(2)
    out=simulate(s,SmoothBacksteppingController(
        num_robots=s.num_robots,dimension=2,
        collision_distance=s.collision_distance,sensing_distance=s.sensing_distance,
        config=ControllerConfig(k1=1.,k2=.8,k3=2.5,max_virtual_speed=.8)))
    req=s.leave_requests[0]
    k=round(req.time/s.dt)
    ids=sorted(set(np.flatnonzero(out.active[k]))-{req.robot})
    E={tuple(sorted(e)) for e in out.edge_history[k] if req.robot not in e}
    C=sorted(map(sorted,connected_components(ids,E)),key=len)
    assert list(map(len,C))==[1,3]
    return s,req.robot,out.positions[k],out.velocities[k],C,E,ids

def reachable(u,A,V,T,t):
    return linear_integral(((0.,V),(A,u),(-A,A*T)),t)

def three_disks(points,radii):
    """Different two-dimensional comparator: all centers and circle intersections.
    If a point lies in all disks without a feasible center, their boundaries
    are either nested or have a feasible intersection vertex."""
    possible=list(points)
    for i,j in combinations(range(len(points)),2):
        p,q=points[i],points[j]
        r,s=radii[i],radii[j]
        d=float(np.linalg.norm(q-p))
        if d==0. or d>r+s or d<abs(r-s):continue
        x=(r*r-s*s+d*d)/(2*d)
        off=sqrt(max(r*r-x*x,0))
        e=(q-p)/d
        n=np.array([-e[1],e[0]])
        possible.extend((p+x*e+off*n,p+x*e-off*n))
    return any(all(np.linalg.norm(x-p)<=r+1e-9 for p,r in zip(points,radii))
               for x in possible)

def private_prefix(p,v,direction,sign,left,right,dead,R,d):
    # Common start, same velocities, three units of a smooth, hidden shift
    # for the entire remote component. No data are forwarded by the old node.
    def place(t):
        z=(t+3)/3
        q=p+t*v
        q[right,:]+=sign*.8*direction*(3*z*z-2*z*z*z)
        return q
    speed=max(np.linalg.norm(v[i]) for i in [left,dead,*right])+.8/2
    accel=.8*2/3
    assert speed<1 and accel<1
    prior_left_right=float("inf")
    clearance=float("inf")
    old_edge=0.
    edges={(min(left,dead),max(left,dead)),(min(right[0],dead),max(right[0],dead)),
           *[(a,b) for a,b in zip(right,right[1:])]}
    for before,after in zip(np.linspace(-3,0,301),np.linspace(-3,0,301)[1:]):
        a,b=place(before),place(after)
        for i,j in combinations(sorted([left,dead,*right]),2):
            # Relative acceleration is zero if both have the same shift;
            # else it is bounded by accel. Use the conservative bound on all.
            m=accel*(after-before)**2/8
            start,end=a[i]-a[j],b[i]-b[j]
            lo=min_chord(start,end)-m
            clearance=min(clearance,lo)
            if left in (i,j) and dead not in (i,j):prior_left_right=min(prior_left_right,lo)
            if (i,j) in edges:old_edge=max(old_edge,float(max(np.linalg.norm(start),np.linalg.norm(end)))+m)
    assert prior_left_right>R+.001 and clearance>d+.001 and old_edge<R-.001
    return clearance,prior_left_right,old_edge

def run():
    s,dead,p,v,C,E,ids=actual_cut()
    left=C[0][0]
    right=C[1]
    A=V=1.
    S=s.sensing_distance
    R=S-s.reconfiguration.edge_activation_margin
    center=p[left]
    a=p[right[0]]-center
    a/=np.linalg.norm(a)
    direction=np.array([-a[1],a[0]])
    T=1.11
    tau=.85
    reach={i:reachable(float(np.linalg.norm(v[i])),A,V,T,T) for i in ids}
    at_contact={i:reachable(float(np.linalg.norm(v[i])),A,V,T,tau) for i in ids}
    worlds=[]
    all_worlds=[]
    prefix=[]
    for sign in (-1,1):
        g=p.copy()
        g[right,:]+=sign*.8*direction
        assert np.array_equal(g[[left,dead]],p[[left,dead]])
        prefix.append(private_prefix(p,v,direction,sign,left,right,dead,S,s.collision_distance))
        nearest_time_delta=min(float(np.linalg.norm(g[i]-center))-S-at_contact[i]-at_contact[left]
                               for i in right)
        assert nearest_time_delta>.001
        # No successful right endpoint can come from omitted members.
        viable=[i for i in right if np.linalg.norm(g[i]-center)<=R+reach[i]+reach[left]+1e-9]
        assert viable==[right[0]]
        exact,T0,clear1,clear2,edge,ids0,_=witness(g,v,C,E,dead,A,V,R,s)
        # Initially both sides brake along their own unchanged velocity.
        # If the external sign arrives at the declared cut, waiting from
        # rest only adds that excess beyond the common braking prelude.
        with_bit_at=.002
        qualified=exact+max(0,with_bit_at-T0)
        assert qualified<T-.0001
        worlds.append(dict(sign=sign,physical_witness=round(exact,9),bit_at_002_witness=round(qualified,9),braking=round(T0,9),
                           clearance=round(min(clear1,clear2),9),edge=round(edge,9),
                           only_possible_peer=viable,
                           no_early_cross_sense_margin=round(nearest_time_delta,9)))
        all_worlds.append((g,viable))

    # Any two successful velocities agree at the last indistinguishable cut
    # and at the rest deadline. Relative travel <= A*(T-tau)^2/2.
    difference=A*(T-tau)**2/2
    enlargement=difference/2
    mid_slack=[]
    for i,j in product(all_worlds[0][1],all_worlds[1][1]):
        b,c=all_worlds[0][0][i],all_worlds[1][0][j]
        rb,rc=R+reach[i]+enlargement,R+reach[j]+enlargement
        mid=(b+c)/2
        radius_sq=(rb*rb+rc*rc)/2-float((b-c)@(b-c))/4
        margin=float(np.linalg.norm(center-mid))-reach[left]-sqrt(max(0,radius_sq))
        # Even the relaxed midpoint enclosure excludes the local reachable ball.
        assert margin>.001
        # Independent direct 2-D disk arrangement decision agrees.
        assert not three_disks((center,b,c),(reach[left],rb,rc))
        mid_slack.append(round(margin,9))
    positive=all(w["physical_witness"]<T for w in worlds)
    assert positive
    print(json.dumps(dict(deadline=T,common_history_until=tau,
                          pair_endpoint_distance_bound=round(difference,9),
                          terminal_midpoint_conflict_margin=mid_slack,
                          pre_cut=dict(clearance=round(min(x[0] for x in prefix),9),
                                       left_remote=round(min(x[1] for x in prefix),9),
                                       continuing_edge_upper=round(max(x[2] for x in prefix),9)),
                          given_cut_sign_bit=True,worlds=worlds),sort_keys=True,
                     default=lambda n:int(n)))

run()
