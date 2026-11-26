from fractions import Fraction as F
from itertools import combinations, product
import json
import numpy as np
from constrained_omrs import (default_open_formation_scenario, ControllerConfig,
                               SmoothBacksteppingController, simulate)

def min_chord(x,y):
    p=y-x
    d=p@p
    t=0 if d==0 else max(0,min(1,-(x@p)/d))
    return float(np.linalg.norm(x+t*p))

def regime(dim):
    s=default_open_formation_scenario(dim)
    r=simulate(s,SmoothBacksteppingController(
        num_robots=s.num_robots,dimension=s.dimension,collision_distance=s.collision_distance,
        sensing_distance=s.sensing_distance,
        config=ControllerConfig(k1=1.,k2=.8,k3=2.5,max_virtual_speed=.8)))
    rows=[]
    for req in s.leave_requests:
        events=[e for e in r.switch_events if e.robot==req.robot and e.time>=req.time]
        a=next(e for e in events if e.kind=="bridge_activation")
        b=next(e for e in events if e.kind=="robot_leave")
        lo,hi=map(lambda t:int(round(t/s.dt)),(a.time,b.time))
        assert lo<hi
        left={tuple(sorted(edge)) for edge in b.edges_removed}
        right={tuple(sorted(edge)) for edge in a.edges_added}
        assert left and right and not (left&right)
        subjects=sorted(set(np.flatnonzero(r.active[lo])))
        lower=float("inf")
        upper=0.
        count=0
        for k in range(lo,hi):
            vv=r.velocities[k]
            aa=r.realized_accelerations[k]
            p=r.positions[k]
            q=r.positions[k+1]
            assert np.allclose(p+s.dt*vv+s.dt*s.dt*aa/2,q,rtol=0,atol=1e-10)
            assert all(r.active[k,z] for z in subjects)
            for i,j in combinations(subjects,2):
                x,y=p[i]-p[j],q[i]-q[j]
                dev=float(np.linalg.norm(aa[i]-aa[j])*s.dt*s.dt/8)
                lower=min(lower,min_chord(x,y)-dev)
                if (i,j) in left|right:
                    upper=max(upper,float(max(np.linalg.norm(x),np.linalg.norm(y)))+dev)
                count+=1
            edges={tuple(sorted(x)) for x in r.edge_history[k]}
            assert left|right<=edges
        assert lower>s.collision_distance+1e-7
        assert upper<s.sensing_distance-1e-7
        rows.append(dict(robot=req.robot,bridge_at=round(a.time,6),leave_at=round(b.time,6),
                         overlap=round((hi-lo)*s.dt,8),old_edges=sorted(left),new_edges=sorted(right),
                         continuous_lower_clearance=round(lower,8),continuous_upper_edge_distance=round(upper,8),
                         pair_segments=count))
    return dict(dimension=dim,source_clearance=s.collision_distance,nominal_range=s.sensing_distance,rows=rows)

def integral_envelope(lines,h,minimize):
    # Exact area of a piecewise affine upper/lower envelope.
    cuts={F(0),h}
    for (m,b),(n,c) in combinations(lines,2):
        if m!=n:
            t=(c-b)/(m-n)
            if 0<t<h:cuts.add(t)
    choose=min if minimize else max
    value=lambda t:choose(m*t+b for m,b in lines)
    cuts=sorted(cuts)
    return sum((value(l)+value(r))*(r-l)/2 for l,r in zip(cuts,cuts[1:]))

def direct_minimum(u,A,h):
    return integral_envelope(((0,F(0)),(-A,u)),h,False)

def own_minimum(u,A,h):
    z=min(h,u/A)
    return u*z-A*z*z/2

def verify_piece(p,u,a,t):
    v=u+a*t
    x=p+u*t+a*t*t/2
    assert 0<=u<=1 and 0<=v<=1 and -1<=a<=1
    return x,v

def qualification(window,delay,active,matching,erased,ack_first):
    # Plausible qualified-handoff protocol, not a behavior of the KTH
    # transport. Two ordered events; the workflow aborts on lost joint link.
    issued=bool(active)
    admitted=(delay<window or (delay==window and ack_first))
    ack_callback=issued and admitted and matching and not erased
    return ("start" if issued else "no-start", "qualify" if ack_callback else "hold-or-abort")

def exchanges():
    T=F(1)
    rows={}
    for label,h,active,matched,erased,first in (
           ("both-edges-before-release",F(3,4),True,True,False,False),
           ("equal-release-first",F(1),True,True,False,False),
           ("equal-ack-first",F(1),True,True,False,True),
           ("late",F(5,4),True,True,False,True),
           ("erased",F(3,4),True,True,True,True),
           ("wrong-identity",F(3,4),True,False,False,True),
           ("abrupt",F(0),False,True,False,True)):
        rows[label]=qualification(T,h,active,matched,erased,first)
    assert {k for k,v in rows.items() if v[1]=="qualify"}=={"both-edges-before-release","equal-ack-first"}
    return rows

def model():
    # Route x in [0,1/4] at y=0. Anchors and a surviving third node
    # keep the base graph connected. A stopped body remains excluded.
    old=(F(-7,8),F(3,4))
    new=(F(1),F(3,4))
    anchor=(F(1,16),F(3,2))
    stopped=(F(1,16),F(-1,2))
    radius=F(5,4)
    route_end=F(1,4)
    width=F(1,8)
    h=F(1,4)
    def dsq(a,b):return sum((x-y)**2 for x,y in zip(a,b))
    assert dsq(old,anchor)<radius**2 and dsq(new,anchor)<radius**2
    assert radius**2-old[1]**2==radius**2-new[1]**2==1
    assert old[0]+1==width and new[0]-1==0
    assert min(abs(x[1]) for x in (old,new,anchor,stopped))==F(1,2)
    assert all(dsq(a,b)>F(1,9) for a,b in combinations((old,new,anchor,stopped),2))
    # Valid exact sample paths attaining equality and earlier slack.
    for init,a,b in ((F(1,2),F(0),F(0)),(F(5,8),F(-1),F(1))):
        x,u=verify_piece(F(0),init,a,h)
        assert x==width
        y,v=verify_piece(x,u,b,h)
        assert y==route_end
    assert own_minimum(F(1),F(1),h)==F(7,32)>width
    assert own_minimum(F(5,8),F(1),h)==width
    assert own_minimum(F(5,8)+F(1,1000),F(1),h)>width
    n=0
    for a,b,t in product(range(13),range(1,12),range(16)):
        u,A,h0=F(a,12),F(b,9),F(t,8)
        assert own_minimum(u,A,h0)==direct_minimum(u,A,h0)
        n+=1
    return dict(width=str(width),range=str(radius),check_cases=n,
                required_overlap=str(h),crit_entry_speed="5/8",
                early_braking_distance_from_unit_speed="39/128",
                physical_feasible_at_critical_speed=True,physically_infeasible_at_unit_speed=True)

if __name__=="__main__":
    print(json.dumps({"published":list(map(regime,(2,3))),"authored":model(),"authored_exchange_on_known_schedule":exchanges()},sort_keys=True))
