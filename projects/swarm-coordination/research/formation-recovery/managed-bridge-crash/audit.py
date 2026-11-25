from itertools import combinations
from pathlib import Path
from hashlib import sha1
import json
import numpy as np

ROOT=Path(__file__).resolve().parent
for line in (ROOT/'PINNED.tsv').read_text().splitlines():
    h,p=line.split('\t')
    b=(ROOT/p).read_bytes()
    assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==h,p
from constrained_omrs import (default_open_formation_scenario,ControllerConfig,
                               SmoothBacksteppingController,simulate)
from constrained_omrs.graph import connected_components

def physical_crossing(pos,live,range_):
    E=[(i,j) for i,j in combinations(live,2) if np.linalg.norm(pos[i]-pos[j])<range_]
    return connected_components(live,E)

def min_chord(x,y):
    p=y-x;l=float(p@p)
    t=0.0 if l==0 else max(0,min(1,float(-x@p)/l))
    return np.linalg.norm(x+t*p)

def frozen_body(res,s,robot,k):
    """Same survivor path from managed run, departing body stopped at its sampled pose."""
    body=res.positions[k,robot]
    lo=float('inf');hi=float('inf'); checked=0;violated=0;unresolved=0
    for t in range(k,len(res.time)-1):
        for i in range(s.num_robots):
            if i==robot or not res.active[t,i] or not res.active[t+1,i]:continue
            x=res.positions[t,i]-body
            y=res.positions[t+1,i]-body
            g=min_chord(x,y)
            q=np.linalg.norm(res.realized_accelerations[t,i])*s.dt**2/8
            assert np.allclose(res.positions[t+1,i],res.positions[t,i]+s.dt*res.velocities[t,i]+.5*s.dt**2*res.realized_accelerations[t,i],rtol=0,atol=1e-10)
            lower=g-q;upper=g+q
            lo=min(lo,lower);hi=min(hi,upper)
            if upper<s.collision_distance-1e-8:violated+=1
            elif lower<s.collision_distance+1e-8:unresolved+=1
            checked+=1
    return dict(chord_lower=round(lo,9),chord_upper=round(hi,9),
                checked=checked,definite_violations=violated,unresolved=unresolved)

def rigid_witness(pos,body,C,range_,clearance):
    assert len(C)==2
    A,B=map(sorted,C)
    best,i,j=min((np.linalg.norm(pos[i]-pos[j]),i,j) for i in A for j in B)
    gap=best-range_
    assert gap>0
    shift=(pos[j]-pos[i])*(gap/(2*best))
    body_min=min(float(min_chord(pos[k]-body,pos[k]+v-body))
                 for group,v in ((A,shift),(B,-shift)) for k in group)
    # Every cross pair has initial length >= best and can decrease by at
    # most gap before the terminal cut. Internal relative positions don't change.
    assert range_>clearance
    return dict(analytic_time=round(float(gap/2),9),chosen=[i,j],
                body_min=round(body_min,9),straight_clear=bool(body_min>clearance+1e-8))

def command_config(s):
    return SmoothBacksteppingController(
        num_robots=s.num_robots,dimension=s.dimension,collision_distance=s.collision_distance,
        sensing_distance=s.sensing_distance,config=ControllerConfig(k1=1.,k2=.8,k3=2.5,max_virtual_speed=.8))

def case(dim):
    s=default_open_formation_scenario(dim)
    r=simulate(s,command_config(s))
    def ix(t):return int(round(t/s.dt))
    out=[]
    for leave in s.leave_requests:
        robot=leave.robot
        times=[('request',leave.time)]
        exact=[e for e in r.switch_events if e.robot==robot and e.kind in ('bridge_activation','robot_leave')]
        times.extend((e.kind,e.time) for e in exact)
        for label,t in times:
            k=ix(t)
            V=sorted(set(np.flatnonzero(r.active[k]))-{robot})
            C=physical_crossing(r.positions[k],V,s.sensing_distance)
            D=connected_components(V,[e for e in r.edge_history[k] if robot not in e])
            body=min(np.linalg.norm(r.positions[k,i]-r.positions[k,robot]) for i in V)
            gap=0 if len(C)==1 else min(float(np.linalg.norm(r.positions[k,i]-r.positions[k,j]))
                for a,b in combinations(C,2) for i in a for j in b)-s.sensing_distance
            q=dict(event=label,time=round(t,4),robot=robot,established_components=len(D),
                geometric_components=len(C),body_clearance=round(float(body),8),
                smallest_cross_gap=round(gap,8))
            if label=='request' and len(C)==2:
                target=s.sensing_distance-s.reconfiguration.edge_activation_margin
                q['speed_only']=rigid_witness(r.positions[k],r.positions[k,robot],C,target,s.collision_distance)
            if label=='robot_leave':q['frozen_replay']=frozen_body(r,s,robot,k)
            out.append(q)
    return dict(dimension=dim,collision_distance=s.collision_distance,sensing_distance=s.sensing_distance,
                min_active_distance=round(float(np.nanmin(r.min_pair_distance)),10),
                max_established_distance=round(float(np.nanmax(r.max_established_edge_distance)),10),
                cuts=out)
if __name__=='__main__':
    for dim in (2,3):
        print(json.dumps(case(dim),sort_keys=True),flush=True)

    # Matched diagnostic beyond the source request poses. At T=1.05 the
    # box-constrained left endpoint cannot be >=1/2 from the failed body.
    from fractions import Fraction as F
    d=F(1,20)
    assert d*d+4*d < F(1,4)
    P=np.array([[-2.,0],[2.,0]])
    Q=np.array([[-2.,1],[2.,1]])
    R=np.array([[-1.,1],[1.,1]])
    body=np.array([-1.,0])
    assert np.max(np.linalg.norm(Q-P,axis=1))==np.max(np.linalg.norm(R-Q,axis=1))==1.
    assert all(min_chord(a-body,b-body)>=.5 for x,y in ((P,Q),(Q,R)) for a,b in zip(x,y))
    assert np.linalg.norm(R[1]-R[0])==2.
    print(json.dumps({'matched_blocked':{'deadline':1.05,'infeasible':True,'straight_contact_lower':1,
                                        'clear_detour_time':2,'upper_endpoint_squared_clearance':str(d*d+4*d)}},
                     sort_keys=True))
