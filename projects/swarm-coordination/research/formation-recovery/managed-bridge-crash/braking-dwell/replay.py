"""Overlap continuous link dwell with braking, on pinned point-mass cuts."""
from itertools import combinations,product
from math import sqrt
from fractions import Fraction as F
import json
import numpy as np
import warm as w

# Rest-rest displacement upper bound of one scalar input.
def total(T,A,V):
    ramp=V/A
    return A*T*T/4 if T<=2*ramp else V*(T-ramp)

def time_to_stop_at(L,A,V):
    return 2*sqrt(L/A) if L<=V*V/A else L/V+V/A

def bound_sample(T,t,L,A,V):
    tau=min(T,time_to_stop_at(L,A,V))
    return w.linear_integral(((0,V),(A,0),(-A,A*tau)),min(tau,t))

def scalar_can(T,h,C,L,A,V):
    if T<h or L<C:
        return False
    return bound_sample(T,T-h,L,A,V) >= C-1e-12

def scalar_checks():
    assert abs(bound_sample(1.2,.8,.3,1,4)-(.3-(sqrt(1.2)-.8)**2/2))<1e-12
    assert scalar_can(1.2,.4,.25,.3,1,4)
    assert not scalar_can(1.2,.4,.25,.25,1,4)
    assert scalar_can(sqrt(1.32),.4,.25,.6,1,4)
    assert not scalar_can(sqrt(1.32)-1e-5,.4,.25,.6,1,4)
    assert not scalar_can(1.4-1e-5,.4,.25,.25,1,4)
    assert scalar_can(1.4,.4,.25,.25,1,4)
    T,h,C,L=F(112,100),F(2,5),F(1,4),F(3,5)
    cut=T-h
    # Rest alone attains .25 by 1. Dwell alone exceeds .25 by .72
    # with continuous safe braking afterward, but misses rest at T.
    turn=F(71,100)
    def distance(t):
        d=t-turn
        return t*t/2 if d<=0 else turn*turn/2+turn*d-d*d/2
    assert T>=1 and distance(cut)>=C and distance(T)<L and turn-(T-turn)>0
    # At the last viable dwell start, integration of the joint velocity
    # envelope is exactly T^2/4-h^2/2, strictly below .25.
    assert T/2<cut and T*T/4-h*h/2<C
    assert not scalar_can(float(T),float(h),float(C),float(L),1,4)
    # Independent endpoint integration with the explicit switching times
    # and dense trajectories that respect the same velocity-reversal law.
    count=0
    for T,L,A,V in product((.4,1.2,3.1),(0,.07,.3,.8,2.1),(.5,1,2),(.4,1,2)):
        if L==0:continue
        D=min(total(T,A,V),L)
        end,_,profile=w.rigid_profile(D,A,V)
        for t in np.linspace(0,T,31):
            expected=profile(t)[0] if t<end else D
            assert abs(bound_sample(T,float(t),L,A,V)-expected)<1e-10
            count+=1
    return count

def lower(p,v,C,A,V,R,h):
    pairs=[]
    Tstop=float(max(np.linalg.norm(v[i]) for g in C for i in g)/A)
    for i,j in product(*C):
        r=p[j]-p[i]
        d=float(np.linalg.norm(r))
        n=r/d
        pairs.append((d-R,float(v[i]@n),float(-v[j]@n)))
    def possible(T):
        return any(d<=sum(w.linear_integral(((0,V),(A,u),(-A,A*T)),T-h)
                          for u in (a,b)) for d,a,b in pairs)
    lo=max(Tstop,h)
    if possible(lo):
        return lo
    hi=lo+1
    while not possible(hi):hi*=2
    for _ in range(60):
        m=(hi+lo)/2
        if possible(m):hi=m
        else:lo=m
    return lo-1e-8

def witness(p,v,C,E,fail,A,V,R,h,s):
    live=C[0]+C[1]
    braking=max(np.linalg.norm(v[i]) for i in live)/A
    q={i:p[i]+v[i]*np.linalg.norm(v[i])/(2*A) for i in live}
    d,i,j=min((float(np.linalg.norm(q[i]-q[j])),i,j) for i,j in product(*C))
    # Strict threshold for the interval proof by collinearity. The
    # target is deliberately closer than R when extra closure helps.
    close=(d-(R-1e-5))/2
    assert close>0
    only_stop=time_to_stop_at(close,A,V)
    hi=only_stop+h
    lo=max(only_stop,h)
    assert w.rigid_profile(total(hi,A,V),A,V)[2](hi-h)[0]>=close
    for _ in range(60):
        t=(lo+hi)/2
        if w.rigid_profile(total(t,A,V),A,V)[2](t-h)[0]>=close:hi=t
        else:lo=t
    tau=hi+1e-6
    end_range=d-2*total(tau,A,V)
    assert s.collision_distance < end_range < R
    total_t,_,c1,c2,e,pair,count=w.witness(p,v,C,E,fail,A,V,end_range,s)
    same=pair==(i,j)
    # Old proven path uses the identical braked nearest pair. Its
    # separation is d-2*x from first contact continuously to rest.
    prof=w.rigid_profile(total(tau,A,V),A,V)
    assert same and abs(total_t-(braking+tau))<=1e-8
    start=total_t-h
    dist=d-2*prof[2](start-braking)[0]
    assert start>=braking and dist<R-0.5e-5
    assert abs(prof[2](tau)[1])<1e-7
    return total_t,end_range,dist,min(c1,c2),e,count

def main():
    out=[]
    for dim in (2,3):
        s=w.default_open_formation_scenario(dim)
        r=w.simulate(s,w.SmoothBacksteppingController(
            num_robots=s.num_robots,dimension=s.dimension,
            collision_distance=s.collision_distance,sensing_distance=s.sensing_distance,
            config=w.ControllerConfig(k1=1.,k2=.8,k3=2.5,max_virtual_speed=.8)))
        for q in s.leave_requests:
            idx=round(q.time/s.dt)
            f=q.robot
            p,v=r.positions[idx],r.velocities[idx]
            live=sorted(set(np.flatnonzero(r.active[idx]))-{f})
            full=[(i,j) for i,j in combinations(live,2)
                  if np.linalg.norm(p[i]-p[j])<s.sensing_distance]
            C=list(map(sorted,w.connected_components(live,full)))
            E={tuple(sorted(e)) for e in r.edge_history[idx] if f not in e}
            assert len(C)==2
            assert {tuple(g) for g in C}=={tuple(sorted(g)) for g in w.connected_components(live,E)}
            rr=s.sensing_distance-s.reconfiguration.edge_activation_margin
            for A,h in product((.5,1.,2.),(.15,.25,.35)):
                vcap=1.
                L=lower(p,v,C,A,vcap,rr,h)
                slow=w.lower_bound(p,v,C,A,vcap,rr,True)+h
                T,goal,initial,sep,old,count=witness(p,v,C,E,f,A,vcap,rr,h,s)
                assert L<=T+1e-8 and T-L<.003
                assert T<slow-.03
                out.append(dict(dimension=dim,cut=q.time,failed=int(f),accel=A,dwell=h,
                     absolute_motion_lower=round(L,8),certified_motion_upper=round(T,8),
                     stationary_first_lower=round(slow,8),rest_gap=round(goal,8),
                     dwell_start_gap=round(initial,8),clearance=round(sep,8),
                     old_edge_max=round(old,8),pairs=count))
    print(json.dumps(dict(scalar_crosschecks=scalar_checks(),source_cases=out),
                     sort_keys=True,indent=2))
if __name__=="__main__":main()
