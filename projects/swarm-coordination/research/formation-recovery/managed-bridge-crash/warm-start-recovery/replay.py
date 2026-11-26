"""Post-crash bounded point mass using live positions AND velocities."""
from itertools import combinations
from math import ceil, floor, sqrt
import json
import numpy as np
from constrained_omrs import (default_open_formation_scenario, ControllerConfig,
                               SmoothBacksteppingController, simulate)
from constrained_omrs.graph import connected_components

def min_chord(x,y):
    r=y-x
    d=float(r@r)
    u=0 if d==0 else max(0,min(1.,float(-(x@r)/d)))
    return float(np.linalg.norm(x+u*r))

def linear_integral(lines,T):
    # Exact formula for the integral of the lower of finitely many lines
    # (evaluated in double precision on native source states).
    pts={0.,T}
    for (a,b),(c,d) in combinations(lines,2):
        if a!=c:
            t=(d-b)/(a-c)
            if 0.<t<T:pts.add(t)
    def f(t):return min(a*t+b for a,b in lines)
    s=sorted(pts)
    return sum((f(x)+f(y))*(y-x)/2 for x,y in zip(s,s[1:]))

def limit_distance(u,A,V,t):
    return linear_integral(((0.,V),(A,u),(-A,A*t)),t)

def lower_bound(p,v,C,A,V,R,projected):
    pairs=[]
    # Since ALL survivors must stop, braking time of any one is mandatory.
    minimum=float(max(np.linalg.norm(v[i]) for i in C[0]+C[1])/A)
    for i in C[0]:
        for j in C[1]:
            r=p[j]-p[i]
            d=float(np.linalg.norm(r))
            e=r/d
            if projected:
                u_i,u_j=float(v[i]@e),float(-v[j]@e)
            else:
                u_i,u_j=float(np.linalg.norm(v[i])),float(np.linalg.norm(v[j]))
            pairs.append((d-R,u_i,u_j))
    assert all(g>0 for g,_,_ in pairs)
    def possible(t):
        return any(g<=limit_distance(a,A,V,t)+limit_distance(b,A,V,t)
                   for g,a,b in pairs)
    low=minimum
    upper=2.
    while not possible(upper):upper*=2
    if possible(low):return low
    for _ in range(60):
        m=(low+upper)/2
        if possible(m):upper=m
        else:low=m
    # Downward guard for floating evaluation: the recorded negative-case
    # deadline has additional positive slack, not equality.
    return max(minimum,low-1e-8)

def rigid_profile(distance,A,V):
    assert distance>0
    v=min(sqrt(distance*A),V)
    t=v/A
    cruise=max(0.,(distance-v*t)/v)
    end=2*t+cruise
    def run(s):
        if s<t:return .5*A*s*s,A*s,A
        if s<t+cruise:return .5*A*t*t+v*(s-t),v,0.
        u=max(0.,end-s)
        return distance-.5*A*u*u,A*u,(-A if u>0 else 0.)
    return end,(t,t+cruise),run

def witness(p,v,C,edges,failed,A,V,R,s):
    targets=set(C[0]+C[1])
    speeds=np.linalg.norm(v,axis=1)
    stop={i:float(speeds[i]/A) for i in targets}
    T=max(stop.values())
    unit={i:v[i]/speeds[i] if speeds[i]>0 else v[i]*0 for i in targets}
    def brake(i,t):
        if i==failed:return p[i],v[i]*0,v[i]*0
        q=min(stop[i],t)
        a=-A*unit[i]
        return p[i]+q*v[i]+.5*q*q*a, v[i]*(1.-q/stop[i]) if stop[i] else v[i]*0, a if t<stop[i] else a*0
    q={i:brake(i,T)[0] for i in targets}
    dist,j,k=min((float(np.linalg.norm(q[j]-q[k])),j,k) for j in C[0] for k in C[1])
    D=(dist-R)/2
    n=(q[k]-q[j])/dist
    end,mid,profile=rigid_profile(D,A,V)
    moves={i:n if i in C[0] else -n for i in targets}
    def glide(i,t):
        if i==failed:return p[i],v[i]*0,v[i]*0
        x,u,a=profile(t)
        return q[i]+x*moves[i],u*moves[i],a*moves[i]
    sep=float("inf")
    clear=float("inf")
    carried=0.
    certified=0
    for fn,knots in ((brake,[0.,T]+list(stop.values())),(glide,[0.,end,*mid])):
        K=sorted(set(knots))
        seg=sorted(set(K+[m+(n0-m)*z/max(1,ceil((n0-m)/.005))
                          for m,n0 in zip(K,K[1:]) for z in range(1,ceil((n0-m)/.005))]))
        for left,right in zip(seg,seg[1:]):
            if right-left<1e-13:continue
            M=(left+right)/2
            dt=right-left
            f={i:(fn(i,left),fn(i,right),fn(i,M)[2]) for i in targets|{failed}}
            for i,((a,ua,_),(b,ub,_),ai) in f.items():
                assert np.allclose(a+dt*ua+.5*dt*dt*ai,b,atol=1e-10,rtol=0)
                assert np.allclose(ua+dt*ai,ub,atol=1e-10,rtol=0)
                assert max(np.linalg.norm(ua),np.linalg.norm(ub))<=V+1e-9
                assert np.linalg.norm(ai)<=A+1e-9
            for i,j0 in combinations(sorted(f),2):
                a,b=f[i][0][0]-f[j0][0][0],f[i][1][0]-f[j0][1][0]
                margin=float(np.linalg.norm(f[i][2]-f[j0][2]))*dt**2/8
                lo=min_chord(a,b)-margin
                if failed in (i,j0):clear=min(clear,lo)
                else:sep=min(sep,lo)
                if (i,j0) in edges:
                    carried=max(carried,float(max(np.linalg.norm(a),np.linalg.norm(b)))+margin)
                certified+=1
    assert min(sep,clear)>s.collision_distance+1e-8 and carried<s.sensing_distance-1e-8
    assert abs(np.linalg.norm(glide(j,end)[0]-glide(k,end)[0])-R)<1e-9
    assert all(np.linalg.norm(glide(i,end)[1])<1e-9 for i in targets)
    return T+end,T,sep,clear,carried,(j,k),certified

def main():
    out=[]
    for dim in (2,3):
        s=default_open_formation_scenario(dim)
        r=simulate(s,SmoothBacksteppingController(
            num_robots=s.num_robots,dimension=dim,collision_distance=s.collision_distance,
            sensing_distance=s.sensing_distance,
            config=ControllerConfig(k1=1.,k2=.8,k3=2.5,max_virtual_speed=.8)))
        for q in s.leave_requests:
            idx=round(q.time/s.dt)
            failed=q.robot
            p,v=r.positions[idx],r.velocities[idx]
            live=sorted(set(np.flatnonzero(r.active[idx]))-{failed})
            full_edges=[(i,j) for i,j in combinations(live,2) if np.linalg.norm(p[i]-p[j])<s.sensing_distance]
            C=list(map(sorted,connected_components(live,full_edges)))
            E={tuple(sorted(e)) for e in r.edge_history[idx] if failed not in e}
            assert len(C)==2 and {frozenset(g) for g in connected_components(live,E)}=={frozenset(g) for g in C}
            R=s.sensing_distance-s.reconfiguration.edge_activation_margin
            V=1.
            earliest_speed_only=min(float(np.linalg.norm(p[i]-p[j]))-R for i in C[0] for j in C[1])/2
            velocity_scatter=max(float(np.linalg.norm(v[i]-v[j])) for i,j in E)
            assert velocity_scatter>1e-10
            rows=[]
            for A in (.5,1.,2.):
                M=lower_bound(p,v,C,A,V,R,False)
                P=lower_bound(p,v,C,A,V,R,True)
                T,t,c1,c2,e,pair,count=witness(p,v,C,E,failed,A,V,R,s)
                assert earliest_speed_only<M<=P+1e-8 and P<=T+1e-8 and (T-P)<.001
                # Optional modeled service: no application qualification
                # can start until the connected formation is settled at rest.
                h=.25
                too_short=(floor((P+h)*100)-1)/100
                enough=ceil((T+h)*100)/100
                assert too_short<P+h<=T+h<=enough
                rows.append(dict(accel=A,
                                 rest_then_receipt_infeasible_at=too_short,
                                 rest_then_receipt_witness_by=enough,relative_speed_lower=round(P,8),speed_norm_lower=round(M,8),
                                 recovery_witness=round(T,8),brake_time=round(t,9),pair=pair,
                                 safe_pair_segment_count=count,
                                 continuous_survivor_separation=round(c1,8),continuous_stopped_clearance=round(c2,8),
                                 continuous_old_edge_upper=round(e,8)))
            out.append(dict(dimension=dim,departing=int(failed),request_cut=q.time,
                            nearest_speed_only=round(earliest_speed_only,8),
                            speed_scatter_on_required_edge=round(velocity_scatter,12),
                            cases=rows))
    print(json.dumps({"warm":out},sort_keys=True,default=lambda n:int(n)))

if __name__=="__main__":main()
