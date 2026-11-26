"""Uncertain authored crash cut; compare reusing motion versus its axis."""
from itertools import combinations,product
from math import sqrt
from pathlib import Path
import json
import sys
import numpy as np
from warm import lower_bound

source=Path(sys.argv[1])/"local.py"
code=source.read_text()
assert code.endswith("\nrun()\n")
m={}
exec(compile(code[:-len("run()\n")],str(source),"exec"),m)
s,failed,p0,v0,C,E,ids=m["actual_cut"]()
left=C[0][0];right=C[1]
direction=p0[right[0]]-p0[left]
direction/=np.linalg.norm(direction)
lat=np.array([-direction[1],direction[0]])
R=s.sensing_distance-s.reconfiguration.edge_activation_margin
T=1.11
V=A=1.

def cut(sign,advance):
    # Independent variable is time before the previously fixed fault.
    # Stamp-conditioned source template, not a fresh state measurement.
    t=-advance
    z=(t+3)/3
    p=p0+t*v0
    v=v0.copy()
    p[right,:]+=sign*.8*(3*z*z-2*z*z*z)*lat
    v[right,:]+=sign*.8*(6*z-6*z*z)/3*lat
    v[failed]*=0 # the failed body is parked at its actual cut pose
    return p,v

def projected_axes(p,v,sign,rotate):
    i,j=left,right[0]
    if rotate:
        u=p[j]-p[i]
    else:
        n,w=cut(sign,0.)
        # Nominal post-braking axis from the verified original policy.
        u=n[j]+np.linalg.norm(w[j])*w[j]/2-n[i]-np.linalg.norm(w[i])*w[i]/2
    e=u/np.linalg.norm(u)
    r=p[j]-p[i]
    proj=float(r@e)
    side=float(np.linalg.norm(r-proj*e))
    assert side<R
    return e,proj-sqrt(R*R-side*side)

def interval(v,e,k,shift):
    u=shift*v
    d=float(u@e)
    n=A*A-float(np.linalg.norm(u-d*e))**2
    if n<0:return float("inf"),-float("inf")
    w=sqrt(n)
    return (d-w)/k,(d+w)/k

def member(v,e,t):
    return (interval(v,e,2/(t*T),(T+t)/(t*T)),
            interval(v,e,2/((T-t)*T),t/((T-t)*T)))

def choice(p,v,sign,rotate,tuned):
    u,target=projected_axes(p,v,sign,rotate)
    assert target>0
    bounds=[]
    for J,e in (([left],u),(right,-u)):
        sgrid=(T/2,) if not tuned else (T*f for f in np.linspace(.47,.53,601))
        tests=[]
        for t in sgrid:
            it=[a for i in J for a in member(v[i],e,t)]
            ll,hh=max(0.,*(x[0] for x in it)),min(x[1] for x in it)
            if ll<=hh:tests.append((hh,ll,t))
        hh,ll,t=max(tests)
        bounds.append((ll,hh,t))
    (la,ha,t1),(lb,hb,t2)=bounds
    if max(la,target-hb)>min(ha,target-lb)-1e-10:
        return None,round(ha+hb-target,9)
    a=(max(la,target-hb)+min(ha,target-lb))/2
    return ((a*u,-(target-a)*u),(t1,t2)),round(ha+hb-target,9)

def certify(p,v,recipe):
    moves,times=recipe
    a=np.zeros_like(p);b=np.zeros_like(p)
    switches=np.zeros(len(p))
    for J,d,k in zip(C,moves,times):
        for i in J:
            a[i]=2*d/(k*T)-(T+k)*v[i]/(k*T)
            b[i]=-2*d/((T-k)*T)+k*v[i]/((T-k)*T)
            switches[i]=k
            assert max(np.linalg.norm(a[i]),np.linalg.norm(b[i]))<=A+1e-9
    def at(t):
        st=np.minimum(switches,t).reshape(-1,1)
        aft=t-st
        mid=v+st*a
        return p+st*v+st*st*a/2+aft*mid+aft*aft*b/2,mid+aft*b
    p2,v2=at(T)
    assert np.max(np.linalg.norm(v2,axis=1))<1e-9
    assert abs(np.linalg.norm(p2[right[0]]-p2[left])-R)<1e-8
    clear=float("inf");upper=0.
    knots=sorted(set([0.,*times,T]))
    for leftk,rightk in zip(knots,knots[1:]):
        acc=np.where(((leftk+rightk)/2<switches).reshape(-1,1),a,b)
        grid=np.linspace(leftk,rightk,51)
        for lo,hi in zip(grid,grid[1:]):
            x,dx=at(lo);y,dy=at(hi)
            assert max(np.linalg.norm(z[i]) for z in (dx,dy) for i in ids)<=V
            for i,j in combinations(sorted(ids+[failed]),2):
                d=float(np.linalg.norm(acc[i]-acc[j]))*(hi-lo)**2/8
                x0,y0=x[i]-x[j],y[i]-y[j]
                clear=min(clear,m["min_chord"](x0,y0)-d)
                if (i,j) in E:upper=max(upper,max(np.linalg.norm(x0),np.linalg.norm(y0))+d)
    assert clear>s.collision_distance+1e-6 and upper<s.sensing_distance-1e-6
    return dict(clearance=round(float(clear),8),old_link=round(float(upper),8),
                switches=[round(t,8) for t in times])

def main():
    results={}
    for sign,advance in product((-1,1),(0.,.0005,.001,.002,.004,.008,.01,.016,.032,.064)):
        p,v=cut(sign,advance)
        back=m["witness"](p,v,C,E,failed,A,V,R,s)[0]
        # Primitive after a memoized open-loop command from a different
        # initial velocity. The output is kinematic error, not field drift.
        p0s,v0s=cut(sign,0.)
        residual=float(max(np.linalg.norm(v[i]-v0s[i]) for i in ids))
        offset=float(np.linalg.norm(p[right[0]]-p0s[right[0]]+advance*v0[right[0]]))
        assert (residual<1e-9)==(advance==0.)
        lower=lower_bound(p,v,C,A,V,R,True)
        record=dict(fixed_command_residual_speed=round(residual,9),
                    offset_missing=round(offset,9),brake_first_witness=round(back,9),
                    absolute_physical_lower=round(lower,9))
        for name,use_direct,tuned in (("same_axis_half",False,False),
                                       ("same_axis_tuned",False,True),
                                       ("new_axis_tuned",True,True)):
            move,gap=choice(p,v,sign,use_direct,tuned)
            record[name]=dict(phase_capacity_slack=gap,witness=certify(p,v,move) if move else None)
            if move:assert lower<T
        results[f"{sign}/{advance}"]=record
    assert any(x["same_axis_tuned"]["witness"] and x["brake_first_witness"]>T for x in results.values())
    assert any(not x["same_axis_tuned"]["witness"] and x["absolute_physical_lower"]>T for x in results.values())
    print(json.dumps(dict(deadline=T,motion=results),sort_keys=True))

main()
