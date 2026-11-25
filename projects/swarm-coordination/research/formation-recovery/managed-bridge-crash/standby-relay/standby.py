from itertools import combinations, product
from pathlib import Path
from hashlib import sha1
from fractions import Fraction as Q
import numpy as np

for line in Path("PINNED.tsv").read_text().splitlines():
    h,p=line.split("\t")
    b=(Path("upstream")/p).read_bytes()
    assert sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==h

from constrained_omrs import (default_open_formation_scenario,ControllerConfig,
                               SmoothBacksteppingController,simulate)
from constrained_omrs.graph import connected_components

def minball(pts):
    # Minimum enclosing ball support enumeration; exclude affine redundancy.
    n,d=pts.shape
    best=None
    for k in range(1,min(d+1,n)+1):
        for ids in combinations(range(n),k):
            v=pts[list(ids)]
            dif=v[1:]-v[0]
            if k==1:
                x=v[0]; eta=np.ones(1)
            else:
                if np.linalg.matrix_rank(dif)!=k-1: continue
                bary=np.linalg.solve(dif@dif.T,(dif*dif).sum(axis=1)/2)
                eta=np.r_[1-sum(bary),bary]
                if min(eta)<-1e-10: continue
                x=eta@v
            radii=np.linalg.norm(pts-x,axis=1)
            val=float(np.max(radii))
            if max(radii[list(ids)]) < val-1e-9: continue
            if best is None or val<best[0]:best=(val,x,ids,eta)
    assert best is not None
    return best

def min_prefix(x,s,r,end):
    # All originally active/entering robots. Do not move the standby.
    pts=r.positions[:end+1]-x
    previous,next=pts[:-1],pts[1:]
    continue_mask=r.active[:end] & r.active[1:end+1]
    st,finish=previous[continue_mask],next[continue_mask]
    d=finish-st
    den=np.sum(d*d,axis=1)
    t=np.divide(-np.sum(st*d,axis=1),den,out=np.zeros_like(den),where=den>0)
    t=np.clip(t,0,1)
    chord=np.linalg.norm(st+t[:,None]*d,axis=1)
    acc=r.realized_accelerations[:end][continue_mask]
    vs=r.velocities[:end][continue_mask]
    assert np.allclose(st+s.dt*vs+.5*s.dt**2*acc,finish,atol=1e-10,rtol=0)
    sag=np.linalg.norm(acc,axis=1)*s.dt**2/8
    sampled=np.linalg.norm(pts,axis=-1)[r.active[:end+1]].min()
    return min(sampled,(chord-sag).min()),min(sampled,(chord+sag).min())

def qvec(x): return tuple(Q(float(z)) for z in x)
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def scale(k,a): return tuple(k*x for x in a)
def sq(a): return dot(a,a)

def dual(pts,ids,weights):
    # Any exact nonnegative weights of total one give the variance lower bound.
    lam=[max(Q(0),Q(float(v))) for v in weights]
    lam=[v/sum(lam) for v in lam]
    v=[qvec(pts[i]) for i in ids]
    c=tuple(sum(l*x for l,x in zip(lam,col)) for col in zip(*v))
    return sum(a*sq(sub(x,c)) for a,x in zip(lam,v))

def exact_clear(center,s,r,end):
    count=0
    d=Q("0.45")
    h=Q(str(s.dt))
    for t in range(end+1):
        for i in range(s.num_robots):
            if not r.active[t,i]:continue
            x=sub(qvec(r.positions[t,i]),center)
            assert sq(x)>d*d
            if t==end or not r.active[t+1,i]:continue
            y=sub(qvec(r.positions[t+1,i]),center)
            v=sub(y,x)
            a=qvec(r.realized_accelerations[t,i])
            z=0 if not sq(v) else max(Q(0),min(Q(1),-dot(x,v)/sq(v)))
            # euclidean bound by L1, on quadratic interpolant fixed by
            # endpoints and recorded acceleration.
            sag=sum(map(abs,a))*h*h/8
            assert sq(add(x,scale(z,v)))>(d+sag)**2,(t,i)
            count+=1
    return count

def exact_cut_range(center,spec,sel,upper):
    for (_,p,_),ij in zip(spec,sel):
        for j in ij:assert sq(sub(qvec(p[j]),center))<=upper**2

def run(dim):
    s=default_open_formation_scenario(dim)
    control=SmoothBacksteppingController(num_robots=s.num_robots,dimension=s.dimension,
           collision_distance=s.collision_distance,sensing_distance=s.sensing_distance,
           config=ControllerConfig(k1=1.,k2=.8,k3=2.5,max_virtual_speed=.8))
    r=simulate(s,control)
    cut_specs=[]
    for dep in s.leave_requests:
        k=round(dep.time/s.dt)
        live=[int(i) for i,b in enumerate(r.active[k]) if b and i!=dep.robot]
        pts=r.positions[k]
        edges=[(i,j) for i,j in combinations(live,2) if np.linalg.norm(pts[i]-pts[j])<s.sensing_distance]
        groups=connected_components(live,edges)
        assert len(groups)==2
        cut_specs.append((k,pts,groups))
    horizon=cut_specs[-1][0]
    options=[tuple(product(*g)) for _,p,g in cut_specs]
    opts=[]
    for sel in product(*options):
        vectors=np.array([p[i] for (k,p,g),ij in zip(cut_specs,sel) for i in ij])
        rad,center,inds,weights=minball(vectors)
        opts.append((rad,center,sel,dual(vectors,inds,weights)))
    opts.sort(key=lambda a:a[0])
    low,loc,sel,info=opts[0]
    cl=min_prefix(loc,s,r,horizon)
    print(dim, "cuts",len(cut_specs),"anchor assignments",len(opts),"R",s.sensing_distance)
    print(f"Static radio-only lower={low:.8f}, center",np.round(loc,8),f"pre-cut clearance {cl[0]:.8f} to {cl[1]:.8f}")
    for _,p,g in cut_specs:
        m,i,j=min((np.linalg.norm(p[i]-p[j]),i,j) for i,j in product(*g))
        print(f"One cut radius lower={m/2:.8f}")
    if dim==3:
        lower=Q("1.3225314"); upper=Q("1.3225317")
        assert min(v[3] for v in opts)>lower**2
        center=tuple(map(Q,("-0.22462603","-0.42195463","2.11860085")))
    else:
        lower=Q("1.09618"); upper=Q("1.09623")
        k,p,_=cut_specs[0]
        for _,_,sel_,bound in opts:
            if bound>lower**2:continue
            a,b=(qvec(p[j]) for j in sel_[0])
            mid=scale(Q(1,2),add(a,b))
            # Find one recorded active center within this radius of midpoint.
            margin=Q("0.000096")
            assert any(sq(sub(qvec(v),mid))<margin**2
                       for v in r.positions[:k+1][r.active[:k+1]])
            assert sq(sub(a,b))/4+(Q("0.45")-margin)**2>lower**2
        center=tuple(map(Q,("-0.6550702","0.445514")))
    checked=exact_clear(center,s,r,horizon)
    exact_cut_range(center,cut_specs,sel,upper)
    print("Static with clearance enclosure",str(float(lower)),str(float(upper)),
          "rational survivor/standby arc checks",checked)
    return s,r,cut_specs,opts
if __name__=="__main__":
    for d in (2,3):run(d)
