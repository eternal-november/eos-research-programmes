"""Conservative exact zonotope certificate for translating a fixed 3-D cube."""
import numpy as np
from decimal import Decimal as D
from fractions import Fraction as F
from pathlib import Path
from math import sqrt
import sys,json
import survey,ride

I=np.eye(3)
grid=survey.GRID

def slab_hit(u,v,L,H,pad):
    lo,hi=F(0),F(1)
    for a,b,l,h in zip(u,v,L,H):
       l,h=F(l-pad),F(h+pad)
       if b==a:
          if not l<=a<=h:return False
       else:
          s,t=sorted(((l-a)/(b-a),(h-a)/(b-a)))
          lo=max(lo,s);hi=min(hi,t)
          if lo>hi:return False
    return True

def boxzonotope(m,u,v,verify=False,pad=D(".3005")):
    for l,h in m.fences:
        if slab_hit(u,v,l,h,pad):return False
    d=np.array(v,dtype=float)-np.array(u,dtype=float)
    r=float(pad)
    low=np.minimum(u,v)-r;high=np.maximum(u,v)+r
    if verify:
        if not hasattr(m,"ilo"):
            m.ilo,m.ihi=m.T.min(axis=1),m.T.max(axis=1)
        rho=int(pad*grid)
        L=np.minimum(u,v)*grid-rho;H=np.maximum(u,v)*grid+rho
        ix=np.nonzero(((m.ilo<=H)&(m.ihi>=L)).all(axis=1))[0]
    else:
        ix=m.sub(low,high)
    if len(ix)==0:return True
    tri=m.F[ix]
    E=np.roll(tri,-1,axis=1)-tri
    A=np.array(u,dtype=float)
    B=np.array(v,dtype=float)
    gen=np.vstack((I,d))
    own=np.vstack((I,np.cross(I,d)))
    normals=np.cross(E[:,0,:],E[:,1,:])[:,None,:]
    cross=np.cross(E[:,:,None,:],gen[None,None,:,:]).reshape(-1,12,3)
    n=np.concatenate((np.broadcast_to(own,(len(ix),6,3)),normals,cross),axis=1)
    norm=np.linalg.norm(n,axis=2)
    points=np.einsum("nvc,nac->nav",tri,n)
    rad=np.abs(n).sum(axis=2)*r
    a=n@A;b=n@B
    gap=np.maximum(points.min(axis=2)-np.maximum(a,b)-rad,
                   np.minimum(a,b)-rad-points.max(axis=2))
    gap=np.divide(gap,norm,out=np.full_like(gap,-np.inf),where=norm>1e-13)
    win=gap.argmax(axis=1)
    if not np.all(gap.max(axis=1)>1e-9):return False
    if not verify:return True
    c=n[np.arange(len(ix)),win,:]
    u=[int(x*grid) for x in u];v=[int(x*grid) for x in v]
    rho=int(pad*grid)
    axes=np.rint(10**7*c/np.linalg.norm(c,axis=1)[:,None]).astype(np.int64).tolist()
    for axis,T in zip(axes,m.T[ix].tolist()):
      def dot(x):return sum(a*b for a,b in zip(axis,x))
      x,y=sorted((dot(u),dot(v)))
      p=[dot(t) for t in T];R=rho*sum(map(abs,axis))
      if not (max(p)<x-R or y+R<min(p)):return False
    return True

from itertools import product
from functools import lru_cache

def length(a,b):return sqrt(sum((x-y)**2 for x,y in zip(a,b)))

def plan(m,p,domain):
    @lru_cache(None)
    def allowed(a,b):
        return ride.within(a,b,domain) and boxzonotope(m,a,b)
    def ok(a,b):return allowed(*sorted((a,b)))
    def shorten(q):
        h={0:0};par={}
        for i in range(len(q)):
            if i not in h:continue
            for j in range(i+1,len(q)):
                new=h[i]+length(q[i],q[j])
                if new>=h.get(j,float("inf")) or not ok(q[i],q[j]):continue
                h[j]=new;par[j]=i
        j=len(q)-1;r=[q[j]]
        while j:
            j=par[j];r.append(q[j])
        return r[::-1]
    p=shorten(p)
    for _ in range(5):
      hit=False
      for i in range(1,len(p)-1):
        u,a,v=p[i-1:i+2]
        best=a;score=length(u,a)+length(a,v)
        for xyz in product((-1,0,1),repeat=3):
           b=tuple(k+j for k,j in zip(a,xyz))
           if b not in domain or b==u or b==v:continue
           val=length(u,b)+length(b,v)
           if val>=score-1e-9 or not (ok(u,b) and ok(b,v)):continue
           best,score=b,val
        if best!=a:p[i]=best;hit=True
      p=shorten(p)
      if not hit:break
    assert all(ride.within(u,v,domain) and boxzonotope(m,u,v,True) for u,v in zip(p,p[1:]))
    # Integer arithmetic on every chord length; conservative upper rounded
    # to micrometres. No host floating-point rounding is part of the proof.
    from math import isqrt
    def up(u,v):
        n=10**12*sum((x-y)**2 for x,y in zip(u,v))
        d=isqrt(n)
        return d+int(d*d!=n)
    return dict(up_um=2*sum(up(u,v) for u,v in zip(p,p[1:])),polyline=p)

def run():
    opts=json.loads(Path(sys.argv[3]).read_text().splitlines()[-1])
    survey.verify();T,poses,typ,tt=survey.source()
    domain=set(ride.read_lut(set(poses)));m=survey.Map(T,[])
    results={}
    for label,keys,closed in (
       ("A",("103/105","105/107","107/118","118/132"),(118,132)),
       ("B",("103/104","104/117","117/132"),(117,132))):
        m.fences=[ride.closures[closed]]
        q=[]
        for key in keys:
            seq=[tuple(p) for p in opts["legs"][key][1][-1]]
            assert not q or q[-1]==seq[0]
            q+=seq if not q else seq[1:]
        results[label]=plan(m,q,domain)
        print(label,results[label]["up_um"],file=sys.stderr,flush=True)
    print(json.dumps(results,sort_keys=True))
if __name__=="__main__":run()
