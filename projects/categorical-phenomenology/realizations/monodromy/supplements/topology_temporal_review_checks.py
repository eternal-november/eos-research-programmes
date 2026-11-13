from pathlib import Path
import numpy as np,json
rng=np.random.default_rng(20261103)
def helmert(m):
 A=np.zeros((m,m-1))
 for i in range(m-1):
  A[:i+1,i]=1/np.sqrt((i+1)*(i+2)); A[i+1,i]=-(i+1)/np.sqrt((i+1)*(i+2))
 return A
def simplex(d): return np.sqrt((d+1)/d)*helmert(d+1)
def basis(d,r): return np.linalg.qr(rng.normal(size=(d,r)))[0][:,:r]
out=dict(cases=0,max_intertwiner_error=0.,max_moment_error=0.,max_word_error=0.,max_sum_error=0.,max_preparation_error=0.,min_kernel_entry=1.,max_memory_error=0.)
for n in range(1,8):
 m=n+1; A=helmert(m); eps=1/(4*m); tau=gamma=1/(16*n*n); Lam=1/(16*n)
 for r in range(1,n+1):
  for s in range(r,n+1):
   for _ in range(5):
    E=A@basis(n,r); K=basis(s,r); j=K@E.T
    vg=simplex(s)@j; vl=simplex(r)@E.T/(2*n)
    def bg(w): return (1+s*w@j.T@simplex(s).T)/(s+1)
    def bl(w): return (1+(r*2*n)*w@E@simplex(r).T)/(r+1)
    t=tau*(E@rng.normal(size=r)); t*=tau/np.linalg.norm(t)
    lam=Lam*rng.uniform(-1,1)
    L=bg(vl); ng=[]; nl=[]
    for y in range(m):
     def native(v,b):
      e=1/m+eps*v[:,y]; f=t+lam*v/(m*e[:,None]); return e[:,None]*b(f)
     G=native(vg,bg); M=native(vl,bl); ng.append(G);nl.append(M)
     out['max_intertwiner_error']=max(out['max_intertwiner_error'],float(np.max(np.abs(M@L-L@G))))
     out['min_kernel_entry']=min(out['min_kernel_entry'],float(M.min()),float(G.min()))
     expected_moment=(1/m+eps*vg[:,y])[:,None]*t+lam*vg/m
     out['max_moment_error']=max(out['max_moment_error'],float(np.max(np.abs(G@vg-expected_moment))))
    out['max_sum_error']=max(out['max_sum_error'],float(np.max(np.abs(sum(ng).sum(1)-1))),float(np.max(np.abs(sum(nl).sum(1)-1))))
    z=gamma*E@E.T@A[:,0]; pg=bg(z);pl=bl(z)
    out['max_preparation_error']=max(out['max_preparation_error'],float(np.max(np.abs(pl@L-pg))))
    q=1.;zz=z.copy()
    for step in range(10):
     y=int(rng.integers(m));pg=pg@ng[y];pl=pl@nl[y]
     newq=q/m+eps*zz[y]; zz=newq*t+lam*zz/m; q=newq
     out['max_word_error']=max(out['max_word_error'],abs(float(pg.sum()-q)),abs(float(pl.sum()-q)))
    # The outcome-summed hold dynamics is z -> Lam*z; refresh acts after output.
    def hold_native(v,b,lam):
     ans=np.zeros((len(v),len(v)))
     for y in range(m):
      e=1/m+eps*v[:,y]; f=lam*v/(m*e[:,None]);ans+=e[:,None]*b(f)
     return ans
    ph=bg(z)
    Nh=hold_native(vg,bg,Lam); Nr=hold_native(vg,bg,0)
    for step in range(6):
     out['max_memory_error']=max(out['max_memory_error'],float(np.max(np.abs(ph@vg-(Lam**step)*z))))
     ph=ph@Nh
    out['max_memory_error']=max(out['max_memory_error'],float(np.max(np.abs((bg(z)@Nr)@vg))))
    out['cases']+=1
for k,v in out.items():
 if k.startswith('max_'):assert v<1e-12,(k,v)
assert out['min_kernel_entry']>0
with open(str(Path(__file__).resolve().with_name('topology_temporal_review_checks.json')),'w') as f:json.dump(out,f,indent=2)
print(json.dumps(out,indent=2))
