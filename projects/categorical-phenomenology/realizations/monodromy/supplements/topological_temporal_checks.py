from pathlib import Path
"""Numerical checks of Section 12. No topology/novelty certification."""
import numpy as np,json
from scipy.linalg import null_space
rng=np.random.default_rng(103112)
m=4;n=3;r=2;s=3;eps=1/(4*m);gamma=tau=1/(16*n*n);Lam=1/(16*n)
A=null_space(np.ones((1,m)))
ZG=np.sqrt(4/3)*A.T # regular tetrahedron columns in R^3
ZL=np.sqrt(3/2)*null_space(np.ones((1,3))).T # regular triangle columns in R^2
mx={};minval=1.
def chk(name,a,b):
 e=float(np.max(np.abs(np.asarray(a)-np.asarray(b))));mx[name]=max(mx.get(name,0),e)
 if e>1e-11: raise AssertionError((name,e))
for sample in range(100):
 x=rng.normal(size=3);x/=np.linalg.norm(x);P=np.eye(3)-np.outer(x,x)
 F=null_space(x.reshape(1,3))
 vG=P@ZG;Rloc=1/(2*n);vL=Rloc*F@ZL
 bg=lambda z:(1+s*ZG.T@z)/(s+1)
 bl=lambda z:(1+(r/Rloc)*ZL.T@F.T@z)/(r+1)
 L=np.stack([bg(vL[:,i]) for i in range(r+1)])
 chk('link_rows',L.sum(axis=1),np.ones(r+1));chk('link_moments',L@vG.T,vL.T)
 preps=np.column_stack([np.zeros(3),gamma*P])
 pG=np.stack([bg(preps[:,i]) for i in range(m)])
 pL=np.stack([bl(preps[:,i]) for i in range(m)])
 chk('preparation_link',pL@L,pG)
 acts={'hold':(np.zeros(3),Lam),'refresh':(np.zeros(3),0.),'kick':(tau*P[:,0],Lam),'counterkick':(-tau*P[:,1],-Lam)}
 NG={};NL={};TR={}
 for a,(t,lam) in acts.items():
  NG[a]=[];NL[a]=[];TR[a]=[]
  for y in range(m):
   def native(verts,b):
    rows=[]
    for z in verts.T:
     e=1/m+eps*(A@z)[y]
     f=t+lam*z/(m*e)
     rows.append(e*b(f))
    return np.array(rows)
   G=native(vG,bg);B=native(vL,bl);NG[a].append(G);NL[a].append(B)
   minval=min(minval,float(G.min()),float(B.min()),float(L.min()),float(pG.min()),float(pL.min()))
   chk('statewise_'+a,B@L,L@G)
   def lin(v):
    q=x@v;z=P@v;qp=q/m+eps*(A@z)[y];zp=qp*t+lam*z/m
    return qp*x+zp
   T=np.column_stack([lin(e) for e in np.eye(3)])
   TR[a].append(T)
   RG=x[:,None]+vG
   chk('linear_intertwining_'+a,RG@G.T,T@RG)
  chk('global_stochastic_'+a,sum(NG[a]).sum(axis=1),np.ones(s+1))
  chk('local_stochastic_'+a,sum(NL[a]).sum(axis=1),np.ones(r+1))
 for test in range(20):
  actions=rng.choice(list(acts),size=7);ys=rng.integers(0,m,size=7)
  G=np.eye(s+1);B=np.eye(r+1);T=np.eye(3)
  for a,y in zip(actions,ys): G=G@NG[a][y];B=B@NL[a][y];T=TR[a][y]@T
  pg=pG@G@np.ones(s+1);pl=pL@B@np.ones(r+1);pr=x@T@(x[:,None]+preps)
  chk('seven_step_local_global',pg,pl);chk('seven_step_real_positive',pg,pr)
 H=np.column_stack([pG@NG['hold'][y]@np.ones(s+1) for y in range(m)])
 target=np.vstack([np.ones(m)/m,np.ones((n,m))/m+eps*gamma*P@A.T])
 chk('first_read_table',H,target)
 assert np.linalg.matrix_rank(H,tol=1e-12)==3
assert minval>0
res={'status':'passed','samples':100,'minimum_native_probability_or_kernel_entry':minval,'max_errors':mx,'scope':'numeric checks only; displayed algebra and bundle proofs carry theorem'}
print(json.dumps(res,indent=2));open(str(Path(__file__).resolve().with_name('topological_temporal_checks_results.json')),'w').write(json.dumps(res,indent=2)+'\n')
