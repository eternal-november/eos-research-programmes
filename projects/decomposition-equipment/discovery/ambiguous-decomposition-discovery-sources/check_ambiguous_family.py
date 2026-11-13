"""Exact small-state numerical QA; proofs do not depend on enumeration."""
import numpy as np, json
from itertools import product
from pathlib import Path
m=3;n=3*m;q1=.3;q2=.2;r=1-q1-q2
X=np.array(list(product([0.,1.],repeat=n)));N=len(X)
E=np.array(list(product([0.,1.],repeat=3)))
w=2**(E.sum(1)+E[:,0]*E[:,1]+E[:,0]*E[:,2]+E[:,1]*E[:,2]);base=w/95
sgn=(-1)**E.sum(1)
p=82/95;v=p*(1-p);c=116/9025
parents1=np.array([l*m+(j-1)%m for l in range(3) for j in range(m)])
parents2=np.array([l*m+(j-2)%m for l in range(3) for j in range(m)])
A=np.zeros((n,n));A[np.arange(n),parents1]=q1;A[np.arange(n),parents2]=q2
bags=[[j,m+j,2*m+j] for j in range(m)]
def build(theta):
    K=np.ones((N,N))
    for b in bags:
        probs=q1*X[:,parents1[b]]+q2*X[:,parents2[b]]
        loc=np.zeros((N,8))
        for e,mass in zip(E,base+theta*sgn):
            z=probs+r*e
            loc+=mass*np.prod(np.where(E[None,:,:],z[:,None,:],1-z[:,None,:]),axis=2)
        out=(X[:,b] @ np.array([4,2,1])).astype(int)
        K*=loc[:,out]
    pi=np.ones(N)/N
    for it in range(200):
        pn=pi@K
        if np.max(abs(pn-pi))<1e-15:break
        pi=pn
    return K,pn,it
K0,pi0,it0=build(0);K1,pi1,it1=build(1/380)
Z=X-p
C0=Z.T@(pi0[:,None]*Z);D0=Z.T@(K0.T@(pi0[:,None]*Z))
# D rows future and columns past.
AA=D0@np.linalg.inv(C0);R=C0-AA@C0@AA.T
pair_path_error=0
for u in range(n):
 for vv in range(u+1,n):
    codes=(2*X[:,u]+X[:,vv]).astype(int)
    ind=np.eye(4)[codes]
    def paths(K,pi):
       return np.array([((pi*ind[:,a])@K*ind[:,b])@K@ind[:,d] for a in range(4) for b in range(4) for d in range(4)])
    pair_path_error=max(pair_path_error,float(np.max(abs(paths(K0,pi0)-paths(K1,pi1)))))
expected_R=np.zeros((n,n))
for b in bags:
 for i in b:
  for j in b:
   if i!=j:expected_R[i,j]=r*r*c
mask=~np.eye(n,dtype=bool)
L=lambda t:float(sgn@np.log(base+t*sgn))
triple0=float(pi0@np.prod(Z[:,bags[0]],axis=1));triple1=float(pi1@np.prod(Z[:,bags[0]],axis=1))
# Conditional residual third moment averaged over the exact transition.
M=p+Z@A.T
W=np.ones((N,N))
for i in bags[0]:W*=X[None,:,i]-M[:,None,i]
wr0=float(np.sum(pi0[:,None]*K0*W));wr1=float(np.sum(pi1[:,None]*K1*W))
report={'fixture':'3 rings of length 3 (reduced finite QA fixture; theorem allows m>=5)',
'row_sum_error':float(max(np.max(abs(K0.sum(1)-1)),np.max(abs(K1.sum(1)-1)))),
'stationarity_iterations':[it0,it1], 'A_recovery_error':float(np.max(abs(AA-A))),
'innovation_edge_residual_error':float(np.max(abs(R[mask]-expected_R[mask]))),
'pair_history_length3_max_error_all_pairs':pair_path_error,
'full_kernel_difference':float(np.max(abs(K1-K0))),
'stationary_triple_difference':triple1-triple0,
'residual_triple_difference':wr1-wr0,'predicted_residual_difference':-r**3/380,
'C_min_eigenvalue':float(np.linalg.eigvalsh(C0)[0]),'proved_lower_bound':r*(v-c),
'loglinear_L0':L(0),'loglinear_Lpositive':L(1/380),
'positive_nonliftable_pair_disagreement_sum':2.25}
assert report['A_recovery_error']<1e-10
assert report['innovation_edge_residual_error']<1e-10
assert pair_path_error<1e-10
assert abs(wr1-wr0+r**3/380)<1e-10
assert report['C_min_eigenvalue']>=report['proved_lower_bound']-1e-10
assert abs(L(0))<1e-10 and L(1/380)>0
Path(__file__).with_name('Ambiguous_Family_QA.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
