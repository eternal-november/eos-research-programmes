"""16-state exact QA of persistent-source residual covariance identity.
Self-copy site fixture isolates the lemma; general two-parent proof is symbolic.
"""
import numpy as np,json
from itertools import product
from pathlib import Path
E=np.array(list(product([0.,1.],repeat=3)))
p=82/95;q=.5;r=1-q;delta=1/380;lam=.6
base=2**(E.sum(1)+E[:,0]*E[:,1]+E[:,0]*E[:,2]+E[:,1]*E[:,2])/95
sgn=(-1)**E.sum(1)
K=np.zeros((16,16));W=np.zeros_like(K)
for a,x in enumerate(E):
 for h in range(2):
  row=2*a+h;hs=2*h-1
  probs=q*x+r*E
  for b,y in enumerate(E):
   prob=float((base+delta*hs*sgn)@np.prod(np.where(y,probs,1-probs),axis=1))
   w=float(np.prod(y-(q*x+r*p)))
   for hn in range(2):
    K[row,2*b+hn]=prob*((1+lam)/2 if hn==h else (1-lam)/2)
    W[row,2*b+hn]=w
pi=np.ones(16)/16
for _ in range(300):pi=pi@K
B=K*W;one=np.ones(16);mean=float(pi@B@one)
results={}
for h in [1,2,3,6]:
 actual=float(pi@B@np.linalg.matrix_power(K,h-1)@B@one-mean*mean)
 expected=r**6*delta**2*lam**h
 results[str(h)]={'actual':actual,'expected':expected,'error':abs(actual-expected)}
 assert abs(actual-expected)<1e-15
report={'fixture':'3 self-copy bits and one persistent binary source; verifies residual temporal identity independently of multi-parent theorem', 'lambda':lam,'delta':delta,'residual_covariances':results}
Path(__file__).with_name('Persistent_Interface_QA.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
