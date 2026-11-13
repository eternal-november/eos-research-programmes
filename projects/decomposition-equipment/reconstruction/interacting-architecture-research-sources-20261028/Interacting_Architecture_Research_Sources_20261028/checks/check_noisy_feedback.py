"""Small exhaustive arithmetic checks, not a proof or discovery experiment."""
import numpy as np
from itertools import product

def rank(a):
 a=np.array(a,dtype=np.uint8).copy(); r=0
 for j in range(a.shape[1]):
  inds=np.where(a[r:,j])[0]
  if not len(inds): continue
  q=r+inds[0]; a[[r,q]]=a[[q,r]]
  for t in range(a.shape[0]):
   if t!=r and a[t,j]: a[t]^=a[r]
  r+=1
  if r==a.shape[0]: break
 return r
for k in [2,4,5,7,8]:
 n=4*k; P=np.roll(np.eye(n,dtype=np.uint8),1,axis=1)
 A=(np.eye(n,dtype=np.uint8)+P+P@P)%2
 assert rank(A)==n
 for S in [list(range(2*k)),list(range(k,3*k)),list(range(k))]:
  T=[i for i in range(n) if i not in S]
  assert rank(A[np.ix_(S,T)])==2
 S=list(range(0,n,2)); T=list(range(1,n,2))
 assert rank(A[np.ix_(S,T)])==2*k
 print('ring',n,'invertible; contiguous cuts rank2; parity cut rank',2*k)
n=4
B=np.array([[1,1,0,1],[0,1,1,0],[0,0,1,1],[0,0,0,1]],dtype=np.uint8)
assert rank(B)==n
states=np.array(list(product([0,1],repeat=n)),dtype=np.uint8)
p=np.array([.11,.17,.23,.31]); bias=1-2*p
phi=np.prod(np.where((states@B)%2,bias,1.),axis=1)
L=np.log(phi)
chars=1-2*((states.astype(int)@states.T.astype(int))%2)
coeff=chars@L/(2**n)
for idx,v in enumerate(states):
 matches=[j for j in range(n) if np.array_equal(v,B[:,j])]
 if not v.any(): assert np.isclose(coeff[idx],np.log(bias).sum()/2)
 elif matches: assert np.isclose(coeff[idx],-np.log(bias[matches[0]])/2)
 else: assert abs(coeff[idx])<1e-12
print('log Fourier support/coefficients verified for hidden mixing n=4')
