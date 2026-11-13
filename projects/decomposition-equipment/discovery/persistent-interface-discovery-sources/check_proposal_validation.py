import itertools,json,numpy as np

def rank(a):
 a=a.copy(); k=0
 for j in range(a.shape[1]):
  cand=np.where(a[k:,j])[0]
  if not len(cand):continue
  h=k+cand[0];a[[h,k]]=a[[k,h]]
  for h in range(len(a)):
   if h!=k and a[h,j]:a[h]^=a[k]
  k+=1
  if k==len(a):break
 return k
alpha=np.array([.2,.4,.6]); tested=0;passcount=0
for bits in itertools.product([0,1],repeat=9):
 Q=np.array(bits,dtype=np.uint8).reshape(3,3)
 if rank(Q)!=3:continue
 tested+=1
 phi=lambda s: float(np.prod(alpha[np.array(s,dtype=bool)]))
 cov=[phi(Q[i]^Q[j])-phi(Q[i])*phi(Q[j]) for i in range(3) for j in range(i)]
 accepted=all(abs(c)<1e-12 for c in cov)
 permutation=all(Q.sum(axis=0)==1) and all(Q.sum(axis=1)==1)
 assert accepted==permutation
 passcount+=accepted
# Finite exact uniform-character orthogonality underlying row validation.
for w in range(1,8):
 for mask in range(1,2**w):
  assert sum((-1)**((mask&x).bit_count()%2) for x in range(2**w))==0
print(json.dumps({'invertible_3bit_candidates':tested,'passing_permutations':passcount,'uniform_wrong_parity_checks':'passed for widths 1..7','scope':'finite algebra regression, not empirical identifiability proof'},indent=2))
