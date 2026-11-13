"""Exact small-case independent checks; not a proof, finite-data experiment, or novelty claim."""
from itertools import product
from fractions import Fraction as F

def dot(a,b): return (a&b).bit_count()%2
def mat(A,x): return sum(dot(a,x)<<i for i,a in enumerate(A))
def rank(A):
 b={}
 for x in A:
  while x:
   j=x.bit_length()-1
   if j in b:x^=b[j]
   else:b[j]=x;break
 return len(b)
def kernel(A,B,p):
 n=len(A); out=[]
 for y in range(1<<n):
  row=[F(0)]*(1<<n)
  for e in range(1<<n):
   prob=F(1)
   for j in range(n):prob*=p[j] if e>>j&1 else 1-p[j]
   row[mat(A,y)^mat(B,e)]+=prob
  out.append(tuple(row))
 return tuple(out)
# Certificate: all 168 invertible frames, both exact and erroneous dynamic row choices.
n=3; A=(6,1,2); B=(3,6,4); p=(F(1,10),F(1,5),F(3,10))
assert rank(A)==rank(B)==3
# Here use observed M=A and eta=B xi; latent A is conjugate, still invertible.
K=kernel(A,B,p)
means={(w,v):sum(K[y][z]*(-1)**(dot(w,z)^dot(v,y)) for y in range(8) for z in range(8))/8 for w in range(8) for v in range(8)}
def transpose_on(w):return sum(dot(w,mat(A,1<<j))<<j for j in range(3))
accepted=0
for W in product(range(1,8),repeat=3):
 if rank(W)!=3:continue
 V=tuple(transpose_on(w) for w in W)
 mus=[means[w,v] for w,v in zip(W,V)]
 covs=[means[W[i]^W[j],V[i]^V[j]]-mus[i]*mus[j] for i in range(3) for j in range(i)]
 passed=min(mus)>=F(2,5) and all(c==0 for c in covs)
 WB=tuple(sum(dot(w,mat(B,1<<j))<<j for j in range(3)) for w in W)
 assert passed==(set(WB)=={1,2,4})
 accepted+=passed
 for w in W:
  assert all(means[w,v]==0 for v in range(8) if v!=transpose_on(w))
assert accepted==6
# Uniform axis U=<e0>, biased axes quotient e1,e2. All lifts and all invertible
# observed dynamics sharing rows 1,2 give exactly same transition law.
p=(F(1,2),F(1,5),F(3,10)); ref=None; fibers=0
for l1,l2 in product(range(2),repeat=2):
 B=(1|(l1<<1)|(l2<<2),2,4)
 for first in range(8):
  M=(first,1,2)
  if rank(M)!=3:continue
  K=kernel(M,B,p)
  if ref is None:ref=K
  assert K==ref
  fibers+=1
assert fibers==16
# All nonempty proper blocks, deleting uniform output row, exact image count.
for a in range(8):
 A=(a,1,2)
 if rank(A)!=3:continue
 for S in range(1,7):
  outside=7^S
  R=[i for i in range(1,3) if S>>i&1]
  rows=[A[i]&outside for i in R]
  images={tuple(dot(r,x) for r in rows) for x in range(8) if x&S==0}
  assert len(images)==2**rank(rows)
print('PASS: all 168 frames; exactly six certified permutations; all wrong dynamic residual means zero.')
print('PASS: all 16 uniform-noise lifts/dynamic completions have identical full kernels; interface image counts.')
