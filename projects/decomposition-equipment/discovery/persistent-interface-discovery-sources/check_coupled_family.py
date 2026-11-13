"""Small exact algebra checks; not a substitute for the general proofs."""
import json, math
import numpy as np

def rank(a):
 a=np.array(a,dtype=np.uint8).copy(); k=0
 for j in range(a.shape[1]):
  ids=np.where(a[k:,j])[0]
  if not len(ids): continue
  i=k+ids[0]; a[[k,i]]=a[[i,k]]
  for h in range(a.shape[0]):
   if h!=k and a[h,j]: a[h]^=a[k]
  k+=1
  if k==a.shape[0]: break
 return k

def comps(a):
 n=len(a); seen=set(); out=[]
 for i in range(n):
  if i in seen: continue
  block={i}; todo=[i]; seen.add(i)
  while todo:
   u=todo.pop()
   for v in np.where(a[u]|a[:,u])[0]:
    v=int(v)
    if v not in seen: seen.add(v); block.add(v); todo.append(v)
  out.append(block)
 return out

results=[]
R=np.array([[1,1],[0,0]],dtype=np.uint8); S=np.array([[0,1],[1,0]],dtype=np.uint8)
for m in range(3,9):
 n=2*m*m; A=[np.zeros((n,n),dtype=np.uint8) for _ in range(3)]; A[2]=np.eye(n,dtype=np.uint8)
 def ix(i,j): return 2*((i%m)*m+j%m)
 for i in range(m):
  for j in range(m):
   t=ix(i,j)
   for a in A[:2]: a[t:t+2,t:t+2]^=S
   for delta in [-1,1]:
    v=ix(i,j+delta); A[0][t:t+2,v:v+2]^=R
    v=ix(i+delta,j); A[1][t:t+2,v:v+2]^=R
 P,Q=comps(A[0]),comps(A[1]); assert len(P)==len(Q)==m
 assert all(len(p&q)==2 for p in P for q in Q)
 hs=[]; ks=[]
 for block in [P[0],Q[0]]:
  ins=sorted(block); outs=sorted(set(range(n))-block)
  D=[a[np.ix_(outs,ins)] for a in A]; zero=np.zeros_like(D[0])
  H=np.block([[D[i+j] if i+j<3 else zero for j in range(3)] for i in range(3)])
  hs.append(rank(H)); ks.append(rank(np.concatenate(D,axis=1)))
 assert hs==[2*m,m] and ks==[m,m]
 assert max(np.concatenate(A,axis=1).sum(axis=1))==11
 results.append(dict(m=m,n=n,row_Hankel_rank=hs[0],column_Hankel_rank=hs[1],influence_rank=m))
# Bounded-width shifted-matching chain checks.
chain_checks=[]
for k in range(6,15):
 n=2*k; A=[np.zeros((n,n),dtype=np.uint8) for _ in range(3)]; A[2]=np.eye(n,dtype=np.uint8)
 for j in range(k):
  for a in A[:2]: a[2*j:2*j+2,2*j:2*j+2]^=S
 for lag,start in [(0,0),(1,1)]:
  for j in range(start,k-1,2):
   A[lag][2*j:2*j+2,2*j+2:2*j+4]^=R
   A[lag][2*j+2:2*j+4,2*j:2*j+2]^=R
 P,Q=comps(A[0]),comps(A[1]); assert max(map(len,P+Q))==4
 assert len(comps(A[0]|A[1]))==1
 assert max(np.concatenate(A,axis=1).sum(axis=1))==7
 chain_checks.append(dict(sites=k,n=n,max_region_bits=4,connected=True))
# Exact local ICA characteristic/Walsh check, including equal biases.
M=np.array([[1,1,0],[0,1,1],[0,0,1]],dtype=np.uint8); alpha=[.17,.17,.11]; q=3
vec=[np.array([(s>>j)&1 for j in range(q)],dtype=np.uint8) for s in range(2**q)]
g=[]
for s in vec:
 exps=(s@M)%2; g.append(sum(math.log(alpha[j])*int(exps[j]) for j in range(q)))
coeff=[sum(g[s]*((-1)**int((vec[s]@v)%2)) for s in range(2**q))/(2**q) for v in vec]
expected={sum(int(M[i,j])<<i for i in range(q)):-math.log(alpha[j])/2 for j in range(q)}
for v in range(1,2**q): assert abs(coeff[v]-expected.get(v,0))<1e-12
out={'torus_checks':results,'chain_checks':chain_checks,'ICA_equal_bias_check':'passed','scope':'exact finite algebra only; no statistical experiment'}
print(json.dumps(out,indent=2))
