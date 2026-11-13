import itertools,json,math
from pathlib import Path
OUT=Path(__file__).parent

def comp(f,g): return tuple(f[g[i]] for i in range(len(f)))
def canon(sig):
 d={}; return tuple(d.setdefault(v,len(d)) for v in sig)
def closure(k):
 e=tuple(range(k)); a=(k-1,1,1)+tuple(range(2,k-1)); b=(1,2)+tuple(1 for _ in range(k-2)); seen={e}; todo=[e]
 while todo:
  x=todo.pop()
  for g in (a,b):
   y=comp(g,x)
   if y not in seen: seen.add(y);todo.append(y)
 return sorted(seen),e,a,b
results=[]
for k in range(4,13):
 M,e,a,b=closure(k); idx={x:i for i,x in enumerate(M)}; mul=[[idx[comp(x,y)] for y in M] for x in M]; n=len(M)
 H={e,b,comp(b,b)}; P=canon([x in H for x in M]); inv=[[] for _ in M]
 for i in range(n):
  for j in range(n): inv[mul[i][j]].append((i,j))
 def c(P): return canon([(P[i],tuple(sorted({(P[u],P[v]) for u,v in inv[i]}))) for i in range(n)])
 def s(P): return canon([(P[i],tuple(P[mul[g][i]] for g in range(n)),tuple(P[mul[i][g]] for g in range(n))) for i in range(n)])
 def sat(fun,P):
  steps=0
  while True:
   Q=fun(P)
   if Q==P:return P,steps
   P=Q;steps+=1
 Q,rounds=sat(c,P); SP,_=sat(s,P); both,br=sat(lambda x:s(c(x)),P)
 assert n==3*k-2 and SP==P and len(set(Q))==k and rounds==max(2,math.ceil(math.log2(k-2))) and len(set(both))==n
 assert Q[idx[e]]==Q[idx[b]] and Q[idx[a]]!=Q[idx[comp(a,b)]]
 def power(x,i):
  y=e
  for _ in range(i): y=comp(y,x)
  return y
 height={}
 for i in range(k):
  height[power(a,i)]=i; height[comp(b,power(a,i))]=i
 for i in range(k-2):height[comp(comp(b,b),power(a,i))]=i
 assert all((Q[i]==Q[j])==(height[x]==height[y]) for i,x in enumerate(M) for j,y in enumerate(M))
 if k==4:
  outputs=[a,comp(b,a)]; parents=[]
  for x in outputs:
   parents.append({u for u in M if height[u]==1 and any(comp(u,v)==x for v in H)})
  assert parents[0]=={a} and parents[1]=={comp(b,a)} and not (parents[0]&parents[1])
 results.append(dict(k=k,size=n,cut_classes=len(set(Q)),strict_cut_rounds=rounds,combined_classes=len(set(both)),multiplication_seed_stable=True))
# Independently reconstruct the permutation lemma needed by F3 Theorem 2.
perm_counts={}
for n in range(8):
 count=0
 for p in itertools.permutations(range(n)):
  adj=[set() for _ in p]
  for i in range(n):
   for j in range(i+1,n):
    if p[i]>p[j]:adj[i].add(j);adj[j].add(i)
  seen=set()
  for start in range(n):
   if start in seen:continue
   C={start}; todo=[start];seen.add(start)
   while todo:
    u=todo.pop()
    for v in adj[u]:
     if v not in seen:seen.add(v);C.add(v);todo.append(v)
   assert C==set(range(min(C),max(C)+1)) and {p[i] for i in C}==C
  count+=1
 perm_counts[n]=count
out={'scope':'Independent no-author-import finite falsification of selected residuals. Cut signatures are binary/positive-vertex; no zero-vertex unit test is included. Not unrestricted proofs, novelty, or H2 reproduction.','monoids':results,'joint_branch_k4':'Each output admits required marginal factor, but no shared index-one parent for (A1,B1); (A1,A1) has a shared parent.','f3_permutation_lemma_counts':perm_counts,'passed':True}
(OUT/'independent_residual_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
