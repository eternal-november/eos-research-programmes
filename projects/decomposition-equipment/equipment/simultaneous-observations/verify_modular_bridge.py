"""Exact finite controls for modular_repair_draft.md; standard library only."""
from itertools import product
K=[(0,0,0),(0,0,2),(0,1,2),(0,2,0),(2,0,2),(2,1,2),(2,2,0),(2,2,2)]
index={x:i for i,x in enumerate(K)}
t=[[index[tuple(f[x] for x in g)] for g in K] for f in K]
P=(0,0,1,0,0,0,0,0)
Q=(0,0,1,0,0,1,0,0)
R=tuple(zip(P,Q))
def congruent(p):
 return all(p[x]!=p[y] or all(p[t[a][x]]==p[t[a][y]] and p[t[x][a]]==p[t[y][a]] for a in range(8)) for x,y in product(range(8),repeat=2))
def cut_signatures(p):
 sig=[set() for _ in K]
 for a,b in product(range(8),repeat=2):sig[t[a][b]].add((p[a],p[b]))
 return sig
def cut_stable(p):
 sig=cut_signatures(p)
 return all(p[x]!=p[y] or sig[x]==sig[y] for x,y in product(range(8),repeat=2))
assert congruent(P) and congruent(Q) and congruent(R)
assert cut_stable(P) and cut_stable(Q) and not cut_stable(R)
assert R[0]==R[1] and (R[0],R[5]) in cut_signatures(R)[0]
assert (R[0],R[5]) not in cut_signatures(R)[1]
assert t[1][1]==1 and (P[1],P[1])==(P[0],P[5])
assert t[1][2]==1 and (Q[1],Q[2])==(Q[0],Q[5])
for name,p in [('P',P),('Q',Q)]:
 for r in (2,3):
  sig={z:set() for z in product(range(8),repeat=r)}
  for a in range(8):
   for bs in product(range(8),repeat=r):
    sig[tuple(t[a][b] for b in bs)].add((p[a],tuple(p[b] for b in bs)))
  x=(0,)*r;y=(0,)*(r-1)+(1,)
  assert tuple(p[i] for i in x)==tuple(p[i] for i in y) and sig[x]!=sig[y]
  print(name,'coordinate partition is NOT common-parent complete at',r,'active inputs')
print('PASS: both local unary optima, combined-cut failure, incompatible matches, and N>1 boundary')
