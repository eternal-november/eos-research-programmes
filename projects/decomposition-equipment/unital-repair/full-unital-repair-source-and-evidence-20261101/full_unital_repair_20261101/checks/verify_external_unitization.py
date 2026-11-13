#!/usr/bin/env python3
"""Independent unary full-unital modular negative control.
External unitization is essential: the old identity is now a nonunit.
"""
from itertools import product
from pathlib import Path
from hashlib import sha256
import json

class Failure(RuntimeError):pass
def require(condition,message):
 if not condition:raise Failure(message)
def comp(f,g):return tuple(f[i] for i in g)
def canonical(keys):
 d={};return tuple(d.setdefault(k,len(d)) for k in keys)
def sstep(m,p):return canonical((p[x],tuple(p[y] for y in m[x]),tuple(p[row[x]] for row in m)) for x in range(len(m)))
def cstep(m,e,p):
 sig=[set() for _ in p]
 for a,row in enumerate(m):
  for b,x in enumerate(row):sig[x].add((p[a],p[b]))
 return canonical((p[x],x==e,frozenset(sig[x])) for x in range(len(m)))

def main():
 K=((0,0,0),(0,0,2),(0,1,2),(0,2,0),(2,0,2),(2,1,2),(2,2,0),(2,2,2))
 ix={x:i for i,x in enumerate(K)};old=tuple(tuple(ix[comp(a,b)] for b in K) for a in K)
 # Faithful left-regular action on old K plus extra point * indexed8.
 lifted=tuple(tuple(old[a])+(a,) for a in range(8))
 actual=lifted+(tuple(range(9)),);jx={x:i for i,x in enumerate(actual)}
 m=tuple(tuple(jx[comp(a,b)] for b in actual) for a in actual);e=8
 require(len(set(actual))==9,'faithful nine-element transformation monoid')
 require(all(m[a][b]==old[a][b] for a,b in product(range(8),repeat=2)),'old multiplication')
 require(all(m[e][a]==a==m[a][e] for a in range(9)),'new unit')
 require(all(m[m[a][b]][c]==m[a][m[b][c]] for a,b,c in product(range(9),repeat=3)),'associativity')
 P=canonical(('new',) if i==e else ('old',i==2) for i in range(9))
 Q=canonical(('new',) if i==e else ('old',i in (2,5)) for i in range(9))
 R=canonical(zip(P,Q))
 for name,p in [('P',P),('Q',Q)]:
  require(sstep(m,p)==p,f'{name} substitution stable')
  require(cstep(m,e,p)==p,f'{name} full-unital cut stable')
 require(sstep(m,R)==R,'intersection substitution stable')
 CR=cstep(m,e,R)
 require(CR!=R,'intersection should fail cut stability')
 require(R[0]==R[1] and CR[0]!=CR[1],'separating source pair')
 require(m[0][5]==0 and all(m[u][5]!=1 for u in range(9)),'right-factor witness')
 result={'status':'Full-unital unary modular negative control passed','domain':'Unary coefficient monoid only; no claim local stability on branching full profiles',
         'old_transformations':K,'new_actual_transformations':actual,'new_unit_index':8,'old_identity_index':2,
         'multiplication':m,'P':P,'Q':Q,'intersection':R,'cut_intersection':CR,
         'block_counts':{'P':len(set(P)),'Q':len(set(Q)),'intersection':len(set(R)),'cut_intersection':len(set(CR))},
         'witness':{'source_same_class':[0,1],'factorization':[0,5],'no_source1_factorization_with_right':5},
         'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
 out=Path(__file__).with_name('external_unitization_results.json');out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'block_counts':result['block_counts']},indent=2))
if __name__=='__main__':main()
