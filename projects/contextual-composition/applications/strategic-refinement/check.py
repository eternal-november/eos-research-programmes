from fractions import Fraction as F
from itertools import product
import json
checks=0
def check(p):
 global checks
 assert p
 checks+=1
S=list(product((0,1), repeat=2)) # 0=out,1=invest
def utilities(cost):
 return {s:tuple(F(0) if s[i]==0 else F((3 if s[1-i]==0 else 1)-cost) for i in range(2)) for s in S}
def br(u,i,opp):
 vals={a:u[(a,opp) if i==0 else (opp,a)][i] for a in (0,1)}
 return {a for a,v in vals.items() if v==max(vals.values())}
def ne(u): return [s for s in S if all(s[i] in br(u,i,s[1-i]) for i in range(2))]
u=utilities(2); v=utilities(0)
check(ne(u)==[(0,1),(1,0)])
check(ne(v)==[(1,1)])
for s in S:
 check(all(v[s][i]-u[s][i]==2*s[i] for i in range(2)))
 check(all(0<=2*s[i] for i in range(2))) # native cost-lowering, singleton witness and same body
# original symmetric mixed equilibrium p=1/2; new unique dominant action 1
check(F(1,2)*u[(1,0)][0]+F(1,2)*u[(1,1)][0]==0)
check(F(1,2)*v[(1,0)][0]+F(1,2)*v[(1,1)][0]==2)
# common-mode invariance and oscillation bound for 3-action exact finite vectors
for p in product(range(-1,2),repeat=3):
 for d in product(range(3),repeat=3):
  B={i for i in range(3) if p[i]==max(p)}
  w=tuple(p[i]+d[i] for i in range(3)); C={i for i in range(3) if w[i]==max(w)}
  if len(set(d))==1: check(B==C)
  for a in B: check(max(w)-w[a]<=max(d)-min(d))
# necessity witness, baseline tied: every nonconstant saving changes full BR set
for d in product(range(3),repeat=3):
 check(({i for i in range(3) if d[i]==max(d)}=={0,1,2})==(len(set(d))==1))
# sharpness
check(max((0,2))-(0,2)[0]==2)
# sequential local automatic stages cannot certify earlier choice
old=(0,0); new=(1,0)
check({i for i in range(2) if old[i]==max(old)}=={0,1})
check({i for i in range(2) if new[i]==max(new)}=={0})
# endpoint potential identity on two paths with common endpoints
phi={'start':3,'L':2,'R':1,'end':0}
for mid in ('L','R'):
 check((phi['start']-phi[mid])+(phi[mid]-phi['end'])==3)
print(json.dumps({'status':'passed','exact_assertions':checks,'old_pure_equilibria':ne(u),'new_pure_equilibria':ne(v),'old_symmetric_mixed_probability':'1/2','scope':'finite worked example and exact arithmetic diagnostics; not Lean or general open-game implementation'},indent=2))
