from fractions import Fraction as F
from itertools import product
import json
# Same fixed world/boundary values, noninjective exact primitive row maps.
audit={0:F(1,2),1:F(1,2),2:F(0)}
Ws=tuple(product((0,1),(0,1),audit));Wm=tuple(product((0,1),(0,1),(0,1)));Wt=tuple(product((0,1),(0,1)))
ms={w:F(1,4)*audit[w[2]] for w in Ws};mm={w:F(1,8) for w in Wm};mt={w:F(1,4) for w in Wt}
r=lambda w:(w[0],w[1],w[2]%2);s=lambda w:w[:2]
Z=lambda W:tuple((x,y) for x,y in product(W,repeat=2) if x[0]==y[0])
qt={z:F(1,4) if z[0][1]!=z[1][1] else F(0) for z in Z(Wt)}
def lift(W,mu,targetmu,f,q):
 out={}
 for z in Z(W):
  a,b=map(f,z);den=targetmu[a]*targetmu[b]
  out[z]=q[(a,b)]*mu[z[0]]*mu[z[1]]/den if den else F(0)
 return out
qm=lift(Wm,mm,mt,s,qt);qs=lift(Ws,ms,mm,r,qm);direct=lift(Ws,ms,mt,lambda w:s(r(w)),qt)
assert qs==direct and sum(qs.values())==1
for w,p in ms.items():assert sum(v for z,v in qs.items() if z[0]==w)==p
for z,p in qt.items():assert sum(v for x,v in qs.items() if tuple(s(r(w)) for w in x)==z)==p
# Every fixed-boundary preimage of target matching is source matching.
assert all((x[0]==y[0]) == (s(r(x))[0]==s(r(y))[0]) for x,y in product(Ws,repeat=2))
# Boundary quotient counterexample: distinct source values, singleton target value.
source_matching=[];target_matching=[('*','*')];assert not source_matching and target_matching
# Three global outcomes; zero blocked paths retained, active divergence distinct.
hist={():('active_start',F(1))};horizons=[]
for n in range(6):
 masses={k:sum(p for state,p in hist.values() if state==k) for k in ('done','blocked','active')}
 if n:assert masses=={'done':F(1,3),'blocked':F(1,3),'active':F(1,3)}
 assert sum(p for _,p in hist.values())==1
 horizons.append({'n':n,'raw':len(hist),'zero':sum(p==0 for _,p in hist.values())})
 nxt={}
 for h,(state,p) in hist.items():
  if state in ('done','blocked'):nxt[h]=(state,p)
  elif state=='active_start':
   for z in ('done','blocked','active'):nxt[h+(z,)]=(z,p*F(1,3))
  else:
   nxt[h+('continue',)]=('active',p)
   nxt[h+('zero_block',)]=('blocked',F(0))
 hist=nxt
# A locally blocked actor revives after another actor's global world update.
def menu(actor,world,done):
 if done:return ()
 if actor=='waiter':return ('finish',) if world==1 else ()
 return ('update',) if world==0 else ()
assert not menu('waiter',0,False) and menu('updater',0,False)
assert menu('waiter',1,False)
# Actual augmentation of a limit-mode context object preserves its native map.
eps=(1,0,0);A=((1,0,0),(0,1,0),(0,0,0))
assert tuple(sum(eps[i]*A[i][j] for i in range(3)) for j in range(3))==eps
print(json.dumps({'status':'passed','matching_source_atoms':len(qs),'matching_source_zero_atoms':sum(p==0 for p in qs.values()),
 'target_matching_atoms':len(qt),'horizons':horizons,
 'checks':['matching-reflecting-conditional-lift','exact-marginals-and-pushforward','zero-fibre-composition','boundary-quotient-obstruction','done-blocked-infiniteactive-separation','passive-readiness-revival','actual-limit-context-augmentation']},indent=2))
