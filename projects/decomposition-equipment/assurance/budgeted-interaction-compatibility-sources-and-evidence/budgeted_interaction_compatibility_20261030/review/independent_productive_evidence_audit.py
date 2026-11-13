"""Independent causal policy and frozen-prior exhaustive scheduling audit."""
from itertools import product
from functools import lru_cache
from pathlib import Path
import json
BASE=Path(__file__).resolve().parents[1]
N=[{1,2},{0,3},{0,3},{1,2}]
W=[p for p in product(*[(-1,*sorted(n)) for n in N]) if all(j==-1 or p[j]!=i for i,j in enumerate(p))]
J=[((0,1),2,5),((0,2),4,7),((1,3),6,9)]
def choose(t,obs):
 fixed={0:(-1,-1),1:(-1,-1),2:(1,0),3:(-1,-1),4:(0,0),5:(0,1),9:(-1,-1)}
 if t in fixed:return fixed[t]
 edge02=obs[5][2]==2;edge13=obs[3][3]==2
 if edge02:return {6:(3,2),7:(2,1),8:(1,2)}[t]
 if not edge13:return {6:(2,1),7:(1,2),8:(3,2)}[t]
 return {6:(2,1),7:(3,2),8:(1,2)}[t]
paths=[]
for p in W:
 prev=(0,)*4;obs={};used=[set() for _ in J];times=[[] for _ in J];energy=0;path=[]
 for t in range(10):
  a,j=choose(t,obs);u=tuple(2 if i==a else 0 for i in range(4))
  x=tuple(u[i]+(0 if p[i]==-1 else prev[p[i]]) for i in range(4))
  assert max(x)<=3 and sum(u)<=2;energy+=sum(u)
  if j!=-1:
   nodes,rel,deadline=J[j]
   assert rel<=t<=deadline and a in nodes and a not in used[j]
   used[j].add(a);times[j].append(t)
  else:assert a==-1
  obs[t]=x;prev=u;path.append(a)
 assert all(used[i]==set(J[i][0]) for i in range(3)) and energy==12 and prev==(0,)*4
 paths.append({'world':p,'path':path,'stage_times':times})
@lru_cache(None)
def frozen(t,prev,done):
 if all(done[i]==3 for i in range(3)):return True
 if t>9:return False
 if any(t>J[i][2] and done[i]!=3 for i in range(3)):return False
 if frozen(t+1,-1,done):return True
 for j,(nodes,r,d) in enumerate(J):
  if not r<=t<=d:continue
  for b,a in enumerate(nodes):
   if done[j]>>b&1:continue
   if prev!=-1 and prev in N[a]:continue
   nxt=list(done);nxt[j]|=1<<b
   if frozen(t+1,a,tuple(nxt)):return True
 return False
assert len(W)==47 and not frozen(2,-1,(0,0,0))
for prev,a in product(range(4),repeat=2):
 safe=all(2+(2 if p[a]==prev else 0)<=3 for p in W)
 assert safe==(prev not in N[a])
result={'status':'PASS','world_count':len(W),'causal_policy_all_worlds_win':True,'energy_per_world':12,'diagnostic_energy':0,'frozen_prior_win':False,'frozen_dp_states':frozen.cache_info().currsize,'stage_credit_checks':len(W)*6,'frozen_transition_pair_checks':16,'paths':paths}
(BASE/'review/independent_productive_evidence_audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='paths'},indent=2))
