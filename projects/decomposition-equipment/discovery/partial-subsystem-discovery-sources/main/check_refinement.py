import itertools,json
import numpy as np
from pathlib import Path

def refine(F, initial):
    p=initial
    history=[]
    while True:
        blocks=sorted(set(p)); T=np.stack([F[:,:,:,np.array(p)==b].sum(-1) for b in blocks],-1)
        gap=float(np.max(abs(T[:,:,0]-T[:,:,1])))
        history.append({'blocks':len(blocks),'hidden_effect_gap':gap})
        if gap>1e-10:return None,history
        sig=[(p[x],tuple(np.round(T[x,:,0,:].flatten(),12))) for x in range(len(p))]
        unique={};new=[]
        for t in sig:
            if t not in unique:unique[t]=len(unique)
            new.append(unique[t])
        if all((p[x]==p[y])==(new[x]==new[y]) for x in range(len(p)) for y in range(len(p))):return new,history
        p=new

def partitions(n):
    def rec(p):
        if len(p)==n:yield p;return
        for b in range(max(p)+2):yield from rec(p+[b])
    yield from rec([0])

def valid(F,p):
    blocks=sorted(set(p));T=np.stack([F[:,:,:,np.array(p)==b].sum(-1) for b in blocks],-1)
    if np.max(abs(T[:,:,0]-T[:,:,1]))>1e-10:return False
    return all(p[x]!=p[y] or np.max(abs(T[x]-T[y]))<1e-10 for x in range(len(p)) for y in range(len(p)))

states=list(itertools.product(range(2),repeat=3));ws=list(itertools.product(range(2),repeat=2))
F=np.zeros((8,4,2,8))
for ix,(a,b,y) in enumerate(states):
 for iw,(v,vprev) in enumerate(ws):
  for z in range(2):
   probs=[.1+.1*a+.15*b+.2*vprev+.05*a*b,.15+.1*b+.2*a+.15*v+.05*a*v,.1+.1*y+.1*a+.1*v+.4*z]
   for j,st in enumerate(states):F[ix,iw,z,j]=np.prod([p if bit else 1-p for bit,p in zip(st,probs)])
assert np.allclose(F.sum(-1),1) and F.min()>0
p,hist=refine(F,[x[0] for x in states]);assert len(set(p))==4
assert all((p[i]==p[j])==(states[i][:2]==states[j][:2]) for i in range(8) for j in range(8))
count=0;checked=0
for q in partitions(8):
 if any(q[i]==q[j] and states[i][0]!=states[j][0] for i in range(8) for j in range(8)):continue
 checked+=1
 if valid(F,q):
  count+=1;assert all(q[i]!=q[j] or p[i]==p[j] for i in range(8) for j in range(8))
# Unequal fibers: singleton A and double B, hidden mode changes only conditional B detail.
G=np.zeros((3,1,2,3))
for x in range(3):
 for z in range(2):
  r=.3 if x==0 else .6;G[x,0,z]=[r,(1-r)*(.2+.5*z),(1-r)*(.8-.5*z)]
u,uh=refine(G,[0,1,1]);assert u==[0,1,1]
# Marginal robustness without joint robustness.
J=np.zeros((4,1,2,4));ss=list(itertools.product(range(2),repeat=2))
for x in range(4):
 for z in range(2):
  t=.2+.5*z
  for j,(a,b) in enumerate(ss):J[x,0,z,j]=.5*(t if a!=b else 1-t)
pa,_=refine(J,[s[0] for s in ss]);pb,_=refine(J,[s[1] for s in ss]);pj,jh=refine(J,list(range(4)))
assert pa is not None and pb is not None and pj is None
out={'status':'PASS','nonlinear_refinement_history':hist,'task_preserving_partitions_exhaustively_checked':checked,'valid_partitions':count,'unequal_fiber_history':uh,'joint_obstruction':jh,'scope':'Exact known response-kernel algorithm QA; not sensor calibration or finite-sample inference.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
