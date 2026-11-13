import itertools,json
from pathlib import Path
import numpy as np
hidden_states=list(itertools.product([0,1],repeat=3))
perm=np.random.default_rng(731).permutation(8)
states=[hidden_states[j] for j in perm]
U=np.array([[1.,0.],[-1.,0.],[0.,1.],[0.,-1.]])
Z=np.array([[0,0],[1,0],[-1,0],[0,1],[0,-1]],float)
tau=.75; pi=np.array([1-tau,*([tau/4]*4)])
A=.025*np.array([[1.3,.2],[.1,.85]])
Aj=.025*np.linalg.inv(np.array([[1.3,.2],[.1,.85]])).T
def macro(c,u):
 a,b,y=c;w=np.array([2+a+2*a*b,2+b+u*a,2+(a^b)+u,2+2*(b^u)+a*b],float)
 return w/w.sum(),1+.2*a+.15*b+.1*u*a*b
def raw(c,u,amp):
 a,b,y=c;base,s=macro(c,u); K=[]
 for ap,bp,yp in states:
  d=.2+.1*y+.05*ap+.03*bp+.02*a+.02*b*u
  K.append((base[2*ap+bp]+s*(Z@amp.T@U[2*ap+bp]))*(d if yp else 1-d))
 return np.array(K).T
K=np.array([[raw(c,u,A) for u in [0,1]] for c in states])
assert K.min()>0 and abs(K.sum(axis=-1)-1).max()<1e-12
# Population readout tables. No latent coordinates supplied to partition search.
B=np.einsum('z,xuzy->xuy',pi,K)
J=raw((0,0,0),0,Aj);Bj=pi@J
pair=np.einsum('z,xuzy,zv->xuyv',pi,K,J)
D=pair-np.einsum('xuy,v->xuyv',B,Bj)
task=[x[0] for x in states]
def parts(xs):
 if not xs:yield [];return
 x,*rest=xs
 for p in parts(rest):
  yield [[x]]+[b[:] for b in p]
  for j in range(len(p)):
   q=[b[:] for b in p];q[j]=[x]+q[j];yield q
candidates=[p+q for p in parts([i for i,t in enumerate(task) if t==0]) for q in parts([i for i,t in enumerate(task) if t==1])]
def conditional(p):
 for oldblock in p:
  for x,y in itertools.combinations(oldblock,2):
   for u in [0,1]:
    for target in p:
     if abs(B[x,u,target].sum()-B[y,u,target].sum())>1e-12:return False
     if abs(D[x,u,target].sum(axis=0)-D[y,u,target].sum(axis=0)).max()>1e-12:return False
 return True
def autonomous(p):
 return conditional(p) and all(abs(D[x,u,target].sum(axis=0)).max()<1e-12 for x,u,target in itertools.product(range(8),[0,1],p))
valid=[p for p in candidates if conditional(p)]
minimum=min(map(len,valid));coarsest=[p for p in valid if len(p)==minimum]
assert minimum==4 and len(coarsest)==1
q=coarsest[0]
truth=[{i for i,x in enumerate(states) if x[:2]==(a,b)} for a,b in itertools.product([0,1],repeat=2)]
assert {frozenset(x) for x in q}=={frozenset(x) for x in truth}
assert all(all(any(set(b)<=t for t in truth) for b in p) for p in valid)
assert not any(autonomous(p) for p in candidates)
# Full pointwise stochastic row ground truth verifies learned quotient, including every source value.
for old in q:
 for x,y in itertools.combinations(old,2):
  for u,z,target in itertools.product([0,1],range(5),q):
   assert abs(K[x,u,z,target].sum()-K[y,u,z,target].sum())<1e-12
# The initial task quotient passes cancellation but fails conditional lumpability.
taskp=[[i for i,t in enumerate(task) if t==a] for a in [0,1]]
assert not conditional(taskp)
assert all(abs(D[x,u,t].sum(axis=0)).max()<1e-12 for x,u,t in itertools.product(range(8),[0,1],taskp))
out={'status':'PASS','random_raw_label_permutation':perm.tolist(),'task_preserving_candidates':len(candidates),'conditional_partitions':len(valid),'coarsest_conditional_partition':q,'coarsest_states':minimum,'autonomous_partitions':0,'minimum_raw_probability':float(K.min()),'learner_input':'Random raw labels, task signature, averaged B rows, and paired observed D response tables; hidden coordinates used only after search for QA.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
