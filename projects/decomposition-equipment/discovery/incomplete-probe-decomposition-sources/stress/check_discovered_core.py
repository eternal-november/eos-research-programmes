import itertools,json
from pathlib import Path
import numpy as np
states=list(itertools.product([0,1],repeat=3))
U=np.zeros((8,2))
for j,(a,b,y) in enumerate(states):U[j,0 if a==b else 1]=1 if y else -1
Z=np.array([[0,0],[1,0],[-1,0],[0,1],[0,-1]],float)
def B4(a,b,u):
 w=np.array([2+a+2*a*b,2+b+u*a,2+(a^b)+u,2+2*(b^u)+a*b],float);return w/w.sum()
def B(x,u):
 a,b,y=x;p=.25+.1*y+.05*a+.03*b*u
 return np.array([B4(a,b,u)[2*ap+bp]*(p if yp else 1-p) for ap,bp,yp in states])
def s(x,u):
 a,b,y=x;return 1+.2*a+.15*b+.1*u*a*b+.05*y
# Restricted-growth enumeration, all225 task-preserving partitions.
def parts(xs):
 if not xs:yield [];return
 x,*rest=xs
 for p in parts(rest):
  yield [[x]]+[b[:] for b in p]
  for j in range(len(p)):
   q=[b[:] for b in p];q[j]=[x]+q[j];yield q
candidates=[p+q for p in parts(list(range(4))) for q in parts(list(range(4,8)))]
def valid(p, baseline=B):
 if any(abs(U[block].sum(axis=0)).max()>1e-12 for block in p):return False
 for oldblock in p:
  for x,y in itertools.combinations(oldblock,2):
   for u in [0,1]:
    if any(abs(baseline(states[x],u)[block].sum()-baseline(states[y],u)[block].sum())>1e-12 for block in p):return False
 return True
passed=[p for p in candidates if valid(p)]
assert len(candidates)==225 and len(passed)==1
assert sorted(sorted(b) for b in passed[0])==[[0,1],[2,3],[4,5],[6,7]]
Hs=[np.eye(2),np.array([[1.3,.2],[.1,.85]])]
minimum=1.
for H in Hs:
 for A in [.005*H,.005*np.linalg.inv(H).T]:
  for x,u in itertools.product(states,[0,1]):
   K=B(x,u)[None,:]+s(x,u)*Z@A.T@U.T
   minimum=min(minimum,float(K.min()));assert abs(K.sum(axis=1)-1).max()<1e-12
assert minimum>0
def Bbad(x,u):return B(x,u)+.005*(2*x[2]-1)*np.array([1,1,0,0,-1,-1,0,0])
bad_passed=[p for p in candidates if valid(p,Bbad)]
assert not bad_passed
assert min(Bbad(x,u).min() for x,u in itertools.product(states,[0,1]))>0
out={'bad_case_valid_partitions':len(bad_passed),'status':'PASS','task_preserving_partitions':225,'valid_partitions':passed,'minimum_probability':minimum,'result':'Unknown task-preserving quotient is uniquely core(a,b), discardingy; taska alone fails lumpability.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
