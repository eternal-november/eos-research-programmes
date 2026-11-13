import itertools, json
from pathlib import Path
import numpy as np
OUT=Path(__file__).with_suffix('.json')
U=np.array([[1.,0.],[-1.,0.],[0.,1.],[0.,-1.]])
Up=np.linalg.pinv(U)
contexts=list(itertools.product([0,1],repeat=3))
states=list(itertools.product([0,1],repeat=2))
Z=np.array([[0,0],[1,0],[-1,0],[0,1],[0,-1]],float)
lam=.025
def B(c):
 a,b,u=c
 w=np.array([2+a+2*a*b,2+b+u*a,2+(a^b)+u,2+2*(b^u)+a*b],float)
 return w/w.sum()
def s(c):
 a,b,u=c
 return 1+.2*a+.15*b+.1*u*a*b
def rows(A,c): return B(c)[None,:]+s(c)*(Z@A.T@U.T)
def pi(t): return np.array([1-t,t/4,t/4,t/4,t/4])
def pair(A,D,c,e,t): return np.einsum('z,zi,zj->ij',pi(t),rows(A,c),rows(D,e))
H=np.array([[1.3,.2],[.1,.85]])
Hs=[np.eye(2),H,np.array([[1,-1],[1,1]])/np.sqrt(2)]
mins=[]
max_pair_error=0.
max_s_error=0.
for h in Hs:
 AL=lam*h; AR=lam*np.linalg.inv(h).T
 for A in [AL,AR]:
  for c in contexts:
   r=rows(A,c);mins.append(r.min());assert np.max(abs(r.sum(axis=1)-1))<1e-12
 for t in [.25,.75]:
  for c,e in itertools.product(contexts,repeat=2):
   J=pair(AL,AR,c,e,t)
   baseline=pair(lam*np.eye(2),lam*np.eye(2),c,e,t)
   max_pair_error=max(max_pair_error,float(abs(J-baseline).max()))
   D=2/t*Up@(J-np.outer(B(c),B(e)))@Up.T
   expected=s(c)*s(e)*lam**2*np.eye(2)
   assert abs(D-expected).max()<1e-12
  c0=(0,0,0)
  def D(c,e):return 2/t*Up@(pair(AL,AR,c,e,t)-np.outer(B(c),B(e)))@Up.T
  for c in contexts:
   recovered=D(c,c0)@np.linalg.inv(D(c0,c0))
   max_s_error=max(max_s_error,float(abs(recovered-s(c)*np.eye(2)).max()))
assert min(mins)>0 and max_pair_error<1e-12 and max_s_error<1e-10
# Pair stationary law is nonuniform, and shared across all worlds.
def pair_transition(AL,AR):
 return np.array([pair(AL,AR,(*x,0),(*y,0),.75).ravel() for x,y in itertools.product(states,repeat=2)])
P=pair_transition(lam*np.eye(2),lam*np.eye(2))
p=np.ones(16)/16
for _ in range(1000):
 pn=p@P
 if np.max(abs(pn-p))<1e-15:break
 p=pn
assert np.max(abs(p@P-p))<1e-13
assert np.max(abs(p-1/16))>.001
# Four-component positive whole row; rotated world agrees on every pair but not fourth law.
Q=Hs[-1]; c=(0,0,0); t=.75
whole=[]
for h in [np.eye(2),Q]:
 A=lam*h; rr=rows(A,c)
 joint=sum(pi(t)[z]*np.einsum('i,j,k,l->ijkl',rr[z],rr[z],rr[z],rr[z]) for z in range(5))
 assert joint.min()>0 and abs(joint.sum()-1)<1e-12
 f=np.eye(4)[0]-B(c)[0]
 moment=np.einsum('ijkl,i,j,k,l',joint,f,f,f,f)
 whole.append(float(moment))
assert abs(whole[0]-lam**4*t/2)<1e-16
assert abs(whole[1]-lam**4*t/4)<1e-16
assert abs(pair(lam*np.eye(2),lam*np.eye(2),c,c,t)-pair(lam*Q,lam*Q,c,c,t)).max()<1e-12
# Same-side test resolves nonorthogonal gauge.
same_side_difference=float(abs(pair(lam*H,lam*H,c,c,t)-pair(lam*np.eye(2),lam*np.eye(2),c,c,t)).max())
assert same_side_difference>1e-5
# A scalar four-cycle obstruction. A1 A2T=A2 A3T=A3 A4T=cI implies A4 A1T=cI.
cc=lam**2; C=cc*np.eye(2)
factors=[np.eye(2)]
for _ in range(3):factors.append(C.T@np.linalg.inv(factors[-1]).T)
forced=factors[3]@factors[0].T
assert abs(forced-C).max()<1e-12
cycle_residual=float(abs(forced-2*C).max());assert cycle_residual>0
# Each inconsistent edge separately has positive realization, including the doubled edge.
for scale in [lam,np.sqrt(2)*lam]:
 assert min(rows(scale*np.eye(2),c).min() for c in contexts)>0
# Explicit internal interaction: nonzero old-bit mixed difference in baseline.
interaction=B((1,1,0))-B((1,0,0))-B((0,1,0))+B((0,0,0))
assert np.linalg.norm(interaction)>1e-3
result={'status':'PASS','minimum_local_probability':float(min(mins)),
 'max_observed_pair_error':max_pair_error,'max_context_factor_recovery_error':max_s_error,
 'pair_stationary_distance_from_uniform':float(max(abs(p-1/16))),
 'same_side_test_difference':same_side_difference,
 'fourth_centered_moments_base_and_rotation':whole,'inconsistent_cycle_residual':cycle_residual,
 'baseline_mixed_difference_norm':float(np.linalg.norm(interaction)),
 'growth_examples':[{'modules':n,'whole_states':4**n,'pair_table_entries':n*64*16} for n in [4,6,10,50]],
 'scope':'Exact finite numerical verification of displayed family; not finite-sample inference, unknown patch discovery, or external physical certification.'}
OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
