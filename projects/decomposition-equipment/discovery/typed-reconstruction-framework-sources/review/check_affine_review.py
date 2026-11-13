from itertools import product
from math import gcd
import json

def compose(f,gs,N):
 return ((f[0]+sum(a*g[0] for a,g in zip(f[1],gs)))%N,tuple(a*v%N for a,g in zip(f[1],gs) for v in g[1]))
identity=(0,(1,)); survivors=[]; checked=0
for b,a,c,t,s in product((0,2),(1,3),(1,3),(1,3),(1,3)):
 mu=(b,(a,c)); tau=(t,(s,)); checked+=1
 assoc=compose(mu,[mu,identity],4)==compose(mu,[identity,mu],4)
 natural=compose(tau,[mu],4)==compose(mu,[tau,identity],4)
 invol=compose(tau,[tau],4)==identity
 if assoc and natural and invol: survivors.append((mu,tau))
assert not survivors
# Full interval/root unary normalization is not identity insertion.
f=(2,(3,1)); outer=(2,(3,)); inner=(0,(1,3))
assert compose(outer,[inner],4)==f and outer!=identity
# Independent exhaustive 2-input cut transport, including full interval and singleton.
N=4; U=(1,3); cases=0
for b,a1,a2,u0,v0,u1,v1,u2,v2 in product(range(4),U,U,U,range(4),U,range(4),U,range(4)):
 f=(b,(a1,a2)); rs=[(v1,(u1,)),(v2,(u2,))]; r0=(v0,(u0,))
 fp=compose(r0,[compose(f,rs,N)],N)
 for lo,hi in [(0,1),(1,2),(0,2)]:
  a=f[1]; ap=fp[1]; p=a[lo]; pp=ap[lo]
  old=(0,tuple(x*pow(p,-1,N)%N for x in a[lo:hi]))
  new=(0,tuple(x*pow(pp,-1,N)%N for x in ap[lo:hi]))
  c=sum(a[k]*pow(p,-1,N)*rs[k][0] for k in range(lo,hi))%N
  gauge=(c,rs[lo][1])
  assert compose(old,rs[lo:hi],N)==compose(gauge,[new],N)
  cases+=1
print(json.dumps({'status':'PASS','affine_section_candidates_rejected':checked,'root_unary_counterexample':True,'exhaustive_Z4_two_input_cut_transport_cases':cases},indent=2))
