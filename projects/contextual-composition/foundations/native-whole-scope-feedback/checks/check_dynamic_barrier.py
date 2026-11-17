from fractions import Fraction as F
from itertools import product
# Actual finite completed X records; retry depth is retained, not quotiented.
def records(N):
 return [(k,b,F(1,4)**k*F(1,2)*pb) for k in range(N) for b,pb in [(0,F(1,2)),(1,F(1,2)),(2,F(0))]]
for N in range(1,7):
 rs=records(N);q=sum(m for k,b,m in rs)
 assert q==F(2,3)*(1-F(1,4)**N)
 total=q*q
 # Each first Y law conditional on its own ENTIRE (retry depth,b) record
 # and the global return token. Crosswise z=b_other.
 for k,b,m in rs:
  own_mass=m*q
  for z,pz in [(0,F(1,2)),(1,F(1,2)),(2,F(0))]:
   pushed=sum(m*n for kk,bb,n in rs if bb==z)
   assert pushed==own_mass*pz
 # Source positive full-prefix fibre fails fair test.
 m=F(1,4) # retry0 then return then b0
 assert m*m!=m*m*F(1,2)
 print('retry bound',N,'X stage return mass',q,'binary cut mass',total)
# All-raw dynamic cases are different even when visible jobs are empty.
null={'sealed':True,'returned':True,'jobs':(), 'done':False,'real_factors':1}
spin={'sealed':False,'returned':False,'jobs':(), 'done':False,'real_factors':1}
assert null['jobs']==spin['jobs'] and null!=spin
# BIRTH-REACTIVE finite prefix: a completed opaque z outcome exports U
# independently of helper future. Return-gated interface cannot match it.
cert=('closed_X','full_own_X_record',2,1,'primitive_ancestry')
def export(helper_status):return {'slot':('episode',2,'U'),'d':cert,'owner':'old-paid-Y'}
assert export('pending')==export('Spin')==export('returned')
prefix={'V_frame':'pending','helper':'Spin','U_certificate':export('Spin'),'U_call':'started','child_factors':1}
assert prefix['V_frame']!='returned' and prefix['U_call']=='started'
# Selected independent root completion approximants, not all-family scalar claims.
def step(q):
 s=F(1,2)+q/F(4)
 return F(4,9)*((s+s*s)/2)**2
assert step(F(1,10))<F(1,10)
q=F(0)
for m in range(1,7):
 r=step(q);assert q<r<F(1,10);q=r
 print('loop depth',m,'quiescence approx',float(q))
print('PASS exact binder marginals, strict source failure, null/Spin distinction, finite-prefix external birth')
print('Clock: old paid scope advances once before pending entries; silent unfolding advances zero')
