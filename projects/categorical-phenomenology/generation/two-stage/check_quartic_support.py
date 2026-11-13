#!/usr/bin/env python3
"""Exact rational arithmetic regressions, not a physical experiment or proof search."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

zero = (F(0), F(0))
axis = [(F(1,4),zero)]
axis += [(F(3,16),v) for v in [(F(1),F(0)),(F(-1),F(0)),(F(0),F(1)),(F(0),F(-1))]]
Q = ((F(3,5),F(-4,5)),(F(4,5),F(3,5)))
rotated = [(p,tuple(sum(Q[i][j]*z[j] for j in range(2)) for i in range(2))) for p,z in axis]

def mom(law, powers):
    return sum(p * product_f(z[j]**powers[j] for j in range(len(powers))) for p,z in law)
def product_f(values):
    ans=F(1)
    for v in values: ans*=v
    return ans
def source_checks(law):
    assert sum(p for p,z in law)==1
    assert all(p>=0 and sum(x*x for x in z)<=1 for p,z in law)
    assert all(mom(law,p)==0 for p in [(1,0),(0,1),(1,1)])
    assert mom(law,(2,0))==mom(law,(0,2))==F(3,8)
source_checks(axis); source_checks(rotated)
assert mom(axis,(4,0))==mom(axis,(0,4))==F(3,8)
assert mom(axis,(6,0))==mom(axis,(0,6))==F(3,8)
c=F(3,8)
assert mom(axis,(4,0))/c**2==F(8,3)
assert mom(axis,(6,0))/c**3==F(64,9)

# At the old nonlinear family's reference context c=(0,0,0), s(c)=1.
B=(F(1,5),F(1,5),F(1,5),F(2,5))
lam=F(1,40)
U=((F(1),F(0)),(F(-1),F(0)),(F(0),F(1)),(F(0),F(-1)))
G=tuple(tuple(lam*x for x in row) for row in U)
L=tuple(tuple(U[y][j]/(2*lam) for y in range(4)) for j in range(2))
assert [[sum(L[i][y]*G[y][j] for y in range(4)) for j in range(2)] for i in range(2)]==[[1,0],[0,1]]
assert all(B[y]>=lam for y in range(4))  # Positivity on the entire unit ball.
def kernel(y,z): return B[y]+sum(G[y][j]*z[j] for j in range(2))
def score(j,y): return sum(L[j][k]*((1 if k==y else 0)-B[k]) for k in range(4))
scores=[[score(j,y) for y in range(4)] for j in range(2)]
for _,z in axis+rotated:
    assert all(kernel(y,z)>0 for y in range(4))
    assert sum(kernel(y,z) for y in range(4))==1
    assert all(sum(kernel(y,z)*score(j,y) for y in range(4))==z[j] for j in range(2))
def law_outputs(law,k):
    return {ys:sum(p*product_f(kernel(y,z) for y in ys) for p,z in law) for ys in product(range(4),repeat=k)}
def score_moment(table,js):
    return sum(p*product_f(score(j,y) for j,y in zip(js,ys)) for ys,p in table.items())
for k in [1,2,3]: assert law_outputs(axis,k)==law_outputs(rotated,k)
quartet=law_outputs(axis,4)
assert sum(quartet.values())==1 and min(quartet.values())>0
assert quartet!=law_outputs(rotated,4)
for js in product(range(2),repeat=4):
    expected=F(3,8) if len(set(js))==1 else F(0)
    assert score_moment(quartet,js)==expected
six=law_outputs(axis,6)
for j in range(2): assert score_moment(six,(j,)*6)==F(3,8)
assert score_moment(six,(0,0,0,0,1,1))==0

# A source consistent with mean/cov/radius but not the saturation law.
p_mix=F(1,10)
mixture=[((1-p_mix)*p,z) for p,z in axis]+[(p_mix*p,z) for p,z in rotated]
source_checks(mixture)
def nearest(z):
    j=max(range(2),key=lambda j:abs(z[j]))
    if abs(z[j])<=F(1,2): return zero
    return tuple(F(1 if z[j]>0 else -1) if k==j else F(0) for k in range(2))
def q(z): return sum(x*x for x in z)-sum(x**4 for x in z)
def distance2(z):
    u=nearest(z)
    return sum((z[j]-u[j])**2 for j in range(2))
delta=sum(p*q(z) for p,z in mixture)
e2=sum(p*distance2(z) for p,z in mixture)
assert delta==sum(c-mom(mixture,p) for p in [(4,0),(0,4)])
assert e2<=F(4,3)*delta
for j in range(2):
    d4=c-mom(mixture,(4,0) if j==0 else (0,4))
    d6=c-mom(mixture,(6,0) if j==0 else (0,6))
    assert 0<=d6<=2*d4
# Bounded exact grid regression of the sharp rounding inequality.
grid_count=0
for a,b in product(range(-20,21),repeat=2):
    z=(F(a,20),F(b,20))
    if sum(x*x for x in z)>1: continue
    assert 3*distance2(z)<=4*q(z)
    grid_count+=1
assert 3*distance2((F(1,2),F(0)))==4*q((F(1,2),F(0)))

# Symmetric scalar laws represented by total weights at each squared radius.
A=[(F(1,2),F(0)),(F(1,2),F(2))]
C=[(F(1,3),F(0)),(F(1,2),F(1)),(F(1,6),F(3))]
def even(law,k): return sum(p*radius2**k for p,radius2 in law)
assert even(A,1)==even(C,1)==1
assert even(A,2)==even(C,2)==2
assert even(A,3)==4 and even(C,3)==5

# Growing-r radius counterexample, using squared radii for exact moments.
radius_counterexamples=[]
for r in [1,2,3,8,16,64]:
    target_radius2=F(4*r,3)
    target_signed_weight=F(3,8*r)
    alternate=[(F(1,3*r),F(r)),(F(1,12*r),F(2*r))]
    assert F(1,4)+2*r*target_signed_weight==1
    assert F(1,6)+2*r*sum(w for w,s in alternate)==1
    target=[2*target_signed_weight*target_radius2**k for k in [1,2,3]]
    other=[sum(2*w*s**k for w,s in alternate) for k in [1,2,3]]
    assert target[:2]==other[:2]==[F(1),F(4*r,3)]
    assert target[2]==F(16*r*r,9) and other[2]==2*r*r
    eps=F(1,8*r*r); baseline=F(1,2*r)
    assert eps**2*(2*r)<baseline**2 # Strict positivity on the larger ball.
    radius_counterexamples.append({'r':r,'target_radius_squared':str(target_radius2),'alternative_radius_squared':str(2*r),'target_sixth':str(target[2]),'alternative_sixth':str(other[2])})

out={
    'status':'PASS',
    'arithmetic':'fractions.Fraction throughout; exact equality assertions',
    'old_tau':'3/4', 'raw_covariance_diagonal':str(c),
    'standardized_radius_squared':'8/3',
    'standardized_fourth_axis_moment':'8/3',
    'standardized_sixth_axis_moment':'64/9',
    'same_context_response_rank':2,
    'quartet_tensor_entries_checked':16,
    'quartet_table_atoms':len(quartet),
    'simulated_six_view_table_atoms':len(six),
    'pair_and_triple_laws_equal_under_rotated_source':True,
    'quartet_laws_distinct_under_rotated_source':True,
    'approximate_mixture_defect':str(delta),
    'approximate_mixture_rounding_mean_square':str(e2),
    'sharp_rounding_grid_points':grid_count,
    'unsaturated_scalar_sixth_moments':['4','5'],
    'growing_rank_radius_counterexamples':radius_counterexamples,
    'limitations':'Synthetic model tables only. No new physical data, no sampled-data calibration, no claim exact support follows from finite samples.'
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
