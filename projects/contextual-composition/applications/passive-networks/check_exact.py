"""Exact finite diagnostics; written proofs, not these tests, justify generality."""
import sympy as s
from itertools import combinations

def lap(n, edges):
    L=s.zeros(n)
    for a,b,c in edges:
        c=s.Rational(c); L[a,a]+=c; L[b,b]+=c; L[a,b]-=c; L[b,a]-=c
    return L

def reduce(L,B):
    # Drop precisely the connected components with no boundary contact.
    reached=set(B)
    while True:
        extra={j for i in reached for j in range(L.rows) if i!=j and L[i,j]!=0}
        if extra<=reached: break
        reached |= extra
    I=sorted(reached-set(B))
    BB=L.extract(B,B)
    if not I: return BB
    return BB-L.extract(B,I)*L.extract(I,I).inv()*L.extract(I,B)

checks=[]
star=[(0,3,2),(1,3,3),(2,3,5)]
tri=[(0,1,s.Rational(3,5)),(0,2,1),(1,2,s.Rational(3,2))]
R=reduce(lap(4,star),[0,1,2])
assert R==lap(3,tri)
assert R==s.Matrix([[s.Rational(8,5),-s.Rational(3,5),-1],[-s.Rational(3,5),s.Rational(21,10),-s.Rational(3,2)],[-1,-s.Rational(3,2),s.Rational(5,2)]])
checks.append('star_mesh_exact')
assert reduce(lap(6,star+[(4,5,7)]),[0,1,2])==R
checks.append('floating_component_invariance')
# Attach edges through two new vertices; compare all external currents.
context=[(1,4,7),(2,4,2),(4,5,3),(0,5,11)]
A=lap(6,star+context)
T=lap(6,tri+context) # vertex3 now isolated and discarded
assert reduce(A,[0,5])==reduce(T,[0,5])
checks.append('asymmetric_contextual_substitution')
# Eliminate original interior3 first, then newly internal1,2,4.
intermediate=reduce(A,[0,1,2,4,5])
assert reduce(intermediate,[0,4])==reduce(A,[0,5])
checks.append('staged_equals_joint_elimination')
H=s.Matrix([[1,-1],[-1,1]]); e=s.Matrix([1,0])
assert (H+s.eye(2)).inv()*e==s.Matrix([s.Rational(2,3),s.Rational(1,3)])
assert (2*H+s.eye(2)).inv()*e==s.Matrix([s.Rational(3,5),s.Rational(2,5)])
assert H.nullspace()==(2*H).nullspace()
checks.append('same_connectivity_distinct_loaded_behavior')
# Positive rational parameter family of star replacements, not only one choice.
for a in range(1,5):
 for b in range(1,5):
  for c in range(1,5):
   z=s.Rational(1,a+b+c)
   assert reduce(lap(4,[(0,3,a),(1,3,b),(2,3,c)]),[0,1,2])==lap(3,[(0,1,a*b*z),(0,2,a*c*z),(1,2,b*c*z)])
checks.append('64_rational_star_cases')
# Enumerate all 64 simple unweighted graphs on 4 vertices, boundary0,1,2.
for mask in range(64):
 E=[(a,b,1) for k,(a,b) in enumerate(combinations(range(4),2)) if mask>>k&1]
 L=lap(4,E); Q=reduce(L,[0,1,2])
 for j in range(3):
  u=(Q+s.eye(3)).inv()[:,j]
  assert (Q+s.eye(3))*u==s.eye(3)[:,j]
 assert Q==Q.T and Q*s.ones(3,1)==s.zeros(3,1)
checks.append('64_graphs_including_disconnected_and_floating_cases')
print('\n'.join('PASS '+c for c in checks))
print('All exact diagnostics passed. No Lean replay or independent audit claimed.')
