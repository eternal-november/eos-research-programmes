#!/usr/bin/env python3
"""Exact rational regressions for gram_behavioral_theorem.md; not its proof."""
import itertools,json,random
from pathlib import Path
import sympy as s
random.seed(20261105)
out={'closure_cases':0,'shift_two_step_cases':0,'finite_reconstruction_cases':0,'scalar_cases':0,'gram_rank_cases':0}
def raw_step(A,B,Y,eta):
 E=A*B-Y
 return A-eta*E*B.T, B-eta*A.T*E

def gram(A,B):return (A*A.T,A*B,B.T*B)
def step(L,F,R,E,eta):
 return (L-eta*(E*F.T+F*E.T)+eta**2*E*R*E.T,
         F-eta*(L*E+E*R)+eta**2*E*F.T*E,
         R-eta*(E.T*F+F.T*E)+eta**2*E.T*L*E)
def randmat(m,n):return s.Matrix(m,n,lambda i,j:random.randint(-2,2))
def unit(m,n,i,j):
 E=s.zeros(m,n);E[i,j]=1;return E
def zero(M):return all(s.expand(v)==0 for v in M)
for m,n,h in itertools.product(range(1,4),range(1,4),range(1,5)):
 for eta in (s.Rational(1,3),s.Rational(1),s.Rational(-2,3)):
  A,B=randmat(m,h),randmat(h,n);L,F,R=gram(A,B);E=randmat(m,n)
  A1,B1=raw_step(A,B,F-E,eta);pred=step(L,F,R,E,eta)
  assert all(zero(x-y) for x,y in zip(gram(A1,B1),pred))
  out['closure_cases']+=1
  G=L.row_join(F).col_join(F.T.row_join(R));C=A.T.row_join(B)
  assert G==C.T*C and G.rank()==C.rank()<=h
  T=s.eye(m).row_join(-eta*E).col_join((-eta*E.T).row_join(s.eye(n)))
  assert A1.T.row_join(B1)==C*T
  assert A1.T.row_join(B1).rank()<=G.rank()
  out['gram_rank_cases']+=1
  c=s.Rational(2,3);Z=randmat(m,n)
  p=step(L,F,R,E,eta);q=step(L+c*s.eye(m),F,R-c*s.eye(n),E,eta)
  assert p[1]==q[1]
  p2=step(*p,Z,eta);q2=step(*q,Z,eta)
  assert zero(q2[1]-p2[1]-eta**3*c*(E*E.T*Z-Z*E.T*E))
  out['shift_two_step_cases']+=1
  # Finite exact recovery using m+n-1 reset experiments and one continuation.
  # Recover L0=L-L[0,0] I and R0=R+L[0,0] I.
  if m*n>1:
   K={}
   for i,j in [(i,0) for i in range(m)]+[(0,j) for j in range(1,n)]:
    ee=unit(m,n,i,j);f1=step(L,F,R,ee,eta)[1]
    K[i,j]=(F-f1+eta**2*ee*F.T*ee)/eta
   L0=s.zeros(m);R0=s.zeros(n)
   for i in range(m):
    for k in range(m):
     if i!=k:L0[k,i]=K[i,0][k,0]
    L0[i,i]=K[i,0][i,0]-K[0,0][0,0]
   for j in range(n):
    for ell in range(n):
     if j!=ell:R0[j,ell]=K[0,j][0,ell]
    R0[j,j]=K[0,j][0,j]
   assert L0==L-L[0,0]*s.eye(m)
   assert R0==R+L[0,0]*s.eye(n)
   ee=unit(m,n,0,0)
   if n>1:zz=unit(m,n,0,1);ridx=(0,1);sign=1
   else:zz=unit(m,n,1,0);ridx=(1,0);sign=-1
   actual=step(*step(L,F,R,ee,eta),zz,eta)[1]
   base=step(*step(L0,F,R0,ee,eta),zz,eta)[1]
   a=s.simplify((actual-base)[ridx]/(sign*eta**3))
   assert a==L[0,0]
   assert L0+a*s.eye(m)==L and R0-a*s.eye(n)==R
   out['finite_reconstruction_cases']+=1
  else:
   SS=L[0]+R[0];ee=E[0]
   assert pred[1][0]==(1+eta**2*ee**2)*F[0]-eta*ee*SS
   assert pred[0][0]+pred[2][0]==(1+eta**2*ee**2)*SS-4*eta*ee*F[0]
   out['scalar_cases']+=1
# Symbolic rank-1 versus rank-2 example, arbitrary eta (including sign).
e=s.symbols('eta',nonzero=True)
Ap,Bp=s.Matrix([[1]]),s.Matrix([[0,0]])
Aq,Bq=s.zeros(1,2),s.eye(2)
Y0=s.Matrix([[-1,0]]);Y1=s.Matrix([[-e,-1]])
Ap1,Bp1=raw_step(Ap,Bp,Y0,e);Aq1,Bq1=raw_step(Aq,Bq,Y0,e)
assert Ap1*Bp1==Aq1*Bq1==s.Matrix([[-e,0]])
Ap2,Bp2=raw_step(Ap1,Bp1,Y1,e);Aq2,Bq2=raw_step(Aq1,Bq1,Y1,e)
assert zero(Ap2*Bp2-s.Matrix([[-e,-e]]))
assert zero(Aq2*Bq2-s.Matrix([[-e,-e-e**3]]))
out['symbolic_width_separation']='passed for symbolic nonzero eta'
M=s.symbols('M',positive=True)
Y0b=s.Matrix([[-M,0]]);Y1b=s.Matrix([[0,-M]])
Ap1b,Bp1b=raw_step(Ap,Bp,Y0b,e);Aq1b,Bq1b=raw_step(Aq,Bq,Y0b,e)
Ap2b,Bp2b=raw_step(Ap1b,Bp1b,Y1b,e);Aq2b,Bq2b=raw_step(Aq1b,Bq1b,Y1b,e)
assert zero(Aq2b*Bq2b-Ap2b*Bp2b-s.Matrix([[0,-e**3*M**3]]))
out['bounded_target_noise_witness']='exact gap |eta|^3 M^3 verified symbolically'
# Scalar same behavior, different actual Gram ranks.
# F=0,S=2: h=1 A=sqrt(2),B=0 vs h=2 A=(1,0),B=(0,1)^T.
P=(s.Matrix([[2]]),s.Matrix([[0]]),s.Matrix([[0]]))
Q=(s.Matrix([[1]]),s.Matrix([[0]]),s.Matrix([[1]]))
for k in range(8):
 E=s.Matrix([[s.Rational(k-3,5)]])
 P=step(*P,E,s.Rational(1,2));Q=step(*Q,E,s.Rational(1,2))
 assert P[1]==Q[1] and P[0]+P[2]==Q[0]+Q[2]
out['scalar_rank_ambiguity_steps']=8
# The explicit pair remains indistinguishable for any tested stationary target.
# Small rational steps and five rounds keep exact expression sizes manageable.
stationary=0
for vals in [(0,0),(1,0),(0,1),(1,1),(1,-2),(-2,1)]:
 aa,bb=Ap.copy(),Bp.copy();cc,dd=Aq.copy(),Bq.copy()
 yy=s.Matrix([list(vals)])
 for _ in range(5):
  aa,bb=raw_step(aa,bb,yy,s.Rational(1,4))
  cc,dd=raw_step(cc,dd,yy,s.Rational(1,4))
  assert aa*bb==cc*dd
  stationary+=1
out['stationary_target_equal_output_cases']=stationary
out['status']='all exact rational and symbolic checks passed'
Path(__file__).with_name('check_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
