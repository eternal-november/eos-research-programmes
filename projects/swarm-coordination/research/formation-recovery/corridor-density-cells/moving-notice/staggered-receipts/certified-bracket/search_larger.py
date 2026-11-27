from fractions import Fraction
from math import lcm
import numpy as np
from scipy.optimize import linprog
import json

def run(k):
 n=2*k;m=3*n
 lo=[];rhs=[];eq=[];same=[]
 A=np.zeros((5,n,m+1))
 for j in range(n):
  A[0,j,-1]=-2 if j<k else 2
  A[4,j,-1]=-A[0,j,-1]
  for i in range(3):A[i+1,j,i*n+j]=1
 X,V=np.zeros((5,m+1)),np.zeros((5,m+1))
 def le(B,u):lo.append(B[:-1]);rhs.append(u-B[-1])
 def equal(B):eq.append(B[:-1]);same.append(-B[-1])
 for j in range(n):
  if j<k:equal(A[1,j]+A[3,j])
  end=X+2*V+A[:,j]
  for P in (X,X+V,end):
   for i in range(4):
    B=P[i+1]-P[i]
    le(B,6*k*k);le(-B,0)
  X=end;V=V+A[:,j]
  for row in V:le(row,2*k);le(-row,2*k)
 for row in V[1:4]:equal(row)
 r=linprog(-X[2,:-1],A_ub=lo,b_ub=rhs,A_eq=eq,b_eq=same,bounds=[(-2,2)]*m,method="highs")
 assert r.success
 vals=[Fraction(float(v)).limit_denominator(50000) for v in r.x]
 d=lcm(*(x.denominator for x in vals))
 aa=[[int(x*d) for x in vals[i*n:(i+1)*n]] for i in range(3)]
 return {"k":k,"d":d,"interior":aa,"float":-r.fun/(2*k*k)+2}
for k in (64,128):print(json.dumps(run(k)))

